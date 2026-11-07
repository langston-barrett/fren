"""Trusted preparation and head-status reporting for pre-merge.

Only the review's post job produces posted-review, after posting a checked
verdict, clean or blocking. A workflow_run of pr-review carries main's
SHA, not the PR head: the attestation identifies that head without trusting branch names,
comments by other workflows, or artifacts from jobs that run PR code.
"""

import base64
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

JOBS = ("own-spec-agreement", "methods-agree", "coverage", "fuzz-frontends")
PUSHERS = {"OWNER", "MEMBER", "COLLABORATOR"}
BOT = {"github-actions", "github-actions[bot]"}
VERDICT = re.compile(r"Review of ([0-9a-f]{40}): (no blocking issues(?: \((?:fixes|rebase) only\))?|blocking issues)")
CLEAN = re.compile(r"Review of ([0-9a-f]{40}): no blocking issues(?: \((?:fixes|rebase) only\))?")
POST_CONTEXT = re.compile(r"Post review \(PR ([0-9]+), head ([0-9a-f]{40}), attempt ([0-9]+)\)")
DEPENDENCY = "Gate dependency (PR {pr}, head {head}, source {source}, main {base}, merge {merge}, attempt {attempt})"
DEPENDENCY_CONTEXT = re.compile(r"Gate dependency \(PR ([0-9]+), head ([0-9a-f]{40}), source ([0-9a-f]{40}), main ([0-9a-f]{40}), merge ([0-9a-f]{40}), attempt ([0-9]+)\)")


def selected(paths):
    """r[ci.linked-runtime]: conservative inputs of the shared slow checks."""
    paths = tuple(paths)
    # Changes to the shared build/toolchain, runner action, or gate can
    # affect every job. Include scripts, which Lake and the jobs invoke,
    # and all c/ inputs: their runtime objects are linked into the executables.
    common = any(p in ("lakefile.lean", "lake-manifest.json", "lean-toolchain")
                 or p.startswith(("c/", "scripts/", ".github/actions/", ".github/pre-merge/"))
                 or p in (".github/workflows/ci.yml", ".github/workflows/pre-approval.yml",
                          ".github/workflows/slow-checks.yml",
                          ".github/workflows/pre-merge.yml") for p in paths)
    # Both front ends and the shared core implement decisions exercised by
    # agreement and fuzzing. Include root modules as well as their trees.
    frontends = any(p.startswith(("src/Fren/", "src/FrenCli/", "src/FrenCore/"))
                    or p in ("src/Fren.lean", "src/FrenCli.lean", "src/FrenCore.lean",
                             "src/FrenMain.lean", "src/FrenCoreCodes.lean") for p in paths)
    # The test driver/comparison code and fuzzer define the agreement jobs
    # and their corpora; widening this to all test helpers errs toward running.
    driver = any(p.startswith(("src/FrenTest/", "src/FrenTestMain.", "src/FrenFuzz")) for p in paths)
    own = any(p.startswith(("src/Reqs/", "src/Impls/"))
              or p in ("src/Reqs.lean", "src/Impls.lean") for p in paths)
    # methodsAgree runs own, ui/examples and generated fuzz specs under solver,
    # enumeration and random evaluation. Front-end/core changes can change
    # those inputs or their verdicts, not just Check/Enumerate/Eval files.
    methods = any(p.startswith(("test/ui/", "examples/", "test/method")) for p in paths)
    # Coverage instruments Lean and runs all of lake test: any fixture,
    # exclusion/test list, example or library spec can change what executes.
    coverage = any(p.endswith((".lean", ".fren", ".md"))
                   or p.startswith(("test/", "lib/", "examples/", "src/FrenTestFiles/")) for p in paths)
    return dict(zip(JOBS, (common or frontends or driver or own,
                           common or frontends or driver or own or methods,
                           common or coverage,
                           common or frontends or driver)))


def output(**values):
    with open(os.environ["GITHUB_OUTPUT"], "a") as f:
        for key, value in values.items():
            if isinstance(value, bool):
                value = str(value).lower()
            f.write(f"{key}={value}\n")


def run(*args):
    return subprocess.check_output(args, text=True).strip()


def api(endpoint, payload=None, method=None):
    args = ["gh", "api", endpoint]
    if method:
        args += ["--method", method]
    if payload is not None:
        args += ["--input", "-"]
    return json.loads(subprocess.check_output(args, input=None if payload is None else json.dumps(payload), text=True))


def first_line(body):
    return body.strip().splitlines()[0] if body.strip() else ""


def artifact_name(pr, head):
    return f"posted-review-{int(pr)}-{head}"


def record():
    """Bind a checked verdict to the actual comment, including blocking ones."""
    text = Path(os.environ["RUNNER_TEMP"], "comment.md").read_text()
    posted = json.loads(Path(os.environ["RUNNER_TEMP"], "posted-comment.json").read_text())
    match = VERDICT.fullmatch(text.splitlines()[0])
    valid = match is not None and match[1] == os.environ["HEAD"]
    if valid:
        if posted["body"].rstrip("\n") != text.rstrip("\n"):
            raise ValueError("Posted comment differs from the checked review")
        pr = int(os.environ.get("POST") or os.environ["PR"])
        directory = Path(os.environ["RUNNER_TEMP"], "posted-review")
        directory.mkdir()
        (directory / "review.json").write_text(json.dumps({
            "pr": pr, "head": match[1], "body": posted["body"],
            "attempt": int(os.environ["GITHUB_RUN_ATTEMPT"]),
            "createdAt": posted["created_at"], "commentId": int(posted["id"]),
        }))
        output(artifact=artifact_name(pr, match[1]))
    output(recorded=valid)


def pages(endpoint, key=None):
    """Read complete comment/artifact/check lists, rather than a capped prefix."""
    page = 1
    while True:
        data = api(endpoint + ("&" if "?" in endpoint else "?") + f"per_page=100&page={page}")
        rows = data[key] if key else data
        yield from rows
        if len(rows) < 100:
            return
        page += 1


def status(head, state, description, check=None):
    # Each attempt owns one check run. Finishing an older run cannot
    # overwrite a newer run's aggregate, as a commit status could.
    check = os.environ.get("CHECK_RUN_ID") if check is None else check
    repo = os.environ["GITHUB_REPOSITORY"]
    payload = {
        "status": "completed", "conclusion": state,
        "output": {"title": "pre-merge", "summary": description},
    }
    if check:
        api(f"repos/{repo}/check-runs/{int(check)}", payload, method="PATCH")
    else:
        api(f"repos/{repo}/check-runs", {**payload, "name": "pre-merge", "head_sha": head})


def eligible(pr, repo, head):
    return (pr["state"] == "open" and pr["head"]["repo"] is not None
            and pr["head"]["repo"]["full_name"] == repo
            and pr["base"]["repo"]["full_name"] == repo
            and pr["base"]["ref"] == "main" and pr["head"]["sha"] == head)


def review_kind():
    path = Path(__file__).resolve().parents[1] / "pr-review/kind.py"
    spec = importlib.util.spec_from_file_location("review_kind", path)
    kind = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(kind)
    return kind


def main_update_sources(head, main):
    # No custom conflict resolution can inherit a review. Follow at most
    # ten updates, as in pr-review/prepare.sh.
    commit = head
    for _ in range(10):
        parents = run("git", "show", "-s", "--format=%P", commit).split()
        if len(parents) != 2:
            return
        first, source = parents
        if subprocess.run(["git", "merge-base", "--is-ancestor", source, main]).returncode != 0:
            return
        if run("git", "merge-tree", "--write-tree", first, source) != run("git", "rev-parse", f"{commit}^{{tree}}"):
            return
        yield first
        commit = first


def inherited_source(pr, main):
    """Select the currently evidenced dependency, separately from its verdict."""
    kind = review_kind()
    # kind also reads human requests and accepts review prefixes. The gate
    # requires the complete verdict line, as it does for attestations.
    comments = []
    for comment in pr["comments"]:
        if comment.get("negativeOnly"):
            continue  # It can block a verdict, not establish an independent review.
        body = comment["body"]
        if first_line(body).startswith("Review of ") and not VERDICT.fullmatch(first_line(body)):
            body = "Unrecognized review: " + body
        comments.append({**comment, "body": body})
    pr = {**pr, "comments": comments}
    head = pr["headRefOid"]
    verdict = kind.verdict(pr, head)
    if verdict is not None:
        return head
    decision = kind.decide(pr, "workflow_dispatch")
    if decision["kind"] == "skip" and decision.get("previous"):
        previous = decision["previous"]
        if kind.wording_problem(previous, head) is None:
            return previous
    for first in main_update_sources(head, main):
        verdict = kind.verdict(pr, first)
        if verdict is not None:
            return first


def latest_verdict(pr, head):
    latest = None
    for c in sorted(pr["comments"], key=lambda c: (c["createdAt"], c.get("id", 0))):
        match = VERDICT.fullmatch(first_line(c["body"]))
        if c["authorAssociation"] in PUSHERS and match and match[1] == head:
            latest = match[2]
    return latest


def clean_source(pr, main):
    if latest_verdict(pr, pr["headRefOid"]) == "blocking issues":
        return
    source = inherited_source(pr, main)
    verdict = latest_verdict(pr, source) if source else None
    if verdict is not None and CLEAN.fullmatch(f"Review of {source}: {verdict}"):
        return source


def inherited_review(pr, main):
    return clean_source(pr, main) is not None


def recorded_source(repo, pr, head):
    """Recover a previously trusted dependency, never a positive verdict.

    The pending job's name is assigned from successful trusted preparation,
    before PR code runs. Check metadata locates that run and attempt; neither
    arbitrary check text nor an artifact supplies the dependency identity.
    """
    records = []
    seen = set()
    for check in pages(f"repos/{repo}/commits/{head}/check-runs?check_name=pre-merge&filter=all", "check_runs"):
        match = re.fullmatch(r"pre-merge:([1-9][0-9]*):([1-9][0-9]*)", check.get("external_id") or "")
        if (check.get("name") != "pre-merge" or check.get("head_sha") != head
                or (check.get("app") or {}).get("slug") != "github-actions" or not match):
            continue
        run_id, attempt = map(int, match.groups())
        if check.get("details_url") != f"https://github.com/{repo}/actions/runs/{run_id}":
            continue
        if (run_id, attempt) in seen:
            continue
        seen.add((run_id, attempt))
        info = api(f"repos/{repo}/actions/runs/{run_id}/attempts/{attempt}")
        if (info.get("path") != ".github/workflows/pre-merge.yml" or info.get("id") != run_id
                or info.get("run_attempt") != attempt or info.get("head_branch") != "main"
                or (info.get("head_repository") or {}).get("full_name") != repo
                or info.get("event") not in ("workflow_run", "workflow_dispatch")):
            continue
        jobs = list(pages(f"repos/{repo}/actions/runs/{run_id}/attempts/{attempt}/jobs", "jobs"))
        jobs = [j for j in jobs if j.get("run_id") == run_id and j.get("run_attempt") == attempt]
        if not any(j["name"] == "prepare" and j["status"] == "completed"
                   and j["conclusion"] == "success" for j in jobs):
            continue
        dependencies = []
        for job in jobs:
            binding = DEPENDENCY_CONTEXT.fullmatch(job["name"])
            if (binding and int(binding[1]) == pr and binding[2] == head and int(binding[6]) == attempt
                    and job["status"] in ("in_progress", "completed") and job["conclusion"] != "skipped"):
                dependencies.append(binding[3])
        if len(dependencies) == 1:
            records.append((run_id, attempt, dependencies[0]))
    # A later gate may have consumed an independent review of H itself.
    return max(records)[2] if records else None


def trusted_review_run(repo, review_run, attempt=None):
    endpoint = f"repos/{repo}/actions/runs/{review_run}"
    if attempt is not None:
        endpoint += f"/attempts/{attempt}"
    info = api(endpoint)
    if (info.get("path") != ".github/workflows/claude-review.yml"
            or (info.get("head_repository") or {}).get("full_name") != repo
            or info.get("head_branch") != "main" or info.get("status") != "completed"
            or info.get("event") not in ("workflow_run", "workflow_dispatch")
            or info.get("id") != review_run or int(info.get("run_attempt", 0)) <= 0
            or (attempt is not None and info["run_attempt"] != attempt)):
        return
    return info


def current_context(repo, pr, head=None):
    """Validate a negative target against the repository's current PR data."""
    data = api(f"repos/{repo}/pulls/{pr}")
    head = data["head"]["sha"] if head is None else head
    if data["number"] == pr and eligible(data, repo, head):
        # PR base metadata is an anchor, not the current target branch tip.
        # Negative recovery needs no main snapshot or tested merge identity.
        return {"pr": pr, "head": head, "pr-base": data["base"]["sha"]}


def fetch_objects(*refs):
    # Only git objects are read; no PR checkout/configuration is executed.
    # Keep credentials out of argv, including CalledProcessError's text.
    basic = base64.b64encode(f"x-access-token:{os.environ['GH_TOKEN']}".encode()).decode()
    env = {**os.environ, "GIT_CONFIG_COUNT": "1", "GIT_CONFIG_KEY_0": "http.https://github.com/.extraheader",
           "GIT_CONFIG_VALUE_0": f"AUTHORIZATION: basic {basic}"}
    subprocess.run(["git", "fetch", "--quiet", "--no-tags", "origin", *refs], env=env, check=True)


def negative_context(repo, pr, source, attested=None, blocking_comment=None):
    """r[ci.review-revocation]: current head or a proven dependent only.

    Different event heads are never positive authorizations. Only the
    selected, currently blocked source of permitted inheritance can route
    a negative event to the live dependent head.
    """
    if attested and int(attested["pr"]) != pr:
        return
    context = current_context(repo, pr)
    if context is None:
        return
    head = context["head"]
    if head != source:
        main = current_main(repo)
        fetch_objects(main, head)
        if subprocess.run(["git", "merge-base", "--is-ancestor", source, head],
                          capture_output=True).returncode != 0:
            return
        meta = review_metadata(repo, pr, head, attested, blocking_comment, source)
        if latest_verdict(meta, source) != "blocking issues":
            return
        selected = inherited_source(meta, main)
        if selected == head:
            return
        recorded = recorded_source(repo, pr, head)
        if recorded is not None and recorded != source:
            return
        if selected != source:
            # Missing original evidence removes positive authorization, not
            # a dependency already consumed by a trusted gate. A presently
            # verified independent review or different source still wins.
            if (selected is not None or recorded != source
                    or not (review_kind().wording_problem(source, head) is None
                            or source in main_update_sources(head, main))):
                return
        # A head change while fetching or reading reviews needs a new
        # dependency decision, never a write against a different head.
        if current_context(repo, pr, head) is None:
            return
    return {**context, "source": source}


def current_main(repo):
    """Capture the target ref independently of the PR's base anchor."""
    data = api(f"repos/{repo}/git/ref/heads/main")
    commit = data["object"]
    if (data["ref"] != "refs/heads/main" or commit["type"] != "commit"
            or not re.fullmatch(r"[0-9a-f]{40}", commit["sha"])):
        raise ValueError("The target branch did not identify a main commit")
    return commit["sha"]


def blocking_comment_event(repo):
    """Read a negative-only target from GitHub's trusted event envelope."""
    if os.environ.get("GITHUB_EVENT_NAME") != "issue_comment":
        return
    event = json.loads(Path(os.environ["GITHUB_EVENT_PATH"]).read_text())
    if (event.get("repository", {}).get("full_name") != repo
            or event.get("action") not in ("created", "edited")):
        return
    issue, comment = event["issue"], event["comment"]
    match = VERDICT.fullmatch(first_line(comment["body"]))
    if (not issue.get("pull_request") or not match or match[2] != "blocking issues"
            or (comment["author_association"] not in PUSHERS and comment["user"]["login"] not in BOT)
            or int(issue["number"]) <= 0 or int(comment["id"]) <= 0):
        return
    return {"pr": int(issue["number"]), "head": match[1], "comment": comment}


def posted_target(repo, review_run):
    """r[ci.review-revocation]: recover a target without any uploaded artifact.

    GitHub persists the post job's name from main's trusted preparation
    outputs, including the actual post destination and attempt. PR code,
    reviewer text, logs and artifact names cannot supply this context.
    It can only revoke: it never stands in for a posted authorization.
    """
    event_attempt = os.environ.get("REVIEW_ATTEMPT")
    info = trusted_review_run(repo, review_run, int(event_attempt) if event_attempt else None)
    if info is None:
        return
    attempt = info["run_attempt"]
    targets = set()
    for job in pages(f"repos/{repo}/actions/runs/{review_run}/attempts/{attempt}/jobs", "jobs"):
        match = POST_CONTEXT.fullmatch(job["name"])
        if (match and int(match[1]) > 0 and int(match[3]) == attempt
                and job["run_id"] == review_run and job["run_attempt"] == attempt
                and job["status"] == "completed" and job["conclusion"] != "skipped"):
            targets.add((int(match[1]), match[2]))
    # There is one non-matrix post job. Reject ambiguous or absent context.
    if len(targets) != 1:
        return
    pr, head = targets.pop()
    return {"pr": pr, "source": head}


def revocation_context(repo, review_run):
    target = posted_target(repo, review_run)
    return negative_context(repo, target["pr"], target["source"]) if target else None


def posted_review(repo, review_run, artifact_id=None):
    # An overall failure/cancellation may follow a valid posted verdict.
    info = trusted_review_run(repo, review_run)
    if info is None:
        return
    artifacts = pages(f"repos/{repo}/actions/runs/{review_run}/artifacts", "artifacts")
    artifact = next((a for a in artifacts if not a["expired"]
                     and a["name"].startswith("posted-review-")
                     and (artifact_id is None or a["id"] == artifact_id)), None)
    if artifact is None:
        return
    with tempfile.TemporaryDirectory() as temp:
        subprocess.run(["gh", "run", "download", str(review_run), "--repo", repo,
                        "-n", artifact["name"], "-D", temp], check=True)
        review = json.loads(Path(temp, "review.json").read_text())
    if review["attempt"] != info["run_attempt"]:
        return
    match = VERDICT.fullmatch(review["body"].splitlines()[0])
    if (match is None or match[1] != review["head"] or int(review["commentId"]) <= 0
            or artifact["name"] != artifact_name(review["pr"], review["head"])):
        raise ValueError("Attestation does not identify its posted verdict")
    return review


def review_metadata(repo, pr, head, attested=None, blocking_comment=None, source=None):
    """r[ci.current-review]: actual comment order and verified bot provenance.

    Names narrow the artifact query to this PR/head; each candidate still
    needs the trusted workflow, current attempt and matching posted comment.
    A bot review awaiting its attestation cannot authorize a green check.
    """
    records = {}
    heads = {head} | ({attested["head"]} if attested else set())
    if source:
        heads.add(source)
    if blocking_comment:
        heads.add(VERDICT.fullmatch(first_line(blocking_comment["body"]))[1])
    for sha in sorted(heads):
        name = artifact_name(pr, sha)
        try:
            artifacts = list(pages(f"repos/{repo}/actions/artifacts?name={name}", "artifacts"))
        except Exception:
            artifacts = []
        for artifact in artifacts:
            if artifact["expired"]:
                continue
            try:
                review = posted_review(repo, artifact["workflow_run"]["id"], artifact["id"])
            except Exception:
                # An unavailable artifact grants nothing. Keep reading the
                # actual comments: unattested bot verdicts below only block.
                continue
            if review and int(review["pr"]) == pr and review["head"] == sha:
                records[int(review["commentId"])] = review
    if attested:
        records[int(attested["commentId"])] = attested
    comments = []
    matched = set()
    for c in pages(f"repos/{repo}/issues/{pr}/comments"):
        association = c["author_association"]
        match = VERDICT.fullmatch(first_line(c["body"]))
        body = c["body"]
        negative_only = False
        if c["user"]["login"] in BOT or association not in PUSHERS:
            record = records.get(c["id"])
            if (record and c["user"]["login"] in BOT
                    and record["body"].rstrip("\n") == body.rstrip("\n")
                    and record["createdAt"] == c["created_at"]):
                association = "COLLABORATOR"
                matched.add(c["id"])
            elif match and c["user"]["login"] in BOT:
                # Includes edits and an in-progress or expired attestation.
                # Never turn arbitrary bot text into a clean authorization.
                # Source-head negatives must remain visible to inheritance
                # even before its dependency has been selected.
                association = "COLLABORATOR"
                body = f"Review of {match[1]}: blocking issues"
                negative_only = True
            else:
                continue
        comments.append({"body": body, "authorAssociation": association,
                         "createdAt": c["created_at"], "id": c["id"], "negativeOnly": negative_only})
    for comment, record in records.items():
        if comment not in matched:
            # API lag, deletion or editing cannot erase a signed blocking
            # verdict, nor let a missing clean comment authorize success.
            comments.append({"body": f"Review of {record['head']}: blocking issues",
                             "authorAssociation": "COLLABORATOR", "id": comment,
                             "createdAt": record["createdAt"]})
    if blocking_comment and not any(c["id"] == blocking_comment["id"] for c in comments):
        # A genuine blocking event is evidence of publication even if the
        # comment list lags. Fresh API text wins for edits; a later clean
        # review still supersedes this event in the ordinary posted order.
        event_head = VERDICT.fullmatch(first_line(blocking_comment["body"]))[1]
        comments.append({"body": f"Review of {event_head}: blocking issues", "authorAssociation": "COLLABORATOR",
                         "id": blocking_comment["id"], "createdAt": blocking_comment["created_at"],
                         "negativeOnly": blocking_comment["user"]["login"] in BOT})
    comments.sort(key=lambda c: (c["createdAt"], c["id"]))
    return {"headRefOid": head, "comments": comments}


def authorization_source(repo, pr, head, main, attested=None, manual=False, blocking_comment=None):
    """r[ci.current-review]: one authorization decision for every entry/report."""
    data = api(f"repos/{repo}/pulls/{pr}")
    if data["number"] != pr or not eligible(data, repo, head):
        return
    if attested and (int(attested["pr"]) != pr or (not manual and attested["head"] != head)):
        return
    meta = review_metadata(repo, pr, head, attested, blocking_comment)
    if not manual:
        # Automatic events never inherit a review of another head.
        latest = latest_verdict(meta, head)
        return head if latest is not None and latest != "blocking issues" else None
    return clean_source(meta, main)


def authorized(repo, pr, head, main, attested=None, manual=False, blocking_comment=None):
    return authorization_source(repo, pr, head, main, attested, manual, blocking_comment) is not None


def invalidate(head):
    """Revoke completed and running checks; an older reporter rechecks too."""
    repo = os.environ["GITHUB_REPOSITORY"]
    for check in pages(f"repos/{repo}/commits/{head}/check-runs?check_name=pre-merge&filter=all", "check_runs"):
        if check["name"] == "pre-merge" and (check.get("app") or {}).get("slug") == "github-actions":
            status(head, "failure", "The current review does not authorize this gate", str(check["id"]))


def prepare():
    repo = os.environ["GITHUB_REPOSITORY"]
    manual = os.environ.get("PR_INPUT", "") not in ("", "0")
    manual_data = None
    if manual:
        manual_data = api(f"repos/{repo}/pulls/{int(os.environ['PR_INPUT'])}")
        manual_head = manual_data["head"]["sha"]
        if eligible(manual_data, repo, manual_head):
            # Even an invalid review-run input must fail the known head's
            # aggregate, rather than leave an earlier green check untouched.
            output(head=manual_head, pr=int(os.environ["PR_INPUT"]), **{"pr-base": manual_data["base"]["sha"]})
    attested = None
    if os.environ.get("REVIEW_RUN"):
        review_run = int(os.environ["REVIEW_RUN"])
        error = None
        try:
            attested = posted_review(repo, review_run)
        except Exception as failure:
            error = failure
        if attested is None:
            context = revocation_context(repo, review_run)
            if context and (not manual or (context["pr"] == int(os.environ["PR_INPUT"])
                                          and context["head"] == manual_data["head"]["sha"])):
                output(**context, recovered=True, revoked=True, relevant=False)
                raise ValueError("Missing authorization attestation; recovered a revocation-only target")
            if error is not None:
                raise error
    comment_event = os.environ.get("GITHUB_EVENT_NAME") == "issue_comment"
    comment_target = None
    if comment_event:
        comment_target = blocking_comment_event(repo)
        if comment_target is None:
            return
        pr, head = comment_target["pr"], comment_target["head"]
    elif manual:
        pr = int(os.environ["PR_INPUT"])
        head = manual_data["head"]["sha"]
        if os.environ.get("REVIEW_RUN") and attested is None:
            raise ValueError("No trusted posted verdict for review-run")
    elif attested:
        pr, head = int(attested["pr"]), attested["head"]
    else:
        return
    invalidation = comment_event or (attested and not CLEAN.fullmatch(attested["body"].splitlines()[0]))
    if invalidation:
        source = comment_target["head"] if comment_target else attested["head"]
        if attested and int(attested["pr"]) != pr:
            raise ValueError("The review-run does not target the requested PR")
        context = negative_context(repo, pr, source, attested,
                                   comment_target["comment"] if comment_target else None)
        if context is None:
            return
        try:
            if context["head"] == source and authorized(repo, pr, source, None, attested,
                    blocking_comment=comment_target["comment"] if comment_target else None):
                return
        except Exception:
            output(**context, revoked=True, relevant=False)
            raise
        output(**context, revoked=True, relevant=False)
        raise ValueError("The current review does not authorize this gate")
    data = api(f"repos/{repo}/pulls/{pr}")
    if data["number"] != pr or not eligible(data, repo, head):
        print("Review is stale, closed, from a fork, or not against main")
        return
    # Positive source completions still cannot start a dependent head's gate.
    output(head=head, pr=pr, **{"pr-base": data["base"]["sha"]})
    main = current_main(repo)
    output(base=main)
    # Only read git objects in the trusted checkout. GitHub's merge ref is
    # the same merge pre-approval checks out; never test the head on its own.
    fetch_objects(f"refs/pull/{pr}/merge")
    merge = run("git", "rev-parse", "FETCH_HEAD")
    parents = run("git", "show", "-s", "--format=%P", merge).split()
    if len(parents) != 2 or parents[1] != head or parents[0] != main:
        raise ValueError("GitHub's merge ref does not yet match the current head and main; rerun")
    # The verified merge brought this snapshot's objects into the trusted
    # checkout, including the main commit used by structural inheritance.
    source = authorization_source(repo, pr, head, main, attested, manual)
    if source is None:
        output(revoked=True)
        raise ValueError("The current review does not authorize this gate")
    names = subprocess.check_output(["git", "diff", "--no-ext-diff", "--no-textconv", "--no-renames",
                                     "--name-only", "-z", f"{parents[0]}...{head}"])
    jobs = selected(names.decode().split("\0"))
    dependency = DEPENDENCY.format(pr=pr, head=head, source=source, base=main, merge=merge,
                                   attempt=int(os.environ.get("GITHUB_RUN_ATTEMPT", "1")))
    output(merge=merge, base=parents[0], source=source, dependency=dependency, relevant=any(jobs.values()), **jobs)
    print(json.dumps({"pr": pr, "head": head, "merge": merge, "jobs": jobs}, indent=2))


def report_blocked(repo, context, attested=None, blocking_comment=None):
    """Publish only revocation; a direct event may have been superseded."""
    head = context["head"]
    try:
        if head == context["source"] and authorized(repo, context["pr"], head, None, attested,
                                                    blocking_comment=blocking_comment):
            return
    except Exception:
        try:
            invalidate(head)
        finally:
            status(head, "failure", "Blocking review ordering could not be verified")
        raise
    try:
        invalidate(head)
    finally:
        status(head, "failure", "The current blocking review revokes this gate")
    sys.exit(1)


def report_unavailable(context):
    # A missing attestation can only fail a verified negative target.
    head = context["head"]
    try:
        invalidate(head)
    finally:
        status(head, "failure", "Review authorization unavailable; recovered target revoked")
    sys.exit(1)


def finish():
    """r[ci.review-revocation]: recheck publication and revoke stale success."""
    jobs = json.loads(os.environ["NEEDS"])
    prepared = jobs["prepare"]["outputs"]
    head = prepared.get("head")
    repo = os.environ["GITHUB_REPOSITORY"]
    if os.environ.get("GITHUB_EVENT_NAME") == "issue_comment":
        # Checkout or preparation may have failed before any outputs. Only
        # the trusted event identifies this negative target; it cannot run
        # slow work or publish success. Revalidate eligibility and ordering.
        target = blocking_comment_event(repo)
        context = negative_context(repo, target["pr"], target["head"], blocking_comment=target["comment"]) if target else None
        if context:
            report_blocked(repo, context, blocking_comment=target["comment"])
        return
    review_run = os.environ.get("REVIEW_RUN")
    if review_run:
        try:
            attested = posted_review(repo, int(review_run))
        except Exception:
            attested = None  # The known-head or independent recovery path below fails closed.
        manual_pr = os.environ.get("PR_INPUT", "")
        if (attested and not CLEAN.fullmatch(first_line(attested["body"]))
                and (manual_pr in ("", "0") or int(manual_pr) == int(attested["pr"]))):
            context = negative_context(repo, int(attested["pr"]), attested["head"], attested)
            if context:
                report_blocked(repo, context, attested)
            return
        if attested is None:
            try:
                target = posted_target(repo, int(review_run))
            except Exception:
                target = None
            if target and (manual_pr in ("", "0") or int(manual_pr) == target["pr"]):
                context = negative_context(repo, target["pr"], target["source"])
                if context:
                    report_unavailable(context)
                return  # An unrelated or recleaned source cannot revoke H.
    if not head:
        # Preparation may have failed/cancelled before writing outputs.
        # Retry recovery from job metadata, never from PR-controlled data.
        context = None
        manual_pr = os.environ.get("PR_INPUT", "")
        if manual_pr not in ("", "0"):
            # An explicit permissioned dispatch targets this PR, even if its
            # review-run input names a different one. Never revoke that one.
            context = current_context(repo, int(manual_pr))
        elif os.environ.get("REVIEW_RUN"):
            context = revocation_context(repo, int(os.environ["REVIEW_RUN"]))
        if context:
            prepared = {**context, "recovered": "true"}
            head = context["head"]
    if not head:
        return
    if prepared.get("recovered") == "true":
        # Preparation's target may have gained an independent review or a
        # different dependency. Recompute against the current PR and source.
        context = negative_context(repo, int(prepared["pr"]), prepared.get("source", head))
        if context is None:
            return
        report_unavailable(context)
    relevant = prepared.get("relevant") == "true"
    good = (jobs["prepare"]["result"] == "success" and jobs["pending"]["result"] == "success"
            and jobs["slow"]["result"] == ("success" if relevant else "skipped"))

    def current():
        repo = os.environ["GITHUB_REPOSITORY"]
        review_run = os.environ.get("REVIEW_RUN")
        attested = posted_review(repo, int(review_run)) if review_run else None
        if (review_run and attested is None) or (not prepared.get("base") and prepared.get("revoked") != "true"):
            return False
        return authorized(repo, int(prepared["pr"]), head, prepared.get("base"), attested,
                          os.environ.get("PR_INPUT", "") not in ("", "0"))

    try:
        valid = current()
        if valid and good:
            status(head, "success", "Relevant slow checks passed")
            # Close the publication race: if a blocking completion revoked
            # checks between our read and write, never leave this write green.
            valid = current()
            if valid:
                return
        if valid and prepared.get("revoked") == "true" and not os.environ.get("CHECK_RUN_ID"):
            return  # A newer clean verdict superseded the blocking event.
    except Exception:
        try:
            invalidate(head)
        finally:
            status(head, "failure", "Review authorization could not be verified")
        raise
    if not valid:
        try:
            invalidate(head)
        finally:
            status(head, "failure", "The current review does not authorize this gate")
    else:
        status(head, "failure", "Slow checks failed or were cancelled")
    sys.exit(1)


if __name__ == "__main__":
    {"record": record, "prepare": prepare, "finish": finish}[sys.argv[1]]()
