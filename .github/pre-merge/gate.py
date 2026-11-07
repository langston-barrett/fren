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


def inherited_review(pr, main):
    """Use pr-review's structural rules on already authenticated comments."""
    path = Path(__file__).resolve().parents[1] / "pr-review/kind.py"
    spec = importlib.util.spec_from_file_location("review_kind", path)
    kind = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(kind)
    # kind also reads human requests and accepts review prefixes. The gate
    # requires the complete verdict line, as it does for attestations.
    comments = []
    for comment in pr["comments"]:
        body = comment["body"]
        if first_line(body).startswith("Review of ") and not VERDICT.fullmatch(first_line(body)):
            body = "Unrecognized review: " + body
        comments.append({**comment, "body": body})
    pr = {**pr, "comments": comments}
    head = pr["headRefOid"]
    verdict = kind.verdict(pr, head)
    if verdict is not None:
        return CLEAN.fullmatch(f"Review of {head}: {verdict}") is not None
    decision = kind.decide(pr, "workflow_dispatch")
    if decision["kind"] == "skip" and decision.get("previous"):
        previous = decision["previous"]
        verdict = kind.verdict(pr, previous)
        # decide looks at reviews before the skip request. Its source must
        # still be clean now, including rereviews posted after that request.
        return (verdict is not None and CLEAN.fullmatch(f"Review of {previous}: {verdict}") is not None
                and kind.wording_problem(previous, head) is None)
    # The same pure-main-update test as pr-review/prepare.sh. No custom
    # conflict resolution can inherit a review. Follow at most ten updates.
    commit = head
    for _ in range(10):
        parents = run("git", "show", "-s", "--format=%P", commit).split()
        if len(parents) != 2:
            return False
        first, source = parents
        if subprocess.run(["git", "merge-base", "--is-ancestor", source, main]).returncode != 0:
            return False
        if run("git", "merge-tree", "--write-tree", first, source) != run("git", "rev-parse", f"{commit}^{{tree}}"):
            return False
        verdict = kind.verdict(pr, first)
        if verdict is not None:
            return CLEAN.fullmatch(f"Review of {first}: {verdict}") is not None
        commit = first
    return False


def posted_review(repo, review_run, artifact_id=None):
    info = api(f"repos/{repo}/actions/runs/{review_run}")
    # Only main's completed review workflow attests bot reviews. An overall
    # failure can follow a valid posted verdict (for example probe cleanup).
    if (info["path"] != ".github/workflows/claude-review.yml"
            or info["head_repository"]["full_name"] != repo
            or info["head_branch"] != "main" or info["status"] != "completed"):
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


def review_metadata(repo, pr, head, attested=None):
    """r[ci.current-review]: actual comment order and verified bot provenance.

    Names narrow the artifact query to this PR/head; each candidate still
    needs the trusted workflow, current attempt and matching posted comment.
    A bot review awaiting its attestation cannot authorize a green check.
    """
    records = {}
    heads = {head} | ({attested["head"]} if attested else set())
    for sha in sorted(heads):
        name = artifact_name(pr, sha)
        for artifact in pages(f"repos/{repo}/actions/artifacts?name={name}", "artifacts"):
            if artifact["expired"]:
                continue
            review = posted_review(repo, artifact["workflow_run"]["id"], artifact["id"])
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
        if c["user"]["login"] in BOT or association not in PUSHERS:
            record = records.get(c["id"])
            if (record and c["user"]["login"] in BOT
                    and record["body"].rstrip("\n") == body.rstrip("\n")
                    and record["createdAt"] == c["created_at"]):
                association = "COLLABORATOR"
                matched.add(c["id"])
            elif match and match[1] in heads and c["user"]["login"] in BOT:
                # Includes edits and an in-progress or expired attestation.
                # Never turn arbitrary bot text into a clean authorization.
                association = "COLLABORATOR"
                body = f"Review of {match[1]}: blocking issues"
            else:
                continue
        comments.append({"body": body, "authorAssociation": association,
                         "createdAt": c["created_at"], "id": c["id"]})
    for comment, record in records.items():
        if comment not in matched:
            # API lag, deletion or editing cannot erase a signed blocking
            # verdict, nor let a missing clean comment authorize success.
            comments.append({"body": f"Review of {record['head']}: blocking issues",
                             "authorAssociation": "COLLABORATOR", "id": comment,
                             "createdAt": record["createdAt"]})
    comments.sort(key=lambda c: (c["createdAt"], c["id"]))
    return {"headRefOid": head, "comments": comments}


def authorized(repo, pr, head, main, attested=None, manual=False):
    """r[ci.current-review]: one authorization decision for every entry/report."""
    data = api(f"repos/{repo}/pulls/{pr}")
    if not eligible(data, repo, head):
        return False
    if attested and (int(attested["pr"]) != pr or (not manual and attested["head"] != head)):
        return False
    meta = review_metadata(repo, pr, head, attested)
    if not manual:
        # Automatic events never inherit a review of another head.
        latest = None
        for comment in meta["comments"]:
            verdict = VERDICT.fullmatch(first_line(comment["body"]))
            if verdict and verdict[1] == head:
                latest = verdict[2]
        return latest is not None and latest != "blocking issues"
    return inherited_review(meta, main)


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
            output(head=manual_head, pr=int(os.environ["PR_INPUT"]), base=manual_data["base"]["sha"])
    attested = posted_review(repo, int(os.environ["REVIEW_RUN"])) if os.environ.get("REVIEW_RUN") else None
    comment_event = os.environ.get("GITHUB_EVENT_NAME") == "issue_comment"
    if comment_event:
        event = json.loads(Path(os.environ["GITHUB_EVENT_PATH"]).read_text())
        c = event["comment"]
        match = VERDICT.fullmatch(first_line(c["body"]))
        if (not event["issue"].get("pull_request") or not match or match[2] != "blocking issues"
                or (c["author_association"] not in PUSHERS and c["user"]["login"] not in BOT)):
            return
        pr = int(event["issue"]["number"])
        head = match[1]
    elif manual:
        pr = int(os.environ["PR_INPUT"])
        head = manual_data["head"]["sha"]
        if os.environ.get("REVIEW_RUN") and attested is None:
            raise ValueError("No trusted posted verdict for review-run")
    elif attested:
        pr, head = int(attested["pr"]), attested["head"]
    else:
        return
    data = api(f"repos/{repo}/pulls/{pr}")
    if not eligible(data, repo, head):
        print("Review is stale, closed, from a fork, or not against main")
        return
    main = data["base"]["sha"]
    # An old blocking completion must not invalidate a newer clean review.
    invalidation = comment_event or (attested and not CLEAN.fullmatch(attested["body"].splitlines()[0]))
    if invalidation:
        try:
            if authorized(repo, pr, head, main, attested):
                return
        except Exception:
            output(head=head, pr=pr, base=main, revoked=True)
            raise
    # Report a head even when its latest verdict is blocking or authorization
    # fails. The always reporter must revoke any earlier green check.
    output(head=head, pr=pr, base=main)
    if invalidation or not authorized(repo, pr, head, main, attested, manual):
        output(revoked=True)
        raise ValueError("The current review does not authorize this gate")
    # Only read git objects in the trusted checkout. GitHub's merge ref is
    # the same merge pre-approval checks out; never test the head on its own.
    basic = base64.b64encode(f"x-access-token:{os.environ['GH_TOKEN']}".encode()).decode()
    # Keep credentials out of argv: CalledProcessError prints argv on a
    # failed fetch, including an encoded token if it was passed with -c.
    fetch_env = {**os.environ, "GIT_CONFIG_COUNT": "1",
                 "GIT_CONFIG_KEY_0": "http.https://github.com/.extraheader",
                 "GIT_CONFIG_VALUE_0": f"AUTHORIZATION: basic {basic}"}
    subprocess.run(["git", "fetch", "--quiet", "--no-tags", "origin", f"refs/pull/{pr}/merge"],
                   env=fetch_env, check=True)
    merge = run("git", "rev-parse", "FETCH_HEAD")
    parents = run("git", "show", "-s", "--format=%P", merge).split()
    if len(parents) != 2 or parents[1] != head or parents[0] != data["base"]["sha"]:
        raise ValueError("GitHub's merge ref does not yet match the current head and main; rerun")
    names = subprocess.check_output(["git", "diff", "--no-ext-diff", "--no-textconv", "--no-renames",
                                     "--name-only", "-z", f"{parents[0]}...{head}"])
    jobs = selected(names.decode().split("\0"))
    output(merge=merge, base=parents[0], relevant=any(jobs.values()), **jobs)
    print(json.dumps({"pr": pr, "head": head, "merge": merge, "jobs": jobs}, indent=2))


def finish():
    """r[ci.review-revocation]: recheck publication and revoke stale success."""
    jobs = json.loads(os.environ["NEEDS"])
    prepared = jobs["prepare"]["outputs"]
    head = prepared.get("head")
    if not head:
        return
    relevant = prepared.get("relevant") == "true"
    good = (jobs["prepare"]["result"] == "success" and jobs["pending"]["result"] == "success"
            and jobs["slow"]["result"] == ("success" if relevant else "skipped"))

    def current():
        repo = os.environ["GITHUB_REPOSITORY"]
        review_run = os.environ.get("REVIEW_RUN")
        attested = posted_review(repo, int(review_run)) if review_run else None
        if review_run and attested is None:
            return False
        return authorized(repo, int(prepared["pr"]), head, prepared["base"], attested,
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
