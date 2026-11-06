"""Trusted preparation and head-status reporting for pre-merge.

Only the review's post job produces posted-review, after posting a checked
clean verdict. A workflow_run of pr-review carries main's SHA, not the PR
head: the attestation identifies that head without trusting branch names,
comments by other workflows, or artifacts from jobs that run PR code.
"""

import base64
from datetime import datetime, timezone
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

JOBS = ("own-spec-agreement", "methods-agree", "coverage", "fuzz-frontends")
CLEAN = re.compile(r"Review of ([0-9a-f]{40}): no blocking issues(?: \((?:fixes|rebase) only\))?")


def selected(paths):
    """Conservative filters, alongside the reasons for each input set."""
    paths = tuple(paths)
    # Changes to the shared build/toolchain, runner action, or gate can
    # affect every job. Include scripts: Lake and the jobs invoke them.
    common = any(p in ("lakefile.lean", "lake-manifest.json", "lean-toolchain")
                 or p.startswith(("scripts/", ".github/actions/", ".github/pre-merge/"))
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


def record():
    """Called by the trusted post job only after gh pr comment succeeds."""
    text = Path(os.environ["RUNNER_TEMP"], "comment.md").read_text()
    match = CLEAN.fullmatch(text.splitlines()[0])
    clean = match is not None and match[1] == os.environ["HEAD"]
    output(clean=clean)
    if clean:
        directory = Path(os.environ["RUNNER_TEMP"], "posted-review")
        directory.mkdir()
        (directory / "review.json").write_text(json.dumps({
            "pr": int(os.environ.get("POST") or os.environ["PR"]),
            "head": match[1], "body": text, "attempt": int(os.environ["GITHUB_RUN_ATTEMPT"]),
            "createdAt": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        }))


def status(head, state, description):
    # Each attempt owns one check run. Finishing an older run cannot
    # overwrite a newer run's aggregate, as a commit status could.
    check = os.environ.get("CHECK_RUN_ID")
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


def inherited_review(pr, main, attested=None):
    """Manual-only: the coordinator confirms prose and the review skip;
    reuse pr-review's exact comment rules and structural checks here.
    A current blocking review always wins over an inherited clean one.
    """
    path = Path(__file__).resolve().parents[1] / "pr-review/kind.py"
    spec = importlib.util.spec_from_file_location("review_kind", path)
    kind = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(kind)
    head = pr["headRefOid"]
    if attested is not None:
        # Only posted_review's trusted artifact can authorize a bot's
        # clean verdict. Arbitrary NONE-associated comments never can.
        for c in pr["comments"]:
            first = c["body"].strip().splitlines()[0] if c["body"].strip() else ""
            author = c.get("author") or {}
            trusted = (c.get("authorAssociation") in kind.PUSHERS or
                       author.get("login") in ("github-actions", "github-actions[bot]"))
            if (trusted and c["createdAt"] >= attested["createdAt"] and
                    first in (f"Review of {head}: blocking issues",
                              f"Review of {attested['head']}: blocking issues")):
                return False
        pr = {**pr, "comments": [*pr["comments"], {
            "body": attested["body"], "createdAt": attested["createdAt"],
            "authorAssociation": "COLLABORATOR",
        }]}
    verdict = kind.verdict(pr, head)
    if verdict is not None:
        return CLEAN.fullmatch(f"Review of {head}: {verdict}") is not None
    decision = kind.decide(pr, "workflow_dispatch")
    if decision["kind"] == "skip" and decision.get("previous"):
        return kind.wording_problem(decision["previous"], head) is None
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


def posted_review(repo, review_run, detail=False):
    info = api(f"repos/{repo}/actions/runs/{review_run}")
    # Manual trials on a branch do not attest a review by main's workflow.
    if (info["path"] != ".github/workflows/claude-review.yml"
            or info["head_repository"]["full_name"] != repo
            or info["head_branch"] != "main" or info["status"] != "completed"):
        print("No completed trusted review run")
        return
    # The posted verdict is the authority. A failed probe or post-action
    # cleanup can fail the overall run even after a clean review was posted.
    with tempfile.TemporaryDirectory() as temp:
        # No artifact (blocking verdict, withheld review, or skip) starts no
        # gate. Download only the post job's artifact, never a probe's.
        artifacts = api(f"repos/{repo}/actions/runs/{review_run}/artifacts?per_page=100")["artifacts"]
        if not any(a["name"] == "posted-review" and not a["expired"] for a in artifacts):
            print("The review workflow posted no clean verdict")
            return
        subprocess.run(["gh", "run", "download", str(review_run), "--repo", repo,
                        "-n", "posted-review", "-D", temp], check=True)
        review = json.loads(Path(temp, "review.json").read_text())
    if review["attempt"] != info["run_attempt"]:
        print("The attestation belongs to an older review attempt")
        return
    head, pr = review["head"], int(review["pr"])
    match = CLEAN.fullmatch(review["body"].splitlines()[0])
    if match is None or match[1] != head:
        raise ValueError("Attestation is not a clean verdict of its head")
    return review if detail else (pr, head)


def prepare():
    repo = os.environ["GITHUB_REPOSITORY"]
    manual = os.environ.get("PR_INPUT", "")
    if manual and manual != "0":
        pr = int(manual)
        data = api(f"repos/{repo}/pulls/{pr}")
        head = data["head"]["sha"]
    else:
        review = posted_review(repo, int(os.environ["REVIEW_RUN"]))
        if review is None:
            return
        pr, head = review
        data = api(f"repos/{repo}/pulls/{pr}")
    if not eligible(data, repo, head):
        print("Review is stale, closed, from a fork, or not against main")
        return
    # Output the head first, so an error fetching/diffing the merge still
    # reports a failing aggregate on the intended head.
    output(head=head, pr=pr)
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
    if manual and manual != "0":
        meta = json.loads(run("gh", "pr", "view", str(pr), "--repo", repo,
                              "--json", "headRefOid,comments"))
        attested = None
        if os.environ.get("REVIEW_RUN"):
            attested = posted_review(repo, int(os.environ["REVIEW_RUN"]), detail=True)
            if attested is None or int(attested["pr"]) != pr:
                raise ValueError("The attested review is not of this PR")
        if meta["headRefOid"] != head or not inherited_review(meta, parents[0], attested):
            raise ValueError("Manual gate requires a clean current or valid inherited review")
    names = subprocess.check_output(["git", "diff", "--no-ext-diff", "--no-textconv", "--no-renames",
                                     "--name-only", "-z", f"{parents[0]}...{head}"])
    jobs = selected(names.decode().split("\0"))
    output(merge=merge, base=parents[0], relevant=any(jobs.values()), **jobs)
    print(json.dumps({"pr": pr, "head": head, "merge": merge, "jobs": jobs}, indent=2))


def finish():
    jobs = json.loads(os.environ["NEEDS"])
    head = jobs["prepare"]["outputs"].get("head")
    if not head:
        return
    # success includes the no-relevant-job case; a failure, cancellation,
    # or unexpected skip of any selected job fails the aggregate.
    relevant = jobs["prepare"]["outputs"].get("relevant") == "true"
    good = (jobs["prepare"]["result"] == "success" and jobs["pending"]["result"] == "success"
            and jobs["slow"]["result"] == ("success" if relevant else "skipped"))
    status(head, "success" if good else "failure", "Relevant slow checks passed" if good else "Slow checks failed or were cancelled")
    if not good:
        sys.exit(1)


if __name__ == "__main__":
    {"record": record, "prepare": prepare, "finish": finish}[sys.argv[1]]()
