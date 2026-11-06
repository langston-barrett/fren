"""Resolve a completed review or failing pre-merge to a current agent head."""
import io
import importlib.util
import os
from pathlib import Path
import re
import subprocess
import zipfile

from common import MAX_ROUNDS, LIMIT, MODELS, api, comments, output, prompt, rounds_done, trusted

REVIEW = re.compile(r"Review of ([0-9a-f]{40}): (no blocking issues|blocking issues)(?:\s|$)")


def reviewed_pr(repo, run_id):
    # A pr-review workflow_run itself has head_branch=main and no PRs.
    # Its context artifact was uploaded by the trusted prepare job, which
    # runs no PR code. Read only log.txt from it; never extract its files.
    artifacts = api(f"repos/{repo}/actions/runs/{run_id}/artifacts")["artifacts"]
    contexts = [a for a in artifacts if re.fullmatch(r"context-\d+", a["name"]) and not a["expired"]]
    if len(contexts) != 1:
        return None
    artifact = contexts[0]
    pr = artifact["name"].removeprefix("context-")
    info = api(f"repos/{repo}/pulls/{pr}")
    if not agent_pr(info, repo):
        return None
    archive = subprocess.check_output([
        "gh", "api", f"repos/{repo}/actions/artifacts/{artifact['id']}/zip"])
    with zipfile.ZipFile(io.BytesIO(archive)) as z:
        line = z.read("log.txt").decode().splitlines()[0]
    if line != f"commit {info['head']['sha']}":
        return None
    return info


def agent_pr(info, repo):
    head = info["head"]
    return (info["state"] == "open" and not info["draft"] and
            head.get("repo") is not None and head["repo"]["full_name"] == repo and
            re.fullmatch(r"agent/\d+-(luna|terra)-(low|medium|high)", head["ref"]) is not None)


def review_bot(item):
    return (item.get("user", {}).get("login") == "github-actions[bot]" and
            item["user"].get("type") == "Bot")


def generated_review(repo, run_id, pr, head):
    """Recover trusted automation output, not arbitrary bot-comment text.

    GitHub gives its bot author_association=NONE. Human comments still
    require the trusted associations. For automation, the completed run's
    context has already identified this repository's current agent head;
    revalidate its review artifact with the workflow's own checker and
    require the posted bot comment to match that exact output.
    """
    artifacts = api(f"repos/{repo}/actions/runs/{run_id}/artifacts")["artifacts"]
    reviews = [a for a in artifacts if a["name"] == f"review-{pr}" and not a["expired"]]
    if len(reviews) != 1:
        return None
    archive = subprocess.check_output([
        "gh", "api", f"repos/{repo}/actions/artifacts/{reviews[0]['id']}/zip"])
    with zipfile.ZipFile(io.BytesIO(archive)) as z:
        raw = z.read("review.md").decode().strip()
        names = set(z.read("names.txt").decode().splitlines()) - {""}
    path = Path(__file__).resolve().parent.parent / "pr-review/check.py"
    spec = importlib.util.spec_from_file_location("review_check", path)
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    first = raw.splitlines()[0] if raw else ""
    if first.endswith("(fixes only)"):
        kind = "fixes"
    elif first.endswith("(rebase only)"):
        kind = "rebase"
    else:
        kind = "full"
    body, ok = checker.comment(raw, head, kind,
                               f"https://github.com/{repo}/actions/runs/{run_id}",
                               names, checker.hashed_names())
    return body if ok else None


def main():
    env, repo = os.environ, os.environ["REPO"]
    run_id = env["RUN_ID"]
    if env["RUN_NAME"] == "pr-review":
        info = reviewed_pr(repo, run_id)
        if info is None:
            return output(mode="skip")
    else:
        prs = api(f"repos/{repo}/pulls?state=open&head={repo.split('/')[0]}:{env['RUN_BRANCH']}")
        if len(prs) != 1:
            return output(mode="skip")
        info = prs[0]
        if not agent_pr(info, repo) or info["head"]["sha"] != env["RUN_SHA"]:
            return output(mode="skip")
    pr, head, branch = str(info["number"]), info["head"]["sha"], info["head"]["ref"]
    thread = api(f"repos/{repo}/issues/{pr}/comments", pages=True)
    if env["RUN_NAME"] == "pr-review":
        generated = generated_review(repo, run_id, pr, head) if any(
            review_bot(c) and REVIEW.match(c["body"]) for c in thread) else None
        reviews = []
        for item in thread:
            if not REVIEW.match(item["body"]):
                continue
            if trusted(item):
                reviews.append(item["body"])
            elif review_bot(item) and generated and item["body"].strip() == generated.strip():
                reviews.append(generated)
        if not reviews:
            return output(mode="skip")
        review = reviews[-1]
        match = REVIEW.match(review)
        if match.group(1) != head or match.group(2) != "blocking issues":
            return output(mode="skip")
        what = ("The review of your current head has blocking issues. Fix every [blocking] "
                "finding at every instance, and the small [non-blocking] findings. If you "
                "disagree, explain why in your comment.\n\n" + review)
    else:
        log = subprocess.check_output([
            "gh", "run", "view", run_id, "-R", repo, "--log-failed"], text=True)
        lines = [line for line in log.splitlines() if re.search(r"error:|FAIL|crashed|warning:", line)]
        what = "Your current head's pre-merge failed. Fix the cause. Failing log lines:\n\n" + "\n".join(lines[:80])
    # A push records the round even when posting its response failed.
    commits = api(f"repos/{repo}/pulls/{pr}/commits", pages=True)
    done = rounds_done(thread, commits, pr)
    mode = "fix"
    if done >= MAX_ROUNDS:
        # A separate publisher posts this once, with no write token here.
        mode = "limit" if done == MAX_ROUNDS and not any(
            trusted(c) and c["body"] == LIMIT for c in thread) else "skip"
    issue, name, effort = re.fullmatch(r"agent/(\d+)-(luna|terra)-(low|medium|high)", branch).groups()
    if mode == "fix":
        inline = comments(api(f"repos/{repo}/pulls/{pr}/comments", pages=True))
        reviews = comments(api(f"repos/{repo}/pulls/{pr}/reviews", pages=True))
        body = (info["body"] or "") if trusted(info) else "(description omitted: untrusted author)"
        prompt(issue, done + 1,
               f"## This round\n\nYou wrote PR #{pr} ({branch}), checked out with your earlier work. "
               "Write what changed for each finding and your checks to ../agent/comment.md, "
               "and the commit message to ../agent/commit-msg.txt.\n\n" + what +
               f"\n\n## Trusted PR discussion\n\n{comments(thread)}\n\n{inline}\n\n{reviews}"
               f"\n\n## PR description\n\n{body}")
    output(mode=mode, issue=issue, pr=pr, branch=branch, base=head,
           model=MODELS[name], effort=effort, round=done + 1)


if __name__ == "__main__":
    main()
