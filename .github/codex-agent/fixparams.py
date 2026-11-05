"""For codex-agent's `fix` job: find the agent's pull request, its model and
effort (from its branch, agent/<issue>-<model>-<effort>), and the round;
write the brief with the review or the failed run's log to
$RUNNER_TEMP/agent/prompt.md. Sets skip=true when there's nothing to do."""
import json, os, re, subprocess, sys

MAX_ROUNDS = 3

def gh(*args):
    return subprocess.run(["gh", *args], check=True, capture_output=True, text=True).stdout

def out(**kv):
    with open(os.environ["GITHUB_OUTPUT"], "a") as f:
        for k, v in kv.items():
            f.write(f"{k}={v}\n")

def main():
    env, repo = os.environ, os.environ["REPO"]
    if env["EVENT"] == "issue_comment":
        pr = env["PR"]
        what = "The review of your pull request's current head has blocking issues. Fix every [blocking] finding at every instance it lists, and any [non-blocking] ones that are small. If you disagree with a finding, say why in your comment instead of changing the code.\n\n" + env["COMMENT"]
    else:
        prs = json.loads(gh("pr", "list", "-R", repo, "--head", env["RUN_BRANCH"], "--json", "number"))
        if not prs:
            return out(skip="true")
        pr = str(prs[0]["number"])
        log = subprocess.run(["gh", "run", "view", env["RUN_ID"], "-R", repo, "--log-failed"], capture_output=True, text=True).stdout
        lines = [l for l in log.splitlines() if re.search(r"error:|FAIL|crashed|warning:", l)]
        what = "Your pull request's `pre-merge` run failed. Fix the cause. The failing lines of its log:\n\n" + "\n".join(lines[:80])
    info = json.loads(gh("pr", "view", pr, "-R", repo, "--json", "headRefName,state,commits,body"))
    branch = info["headRefName"]
    m = re.fullmatch(r"agent/(\d+)-(.+)-(low|medium|high)", branch)
    if info["state"] != "OPEN" or not branch.startswith("agent/") or not m:
        return out(skip="true")
    model, effort = m.group(2), m.group(3)
    done = sum(1 for c in json.loads(gh("api", f"repos/{repo}/issues/{pr}/comments", "--paginate"))
               if c["body"].startswith("codex-agent fix round"))
    if done >= MAX_ROUNDS:
        gh("pr", "comment", pr, "-R", repo, "--body", f"codex-agent has answered {done} rounds; leaving this pull request to the coordinator.")
        return out(skip="true")
    temp = os.path.join(env["RUNNER_TEMP"], "agent")
    os.makedirs(temp, exist_ok=True)
    brief = open(".github/codex-agent/brief.md").read().replace("{{TEMP}}", temp)
    with open(os.path.join(temp, "prompt.md"), "w") as f:
        f.write(brief + f"\n\n## This round\n\nYou wrote pull request #{pr} (branch {branch}), which is checked out with your earlier work. Write the commit message to {temp}/commit-msg.txt and a comment saying what changed for each finding, with the checks you ran, to {temp}/comment.md.\n\n" + what + f"\n\n## The pull request's description\n\n{info['body']}\n")
    out(skip="false", pr=pr, branch=branch, model=model, effort=effort, round=done + 1)

main()
