"""Decide the issue, model and effort of a codex-agent run, check that the
labeller may write, and write Codex's brief to $RUNNER_TEMP/agent/prompt.md."""
import json, os, subprocess, sys

MODELS = {"luna": "gpt-6-luna", "terra": "gpt-6.1-terra"}
EFFORTS = {"low", "medium", "high"}

def gh(*args):
    return subprocess.run(["gh", *args], check=True, capture_output=True, text=True).stdout

def main():
    env = os.environ
    repo = env["REPO"]
    if env["EVENT"] == "workflow_dispatch":
        issue, name, effort = env["IN_ISSUE"], env["IN_MODEL"], env["IN_EFFORT"]
    else:
        issue = env["EV_ISSUE"]
        rest = env["LABEL"].removeprefix("agent/")
        name, _, effort = rest.partition("-")
        perm = json.loads(gh("api", f"repos/{repo}/collaborators/{env['SENDER']}/permission"))["permission"]
        if perm not in ("admin", "maintain", "write"):
            sys.exit(f"{env['SENDER']} may not start codex-agent ({perm})")
    if name not in MODELS or effort not in EFFORTS or not issue.isdigit():
        sys.exit(f"unknown model, effort or issue: {name!r} {effort!r} {issue!r}")
    data = json.loads(gh("issue", "view", issue, "-R", repo, "--json", "title,body,comments"))
    comments = "\n\n".join(f"Comment:\n{c['body']}" for c in data["comments"])
    temp = os.path.join(env["RUNNER_TEMP"], "agent")
    os.makedirs(temp, exist_ok=True)
    with open(os.path.join(temp, "prompt.md"), "w") as f:
        f.write(open(".github/codex-agent/brief.md").read().replace("{{TEMP}}", temp))
        f.write(f"\n\n## The issue: #{issue}, {data['title']}\n\n{data['body']}\n\n{comments}\n")
    with open(env["GITHUB_OUTPUT"], "a") as out:
        out.write(f"issue={issue}\nmodel={MODELS[name]}\neffort={effort}\n")

main()
