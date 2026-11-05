"""Prepare a trusted issue's prompt and publishing metadata, without writes."""
import os
import subprocess

from common import MODELS, EFFORTS, api, comments, output, prompt, trusted


def main():
    env = os.environ
    repo = env["REPO"]
    if env["EVENT"] == "workflow_dispatch":
        issue, name, effort = env["IN_ISSUE"], env["IN_MODEL"], env["IN_EFFORT"]
    else:
        issue = env["EV_ISSUE"]
        name, _, effort = env["LABEL"].removeprefix("agent/").partition("-")
        perm = api(f"repos/{repo}/collaborators/{env['SENDER']}/permission")["permission"]
        if perm not in ("admin", "maintain", "write"):
            raise ValueError(f"{env['SENDER']} may not start codex-agent ({perm})")
    if name not in MODELS or effort not in EFFORTS or not issue.isdigit():
        raise ValueError(f"unknown model, effort or issue: {name!r} {effort!r} {issue!r}")
    data = api(f"repos/{repo}/issues/{issue}")
    if not trusted(data) or "pull_request" in data or data["state"] != "open":
        return output(mode="skip")
    thread = comments(api(f"repos/{repo}/issues/{issue}/comments", pages=True))
    branch = f"agent/{issue}-{name}-{effort}"
    base = subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()
    prompt(issue, 0, f"## The issue: #{issue}, {data['title']}\n\n{data['body'] or ''}\n\n{thread}")
    output(mode="issue", issue=issue, pr="", branch=branch, base=base,
           model=MODELS[name], effort=effort, round=0)


if __name__ == "__main__":
    main()
