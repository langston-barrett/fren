"""Read-only GitHub helpers and prompt formatting for the prepare job."""
import json
import os
from pathlib import Path
import re
import subprocess

MODELS = {"luna": "gpt-6-luna", "terra": "gpt-6.1-terra"}
EFFORTS = {"low", "medium", "high"}
PUSHERS = {"OWNER", "MEMBER", "COLLABORATOR"}
MAX_ROUNDS = 3
LIMIT = (f"codex-agent has answered {MAX_ROUNDS} rounds; "
         "leaving this pull request to the coordinator.")
ROUND = re.compile(r"codex-agent fix round (\d+)(?:,| made no change:| rejected:)")
TRAILERS = re.compile(r"\n\nCodex-Agent-PR: (\d+)\nCodex-Agent-Round: (\d+)\n*\Z")


def rounds_done(thread, commits, pr):
    """Pushed rounds survive a failed comment POST in commit trailers."""
    rounds = [int(m.group(1)) for c in thread if trusted(c)
              if (m := ROUND.match(c["body"]))]
    for commit in commits:
        match = TRAILERS.search(commit["commit"]["message"])
        if match and match.group(1) == str(pr):
            rounds.append(int(match.group(2)))
    return max(rounds, default=0)


def branch_exists(repo, branch):
    refs = api(f"repos/{repo}/git/matching-refs/heads/{branch}")
    return any(ref["ref"] == f"refs/heads/{branch}" for ref in refs)


def api(path, *, pages=False):
    args = ["gh", "api", path]
    if pages:
        args += ["--paginate", "--slurp"]
    data = json.loads(subprocess.check_output(args, text=True))
    return [item for page in data for item in page] if pages else data


def trusted(item):
    return item.get("author_association") in PUSHERS


def comments(items):
    return "\n\n".join(f"Comment:\n{c['body']}" for c in items if trusted(c))


def output(**values):
    with open(os.environ["GITHUB_OUTPUT"], "a") as f:
        for key, value in values.items():
            if "\n" in str(value) or "\r" in str(value):
                raise ValueError(f"multiline output: {key}")
            f.write(f"{key}={value}\n")


def prompt(issue, round_number, text):
    # The prepare and Codex runners have different temporary directories.
    # This relative directory is created beside the checkout in both jobs.
    dest = Path("agent")
    dest.mkdir(exist_ok=True)
    brief = Path(".github/codex-agent/brief.md").read_text()
    brief = (brief.replace("{{TEMP}}", "../agent")
             .replace("{{ROUND}}", str(round_number))
             .replace("{{SEED}}", str(700000 + 1000 * int(issue) + 100 * round_number)))
    (dest / "prompt.md").write_text(brief + "\n\n" + text + "\n")
