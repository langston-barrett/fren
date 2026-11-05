"""Read-only GitHub helpers and prompt formatting for the prepare job."""
import json
import os
from pathlib import Path
import subprocess

MODELS = {"luna": "gpt-6-luna", "terra": "gpt-6.1-terra"}
EFFORTS = {"low", "medium", "high"}
PUSHERS = {"OWNER", "MEMBER", "COLLABORATOR"}


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
