"""Validate the repository variable before any model credential is used."""
import os


def engine(value):
    value = value or "claude"
    if value not in ("claude", "codex"):
        raise ValueError("PR_REVIEW_ENGINE must be claude or codex")
    return value


def effort(kind):
    return "medium" if kind in ("fixes", "rebase") else "high"


if __name__ == "__main__":
    with open(os.environ["GITHUB_OUTPUT"], "a") as output:
        output.write(f"engine={engine(os.environ.get('PR_REVIEW_ENGINE', ''))}\n")
