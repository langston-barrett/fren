"""Capture the full change from the saved base, including agent commits."""
import os
from pathlib import Path
import subprocess


def export(base, destination):
    subprocess.run(["git", "add", "--all"], check=True)
    with Path(destination).open("wb") as patch:
        subprocess.run(["git", "diff", "--cached", "--binary", "--full-index",
                        "--no-ext-diff", "--no-textconv", "--no-renames", base, "--"],
                       stdout=patch, check=True)


if __name__ == "__main__":
    export(os.environ["BASE"], "../agent/change.patch")
