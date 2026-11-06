"""Copy only regular, non-leaking result files after the sandbox is dead."""
import importlib.util
import json
import os
from pathlib import Path
import re
import stat

FILES = ("change.patch", "pr-title.txt", "pr-body.md", "commit-msg.txt",
         "comment.md", "last.md", "log.jsonl", "stderr.log")
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("review_check", HERE.parent / "pr-review/check.py")
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)


def read_regular(directory, name, limit=-1):
    # Opening relative to a checked directory FD also rejects symlinks in
    # the parent. Nonblocking opens cannot hang on a FIFO left by Codex.
    with_fd = os.open(directory, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        fd = os.open(name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=with_fd)
        with os.fdopen(fd, "rb") as f:
            if not stat.S_ISREG(os.fstat(f.fileno()).st_mode):
                raise ValueError("not a regular file")
            return f.read(limit)
    finally:
        os.close(with_fd)


def secrets(raw):
    """Token/key values and opaque auth identifiers, including nested ones.

    Do not generate leak-detector fragments from the JSON structure:
    common auth metadata otherwise withholds ordinary error messages.
    Copies of the full JSON still contain these credential values.
    """
    found = []

    def visit(value):
        if isinstance(value, dict):
            for key, child in value.items():
                if isinstance(child, str) and ("token" in key.lower() or "key" in key.lower()
                                               or key.lower().endswith("_id") or key.lower() == "id"):
                    found.append(child)
                visit(child)
        elif isinstance(value, list):
            for child in value:
                visit(child)
        elif isinstance(value, str) and re.fullmatch(r"[A-Za-z0-9_+/=.-]{16,}", value):
            # Preserve opaque values even under an unfamiliar field name.
            # Short auth modes and ISO timestamps do not match, so common
            # metadata cannot recreate the structural false positive.
            found.append(value)

    visit(json.loads(raw))
    return list(dict.fromkeys(found))


def collect(source, destination, credentials):
    destination.mkdir(mode=0o700)
    withheld = []
    for name in FILES:
        try:
            data = read_regular(source, name)
        except FileNotFoundError:
            continue
        except (OSError, ValueError):
            withheld.append(name)
            continue
        if checker.leaks(data.decode("utf-8", "replace"), credentials):
            withheld.append(name)
            continue
        (destination / name).write_bytes(data)
    if withheld:
        (destination / "withheld.txt").write_text(
            "Files withheld by the credential/regular-file check:\n" + "\n".join(withheld) + "\n")
    return withheld
