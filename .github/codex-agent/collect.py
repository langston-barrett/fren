"""Copy only regular, non-leaking result files after the sandbox is dead."""
import importlib.util
import json
import os
from pathlib import Path
import stat

FILES = ("change.patch", "pr-title.txt", "pr-body.md", "commit-msg.txt",
         "comment.md", "last.md", "log.jsonl", "stderr.log")
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("review_check", HERE.parent / "pr-review/check.py")
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)


def read_regular(directory, name):
    # Opening relative to a checked directory FD also rejects symlinks in
    # the parent. Nonblocking opens cannot hang on a FIFO left by Codex.
    with_fd = os.open(directory, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        fd = os.open(name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=with_fd)
        with os.fdopen(fd, "rb") as f:
            if not stat.S_ISREG(os.fstat(f.fileno()).st_mode):
                raise ValueError("not a regular file")
            return f.read()
    finally:
        os.close(with_fd)


def secrets(raw):
    """The auth JSON and each token/key value, including nested tokens."""
    found = [raw]

    def visit(value):
        if isinstance(value, dict):
            for key, child in value.items():
                if isinstance(child, str) and ("token" in key.lower() or "key" in key.lower()):
                    found.append(child)
                visit(child)
        elif isinstance(value, list):
            for child in value:
                visit(child)

    visit(json.loads(raw))
    return found


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
