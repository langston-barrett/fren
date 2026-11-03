#!/usr/bin/env python3
"""Tests of `scripts/local-review`, with no model: a dry run, a run with a
stand-in for Codex, and a run without Codex, each in a scratch repository
whose base holds this checkout's AGENTS.md and pr-review scripts.

    python3 -I -B scripts/local_review_test.py
"""

import importlib.machinery
import importlib.util
import os
import re
import shutil
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True

HERE = os.path.dirname(os.path.realpath(__file__))
TOP = os.path.dirname(HERE)
SCRIPT = os.path.join(HERE, "local-review")


def load():
    loader = importlib.machinery.SourceFileLoader("local_review", SCRIPT)
    spec = importlib.util.spec_from_loader("local_review", loader)
    module = importlib.util.module_from_spec(spec)
    loader.exec_module(module)
    return module


local_review = load()

# A stand-in for Codex: checks the flags that keep it read-only and off the
# web, reads the prompt from stdin, and gives the review as its last message.
FAKE_CODEX = r"""#!PYTHON
import sys
args = sys.argv[1:]
prompt = sys.stdin.read()
need = ["exec", "web_search=disabled", "read-only", "--ignore-user-config", "-"]
missing = [a for a in need if a not in args]
assert not missing, missing
for feature in ["apps", "browser_use", "in_app_browser"]:
    assert any(args[i] == "--disable" and args[i + 1] == feature for i in range(len(args) - 1)), feature
assert args[args.index("-m") + 1] == "test-model"
assert "model_reasoning_effort=low" in args
assert "Note from the author" in prompt
head = prompt.split("head `")[1].split("`")[0]
with open(args[args.index("-o") + 1], "w") as f:
    f.write(f"Review of {head}: no blocking issues\n\nProbes: none ran.\n")
"""


def run(*args, cwd=None, env=None, check=True):
    result = subprocess.run(list(args), cwd=cwd, env=env, capture_output=True, text=True)
    if check and result.returncode != 0:
        raise AssertionError(f"{args} failed: {result.stderr}")
    return result


def commit(repo, message, parent=None):
    """Commits the index with plumbing, which runs no hook."""
    git = ["git", "-C", repo, "-c", "user.name=Test", "-c", "user.email=test@example.com"]
    run(*git, "add", "-A")
    tree = run(*git, "write-tree").stdout.strip()
    cmd = [*git, "commit-tree", tree, "-m", message] + (["-p", parent] if parent else [])
    sha = run(*cmd).stdout.strip()
    run(*git, "update-ref", "HEAD", sha)
    return sha


def make_repo(root):
    """A base, `main`, with the files that compose the brief, and a branch
    with one commit that adds a file, a CLAUDE.md and a symbolic link."""
    repo = os.path.join(root, "repo")
    os.makedirs(repo)
    run("git", "init", "-q", "-b", "main", repo)
    for path in local_review.TRUSTED:
        os.makedirs(os.path.join(repo, os.path.dirname(path)), exist_ok=True)
        shutil.copy(os.path.join(TOP, path), os.path.join(repo, path))
    base = commit(repo, "Base")
    run("git", "-C", repo, "checkout", "-q", "-b", "topic")
    with open(os.path.join(repo, "new.txt"), "w") as f:
        f.write("a new line\n")
    os.makedirs(os.path.join(repo, ".claude"))
    for path in ["CLAUDE.md", ".claude/settings.json"]:
        with open(os.path.join(repo, path), "w") as f:
            f.write("{}\n")
    os.symlink("new.txt", os.path.join(repo, "link.txt"))
    head = commit(repo, "Add a new file\n\nIts body.", base)
    run("git", "-C", repo, "branch", "-f", "main", base)
    return repo, base, head


def env_without_gh(root, **extra):
    """An environment whose PATH has git but no gh, so the branch has no
    pull request."""
    bin_dir = os.path.join(root, "bin")
    os.makedirs(bin_dir, exist_ok=True)
    os.symlink(shutil.which("git"), os.path.join(bin_dir, "git"))
    env = {k: v for k, v in os.environ.items() if not k.startswith("LOCAL_REVIEW_")}
    return {**env, "PATH": bin_dir, "HOME": root, **extra}


def test_relabel():
    sha = "a" * 40
    assert local_review.relabel(f"Review of {sha}: blocking issues\n\n1. x") == \
        f"Pre-push check of {sha}: blocking issues\n\n1. x\n"
    assert local_review.relabel("no verdict").startswith("Pre-push check of (no verdict line)")
    assert not local_review.relabel(f"  Review of {sha}: x").startswith("Review of")


def test_dry_run():
    with tempfile.TemporaryDirectory() as root:
        repo, base, head = make_repo(root)
        result = run(sys.executable, "-I", "-B", SCRIPT, "--base", "main", "--dry-run", "--keep",
                     cwd=repo, env=env_without_gh(root))
        prompt = result.stdout
        assert prompt.startswith(local_review.PREAMBLE.split("{pr}")[0]), prompt[:200]
        assert "The branch has no pull request yet" in prompt
        assert "# Reviews by separate agents" in prompt
        assert "# Keeping the front ends together" in prompt
        assert f"head `{head}`" in prompt
        assert f"(`{base}`)" in prompt
        assert "Title: Add a new file" in prompt and "> Its body." in prompt
        assert "{{" not in prompt
        scratch = re.search(r"scratch copy in (\S+)", result.stderr).group(1)
        try:
            work = os.path.join(scratch, "head")
            assert os.path.exists(os.path.join(work, "new.txt"))
            for gone in ["CLAUDE.md", ".claude", "AGENTS.md", "link.txt", ".git"]:
                assert not os.path.lexists(os.path.join(work, gone)), gone
            with open(os.path.join(work, ".review", "diff.patch")) as f:
                assert "+a new line" in f.read()
            with open(os.path.join(work, ".review", "probes.md")) as f:
                assert f.read() == local_review.PROBES
            with open(os.path.join(work, ".review", "log.txt")) as f:
                assert "Add a new file" in f.read()
        finally:
            shutil.rmtree(scratch)
        assert not os.path.exists(os.path.join(repo, ".lake"))


def test_fake_codex():
    with tempfile.TemporaryDirectory() as root:
        repo, _, head = make_repo(root)
        codex = os.path.join(root, "fake-codex")
        with open(codex, "w") as f:
            f.write(FAKE_CODEX.replace("PYTHON", sys.executable))
        os.chmod(codex, 0o755)
        env = env_without_gh(root, LOCAL_REVIEW_CODEX=codex, LOCAL_REVIEW_MODEL="test-model",
                             LOCAL_REVIEW_EFFORT="low")
        result = run(sys.executable, "-I", "-B", SCRIPT, "--base", "main", cwd=repo, env=env,
                     check=False)
        assert result.returncode == 0, result.stdout + result.stderr
        assert result.stdout == f"Pre-push check of {head}: no blocking issues\n\nProbes: none ran.\n"
        out = os.path.join(repo, ".lake", "local-review", head)
        with open(os.path.join(out, "review.md")) as f:
            assert f.read() == result.stdout
        assert os.path.exists(os.path.join(out, "prompt.md"))
        assert not [d for d in os.listdir(tempfile.gettempdir()) if d.startswith(f"local-review-{head[:12]}")]


def test_no_codex():
    with tempfile.TemporaryDirectory() as root:
        repo, _, _ = make_repo(root)
        env = env_without_gh(root, LOCAL_REVIEW_CODEX="codex-that-is-not-installed")
        result = run(sys.executable, "-I", "-B", SCRIPT, "--base", "main", cwd=repo, env=env,
                     check=False)
        assert result.returncode == 1
        assert "`codex-that-is-not-installed` is not installed" in result.stderr, result.stderr
        assert result.stdout == ""


def main():
    tests = [test_relabel, test_dry_run, test_fake_codex, test_no_codex]
    for test in tests:
        test()
    print(f"{len(tests)} tests passed")


if __name__ == "__main__":
    main()
