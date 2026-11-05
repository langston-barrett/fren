"""Validate an untrusted patch on a fresh runner, then publish without running it.

Only this job receives FREN_DEV_TOKEN. All publishing metadata comes from
prepare's outputs, never from the runner on which Codex had full access.
"""
import os
from pathlib import Path, PurePosixPath
import subprocess
import sys

# With Python's isolated mode, import only the workflow's own helpers,
# regardless of the working directory's Python files or PYTHONPATH.
sys.path.insert(0, str(Path(__file__).resolve().parent))

from common import api, trusted
from fixparams import LIMIT, MAX_ROUNDS, ROUND


def git(*args, **kwargs):
    # No hook or fsmonitor may run, including at commit time. The checkout
    # and its git config are fresh; only git apply reads the agent's patch.
    return subprocess.run(["git", "-c", "core.hooksPath=/dev/null",
                           "-c", "core.fsmonitor=false", *args], check=True, **kwargs)


def validate_patch(patch):
    """Ask git to parse the patch itself, including quoted/binary paths."""
    stat = git("apply", "--numstat", "-z", str(patch), capture_output=True).stdout
    paths = []
    for record in stat.split(b"\0"):
        if not record:
            continue
        path = record.split(b"\t", 2)[2].decode("utf-8", "surrogateescape")
        parts = PurePosixPath(path).parts
        if (not parts or parts[0] == ".github" or
                PurePosixPath(path).is_absolute() or any(p in ("..", ".git") for p in parts)):
            raise ValueError(f"forbidden patch path: {path!r}")
        paths.append(path)
    return paths


def text(name, fallback="", limit=None):
    path = Path(os.environ["ARTIFACT"]) / name
    value = path.read_text(errors="replace").strip() if path.is_file() and not path.is_symlink() else ""
    value = value or fallback
    return value[:limit] if limit else value


def comment(number, body):
    # Structured input preserves newlines; never interpolate model text
    # into a shell command or let it become a command-line flag.
    import json
    subprocess.run(["gh", "api", f"repos/{os.environ['REPO']}/issues/{number}/comments",
                    "--method", "POST", "--input", "-"],
                   input=json.dumps({"body": body}), text=True, check=True)


def main():
    env = os.environ
    repo, mode, pr = env["REPO"], env["MODE"], env["PR"]
    branch, base, round_number = env["BRANCH"], env["BASE"], int(env["ROUND"])
    if pr:
        info = api(f"repos/{repo}/pulls/{pr}")
        if (info["state"] != "open" or info["head"]["sha"] != base or
                info["head"]["ref"] != branch or info["head"]["repo"]["full_name"] != repo):
            raise ValueError("PR closed or head changed since preparation; nothing published")
        thread = api(f"repos/{repo}/issues/{pr}/comments", pages=True)
        if mode == "limit":
            if not any(trusted(c) and c["body"] == LIMIT for c in thread):
                comment(pr, LIMIT)
            return
        done = max((int(m.group(1)) for c in thread if trusted(c)
                    if (m := ROUND.match(c["body"]))), default=0)
        if round_number <= done or round_number > MAX_ROUNDS:
            return
    patch = Path(env["ARTIFACT"]) / "change.patch"
    if not patch.is_file() or patch.is_symlink():
        raise ValueError("missing patch artifact")
    subject = pr or env["ISSUE"]
    prefix = (f"codex-agent fix round {round_number}" if pr else
              f"codex-agent ({env['MODEL']}, {env['EFFORT']} effort)")
    if patch.stat().st_size == 0:
        explanation = text("pr-body.md", text("last.md", "No explanation supplied."), 1500)
        comment(subject, prefix + " made no change:\n\n" + explanation)
        return
    try:
        paths = validate_patch(patch)
        if not paths:
            raise ValueError("patch has no changed paths")
        git("apply", "--index", "--binary", str(patch))
    except (ValueError, subprocess.CalledProcessError) as exc:
        comment(subject, prefix + f" rejected: {exc}. Nothing pushed.")
        raise
    # Defense in depth: inspect the applied index too, still against BASE.
    names = git("diff", "--cached", "--name-only", "-z", base,
                capture_output=True).stdout.split(b"\0")
    if any(p == b".github" or p.startswith(b".github/") for p in names):
        raise ValueError("applied patch changes .github")
    title = text("pr-title.txt", f"Fix #{env['ISSUE']}", 200).splitlines()[0]
    message = text("commit-msg.txt", title)
    git("config", "user.name", "fren-dev")
    git("config", "user.email", "352592472+fren-dev@users.noreply.github.com")
    git("-c", "commit.gpgsign=false", "commit", "--file=-", input=message, text=True)
    # A lease also checks races between the API check and the push. Initial
    # runs must create a branch; fix runs must replace precisely BASE.
    expected = base if pr else ""
    import base64
    basic = base64.b64encode(f"x-access-token:{env['GH_TOKEN']}".encode()).decode()
    # Keep the encoded credential out of argv, including Python's error
    # report if git fails. Only this fresh runner ever sees it.
    push_env = {**env, "GIT_CONFIG_COUNT": "1",
                "GIT_CONFIG_KEY_0": "http.https://github.com/.extraheader",
                "GIT_CONFIG_VALUE_0": f"AUTHORIZATION: basic {basic}"}
    git("push", f"--force-with-lease=refs/heads/{branch}:{expected}",
        f"https://github.com/{repo}.git", f"HEAD:refs/heads/{branch}", env=push_env)
    if pr:
        head = git("rev-parse", "HEAD", capture_output=True, text=True).stdout.strip()
        comment(pr, prefix + f", {head}:\n\n" + text("comment.md", text("last.md")))
    else:
        import json
        body = text("pr-body.md", text("last.md")) + (
            f"\n\nCloses #{env['ISSUE']}. Written by {env['MODEL']} at {env['EFFORT']} "
            "effort in the `codex-agent` workflow.\n")
        created = subprocess.check_output([
            "gh", "api", f"repos/{repo}/pulls", "--method", "POST", "--input", "-"],
            input=json.dumps({"head": branch, "base": "main", "title": title, "body": body}), text=True)
        comment(subject, prefix + " opened " + json.loads(created)["html_url"] + ".")


if __name__ == "__main__":
    main()
