"""Run shared slow checks without exposing runner credentials to PR code.

Only the source checkout is a writable host mount. Trusted code and the
host's logs/artifact staging stay outside it.
Collect only regular output files after confirmed container teardown.
"""

import os
from pathlib import Path
import re
import signal
import shutil
import stat
import subprocess
import sys

HERE = Path(__file__).resolve().parent


def inert(text):
    return text.replace("::", "∷").replace("##[", "# #[")


def regular(path, root):
    """No symlink in any component, including the output directory itself."""
    try:
        parts = path.relative_to(root).parts
        at = root
        for part in parts[:-1]:
            at /= part
            if not stat.S_ISDIR(at.lstat().st_mode):
                return False
        return stat.S_ISREG(path.lstat().st_mode)
    except (OSError, ValueError):
        return False


def collect(work, dest, artifacts=True):
    if artifacts:
        dest.mkdir()
    # A worker can replace any path in its checkout, including .lake or
    # fuzz, with a symlink to a runner file. Never follow those links.
    total = 0
    fuzz = work / "fuzz"
    if artifacts and not fuzz.is_symlink() and fuzz.is_dir():
        for directory, dirs, files in os.walk(fuzz, followlinks=False):
            dirs[:] = [d for d in dirs if not Path(directory, d).is_symlink()]
            for name in files:
                source = Path(directory, name)
                if not all(re.fullmatch(r"[A-Za-z0-9_.-]+", p) for p in source.relative_to(fuzz).parts):
                    continue
                if not regular(source, work):
                    continue
                size = source.stat().st_size
                if size > 8 * 1024**2 or total + size > 64 * 1024**2:
                    raise ValueError("Worker artifacts exceed the output limit")
                target = dest / source.relative_to(fuzz)
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(source, target)
                total += size
    summary = work / ".lake/slow-summary.md"
    if regular(summary, work) and summary.stat().st_size <= 1024**2:
        with open(os.environ["GITHUB_STEP_SUMMARY"], "a") as f:
            f.write(inert(summary.read_text()))


def main():
    job = sys.argv[1]
    if job not in ("own-spec-agreement", "methods-agree", "coverage", "fuzz-frontends"):
        raise ValueError("Unknown job")
    temp = Path(os.environ["RUNNER_TEMP"])
    work = (temp / "slow-work").resolve()
    image = "slow-check:local"
    subprocess.run(["docker", "build", "--tag", image, str(HERE)], check=True)
    env = {**os.environ, "SLOW_CONTAINER": f"slow-{os.environ['GITHUB_RUN_ID']}-{os.environ['GITHUB_RUN_ATTEMPT']}-{job}"}
    def cancelled(signum, frame):
        raise SystemExit(128 + signum)
    signal.signal(signal.SIGTERM, cancelled)

    def invoke(command, log):
        with log.open("wb") as f:
            try:
                result = subprocess.run(["bash", str(HERE / "sandbox.sh"), image, str(work),
                                         "bash", "/trusted/inside.sh", command], stdout=f, stderr=subprocess.STDOUT, env=env)
            finally:
                # A failed removal or an unavailable daemon must not be
                # mistaken for teardown. Never collect with a live worker.
                subprocess.run(["docker", "rm", "--force", env["SLOW_CONTAINER"]],
                               stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                remaining = subprocess.check_output(["docker", "ps", "--all", "--quiet", "--filter",
                                                     f"name=^/{env['SLOW_CONTAINER']}$"], text=True)
                if remaining.strip():
                    raise RuntimeError("Slow worker teardown failed")
        # No worker stdout reaches the Actions command parser. The raw log
        # lives outside its mounts, and Docker has removed its processes.
        with log.open("rb") as f:
            data = f.read(8 * 1024**2 + 1)
        text = data[:8 * 1024**2].decode(errors="replace")
        if len(data) > 8 * 1024**2:
            text += "\n[worker log truncated]\n"
        print(inert(text), flush=True)
        return result.returncode, text

    if job == "coverage":
        code, text = invoke("llvm-version", temp / "slow-llvm.log")
        versions = re.findall(r"^LLVM_VERSION=([0-9]{1,3})$", text, re.MULTILINE)
        if code or not versions:
            raise ValueError("Isolated toolchain probe did not return an LLVM version")
        subprocess.run(["docker", "build", "--tag", image, "--build-arg", f"LLVM_VERSION={versions[-1]}", str(HERE)], check=True)
    code, _ = invoke(job, temp / "slow-worker.log")
    if job in ("fuzz-frontends", "coverage"):
        collect(work, temp / "fuzz", artifacts=job == "fuzz-frontends")
    sys.exit(code)


if __name__ == "__main__":
    main()
