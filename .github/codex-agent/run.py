"""Stage the sign-in privately, run the container, then collect safe output."""
import os
from pathlib import Path
import shutil
import signal
import subprocess
import tempfile

from collect import collect, read_regular, secrets
from publication import report
from teardown import remove

HERE = Path(__file__).resolve().parent


def main():
    def interrupted(signum, _frame):
        raise SystemExit(128 + signum)

    signal.signal(signal.SIGTERM, interrupted)
    raw = os.environ.pop("CODEX_AUTH_JSON")
    credentials = secrets(raw)
    root = Path.cwd()
    output = root / "agent"
    # CODEX_AUTH_JSON is a snapshot, not a renewable shared credential.
    # For unattended runs, provision API-key auth. For ChatGPT auth the
    # owner must replace the secret after token rotation or expiration;
    # this workflow has no secret-write permission. See README.md.
    with tempfile.TemporaryDirectory(prefix="codex-auth-", dir=os.environ["RUNNER_TEMP"]) as temp:
        auth = Path(temp)
        token_file = auth / "auth.json"
        token_file.write_text(raw)
        token_file.chmod(0o600)
        status = 1
        try:
            with (output / "prompt.md").open("rb") as prompt, \
                    (output / "log.jsonl").open("wb") as log, \
                    (output / "stderr.log").open("wb") as error:
                status = subprocess.run([
                    "bash", str(HERE / "sandbox.sh"), "codex-agent:local",
                    str(root / "work"), str(output), str(auth),
                    str(Path(os.environ.get("ELAN_HOME", Path.home() / ".elan")).resolve()),
                    "bash", "/trusted/work.sh", os.environ["MODEL"], os.environ["EFFORT"],
                    os.environ["BASE"]], stdin=prompt, stdout=log, stderr=error).returncode
        finally:
            # The shell trap removes the container on normal/error exits.
            # Remove it again before reading any untrusted output, including
            # cancellation, then the workflow's always step does so too.
            remove(os.environ["CODEX_CONTAINER"])
            try:
                current = read_regular(auth, "auth.json").decode()
                credentials += secrets(current)
            except (OSError, ValueError):
                pass
            safe = Path(os.environ["RUNNER_TEMP"]) / "codex-result"
            collect(output, safe, credentials)
            # Model processes are gone; neither auth nor raw outputs are
            # uploaded or restored in another job.
            shutil.rmtree(output)
    return status


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as error:
        report(error)
        raise SystemExit(1) from None
