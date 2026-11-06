"""Run the read-only reviewer; release only checked output after teardown."""
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
# These helpers come from the workflow commit, outside the head's checkout.
sys.path.insert(0, str(HERE.parent / "codex-agent"))
from collect import checker, read_regular, secrets
from run import failure_summary
from teardown import remove

sys.path.insert(0, str(HERE))
from engine import effort

RENEW = ("CODEX_REVIEW_AUTH_JSON renewal required: its CI-only credentials "
         "changed or could not be verified. Repeat the dedicated login and "
         "replace the repository "
         "secret before another run; this workflow cannot persist refreshes.\n")


def collect_review(output, safe, credentials, status):
    """No logs, sessions or auth files are ever publication candidates."""
    if status:
        return
    for name in ("review.md", "last.md"):
        try:
            text = read_regular(output, name, 2_000_001).decode("utf-8")
        except FileNotFoundError:
            continue
        except (OSError, ValueError, UnicodeError):
            break
        if len(text.encode()) > 2_000_000 or checker.leaks(text, credentials):
            break
        (safe / "review.md").write_text(text)
        return
    (safe / "review.md").write_text("(withheld: missing, unsafe or credential-bearing review)\n")


def main():
    def interrupted(signum, _frame):
        print("Codex review interrupted; CODEX_REVIEW_AUTH_JSON may require renewal.", file=sys.stderr)
        raise SystemExit(128 + signum)

    signal.signal(signal.SIGTERM, interrupted)
    signal.signal(signal.SIGINT, interrupted)
    raw = os.environ.pop("CODEX_REVIEW_AUTH_JSON", "")
    try:
        credentials = secrets(raw)
    except (ValueError, TypeError):
        print("CODEX_REVIEW_AUTH_JSON is missing or invalid; provision or renew the "
              "dedicated CI-only login.", file=sys.stderr)
        raise
    if not credentials:
        raise ValueError("no credential values")
    safe = Path(os.environ["RUNNER_TEMP"]) / "review"
    safe.mkdir(mode=0o700)
    with tempfile.TemporaryDirectory(prefix="codex-review-", dir=os.environ["RUNNER_TEMP"]) as temp:
        private = Path(temp)
        auth, output = private / "auth", private / "output"
        auth.mkdir(mode=0o700)
        output.mkdir(mode=0o700)
        (auth / "auth.json").write_text(raw)
        (auth / "auth.json").chmod(0o600)
        status = 1
        try:
            with Path(".review/brief.md").open("rb") as prompt, \
                    (output / "log.jsonl").open("wb") as log, \
                    (output / "stderr.log").open("wb") as error:
                status = subprocess.run([
                    "bash", str(HERE / "codex-sandbox.sh"), "codex-review:local",
                    str(Path.cwd()), str(output), str(auth),
                    "bash", "/trusted/pr-review/codex-work.sh", effort(os.environ["KIND"])],
                    stdin=prompt, stdout=log, stderr=error).returncode
        finally:
            # No read of model output or refreshed auth until every model
            # process is gone. Failure to confirm removal withholds everything.
            try:
                remove(os.environ["CODEX_CONTAINER"])
            except BaseException:
                print("Codex teardown failed; CODEX_REVIEW_AUTH_JSON may require renewal. "
                      "No model output can be collected.", file=sys.stderr)
                raise
            auth_known = True
            try:
                current = secrets(read_regular(auth, "auth.json").decode())
                if set(current) != set(credentials):
                    (safe / "renewal-required.txt").write_text(RENEW)
                    print(RENEW, end="")
                credentials += current
            except (OSError, ValueError, UnicodeError):
                # Unknown rotated credentials cannot be safely redacted.
                status = 1
                auth_known = False
                (safe / "renewal-required.txt").write_text(RENEW)
                print(RENEW, end="")
            if status and auth_known:
                failure_summary(output, credentials, status, "Codex review")
            collect_review(output, safe, credentials, status)
            shutil.rmtree(output)
    if status:
        print("Codex review failed. Check the trusted configuration and renew "
              "CODEX_REVIEW_AUTH_JSON if the dedicated login expired.", file=sys.stderr)
    return status


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as error:
        # Error details can contain credentials or model-controlled text.
        print(f"Codex review failed: {type(error).__name__}", file=sys.stderr)
        raise SystemExit(1) from None
