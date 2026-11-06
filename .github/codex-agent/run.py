"""Stage the sign-in privately, run the container, then collect safe output."""
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import tempfile

from collect import checker, collect, read_regular, secrets
from publication import inert, report
from teardown import remove

HERE = Path(__file__).resolve().parent


def failure_summary(output, credentials, status, label="codex-agent"):
    """Report a few diagnostic lines only after teardown, without credentials."""
    print(f"{label} sandbox exited {status}", file=sys.stderr)
    try:
        text = read_regular(output, "stderr.log", 16384).decode("utf-8", "replace")
    except (OSError, ValueError):
        print("stderr unavailable (not a readable regular file)", file=sys.stderr)
        text = ""
    # Drop terminal controls before making runner commands inert. Long
    # opaque strings include unknown/refreshed tokens, JWTs and API keys.
    def lines_of(value):
        value = re.sub(r"\x1b\[[0-?]*[ -/]*[@-~]|[^\x20-\x7e\n]", "", value)
        return [line.strip() for line in value.splitlines() if line.strip()]

    lines = lines_of(text)
    errors = [line for line in lines if re.search(
        r"error|fatal|failed|traceback|caused by|denied|invalid", line, re.IGNORECASE)]
    source = "stderr"
    if not errors:
        # With --json, some configuration/provider failures appear only
        # as stdout events. Inspect only structured JSON error events here.
        # If none are found, the fallback below can report stderr lines of
        # any kind, with the same bounds, redaction and neutralization.
        try:
            log = read_regular(output, "log.jsonl", 16384).decode("utf-8", "replace")
        except (OSError, ValueError):
            log = ""
        for line in log.splitlines():
            try:
                event = json.loads(line)
            except (ValueError, RecursionError):
                continue
            if not isinstance(event, dict):
                continue
            message = event.get("message") if event.get("type") == "error" else None
            if event.get("type") == "turn.failed" and isinstance(event.get("error"), dict):
                message = event["error"].get("message")
            if isinstance(message, str):
                errors.extend(lines_of(message))
        if errors:
            source = "codex"
    for line in list(dict.fromkeys(errors or lines))[:3]:
        for credential in credentials:
            if credential:
                line = line.replace(credential, "[redacted]")
        line = re.sub(r"(?i)\b(?:bearer\s+|(?:token|api[_-]?key)\s*[:=]\s*)\S+",
                      "[redacted]", line)
        line = re.sub(r"\b(?:sk-[A-Za-z0-9_-]+|gh[pousr]_[A-Za-z0-9]+|github_pat_\w+)",
                      "[redacted]", line)
        line = re.sub(r"[A-Za-z0-9_+/=.-]{24,}", "[redacted]", line)
        # Keep the detector's encoded/fragment matching as a final guard,
        # before truncation could split a known credential into a prefix.
        if checker.leaks(line, credentials):
            line = "[redacted credential-bearing line]"
        print(source + ": " + inert(line[:400]), file=sys.stderr)
    if not errors and not lines:
        print("no readable stderr or Codex error events", file=sys.stderr)


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
            auth_known = True
            try:
                current = secrets(read_regular(auth, "auth.json").decode())
                if not current:
                    raise ValueError("no credential values")
                credentials += current
            except (OSError, ValueError, RecursionError):
                # Unknown rotated credentials cannot be safely scanned or
                # redacted, even if the sandbox reported success.
                status = 1
                auth_known = False
                print("Final Codex credentials could not be verified; "
                      "all output and diagnostics withheld.", file=sys.stderr)
            if status and auth_known:
                failure_summary(output, credentials, status)
            safe = Path(os.environ["RUNNER_TEMP"]) / "codex-result"
            if auth_known:
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
