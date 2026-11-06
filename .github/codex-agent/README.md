# Codex authors in CI

`codex-agent` works small follow-up issues. Add `agent/<model>-<effort>`
(`agent/luna-low`, for example), or dispatch it on `main` with an issue,
model and effort. Only issues and human comments from OWNER, MEMBER or
COLLABORATOR qualify; a label setter must also have write access.
Automated review findings must match the completed `pr-review` run's
validated artifact and the current PR head. It opens an `agent/*` PR and
answers at most three blocking reviews or failed
`pre-merge` runs. The coordinator handles conflicts with `main`, small
findings on a clean review, and any remaining work after the round limit.
These PRs still require the normal CI checks and review before merging.

Preparation only reads GitHub. Codex runs in an unprivileged container
with its own PID namespace, no capabilities or privilege escalation, no
runner environment, home, Docker socket or file-command paths, and a
read-only root and Lean toolchain. Its checkout, output and private Codex
authentication directory are the writable host mounts; home and temporary
files use private scratch space. Network access is available
for inference and dependencies. The container and all children are removed
before any output is collected or uploaded. This boundary keeps the
runner's runtime token away from Codex: the token can write `main`'s
caches even when the job has `permissions: {}`. `lint` tests the boundary
and teardown with `test_sandbox.sh` and a hostile stand-in for Codex.

Only regular output files enter the artifact, after the workflow's trusted
`pr-review/check.py` leak detector checks each against the original
token/key values, auth identifiers, other opaque values and any refreshed
values still present. It scans values, not common field names from the
JSON structure.
Files containing known credential copies, plain or encoded, are withheld.
No authentication file is uploaded. A separate fresh runner validates the
patch and publishes it with `FREN_DEV_TOKEN`, without executing patched
code. Workers and publishers have separate branch concurrency groups.
Fix commits end with the publisher's pull request and round trailers, so
a failed comment does not lose a pushed round. The publisher strips round
trailers supplied by the model and neutralizes mentions, runner commands
and commit check directives in comments, pull request titles and
descriptions, and commit messages. This keeps model text from starting an
assistant under the publishing account or suppressing required checks.
Git and API responses are captured; runner logs report exception types.
After container teardown, a failed sandbox also reports up to three
stderr error lines, bounded and redacted for known credentials and opaque
token-like strings, even when its raw logs are withheld. If stderr has no
error line, it falls back to Codex's structured JSON error events.
Mentions are broken with zero-width spaces, including entity forms and
code. API bodies are bounded below GitHub's limit after neutralization,
including multibyte text.

## Authentication lifecycle

Codex and every program it runs can read `/auth/auth.json` and use the
network to send that sign-in elsewhere. The artifact leak detector does
not restrict network traffic. Provision `CODEX_AUTH_JSON` with a dedicated
API key in a project with an [enforced spending limit][spend-limits].
This limits exposure and supports unattended authentication. The value
is the file that `codex login --with-api-key` creates; replace the GitHub
secret when that API key is rotated or revoked. This workflow does not
update repository secrets or persist authentication in an artifact/cache.

If the owner instead provisions a ChatGPT sign-in snapshot, Codex can
refresh its tokens during a run, but the updated file is discarded at
teardown. The owner must renew `CODEX_AUTH_JSON` from a fresh local
`codex login` after token rotation or expiration, before retrying a failed
sign-in. Do not share that renewable session with other clients or assume
that copying one snapshot provides continuing unattended authentication.
See the [official authentication guidance](https://learn.chatgpt.com/docs/auth)
for automatic refresh, credential storage and API-key automation advice.

## First run after merge

The coordinator dispatches the workflow on one small, trusted follow-up
issue immediately after merge, for example:

```sh
gh workflow run codex-agent --ref main -f issue=N -f model=luna -f effort=low
```

Check that the production image starts Codex through its installed Node.js,
that sign-in succeeds, and that `lake build --wfail` succeeds inside the
container without writes to the read-only elan directory. Inspect the
build log to confirm that moving the restored `.lake` to `/work` rebuilds
only changed modules and dependencies. Confirm the generated pull request
or no-change comment, its checks and review, and any subsequent fix-round
response. Record any failure on the area's tracking queue for correction.

[spend-limits]: https://developers.openai.com/api/docs/guides/spend-limits
