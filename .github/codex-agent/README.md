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
Only failed build or test jobs start a `pre-merge` fix round. Timeouts and
cancellations alone leave the head unchanged for the coordinator to rerun.
If the agent job fails, the publisher posts a fixed notice without reading
its output. A missing patch also gets a rejection comment.

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
token/key/secret/password values, auth identifiers, other opaque values
and any refreshed values still present. If the final authentication file
cannot be read or parsed, or yields no nonempty credential values, all
output and diagnostics are withheld and the run fails. It scans values,
not common field names from the JSON structure.
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
After container teardown, when final credentials are verified, a failed
sandbox also reports up to three distinct nonblank lines, even when its
raw logs are withheld. It prefers stderr error lines, then Codex's
structured JSON error events, then stderr lines of any kind. Every line is
bounded, redacted for known credentials and opaque token-like strings,
and made inert before printing.
Mentions are broken with zero-width spaces, including entity forms and
code. API bodies are bounded below GitHub's limit after neutralization,
including multibyte text.

## Authentication lifecycle

The current threat model trusts the only accounts that can push, the owner
and `fren-dev`, and the issues we write. Under that model we accept that
code the agent runs can read its model credential, and that any branch
workflow can reach repository secrets. If that trust changes, keep model
authentication outside executed code behind an inference proxy or a
separate execution boundary, and move secrets to protected environments
restricted to trusted default-branch runs, keeping the publishing token
out of contributor-controlled workflows.

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
response. In particular, confirm that a blocking bot review on an
`agent/*` pull request starts a fix round. A bot review that does not match
its validated artifact is skipped with a fixed diagnostic in the prepare
log. Record any failure on the area's tracking queue for correction.

[spend-limits]: https://developers.openai.com/api/docs/guides/spend-limits
