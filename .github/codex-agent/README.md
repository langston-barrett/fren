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
`pr-review/check.py` leak detector checks each against the original auth
JSON, its token/key fields and any refreshed token fields still present.
Files containing known credential copies, plain or encoded, are withheld.
No authentication file is uploaded. A separate fresh runner validates the
patch and publishes it with `FREN_DEV_TOKEN`, without executing patched
code. Workers and publishers have separate branch concurrency groups.
Fix commits end with publisher-generated PR/round trailers, so a failed
response POST does not lose a pushed round. API bodies are bounded below
GitHub's limit, including multibyte text.

## Authentication lifecycle

Provision `CODEX_AUTH_JSON` with a dedicated CI credential. API-key
authentication is the recommended choice for unattended runs. The value
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
