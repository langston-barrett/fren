# Review engines

The `pr-review` workflow uses the repository variable `PR_REVIEW_ENGINE`:
unset or empty selects `claude`, as does `claude`; `codex` selects Codex.
Any other value fails preparation before a credential is used. Both
engines read the same prepared brief, diff, context and probe results,
and use the same `check.py` verdict checks and posting job. Claude keeps
its existing models. Codex uses exactly `gpt-6.1-sol`, with high reasoning
effort for a full review and medium for `fixes` and `rebase` checks.

## Provisioning Codex

The owner must provision `CODEX_REVIEW_AUTH_JSON` before selecting Codex.
Use a dedicated, CI-only ChatGPT login in a new private `CODEX_HOME` on
your own machine. Never copy the VM's shared login, your ordinary
`~/.codex/auth.json`, or an agent's current session. File storage is
required; an OS keychain entry cannot be mounted into CI:

```sh
review_home=$(mktemp -d)
chmod 700 "$review_home"
printf '%s\n' 'cli_auth_credentials_store = "file"' > "$review_home/config.toml"
CODEX_HOME="$review_home" codex login
gh secret set CODEX_REVIEW_AUTH_JSON --repo langston-barrett/fren < "$review_home/auth.json"
rm -rf "$review_home"
gh variable set PR_REVIEW_ENGINE --repo langston-barrett/fren --body codex
```

These are owner setup commands, not workflow steps. Do not print the auth
file or pass its contents as a command-line argument. To switch back,
set the variable to `claude` or remove it; retain the existing
`CLAUDE_CODE_OAUTH_TOKEN` for that engine.

Codex may refresh this login inside CI: its private auth directory is
writable. The workflow compares credential values after teardown and
filters the review against both the original and refreshed values. A
rotation emits the static `CODEX_REVIEW_AUTH_JSON renewal required`
message in the log, summary and review artifact. The owner must repeat
the dedicated login and replace the secret before another run. A failed
login also reports that renewal may be needed. The workflow cannot
persist a refresh and has no token with Secrets write permission. It
never uploads auth, sessions, raw model events or stderr. Failed runs
print only bounded diagnostics after credential filtering and command
neutralization, using the author workflow's diagnostic helper. Only a
checked review, machine names and a static renewal notice enter the
artifact that the posting job reads.

## Isolation and tests

The threat model at the top of `claude-review.yml` applies to both
engines. Codex reuses the author workflow's pinned tool image, regular
file reader, credential extraction/leak detector and confirmed teardown.
Its separate sandbox mounts the head read-only and passes no runner
environment, GitHub token, host processes or Docker socket. Network is
available to Codex for inference and login refresh; no network tool is
available to the model. The model never executes the head's code.

The trusted catalog and config remove shell, patch, image, web, app,
plugin and delegation tools. Catalog metadata matters as well as feature
flags: in the pinned CLI, `multi_agent_version` can enable delegation
despite a disabled feature. The catalog explicitly clears it. A small
trusted stdio MCP supplies only Read, literal Grep, Glob and Write to
`review.md`; its resource helpers expose no content. Reads reject links,
nonregular files, private configuration and paths outside the checkout.
Read returns bounded byte pages with `next_offset`; Grep and Glob give
continuation offsets if the result is too large. Follow those offsets
to inspect an entire diff or every match. The checkout's instructions,
links, `.codex`, `.agents` and `.claude` are removed before either model
runs. The common brief contains the workflow commit's review rules.

`lint` runs the Python suites and `test_codex_sandbox.sh`. The latter
builds the production image, runs its real pinned CLI against an offline
fake Responses server, and rejects any unexpected advertised tool. The
fixture also tries unsupported execution, patch, web and delegation
calls. A hostile stand-in checks the actual container boundaries,
read-only checkout, writable private auth, stdin and child teardown,
including cancellation. Unit tests cover engine selection, effort,
path restrictions, continuation, original/refreshed credential filtering
and Codex final-message publication through the common verdict checker.
These exercise the real CLI and container with simulated inference and
credentials; they do not claim a live authenticated review.
