#!/usr/bin/env bash
# Only trusted configuration is loaded; the checkout cannot supply memory,
# hooks, skills, plugins or MCP servers. Auth alone is allowed to refresh.
set -euo pipefail
cp /trusted/pr-review/codex.toml /auth/config.toml
codex exec --strict-config --ignore-rules --ephemeral --skip-git-repo-check \
  --model gpt-6.1-sol -c "model_reasoning_effort=$1" --json \
  --output-last-message /agent/last.md -
