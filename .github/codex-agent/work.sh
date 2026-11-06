#!/usr/bin/env bash
# Runs only inside sandbox.sh. Even the export uses the agent's Git
# configuration, so it belongs inside the container, before teardown.
set -euo pipefail
model=$1 effort=$2 base=$3
codex exec -m "$model" -c model_reasoning_effort="$effort" \
  -c cli_auth_credentials_store=file -s danger-full-access \
  --json -o /agent/last.md -
BASE="$base" python3 /trusted/export.py
