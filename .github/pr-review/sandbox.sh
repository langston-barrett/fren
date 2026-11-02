#!/usr/bin/env bash
# Runs a binary that a pull request built, in a container that can affect
# nothing but its own standard output and error:
#
#   sandbox.sh BIN_DIR WORK_DIR COMMAND [ARG...]
#
# BIN_DIR is mounted read-only at /bin-pr, WORK_DIR read-only at /work (the
# working directory), and COMMAND runs there as `nobody` (65534), with no
# network, a read-only root, a scratch /tmp, no capabilities, no way to
# gain privileges, a time limit, and an environment of only HOME=/tmp: no
# variable of the runner, so no ACTIONS_RUNTIME_TOKEN, GITHUB_ENV or
# GITHUB_PATH, and no docker socket. The caller captures what it prints;
# nothing it writes outlives it. probe.sh runs `fren check` so, and
# test_sandbox.sh checks, with a hostile stand-in for `fren`, that each way
# out fails.
set -euo pipefail

IMAGE=ubuntu:24.04
bin=$1 work=$2
shift 2
exec docker run --rm --pull never --network none --user 65534:65534 --read-only \
  --tmpfs /tmp:rw,nosuid,nodev,size=256m --cap-drop ALL --security-opt no-new-privileges \
  --pids-limit 256 --memory 4g --env HOME=/tmp \
  --volume "$bin:/bin-pr:ro" --volume "$work:/work:ro" --workdir /work \
  "$IMAGE" timeout --kill-after=10 120 "$@"
