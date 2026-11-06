#!/usr/bin/env bash
# Real hostile-worker probe, including cancellation/child teardown.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
image=ubuntu:24.04@sha256:fe81560990fae86dc4743202b2cb4d3df98d0bcf949173cecef15ce1127ef852
scratch=$(mktemp -d "${RUNNER_TEMP:-/tmp}/slow-sandbox.XXXXXX")
name=slow-test-$(cat /proc/sys/kernel/random/uuid)
host_pid= sandbox_pid=
cleanup() {
  docker rm --force "$name" > /dev/null 2>&1 || true
  [ -z "$host_pid" ] || kill "$host_pid" 2>/dev/null || true
  [ -z "$sandbox_pid" ] || kill "$sandbox_pid" 2>/dev/null || true
  rm -rf "$scratch"
}
trap cleanup EXIT
mkdir "$scratch/work"
chmod 755 "$scratch"
chmod 777 "$scratch/work"
printf 'host command\n' > "$scratch/command"
docker pull --quiet "$image" > /dev/null
env ACTIONS_RUNTIME_TOKEN=slow-host-only-token sleep 120 &
host_pid=$!
out=$(env GH_TOKEN=slow-host-only-token ACTIONS_RUNTIME_TOKEN=slow-host-only-token \
  GITHUB_ENV="$scratch/command" GITHUB_OUTPUT="$scratch/command" \
  GITHUB_STEP_SUMMARY="$scratch/command" SLOW_CONTAINER="$name" \
  bash "$here/sandbox.sh" "$image" "$scratch/work" \
  bash /trusted/hostile-worker.sh "$scratch/command")
printf '%s\n' "$out"
grep -q '^worker boundaries passed$' <<< "$out"
[ "$(cat "$scratch/command")" = 'host command' ]
[ "$(cat "$scratch/work/changed")" = allowed ]
sleep 4
[ ! -e "$scratch/work/orphan" ]
[ -z "$(docker ps --all --quiet --filter "name=^/$name$")" ]
SLOW_CONTAINER="$name" bash "$here/sandbox.sh" "$image" "$scratch/work" \
  bash -c 'echo ready > /work/ready; sleep 120' > "$scratch/cancel.log" 2>&1 &
sandbox_pid=$!
for _ in $(seq 1 50); do
  [ ! -e "$scratch/work/ready" ] || break
  sleep 0.1
done
[ -e "$scratch/work/ready" ]
kill -TERM "$sandbox_pid"
status=0
wait "$sandbox_pid" || status=$?
sandbox_pid=
[ "$status" = 143 ]
[ -z "$(docker ps --all --quiet --filter "name=^/$name$")" ]
echo 'slow worker: isolation and teardown passed'
