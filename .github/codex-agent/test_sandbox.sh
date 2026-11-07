#!/usr/bin/env bash
# Exercise the real container with a hostile stand-in, including teardown.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
scratch=$(mktemp -d "${RUNNER_TEMP:-/tmp}/codex-sandbox.XXXXXX")
name=codex-agent-test-$(cat /proc/sys/kernel/random/uuid)
host_pid= sandbox_pid=
cleanup() {
  docker rm --force "$name" > /dev/null 2>&1 || true
  [ -z "$host_pid" ] || kill "$host_pid" 2>/dev/null || true
  [ -z "$sandbox_pid" ] || kill "$sandbox_pid" 2>/dev/null || true
  rm -rf "$scratch"
}
trap cleanup EXIT
mkdir "$scratch/work" "$scratch/output" "$scratch/auth" "$scratch/elan"
chmod 755 "$scratch"
chmod 777 "$scratch/work" "$scratch/output" "$scratch/auth"
printf '%s\n' 'runner file command' > "$scratch/command"
printf '%s\n' 'prompt on stdin' "$scratch/command" > "$scratch/prompt"
docker pull --quiet ubuntu:24.04 > /dev/null
# Deliberately leave fake runner credentials in a host process and in the
# caller environment. None may reach the container, even through /proc.
env ACTIONS_RUNTIME_TOKEN=host-only-test-token bash -c \
  'exec -a codex-host-sentinel sleep 120' &
host_pid=$!
status=0
out=$(env CODEX_CONTAINER="$name" GH_TOKEN=host-only-test-token \
  ACTIONS_RUNTIME_TOKEN=host-only-test-token GITHUB_ENV="$scratch/command" \
  bash "$here/sandbox.sh" ubuntu:24.04 "$scratch/work" "$scratch/output" \
  "$scratch/auth" "$scratch/elan" bash /trusted/hostile-codex.sh < "$scratch/prompt") || status=$?
printf '%s\n' "$out"
[ "$status" = 0 ] || { echo "FAIL: stand-in exited $status"; exit 1; }
if grep -q '^REACHED:' <<< "$out"; then echo 'FAIL: sandbox escape'; exit 1; fi
[ "$(grep -c '^blocked:' <<< "$out")" = 14 ]
grep -q '^done$' <<< "$out"
[ "$(cat "$scratch/command")" = 'runner file command' ]
[ "$(cat "$scratch/work/changed")" = allowed ]
[ "$(cat "$scratch/output/result")" = allowed ]
sleep 4
[ ! -e "$scratch/output/orphan" ]
[ -z "$(docker ps --all --quiet --filter "name=^/$name$")" ]

# Cancellation must tear down children too, before a later step starts.
CODEX_CONTAINER="$name" bash "$here/sandbox.sh" ubuntu:24.04 \
  "$scratch/work" "$scratch/output" "$scratch/auth" "$scratch/elan" \
  bash -c 'echo ready > /agent/ready; sleep 120' > "$scratch/cancel.log" 2>&1 &
sandbox_pid=$!
for _ in $(seq 1 50); do
  [ ! -e "$scratch/output/ready" ] || break
  sleep 0.1
done
[ -e "$scratch/output/ready" ]
kill -TERM "$sandbox_pid"
status=0
wait "$sandbox_pid" || status=$?
sandbox_pid=
[ "$status" = 143 ]
[ -z "$(docker ps --all --quiet --filter "name=^/$name$")" ]
echo 'codex sandbox: boundaries, stdin and child teardown passed'
bash "$here/test_lake_sandbox.sh"
