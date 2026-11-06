#!/usr/bin/env bash
# Real container boundaries and pinned-CLI tools; no live login/inference.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
image=${CODEX_REVIEW_TEST_IMAGE:-codex-review-test:local}
if [ -z "${CODEX_REVIEW_TEST_IMAGE:-}" ]; then
  docker build --tag "$image" "$here/../codex-agent"
fi
docker run --rm --network none --read-only --cap-drop ALL --security-opt no-new-privileges \
  --tmpfs /tmp:rw,nosuid,nodev,size=256m --volume "$(dirname "$here"):/trusted:ro" \
  "$image" python3 -I -B -m unittest discover -s /trusted/pr-review -p test_codex_cli.py

scratch=$(mktemp -d "${RUNNER_TEMP:-/tmp}/codex-review-test.XXXXXX")
name=codex-review-test-$(cat /proc/sys/kernel/random/uuid)
host_pid= sandbox_pid=
cleanup() {
  docker rm --force "$name" > /dev/null 2>&1 || true
  [ -z "$host_pid" ] || kill "$host_pid" 2>/dev/null || true
  [ -z "$sandbox_pid" ] || kill "$sandbox_pid" 2>/dev/null || true
  rm -rf "$scratch"
}
trap cleanup EXIT
mkdir "$scratch/work" "$scratch/output" "$scratch/auth"
chmod 755 "$scratch" "$scratch/work"
chmod 777 "$scratch/output" "$scratch/auth"
echo 'runner file command' > "$scratch/command"
printf '%s\n' 'prompt on stdin' "$scratch/command" > "$scratch/prompt"
env ACTIONS_RUNTIME_TOKEN=host-only-test-token bash -c \
  'exec -a codex-review-host-sentinel sleep 120' &
host_pid=$!
out=$(env CODEX_CONTAINER="$name" GH_TOKEN=host-only-test-token \
  ACTIONS_RUNTIME_TOKEN=host-only-test-token GITHUB_ENV="$scratch/command" \
  bash "$here/codex-sandbox.sh" "$image" "$scratch/work" "$scratch/output" \
  "$scratch/auth" bash /trusted/pr-review/hostile-codex.sh < "$scratch/prompt")
printf '%s\n' "$out"
! grep -q '^REACHED:' <<< "$out"
[ "$(grep -c '^blocked:' <<< "$out")" = 14 ]
grep -q '^done$' <<< "$out"
[ "$(cat "$scratch/command")" = 'runner file command' ]
[ ! -e "$scratch/work/changed" ]
[ "$(cat "$scratch/output/result")" = allowed ]
[ "$(cat "$scratch/auth/auth.json")" = refreshed-fixture ]
sleep 4
[ ! -e "$scratch/output/orphan" ]
[ -z "$(docker ps --all --quiet --filter "name=^/$name$")" ]

CODEX_CONTAINER="$name" bash "$here/codex-sandbox.sh" "$image" \
  "$scratch/work" "$scratch/output" "$scratch/auth" \
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
echo 'Codex review sandbox: boundaries, stdin, refresh and teardown passed'
