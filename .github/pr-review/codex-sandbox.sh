#!/usr/bin/env bash
# codex-sandbox.sh IMAGE WORK OUTPUT AUTH COMMAND [ARG...]
# The model has no execution tool. Only the trusted MCP reads the head;
# its only write is review.md. No runner environment or socket is passed.
set -euo pipefail
image=$1 work=$2 output=$3 auth=$4
shift 4
here=$(cd "$(dirname "$0")/.." && pwd)
name=${CODEX_CONTAINER:?}
uid=$(id -u) gid=$(id -g)
if [ "$uid" = 0 ]; then uid=65534; gid=65534; fi
cleanup() { docker rm --force "$name" > /dev/null 2>&1 || true; }
trap cleanup EXIT
trap 'exit 143' TERM
trap 'exit 130' INT
exec 3<&0
docker run --rm --interactive --pull never --name "$name" --init \
  --network bridge --ipc private --user "$uid:$gid" \
  --read-only --cap-drop ALL --security-opt no-new-privileges \
  --pids-limit 128 --cpus 4 --memory 4g \
  --tmpfs /tmp:rw,nosuid,nodev,noexec,size=256m \
  --tmpfs "/home/codex:rw,nosuid,nodev,noexec,uid=$uid,gid=$gid,mode=0700,size=256m" \
  --env HOME=/home/codex --env CODEX_HOME=/auth \
  --volume "$work:/work:ro" --volume "$output:/agent:rw" \
  --volume "$auth:/auth:rw" --volume "$here:/trusted:ro" \
  --workdir /work "$image" "$@" <&3 &
child=$!
exec 3<&-
wait "$child"
