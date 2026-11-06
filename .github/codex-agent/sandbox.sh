#!/usr/bin/env bash
# sandbox.sh IMAGE WORK OUTPUT AUTH ELAN COMMAND [ARG...]
#
# Only WORK, OUTPUT and the private Codex AUTH directory are writable host
# mounts. The runner's environment, processes, home, socket and file-command
# paths are absent. Network access is available for Codex and dependencies.
# Destroy the container and all its children before returning to the runner.
set -euo pipefail

image=$1 work=$2 output=$3 auth=$4 elan=$5
shift 5
here=$(cd "$(dirname "$0")" && pwd)
name=${CODEX_CONTAINER:-codex-agent-$(cat /proc/sys/kernel/random/uuid)}
uid=$(id -u) gid=$(id -g)
if [ "$uid" = 0 ]; then uid=65534; gid=65534; fi
cleanup() { docker rm --force "$name" > /dev/null 2>&1 || true; }
trap cleanup EXIT
trap 'exit 143' TERM
trap 'exit 130' INT
exec 3<&0

# Docker's default PID namespace is private; host/container PID sharing is
# deliberately never requested.
docker run --rm --interactive --pull never --name "$name" --init \
  --network bridge --ipc private --user "$uid:$gid" \
  --read-only --cap-drop ALL --security-opt no-new-privileges \
  --pids-limit 512 --cpus 4 --memory 12g \
  --tmpfs /tmp:rw,nosuid,nodev,size=1g \
  --tmpfs "/home/codex:rw,nosuid,nodev,uid=$uid,gid=$gid,mode=0700,size=2g" \
  --env HOME=/home/codex --env CODEX_HOME=/auth --env ELAN_HOME=/opt/elan \
  --env PATH=/opt/elan/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin \
  --volume "$work:/work:rw" --volume "$output:/agent:rw" \
  --volume "$auth:/auth:rw" --volume "$elan:/opt/elan:ro" \
  --volume "$here:/trusted:ro" --workdir /work "$image" "$@" <&3 &
child=$!
exec 3<&-
wait "$child"
