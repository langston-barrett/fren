#!/usr/bin/env bash
# IMAGE WORK COMMAND...: only the checkout is writable on the host.
# No runner credentials, processes, home, Docker socket or file-command
# paths enter the container. Trusted scripts are read-only; toolchains
# download into the private checkout. Network is available for downloads.
set -euo pipefail
image=$1 work=$2
shift 2
here=$(cd "$(dirname "$0")" && pwd)
name=${SLOW_CONTAINER:-slow-check-$(cat /proc/sys/kernel/random/uuid)}
uid=$(id -u) gid=$(id -g)
if [ "$uid" = 0 ]; then uid=65534; gid=65534; fi
cleanup() { docker rm --force "$name" > /dev/null 2>&1 || true; }
trap cleanup EXIT
trap 'exit 143' TERM
trap 'exit 130' INT
docker run --rm --pull never --name "$name" --init \
  --network bridge --ipc private --user "$uid:$gid" \
  --read-only --cap-drop ALL --security-opt no-new-privileges \
  --pids-limit 1024 --cpus 4 --memory 14g \
  --tmpfs /tmp:rw,nosuid,nodev,size=2g \
  --tmpfs "/home/build:rw,nosuid,nodev,uid=$uid,gid=$gid,mode=0700,size=256m" \
  --env HOME=/home/build --env ELAN_HOME=/work/.lake/worker-elan \
  --env TMPDIR=/work/.lake/worker-tmp \
  --env PATH=/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin \
  --env RUNNER_TEMP=/tmp --env LEAN_STACK_SIZE_KB=8388608 \
  --env CI=true --env GITHUB_ACTIONS=true \
  --env GITHUB_STEP_SUMMARY=/work/.lake/slow-summary.md \
  --env "SLOW_RUN=${GITHUB_RUN_ID:-0}" --env "SLOW_ATTEMPT=${GITHUB_RUN_ATTEMPT:-1}" \
  --env "SLOW_COUNT=${SLOW_COUNT:-150}" \
  --volume "$work:/work:rw" \
  --volume "$here:/trusted:ro" --workdir /work "$image" "$@" &
child=$!
wait "$child"
