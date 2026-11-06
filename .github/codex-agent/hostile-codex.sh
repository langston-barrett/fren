#!/usr/bin/env bash
# A test-only stand-in for Codex, never run on the host.
# shellcheck disable=SC2016
set -eu
try() {
  local what=$1
  shift
  if "$@" > /dev/null 2>&1; then echo "REACHED: $what"; else echo "blocked: $what"; fi
}
IFS= read -r input
IFS= read -r host_file
[ "$input" = 'prompt on stdin' ] || exit 1
try 'runner variables' sh -c 'env | grep -E "TOKEN|ACTIONS_|GITHUB_|_KEY|SECRET"'
try 'runner process credentials' sh -c 'cat /proc/[0-9]*/environ 2>/dev/null | tr "\0" "\n" | grep -E "TOKEN|ACTIONS_RUNTIME"'
try 'host process marker' sh -c 'cat /proc/[0-9]*/cmdline 2>/dev/null | grep "[c]odex-host-sentinel"'
try 'Docker socket' sh -c 'test -S /var/run/docker.sock || test -S /run/docker.sock'
try 'host-only file' sh -c 'test -r "$1"' sh "$host_file"
try 'runner file commands' sh -c 'test -n "${GITHUB_ENV:-}" && echo bad >> "$GITHUB_ENV"'
try 'root filesystem' sh -c 'echo bad > /hostile'
try 'toolchain mount' sh -c 'echo bad > /opt/elan/hostile'
try 'trusted scripts' sh -c 'echo bad >> /trusted/export.py'
try 'root user' sh -c '[ "$(id -u)" = 0 ]'
try 'sudo' sh -c 'sudo -n true'
try 'capabilities' sh -c 'grep -E "^CapEff:[[:space:]]*0*[1-9a-f]" /proc/self/status'
try 'gain privileges' sh -c 'grep -Eq "^NoNewPrivs:[[:space:]]*0$" /proc/self/status'
try 'mount a filesystem' sh -c 'mkdir /tmp/proc; mount -t proc proc /tmp/proc'
echo allowed > /work/changed
echo allowed > /agent/result
# If these children outlive the command, the test sees the file later.
(sleep 3; echo survived > /agent/orphan) > /dev/null 2>&1 &
echo done
