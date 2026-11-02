#!/bin/bash
# A hostile stand-in for a pull request's `fren`, for test_sandbox.sh. It
# tries each way out of sandbox.sh's container that a probe could use, and
# prints one line per attempt: `blocked: WHAT` if it failed, `REACHED:
# WHAT` if it worked. It is never run outside that test.
# shellcheck disable=SC2016
try() {
  local what=$1
  shift
  if "$@" > /dev/null 2>&1; then echo "REACHED: $what"; else echo "blocked: $what"; fi
}
temp=${RUNNER_TEMP:-/home/runner/work/_temp}
commands="$temp/_runner_file_commands"
try 'write $GITHUB_ENV' sh -c '[ -n "$GITHUB_ENV" ] && echo "BASH_ENV=/tmp/x" >> "$GITHUB_ENV"'
try 'write $GITHUB_PATH' sh -c '[ -n "$GITHUB_PATH" ] && echo /tmp >> "$GITHUB_PATH"'
try 'write a file command of the runner' sh -c "ls '$commands' && for f in '$commands'/*; do echo BASH_ENV=/tmp/x >> \"\$f\"; done"
try 'overwrite probes.md' sh -c "echo forged > '$temp/probes.md'"
try 'reach the docker socket' sh -c 'test -S /var/run/docker.sock || test -S /run/docker.sock'
try 'read a token from the environment' sh -c 'env | grep -E "TOKEN|ACTIONS_|GITHUB_|_KEY|SECRET"'
try "read a token from another process" sh -c 'cat /proc/[0-9]*/environ 2>/dev/null | tr "\0" "\n" | grep -E "TOKEN|ACTIONS_RUNTIME"'
try 'open a network connection' bash -c 'exec 3<>/dev/tcp/140.82.112.3/443'
try 'resolve a name' getent hosts github.com
try 'write the checkout' sh -c 'echo x > /work/.hostile'
try 'write the binaries' sh -c 'echo x > /bin-pr/.hostile'
try 'write the root filesystem' sh -c 'echo x > /hostile'
try 'become root' sh -c '[ "$(id -u)" = 0 ]'
try 'gain a capability' sh -c 'grep -E "^CapEff:\s*0*[1-9a-f]" /proc/self/status'
echo "done"
