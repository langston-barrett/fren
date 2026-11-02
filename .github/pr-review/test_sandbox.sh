#!/usr/bin/env bash
# Tests sandbox.sh, which runs the binaries of a pull request in pr-review's
# probe job, with hostile-fren.sh in place of `fren`: every attempt to get
# out must fail, and the runner's files that a later step reads (the file
# commands, and probes.md) must be unchanged. The `lint` workflow runs it,
# on a runner with docker, as the probe job does:
#
#   bash .github/pr-review/test_sandbox.sh
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
temp=${RUNNER_TEMP:-$(mktemp -d)}
scratch=$(mktemp -d "$temp/sandbox-test.XXXXXX")
mkdir "$scratch/bin" "$scratch/work"
cp "$here/hostile-fren.sh" "$scratch/bin/fren"
chmod 755 "$scratch/bin" "$scratch/bin/fren" "$scratch/work"
echo 'mod x' > "$scratch/work/x.fren"
echo "the workflow's probes.md" > "$temp/probes.md"

fingerprint() {
  for f in "$temp/probes.md" "${GITHUB_ENV:-/dev/null}" "${GITHUB_PATH:-/dev/null}" \
      "$temp"/_runner_file_commands/*; do
    [ -f "$f" ] && sha256sum "$f"
  done
  return 0
}
before=$(fingerprint)
docker pull --quiet ubuntu:24.04 > /dev/null
out=$("$here/sandbox.sh" "$scratch/bin" "$scratch/work" /bin-pr/fren check x.fren 2>&1) || true
after=$(fingerprint)
printf '%s\n' "$out"

fail=0
grep -q '^done$' <<< "$out" || { echo "FAIL: the stand-in did not finish"; fail=1; }
if grep -q '^REACHED' <<< "$out"; then echo "FAIL: a way out worked"; fail=1; fi
[ "$(grep -c '^blocked: ' <<< "$out")" = 14 ] || { echo "FAIL: not every attempt was reported blocked"; fail=1; }
[ "$before" = "$after" ] || { echo "FAIL: a file of the runner changed"; diff <(echo "$before") <(echo "$after") || true; fail=1; }
[ ! -e "$scratch/work/.hostile" ] && [ ! -e "$scratch/bin/.hostile" ] \
  || { echo "FAIL: the stand-in wrote a mounted directory"; fail=1; }
rm -rf "$scratch"
[ "$fail" = 0 ] && echo "sandbox: every way out failed"
exit "$fail"
