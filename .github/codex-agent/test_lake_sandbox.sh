#!/usr/bin/env bash
# Exercise the real Lake cache through the author sandbox.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
scratch=$(mktemp -d "${RUNNER_TEMP:-/tmp}/codex-lake-sandbox.XXXXXX")
trap 'rm -rf "$scratch"' EXIT
chmod 755 "$scratch"
mkdir "$scratch/work" "$scratch/output" "$scratch/auth"
chmod 777 "$scratch/work" "$scratch/output" "$scratch/auth"

# Reuse only the exact pinned toolchain. On a runner without it, install into
# private test state using the same elan installer as the Lean CI action.
pin=$(cat "$root/lean-toolchain")
toolchain=${pin/:/---}
toolchain=${toolchain//\//--}
elan=${ELAN_HOME:-$HOME/.elan}
if [ ! -x "$elan/bin/lake" ] || [ ! -x "$elan/toolchains/$toolchain/bin/lake" ]; then
  elan="$scratch/elan"
  echo "Preparing pinned Lake toolchain"
  started=$SECONDS
  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf |
    env ELAN_HOME="$elan" sh -s -- -y --default-toolchain none
  env ELAN_HOME="$elan" "$elan/bin/elan" toolchain install "$pin"
  env ELAN_HOME="$elan" "$elan/bin/elan" default "$pin"
  echo "Toolchain preparation: $((SECONDS - started)) seconds"
fi
cp "$root/lean-toolchain" "$scratch/work/lean-toolchain"
cat > "$scratch/work/lakefile.lean" <<'LAKE'
import Lake
open Lake DSL
package probe where
  enableArtifactCache := true
  restoreAllArtifacts := true
lean_lib Probe
LAKE
# A fresh artifact prevents an existing toolchain cache from satisfying the
# negative control before Lake attempts to write it.
printf 'def probe : String := "%s"\n' "$(cat /proc/sys/kernel/random/uuid)" \
  > "$scratch/work/Probe.lean"
sandbox() {
  bash "$here/sandbox.sh" ubuntu:24.04 "$scratch/work" "$scratch/output" \
    "$scratch/auth" "$elan" "$@"
}

# Remove the sandbox override in the child to exercise Lake's real default.
status=0
sandbox env -u LAKE_CACHE_DIR bash -c '
  lake env sh -c '\''printf "default cache: %s\n" "$LAKE_CACHE_DIR"'\''
  lake build Probe
' > "$scratch/default.log" 2>&1 || status=$?
cat "$scratch/default.log"
[ "$status" != 0 ]
grep -F "default cache: /opt/elan/toolchains/$toolchain/lake/cache" "$scratch/default.log"
grep -F "failed to cache artifact: read-only file system" "$scratch/default.log"
# Discard partial outputs of the failed build, not the restored fixture below.
rm -rf "$scratch/work/.lake"

sandbox bash -c '
  set -euo pipefail
  lake env sh -c '\''
    test "$LAKE_CACHE_DIR" = /work/.lake/author-cache
    mkdir -p "$LAKE_CACHE_DIR"
    echo child > "$LAKE_CACHE_DIR/child-write"
  '\''
  if touch /opt/elan/sandbox-write-test 2>/dev/null; then
    echo "FAIL: toolchain mount is writable"; exit 1
  fi
  echo "lake env child wrote to cache; toolchain write denied"
  lake build Probe
  test -f .lake/author-cache/child-write
  test -n "$(find .lake/author-cache/artifacts -type f -print -quit)"
  test -f .lake/build/lib/lean/Probe.olean
  cp -a .lake/build /tmp/restored-build
  rm -rf .lake/build .lake/author-cache
  cp -a /tmp/restored-build .lake/build
  before=$(sha256sum .lake/build/lib/lean/Probe.olean)
  inode=$(stat -c %i .lake/build/lib/lean/Probe.olean)
  lake build Probe > /tmp/reuse.log 2>&1
  cat /tmp/reuse.log
  test "$before" = "$(sha256sum .lake/build/lib/lean/Probe.olean)"
  test "$inode" = "$(stat -c %i .lake/build/lib/lean/Probe.olean)"
  if grep -E "Building Probe|Built Probe" /tmp/reuse.log; then
    echo "FAIL: restored build was rebuilt"; exit 1
  fi
  echo "codex sandbox: Lake cache and restored artifacts passed"
'
