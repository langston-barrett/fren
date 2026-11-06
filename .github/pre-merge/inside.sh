#!/usr/bin/env bash
set -euo pipefail
# No toolchain selected by the PR executes on the host. Elan downloads it
# into this checkout, without access to runner credentials or home.
mkdir -p "$ELAN_HOME" "$TMPDIR"
if [ "$1" = llvm-version ]; then
  lean --version > /dev/null
  version=$("$(dirname "$(elan which lean)")/clang" --version | sed -n 's/^clang version \([0-9]*\).*/\1/p')
  printf 'LLVM_VERSION=%s\n' "$version"
  exit
fi
# Dependencies can run lakefile code, so they are built here too.
lake build +Smt +cvc5
exec bash /trusted/checks.sh "$@"
