#!/usr/bin/env bash
# The shared job definitions, called only inside sandbox.sh.
set -euo pipefail
case "$1" in
  own-spec-agreement)
    lake -R -Kcheck_reqs=1 build --wfail Reqs
    lake -R -Kcheck_reqs=1 build fren_test
    out=$(FREN_QUERY_CACHE= lake env .lake/build/bin/fren_test --job ownSpecAgreement)
    echo "$out"
    test "$out" = '[]'
    ;;
  methods-agree)
    lake build --wfail fren_test
    export LEAN_ABORT_ON_PANIC=1
    part() {
      local name="${*// /-}" status=0
      lake env .lake/build/bin/fren_test --job methodsAgree "$@" > "/tmp/methods-$name.out" || status=$?
      if [ "$status" -ne 0 ]; then
        local how="exit status $status" sig
        if [ "$status" -gt 128 ] && sig=$(kill -l $((status - 128)) 2>/dev/null); then how="$how, signal SIG$sig"; fi
        echo "methodsAgree $* ended with $how"
        return 1
      fi
    }
    code=0
    # One part at a time, as on main, to bound solver memory.
    part own || code=1
    part ui 0 1 || code=1
    part fuzz || code=1
    for f in /tmp/methods-*.out; do
      cat "$f"
      test "$(tail -n 1 "$f")" = '[]' || code=1
    done
    exit "$code"
    ;;
  coverage)
    version=$("$(dirname "$(elan which lean)")/clang" --version | sed -n 's/^clang version \([0-9]*\).*/\1/p')
    COVERAGE_RUNTIME=$(find "/usr/lib/llvm-$version" -name 'libclang_rt.profile*.a' | grep -E 'x86_64|linux/libclang_rt.profile.a' | head -n 1)
    LLVM_COV="/usr/lib/llvm-$version/bin/llvm-cov"
    export COVERAGE_RUNTIME LLVM_COV
    lake -R -Kcoverage="$COVERAGE_RUNTIME" build fren fren_test fren_coverage FrenFuzz FrenFuzzFrontends
    lake -Kcoverage="$COVERAGE_RUNTIME" test
    for gcov in false true; do
      status=0
      lake exe fren_coverage "$gcov" > "/tmp/coverage-$gcov.log" 2>&1 || status=$?
      if [ "$status" -ne 2 ]; then
        cat "/tmp/coverage-$gcov.log"
        echo "fren_coverage $gcov: expected exit 2, got $status"
        exit 1
      fi
    done
    lake exe fren_coverage "$LLVM_COV" gcov
    ;;
  fuzz-frontends)
    lake build fren_fuzz_frontends
    # Run IDs distinguish workflows, and attempts give reruns fresh seeds.
    # Counts above 2500 can overlap the next attempt's seeds.
    base=$((1000000 + SLOW_RUN * 1000000 + SLOW_ATTEMPT * 10000))
    fuzz() { lake env .lake/build/bin/fren_fuzz_frontends --avoid-known --out fuzz "$@"; }
    fuzz --count "$SLOW_COUNT" --seed "$base" & a=$!
    fuzz --count "$SLOW_COUNT" --seed "$((base + SLOW_COUNT))" & b=$!
    fuzz --guards --count "$SLOW_COUNT" --seed "$((base + 2 * SLOW_COUNT))" & c=$!
    fuzz --guards --count "$SLOW_COUNT" --seed "$((base + 3 * SLOW_COUNT))" & d=$!
    code=0
    for pid in "$a" "$b" "$c" "$d"; do wait "$pid" || code=1; done
    if compgen -G 'fuzz/results-*.jsonl' > /dev/null; then
      {
        echo '### Front-end fuzzer'
        echo
        echo "The specs are in the artifact fuzz-frontends-$SLOW_RUN."
        echo
        lake env .lake/build/bin/fren_fuzz_frontends --report fuzz
      } > .lake/slow-summary.md || code=1
    fi
    exit "$code"
    ;;
  *) echo 'Unknown slow job' >&2; exit 2 ;;
esac
