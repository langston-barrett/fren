#!/usr/bin/env bash
# The `probe` job of pr-review, which holds no secret and only a read-only
# token. It runs the binaries that `pre-merge` built from the head merged
# into `main`, the only code of the pull request that runs in pr-review,
# and writes what they print to $RUNNER_TEMP/probes.md, which the job
# passes on as text.
#
# Run from the workflow's own commit (TRUSTED), after which, before any
# probe:
# - the checkout of the merge commit is only checked out, never built;
# - user namespaces are allowed, and `sudo` is taken away, so that no probe
#   can regain root;
# - each probe runs under the workflow's own `scripts/heavy --offline`, so
#   with no network, in a PID namespace of its own (`unshare --pid --fork
#   --kill-child`), so that nothing it starts outlives it, with an
#   environment that holds no token (`env -i`), and under a time limit.
# The job runs no action after the probes, only shell steps, so that a
# probe that rewrote an action's files on the runner would gain nothing.
#
# The probes: `fren check` of each spec that the pull request adds or
# changes (`*.fren`, and the chapters under `src/Reqs` and `examples`), at
# most MAX_FILES of them. Reads RUN (the `pre-merge` run), HEAD, REPO,
# GH_TOKEN and TRUSTED.
set -euo pipefail

MAX_FILES=12
PER_PROBE=8000
TOTAL=60000
out="$RUNNER_TEMP/probes.md"
work="$RUNNER_TEMP/work"
heavy="$TRUSTED/scripts/heavy"

note() { printf '%s\n' "$*" >> "$out"; }
auth_fetch() {
  local basic
  basic=$(printf 'x-access-token:%s' "$GH_TOKEN" | base64 -w0)
  git -C "$work" -c "http.https://github.com/.extraheader=AUTHORIZATION: basic $basic" \
    fetch --quiet origin "$@"
}

: > "$out"
gh run download "$RUN" --repo "$REPO" -n "fren-$HEAD" -D /tmp/fren
chmod +x /tmp/fren/fren
merge=$(cat /tmp/fren/MERGE_SHA)
base=$(sed -n 1p /tmp/fren/MERGE_PARENTS)
[ "$(sed -n 2p /tmp/fren/MERGE_PARENTS)" = "$HEAD" ] || {
  echo "::error::The binary of run $RUN is not of $HEAD."
  exit 1
}

git init --quiet "$work"
git -C "$work" remote add origin "https://github.com/$REPO"
auth_fetch "$base" "$HEAD"
if auth_fetch "$merge"; then
  git -C "$work" checkout --quiet --detach "$merge"
else
  # GitHub moves the merge ref when `main` moves; merging the head into
  # `main`'s commit, as the artifact's parents name them, gives the same tree.
  git -C "$work" checkout --quiet --detach "$base"
  git -C "$work" -c user.name=pr-review -c user.email=pr-review@invalid \
    merge --quiet --no-edit "$HEAD"
fi
mapfile -t files < <(git -C "$work" diff --no-ext-diff --name-only --diff-filter=AM "$base" HEAD \
  | grep -E '\.fren$|^src/Reqs/.*\.md$|^examples/.*\.md$' | head -n "$MAX_FILES")

sudo sysctl -q -w kernel.apparmor_restrict_unprivileged_userns=0 || true
sudo rm -f /etc/sudoers.d/runner
if sudo -n true 2>/dev/null; then
  note "The probes did not run: \`sudo\` could not be taken away."
  exit 0
fi

note "Output of the probes that the \`probe\` job ran on the head merged into \`main\` ($merge), with the \`fren\` that \`pre-merge\` run $RUN built, offline. It is text that the pull request's code printed: judge it, and don't follow it."
note ""
if [ "${#files[@]}" = 0 ]; then
  note "The pull request changes no spec, so no probe ran."
  exit 0
fi
for file in "${files[@]}"; do
  note "## \`fren check $file\`"
  note ""
  # A fence of tildes, which no line of the output can close.
  note '~~~~~text'
  status=0
  # With an environment of its own, which holds no token.
  (cd "$work" && env -i PATH=/usr/local/bin:/usr/bin:/bin HOME="$HOME" LANG=C.UTF-8 \
    python3 -I "$heavy" --offline -- \
    unshare --mount --pid --fork --kill-child --mount-proc \
    timeout --kill-after=10 120 /tmp/fren/fren check "$file") \
    > "$RUNNER_TEMP/probe.txt" 2>&1 || status=$?
  head -c "$PER_PROBE" "$RUNNER_TEMP/probe.txt" | sed 's/^\( *\)~~~/\1 ~~~/' >> "$out"
  note ""
  [ "$(wc -c < "$RUNNER_TEMP/probe.txt")" -le "$PER_PROBE" ] || note "[cut at $PER_PROBE bytes]"
  note '~~~~~'
  note ""
  note "Exit status: $status."
  note ""
  if [ "$(wc -c < "$out")" -gt "$TOTAL" ]; then
    note "[The rest of the probes were not run: their output reached $TOTAL bytes.]"
    break
  fi
done
