#!/usr/bin/env bash
# Prepares the review of a pull request's head that `pre-merge` passed on:
# finds the pull request and that run, downloads the binaries that the run
# built to /tmp/fren and /tmp/fren_test, checks out the merge commit that
# they were built from, and decides the kind of review (kind.py). Writes
# its decisions to `$GITHUB_OUTPUT`, and, for a run with nothing to
# review, `kind=skip` with the reason.
#
# Reads EVENT (the workflow's event), PR_INPUT (the pull request of a run
# by hand), RUN_ID, RUN_SHA, RUN_BRANCH and RUN_PULL (the `pre-merge` run
# of a workflow_run, its head, its branch and its pull request), REPO,
# GH_TOKEN, and
# TRUSTED, the directory of this script, from the workflow's own commit
# rather than from the checkout.
set -euo pipefail

out() { echo "$1=$2" >> "$GITHUB_OUTPUT"; }
skip() { echo "Nothing to review: $1"; out kind skip; out reason "$1"; exit 0; }
# Fetches with the token, which the checkout does not keep, so that the
# reviewer's git has no credentials.
auth_fetch() {
  local basic
  basic=$(printf 'x-access-token:%s' "$GH_TOKEN" | base64 -w0)
  git -c "http.https://github.com/.extraheader=AUTHORIZATION: basic $basic" \
    fetch --quiet origin "$@"
}

if [ "$EVENT" = workflow_run ]; then
  pr=$RUN_PULL
  # GitHub sometimes leaves a run's pull requests empty.
  if [ -z "$pr" ]; then
    pr=$(gh pr list --repo "$REPO" --head "$RUN_BRANCH" --state open \
      --json number,headRefOid \
      | jq -r --arg sha "$RUN_SHA" '[.[] | select(.headRefOid == $sha)][0].number // empty')
  fi
else
  pr=$PR_INPUT
fi
if [ -z "$pr" ]; then
  skip "the pre-merge run $RUN_ID is of no pull request"
fi
gh pr view "$pr" --repo "$REPO" \
  --json number,state,isDraft,author,headRefOid,headRefName,title,body,comments,commits \
  > "$RUNNER_TEMP/pr.json"
head=$(jq -r .headRefOid "$RUNNER_TEMP/pr.json")
branch=$(jq -r .headRefName "$RUNNER_TEMP/pr.json")
out pr "$pr"
out head "$head"
out branch "$branch"

if [ "$EVENT" = workflow_run ]; then
  [ "$(jq -r .state "$RUNNER_TEMP/pr.json")" = OPEN ] || skip "#$pr is not open"
  [ "$(jq -r .isDraft "$RUNNER_TEMP/pr.json")" = false ] || skip "#$pr is a draft"
  [ "$(jq -r .author.is_bot "$RUNNER_TEMP/pr.json")" = false ] || skip "#$pr is a bot's"
  # A newer head has its own run of `pre-merge`, and its own review.
  [ "$head" = "$RUN_SHA" ] || skip "#$pr's head $head is newer than $RUN_SHA"
  run=$RUN_ID
else
  run=$(gh run list --repo "$REPO" --workflow pre-merge --branch "$branch" \
    --event pull_request --limit 100 --json headSha,databaseId,conclusion \
    | jq -r --arg head "$head" \
      '[.[] | select(.headSha == $head and .conclusion == "success")][0].databaseId // empty')
  if [ -z "$run" ]; then
    echo "::error::No run of pre-merge passed on $head, the head of #$pr."
    exit 1
  fi
fi
out run "$run"

gh run download "$run" --repo "$REPO" -n "fren-$head" -D /tmp/fren
gh run download "$run" --repo "$REPO" -n "fren_test-$head" -D /tmp/fren_test
chmod +x /tmp/fren/fren /tmp/fren_test/fren_test
merge=$(cat /tmp/fren/MERGE_SHA)
base=$(sed -n 1p /tmp/fren/MERGE_PARENTS)
[ "$(sed -n 2p /tmp/fren/MERGE_PARENTS)" = "$head" ] || {
  echo "::error::The binaries of run $run are not of $head."
  exit 1
}
out merge "$merge"
out base "$base"

# GitHub moves the pull request's merge ref when `main` moves, so the merge
# commit may be gone; merging the head into `main`'s commit, as the
# artifact's parents name them, rebuilds the same tree.
auth_fetch "$base" "$head"
if auth_fetch "$merge"; then
  git checkout --quiet --detach "$merge"
else
  git checkout --quiet --detach "$base"
  git -c user.name=pr-review -c user.email=pr-review@invalid \
    merge --quiet --no-edit "$head"
  echo "::notice::Rebuilt the merge commit $merge as $(git rev-parse HEAD)."
fi
git log -1 --format='Checked out %H (%s)'

# An update from `main` (`gh pr update-branch`) of a reviewed head needs no
# new review: a merge of the reviewed head and a commit of `main`, with the
# tree that merging them gives, so without a resolution of its own.
if [ "$EVENT" = workflow_run ] \
  && [ "$(git rev-list --parents -n 1 "$head" | wc -w)" = 3 ]; then
  reviewed=$(git rev-parse "$head^1")
  from=$(git rev-parse "$head^2")
  if jq -e --arg sha "$reviewed" \
      'any(.comments[]; .body | ltrimstr("\n") | startswith("Review of " + $sha + ":"))' \
      "$RUNNER_TEMP/pr.json" > /dev/null \
    && git merge-base --is-ancestor "$from" origin/main \
    && [ "$(git merge-tree --write-tree "$reviewed" "$from")" = "$(git rev-parse "$head^{tree}")" ]; then
    skip "$head only merges main's $from into the reviewed head $reviewed"
  fi
fi

python3 -I "$TRUSTED/kind.py" "$RUNNER_TEMP/pr.json" "$EVENT" "$RUNNER_TEMP" > "$RUNNER_TEMP/kind"
kind=$(sed -n 's/^kind=//p' "$RUNNER_TEMP/kind")
reason=$(sed -n 's/^reason=//p' "$RUNNER_TEMP/kind")
previous=$(sed -n 's/^previous=//p' "$RUNNER_TEMP/kind")
# A light check diffs the previous head; one that GitHub no longer serves
# gets a full review.
if [ -n "$previous" ] && ! auth_fetch "$previous"; then
  kind=full
  reason="$previous, the reviewed head, can no longer be fetched"
  previous=
fi
[ "$kind" != skip ] || skip "$reason"
echo "Review: $kind, since $reason"
out kind "$kind"
out reason "$reason"
out previous "$previous"
