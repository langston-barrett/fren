#!/usr/bin/env bash
# The `prepare` job of pr-review, which holds no secret and runs nothing
# that the pull request controls. In a checkout of the workflow's own
# commit, it finds the pull request and the passing `pre-merge` run of its
# head, fetches the head's commits as objects (it checks none of them
# out), decides the kind of review (kind.py), and writes into
# $RUNNER_TEMP/context the texts that the reviewer reads: the brief
# (compose.py), the diff and log of the head, and for a light check the
# diff against the previous head. Writes its decisions to
# `$GITHUB_OUTPUT`, and `kind=skip` with the reason when there is nothing
# to review.
#
# Git only reads the pull request's objects here: diffs run with
# `--no-ext-diff --no-textconv`, and attributes and configuration come from
# the workflow's own checkout.
#
# Reads EVENT (the workflow's event), PR_INPUT (the pull request of a run
# by hand), RUN_ID, RUN_SHA, RUN_BRANCH and RUN_PULL (the `pre-merge` run
# of a workflow_run, its head, its branch and its pull request), REPO and
# GH_TOKEN.
set -euo pipefail

here=$(dirname "$0")
context="$RUNNER_TEMP/context"
mkdir -p "$context"
out() { echo "$1=$2" >> "$GITHUB_OUTPUT"; }
skip() { echo "Nothing to review: $1"; out kind skip; out reason "$1"; exit 0; }
# Fetches with the token, which the checkout does not keep.
auth_fetch() {
  local basic
  basic=$(printf 'x-access-token:%s' "$GH_TOKEN" | base64 -w0)
  git -c "http.https://github.com/.extraheader=AUTHORIZATION: basic $basic" \
    fetch --quiet origin "$@"
}
diff() { git diff --no-ext-diff --no-textconv "$@"; }

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
[ -n "$pr" ] || skip "the pre-merge run $RUN_ID is of no pull request"
gh pr view "$pr" --repo "$REPO" \
  --json number,state,isDraft,isCrossRepository,author,headRefOid,headRefName,title,body,comments \
  > "$RUNNER_TEMP/pr.json"
head=$(jq -r .headRefOid "$RUNNER_TEMP/pr.json")
branch=$(jq -r .headRefName "$RUNNER_TEMP/pr.json")
out pr "$pr"
out head "$head"
# A pull request from a fork is never reviewed, by hand either: the probes
# run its code, so its author must be one who can push here.
[ "$(jq -r .isCrossRepository "$RUNNER_TEMP/pr.json")" = false ] || skip "#$pr is from a fork"

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

auth_fetch "$head"
base=$(git merge-base origin/main "$head")
out base "$base"

# An update from `main` (`gh pr update-branch`) of a reviewed head needs no
# new review: a merge of the reviewed head and a commit of `main`, with the
# tree that merging them gives, so with no resolution of its own. Several
# updates in a row are followed back, up to 10; a chain that reaches no
# reviewed head gets a review. The old review stands, so the message says
# whether it found blocking issues: a skip is not an approval.
if [ "$EVENT" = workflow_run ]; then
  commit=$head
  for _ in $(seq 10); do
    [ "$(git rev-list --parents -n 1 "$commit" | wc -w)" = 3 ] || break
    first=$(git rev-parse "$commit^1")
    from=$(git rev-parse "$commit^2")
    git merge-base --is-ancestor "$from" origin/main || break
    [ "$(git merge-tree --write-tree "$first" "$from")" = "$(git rev-parse "$commit^{tree}")" ] || break
    verdict=$(python3 -I "$here/kind.py" verdict "$RUNNER_TEMP/pr.json" "$first")
    if [ -n "$verdict" ]; then
      skip "$head only merges main into $first, whose review stands: $verdict"
    fi
    commit=$first
  done
fi

python3 -I "$here/kind.py" "$RUNNER_TEMP/pr.json" "$EVENT" "$RUNNER_TEMP" > "$RUNNER_TEMP/kind"
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
# A wording-only head is one commit on top of the reviewed head, with no
# rebase (AGENTS.md); any other gets a full review.
if [ "$kind" = skip ] && [ -n "$previous" ]; then
  if [ "$(git rev-list --parents -n 1 "$head")" != "$head $previous" ]; then
    kind=full
    reason="$head asks to skip as wording only, but is not one commit on top of $previous"
  fi
  previous=
fi
[ "$kind" != skip ] || skip "$reason"
echo "Review: $kind, since $reason"
out kind "$kind"

diff --stat "$base" "$head" > "$context/diff-stat.txt"
diff "$base" "$head" > "$context/diff.patch"
git log --no-decorate "$base..$head" > "$context/log.txt"
if [ -n "$previous" ]; then
  old_base=$(git merge-base origin/main "$previous")
  git range-diff --no-ext-diff --no-textconv "$old_base..$previous" "$base..$head" \
    > "$context/range-diff.txt"
  if git merge-base --is-ancestor "$previous" "$head"; then
    diff "$previous" "$head" > "$context/fixes.patch"
  fi
fi
PR=$pr HEAD=$head BASE=$base RUN=$run PREVIOUS=$previous REPO=$REPO \
  python3 -I "$here/compose.py" "$RUNNER_TEMP" "$kind" > "$context/brief.md"
ls -l "$context"
