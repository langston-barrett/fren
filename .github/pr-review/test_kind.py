"""Tests of kind.py's decision. Run with
`python3 -B -m unittest discover -s .github/pr-review` (the `lint` workflow
does)."""

import unittest

from kind import decide

OLD = "a" * 40
HEAD = "b" * 40


def comment(at, body):
    return {"createdAt": f"2026-11-02T{at}:00Z", "body": body, "author": {"login": "same"}}


def review(at, sha, clean=True):
    verdict = "no blocking issues" if clean else "blocking issues"
    return comment(at, f"Review of {sha}: {verdict}\n\n1. [non-blocking] x")


def pr(*comments, head=HEAD):
    return {"headRefOid": head, "comments": list(comments)}


class Decide(unittest.TestCase):
    def kind(self, p, event="workflow_dispatch"):
        return decide(p, event)["kind"]

    def test_no_comments(self):
        self.assertEqual(self.kind(pr()), "full")

    def test_fixes_after_clean_review(self):
        d = decide(pr(review("01:00", OLD), comment("02:00", f"fixes only: new head {HEAD[:8]}")), "workflow_run")
        self.assertEqual((d["kind"], d["previous"]), ("fixes", OLD))

    def test_fixes_after_blocking_review(self):
        p = pr(review("01:00", OLD, clean=False), comment("02:00", f"**Fixes only** (head {HEAD})"))
        self.assertEqual(self.kind(p), "fixes")

    def test_rebase_after_clean_review(self):
        p = pr(review("01:00", OLD), comment("02:00", f"rebase only: {HEAD[:7]}, no conflicts"))
        self.assertEqual(self.kind(p), "rebase")

    def test_rebase_after_blocking_review(self):
        p = pr(review("01:00", OLD, clean=False), comment("02:00", f"rebase only: {HEAD[:8]}"))
        self.assertEqual(self.kind(p), "full")

    def test_request_that_names_no_head(self):
        p = pr(review("01:00", OLD), comment("02:00", "fixes only, for the review of aaaaaaaa"))
        self.assertEqual(self.kind(p), "full")

    def test_short_prefix_is_no_name(self):
        p = pr(review("01:00", OLD), comment("02:00", f"fixes only: {HEAD[:6]}"))
        self.assertEqual(self.kind(p), "full")

    def test_request_that_predates_the_previous_review(self):
        # The comment names the head, but no head had a review before it.
        p = pr(comment("01:00", f"fixes only: {HEAD[:8]}"), review("02:00", OLD))
        self.assertEqual(self.kind(p), "full")

    def test_head_already_reviewed(self):
        p = pr(review("01:00", OLD), comment("02:00", f"fixes only: {HEAD[:8]}"), review("03:00", HEAD))
        self.assertEqual(self.kind(p, "workflow_run"), "skip")
        # By hand, the head is reviewed again, in full: the request came
        # before the head's own review.
        p = pr(review("01:00", HEAD), comment("02:00", f"fixes only: {HEAD[:8]}"))
        self.assertEqual(self.kind(p), "full")

    def test_later_comment_under_the_same_login(self):
        # Another agent's later comment that names the head decides, since
        # every agent posts under one login.
        p = pr(review("01:00", OLD), comment("02:00", f"fixes only: {HEAD[:8]}"),
               comment("03:00", f"Queued {HEAD[:8]} after updating the branch"))
        self.assertEqual(self.kind(p), "full")

    def test_later_comment_about_another_head(self):
        # A comment that does not name the head leaves the request standing.
        p = pr(review("01:00", OLD), comment("02:00", f"fixes only: {HEAD[:8]}"),
               comment("03:00", "Coordinator: waiting for main to go green"))
        self.assertEqual(self.kind(p), "fixes")

    def test_reviews_are_not_requests(self):
        p = pr(review("01:00", OLD), comment("02:00", f"Review of {HEAD}: no blocking issues (fixes only)"))
        self.assertEqual(self.kind(p, "workflow_run"), "skip")


if __name__ == "__main__":
    unittest.main()
