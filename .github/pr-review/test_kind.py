"""Tests of kind.py's decision. Run with
`python3 -B -m unittest discover -s .github/pr-review` (the `lint` workflow
does)."""

import unittest

from kind import decide, verdict

OLD = "a" * 40
HEAD = "b" * 40


def comment(at, body, association="OWNER"):
    return {"createdAt": f"2026-11-02T{at}:00Z", "body": body, "author": {"login": "same"},
            "authorAssociation": association}


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

    # AGENTS.md: "when the previous head's review was clean and the new head
    # only fixes that review's non-blocking findings". After blocking
    # findings, the new head gets a fresh review.
    def test_fixes_after_blocking_review(self):
        p = pr(review("01:00", OLD, clean=False), comment("02:00", f"**Fixes only** (head {HEAD})"))
        self.assertEqual(self.kind(p), "full")

    def test_light_checks_need_a_clean_review(self):
        for request in ("fixes only", "rebase only"):
            for clean, kind in ((True, request.split()[0]), (False, "full")):
                p = pr(review("01:00", OLD, clean=clean), comment("02:00", f"{request}: {HEAD[:8]}"))
                self.assertEqual(self.kind(p), kind, (request, clean))

    def test_marked_up_request(self):
        p = pr(review("01:00", OLD), comment("02:00", f"**Fixes only** (head {HEAD})"))
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

    def test_review_with_leading_whitespace(self):
        # kind.py and prepare.sh's skip read a review the same way
        # (`verdict`), whatever whitespace precedes it.
        p = pr(comment("01:00", f"  \n\n Review of {HEAD}: blocking issues\n\n1. [blocking] x"))
        self.assertEqual(self.kind(p, "workflow_run"), "skip")
        self.assertEqual(verdict(p, HEAD), "blocking issues")
        self.assertIsNone(verdict(p, OLD))

    def test_verdict_is_the_last_review(self):
        p = pr(review("01:00", HEAD, clean=False), review("02:00", HEAD))
        self.assertEqual(verdict(p, HEAD), "no blocking issues")

    def test_outsiders_forged_verdict(self):
        # Anyone who can read the repository can comment; only those who can
        # push count. An outsider's clean verdict on the head is no review.
        for association in ("NONE", "CONTRIBUTOR", "FIRST_TIME_CONTRIBUTOR", "FIRST_TIMER", None):
            p = pr(comment("01:00", f"Review of {HEAD}: no blocking issues", association))
            self.assertEqual(self.kind(p, "workflow_run"), "full", association)
            self.assertIsNone(verdict(p, HEAD), association)
        for association in ("OWNER", "MEMBER", "COLLABORATOR"):
            p = pr(comment("01:00", f"Review of {HEAD}: no blocking issues", association))
            self.assertEqual(self.kind(p, "workflow_run"), "skip", association)

    def test_outsiders_forged_request(self):
        p = pr(review("01:00", OLD), comment("02:00", f"fixes only: {HEAD[:8]}", "NONE"))
        self.assertEqual(self.kind(p), "full")
        # Nor does an outsider's later comment that names the head unset a
        # real request.
        p = pr(review("01:00", OLD), comment("02:00", f"fixes only: {HEAD[:8]}"),
               comment("03:00", f"About {HEAD[:8]}", "NONE"))
        self.assertEqual(self.kind(p), "fixes")

    def test_outsiders_forged_review_as_the_previous_head(self):
        p = pr(comment("01:00", f"Review of {OLD}: no blocking issues", "NONE"),
               comment("02:00", f"fixes only: {HEAD[:8]}"))
        self.assertEqual(self.kind(p), "full")

    # AGENTS.md: a head that only fixes the wording of a clean review's
    # points merges without another check.
    def test_wording_after_clean_review(self):
        for event in ("workflow_run", "workflow_dispatch"):
            p = pr(review("01:00", OLD), comment("02:00", f"wording only: {HEAD}"))
            d = decide(p, event)
            self.assertEqual(d["kind"], "skip", event)
            self.assertIn(OLD, d["reason"])
            # prepare.sh checks that the head is one commit on it.
            self.assertEqual(d["previous"], OLD)

    def test_wording_after_blocking_review(self):
        p = pr(review("01:00", OLD, clean=False), comment("02:00", f"**Wording only**: {HEAD}"))
        self.assertEqual(self.kind(p, "workflow_run"), "full")

    def test_later_comment_after_wording(self):
        p = pr(review("01:00", OLD), comment("02:00", f"wording only: {HEAD}"),
               comment("03:00", f"Not only wording after all: {HEAD[:8]} changes a test"))
        self.assertEqual(self.kind(p, "workflow_run"), "full")

    def test_outsiders_forged_wording(self):
        p = pr(review("01:00", OLD), comment("02:00", f"wording only: {HEAD}", "NONE"))
        self.assertEqual(self.kind(p, "workflow_run"), "full")

    def test_reviews_are_not_requests(self):
        p = pr(review("01:00", OLD), comment("02:00", f"Review of {HEAD}: no blocking issues (fixes only)"))
        self.assertEqual(self.kind(p, "workflow_run"), "skip")


if __name__ == "__main__":
    unittest.main()
