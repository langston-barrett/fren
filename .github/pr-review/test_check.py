"""Tests of check.py, run with test_kind.py."""

import unittest

from check import comment, problem, scrub

HEAD = "b" * 40
OK = f"Review of {HEAD}: no blocking issues"
BAD = f"Review of {HEAD}: blocking issues"


class Problem(unittest.TestCase):
    def test_clean(self):
        self.assertIsNone(problem(f"{OK}\n\n1. **[non-blocking, fix before merge]** `a.md:3`. Wording.", HEAD, "full"))

    def test_blocking(self):
        text = f"{BAD}\n\n1. [blocking] x\n2. [non-blocking] y"
        self.assertIsNone(problem(text, HEAD, "full"))

    def test_light_verdict_only_for_light_checks(self):
        self.assertIsNone(problem(f"{OK} (fixes only)", HEAD, "fixes"))
        self.assertIsNotNone(problem(f"{OK} (fixes only)", HEAD, "full"))
        self.assertIsNotNone(problem(f"{OK} (rebase only)", HEAD, "fixes"))

    def test_verdict_disagrees_with_findings(self):
        self.assertIsNotNone(problem(f"{OK}\n\n1. [blocking] x", HEAD, "full"))
        self.assertIsNotNone(problem(f"{BAD}\n\n1. [non-blocking] x", HEAD, "full"))
        self.assertIsNotNone(problem(BAD, HEAD, "full"))

    def test_unmarked_or_doubly_marked_finding(self):
        self.assertIsNotNone(problem(f"{OK}\n\n1. Wording.", HEAD, "full"))
        self.assertIsNotNone(problem(f"{OK}\n\n1. [non-blocking] [blocking] x", HEAD, "full"))

    def test_nested_items_need_no_mark(self):
        self.assertIsNone(problem(f"{OK}\n\n1. [non-blocking] x:\n   1. a step\n   2. another", HEAD, "full"))

    def test_other_head(self):
        self.assertIsNotNone(problem("Review of " + "c" * 40 + ": no blocking issues", HEAD, "full"))

    def test_token(self):
        self.assertIsNotNone(problem(f"{OK}\n\nsk-ant-oat01-abcdefghijkl", HEAD, "full"))
        self.assertIsNotNone(problem(f"{OK}\n\nghs_" + "a" * 36, HEAD, "full"))


class Comment(unittest.TestCase):
    def test_scrub(self):
        self.assertEqual(scrub("ran on Box-1 and box-1.", {"box-1"}), "ran on a machine and a machine.")
        self.assertEqual(scrub("boxes", {"box"}), "boxes")

    def test_failure_is_no_review(self):
        body, ok = comment("", HEAD, "full", "URL", set())
        self.assertFalse(ok)
        self.assertFalse(body.startswith("Review of"))

    def test_advisory(self):
        body, ok = comment(OK, HEAD, "full", "URL", set())
        self.assertTrue(ok)
        self.assertTrue(body.startswith(OK + "\n"))
        self.assertIn("advisory", body)


if __name__ == "__main__":
    unittest.main()
