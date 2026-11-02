"""Tests of check.py, run with test_kind.py."""

import base64
import hashlib
import unittest

from check import comment, hashed_names, leaks, problem, scrub, verdicts

HEAD = "b" * 40
OK = f"Review of {HEAD}: no blocking issues"
BAD = f"Review of {HEAD}: blocking issues"
SECRET = "sk-ant-oat01-Zq3x9KfL2mPw7RtY5vBn8HjC4dGs6AeU1oIk0"
# Every review says which probes it ran and which it could not.
PROBED = "\n\nProbes: ran `fren check a.fren` (`.review/probes.md`); could not run `ui`, which needs a rebuild."


class Problem(unittest.TestCase):
    def test_clean(self):
        text = f"{OK}\n\n1. **[non-blocking, fix before merge]** `a.md:3`. Wording.{PROBED}"
        self.assertIsNone(problem(text, HEAD, "full"))

    def test_blocking(self):
        text = f"{BAD}\n\n1. [blocking] x\n2. [non-blocking] y{PROBED}"
        self.assertIsNone(problem(text, HEAD, "full"))

    def test_probes_required(self):
        self.assertIsNotNone(problem(f"{OK}\n\n1. [non-blocking] x", HEAD, "full"))
        self.assertIsNotNone(problem(f"{OK}\n\nNo probes were needed.", HEAD, "full"))
        for line in ("Probes: none ran.", "**Probes:** ran one.", "**Probes**: ran one.", "_Probes:_ ran one."):
            self.assertIsNone(problem(f"{OK}\n\n{line}", HEAD, "full"), line)

    def test_light_verdict_only_for_light_checks(self):
        self.assertIsNone(problem(f"{OK} (fixes only){PROBED}", HEAD, "fixes"))
        self.assertIsNotNone(problem(f"{OK} (fixes only)", HEAD, "full"))
        self.assertIsNotNone(problem(f"{OK} (rebase only)", HEAD, "fixes"))

    def test_verdicts_share_the_prefix(self):
        self.assertTrue(all(v.startswith(f"Review of {HEAD}: ") for v in verdicts(HEAD, "rebase")))

    def test_verdict_disagrees_with_findings(self):
        self.assertIsNotNone(problem(f"{OK}\n\n1. [blocking] x", HEAD, "full"))
        self.assertIsNotNone(problem(f"{BAD}\n\n1. [non-blocking] x", HEAD, "full"))
        self.assertIsNotNone(problem(BAD, HEAD, "full"))

    def test_unmarked_or_doubly_marked_finding(self):
        self.assertIsNotNone(problem(f"{OK}\n\n1. Wording.", HEAD, "full"))
        self.assertIsNotNone(problem(f"{OK}\n\n1. [non-blocking] [blocking] x", HEAD, "full"))

    def test_strict_marks(self):
        for mark in ("[blockingly]", "[non-blocking-ish]", "[blocking, maybe]", "[Blocking]"):
            self.assertIsNotNone(problem(f"{BAD}\n\n1. {mark} x", HEAD, "full"), mark)
            self.assertIsNotNone(problem(f"{OK}\n\n1. {mark} x", HEAD, "full"), mark)

    def test_nested_items_need_no_mark(self):
        self.assertIsNone(problem(f"{OK}\n\n1. [non-blocking] x:\n   1. a step\n   2. another{PROBED}", HEAD, "full"))

    def test_other_head(self):
        self.assertIsNotNone(problem("Review of " + "c" * 40 + ": no blocking issues", HEAD, "full"))

    def test_token(self):
        self.assertIsNotNone(problem(f"{OK}\n\nsk-ant-oat01-abcdefghijkl", HEAD, "full"))
        self.assertIsNotNone(problem(f"{OK}\n\nghs_" + "a" * 36, HEAD, "full"))

    def test_remote_loading(self):
        for text in ("![x](https://example.com/p.png?d=1)", "![x](/relative.png)", "![x][ref]",
                     '<img src="https://example.com/p.png">', "<https://example.com/?d=1>",
                     "[x](http://example.com)", "see https://evil.example/?d=1",
                     "[x](https://github.com.evil.example/)",
                     # A shortcut reference image, with an entity, or a
                     # protocol-relative destination, in its definition.
                     "See ![logo] here.\n\n[logo]: h&#116;tps://evil.example/x.png",
                     "See ![logo] here.\n\n[logo]: //evil.example/x.png",
                     "See [logo] here.\n\n[logo]: h&#116;tps://evil.example/x.png",
                     "See [logo] here.\n\n[logo]: //evil.example/x.png",
                     "[x](//evil.example/a)", "[x](h&#x74;tp://evil.example)",
                     "[x](h&amp;#116;tps://evil.example)", "&lt;img src=x&gt;",
                     "<!-- hidden -->", "</details>", "x<img src=//evil.example/p>",
                     "`Set<img src=x>`", "a<Picture>"):
            self.assertIsNotNone(problem(f"{OK}\n\n{text}{PROBED}", HEAD, "full"), text)

    def test_github_links(self):
        for text in ("[#670](https://github.com/langston-barrett/fren/pull/670)",
                     "[docs](https://docs.github.com/en/actions)", "[x](//github.com/a)",
                     "a // comment, and `x // y`", "`a < b` and 3 < 4",
                     # Fren's type applications.
                     "`Set<Role>`, `Set<Set<Role>>` and `Rel<Role, Role>`"):
            self.assertIsNone(problem(f"{OK}\n\n{text}{PROBED}", HEAD, "full"), text)

    def test_findings_that_escape_the_column(self):
        # Markdown renders each as a numbered item, so each is a finding.
        for line in (" 1. [blocking] x", "  1. [blocking] x", "1.[blocking] x", "1) [blocking] x"):
            self.assertIsNotNone(problem(f"{OK}\n\n{line}{PROBED}", HEAD, "full"), line)
            self.assertIsNone(problem(f"{BAD}\n\n{line}{PROBED}", HEAD, "full"), line)

    def test_no_blocking_mark_under_a_clean_verdict(self):
        # Even where no finding is recognized, such as an item indented
        # three spaces.
        self.assertIsNotNone(problem(f"{OK}\n\n   1. [blocking] x{PROBED}", HEAD, "full"))
        self.assertIsNotNone(problem(f"{OK}\n\nA [blocking] point.{PROBED}", HEAD, "full"))


class Leaks(unittest.TestCase):
    def test_copies(self):
        part = SECRET.split("-")[-1]
        for text in (SECRET, " ".join(SECRET), SECRET[::-1], SECRET.encode().hex(),
                     SECRET.encode().hex().upper(), base64.b64encode(SECRET.encode()).decode(),
                     base64.b64encode(("xy" + SECRET).encode()).decode(),
                     base64.b64encode(part[3:].encode()).decode(), part[5:25],
                     "\n".join(part[i:i + 4] for i in range(0, len(part), 4))):
            self.assertTrue(leaks(f"Review\n\n{text}\n", [SECRET]), text)

    def test_no_copy(self):
        self.assertFalse(leaks(f"{OK}\n\n1. [non-blocking] Wording of sk-ant- tokens.", [SECRET, ""]))


class Comment(unittest.TestCase):
    def test_scrub(self):
        self.assertEqual(scrub("ran on Box-1 and box-1.", {"box-1"}), "ran on a machine and a machine.")
        self.assertEqual(scrub("boxes", {"box"}), "boxes")

    def test_scrub_by_hash(self):
        hashes = {hashlib.sha256(b"quokka").hexdigest()}
        self.assertEqual(scrub("On Quokka, or (quokka)'s disk: quokkas.", set(), hashes),
                         "On a machine, or (a machine)'s disk: quokkas.")

    def test_hashed_names_are_hashes(self):
        names = hashed_names()
        self.assertTrue(names)
        self.assertTrue(all(len(h) == 64 and int(h, 16) >= 0 for h in names))

    def test_failure_is_no_review(self):
        body, ok = comment("", HEAD, "full", "URL", set())
        self.assertFalse(ok)
        self.assertFalse(body.startswith("Review of"))

    def test_review_is_posted_as_written(self):
        # The comment counts as the review, so it is the review itself,
        # with no note added.
        body, ok = comment(OK + PROBED, HEAD, "full", "URL", set())
        self.assertTrue(ok)
        self.assertEqual(body, OK + PROBED + "\n")


if __name__ == "__main__":
    unittest.main()
