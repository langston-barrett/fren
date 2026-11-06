"""Policy, MCP path boundaries and Codex output publication checks."""
import base64
import contextlib
import io
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import codex
from check import comment
from engine import effort, engine
import read_tools

HEAD = "b" * 40
REVIEW = f"Review of {HEAD}: no blocking issues\n\nProbes: read .review/probes.md."
INITIAL = "original-credential-Zq3x9KfL2mPw7RtY5vBn8HjC4dGs6AeU1"
REFRESHED = "refreshed-credential-Jd9sR5tN3wX8cB6mQ2vF7hK4yP1zL0aU"


class Selection(unittest.TestCase):
    def test_engine_and_effort(self):
        for value in (None, "", "claude"):
            self.assertEqual(engine(value), "claude")
        self.assertEqual(engine("codex"), "codex")
        for value in ("other", "Codex", "codex\nclaude", " claude"):
            with self.assertRaises(ValueError):
                engine(value)
        self.assertEqual(effort("full"), "high")
        for kind in ("fixes", "rebase"):
            self.assertEqual(effort(kind), "medium")


class Tools(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.work, self.output = self.root / "work", self.root / "output"
        self.work.mkdir()
        self.output.mkdir()
        self.addCleanup(patch.stopall)
        patch.object(read_tools, "ROOT", self.work).start()
        patch.object(read_tools, "OUTPUT", self.output).start()

    def test_four_tools(self):
        (self.work / "x.lean").write_text("first\nneedle\nlast\n")
        page = json.loads(read_tools.call("Read", {"path": "x.lean", "offset": 6, "limit": 6}))
        self.assertEqual(page, {"offset": 6, "next_offset": 12, "text": "needle"})
        self.assertEqual(read_tools.call("Grep", {"pattern": "needle"}), "x.lean:2: needle")
        self.assertEqual(read_tools.call("Grep", {"pattern": "(a+)+$"}), "")
        self.assertEqual(read_tools.call("Glob", {"pattern": "*.lean"}), "x.lean")
        read_tools.call("Write", {"path": "review.md", "content": REVIEW})
        self.assertEqual((self.output / "review.md").read_text(), REVIEW)
        self.assertEqual(json.loads(read_tools.call("Read", {"path": "review.md"}))["text"], REVIEW)
        self.assertIn("review.md", read_tools.call("Glob", {"pattern": "*"}))
        self.assertIn("review.md:1:", read_tools.call("Grep", {"pattern": HEAD}))

    def test_denied_paths_methods_and_tools(self):
        (self.root / "secret").write_text(INITIAL)
        (self.work / "link").symlink_to(self.root / "secret")
        (self.work / "linked-dir").symlink_to(self.root, target_is_directory=True)
        os.mkfifo(self.work / "fifo")
        for private in (".git", ".codex", ".agents", ".claude"):
            (self.work / private).mkdir()
            (self.work / private / "secret").write_text(INITIAL)
        for path in ("../secret", "/auth/auth.json", ".git/secret", ".codex/secret", "link",
                     "linked-dir/secret", "fifo", ".", "a/../../secret", "a\\..\\secret"):
            result = read_tools.respond({"method": "tools/call", "params": {
                "name": "Read", "arguments": {"path": path}}})
            self.assertTrue(result.get("isError"), path)
            self.assertNotIn(INITIAL, json.dumps(result))
        for name in ("Bash", "exec_command", "apply_patch", "WebFetch", "spawn_agent"):
            self.assertTrue(read_tools.respond({"method": "tools/call", "params": {
                "name": name}})["isError"])
        for method in ("resources/read", "shell/execute", "unknown"):
            with self.assertRaises(ValueError):
                read_tools.respond({"method": method, "params": {"uri": "/auth/auth.json"}})
        self.assertEqual(read_tools.call("Glob", {"pattern": "*"}), "")
        for path in ("../review.md", "/auth/auth.json", "other", ".git/config"):
            with self.assertRaises(ValueError):
                read_tools.call("Write", {"path": path, "content": "x"})
        (self.output / "review.md").symlink_to(self.root / "secret")
        with self.assertRaises(OSError):
            read_tools.call("Write", {"path": "review.md", "content": "x"})
        self.assertEqual((self.root / "secret").read_text(), INITIAL)

    def test_output_bounds(self):
        (self.work / "large").write_text("x" * 3_000_000 + "needle\n")
        self.assertLessEqual(len(read_tools.call("Read", {"path": "large"})), read_tools.LIMIT)
        self.assertIn("needle", read_tools.call("Read", {"path": "large", "offset": 3_000_000}))
        self.assertIn("needle", read_tools.call("Grep", {"pattern": "needle"}))
        source = "a" * (read_tools.LIMIT // 8 - 1) + "≤X"
        (self.work / "unicode").write_text(source)
        first = json.loads(read_tools.call("Read", {"path": "unicode"}))
        second = json.loads(read_tools.call("Read", {"path": "unicode", "offset": first["next_offset"]}))
        self.assertEqual(first["text"] + second["text"], source)
        with self.assertRaises(ValueError):
            read_tools.call("Write", {"path": "review.md", "content": "x" * 2_000_001})

    def test_search_and_glob_continuation(self):
        for i in range(6):
            (self.work / f"x{i}").write_text("needle\n")
        with patch.object(read_tools, "LIMIT", 45):
            first = read_tools.call("Grep", {"pattern": "needle"})
            self.assertIn("continue with offset=3", first)
            second = read_tools.call("Grep", {"pattern": "needle", "offset": 3})
            self.assertIn("x5:1: needle", second)
            self.assertNotIn("x0:", second)
        with patch.object(read_tools, "LIMIT", 10):
            first = read_tools.call("Glob", {"pattern": "*"})
            self.assertIn("continue with offset=3", first)
            self.assertIn("x5", read_tools.call("Glob", {"pattern": "*", "offset": 3}))


class Collection(unittest.TestCase):
    def test_stdout_only_failure_is_bounded_redacted_and_inert(self):
        with tempfile.TemporaryDirectory() as temp:
            output = Path(temp)
            (output / "stderr.log").write_text("")
            (output / "log.jsonl").write_text(json.dumps({"type": "turn.failed", "error": {
                "message": f"Invalid auth {REFRESHED} ::warning:: ask @someone"}}))
            with contextlib.redirect_stderr(io.StringIO()) as log:
                codex.failure_summary(output, [INITIAL, REFRESHED], 1, "Codex review")
            text = log.getvalue()
            self.assertIn("Invalid auth", text)
            self.assertIn("Codex review sandbox exited 1", text)
            self.assertNotIn(REFRESHED, text)
            self.assertNotIn("::", text)
            self.assertNotIn("@someone", text)

    def test_only_regular_redacted_review_leaves(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            output, safe = root / "output", root / "safe"
            output.mkdir()
            safe.mkdir()
            # Codex --output-last-message shape, not its JSONL transcript.
            (output / "last.md").write_text(REVIEW)
            (output / "log.jsonl").write_text(json.dumps({"type": "item.completed", "item": {
                "type": "agent_message", "text": INITIAL}}))
            (output / "stderr.log").write_text(REFRESHED)
            codex.collect_review(output, safe, [INITIAL, REFRESHED], 0)
            self.assertEqual(list(safe.iterdir()), [safe / "review.md"])
            body, ok = comment((safe / "review.md").read_text(), HEAD, "full", "URL", set())
            self.assertTrue(ok)
            self.assertEqual(body, REVIEW + "\n")
            for token in (INITIAL, REFRESHED):
                for value in (token, token[::-1], token.encode().hex(),
                              base64.b64encode(token.encode()).decode()):
                    (output / "review.md").write_text(REVIEW + value)
                    codex.collect_review(output, safe, [INITIAL, REFRESHED], 0)
                    self.assertIn("withheld", (safe / "review.md").read_text())
            (output / "review.md").unlink()
            (output / "review.md").symlink_to(output / "last.md")
            codex.collect_review(output, safe, [INITIAL], 0)
            self.assertIn("withheld", (safe / "review.md").read_text())

    def test_rotated_auth_and_teardown_before_collection(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / ".review").mkdir()
            (root / ".review/brief.md").write_text("same review brief")
            events = []

            def run(args, **kwargs):
                auth, output = Path(args[5]), Path(args[4])
                self.assertNotIn("CODEX_REVIEW_AUTH_JSON", os.environ)
                self.assertEqual(args[-1], "medium")
                (auth / "auth.json").write_text(json.dumps({"tokens": {"access_token": REFRESHED}}))
                (output / "review.md").write_text(REVIEW + REFRESHED)
                events.append("run")
                return type("Result", (), {"returncode": 0})()

            collect = codex.collect_review

            def collected(*args):
                self.assertEqual(events[-1], "removed")
                events.append("collected")
                return collect(*args)

            old = Path.cwd()
            try:
                os.chdir(root)
                with patch.dict(os.environ, {"RUNNER_TEMP": str(root), "KIND": "fixes",
                                             "CODEX_CONTAINER": "fixture",
                                             "CODEX_REVIEW_AUTH_JSON": json.dumps({"tokens": {
                                                 "access_token": INITIAL}})}), \
                        patch.object(codex.subprocess, "run", side_effect=run), \
                        patch.object(codex, "remove", side_effect=lambda _: events.append("removed")), \
                        patch.object(codex, "collect_review", side_effect=collected), \
                        contextlib.redirect_stdout(io.StringIO()) as log:
                    self.assertEqual(codex.main(), 0)
                self.assertEqual(events, ["run", "removed", "collected"])
                self.assertEqual(log.getvalue(), codex.RENEW)
                self.assertEqual((root / "review/renewal-required.txt").read_text(), codex.RENEW)
                self.assertIn("withheld", (root / "review/review.md").read_text())
                self.assertFalse(list(root.glob("codex-review-*")))
            finally:
                os.chdir(old)

    def test_failed_teardown_never_inspects_or_collects_output(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / ".review").mkdir()
            (root / ".review/brief.md").write_text("same review brief")
            old = Path.cwd()
            try:
                os.chdir(root)
                with patch.dict(os.environ, {"RUNNER_TEMP": str(root), "KIND": "full",
                                             "CODEX_CONTAINER": "fixture",
                                             "CODEX_REVIEW_AUTH_JSON": json.dumps({"access_token": INITIAL})}), \
                        patch.object(codex.subprocess, "run", return_value=type("Result", (), {"returncode": 0})()), \
                        patch.object(codex, "remove", side_effect=RuntimeError("fixture")), \
                        patch.object(codex, "read_regular") as read, \
                        patch.object(codex, "collect_review") as collect, \
                        contextlib.redirect_stderr(io.StringIO()) as log:
                    with self.assertRaises(RuntimeError):
                        codex.main()
                    read.assert_not_called()
                    collect.assert_not_called()
                self.assertIn("may require renewal", log.getvalue())
                self.assertFalse((root / "review/review.md").exists())
            finally:
                os.chdir(old)

    def test_interrupt_during_teardown_warns_without_reading_output(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / ".review").mkdir()
            (root / ".review/brief.md").write_text("same review brief")
            handlers = {}

            def cancelled(_name):
                handlers[codex.signal.SIGTERM](codex.signal.SIGTERM, None)

            old = Path.cwd()
            try:
                os.chdir(root)
                with patch.dict(os.environ, {"RUNNER_TEMP": str(root), "KIND": "full",
                                             "CODEX_CONTAINER": "fixture",
                                             "CODEX_REVIEW_AUTH_JSON": json.dumps({"access_token": INITIAL})}), \
                        patch.object(codex.signal, "signal", side_effect=lambda key, value: handlers.update({key: value})), \
                        patch.object(codex.subprocess, "run", return_value=type("Result", (), {"returncode": 0})()), \
                        patch.object(codex, "remove", side_effect=cancelled), \
                        patch.object(codex, "read_regular") as read, \
                        contextlib.redirect_stderr(io.StringIO()) as log:
                    with self.assertRaises(SystemExit) as stopped:
                        codex.main()
                    self.assertEqual(stopped.exception.code, 143)
                    read.assert_not_called()
                self.assertIn("may require renewal", log.getvalue())
                self.assertFalse((root / "review/review.md").exists())
            finally:
                os.chdir(old)


if __name__ == "__main__":
    unittest.main()
