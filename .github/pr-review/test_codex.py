"""Policy, MCP path boundaries and Codex output publication checks."""
import base64
import contextlib
import fnmatch
import io
from itertools import product
import json
import os
from pathlib import Path
import subprocess
import sys
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

    def results(self, name, args):
        found, cursor = {}, (0, 0)
        for _ in range(1000):
            reply = read_tools.respond({"method": "tools/call", "params": {
                "name": name, "arguments": dict(args, offset=cursor[0], column=cursor[1])}})
            self.assertNotIn("isError", reply)
            self.assertLessEqual(len(json.dumps(reply).encode()), read_tools.PAGE_BYTES)
            page = json.loads(reply["content"][0]["text"])
            for chunk in page["matches"]:
                prior = found.setdefault(chunk["offset"], "")
                self.assertEqual(chunk["column"], len(prior))
                found[chunk["offset"]] += chunk["text"]
            if page["next_offset"] is None:
                return [found[i] for i in sorted(found)]
            following = page["next_offset"], page["next_column"]
            self.assertGreater(following, cursor)
            cursor = following
        self.fail("search continuation did not finish")

    def read_all(self, path):
        offset, found = 0, ""
        for _ in range(1000):
            reply = read_tools.respond({"method": "tools/call", "params": {
                "name": "Read", "arguments": {"path": path, "offset": offset}}})
            self.assertNotIn("isError", reply)
            self.assertLessEqual(len(json.dumps(reply).encode()), read_tools.PAGE_BYTES)
            page = json.loads(reply["content"][0]["text"])
            found += page["text"]
            if page["next_offset"] is None:
                return found
            self.assertGreater(page["next_offset"], offset)
            offset = page["next_offset"]
        self.fail("read continuation did not finish")

    def test_four_tools(self):
        (self.work / "x.lean").write_text("first\nneedle\nlast\n")
        page = json.loads(read_tools.call("Read", {"path": "x.lean", "offset": 6, "limit": 6}))
        self.assertEqual(page, {"offset": 6, "next_offset": 12, "text": "needle"})
        self.assertEqual(self.results("Grep", {"pattern": "needle"}), ["x.lean:2: needle"])
        self.assertEqual(self.results("Grep", {"pattern": "(a+)+$"}), [])
        self.assertEqual(self.results("Glob", {"pattern": "*.lean"}), ["x.lean"])
        read_tools.call("Write", {"path": "review.md", "content": REVIEW})
        self.assertEqual((self.output / "review.md").read_text(), REVIEW)
        self.assertEqual(json.loads(read_tools.call("Read", {"path": "review.md"}))["text"], REVIEW)
        self.assertIn("review.md", self.results("Glob", {"pattern": "*"}))
        self.assertIn("review.md:1:", "".join(self.results("Grep", {"pattern": HEAD})))

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
        self.assertEqual(self.results("Glob", {"pattern": "*"}), [])
        for path in ("../review.md", "/auth/auth.json", "other", ".git/config"):
            with self.assertRaises(ValueError):
                read_tools.call("Write", {"path": path, "content": "x"})
        (self.output / "review.md").symlink_to(self.root / "secret")
        with self.assertRaises(OSError):
            read_tools.call("Write", {"path": "review.md", "content": "x"})
        self.assertEqual((self.root / "secret").read_text(), INITIAL)

    def test_output_bounds(self):
        (self.work / "large").write_text("x" * 3_000_000 + "needle\n")
        reply = read_tools.respond({"method": "tools/call", "params": {
            "name": "Read", "arguments": {"path": "large"}}})
        self.assertLessEqual(len(json.dumps(reply).encode()), read_tools.PAGE_BYTES)
        self.assertIn("needle", read_tools.call("Read", {"path": "large", "offset": 3_000_000}))
        self.assertIn("needle", "".join(self.results("Grep", {"pattern": "needle"})))
        for source in ("a" * (read_tools.PAGE_BYTES - 1) + "≤X",
                       " x y z 0 1 2 [] {} \"\\\n" * 1000,
                       "一🙂≤\x00\x01\"\\" * 1000):
            (self.work / "unicode").write_text(source)
            self.assertEqual(self.read_all("unicode"), source)
        with self.assertRaises(ValueError):
            read_tools.call("Write", {"path": "review.md", "content": "x" * 2_000_001})

    def test_search_and_glob_continuation(self):
        for i in range(100):
            (self.work / f"x{i}").write_text("needle\n")
        self.assertEqual(self.results("Grep", {"pattern": "needle"}),
                         [f"x{i}:1: needle" for i in sorted(range(100), key=lambda i: f"x{i}")])
        self.assertEqual(self.results("Glob", {"pattern": "*"}), sorted(f"x{i}" for i in range(100)))

    def test_recursive_globs_include_files_at_the_directory_root(self):
        paths = ["x.py", "src/a/b.py", "src/Reqs/Style.md", "src/Reqs/Lang/Types.md"]
        for name in paths:
            path = self.work / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("fixture")
        for pattern, expected in (
                ("**/*.py", paths[:2]),
                ("src/Reqs/**/*.md", paths[2:]),
                ("src/**/Reqs/**/Style.md", [paths[2]]),
                ("src/**/**/Style.md", [paths[2]]),
                ("**/src/**/b.py", [paths[1]]),
                ("src/**/missing/*.md", []),
                ("src/*.py", [paths[1]])):
            with self.subTest(pattern=pattern):
                self.assertCountEqual(self.results("Glob", {"pattern": pattern}), expected)

    def test_recursive_globs_preserve_classes_and_handle_repeated_segments(self):
        self.assertTrue(read_tools.glob_matches("*/x.py", "[/**/]/**/x.py"))
        self.assertFalse(read_tools.glob_matches("a/x.py", "[/**/]/**/x.py"))
        self.assertTrue(read_tools.glob_matches("x.py", "**/" * 1200 + "x.py"))
        self.assertFalse(read_tools.glob_matches("x.py", "**/" * 1200 + "absent.py"))

    def test_recursive_globs_agree_with_optional_directory_expansion(self):
        paths = ["/".join(dirs + (leaf,)) for size in range(4)
                 for dirs in product(("a", "b"), repeat=size) for leaf in ("x.py", "y.py")]
        for dirs in product(("a", "*", "**"), repeat=3):
            variants = [""]
            for directory in dirs:
                kept = [prefix + directory + "/" for prefix in variants]
                variants = variants + kept if directory == "**" else kept
            for leaf in ("x.py", "*.py"):
                pattern = "/".join(dirs + (leaf,))
                for path in paths:
                    expected = any(fnmatch.fnmatchcase(path, prefix + leaf) for prefix in variants)
                    self.assertEqual(read_tools.glob_matches(path, pattern), expected, (path, pattern))

    def test_long_unicode_match_and_path_fragments(self):
        path = self.work
        for _ in range(20):
            path /= "🙂" * 40
        path.mkdir(parents=True)
        source = "一" * 1000 + "needle" + "🙂" * 1000
        (path / "x").write_text(source)
        relative = (path / "x").relative_to(self.work).as_posix()
        first = json.loads(read_tools.call("Glob", {"pattern": "*"}))
        self.assertEqual(first["next_offset"], 0)
        self.assertGreater(first["next_column"], 0)
        self.assertEqual(self.results("Glob", {"pattern": "*"}), [relative])
        self.assertEqual(self.results("Grep", {"pattern": "needle"}), [relative + ":1: " + source])

    def test_grep_path_scope(self):
        (self.work / ".review").mkdir()
        (self.work / ".review/diff.patch").write_text("needle diff")
        (self.work / "src").mkdir()
        (self.work / "src/code").write_text("needle code")
        (self.work / "src-other").write_text("needle outside")
        self.assertEqual(self.results("Grep", {"pattern": "needle", "path": ".review/diff.patch"}),
                         [".review/diff.patch:1: needle diff"])
        self.assertEqual(self.results("Grep", {"pattern": "needle", "path": "src"}),
                         ["src/code:1: needle code"])
        for path in ("../src", "/auth", ".git", "src\\code"):
            self.assertTrue(read_tools.respond({"method": "tools/call", "params": {
                "name": "Grep", "arguments": {"pattern": "needle", "path": path}}})["isError"])

    def test_bad_names_and_nonobject_arguments_do_not_break_search(self):
        (self.work / "bad\\name").write_text("needle ignored")
        with open(os.fsencode(self.work) + b"/bad-\xff", "w") as stream:
            stream.write("needle ignored")
        (self.work / "safe").write_text("needle found")
        for args in (None, [], 1, "text"):
            self.assertTrue(read_tools.respond({"method": "tools/call", "params": {
                "name": "Read", "arguments": args}})["isError"])
        self.assertEqual(self.results("Grep", {"pattern": "needle"}), ["safe:1: needle found"])
        requests = [{"jsonrpc": "2.0", "id": 1, "method": "tools/call", "params": {
            "name": "Read", "arguments": []}}, {"jsonrpc": "2.0", "id": 2, "method": "ping"}]
        result = subprocess.run([sys.executable, "-I", "-B", str(Path(read_tools.__file__))],
                                input="\n".join(map(json.dumps, requests)) + "\n",
                                text=True, capture_output=True, timeout=10)
        self.assertEqual(result.returncode, 0, result.stderr)
        replies = list(map(json.loads, result.stdout.splitlines()))
        self.assertTrue(replies[0]["result"]["isError"])
        self.assertEqual(replies[1]["result"], {})

    def test_static_replies_and_errors_fit_envelopes(self):
        for method in ("initialize", "tools/list", "resources/list", "resources/templates/list", "ping"):
            reply = {"jsonrpc": "2.0", "id": 123, "result": read_tools.respond({"method": method})}
            self.assertLessEqual(len(json.dumps(reply).encode()), read_tools.RPC_BYTES)
        denied = read_tools.respond({"method": "tools/call", "params": {"name": "unknown"}})
        self.assertLessEqual(len(json.dumps(denied).encode()), read_tools.PAGE_BYTES)


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
