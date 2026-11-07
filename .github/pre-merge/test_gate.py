"""Gate decisions, failure propagation, and trusted review attestations."""

import ast
import importlib.util
import re
import itertools
import json
import os
from pathlib import Path
import subprocess
import tempfile
import textwrap
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("slow_gate", HERE / "gate.py")
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
REAL_RUN = subprocess.run
HEAD = "a" * 40
REPO = "owner/fren"


def report_runs(event, ref, head="", automatic=0, dispatch="", pr=0):
    """Evaluate the actual reporter scheduling expression, not authorization."""
    workflow = (HERE.parent / "workflows/pre-merge.yml").read_text()
    report = workflow.split("  report:\n", 1)[1]
    condition = re.search(r"^    if: \$\{\{ (.+) \}\}$", report, re.MULTILINE)[1]
    expression = condition.replace("always()", "True")
    for field, supplied in {"github.event_name": event, "github.ref": ref,
                            "needs.prepare.outputs.head": head, "github.event.workflow_run.id": automatic,
                            "inputs.review-run": dispatch, "inputs.pr": pr}.items():
        expression = expression.replace(field, repr(supplied))
    expression = expression.replace("&&", " and ").replace("||", " or ")
    # Only the workflow's Boolean/string subset; no code evaluation or
    # precomputed approval decision stands in for the actual protocol.
    def value(node):
        if isinstance(node, ast.Constant): return node.value
        if isinstance(node, ast.BoolOp):
            values = [value(v) for v in node.values]
            return all(values) if isinstance(node.op, ast.And) else any(values)
        if isinstance(node, ast.Compare) and len(node.ops) == 1:
            left, right = value(node.left), value(node.comparators[0])
            if isinstance(node.ops[0], ast.Eq): return left == right
            if isinstance(node.ops[0], ast.NotEq): return left != right
        raise AssertionError(ast.dump(node))
    return bool(value(ast.parse(expression, mode="eval").body))


class Filters(unittest.TestCase):
    def expect(self, paths, *jobs):
        self.assertEqual({job for job, yes in gate.selected(paths).items() if yes}, set(jobs), paths)

    def test_shared_inputs(self):
        for p in ("lakefile.lean", "lean-toolchain", "lake-manifest.json", "src/FrenCore.lean",
                  "src/FrenCore/Eval.lean", "src/FrenCoreCodes.lean", "src/Fren/Check.lean", "src/FrenCli/Parse/Expr.lean",
                  "src/FrenTestMain.lean", "src/FrenTest/FuzzFrontends.lean",
                  "scripts/test.py", ".github/actions/lake/action.yml",
                  ".github/workflows/slow-checks.yml", ".github/workflows/pre-merge.yml"):
            self.expect([p], *gate.JOBS)

    def test_all_linked_runtime_inputs_and_future_c_files(self):
        root = HERE.parents[1]
        existing = {p.relative_to(root).as_posix() for p in (root / "c").rglob("*") if p.is_file()}
        paths = existing | {"c/glibc_c23.c", "c/mimalloc_malloc.c", "c/mimalloc_lazy_commit.c",
                            "c/new.c", "c/runtime/new.h", "c/runtime/new.S", "c/generated.inc", "c/Makefile"}
        for path in paths:
            with self.subTest(path=path):
                self.expect([path], *gate.JOBS)

    def test_corpus_and_test_lists(self):
        for p in ("src/Reqs/Methods.md", "src/Impls/Models.lean", "src/Reqs.lean"):
            self.expect([p], *gate.JOBS[:3])
        self.expect(["test/ui/lang/nat.fren"], "methods-agree", "coverage")
        self.expect(["test/methods_agree.txt"], "methods-agree", "coverage")
        for p in ("test/coverage.txt", "test/unformalized_rules.txt", "src/FrenCoverage.lean",
                  "src/FrenTestFiles/Example.fren", "lib/test.md"):
            self.expect([p], "coverage")
        self.expect(["examples/arith.fren"], "methods-agree", "coverage")

    def test_unrelated_and_union(self):
        self.expect([])
        self.expect([".github/codex-agent/Dockerfile", ".github/pr-review/check.py", "LICENSE"])
        self.expect(["LICENSE", "test/ui/checks/test.fren"], "methods-agree", "coverage")


class Attestation(unittest.TestCase):
    def test_only_exact_clean_lines(self):
        for suffix in ("", " (fixes only)", " (rebase only)"):
            self.assertEqual(gate.CLEAN.fullmatch(f"Review of {HEAD}: no blocking issues{suffix}")[1], HEAD)
        for line in (f"Review of {HEAD}: blocking issues", f"Review of {HEAD[:7]}: no blocking issues",
                     f"Review of {HEAD}: no blocking issues perhaps", "The workflow did not review"):
            self.assertIsNone(gate.CLEAN.fullmatch(line))

    def test_record_binds_clean_and_blocking_verdicts_to_actual_comment(self):
        for first, recorded in ((f"Review of {HEAD}: no blocking issues", True),
                                (f"Review of {HEAD}: no blocking issues (fixes only)", True),
                                (f"Review of {'b' * 40}: no blocking issues", False),
                                (f"Review of {HEAD}: blocking issues", True),
                                ("The workflow did not review", False)):
            with tempfile.TemporaryDirectory() as temp:
                out = Path(temp, "outputs")
                body = first + "\n\nProbes: none\n"
                Path(temp, "comment.md").write_text(body)
                posted = {"id": 123, "body": body, "created_at": "2026-11-06T12:00:00Z"}
                Path(temp, "posted-comment.json").write_text(json.dumps(posted))
                with patch.dict(os.environ, RUNNER_TEMP=temp, GITHUB_OUTPUT=str(out), HEAD=HEAD, PR="12", POST="", GITHUB_RUN_ATTEMPT="1"):
                    gate.record()
                self.assertIn(f"recorded={str(recorded).lower()}", out.read_text())
                artifact = Path(temp, "posted-review/review.json")
                self.assertEqual(artifact.exists(), recorded)
                if recorded:
                    review = json.loads(artifact.read_text())
                    self.assertEqual((review["commentId"], review["createdAt"]), (123, posted["created_at"]))
                    self.assertIn(gate.artifact_name(12, HEAD), out.read_text())

    def test_record_rejects_posted_text_different_from_checked_review(self):
        with tempfile.TemporaryDirectory() as temp:
            Path(temp, "comment.md").write_text(f"Review of {HEAD}: no blocking issues")
            Path(temp, "posted-comment.json").write_text(json.dumps({"body": "different"}))
            with patch.dict(os.environ, RUNNER_TEMP=temp, GITHUB_OUTPUT=str(Path(temp, "out")), HEAD=HEAD), \
                    self.assertRaisesRegex(ValueError, "differs"):
                gate.record()

    def test_workflow_post_shell_preserves_blocking_comment_metadata(self):
        workflow = (HERE.parent / "workflows/claude-review.yml").read_text()
        block = workflow.split("    # A run by hand posts only where its `post` input says.\n", 1)[1]
        shell = textwrap.dedent(block.split("      run: |\n", 1)[1].split("      env:\n", 1)[0])
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            body = f"Review of {HEAD}: blocking issues\n\n1. [blocking] Example.\n\nProbes: mocked.\n"
            (root / "comment.md").write_text(body)
            bin_dir = root / "bin"
            bin_dir.mkdir()
            gh = bin_dir / "gh"
            gh.write_text("""#!/usr/bin/python3
import json, pathlib, sys
assert sys.argv[1:5] == ['api', 'repos/owner/fren/issues/13/comments', '--method', 'POST']
payload = json.loads(pathlib.Path(sys.argv[sys.argv.index('--input') + 1]).read_text())
print(json.dumps({'id': 123, 'created_at': '2026-11-06T12:00:00Z', 'body': payload['body']}))
""")
            gh.chmod(0o755)
            with patch.dict(os.environ, PATH=str(bin_dir) + os.pathsep + os.environ["PATH"],
                            RUNNER_TEMP=temp, REPO=REPO, PR="12", POST="13", HEAD=HEAD,
                            GH_TOKEN="dummy-token", GITHUB_RUN_ATTEMPT="2", GITHUB_OUTPUT=str(root / "out")):
                result = subprocess.run(["bash", "-euo", "pipefail", "-c", shell], capture_output=True, text=True, check=True)
                gate.record()
            review = json.loads((root / "posted-review/review.json").read_text())
            self.assertEqual((review["pr"], review["commentId"], review["body"]), (13, 123, body))
            self.assertIn("recorded=true", (root / "out").read_text())
            self.assertEqual(result.stdout, "")

    def test_workflow_post_rejects_non_numeric_destinations_before_publication(self):
        workflow = (HERE.parent / "workflows/claude-review.yml").read_text()
        block = workflow.split("    # A run by hand posts only where its `post` input says.\n", 1)[1]
        shell = textwrap.dedent(block.split("      run: |\n", 1)[1].split("      env:\n", 1)[0])
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "comment.md").write_text(f"Review of {HEAD}: blocking issues")
            bin_dir = root / "bin"
            bin_dir.mkdir()
            gh = bin_dir / "gh"
            gh.write_text('#!/bin/sh\n: > "$RUNNER_TEMP/gh-was-called"\nexit 0\n')
            gh.chmod(0o755)
            with patch.dict(os.environ, RUNNER_TEMP=temp, REPO=REPO, PR="12", POST="13/comments/../../13",
                            GH_TOKEN="dummy-token", PATH=str(bin_dir) + os.pathsep + os.environ["PATH"]):
                result = REAL_RUN(["bash", "-euo", "pipefail", "-c", shell], capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("must be a PR number", result.stderr)
            self.assertFalse((root / "gh-was-called").exists())
            self.assertFalse((root / "comment.json").exists())
            self.assertFalse((root / "posted-comment.json").exists())

    def test_reject_fork_closed_wrong_base_and_stale_head(self):
        pr = {"state": "open", "head": {"repo": {"full_name": REPO}, "sha": HEAD},
              "base": {"repo": {"full_name": REPO}, "ref": "main"}}
        self.assertTrue(gate.eligible(pr, REPO, HEAD))
        for key, value in (("state", "closed"), ("head.repo.full_name", "fork/fren"),
                           ("head.repo", None), ("head.sha", "b" * 40), ("base.ref", "other"),
                           ("base.repo.full_name", "other/fren")):
            p = json.loads(json.dumps(pr))
            target = p
            parts = key.split(".")
            for part in parts[:-1]:
                target = target[part]
            target[parts[-1]] = value
            self.assertFalse(gate.eligible(p, REPO, HEAD), key)

    def test_prepare_fails_closed_before_download(self):
        info = {"id": 42, "event": "workflow_run", "run_attempt": 2,
                "path": ".github/workflows/claude-review.yml", "head_repository": {"full_name": REPO},
                "head_branch": "main", "status": "completed", "conclusion": "success"}
        for key, value in (("path", ".github/workflows/fake.yml"), ("head_branch", "trial"),
                           ("status", "in_progress"), ("head_repository", {"full_name": "fork/fren"})):
            candidate = {**info, key: value}
            with patch.dict(os.environ, GITHUB_REPOSITORY=REPO, REVIEW_RUN="42"), \
                    patch.object(gate, "api", return_value=candidate) as api, \
                    patch.object(gate.subprocess, "run") as command:
                gate.prepare()
                self.assertTrue(all(call.args == (f"repos/{REPO}/actions/runs/42",) for call in api.call_args_list))
                command.assert_not_called()


class Aggregate(unittest.TestCase):
    def test_selected_failures_cancellations_and_skips(self):
        for relevant, prepare, pending, slow in itertools.product(
                (True, False), ("success", "failure", "cancelled", "skipped"),
                ("success", "failure", "cancelled", "skipped"),
                ("success", "failure", "cancelled", "skipped")):
            needs = {"prepare": {"result": prepare, "outputs": {"head": HEAD, "pr": "12", "base": "b" * 40, "relevant": str(relevant).lower()}},
                     "pending": {"result": pending}, "slow": {"result": slow}}
            good = prepare == pending == "success" and slow == ("success" if relevant else "skipped")
            with patch.dict(os.environ, NEEDS=json.dumps(needs), GITHUB_REPOSITORY=REPO, REVIEW_RUN="", PR_INPUT=""), \
                    patch.object(gate, "authorized", return_value=True), patch.object(gate, "status") as status:
                if good:
                    gate.finish()
                else:
                    with self.assertRaises(SystemExit):
                        gate.finish()
                self.assertEqual(status.call_args.args[:2], (HEAD, "success" if good else "failure"))

    def test_no_status_when_neither_head_nor_review_run_is_available(self):
        with patch.dict(os.environ, GITHUB_REPOSITORY=REPO, REVIEW_RUN="", NEEDS=json.dumps({"prepare": {"outputs": {}}})), \
                patch.object(gate, "status") as status:
            gate.finish()
            status.assert_not_called()


class MergeDiff(unittest.TestCase):
    def test_git_diff_includes_deleted_and_renamed_paths(self):
        # Filters use git's complete merge-base diff, not the API's capped
        # file list, and disable rename detection so both paths are read.
        with tempfile.TemporaryDirectory() as temp:
            def git(*args):
                return subprocess.check_output(["git", "-C", temp, *args], text=True).strip()
            git("init", "-q")
            git("config", "user.name", "test")
            git("config", "user.email", "test@example.com")
            Path(temp, "src/Reqs").mkdir(parents=True)
            Path(temp, "src/Reqs/Old.md").write_text("old\n")
            git("add", ".")
            git("commit", "-qm", "base")
            base = git("rev-parse", "HEAD")
            Path(temp, "src/Reqs/Old.md").rename(Path(temp, "moved.md"))
            git("add", "-A")
            git("commit", "-qm", "move")
            paths = git("diff", "--no-ext-diff", "--no-textconv", "--no-renames", "--name-only", f"{base}...HEAD").splitlines()
            self.assertIn("src/Reqs/Old.md", paths)
            self.assertTrue(gate.selected(paths)["own-spec-agreement"])


class Protocol(unittest.TestCase):
    """Mock transport only: real prepare/report, provenance, ordering and checks."""
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.out = Path(self.temp.name, "outputs")
        self.main = "b" * 40
        self.merge_parent = self.main
        self.merge_head = HEAD
        self.merge = "c" * 40
        self.anchor = "e" * 40
        self.pr = {"number": 12, "state": "open", "head": {"repo": {"full_name": REPO}, "sha": HEAD},
                   "base": {"repo": {"full_name": REPO}, "ref": "main", "sha": self.anchor}}
        self.prs = {12: self.pr}
        self.reviews = {}
        self.job_contexts = {}
        self.attempt_info = {}
        self.artifact_errors = set()
        self.download_errors = set()
        self.bad_artifacts = set()
        self.expired = set()
        self.comments = []
        self.checks = {10: {"id": 10, "name": "pre-merge", "app": {"slug": "github-actions"}, "conclusion": "success"}}
        self.info = {}
        self.patches = []
        self.before_success_write = None
        self.read_error = False
        self.next_check = 100
        env = dict(GITHUB_REPOSITORY=REPO, REVIEW_RUN="42", PR_INPUT="", CHECK_RUN_ID="",
                   GH_TOKEN="read-only-token", GITHUB_OUTPUT=str(self.out), GITHUB_EVENT_NAME="workflow_run", REVIEW_ATTEMPT="")
        self.env = patch.dict(os.environ, env)
        self.env.start()
        self.addCleanup(self.env.stop)
        for target, replacement in (("api", self.api), ("run", self.git_output)):
            patcher = patch.object(gate, target, side_effect=replacement)
            patcher.start()
            self.addCleanup(patcher.stop)
        patcher = patch.object(gate.subprocess, "run", side_effect=self.command)
        self.command_mock = patcher.start()
        self.addCleanup(patcher.stop)
        patcher = patch.object(gate.subprocess, "check_output", return_value=b"LICENSE\0")
        self.diff = patcher.start()
        self.addCleanup(patcher.stop)
        self.add_review(42, 1, True)

    def add_review(self, run, comment, clean, *, head=HEAD, association="NONE", attested=True):
        body = f"Review of {head}: " + ("no blocking issues" if clean else "blocking issues")
        self.comments.append({"id": comment, "body": body, "created_at": "2026-11-06T12:00:00Z",
                              "author_association": association, "user": {"login": "github-actions" if association == "NONE" else "owner"}})
        if attested:
            self.reviews[run] = {"pr": 12, "head": head, "body": body, "attempt": 2,
                                 "commentId": comment, "createdAt": self.comments[-1]["created_at"]}
            self.info[run] = {"id": run, "event": "workflow_run", "path": ".github/workflows/claude-review.yml",
                              "head_repository": {"full_name": REPO}, "head_branch": "main",
                              "status": "completed", "conclusion": "success", "run_attempt": 2}

    def artifact(self, run):
        r = self.reviews[run]
        return {"id": run, "name": gate.artifact_name(12, r["head"]), "expired": run in self.expired, "workflow_run": {"id": run}}

    def api(self, endpoint, payload=None, method=None):
        from urllib.parse import parse_qs, urlsplit
        parsed = urlsplit(endpoint)
        path, query = parsed.path, parse_qs(parsed.query)
        page = int(query.get("page", [1])[0])
        if "/pulls/" in path:
            if self.read_error:
                raise OSError("review API unavailable")
            return self.prs[int(path.rsplit("/", 1)[1])]
        if path.endswith("/git/ref/heads/main"):
            return {"ref": "refs/heads/main", "object": {"type": "commit", "sha": self.main}}
        if path.endswith("/issues/12/comments"):
            return self.comments[(page-1)*100:page*100]
        if "/actions/runs/" in path:
            run = int(path.split("/runs/")[1].split("/")[0])
            if path.endswith("/jobs"):
                rows = self.job_contexts.get(run, [])
                return {"jobs": rows[(page-1)*100:page*100]}
            if path.endswith("/artifacts"):
                if run in self.artifact_errors:
                    raise OSError("artifact listing failed")
                return {"artifacts": [self.artifact(run)] if run in self.reviews else []}
            if "/attempts/" in path:
                return self.attempt_info[(run, int(path.rsplit("/", 1)[1]))]
            return self.info[run]
        if path.endswith("/actions/artifacts"):
            artifacts = [self.artifact(run) for run in self.reviews if self.artifact(run)["name"] == query["name"][0]]
            return {"artifacts": artifacts[(page-1)*100:page*100]}
        if "/commits/" in path:
            return {"check_runs": list(self.checks.values())[(page-1)*100:page*100]}
        if "/check-runs/" in path:
            check = int(path.rsplit("/", 1)[1])
            if payload["conclusion"] == "success" and self.before_success_write:
                callback, self.before_success_write = self.before_success_write, None
                callback()  # Blocking invalidation wins first; this stale write follows it.
            self.checks[check].update(payload)
            self.patches.append((check, payload["conclusion"]))
            return self.checks[check]
        if path.endswith("/check-runs"):
            self.next_check += 1
            self.checks[self.next_check] = {"id": self.next_check, "app": {"slug": "github-actions"}, **payload}
            return self.checks[self.next_check]
        raise AssertionError(endpoint)

    def command(self, args, **kwargs):
        if args[:3] == ["gh", "run", "download"]:
            run = int(args[3])
            if run in self.download_errors:
                raise subprocess.CalledProcessError(1, args)
            review = self.reviews[run]
            Path(args[-1], "review.json").write_text("not json" if run in self.bad_artifacts else json.dumps(review))
        elif args[:2] == ["git", "fetch"]:
            self.assertNotIn("read-only-token", " ".join(args))
            self.assertIn("AUTHORIZATION: basic ", kwargs["env"]["GIT_CONFIG_VALUE_0"])
        else:
            raise AssertionError(args)
        return subprocess.CompletedProcess(args, 0)

    def git_output(self, *args):
        if args[1] == "rev-parse":
            return self.merge
        return self.merge_parent + " " + self.merge_head

    def outputs(self):
        return dict(line.split("=", 1) for line in self.out.read_text().splitlines()) if self.out.exists() else {}

    def finish(self, outputs=None, prepare="success", slow="skipped", check="10"):
        if outputs is None:
            outputs = {"head": HEAD, "pr": "12", "base": self.main, "relevant": "false"}
        needs = {"prepare": {"result": prepare, "outputs": outputs},
                 "pending": {"result": "success" if prepare == "success" else "skipped"}, "slow": {"result": slow}}
        with patch.dict(os.environ, NEEDS=json.dumps(needs), CHECK_RUN_ID=check):
            gate.finish()

    def test_automatic_and_review_run_only_dispatch_reject_superseded_clean(self):
        for event in ("workflow_run", "workflow_dispatch"):
            with self.subTest(event=event), patch.dict(os.environ, GITHUB_EVENT_NAME=event):
                self.add_review(43, 2, False)
                with self.assertRaisesRegex(ValueError, "current review"):
                    gate.prepare()
                self.assertEqual(self.outputs()["revoked"], "true")
                self.diff.assert_not_called()
                with self.assertRaises(SystemExit):
                    self.finish(self.outputs(), prepare="failure", check="")
                self.assertTrue(all(c["conclusion"] == "failure" for c in self.checks.values()))

    def test_blocking_completion_invalidates_an_already_successful_gate(self):
        gate.prepare()
        self.finish(self.outputs())
        self.assertEqual(self.checks[10]["conclusion"], "success")
        self.add_review(43, 2, False)
        with patch.dict(os.environ, REVIEW_RUN="43"), self.assertRaises(ValueError):
            gate.prepare()
        with patch.dict(os.environ, REVIEW_RUN="43"), self.assertRaises(SystemExit):
            self.finish(self.outputs(), prepare="failure", check="")
        self.assertEqual(self.checks[10]["conclusion"], "failure")

    def test_blocking_arrives_during_work_or_between_success_read_and_write(self):
        for moment in ("during", "publication"):
            with self.subTest(moment=moment):
                self.comments = self.comments[:1]
                self.reviews.pop(43, None)
                if moment == "during":
                    self.add_review(43, 2, False)
                else:
                    self.before_success_write = lambda: (self.add_review(43, 2, False), gate.invalidate(HEAD))
                with self.assertRaises(SystemExit):
                    self.finish()
                self.assertTrue(all(c["conclusion"] == "failure" for c in self.checks.values()))

    def test_bad_attestation_on_manual_pr_still_reports_its_head(self):
        self.info[42]["head_branch"] = "trial"
        with patch.dict(os.environ, PR_INPUT="12"):
            with self.assertRaisesRegex(ValueError, "trusted posted verdict"):
                gate.prepare()
            self.assertEqual(self.outputs()["head"], HEAD)
            with self.assertRaises(SystemExit):
                self.finish(self.outputs(), prepare="failure", check="")
        self.assertEqual(self.checks[10]["conclusion"], "failure")

    def test_manual_pr_path_also_rejects_superseded_clean(self):
        self.add_review(43, 2, False)
        with patch.dict(os.environ, PR_INPUT="12"), self.assertRaises(ValueError):
            gate.prepare()

    def test_newer_clean_supersedes_block_and_old_block_completion_is_ignored(self):
        self.add_review(43, 2, False)
        self.add_review(44, 3, True)
        with patch.dict(os.environ, REVIEW_RUN="43"):
            gate.prepare()
        self.assertFalse(self.out.exists())
        with patch.dict(os.environ, REVIEW_RUN="44"):
            gate.prepare()
            self.finish(self.outputs())
        self.assertEqual(self.checks[10]["conclusion"], "success")

    def test_local_blocking_review_event_revokes_without_starting_tests(self):
        self.add_review(43, 2, False, association="OWNER", attested=False)
        event = {"repository": {"full_name": REPO}, "action": "created", "issue": {"number": 12, "pull_request": {}}, "comment": self.comments[-1]}
        event["issue"]["pull_request"] = {"url": "trusted-api-url"}
        path = Path(self.temp.name, "event.json")
        path.write_text(json.dumps(event))
        with patch.dict(os.environ, GITHUB_EVENT_NAME="issue_comment", GITHUB_EVENT_PATH=str(path), REVIEW_RUN=""):
            with self.assertRaises(ValueError):
                gate.prepare()
            with self.assertRaises(SystemExit):
                self.finish(self.outputs(), prepare="failure", check="")
        self.assertEqual(self.checks[10]["conclusion"], "failure")
        self.diff.assert_not_called()

    def test_editing_a_bot_review_to_blocking_revokes_completed_checks(self):
        self.comments[0]["body"] = f"Review of {HEAD}: blocking issues"
        event = {"repository": {"full_name": REPO}, "action": "created", "issue": {"number": 12, "pull_request": {"url": "pr"}}, "comment": self.comments[0]}
        path = Path(self.temp.name, "event.json")
        path.write_text(json.dumps(event))
        with patch.dict(os.environ, GITHUB_EVENT_NAME="issue_comment", GITHUB_EVENT_PATH=str(path), REVIEW_RUN=""):
            with self.assertRaises(ValueError):
                gate.prepare()
            with self.assertRaises(SystemExit):
                self.finish(self.outputs(), prepare="failure", check="")
        self.assertEqual(self.checks[10]["conclusion"], "failure")
        self.diff.assert_not_called()

    def test_both_current_and_no_relevant_job_cases_remain_successful(self):
        for event in ("workflow_run", "workflow_dispatch"):
            with patch.dict(os.environ, GITHUB_EVENT_NAME=event):
                gate.prepare()
                self.assertEqual(self.outputs()["relevant"], "false")
                self.finish(self.outputs())
                self.assertEqual(self.checks[10]["conclusion"], "success")

    def test_c_runtime_changes_select_every_job_at_preparation(self):
        self.diff.return_value = b"c/glibc_c23.c\0c/future/runtime.S\0"
        gate.prepare()
        self.assertEqual(self.outputs()["relevant"], "true")
        self.assertTrue(all(self.outputs()[job] == "true" for job in gate.JOBS))

    def test_stale_fork_and_merge_mismatch_are_rejected(self):
        for scenario in ("stale", "fork", "merge"):
            with self.subTest(scenario=scenario):
                self.pr["head"]["sha"] = "d" * 40 if scenario == "stale" else HEAD
                self.pr["head"]["repo"]["full_name"] = "fork/fren" if scenario == "fork" else REPO
                if scenario == "merge":
                    with patch.object(gate, "run", return_value="d" * 40), self.assertRaisesRegex(ValueError, "merge ref"):
                        gate.prepare()
                else:
                    gate.prepare()
                    self.assertFalse(self.out.exists())

    def test_missing_or_stale_attempt_cannot_authorize_success(self):
        for scenario in ("missing", "attempt", "branch", "workflow", "in-progress"):
            with self.subTest(scenario=scenario):
                saved = dict(self.info[42])
                if scenario == "missing":
                    self.info[42]["run_attempt"] = 3
                elif scenario == "attempt":
                    self.reviews[42]["attempt"] = 1
                elif scenario == "branch":
                    self.info[42]["head_branch"] = "trial"
                elif scenario == "workflow":
                    self.info[42]["path"] = ".github/workflows/fake.yml"
                else:
                    self.info[42]["status"] = "in_progress"
                with self.assertRaises(SystemExit):
                    self.finish()
                self.assertEqual(self.checks[10]["conclusion"], "failure")
                self.info[42] = saved
                self.reviews[42]["attempt"] = 2

    def test_unattested_or_edited_bot_comment_never_authorizes_green(self):
        self.add_review(43, 2, True, attested=False)
        self.assertFalse(gate.authorized(REPO, 12, HEAD, self.main))
        self.comments.pop()
        self.comments[0]["body"] = f"Review of {HEAD}: blocking issues"
        self.assertFalse(gate.authorized(REPO, 12, HEAD, self.main))

    def test_untrusted_comment_does_not_veto_and_other_head_does_not_veto(self):
        self.add_review(43, 2, False, attested=False)
        self.comments[-1]["user"]["login"] = "outsider"
        self.add_review(44, 3, False, head="d" * 40, association="OWNER", attested=False)
        self.assertTrue(gate.authorized(REPO, 12, HEAD, self.main))

    def test_expired_attestation_fails_even_when_bot_text_is_clean(self):
        self.expired.add(42)
        self.assertFalse(gate.authorized(REPO, 12, HEAD, self.main))
        with self.assertRaises(SystemExit):
            self.finish()
        self.assertEqual(self.checks[10]["conclusion"], "failure")

    def test_deleted_comment_is_not_a_clean_authorization(self):
        self.comments.clear()
        self.assertFalse(gate.authorized(REPO, 12, HEAD, self.main))

    def test_failed_probe_does_not_withhold_a_posted_checked_verdict(self):
        self.info[42]["conclusion"] = "failure"
        gate.prepare()
        self.finish(self.outputs())
        self.assertEqual(self.checks[10]["conclusion"], "success")

    def test_review_api_error_on_post_publication_recheck_fails_closed(self):
        self.before_success_write = lambda: setattr(self, "read_error", True)
        with self.assertRaisesRegex(OSError, "unavailable"):
            self.finish()
        self.assertEqual(self.checks[10]["conclusion"], "failure")

    def test_invalidating_event_keeps_head_when_review_lookup_fails(self):
        self.add_review(43, 2, False)
        with patch.dict(os.environ, REVIEW_RUN="43"), \
                patch.object(gate, "authorized", side_effect=OSError("unavailable")), \
                self.assertRaises(OSError):
            gate.prepare()
        self.assertEqual(self.outputs()["head"], HEAD)
        self.assertEqual(self.outputs()["revoked"], "true")

    def test_unobserved_blocking_comment_cannot_hide_an_attested_block(self):
        self.add_review(43, 2, False)
        self.comments.pop()  # Comment-list lag after the post artifact was uploaded.
        self.assertFalse(gate.authorized(REPO, 12, HEAD, self.main))

    def test_comment_and_check_pagination_and_foreign_check_protection(self):
        for n in range(100, 201):
            self.comments.append({"id": n, "body": "", "created_at": "2026-11-06T12:00:00Z",
                                  "author_association": "OWNER", "user": {"login": "owner"}})
        self.add_review(43, 300, False)
        for n in range(1000, 1101):
            self.checks[n] = {"id": n, "name": "pre-merge", "app": {"slug": "github-actions"}, "conclusion": "success"}
        self.checks[2000] = {"id": 2000, "name": "pre-merge", "app": {"slug": "other"}, "conclusion": "success"}
        self.checks[2001] = {"id": 2001, "name": "lint", "app": {"slug": "github-actions"}, "conclusion": "success"}
        self.checks[2002] = {"id": 2002, "name": "pre-merge", "app": None, "conclusion": "success"}
        with self.assertRaises(SystemExit):
            self.finish()
        self.assertTrue(all(c["conclusion"] == "failure" for i, c in self.checks.items() if i < 2000))
        self.assertEqual(self.checks[2000]["conclusion"], "success")
        self.assertEqual(self.checks[2001]["conclusion"], "success")

    def test_failed_old_check_invalidation_still_fails_own_check(self):
        self.add_review(43, 2, False)
        self.checks[20] = {"id": 20, "name": "pre-merge", "app": {"slug": "github-actions"}, "conclusion": "success"}
        normal_api = self.api
        def api(endpoint, payload=None, method=None):
            if endpoint.endswith("/check-runs/10"):
                raise OSError("cannot patch old check")
            return normal_api(endpoint, payload, method)
        with patch.object(gate, "api", side_effect=api), self.assertRaisesRegex(OSError, "old check"):
            self.finish(check="20")
        self.assertEqual(self.checks[20]["conclusion"], "failure")

    def test_recleaning_during_failed_block_event_does_not_revoke_new_gate(self):
        self.add_review(43, 2, False)
        with patch.dict(os.environ, REVIEW_RUN="43"), self.assertRaises(ValueError):
            gate.prepare()
        self.add_review(44, 3, True)
        with patch.dict(os.environ, REVIEW_RUN="43"):
            self.finish(self.outputs(), prepare="failure", check="")
        self.assertFalse(self.patches)

    def test_issue_comments_from_outsiders_or_other_heads_do_nothing(self):
        for assoc, head in (("NONE", HEAD), ("OWNER", "d" * 40)):
            self.add_review(43, 2, False, head=head, association=assoc, attested=False)
            comment = {**self.comments[-1], "user": {"login": "outsider"}}
            event = {"repository": {"full_name": REPO}, "action": "created", "issue": {"number": 12, "pull_request": {"url": "pr"}}, "comment": comment}
            path = Path(self.temp.name, "event.json")
            path.write_text(json.dumps(event))
            with patch.dict(os.environ, GITHUB_EVENT_NAME="issue_comment", GITHUB_EVENT_PATH=str(path), REVIEW_RUN=""):
                gate.prepare()
            self.assertFalse(self.out.exists())


class RecoveryProtocol(unittest.TestCase):
    """Published comment -> lost authorization -> completion -> revoked green.

    Only transport and failure injection are mocked; recovery reads the real
    run/job/PR protocol and never receives a precomputed approval decision.
    """
    setUp = Protocol.setUp
    add_review = Protocol.add_review
    artifact = Protocol.artifact
    api = Protocol.api
    command = Protocol.command
    git_output = Protocol.git_output
    outputs = Protocol.outputs
    finish = Protocol.finish

    def trusted_post(self, run=43, *, pr=12, head=HEAD, attempt=2, conclusion="failure",
                     event="workflow_run", post=None):
        self.info[run] = {"id": run, "event": event, "path": ".github/workflows/claude-review.yml",
                          "head_repository": {"full_name": REPO}, "head_branch": "main",
                          "status": "completed", "conclusion": conclusion, "run_attempt": attempt}
        workflow = (HERE.parent / "workflows/claude-review.yml").read_text()
        post_block = workflow.split("  post:\n", 1)[1]
        template = re.search(r"^    name: (.+)$", post_block, re.MULTILINE)[1]
        post = str(pr) if post is None and event == "workflow_dispatch" else (post or "")
        target = post or (str(pr) if event == "workflow_run" else "")
        name = (template.replace("${{ inputs.post || (github.event_name == 'workflow_run' && needs.prepare.outputs.pr) || '' }}", target)
                .replace("${{ needs.prepare.outputs.head }}", head)
                .replace("${{ github.run_attempt }}", str(attempt)))
        self.job_contexts[run] = [{"name": name,
                                   "run_id": run, "run_attempt": attempt,
                                   "status": "completed", "conclusion": conclusion}]

    def publish(self, *, clean=False):
        workflow = (HERE.parent / "workflows/claude-review.yml").read_text()
        block = workflow.split("    # A run by hand posts only where its `post` input says.\n", 1)[1]
        shell = textwrap.dedent(block.split("      run: |\n", 1)[1].split("      env:\n", 1)[0])
        root = Path(self.temp.name)
        body = f"Review of {HEAD}: " + ("no blocking issues" if clean else "blocking issues")
        body += "\n\nProbes: protocol regression.\n"
        (root / "comment.md").write_text(body)
        bin_dir = root / "bin"
        bin_dir.mkdir(exist_ok=True)
        gh = bin_dir / "gh"
        gh.write_text("""#!/usr/bin/python3
import json, pathlib, sys
assert sys.argv[1:5] == ['api', 'repos/owner/fren/issues/12/comments', '--method', 'POST']
payload = json.loads(pathlib.Path(sys.argv[sys.argv.index('--input') + 1]).read_text())
print(json.dumps({'id': 2, 'created_at': '2026-11-07T00:00:00Z', 'body': payload['body'],
                  'author_association': 'NONE', 'user': {'login': 'github-actions[bot]'}}))
""")
        gh.chmod(0o755)
        env = {**os.environ, "PATH": str(bin_dir) + os.pathsep + os.environ["PATH"],
               "RUNNER_TEMP": str(root), "REPO": REPO, "PR": "12", "POST": "", "GH_TOKEN": "dummy-token"}
        result = REAL_RUN(["bash", "-euo", "pipefail", "-c", shell], env=env,
                          capture_output=True, text=True, check=True)
        self.assertEqual(result.stdout, "")
        published = json.loads((root / "posted-comment.json").read_text())
        self.comments.append(published)
        return published

    def test_green_through_published_block_lost_attestation_and_completion(self):
        for event, failure in itertools.product(("workflow_run", "workflow_dispatch"),
                ("record", "upload", "cancel", "list", "download", "corrupt", "expired")):
            with self.subTest(event=event, failure=failure):
                self.comments = self.comments[:1]
                self.checks = {10: {"id": 10, "name": "pre-merge", "app": {"slug": "github-actions"}, "conclusion": "success"}}
                self.reviews.pop(43, None)
                self.artifact_errors.clear()
                self.download_errors.clear()
                self.bad_artifacts.clear()
                self.expired.clear()
                self.out.unlink(missing_ok=True)
                local_artifact = Path(self.temp.name, "posted-review")
                if local_artifact.exists():
                    (local_artifact / "review.json").unlink()
                    local_artifact.rmdir()
                with patch.dict(os.environ, REVIEW_RUN="42"):
                    gate.prepare()
                    self.assertEqual(self.outputs()["relevant"], "false")
                    self.finish(self.outputs())
                self.assertEqual(self.checks[10]["conclusion"], "success")
                self.out.unlink()
                published = self.publish()
                self.trusted_post(conclusion="cancelled" if failure == "cancel" else "failure")
                with patch.dict(os.environ, RUNNER_TEMP=self.temp.name, PR="12", POST="", HEAD=HEAD,
                                GITHUB_RUN_ATTEMPT="2"):
                    if failure == "record":
                        with patch.object(Path, "mkdir", side_effect=OSError("recording failed")), self.assertRaises(OSError):
                            gate.record()
                    elif failure != "cancel":
                        gate.record()
                if failure in ("list", "download", "corrupt", "expired"):
                    self.reviews[43] = {"pr": 12, "head": HEAD, "body": published["body"],
                                        "attempt": 2, "commentId": 2, "createdAt": published["created_at"]}
                if failure == "list":
                    self.artifact_errors.add(43)
                elif failure == "download":
                    self.download_errors.add(43)
                elif failure == "corrupt":
                    self.bad_artifacts.add(43)
                elif failure == "expired":
                    self.expired.add(43)
                # This event is completion/dispatch, never issue_comment.
                with patch.dict(os.environ, GITHUB_EVENT_NAME=event, REVIEW_RUN="43", PR_INPUT=""):
                    with self.assertRaisesRegex(ValueError, "revocation-only"):
                        gate.prepare()
                    recovered = self.outputs()
                    self.assertEqual(recovered["head"], HEAD)
                    self.assertEqual(recovered["recovered"], "true")
                    self.assertEqual(recovered["relevant"], "false")
                    with self.assertRaises(SystemExit):
                        self.finish(recovered, prepare="failure", check="")
                self.assertTrue(all(c["conclusion"] == "failure" for c in self.checks.values()))

    def test_report_recovers_when_preparation_has_no_outputs_or_was_cancelled(self):
        self.publish()
        self.trusted_post(conclusion="cancelled")
        for result in ("failure", "cancelled", "success"):
            with self.subTest(result=result), patch.dict(os.environ, REVIEW_RUN="43"):
                with self.assertRaises(SystemExit):
                    self.finish(outputs={"unrelated": "output"}, prepare=result, check="")
                self.assertTrue(all(c["conclusion"] == "failure" for c in self.checks.values()))

    def test_report_retries_context_when_preparation_recovery_failed(self):
        self.publish()
        self.trusted_post()
        real_api = self.api
        def unavailable_jobs(endpoint, payload=None, method=None):
            if "/attempts/" in endpoint and "/jobs?" in endpoint:
                raise OSError("job metadata temporarily unavailable")
            return real_api(endpoint, payload, method)
        with patch.dict(os.environ, REVIEW_RUN="43"):
            with patch.object(gate, "api", side_effect=unavailable_jobs), self.assertRaises(OSError):
                gate.prepare()
            self.assertNotIn("head", self.outputs())
            with self.assertRaises(SystemExit):
                self.finish(outputs=self.outputs() or {"unrelated": "output"}, prepare="failure", check="")
        self.assertEqual(self.checks[10]["conclusion"], "failure")

    def test_workflow_report_runs_for_recovery_only_on_trusted_main_context(self):
        self.assertTrue(report_runs("workflow_run", "refs/heads/main", automatic=43))
        self.assertTrue(report_runs("workflow_dispatch", "refs/heads/main", dispatch="43"))
        self.assertTrue(report_runs("workflow_dispatch", "refs/heads/main", head=HEAD))
        self.assertTrue(report_runs("workflow_dispatch", "refs/heads/main", pr=12))
        self.assertFalse(report_runs("workflow_dispatch", "refs/heads/pr-code", dispatch="43"))
        self.assertTrue(report_runs("issue_comment", "refs/heads/main"))
        self.assertFalse(report_runs("issue_comment", "refs/heads/pr-code"))

    def test_recovered_context_never_authorizes_even_clean_or_no_posted_comment(self):
        self.trusted_post()
        for published_clean in (False, True):
            if published_clean:
                self.publish(clean=True)
            with patch.dict(os.environ, REVIEW_RUN="43"):
                with self.assertRaises(ValueError):
                    gate.prepare()
                # Even an otherwise-successful no-job path stays negative.
                with self.assertRaises(SystemExit):
                    self.finish(self.outputs(), prepare="success", check="")
            self.assertTrue(all(c["conclusion"] == "failure" for c in self.checks.values()))

    def test_recovery_checks_run_attempt_role_and_current_pr_head_provenance(self):
        for invalid in ("workflow", "branch", "repo", "event", "id", "running", "attempt",
                        "job-run", "job-attempt", "job-role", "skip", "ambiguous", "fork", "head", "base", "number"):
            with self.subTest(invalid=invalid):
                self.trusted_post()
                info, job = self.info[43], self.job_contexts[43][0]
                saved_pr = json.loads(json.dumps(self.pr))
                if invalid == "workflow": info["path"] = ".github/workflows/fake.yml"
                elif invalid == "branch": info["head_branch"] = "pr-controlled"
                elif invalid == "repo": info["head_repository"]["full_name"] = "fork/fren"
                elif invalid == "event": info["event"] = "pull_request"
                elif invalid == "id": info["id"] = 44
                elif invalid == "running": info["status"] = "in_progress"
                elif invalid == "attempt": job["name"] = job["name"].replace("attempt 2", "attempt 1")
                elif invalid == "job-run": job["run_id"] = 44
                elif invalid == "job-attempt": job["run_attempt"] = 1
                elif invalid == "job-role": job["name"] = "probe: " + job["name"]
                elif invalid == "skip": job["conclusion"] = "skipped"
                elif invalid == "ambiguous": self.job_contexts[43].append({**job, "name": job["name"].replace("PR 12", "PR 13")})
                elif invalid == "fork": self.pr["head"]["repo"]["full_name"] = "fork/fren"
                elif invalid == "head": self.pr["head"]["sha"] = "d" * 40
                elif invalid == "base": self.pr["base"]["ref"] = "other"
                elif invalid == "number": self.pr["number"] = 13
                self.assertIsNone(gate.revocation_context(REPO, 43))
                self.pr.clear()
                self.pr.update(saved_pr)
        self.assertFalse(self.patches)

    def test_completed_event_attempt_recovers_even_after_a_rerun_started(self):
        self.publish()
        self.trusted_post()
        self.attempt_info[(43, 2)] = dict(self.info[43])
        self.info[43] = {**self.info[43], "run_attempt": 3, "status": "in_progress"}
        with patch.dict(os.environ, REVIEW_RUN="43", REVIEW_ATTEMPT="2"):
            with self.assertRaisesRegex(ValueError, "revocation-only"):
                gate.prepare()
            with self.assertRaises(SystemExit):
                self.finish(self.outputs(), prepare="failure", check="")
        self.assertEqual(self.checks[10]["conclusion"], "failure")

    def test_manual_preview_without_post_intent_cannot_revoke_a_gate(self):
        self.trusted_post(event="workflow_dispatch", post="", conclusion="success")
        with patch.dict(os.environ, REVIEW_RUN="43"):
            gate.prepare()
            self.assertNotIn("head", self.outputs())
            self.finish(outputs={"unrelated": "output"}, prepare="success", check="")
        self.assertFalse(self.patches)
        self.assertEqual(self.checks[10]["conclusion"], "success")

    def test_outputless_manual_reporting_revokes_only_the_requested_current_pr(self):
        other = "d" * 40
        self.trusted_post(pr=13, head=other)
        self.prs[13] = {**self.pr, "number": 13, "head": {"repo": {"full_name": REPO}, "sha": other}}
        with patch.dict(os.environ, REVIEW_RUN="43", PR_INPUT="12"), \
                patch.object(gate, "api", side_effect=self.api) as calls, self.assertRaises(SystemExit):
            self.finish(outputs={"unrelated": "output"}, prepare="cancelled", check="")
        reads = [call.args[0] for call in calls.call_args_list if "/commits/" in call.args[0]]
        self.assertTrue(reads)
        self.assertTrue(all(f"/commits/{HEAD}/" in path for path in reads))
        self.assertEqual(self.checks[10]["conclusion"], "failure")

    def test_post_destination_is_the_recovered_pr_and_manual_mismatch_is_rejected(self):
        self.trusted_post(pr=13, event="workflow_dispatch")
        self.prs[13] = {**self.pr, "number": 13}
        self.assertEqual(gate.revocation_context(REPO, 43)["pr"], 13)
        with patch.dict(os.environ, REVIEW_RUN="43", PR_INPUT="12"), self.assertRaises(ValueError):
            gate.prepare()
        self.assertEqual(self.outputs()["pr"], "12")
        self.assertNotIn("recovered", self.outputs())




class CommentRecovery(unittest.TestCase):
    """Actual comment event -> failed/outputless preparation -> revoked check."""
    setUp = Protocol.setUp
    add_review = Protocol.add_review
    artifact = Protocol.artifact
    api = Protocol.api
    command = Protocol.command
    git_output = Protocol.git_output
    outputs = Protocol.outputs
    finish = Protocol.finish

    def event(self):
        self.add_review(43, 2, False, association="OWNER", attested=False)
        event = {"repository": {"full_name": REPO}, "action": "created",
                 "issue": {"number": 12, "pull_request": {"url": "trusted-api-url"}},
                 "comment": dict(self.comments[-1])}
        path = Path(self.temp.name, "comment-event.json")
        path.write_text(json.dumps(event))
        return event, path

    def test_green_comment_event_recovers_after_checkout_transport_and_cancellation(self):
        for failure in ("checkout", "checkout-cancelled", "first-pr-read", "cancelled-pr-read"):
            with self.subTest(failure=failure):
                self.comments = self.comments[:1]
                self.out.unlink(missing_ok=True)
                self.checks[10]["conclusion"] = "success"
                event, path = self.event()
                with patch.dict(os.environ, GITHUB_EVENT_NAME="issue_comment", GITHUB_EVENT_PATH=str(path),
                                REVIEW_RUN="", PR_INPUT=""):
                    if failure.endswith("pr-read"):
                        error = KeyboardInterrupt if failure == "cancelled-pr-read" else OSError
                        def failed_read(endpoint, *args, **kwargs):
                            if "/pulls/" in endpoint:
                                raise error("first PR read interrupted")
                            return self.api(endpoint, *args, **kwargs)
                        with patch.object(gate, "api", side_effect=failed_read), self.assertRaises(error):
                            gate.prepare()
                    # Checkout failure/cancellation never reached prepare.
                    self.assertEqual(self.outputs(), {})
                    self.assertEqual(self.checks[10]["conclusion"], "success")
                    self.assertTrue(report_runs("issue_comment", "refs/heads/main"))
                    result = "cancelled" if "cancelled" in failure else "failure"
                    with self.assertRaises(SystemExit):
                        self.finish(outputs={}, prepare=result, check="")
                self.assertTrue(all(c["conclusion"] == "failure" for c in self.checks.values()))
                self.assertTrue(all(c.args[0][:3] == ["gh", "run", "download"] for c in self.command_mock.call_args_list))
                self.diff.assert_not_called()

    def test_comment_recovery_rechecks_latest_verdict_and_edits(self):
        for change in ("new-clean", "edited-clean", "event-list-lag"):
            with self.subTest(change=change):
                self.comments = self.comments[:1]
                self.checks[10]["conclusion"] = "success"
                event, path = self.event()
                if change == "new-clean":
                    self.add_review(44, 3, True, association="OWNER", attested=False)
                elif change == "edited-clean":
                    self.comments[-1]["body"] = f"Review of {HEAD}: no blocking issues"
                else:
                    self.comments.pop()  # The trusted publication event precedes list visibility.
                with patch.dict(os.environ, GITHUB_EVENT_NAME="issue_comment", GITHUB_EVENT_PATH=str(path), REVIEW_RUN=""):
                    if change == "event-list-lag":
                        with self.assertRaises(SystemExit):
                            self.finish(outputs={}, prepare="failure", check="")
                    else:
                        self.finish(outputs={}, prepare="cancelled", check="")
                self.assertEqual(self.checks[10]["conclusion"], "failure" if change == "event-list-lag" else "success")

    def test_validated_comment_target_fails_closed_if_latest_review_read_fails(self):
        _, path = self.event()
        def failed_comments(endpoint, *args, **kwargs):
            if "/comments?" in endpoint:
                raise OSError("latest review unavailable")
            return self.api(endpoint, *args, **kwargs)
        with patch.dict(os.environ, GITHUB_EVENT_NAME="issue_comment", GITHUB_EVENT_PATH=str(path), REVIEW_RUN=""), \
                patch.object(gate, "api", side_effect=failed_comments), self.assertRaisesRegex(OSError, "latest review"):
            self.finish(outputs={}, prepare="failure", check="")
        self.assertEqual(self.checks[10]["conclusion"], "failure")

    def test_comment_recovery_rejects_wrong_provenance_or_ineligible_current_head(self):
        for invalid in ("repository", "action", "issue", "outsider", "clean", "head", "fork", "closed", "base", "number"):
            with self.subTest(invalid=invalid):
                saved_pr = json.loads(json.dumps(self.pr))
                event, path = self.event()
                if invalid == "repository": event["repository"]["full_name"] = "fork/fren"
                elif invalid == "action": event["action"] = "deleted"
                elif invalid == "issue": event["issue"].pop("pull_request")
                elif invalid == "outsider":
                    event["comment"].update(author_association="NONE", user={"login": "outsider"})
                elif invalid == "clean": event["comment"]["body"] = f"Review of {HEAD}: no blocking issues"
                elif invalid == "head": self.pr["head"]["sha"] = "d" * 40
                elif invalid == "fork": self.pr["head"]["repo"]["full_name"] = "fork/fren"
                elif invalid == "closed": self.pr["state"] = "closed"
                elif invalid == "base": self.pr["base"]["ref"] = "other"
                elif invalid == "number": self.pr["number"] = 13
                path.write_text(json.dumps(event))
                with patch.dict(os.environ, GITHUB_EVENT_NAME="issue_comment", GITHUB_EVENT_PATH=str(path), REVIEW_RUN=""):
                    gate.prepare()
                    self.finish(outputs={}, prepare="cancelled", check="")
                self.assertFalse(self.patches)
                self.assertEqual(self.checks[10]["conclusion"], "success")
                self.pr.clear()
                self.pr.update(saved_pr)
        self.command_mock.assert_not_called()
        self.diff.assert_not_called()


class TargetSnapshot(unittest.TestCase):
    setUp = Protocol.setUp
    add_review = Protocol.add_review
    artifact = Protocol.artifact
    api = Protocol.api
    command = Protocol.command
    git_output = Protocol.git_output
    outputs = Protocol.outputs
    finish = Protocol.finish

    def test_anchor_main_and_tested_merge_remain_distinct_on_every_entry(self):
        for event, manual in (("workflow_run", ""), ("workflow_dispatch", ""), ("workflow_dispatch", "12")):
            with self.subTest(event=event, manual=manual), patch.dict(os.environ, GITHUB_EVENT_NAME=event, PR_INPUT=manual):
                gate.prepare()
                outputs = self.outputs()
                self.assertNotEqual(self.anchor, self.main)
                self.assertEqual(outputs["pr-base"], self.anchor)
                self.assertEqual(outputs["base"], self.merge_parent)
                self.assertEqual(outputs["merge"], self.merge)
                self.assertEqual(self.diff.call_args.args[0][-1], f"{self.main}...{HEAD}")
                self.finish(outputs)
                self.assertEqual(self.checks[10]["conclusion"], "success")

    def test_stale_main_parent_wrong_head_and_non_merge_never_select_jobs(self):
        for invalid in ("anchor-parent", "other-parent", "wrong-head", "one-parent"):
            with self.subTest(invalid=invalid):
                self.out.unlink(missing_ok=True)
                self.merge_parent = self.anchor if invalid == "anchor-parent" else "d" * 40 if invalid == "other-parent" else self.main
                self.merge_head = "d" * 40 if invalid == "wrong-head" else HEAD
                if invalid == "one-parent": self.merge_head = ""
                with self.assertRaisesRegex(ValueError, "merge ref"):
                    gate.prepare()
                self.assertNotIn("relevant", self.outputs())
                self.assertEqual(self.outputs()["base"], self.main)
                with self.assertRaises(SystemExit):
                    self.finish(self.outputs(), prepare="failure")
        self.diff.assert_not_called()

    def test_main_moves_after_capture_without_relabeling_tested_source_or_cache(self):
        captured = self.main
        def fetch_then_main_moves(args, **kwargs):
            result = self.command(args, **kwargs)
            if args[:2] == ["git", "fetch"]:
                self.main = "d" * 40
                self.pr["base"]["sha"] = "f" * 40  # Anchor metadata may move independently too.
            return result
        with patch.object(gate.subprocess, "run", side_effect=fetch_then_main_moves):
            gate.prepare()
        outputs = self.outputs()
        self.assertEqual(outputs["base"], captured)
        self.assertEqual(outputs["merge"], self.merge)
        self.assertEqual(self.diff.call_args.args[0][-1], f"{captured}...{HEAD}")
        # Reporting uses the tested snapshot for inheritance, not a new main
        # read; the older fast artifact is a separate identity altogether.
        with patch.object(gate, "current_main", side_effect=AssertionError("must retain tested snapshot")):
            self.finish(outputs)
        self.out.unlink()
        with self.assertRaisesRegex(ValueError, "merge ref"):
            gate.prepare()  # A new entry captures newer main and rejects the old merge ref.

    def test_negative_recovery_does_not_mislabel_the_pr_anchor_as_main(self):
        context = gate.current_context(REPO, 12, HEAD)
        self.assertEqual(context, {"pr": 12, "head": HEAD, "pr-base": self.anchor})
        self.assertNotIn("base", context)
        for manual in ("", "12"):
            self.out.unlink(missing_ok=True)
            def no_main(endpoint, *args, **kwargs):
                if "/git/ref/heads/main" in endpoint:
                    raise OSError("main snapshot unavailable")
                return self.api(endpoint, *args, **kwargs)
            with patch.dict(os.environ, PR_INPUT=manual), patch.object(gate, "api", side_effect=no_main):
                with self.assertRaisesRegex(OSError, "main snapshot"):
                    gate.prepare()
                self.assertEqual(self.outputs()["head"], HEAD)
                self.assertNotIn("base", self.outputs())
                with self.assertRaises(SystemExit):
                    self.finish(self.outputs(), prepare="failure", check="")
            self.assertEqual(self.checks[10]["conclusion"], "failure")
        self.assertTrue(all(c.args[0][:3] == ["gh", "run", "download"] for c in self.command_mock.call_args_list))

    def test_main_ref_identity_is_checked(self):
        for ref, kind, sha in (("refs/heads/other", "commit", self.main),
                               ("refs/heads/main", "tag", self.main),
                               ("refs/heads/main", "commit", "not-a-sha")):
            with patch.object(gate, "api", return_value={"ref": ref, "object": {"type": kind, "sha": sha}}), \
                    self.assertRaisesRegex(ValueError, "main commit"):
                gate.current_main(REPO)


class InheritedReview(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.old = os.getcwd()
        os.chdir(self.temp.name)
        self.addCleanup(os.chdir, self.old)
        self.git("init", "-q", "-b", "main")
        self.git("config", "user.name", "test")
        self.git("config", "user.email", "test@example.com")
        Path("file.md").write_text("base\n")
        self.git("add", ".")
        self.git("commit", "-qm", "base")
        self.base = self.git("rev-parse", "HEAD")
        self.git("checkout", "-qb", "feature")
        Path("file.md").write_text("reviewed\n")
        self.git("commit", "-qam", "feature")
        self.reviewed = self.git("rev-parse", "HEAD")

    def git(self, *args):
        return subprocess.check_output(["git", *args], text=True).strip()

    def comment(self, body, time, association="OWNER"):
        return {"body": body, "createdAt": time, "authorAssociation": association}

    def metadata(self, *extra):
        return {"headRefOid": self.git("rev-parse", "HEAD"), "comments": [
            self.comment(f"Review of {self.reviewed}: no blocking issues", "01"),
            *extra,
        ]}

    def test_current_review_and_blocking_override(self):
        self.assertTrue(gate.inherited_review(self.metadata(), self.base))
        meta = self.metadata(self.comment(f"Review of {self.reviewed}: blocking issues", "02"))
        self.assertFalse(gate.inherited_review(meta, self.base))
        meta = self.metadata()
        meta["comments"][0]["authorAssociation"] = "NONE"
        self.assertFalse(gate.inherited_review(meta, self.base))

    def test_manual_review_needs_the_complete_verdict_line(self):
        for suffix in (" perhaps", " (not an allowed light form)"):
            meta = self.metadata()
            meta["comments"][0]["body"] += suffix
            self.assertFalse(gate.inherited_review(meta, self.base))

    def test_wording_shape_and_current_blocking_override(self):
        Path("file.md").write_text("wording\n")
        self.git("commit", "-qam", "wording")
        head = self.git("rev-parse", "HEAD")
        request = self.comment(f"wording only: {head}", "02")
        self.assertTrue(gate.inherited_review(self.metadata(request), self.base))
        self.assertFalse(gate.inherited_review(self.metadata(request, self.comment(
            f"Review of {head}: blocking issues", "03")), self.base))
        self.assertFalse(gate.inherited_review(self.metadata(request, self.comment(
            f"Review of {self.reviewed}: blocking issues", "03")), self.base))
        self.assertFalse(gate.inherited_review(self.metadata(self.comment(
            f"wording only: {head}", "02", "NONE")), self.base))
        Path("AGENTS.md").write_text("process change\n")
        self.git("add", ".")
        self.git("commit", "--amend", "--no-edit", "-q")
        head = self.git("rev-parse", "HEAD")
        self.assertFalse(gate.inherited_review(self.metadata(self.comment(
            f"wording only: {head}", "02")), self.base))

    def test_pure_main_update_and_changed_resolution(self):
        self.git("checkout", "-q", "main")
        Path("other.md").write_text("main\n")
        self.git("add", ".")
        self.git("commit", "-qm", "main")
        main = self.git("rev-parse", "HEAD")
        self.git("checkout", "-q", "feature")
        self.git("merge", "-q", "--no-ff", "--no-edit", "main")
        self.assertTrue(gate.inherited_review(self.metadata(), main))
        Path("file.md").write_text("custom resolution\n")
        self.git("add", ".")
        self.git("commit", "-q", "--amend", "--no-edit")
        self.assertFalse(gate.inherited_review(self.metadata(), main))

    def test_prepare_inherits_against_captured_main_with_real_git_objects(self):
        # A reviewed head is updated from newer main, whose commit is not
        # the PR anchor. Its synthetic merge has a third, distinct identity.
        self.git("checkout", "-q", "main")
        Path("main.md").write_text("new main\n")
        self.git("add", ".")
        self.git("commit", "-qm", "new main")
        main = self.git("rev-parse", "HEAD")
        self.git("checkout", "-q", "feature")
        self.git("merge", "-q", "--no-ff", "--no-edit", "main")
        head = self.git("rev-parse", "HEAD")
        meta = self.metadata()
        self.git("checkout", "-q", "--detach", "main")
        self.git("merge", "-q", "--no-ff", "--no-edit", "feature")
        merge = self.git("rev-parse", "HEAD")
        self.assertNotEqual(main, self.base)
        self.assertFalse(gate.inherited_review(meta, self.base))
        self.assertTrue(gate.inherited_review(meta, main))
        pr = {"number": 12, "state": "open", "head": {"repo": {"full_name": REPO}, "sha": head},
              "base": {"repo": {"full_name": REPO}, "ref": "main", "sha": self.base}}
        comments = [{"id": i, "body": c["body"], "created_at": c["createdAt"],
                     "author_association": "OWNER", "user": {"login": "owner"}}
                    for i, c in enumerate(meta["comments"], 1)]
        def api(endpoint):
            if "/pulls/" in endpoint: return pr
            if endpoint.endswith("/git/ref/heads/main"):
                return {"ref": "refs/heads/main", "object": {"type": "commit", "sha": main}}
            if "/actions/artifacts?" in endpoint: return {"artifacts": []}
            if "/issues/12/comments?" in endpoint: return comments
            raise AssertionError(endpoint)
        real_git_output = gate.run
        def git_output(*args):
            return merge if args == ("git", "rev-parse", "FETCH_HEAD") else real_git_output(*args)
        def command(args, **kwargs):
            # Fetch transport is mocked; all merge, inheritance and diff
            # decisions use the actual objects created above.
            return subprocess.CompletedProcess(args, 0) if args[:2] == ["git", "fetch"] else REAL_RUN(args, **kwargs)
        output = Path(self.temp.name, "outputs")
        with patch.dict(os.environ, GITHUB_REPOSITORY=REPO, GITHUB_EVENT_NAME="workflow_dispatch",
                        PR_INPUT="12", REVIEW_RUN="", GITHUB_OUTPUT=str(output), GH_TOKEN="read-only-token"), \
                patch.object(gate, "api", side_effect=api), patch.object(gate, "run", side_effect=git_output), \
                patch.object(gate.subprocess, "run", side_effect=command):
            gate.prepare()
        outputs = dict(line.split("=", 1) for line in output.read_text().splitlines())
        self.assertEqual(outputs["pr-base"], self.base)
        self.assertEqual(outputs["base"], main)
        self.assertEqual(outputs["merge"], merge)


    def bot_metadata(self, metadata, attested=None):
        comments = []
        for i, c in enumerate(metadata["comments"], 1):
            comments.append({"id": i, "body": c["body"], "created_at": c["createdAt"],
                             "author_association": c["authorAssociation"],
                             "user": c.get("author", {"login": "github-actions" if c["authorAssociation"] == "NONE" else "owner"})})
        def api(endpoint):
            return {"artifacts": []} if "/artifacts?" in endpoint else comments
        with patch.object(gate, "api", side_effect=api):
            return gate.review_metadata(REPO, 12, metadata["headRefOid"], attested)

    def bot_attestation(self):
        return {"pr": 12, "head": self.reviewed, "body": f"Review of {self.reviewed}: no blocking issues",
                "commentId": 1, "createdAt": "01"}

    def test_bot_reviews_need_authenticated_metadata(self):
        meta = self.metadata()
        meta["comments"][0]["authorAssociation"] = "NONE"
        self.assertFalse(gate.inherited_review(self.bot_metadata(meta), self.base))
        attested = self.bot_attestation()
        self.assertTrue(gate.inherited_review(self.bot_metadata(meta, attested), self.base))
        outsider = self.comment(f"Review of {self.reviewed}: blocking issues", "02", "NONE")
        outsider["author"] = {"login": "outsider"}
        meta["comments"].append(outsider)
        self.assertTrue(gate.inherited_review(self.bot_metadata(meta, attested), self.base))
        outsider["author"] = {"login": "github-actions"}
        self.assertFalse(gate.inherited_review(self.bot_metadata(meta, attested), self.base))

    def test_wording_and_main_updates_still_inherit_attested_bot_review(self):
        attested = self.bot_attestation()
        Path("file.md").write_text("wording\n")
        self.git("commit", "-qam", "wording")
        head = self.git("rev-parse", "HEAD")
        meta = self.metadata(self.comment(f"wording only: {head}", "02"))
        meta["comments"][0]["authorAssociation"] = "NONE"
        self.assertTrue(gate.inherited_review(self.bot_metadata(meta, attested), self.base))
        blocking = self.comment(f"Review of {self.reviewed}: blocking issues", "03", "NONE")
        meta["comments"].append(blocking)
        self.assertFalse(gate.inherited_review(self.bot_metadata(meta, attested), self.base))
        self.git("reset", "--hard", "-q", self.reviewed)
        self.git("checkout", "-q", "main")
        Path("other.md").write_text("main\n")
        self.git("add", ".")
        self.git("commit", "-qm", "main")
        main = self.git("rev-parse", "HEAD")
        self.git("checkout", "-q", "feature")
        self.git("merge", "-q", "--no-ff", "--no-edit", "main")
        meta = self.metadata()
        meta["comments"][0]["authorAssociation"] = "NONE"
        self.assertTrue(gate.inherited_review(self.bot_metadata(meta, attested), main))


class CheckRuns(unittest.TestCase):
    def test_updates_own_check_and_creates_failure_if_preparation_failed(self):
        for check in ("123", ""):
            with patch.dict(os.environ, GITHUB_REPOSITORY=REPO, CHECK_RUN_ID=check), \
                    patch.object(gate, "api") as api:
                gate.status(HEAD, "failure", "failed")
                endpoint, payload = api.call_args.args
                self.assertEqual(payload["conclusion"], "failure")
                if check:
                    self.assertTrue(endpoint.endswith("/123"))
                    self.assertEqual(api.call_args.kwargs, {"method": "PATCH"})
                else:
                    self.assertEqual(payload["head_sha"], HEAD)
                    self.assertEqual(payload["name"], "pre-merge")


if __name__ == "__main__":
    unittest.main()
