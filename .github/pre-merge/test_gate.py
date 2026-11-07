"""Gate decisions, failure propagation, and trusted review attestations."""

import importlib.util
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
HEAD = "a" * 40
REPO = "owner/fren"


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
        info = {"path": ".github/workflows/claude-review.yml", "head_repository": {"full_name": REPO},
                "head_branch": "main", "status": "completed", "conclusion": "success"}
        for key, value in (("path", ".github/workflows/fake.yml"), ("head_branch", "trial"),
                           ("status", "in_progress"), ("head_repository", {"full_name": "fork/fren"})):
            candidate = {**info, key: value}
            with patch.dict(os.environ, GITHUB_REPOSITORY=REPO, REVIEW_RUN="42"), \
                    patch.object(gate, "api", return_value=candidate) as api, \
                    patch.object(gate.subprocess, "run") as command:
                gate.prepare()
                self.assertEqual(api.call_count, 1)
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

    def test_no_status_for_stale_review_or_fork(self):
        with patch.dict(os.environ, NEEDS=json.dumps({"prepare": {"outputs": {}}})), \
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
        self.pr = {"state": "open", "head": {"repo": {"full_name": REPO}, "sha": HEAD},
                   "base": {"repo": {"full_name": REPO}, "ref": "main", "sha": self.main}}
        self.reviews = {}
        self.expired = set()
        self.comments = []
        self.checks = {10: {"id": 10, "name": "pre-merge", "app": {"slug": "github-actions"}, "conclusion": "success"}}
        self.info = {}
        self.patches = []
        self.before_success_write = None
        self.read_error = False
        self.next_check = 100
        env = dict(GITHUB_REPOSITORY=REPO, REVIEW_RUN="42", PR_INPUT="", CHECK_RUN_ID="",
                   GH_TOKEN="read-only-token", GITHUB_OUTPUT=str(self.out), GITHUB_EVENT_NAME="workflow_run")
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
            self.info[run] = {"path": ".github/workflows/claude-review.yml", "head_repository": {"full_name": REPO},
                              "head_branch": "main", "status": "completed", "conclusion": "success", "run_attempt": 2}

    def artifact(self, run):
        r = self.reviews[run]
        return {"id": run, "name": gate.artifact_name(12, r["head"]), "expired": run in self.expired, "workflow_run": {"id": run}}

    def api(self, endpoint, payload=None, method=None):
        from urllib.parse import parse_qs, urlsplit
        parsed = urlsplit(endpoint)
        path, query = parsed.path, parse_qs(parsed.query)
        page = int(query.get("page", [1])[0])
        if path.endswith("/pulls/12"):
            if self.read_error:
                raise OSError("review API unavailable")
            return self.pr
        if path.endswith("/issues/12/comments"):
            return self.comments[(page-1)*100:page*100]
        if "/actions/runs/" in path:
            run = int(path.split("/runs/")[1].split("/")[0])
            if path.endswith("/artifacts"):
                return {"artifacts": [self.artifact(run)] if run in self.reviews else []}
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
            review = self.reviews[int(args[3])]
            Path(args[-1], "review.json").write_text(json.dumps(review))
        elif args[:2] == ["git", "fetch"]:
            self.assertNotIn("read-only-token", " ".join(args))
            self.assertIn("AUTHORIZATION: basic ", kwargs["env"]["GIT_CONFIG_VALUE_0"])
        else:
            raise AssertionError(args)
        return subprocess.CompletedProcess(args, 0)

    def git_output(self, *args):
        if args[1] == "rev-parse":
            return "c" * 40
        return self.main + " " + HEAD

    def outputs(self):
        return dict(line.split("=", 1) for line in self.out.read_text().splitlines()) if self.out.exists() else {}

    def finish(self, outputs=None, prepare="success", slow="skipped", check="10"):
        outputs = outputs or {"head": HEAD, "pr": "12", "base": self.main, "relevant": "false"}
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
        event = {"issue": {"number": 12, "pull_request": {}}, "comment": self.comments[-1]}
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
        event = {"issue": {"number": 12, "pull_request": {"url": "pr"}}, "comment": self.comments[0]}
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
            event = {"issue": {"number": 12, "pull_request": {"url": "pr"}}, "comment": comment}
            path = Path(self.temp.name, "event.json")
            path.write_text(json.dumps(event))
            with patch.dict(os.environ, GITHUB_EVENT_NAME="issue_comment", GITHUB_EVENT_PATH=str(path), REVIEW_RUN=""):
                gate.prepare()
            self.assertFalse(self.out.exists())



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
