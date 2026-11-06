"""Gate decisions, failure propagation, and trusted review attestations."""

import importlib.util
import itertools
import json
import os
from pathlib import Path
import subprocess
import tempfile
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

    def test_record_matches_posted_head(self):
        for first, clean in ((f"Review of {HEAD}: no blocking issues", True),
                             (f"Review of {'b' * 40}: no blocking issues", False),
                             (f"Review of {HEAD}: blocking issues", False)):
            with tempfile.TemporaryDirectory() as temp:
                out = Path(temp, "outputs")
                Path(temp, "comment.md").write_text(first + "\n\nProbes: none\n")
                with patch.dict(os.environ, RUNNER_TEMP=temp, GITHUB_OUTPUT=str(out), HEAD=HEAD, PR="12", POST="", GITHUB_RUN_ATTEMPT="1"):
                    gate.record()
                self.assertIn(f"clean={str(clean).lower()}", out.read_text())
                self.assertEqual(Path(temp, "posted-review/review.json").exists(), clean)

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
            needs = {"prepare": {"result": prepare, "outputs": {"head": HEAD, "relevant": str(relevant).lower()}},
                     "pending": {"result": pending}, "slow": {"result": slow}}
            good = prepare == pending == "success" and slow == ("success" if relevant else "skipped")
            with patch.dict(os.environ, NEEDS=json.dumps(needs)), patch.object(gate, "status") as status:
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


class Preparation(unittest.TestCase):
    def test_current_merge_no_jobs_stale_fork_and_old_attempt(self):
        for scenario in ("current", "failed-probe", "stale", "fork", "old-attempt", "wrong-merge"):
            with self.subTest(scenario=scenario), tempfile.TemporaryDirectory() as temp:
                out = Path(temp, "outputs")
                info = {"path": ".github/workflows/claude-review.yml",
                        "head_repository": {"full_name": REPO}, "head_branch": "main",
                        "status": "completed", "conclusion": "failure" if scenario == "failed-probe" else "success", "run_attempt": 2}
                pr = {"state": "open", "head": {"repo": {"full_name": REPO}, "sha": HEAD},
                      "base": {"repo": {"full_name": REPO}, "ref": "main", "sha": "b" * 40}}
                if scenario == "stale":
                    pr["head"]["sha"] = "d" * 40
                if scenario == "fork":
                    pr["head"]["repo"]["full_name"] = "fork/fren"

                def api(endpoint):
                    if endpoint.endswith("/42"):
                        return info
                    if "/artifacts" in endpoint:
                        return {"artifacts": [{"name": "posted-review", "expired": False}]}
                    return pr

                def command(args, **kwargs):
                    if args[:2] == ["git", "fetch"]:
                        self.assertNotIn("read-only-token", " ".join(args))
                        self.assertIn("AUTHORIZATION: basic ", kwargs["env"]["GIT_CONFIG_VALUE_0"])
                    if args[:3] == ["gh", "run", "download"]:
                        Path(args[-1], "review.json").write_text(json.dumps({
                            "head": HEAD, "pr": 12, "body": f"Review of {HEAD}: no blocking issues\n",
                            "attempt": 1 if scenario == "old-attempt" else 2,
                        }))

                def run(*args):
                    if args[0] == "bash":
                        return "auth"
                    if args[1] == "rev-parse":
                        return "c" * 40
                    return "b" * 40 + " " + ("d" * 40 if scenario == "wrong-merge" else HEAD)

                with patch.dict(os.environ, GITHUB_REPOSITORY=REPO, REVIEW_RUN="42",
                                PR_INPUT="", GH_TOKEN="read-only-token", GITHUB_OUTPUT=str(out)), \
                        patch.object(gate, "api", side_effect=api), \
                        patch.object(gate, "run", side_effect=run), \
                        patch.object(gate.subprocess, "run", side_effect=command), \
                        patch.object(gate.subprocess, "check_output",
                                     return_value=b".github/codex-agent/Dockerfile\0"):
                    if scenario == "wrong-merge":
                        with self.assertRaisesRegex(ValueError, "merge ref"):
                            gate.prepare()
                        self.assertIn("head=" + HEAD, out.read_text())
                    else:
                        gate.prepare()
                        if scenario in ("current", "failed-probe"):
                            self.assertIn("relevant=false", out.read_text())
                            self.assertIn("merge=" + "c" * 40, out.read_text())
                        else:
                            self.assertFalse(out.exists())


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

    def test_wording_shape_and_current_blocking_override(self):
        Path("file.md").write_text("wording\n")
        self.git("commit", "-qam", "wording")
        head = self.git("rev-parse", "HEAD")
        request = self.comment(f"wording only: {head}", "02")
        self.assertTrue(gate.inherited_review(self.metadata(request), self.base))
        self.assertFalse(gate.inherited_review(self.metadata(request, self.comment(
            f"Review of {head}: blocking issues", "03")), self.base))
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

    def test_bot_reviews_need_a_trusted_attestation(self):
        meta = self.metadata()
        meta["comments"][0]["authorAssociation"] = "NONE"
        attested = {"head": self.reviewed, "body": meta["comments"][0]["body"], "createdAt": "01"}
        self.assertFalse(gate.inherited_review(meta, self.base))
        self.assertTrue(gate.inherited_review(meta, self.base, attested))
        meta["comments"].append(self.comment(f"Review of {self.reviewed}: blocking issues", "02", "NONE"))
        self.assertTrue(gate.inherited_review(meta, self.base, attested))
        bot = self.comment(f"Review of {self.reviewed}: blocking issues", "03", "NONE")
        bot["author"] = {"login": "github-actions"}
        meta["comments"].append(bot)
        self.assertFalse(gate.inherited_review(meta, self.base, attested))

    def test_wording_and_main_updates_inherit_attested_bot_reviews(self):
        attested = {"head": self.reviewed, "body": f"Review of {self.reviewed}: no blocking issues", "createdAt": "01"}
        Path("file.md").write_text("wording\n")
        self.git("commit", "-qam", "wording")
        head = self.git("rev-parse", "HEAD")
        meta = self.metadata(self.comment(f"wording only: {head}", "02"))
        meta["comments"][0]["authorAssociation"] = "NONE"
        self.assertTrue(gate.inherited_review(meta, self.base, attested))
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
        self.assertTrue(gate.inherited_review(meta, main, attested))


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
