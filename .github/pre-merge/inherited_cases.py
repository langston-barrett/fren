"""Real inheritance, published source reviews, and dependent check lifecycle.

Only GitHub/download/fetch transport and worker outcomes are simulated.
Authorization, actual git structure, event preparation/recovery, scheduling
and check invalidation are the production decisions, never approval flags.
"""

from contextlib import ExitStack
from datetime import datetime, timedelta, timezone
import itertools
import json
import os
from pathlib import Path
import subprocess
import tempfile
from unittest.mock import patch
from urllib.parse import parse_qs, urlsplit

from test_gate import gate, REAL_RUN, report_runs

REPO = "owner/fren"


class Scenario:
    def __init__(self, shape, *, bot_source=False):
        self.shape, self.bot_source = shape, bot_source
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.previous = Path.cwd()
        os.chdir(self.root)
        self.git("init", "-q", "-b", "main")
        self.git("config", "user.name", "test")
        self.git("config", "user.email", "test@example.com")
        Path("LICENSE").write_text("base\n")
        self.git("add", ".")
        self.git("commit", "-qm", "anchor")
        self.anchor = self.main = self.git("rev-parse", "HEAD")
        self.git("checkout", "-qb", "feature")
        Path("LICENSE").write_text("reviewed\n")
        self.git("commit", "-qam", "reviewed source")
        self.source = self.git("rev-parse", "HEAD")
        if shape == "wording":
            Path("LICENSE").write_text("wording\n")
            self.git("commit", "-qam", "wording")
        else:
            self.git("checkout", "-q", "main")
            Path("base.txt").write_text("main\n")
            self.git("add", ".")
            self.git("commit", "-qm", "main")
            self.main = self.git("rev-parse", "HEAD")
            self.git("checkout", "-q", "feature")
            self.git("merge", "-q", "--no-ff", "--no-edit", "main")
        self.head = self.git("rev-parse", "HEAD")
        self.git("checkout", "-q", "--detach", "main")
        self.git("merge", "-q", "--no-ff", "--no-edit", "feature")
        self.merge = self.git("rev-parse", "HEAD")
        self.output = self.root / "outputs"
        self.event_path = self.root / "event.json"
        self.pr = {"number": 12, "state": "open", "head": {"repo": {"full_name": REPO}, "sha": self.head},
                   "base": {"repo": {"full_name": REPO}, "ref": "main", "sha": self.anchor}}
        self.stack = ExitStack()
        self.stack.enter_context(patch.dict(os.environ, GITHUB_REPOSITORY=REPO, GH_TOKEN="read-only-token",
                PR_INPUT="12", REVIEW_RUN="", REVIEW_ATTEMPT="", GITHUB_EVENT_NAME="workflow_dispatch",
                GITHUB_EVENT_PATH=str(self.event_path), GITHUB_OUTPUT=str(self.output), CHECK_RUN_ID="10",
                GITHUB_RUN_ID="70", GITHUB_RUN_ATTEMPT="1"))
        self.stack.enter_context(patch.object(gate, "api", side_effect=self.api))
        self.stack.enter_context(patch.object(gate.subprocess, "run", side_effect=self.command))
        self.reset()

    def __enter__(self): return self

    def __exit__(self, *args):
        self.stack.close()
        os.chdir(self.previous)
        self.temp.cleanup()

    def git(self, *args):
        return subprocess.check_output(["git", *args], text=True, stderr=subprocess.PIPE).strip()

    def reset(self):
        self.comments, self.records, self.writes, self.fetches = [], {}, [], []
        self.loss = None
        self.losses, self.gate_runs = {}, {}
        self.checks = {10: {"id": 10, "name": "pre-merge", "head_sha": self.head,
                            "app": {"slug": "github-actions"}, "conclusion": "success", "status": "completed"}}
        self.add_review(self.source, clean=True, bot=self.bot_source, run=42)
        if self.shape == "wording": self.add_comment(f"wording only: {self.head}")
        self.output.unlink(missing_ok=True)

    def add_comment(self, body, *, bot=False):
        n = len(self.comments) + 1
        stamp = (datetime(2026, 11, 7, tzinfo=timezone.utc) + timedelta(seconds=n)).isoformat()
        c = {"id": n, "body": body, "created_at": stamp, "author_association": "NONE" if bot else "OWNER",
             "user": {"login": "github-actions[bot]" if bot else "owner"}}
        self.comments.append(c)
        return c

    def add_review(self, head, *, clean=False, bot=False, run=43):
        c = self.add_comment(f"Review of {head}: " + ("no blocking issues" if clean else "blocking issues"), bot=bot)
        if bot:
            self.records[run] = {"pr": 12, "head": head, "body": c["body"], "attempt": 1,
                                  "commentId": c["id"], "createdAt": c["created_at"]}
        return c

    def artifact(self, run):
        return {"id": run, "name": gate.artifact_name(12, self.records[run]["head"]),
                "expired": self.loss_mode(run) == "expired", "workflow_run": {"id": run}}

    def loss_mode(self, run):
        return self.losses.get(run, self.loss if run == 43 else None)

    def api(self, endpoint, payload=None, method=None):
        path, query = urlsplit(endpoint).path, parse_qs(urlsplit(endpoint).query)
        if "/pulls/" in path: return self.pr
        if path.endswith("/git/ref/heads/main"):
            return {"ref": "refs/heads/main", "object": {"type": "commit", "sha": self.main}}
        if path.endswith("/issues/12/comments"): return self.comments
        if "/actions/runs/" in path:
            run = int(path.split("/runs/")[1].split("/")[0])
            if run in self.gate_runs:
                record = self.gate_runs[run]
                return {"jobs": record["jobs"]} if path.endswith("/jobs") else record["info"]
            if path.endswith("/jobs"):
                return {"jobs": [{"name": f"Post review (PR 12, head {self.source}, attempt 1)",
                        "run_id": run, "run_attempt": 1, "status": "completed",
                        "conclusion": "cancelled" if self.loss == "missing" else "failure"}]}
            if path.endswith("/artifacts"):
                if self.loss_mode(run) == "listing": raise OSError("artifact listing unavailable")
                return {"artifacts": [self.artifact(run)] if run in self.records and self.loss_mode(run) != "missing" else []}
            return {"id": run, "path": ".github/workflows/claude-review.yml", "head_repository": {"full_name": REPO},
                    "head_branch": "main", "status": "completed", "event": "workflow_run", "run_attempt": 1}
        if path.endswith("/actions/artifacts"):
            return {"artifacts": [self.artifact(r) for r in self.records
                    if self.artifact(r)["name"] == query["name"][0] and self.loss_mode(r) != "missing"]}
        if "/commits/" in path:
            head = path.split("/commits/")[1].split("/")[0]
            return {"check_runs": [c for c in self.checks.values() if c["head_sha"] == head]}
        if "/check-runs/" in path:
            n = int(path.rsplit("/", 1)[1])
            self.checks[n].update(payload)
            self.writes.append((self.checks[n]["head_sha"], payload["conclusion"]))
            return self.checks[n]
        if path.endswith("/check-runs"):
            n = max(self.checks) + 1
            self.checks[n] = {**payload, "id": n, "app": {"slug": "github-actions"}}
            self.writes.append((payload["head_sha"], payload["conclusion"]))
            return self.checks[n]
        raise AssertionError(endpoint)

    def command(self, args, **kwargs):
        if args[:2] == ["git", "fetch"]:
            self.fetches.append(args)
            if any(str(a).startswith("refs/pull/") for a in args):
                Path(".git/FETCH_HEAD").write_text(self.merge + "\n")
            return subprocess.CompletedProcess(args, 0)
        if args[:3] == ["gh", "run", "download"]:
            run = int(args[3])
            if self.loss_mode(run) == "download": raise OSError("download unavailable")
            Path(args[-1], "review.json").write_text(json.dumps(self.records[run]))
            return subprocess.CompletedProcess(args, 0)
        return REAL_RUN(args, **kwargs)

    def outputs(self):
        return dict(line.split("=", 1) for line in self.output.read_text().splitlines()) if self.output.exists() else {}

    def finish(self, outputs, *, prepare="failure", check=""):
        needs = {"prepare": {"result": prepare, "outputs": outputs},
                 "pending": {"result": "success" if prepare == "success" else "skipped"}, "slow": {"result": "skipped"}}
        with patch.dict(os.environ, NEEDS=json.dumps(needs), CHECK_RUN_ID=check): gate.finish()

    def start_green(self, test):
        with patch.dict(os.environ, PR_INPUT="12", REVIEW_RUN="42" if self.bot_source else "", GITHUB_EVENT_NAME="workflow_dispatch"):
            gate.prepare()
            test.assertEqual(self.outputs()["relevant"], "false")
            # GitHub retains this job name from actual successful prepare
            # outputs. It is not supplied as an approval/dependency flag.
            self.gate_runs[70] = {
                "info": {"id": 70, "path": ".github/workflows/pre-merge.yml", "run_attempt": 1,
                         "head_branch": "main", "head_repository": {"full_name": REPO}, "event": "workflow_dispatch"},
                "jobs": [{"name": name, "run_id": 70, "run_attempt": 1, "status": "completed", "conclusion": "success"}
                         for name in ("prepare", self.outputs()["dependency"])],
            }
            self.checks[10].update(external_id="pre-merge:70:1", details_url=f"https://github.com/{REPO}/actions/runs/70")
            self.finish(self.outputs(), prepare="success", check="10")
        test.assertEqual(self.checks[10]["conclusion"], "success")
        self.checks[11] = {**self.checks[10], "id": 11, "status": "in_progress", "conclusion": None}
        self.writes.clear()
        self.output.unlink()

    def event(self, kind):
        if kind == "local":
            c = self.add_review(self.source)
            self.event_path.write_text(json.dumps({"repository": {"full_name": REPO}, "action": "created",
                    "issue": {"number": 12, "pull_request": {"url": "pr"}}, "comment": c}))
            return patch.dict(os.environ, GITHUB_EVENT_NAME="issue_comment", PR_INPUT="", REVIEW_RUN="")
        self.add_review(self.source, bot=True)
        return patch.dict(os.environ, GITHUB_EVENT_NAME="workflow_dispatch" if kind in ("dispatch", "manual") else "workflow_run",
                          PR_INPUT="12" if kind == "manual" else "", REVIEW_RUN="43", REVIEW_ATTEMPT="1")


class InheritedRevocationCases:
    def test_source_publication_revokes_completed_and_running_no_job_gates(self):
        for shape in self.shapes:
            with Scenario(shape) as c:
                for kind, loss, outputless in itertools.product(("local", "completion", "dispatch", "manual"),
                                                               (None, "missing", "download", "listing"), (False, True)):
                    if kind == "local" and loss is not None: continue
                    with self.subTest(shape=shape, kind=kind, loss=loss, outputless=outputless):
                        c.reset()
                        c.start_green(self)
                        with c.event(kind):
                            c.loss = loss
                            self.assertFalse(gate.authorized(REPO, 12, c.head, c.main, manual=True))
                            if not outputless:
                                with self.assertRaises(ValueError): gate.prepare()
                                outputs = c.outputs()
                                self.assertEqual((outputs["head"], outputs["source"]), (c.head, c.source))
                                self.assertNotIn("merge", outputs)
                                self.assertNotIn("base", outputs)
                            else:
                                outputs = {}
                            self.assertTrue(report_runs(os.environ["GITHUB_EVENT_NAME"], "refs/heads/main",
                                    automatic=43 if kind == "completion" else 0,
                                    dispatch="43" if kind in ("dispatch", "manual") else ""))
                            with self.assertRaises(SystemExit): c.finish(outputs, prepare="cancelled" if outputless else "failure")
                        self.assertTrue(all(check["conclusion"] == "failure" for check in c.checks.values()))
                        self.assertTrue(c.writes)
                        self.assertTrue(all(head == c.head and state == "failure" for head, state in c.writes))

    def test_source_reclean_or_independent_head_review_survives_every_negative_entry(self):
        for shape in self.shapes:
            with Scenario(shape) as c:
                for kind, change, missing in itertools.product(("local", "completion", "dispatch", "manual"),
                        ("source-clean", "head-clean", "head-blocked"), (False, True)):
                    with self.subTest(shape=shape, kind=kind, change=change, missing=missing):
                        c.reset()
                        c.start_green(self)
                        with c.event(kind):
                            c.loss = "missing" if missing else None
                            c.add_review(c.source if change == "source-clean" else c.head, clean=change != "head-blocked")
                            try: gate.prepare()
                            except ValueError:
                                self.assertEqual(kind, "manual")
                                self.assertTrue(missing)
                            c.finish(c.outputs(), prepare="cancelled")
                        self.assertFalse(c.writes)
                        self.assertEqual(c.checks[10]["conclusion"], "success")

    def test_prepared_inherited_target_is_revalidated_before_reporting(self):
        for shape in self.shapes:
            with Scenario(shape) as c:
                for kind, missing in itertools.product(("local", "completion", "manual"), (False, True)):
                    with self.subTest(shape=shape, kind=kind, missing=missing):
                        c.reset()
                        c.start_green(self)
                        with c.event(kind):
                            c.loss = "missing" if missing else None
                            with self.assertRaises(ValueError): gate.prepare()
                            outputs = c.outputs()
                            c.add_review(c.head, clean=True)
                            c.finish(outputs)
                        self.assertFalse(c.writes)

    def test_old_positive_source_completion_never_authorizes_a_dependent_head(self):
        for shape in self.shapes:
            with self.subTest(shape=shape), Scenario(shape, bot_source=True) as c:
                c.start_green(self)
                for event in ("workflow_run", "workflow_dispatch"):
                    with patch.dict(os.environ, GITHUB_EVENT_NAME=event, PR_INPUT="", REVIEW_RUN="42"):
                        gate.prepare()
                        self.assertEqual(c.outputs(), {})
                        c.finish({}, prepare="success")
                self.assertFalse(c.writes)

    def test_unattested_bot_source_block_still_resolves_a_verified_bot_source(self):
        for shape, loss in itertools.product(self.shapes, (None, "missing", "download")):
            with self.subTest(shape=shape, loss=loss), Scenario(shape, bot_source=True) as c:
                c.start_green(self)
                with c.event("completion"):
                    c.loss = loss
                    with self.assertRaises(ValueError): gate.prepare()
                    with self.assertRaises(SystemExit): c.finish(c.outputs())
                self.assertEqual(c.checks[10]["conclusion"], "failure")

    def test_lagging_source_comment_is_not_forged_into_a_direct_head_review(self):
        for shape in self.shapes:
            with self.subTest(shape=shape), Scenario(shape) as c:
                c.start_green(self)
                with c.event("local"):
                    comment = c.comments.pop()
                    meta = gate.review_metadata(REPO, 12, c.head, blocking_comment=comment)
                    self.assertIsNone(gate.latest_verdict(meta, c.head))
                    self.assertEqual(gate.latest_verdict(meta, c.source), "blocking issues")
                    with self.assertRaises(SystemExit): c.finish({})
                self.assertEqual(c.checks[10]["conclusion"], "failure")

    def test_running_original_gate_cannot_restore_green_after_source_is_blocked(self):
        for shape in self.shapes:
            with self.subTest(shape=shape), Scenario(shape, bot_source=True) as c:
                c.start_green(self)
                c.add_review(c.source)
                with patch.dict(os.environ, PR_INPUT="12", REVIEW_RUN="42"), self.assertRaises(SystemExit):
                    c.finish({"head": c.head, "pr": "12", "base": c.main, "relevant": "false"}, prepare="success", check="11")
                self.assertTrue(all(check["conclusion"] == "failure" for check in c.checks.values()))

    def test_new_verified_bot_source_review_supersedes_a_lost_blocking_record(self):
        for shape in self.shapes:
            with Scenario(shape, bot_source=True) as c:
                for loss in (None, "missing", "download"):
                    with self.subTest(shape=shape, loss=loss):
                        c.reset()
                        c.start_green(self)
                        with c.event("completion"):
                            c.loss = loss
                            c.add_review(c.source, clean=True, bot=True, run=44)
                            try: gate.prepare()
                            except OSError: self.assertEqual(loss, "download")
                            c.finish({}, prepare="cancelled")
                        self.assertFalse(c.writes)

    def test_unverified_head_bot_text_cannot_erase_a_real_dependency(self):
        for shape, clean in itertools.product(self.shapes, (False, True)):
            with self.subTest(shape=shape, clean=clean), Scenario(shape) as c:
                c.start_green(self)
                with c.event("local"):
                    c.add_review(c.head, clean=clean, bot=True, run=44)
                    del c.records[44]  # No provenance for the claimed independent review.
                    with self.assertRaises(SystemExit): c.finish({})
                self.assertEqual(c.checks[10]["conclusion"], "failure")

    def test_structural_and_current_pr_mismatches_do_not_supply_a_stale_target(self):
        for shape, invalid in itertools.product(self.shapes, ("custom-tree", "fork", "closed", "other-base", "head-moved")):
            with self.subTest(shape=shape, invalid=invalid), Scenario(shape) as c:
                with c.event("local"):
                    if invalid == "custom-tree":
                        c.git("checkout", "-q", "feature")
                        Path("AGENTS.md").write_text("process change\n")
                        c.git("add", ".")
                        c.git("commit", "--amend", "--no-edit", "-q")
                        c.pr["head"]["sha"] = c.git("rev-parse", "HEAD")
                    elif invalid == "fork": c.pr["head"]["repo"]["full_name"] = "fork/fren"
                    elif invalid == "closed": c.pr["state"] = "closed"
                    elif invalid == "other-base": c.pr["base"]["ref"] = "other"
                    else: c.pr["head"]["sha"] = c.main
                    gate.prepare()
                    c.finish({})
                self.assertFalse(c.writes)

    def test_outputless_first_read_failure_recovers_the_live_source_dependency(self):
        for shape, kind in itertools.product(self.shapes, ("local", "completion")):
            with self.subTest(shape=shape, kind=kind), Scenario(shape) as c:
                c.start_green(self)
                with c.event(kind):
                    def unavailable(endpoint, *args, **kwargs):
                        if "/pulls/" in endpoint: raise OSError("first PR read failed")
                        return c.api(endpoint, *args, **kwargs)
                    with patch.object(gate, "api", side_effect=unavailable), self.assertRaises(OSError):
                        gate.prepare()
                    self.assertEqual(c.outputs(), {})
                    with self.assertRaises(SystemExit): c.finish({}, prepare="failure")
                self.assertTrue(all(check["conclusion"] == "failure" for check in c.checks.values()))

    def test_current_head_and_dependency_changes_after_preparation_are_not_trusted(self):
        for shape in self.shapes:
            with self.subTest(shape=shape), Scenario(shape) as c:
                c.start_green(self)
                with c.event("completion"):
                    c.loss = "missing"
                    with self.assertRaises(ValueError): gate.prepare()
                    outputs = c.outputs()
                    c.pr["head"]["sha"] = c.main  # This live head does not inherit S.
                    c.finish(outputs)
                self.assertFalse(c.writes)

