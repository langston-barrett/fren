"""Previously consumed approval evidence may disappear independently of a block.

The producer is actual successful preparation/reporting; the retained job
name is that producer's output, as GitHub stores it. Only API/worker
transport is simulated. No approval or dependency Boolean is supplied.
"""

from contextlib import redirect_stdout
from copy import deepcopy
import io
import itertools
import json
import os
from unittest.mock import patch

from inherited_cases import Scenario, gate, REPO


class OriginalEvidenceCases:
    def ready(self, c):
        c.reset()
        c.start_green(self)
        if not self.running:
            del c.checks[11]

    def test_original_and_blocking_evidence_lifetimes_are_independent(self):
        observations = []
        with Scenario(self.shape, bot_source=True) as c:
            with redirect_stdout(io.StringIO()):
                self.ready(c)
            # Every row starts from this actual successful production
            # transition. Reuse its immutable DAG/transport state, never
            # a computed approval flag, instead of rebuilding it per loss.
            initial = deepcopy((c.comments, c.records, c.gate_runs, c.checks))
            for kind, old_loss, new_loss in itertools.product(
                    ("local", "completion", "dispatch", "manual"),
                    (None, "missing", "expired", "listing", "download"),
                    (None, "missing", "expired", "listing", "download")):
                if kind == "local" and new_loss is not None:
                    continue  # A local review has no new authorization artifact.
                outputless = self.outputless
                label = (self.shape, self.running, kind, old_loss, new_loss, outputless)
                with self.subTest(case=label), redirect_stdout(io.StringIO()):
                    c.comments, c.records, c.gate_runs, c.checks = deepcopy(initial)
                    c.losses, c.writes, c.fetches, c.loss = {}, [], [], None
                    c.output.unlink(missing_ok=True)
                    with c.event(kind):
                        c.losses.update({42: old_loss, 43: new_loss})
                        # Retained dependency evidence must never authorize a
                        # new pass once the old artifact is lost or S blocks.
                        self.assertFalse(gate.authorized(REPO, 12, c.head, c.main, manual=True))
                        if not outputless:
                            with self.assertRaises(ValueError): gate.prepare()
                            self.assertEqual(c.outputs()["source"], c.source)
                        with self.assertRaises(SystemExit):
                            c.finish({} if outputless else c.outputs(), prepare="cancelled" if outputless else "failure")
                    self.assertEqual(c.checks[10]["conclusion"], "failure")
                    if self.running:
                        self.assertEqual(c.checks[11]["conclusion"], "failure")
                    self.assertTrue(c.writes)
                    self.assertTrue(all(head == c.head and state == "failure" for head, state in c.writes))
                    observations.append({"case": label, "checks": {k: v["conclusion"] for k, v in c.checks.items()}})
        for row in observations:
            print(json.dumps(row))

    def test_independent_head_and_newer_clean_source_are_not_revoked(self):
        with Scenario(self.shape, bot_source=True) as c:
            for kind, change in itertools.product(("local", "completion", "dispatch", "manual"),
                                                  ("source", "head")):
                with self.subTest(kind=kind, change=change), redirect_stdout(io.StringIO()):
                    self.ready(c)
                    with c.event(kind):
                        c.losses.update({42: "listing", 43: "missing"})
                        c.add_review(c.source if change == "source" else c.head, clean=True, bot=True, run=44)
                        c.finish({})
                    self.assertFalse(c.writes)
                    self.assertEqual(c.checks[10]["conclusion"], "success")

    def test_receipt_never_supplies_positive_authorization(self):
        with Scenario(self.shape, bot_source=True) as c, redirect_stdout(io.StringIO()):
            self.ready(c)
            c.losses[42] = "missing"
            self.assertEqual(gate.recorded_source(REPO, 12, c.head), c.source)
            self.assertFalse(gate.authorized(REPO, 12, c.head, c.main, manual=True))
            with self.assertRaises(ValueError): gate.prepare()
            self.assertNotIn("dependency", c.outputs())

    def test_running_gate_records_its_dependency_before_completion(self):
        with Scenario(self.shape, bot_source=True) as c, redirect_stdout(io.StringIO()):
            self.ready(c)
            with patch.dict(os.environ, REVIEW_RUN="42", PR_INPUT="12"):
                gate.prepare()
            c.gate_runs[71] = {"info": {**c.gate_runs[70]["info"], "id": 71},
                              "jobs": [{**j, "run_id": 71, "name": c.outputs()["dependency"] if i else "prepare",
                                        "status": "in_progress" if i else "completed", "conclusion": None if i else "success"}
                                       for i, j in enumerate(c.gate_runs[70]["jobs"])]}
            c.checks[12] = {**c.checks[10], "id": 12, "status": "in_progress", "conclusion": None,
                            "external_id": "pre-merge:71:1", "details_url": f"https://github.com/{REPO}/actions/runs/71"}
            c.output.unlink()
            with c.event("completion"):
                c.losses.update({42: "missing", 43: "missing"})
                with self.assertRaises(SystemExit): c.finish({})
            self.assertEqual(c.checks[10]["conclusion"], "failure")
            self.assertEqual(c.checks[12]["conclusion"], "failure")

    def test_original_query_and_run_metadata_failures_do_not_erase_dependency(self):
        for kind, failure in itertools.product(("local", "completion"), ("query", "run")):
            with self.subTest(kind=kind, failure=failure), Scenario(self.shape, bot_source=True) as c, redirect_stdout(io.StringIO()):
                self.ready(c)
                with c.event(kind):
                    c.losses[43] = "missing"
                    def failed(endpoint, *args, **kwargs):
                        if ((failure == "query" and "/actions/artifacts?" in endpoint)
                                or (failure == "run" and "/actions/runs/42" in endpoint)):
                            raise OSError("original authorization evidence unavailable")
                        return c.api(endpoint, *args, **kwargs)
                    with patch.object(gate, "api", side_effect=failed), self.assertRaises(SystemExit):
                        c.finish({})
                self.assertEqual(c.checks[10]["conclusion"], "failure")

    def test_receipt_provenance_and_actual_structure_are_required(self):
        for invalid in ("app", "url", "head", "check-attempt", "path", "repo", "branch", "event",
                        "run-id", "run-attempt", "job-run", "job-attempt", "prepare", "skipped", "ambiguous",
                        "pr", "source", "custom-tree"):
            with self.subTest(invalid=invalid), Scenario(self.shape, bot_source=True) as c, redirect_stdout(io.StringIO()):
                self.ready(c)
                with c.event("completion"):
                    c.losses.update({42: "missing", 43: "missing"})
                    check, info = c.checks[10], c.gate_runs[70]["info"]
                    jobs = c.gate_runs[70]["jobs"]
                    if invalid == "app": check["app"] = {"slug": "other"}
                    elif invalid == "url": check["details_url"] += "/untrusted"
                    elif invalid == "head": check["head_sha"] = c.source
                    elif invalid == "check-attempt": check["external_id"] = "pre-merge:70:2"
                    elif invalid == "path": info["path"] = ".github/workflows/pre-approval.yml"
                    elif invalid == "repo": info["head_repository"] = {"full_name": "fork/fren"}
                    elif invalid == "branch": info["head_branch"] = "feature"
                    elif invalid == "event": info["event"] = "pull_request"
                    elif invalid == "run-id": info["id"] = 71
                    elif invalid == "run-attempt": info["run_attempt"] = 2
                    elif invalid == "job-run": jobs[1]["run_id"] = 71
                    elif invalid == "job-attempt": jobs[1]["run_attempt"] = 2
                    elif invalid == "prepare": jobs[0]["conclusion"] = "failure"
                    elif invalid == "skipped": jobs[1]["conclusion"] = "skipped"
                    elif invalid == "ambiguous": jobs.append(dict(jobs[1]))
                    elif invalid == "pr": jobs[1]["name"] = jobs[1]["name"].replace("PR 12,", "PR 13,")
                    elif invalid == "source": jobs[1]["name"] = jobs[1]["name"].replace("source " + c.source, "source " + c.main)
                    else:
                        c.git("checkout", "-q", "feature")
                        from pathlib import Path
                        Path("AGENTS.md").write_text("process change\n")
                        c.git("add", ".")
                        c.git("commit", "--amend", "--no-edit", "-q")
                        c.pr["head"]["sha"] = c.git("rev-parse", "HEAD")
                    if self.running:
                        # Both checks refer to the same actual attempt and
                        # must see the same modified provenance, not a spare.
                        c.checks[11].update({k: check[k] for k in ("app", "details_url", "head_sha", "external_id")})
                    c.finish({})
                self.assertFalse(c.writes)

    def test_outputless_retry_after_dependency_transport_failure(self):
        for kind in ("local", "completion", "dispatch", "manual"):
            with self.subTest(kind=kind), Scenario(self.shape, bot_source=True) as c, redirect_stdout(io.StringIO()):
                self.ready(c)
                with c.event(kind):
                    c.losses.update({42: "listing", 43: "missing"})
                    def failed(endpoint, *args, **kwargs):
                        if "/actions/runs/70/" in endpoint: raise OSError("dependency metadata temporarily unavailable")
                        return c.api(endpoint, *args, **kwargs)
                    with patch.object(gate, "api", side_effect=failed), self.assertRaises(OSError):
                        gate.prepare()
                    with self.assertRaises(SystemExit): c.finish({}, prepare="cancelled")
                self.assertEqual(c.checks[10]["conclusion"], "failure")

    def test_unrelated_event_and_later_independent_gate_remain_separate(self):
        with Scenario(self.shape, bot_source=True) as c, redirect_stdout(io.StringIO()):
            self.ready(c)
            # Produce an actual independent gate from H's verified review,
            # then lose both its and S's positive artifacts. The newer gate
            # metadata records H, so an old S event has no dependent target.
            c.add_review(c.head, clean=True, bot=True, run=44)
            with patch.dict(os.environ, REVIEW_RUN="44", PR_INPUT="12"):
                gate.prepare()
            c.gate_runs[71] = {"info": {**c.gate_runs[70]["info"], "id": 71},
                              "jobs": [{**j, "run_id": 71, "name": c.outputs()["dependency"] if i else "prepare"}
                                       for i, j in enumerate(c.gate_runs[70]["jobs"])]}
            c.checks[12] = {**c.checks[10], "id": 12, "external_id": "pre-merge:71:1",
                            "details_url": f"https://github.com/{REPO}/actions/runs/71"}
            c.output.unlink()
            c.losses.update({42: "missing", 44: "missing"})
            for loss in (None, "missing"):
                with c.event("completion"):
                    c.losses[43] = loss
                    c.finish({})
                self.assertFalse(c.writes)
        with Scenario(self.shape, bot_source=True) as c, redirect_stdout(io.StringIO()):
            self.ready(c)
            c.losses[42] = "missing"
            c.source = c.anchor  # An actual ancestor, but not the consumed source.
            with c.event("completion"):
                c.losses[43] = "missing"
                c.finish({})
            self.assertFalse(c.writes)
