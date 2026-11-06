"""The output boundary: no symlink or special file reaches the host."""

import importlib.util
import os
from pathlib import Path
import tempfile
import textwrap
import unittest
from subprocess import CompletedProcess
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("slow_worker", HERE / "worker.py")
worker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(worker)


class Outputs(unittest.TestCase):
    def test_regular_files_only_and_no_symlink_components(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            work = root / "work"
            fuzz = work / "fuzz"
            fuzz.mkdir(parents=True)
            secret = root / "runner-secret"
            secret.write_text("not an artifact")
            (fuzz / "spec.fren").write_text("allowed")
            (fuzz / "::error::bad").write_text("not an artifact")
            (fuzz / "link").symlink_to(secret)
            (fuzz / "directory").symlink_to(root, target_is_directory=True)
            os.mkfifo(fuzz / "fifo")
            (work / ".lake").symlink_to(root, target_is_directory=True)
            (root / "slow-summary.md").write_text("not a summary")
            summary = root / "summary"
            with patch.dict(os.environ, GITHUB_STEP_SUMMARY=str(summary)):
                worker.collect(work, root / "out")
            self.assertEqual([p.name for p in (root / "out").iterdir()], ["spec.fren"])
            self.assertFalse(summary.exists())

    def test_output_root_symlink_and_bounded_artifacts(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            work = root / "work"
            work.mkdir()
            (work / "fuzz").symlink_to(root)
            worker.collect(work, root / "out")
            self.assertEqual(list((root / "out").iterdir()), [])
            (work / "fuzz").unlink()
            (work / "fuzz").mkdir()
            with (work / "fuzz/huge").open("wb") as f:
                f.truncate(8 * 1024**2 + 1)
            with self.assertRaisesRegex(ValueError, "output limit"):
                worker.collect(work, root / "large")

    def test_coverage_collects_only_its_private_summary(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            work = root / "work"
            (work / ".lake").mkdir(parents=True)
            (work / ".lake/slow-summary.md").write_text("coverage\n::error::data\n##[error]data")
            summary = root / "runner-summary"
            with patch.dict(os.environ, GITHUB_STEP_SUMMARY=str(summary)):
                worker.collect(work, root / "out", artifacts=False)
            self.assertIn("coverage", summary.read_text())
            self.assertNotIn("::", summary.read_text())
            self.assertNotIn("##[", summary.read_text())
            self.assertFalse((root / "out").exists())

    def test_host_setup_precedes_pr_checkout_and_never_builds_pr_code(self):
        text = (HERE.parent / "workflows/slow-checks.yml").read_text()
        for job in ("own-spec-agreement", "methods-agree", "coverage", "fuzz-frontends"):
            block = text.split("  " + job + ":\n", 1)[1].split("    steps:\n", 1)[1].split("\n  #", 1)[0]
            self.assertLess(block.index("uses: ./.github/actions/lake"), block.index("ref: ${{ inputs.ref }}"))
            self.assertIn('dependencies: "false"', block)
            self.assertIn('toolchain: "false"', block)
            self.assertNotIn("run: lake", block)
            self.assertIn("run: python3 -I .github/pre-merge/worker.py", block)
            self.assertLess(block.index('mv source "$RUNNER_TEMP/slow-work"'), block.index("run: python3 -I"))

    def test_no_output_is_collected_if_teardown_is_unconfirmed(self):
        with tempfile.TemporaryDirectory() as temp:
            def run(args, **kwargs):
                if args[0] == "bash":
                    kwargs["stdout"].write(b"::error::untrusted\n##[error]untrusted\n")
                return CompletedProcess(args, 0)
            with patch.dict(os.environ, RUNNER_TEMP=temp, GITHUB_RUN_ID="1", GITHUB_RUN_ATTEMPT="1"), \
                    patch.object(worker.sys, "argv", ["worker.py", "fuzz-frontends"]), \
                    patch.object(worker.subprocess, "run", side_effect=run), \
                    patch.object(worker.signal, "signal"), \
                    patch.object(worker.subprocess, "check_output", return_value="still-running\n"), \
                    patch.object(worker, "collect") as collect, patch("builtins.print") as display:
                with self.assertRaisesRegex(RuntimeError, "teardown failed"):
                    worker.main()
                collect.assert_not_called()
                display.assert_not_called()

    def test_modern_and_legacy_workflow_commands_are_inert(self):
        text = worker.inert("::error::x\n:::stop-commands:::x\n##[add-path]x")
        self.assertNotIn("::", text)
        self.assertNotIn("##[", text)

    def test_cold_and_warm_cache_setup_does_not_follow_pr_symlinks(self):
        text = (HERE.parent / "workflows/slow-checks.yml").read_text()
        script = text.split("    - run: |\n", 1)[1].split("    - name:", 1)[0]
        script = textwrap.dedent(script)
        for warm in (True, False):
            with tempfile.TemporaryDirectory() as temp:
                root = Path(temp)
                workspace = root / "workspace"
                (workspace / "source").mkdir(parents=True)
                runner_temp = root / "temp"
                runner_temp.mkdir()
                secret = root / "secret"
                secret.mkdir()
                (secret / "keep").write_text("host")
                (workspace / "source/.lake").symlink_to(secret, target_is_directory=True)
                if warm:
                    (workspace / ".lake/packages").mkdir(parents=True)
                    (workspace / ".lake/packages/cached").write_text("cache")
                worker.subprocess.run(["bash", "-e", "-c", script], cwd=workspace,
                                      env={**os.environ, "RUNNER_TEMP": str(runner_temp)}, check=True)
                self.assertFalse((workspace / "source").exists())
                self.assertEqual((secret / "keep").read_text(), "host")
                self.assertTrue((runner_temp / "slow-work/.lake").is_dir())
                if warm:
                    self.assertEqual((runner_temp / "slow-work/.lake/packages/cached").read_text(), "cache")


if __name__ == "__main__":
    unittest.main()
