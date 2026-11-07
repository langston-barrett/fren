"""Probe the actual fast artifact's merge, even after main has advanced."""

import os
from pathlib import Path
import subprocess
import tempfile
import unittest

HERE = Path(__file__).resolve().parent


class ProbeIdentity(unittest.TestCase):
    def test_existing_and_reconstructed_merge_keep_artifacts_original_main(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            origin = root / "origin"
            def git(*args):
                return subprocess.check_output(["git", "-C", str(origin), *args], text=True).strip()
            origin.mkdir()
            git("init", "-q", "-b", "main")
            git("config", "user.name", "test")
            git("config", "user.email", "test@example.com")
            (origin / "base").write_text("base\n")
            git("add", ".")
            git("commit", "-qm", "anchor")
            anchor = git("rev-parse", "HEAD")
            git("checkout", "-qb", "feature")
            (origin / "feature").write_text("head\n")
            git("add", ".")
            git("commit", "-qm", "head")
            head = git("rev-parse", "HEAD")
            git("checkout", "-q", "main")
            (origin / "main").write_text("tested main\n")
            git("add", ".")
            git("commit", "-qm", "tested main")
            tested_main = git("rev-parse", "HEAD")
            git("checkout", "-q", "--detach")
            git("merge", "-q", "--no-ff", "--no-edit", "feature")
            merge = git("rev-parse", "HEAD")
            expected_tree = git("rev-parse", "HEAD^{tree}")
            git("checkout", "-q", "main")
            (origin / "later").write_text("later main\n")
            git("add", ".")
            git("commit", "-qm", "later main")
            current_main = git("rev-parse", "HEAD")
            self.assertEqual(len({anchor, tested_main, current_main, head, merge}), 5)
            artifact = root / "artifact"
            artifact.mkdir()
            (artifact / "MERGE_SHA").write_text(merge + "\n")
            (artifact / "MERGE_PARENTS").write_text(tested_main + "\n" + head + "\n")
            source = (HERE / "probe.sh").read_text()
            # Relocate the fixed artifact mount for this local harness only.
            # All source-selection and reconstruction commands are unchanged.
            identity = source[source.index("sha() {"):source.index('chmod -R a+rX "$work"')]
            identity = identity.replace("/tmp/fren", str(artifact))
            prefix = '''set -euo pipefail
note() { printf '%s\\n' "$*"; }
auth_fetch() {
  if [ "$1" = "$RECORDED_MERGE" ] && [ "$MISSING_MERGE" = 1 ]; then return 1; fi
  git -C "$work" fetch --quiet "$ORIGIN" "$@"
}
'''
            for missing in ("0", "1"):
                work = root / ("work-" + missing)
                env = {**os.environ, "work": str(work), "ORIGIN": str(origin), "HEAD": head,
                       "REPO": "owner/fren", "RUN": "42", "RECORDED_MERGE": merge, "MISSING_MERGE": missing,
                       "GIT_AUTHOR_NAME": "test", "GIT_COMMITTER_NAME": "test",
                       "GIT_AUTHOR_EMAIL": "test@example.com", "GIT_COMMITTER_EMAIL": "test@example.com"}
                subprocess.run(["bash", "-c", prefix + identity], env=env, check=True, capture_output=True, text=True)
                actual = subprocess.check_output(["git", "-C", str(work), "rev-parse", "HEAD^{tree}"], text=True).strip()
                self.assertEqual(actual, expected_tree)
                parents = subprocess.check_output(["git", "-C", str(work), "show", "-s", "--format=%P"], text=True).split()
                self.assertEqual(parents, [tested_main, head])
                self.assertFalse((work / "later").exists())
            (artifact / "MERGE_PARENTS").write_text(tested_main + "\n" + current_main + "\n")
            env["work"] = str(root / "wrong-head")
            result = subprocess.run(["bash", "-c", prefix + identity], env=env, capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("not of " + head, result.stdout)
            self.assertFalse(Path(env["work"]).exists())


if __name__ == "__main__":
    unittest.main()
