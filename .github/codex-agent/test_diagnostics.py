"""The diagnostic fallback when neither log contains an error line."""
from contextlib import redirect_stderr
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run as agent_run


class StderrFallback(unittest.TestCase):
    def test_nonerror_lines_are_distinct_bounded_redacted_and_inert(self):
        credential = "fixture-sensitive-credential"
        third = "third line " * 100
        with tempfile.TemporaryDirectory() as temp:
            output = Path(temp)
            (output / "stderr.log").write_text(
                "\nstarting @claude\nstarting @claude\nordinary ::notice:: "
                + credential + "\n" + third + "\nfourth line\n")
            (output / "log.jsonl").write_text(json.dumps(
                {"type": "assistant", "message": "arbitrary model event"}) + "\n")
            rendered = io.StringIO()
            with redirect_stderr(rendered):
                agent_run.failure_summary(output, [credential], 1)
        lines = rendered.getvalue().splitlines()
        self.assertEqual(len(lines), 4)
        self.assertEqual(lines[0], "codex-agent sandbox exited 1")
        self.assertEqual(lines[1], "stderr: starting @\u200bclaude")
        self.assertIn("[redacted]", lines[2])
        self.assertNotIn(credential, rendered.getvalue())
        self.assertNotIn("::", lines[2])
        self.assertEqual(lines[3], "stderr: " + third.strip()[:400])
        self.assertNotIn("fourth line", rendered.getvalue())
        self.assertNotIn("arbitrary model event", rendered.getvalue())


if __name__ == "__main__":
    unittest.main()
