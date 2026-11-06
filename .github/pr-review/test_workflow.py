"""Tests of the order of claude-review.yml's `review` job: the workflow's
own scripts are checked out into the empty workspace and moved out of it
before the pull request's tree is checked out, so that nothing the pull
request commits at `.trusted`, such as a symbolic link, is in their way,
and the configuration and links of the pull request's tree are removed
before the model runs."""

import os
import re
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
WORKFLOW = os.path.join(HERE, "..", "workflows", "claude-review.yml")


def review_steps():
    """The `review` job's steps, as text, in order."""
    with open(WORKFLOW) as f:
        text = f.read()
    job = re.search(r"^  review:\n(.*?)(?=^  \w[\w-]*:\n)", text, re.MULTILINE | re.DOTALL).group(1)
    return re.split(r"^    - ", job.split("    steps:\n", 1)[1], flags=re.MULTILINE)[1:]


def first(steps, pattern):
    return next(i for i, s in enumerate(steps) if re.search(pattern, s))


class ReviewJob(unittest.TestCase):
    def test_trusted_copy_comes_first(self):
        steps = review_steps()
        trusted = first(steps, r"path: \.trusted")
        moved = first(steps, r'mv \.trusted "\$RUNNER_TEMP/trusted"')
        head = first(steps, r"ref: \$\{\{ needs\.prepare\.outputs\.head \}\}")
        self.assertEqual(trusted, 0, "the trusted checkout is the job's first step")
        self.assertLess(moved, head)
        # No other step checks anything out before the head.
        self.assertEqual([i for i, s in enumerate(steps[:head]) if "actions/checkout" in s], [trusted])

    def test_configuration_removed_before_the_model(self):
        steps = review_steps()
        head = first(steps, r"ref: \$\{\{ needs\.prepare\.outputs\.head \}\}")
        removed = first(steps, r"-type l -print0")
        model = first(steps, r"anthropics/claude-code-action")
        self.assertLess(head, removed)
        self.assertLess(removed, model)
        for name in ("CLAUDE.md", "AGENTS.md", ".mcp.json", ".claude", ".codex", ".agents"):
            self.assertIn(name, steps[removed])

    def test_codex_uses_trusted_scripts_and_exclusive_credential(self):
        steps = review_steps()
        model = first(steps, r"name: Review with Codex in isolation")
        teardown = first(steps, r"name: Confirm Codex teardown")
        upload = first(steps, r"uses: actions/upload-artifact")
        self.assertLess(model, teardown)
        self.assertLess(teardown, upload)
        self.assertIn("$RUNNER_TEMP/trusted/.github/pr-review/codex.py", steps[model])
        self.assertIn("needs.prepare.outputs.engine == 'codex'", steps[model])
        self.assertIn("secrets.CODEX_REVIEW_AUTH_JSON", steps[model])
        self.assertNotIn("github.token", steps[model])
        self.assertNotIn("CLAUDE_CODE_OAUTH_TOKEN", steps[model])
        claude = steps[first(steps, r"anthropics/claude-code-action")]
        self.assertIn("needs.prepare.outputs.engine == 'claude'", claude)
        self.assertNotIn("CODEX_REVIEW_AUTH_JSON", claude)


if __name__ == "__main__":
    unittest.main()
