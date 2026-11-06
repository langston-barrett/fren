"""Render model metadata as inert text before committing or posting it."""
import importlib.util
from pathlib import Path
import re
import sys

from common import TRAILERS

path = Path(__file__).resolve().parent.parent / "pr-review/check.py"
spec = importlib.util.spec_from_file_location("review_check", path)
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)

CI_CONTROL = re.compile(
    r"\[(?:skip\s+ci|ci\s+skip|no\s+ci|skip\s+actions|actions\s+skip)\]"
    r"|\b(?:skip|request)-checks\s*:", re.IGNORECASE)


def inert(text):
    """Break mentions, runner commands and commit check-control directives.

    Backticks do not stop a workflow's raw substring match. Use the same
    entity-aware mention neutralization as the review publisher, including
    inside code. Preserve the patch itself; this is only for metadata.
    """
    text = checker.unmention(text)
    text = re.sub(r":(?=:)", ":\u200b", text).replace("##[", "#\u200b#[")
    return CI_CONTROL.sub(lambda m: m[0][0] + "\u200b" + m[0][1:], text)


def commit_message(text):
    """Only the publisher may supply terminal PR/round trailers."""
    # Prefixing also strips a message consisting solely of forged trailers.
    text = "\n\n" + text.strip()
    while match := TRAILERS.search(text):
        text = text[:match.start()].rstrip()
    return inert(text.strip())


def report(error):
    """Exception details can echo paths or credentials supplied by Codex."""
    print(inert(f"codex-agent failed: {type(error).__name__}"), file=sys.stderr)
