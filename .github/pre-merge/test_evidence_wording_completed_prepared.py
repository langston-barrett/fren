"""Original-evidence lifetime: wording, completed, prepared."""

import unittest
from evidence_cases import OriginalEvidenceCases


class Evidence(OriginalEvidenceCases, unittest.TestCase):
    shape = 'wording'
    running = False
    outputless = False


if __name__ == "__main__":
    unittest.main()
