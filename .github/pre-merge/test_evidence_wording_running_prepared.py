"""Original-evidence lifetime: wording, running, prepared."""

import unittest
from evidence_cases import OriginalEvidenceCases


class Evidence(OriginalEvidenceCases, unittest.TestCase):
    shape = 'wording'
    running = True
    outputless = False


if __name__ == "__main__":
    unittest.main()
