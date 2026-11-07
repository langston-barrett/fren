"""Original-evidence lifetime: wording, completed, outputless."""

import unittest
from evidence_cases import OriginalEvidenceCases


class Evidence(OriginalEvidenceCases, unittest.TestCase):
    shape = 'wording'
    running = False
    outputless = True


if __name__ == "__main__":
    unittest.main()
