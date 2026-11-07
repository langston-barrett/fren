"""Original-evidence lifetime: merge, running, outputless."""

import unittest
from evidence_cases import OriginalEvidenceCases


class Evidence(OriginalEvidenceCases, unittest.TestCase):
    shape = 'main-update'
    running = True
    outputless = True


if __name__ == "__main__":
    unittest.main()
