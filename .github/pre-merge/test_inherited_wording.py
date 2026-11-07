"""Inherited revocation lifecycle for wording; all shared cases apply."""

import unittest
from inherited_cases import InheritedRevocationCases


class WordingRevocation(InheritedRevocationCases, unittest.TestCase):
    shapes = ("wording",)


if __name__ == "__main__":
    unittest.main()
