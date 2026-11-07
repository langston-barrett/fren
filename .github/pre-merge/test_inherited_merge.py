"""Inherited revocation lifecycle for main-update; all shared cases apply."""

import unittest
from inherited_cases import InheritedRevocationCases


class MainMergeRevocation(InheritedRevocationCases, unittest.TestCase):
    shapes = ("main-update",)


if __name__ == "__main__":
    unittest.main()
