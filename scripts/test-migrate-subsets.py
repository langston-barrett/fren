#!/usr/bin/env python3
"""Regression checks for the one-off subset migration's scope boundaries."""
import pathlib
import runpy
import unittest

Migrator = runpy.run_path(str(pathlib.Path(__file__).with_name('migrate-subsets.py')))['Migrator']


class MigrationTests(unittest.TestCase):
    def migrate(self, source, filename='sample.fren', aliases=None):
        known = {'Bool', 'Int', 'Nat', 'String', 'Set', 'Seq', 'Rel', 'Flag'}
        result = Migrator(filename, known, set(known), aliases or {}).migrate(source)
        again = Migrator(filename, known, set(known), aliases or {}).migrate(result)
        self.assertEqual(result, again)
        return result

    def test_open_range_keeps_delimiter_and_expression(self):
        result = self.migrate('proc p(n: Nat is 1..): () { expect e: n is 1.. }\n')
        self.assertIn('invariant: subset_value is 1..\n', result)
        self.assertIn('proc p(n: SubsetSample1):', result)
        self.assertIn('expect e: n is 1..', result)

    def test_nested_argument_and_negative_closed_range(self):
        result = self.migrate('type Small := Int is -2..=2\nfn f(Seq<Int is 0..3>): Small\n')
        self.assertIn('type Small = subset_value: Int', result)
        self.assertIn('is -2..=2', result)
        self.assertIn('fn f(Seq<SubsetSample1>): Small', result)

    def test_wrappers_stay_with_original_item(self):
        result = self.migrate('#guard_msgs in\nset_option fren.evidence "enumerated" in\nfn f(Int is 0..3): Int\n')
        self.assertLess(result.index('type Subset'), result.index('#guard_msgs'))
        self.assertIn('#guard_msgs in\nset_option fren.evidence "enumerated" in\nfn f(', result)

    def test_fresh_names_and_binder_do_not_capture(self):
        result = self.migrate('const SubsetSample1: Int := 0\nconst subset_value: Int := 2\nfn f(Int is subset_value..): Int\n')
        self.assertIn('type SubsetSample2 = subset_value_: Int', result)
        self.assertIn('invariant: subset_value_ is subset_value..', result)

    def test_qualified_bool_alias_uses_question_binder(self):
        result = self.migrate('fn f(flags::Flag is true): Int\n', aliases={'Flag': 'Bool'})
        self.assertIn('subset_value?: flags::Flag', result)

    def test_strings_comments_and_prose_are_untouched(self):
        source = 'Prose: Int is 0..3\n```text\nfn f(Int is 0..3): Int\n```\n```fren\n-- Int is 1..\nconst s: String := "Int is 2.."\nfn f(Int is 0..3): Int\n```\n'
        result = self.migrate(source, 'sample.md')
        self.assertIn('Prose: Int is 0..3', result)
        self.assertIn('```text\nfn f(Int is 0..3): Int', result)
        self.assertIn('-- Int is 1..', result)
        self.assertIn('"Int is 2.."', result)
        self.assertIn('fn f(SubsetSample1): Int', result)


if __name__ == '__main__':
    unittest.main()
