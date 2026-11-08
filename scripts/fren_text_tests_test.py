#!/usr/bin/env python3
"""Byte-level regressions against the actual compiled registered demo callback.
Run after building fren2_test: scripts/heavy --offline python3 scripts/fren_text_tests_test.py
"""
import pathlib
import subprocess
import tempfile
import unittest

BINARY = (pathlib.Path(__file__).resolve().parents[1] / '.lake/build/bin/fren2_test').resolve()


class TextTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='fren-text-tests-')
        self.addCleanup(self.temp.cleanup)
        self.root = pathlib.Path(self.temp.name)
        self.directory = self.root / 'test/FrenTextDemo'
        self.directory.mkdir(parents=True)
        self.path = self.directory / 'cases.fren'

    def run_cli(self, *args, status=0):
        p = subprocess.run([BINARY, '--lib', 'FrenTextDemo', *args], cwd=self.root,
                           capture_output=True, timeout=20)
        self.assertEqual(p.returncode, status, p.stdout + p.stderr)
        return (p.stdout + p.stderr).decode()

    def check_unchanged(self, data, *args, status=1):
        self.path.write_bytes(data)
        self.run_cli(*args, status=status)
        self.assertEqual(self.path.read_bytes(), data)

    def test_check_partial_failures_and_bless_bytes(self):
        before = ('-- πreamble\r\n\r\n-- case: good\r\n-- context:  7 \r\n'
                  '2\r\n3\r\n-- result: 12\r\n-- retain ü\r\n\r\n'
                  '-- case: wrong\r\n4\r\n-- result: 999\r\n-- keep this\r\n\r\n'
                  '-- case: missing\r\n8').encode()
        self.path.write_bytes(before)
        out = self.run_cli(status=1)
        self.assertIn('3 cases, 2 failed, 0 blessed', out)
        self.assertIn('- expected: 999\n+ actual: 4', out)
        self.assertEqual(self.path.read_bytes(), before)
        self.run_cli('--bless')
        after = before.replace(b'-- result: 999', b'-- result: 4') + b'\r\n-- result: 8'
        self.assertEqual(self.path.read_bytes(), after)
        self.run_cli()
        self.run_cli('--bless')
        self.assertEqual(self.path.read_bytes(), after)

    def test_filter_changes_only_selected_result(self):
        before = b'-- case: choose\n1\n-- result: wrong\n\n-- case: leave\n2\n-- result: wrong'
        self.path.write_bytes(before)
        self.run_cli('--filter', 'choo', '--bless')
        self.assertEqual(self.path.read_bytes(), before.replace(b'-- result: wrong', b'-- result: 1', 1))
        self.run_cli('--filter', 'choose')
        self.run_cli(status=1)
        self.run_cli('--filter', 'absent', status=2)

    def test_multiline_error_replaces_entire_old_span(self):
        before = '-- case: error\r\nλ\r\n-- result: wrong\r\n--  old\r\n--  old2\r\n\r\n-- saved'.encode()
        self.path.write_bytes(before)
        self.run_cli('--bless')
        after = before.replace(b'-- result: wrong\r\n--  old\r\n--  old2\r\n',
                               '-- result: error: invalid natural number\r\n--  λ\r\n'.encode())
        self.assertEqual(self.path.read_bytes(), after)
        self.run_cli()

    def test_context_is_not_ignored_or_split(self):
        raw = '  x: Map<Int, Seq<Int>> = [(1, [2, 3])]  '
        before = f'-- case: context\n-- context:{raw}\n1\n-- result: wrong\n'.encode()
        self.path.write_bytes(before)
        self.run_cli('--bless')
        after = before.replace(b'-- result: wrong',
                               ('-- result: error: demo context must be a natural number, received:' + raw).encode())
        self.assertEqual(self.path.read_bytes(), after)
        self.run_cli()

    def test_missing_result_before_next_case(self):
        before = b'-- case: first\n5\n\n-- case: second\n6\n-- result: 6\n'
        # The demo trims trailing whitespace; the runner still preserves its bytes.
        self.path.write_bytes(before)
        self.run_cli('--filter', 'first', '--bless')
        after = before.replace(b'\n-- case: second', b'\n-- result: 5\n-- case: second')
        self.assertEqual(self.path.read_bytes(), after)
        self.run_cli()

    def test_duplicate_name_and_ambiguous_markers_rejected_before_writes(self):
        malformed = [
            b'-- case: same\n1\n-- case: same\n2\n',
            b'-- case: \n1\n',
            b'-- case: a\n-- context: 1\n-- context: 2\n3\n',
            b'-- case: a\n1\n-- result: 1\n-- result: 1\n',
            b'-- case: a\n1\n--  reserved input\n',
            b'-- case: a\n1\n-- result: 1\ntext after result\n',
            b'-- case: a\n-- result: 1\n',
            b'-- context: outside\n-- case: a\n1\n',
            b'-- case: bad\n\xff\n',
        ]
        for data in malformed:
            with self.subTest(data=data):
                self.check_unchanged(data, '--bless')
        self.path.write_bytes(b'-- case: valid\n1\n-- result: wrong\n')
        bad = self.directory / 'z-last.fren'
        bad.write_bytes(malformed[0])
        self.run_cli('--filter', 'valid', '--bless', status=1)
        self.assertEqual(self.path.read_bytes(), b'-- case: valid\n1\n-- result: wrong\n')
        self.assertEqual(bad.read_bytes(), malformed[0])

    def test_symlink_file_and_directory_rejected(self):
        outside = self.root / 'outside.fren'
        data = b'-- case: a\n1\n-- result: wrong\n'
        outside.write_bytes(data)
        self.path.symlink_to(outside)
        self.run_cli('--bless', status=1)
        self.assertEqual(outside.read_bytes(), data)
        self.path.unlink()
        self.directory.rmdir()
        external = self.root / 'external'
        external.mkdir()
        (external / 'case.fren').write_bytes(data)
        self.directory.symlink_to(external, target_is_directory=True)
        self.run_cli('--bless', status=1)
        self.assertEqual((external / 'case.fren').read_bytes(), data)
        self.directory.unlink()
        (self.root / 'test').rmdir()
        (self.root / 'test').symlink_to(external, target_is_directory=True)
        self.run_cli('--bless', status=1)
        self.assertEqual((external / 'case.fren').read_bytes(), data)

    def test_invalid_cli_and_no_cases(self):
        self.run_cli(status=2)
        self.run_cli('--lib', '../outside', '--bless', status=2)
        self.run_cli('--unknown', status=2)
        self.run_cli('--filter', status=2)
        self.assertEqual(list(self.directory.iterdir()), [])


if __name__ == '__main__':
    unittest.main()
