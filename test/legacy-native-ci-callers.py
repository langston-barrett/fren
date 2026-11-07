#!/usr/bin/env python3
"""Keep each CI test-suite caller in the temporary legacy quarantine."""

from pathlib import Path
import re
import shlex


FILES = tuple(sorted(p for p in Path('.github/workflows').iterdir()
                     if p.suffix in ('.yml', '.yaml')))
CI = '.github/workflows/ci.yml'
PRE = '.github/workflows/pre-merge.yml'


def check(workflows):
    callers = []
    manual = []
    for path, contents in workflows.items():
        for line in contents.splitlines():
            line = line.strip()
            if line.startswith(('#', 'name:')):
                continue
            if re.search(r'\blake\s+(?:-[^\s]+\s+)*test(?:\s|$)', line):
                command = line.removeprefix('- ').removeprefix('run: ')
                args = shlex.split(command)
                test = args.index('test')
                assert args[test + 1:test + 3] == ['--', '--skip-unstable-legacy'], (path, line)
                if path.endswith('pre-merge.yml'):
                    assert '--skip-own-mutants' in args[test + 3:] and '--shard' in args[test + 3:], line
                elif '-Kcoverage=$COVERAGE_RUNTIME' not in args:
                    assert '--skip-own-mutants' not in args and '--shard' in args[test + 3:], line
                else:
                    assert '--skip-own-mutants' not in args and '--shard' not in args, line
                callers.append((path, args[:test]))
            if 'fren_test' in line and ('lake env ' in line or '-- .lake/build/bin/fren_test' in line):
                assert '--job ' in line, (path, line)
            if '--job ' in line and 'fren_test' in line:
                match = re.search(r'--job\s+(\w+)', line)
                assert match, (path, line)
                manual.append((path, match.group(1)))
    ci, pre = CI, PRE
    assert sorted(callers) == sorted([(ci, ['lake']), (ci, ['lake', '-Kcoverage=$COVERAGE_RUNTIME']), (pre, ['lake'])]), callers
    assert sorted(manual) == sorted([(pre, 'ui'), (ci, 'ownSpecAgreement'),
                                     (ci, 'methodsAgree'), (ci, 'methodsAgree')]), manual
    assert re.search(r'(?m)^  methods-agree:\n    if: \$\{\{ false \}\}', workflows[ci])
    assert 'lake exe fren_coverage "$gcov"' in workflows[ci]
    assert 'lake exe fren_coverage "$LLVM_COV" gcov' in workflows[ci]


def main():
    workflows = {str(path): path.read_text() for path in FILES}
    check(workflows)
    # A missing opt-in at each caller must fail, including the coverage caller.
    for path, contents in workflows.items():
        for match in re.finditer(r'(?m)^.*\blake\s+(?:-[^\s]+\s+)*test -- --skip-unstable-legacy.*$', contents):
            changed = dict(workflows)
            line = match.group()
            changed[path] = contents[:match.start()] + line.replace(' --skip-unstable-legacy', '', 1) + contents[match.end():]
            try:
                check(changed)
            except AssertionError:
                continue
            raise AssertionError(f'guard accepted missing opt-in: {path}: {line}')
    for addition in ('lake env .lake/build/bin/fren_test',
                     'lake env .lake/build/bin/fren_test --job enumeration'):
        changed = dict(workflows)
        changed[CI] += '\n    - run: ' + addition + '\n'
        try:
            check(changed)
        except AssertionError:
            continue
        raise AssertionError(f'guard accepted unexpected driver caller: {addition}')
    print('CI test callers and missing-opt-in regressions passed')


if __name__ == '__main__':
    main()
