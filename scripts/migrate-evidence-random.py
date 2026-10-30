#!/usr/bin/env python3
"""One-off #368 migration: rename evidence values, preserving tested claims.

Run against the pre-migration tree. With --verify OLD_FREN NEW_FREN, each
changed standalone spec is checked before and after migration; diagnostics
and verdict summaries must agree after the vocabulary substitution.
"""
import argparse
import pathlib
import re
import shlex
import subprocess


def migrate(text):
    return re.sub(r'(fren\.evidence\s+"[^"\n]*)tested',
                  lambda m: m[0].replace('tested', 'random'), text)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify', nargs=2, metavar=('OLD_FREN', 'NEW_FREN'))
    parser.add_argument('--verify-hosted', nargs=2, metavar=('OLD_COMMAND', 'NEW_COMMAND'),
                        help='commands to check Lean specs; {file} is replaced by the path')
    args = parser.parse_args()
    changes = []
    for name in subprocess.check_output(['git', 'ls-files'], text=True).splitlines():
        path = pathlib.Path(name)
        if path.suffix not in {'.fren', '.md', '.lean'}:
            continue
        before = path.read_text()
        after = migrate(before)
        if before == after:
            continue
        changes.append((path, before, after))

    def command(path, index):
        if path.suffix in {'.fren', '.md'} and args.verify:
            return [args.verify[index], 'check', str(path)]
        if path.suffix == '.lean' and args.verify_hosted:
            return [part.replace('{file}', str(path))
                    for part in shlex.split(args.verify_hosted[index])]
        return None

    def run(cmd):
        return subprocess.run(cmd, text=True, capture_output=True)

    # Check the complete old tree before changing any imported specs.
    baseline = {path: run(cmd) for path, _, _ in changes
                if (cmd := command(path, 0)) is not None}
    for path, _, after in changes:
        path.write_text(after)

    failures = []
    for path, _, _ in changes:
        if path in baseline:
            old = baseline[path]
            new = run(command(path, 1))
            normalize = lambda text: text.replace('tested', 'random').replace('by testing', 'by random testing')
            if old.returncode != new.returncode or normalize(old.stdout + old.stderr) != normalize(new.stdout + new.stderr):
                failures.append(str(path))
        print(path)
    if failures:
        for path, before, _ in changes:
            path.write_text(before)
        raise SystemExit('verdicts changed (migration restored): ' + ', '.join(failures))


if __name__ == '__main__':
    main()
