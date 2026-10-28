#!/usr/bin/env python3
"""One-off #371 migration of declared/inline pattern types to subset aliases.

Run on the pre-migration tree. Expression pattern tests are retained. Inline
restrictions get deterministic fresh declarations immediately before the
containing item, including its `set_option ... in` wrappers. --verify checks
all changed standalone specs before any write and after all writes; it saves
the complete diagnostic/verdict pairs for review, because subset declarations
introduce new inhabitation/definedness checks and per-invariant diagnostics.
"""
import argparse
import dataclasses
import json
import pathlib
import re
import subprocess


@dataclasses.dataclass
class Token:
    text: str
    start: int
    end: int


def tokens(text):
    out = []
    i = 0
    while i < len(text):
        if text[i].isspace():
            i += 1
            continue
        if text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
            continue
        if text.startswith('/-', i):
            depth = 1
            i += 2
            while i < len(text) and depth:
                if text.startswith('/-', i):
                    depth += 1
                    i += 2
                elif text.startswith('-/', i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            continue
        start = i
        raw = re.match(r'r(#+)?"', text[i:])
        if raw:
            hashes = raw.group(1) or ''
            marker = '"' + hashes
            end = text.find(marker, i + len(raw.group()))
            if end < 0:
                raise ValueError('unterminated raw string')
            i = end + len(marker)
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == '\\':
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        elif text[i].isalpha() or text[i] == '_':
            i += 1
            while i < len(text) and (text[i].isalnum() or text[i] in "_'?!"):
                i += 1
        elif text[i].isdigit():
            i += 1
            while i < len(text) and (text[i].isalnum() or text[i] == '_'):
                i += 1
        else:
            operator = next((op for op in ['..=', '::', ':=', '..', '->', '<=', '>=', '!=']
                             if text.startswith(op, i)), None)
            i += len(operator) if operator else 1
        out.append(Token(text[start:i], start, i))
    return out


@dataclasses.dataclass
class TypeNode:
    first: int
    base_end: int
    end: int
    children: list
    is_token: int = None
    pattern_start: int = None
    base_name: str = ""


class Migrator:
    def __init__(self, filename, known, reserved, aliases):
        self.filename = filename
        self.known = known
        self.reserved = reserved
        self.aliases = aliases
        self.serial = 0
        self.created = []
        self.edits = []
        self.stem = ''.join(part[:1].upper() + part[1:] for part in
                            re.findall(r'[A-Za-z0-9]+', pathlib.Path(filename).stem)) or 'Spec'

    def fresh(self):
        while True:
            self.serial += 1
            name = f'Subset{self.stem}{self.serial}'
            if name not in self.reserved:
                self.reserved.add(name)
                self.known.add(name)
                return name

    def is_bool(self, name, seen=()):
        if name == 'Bool':
            return True
        if name in seen:
            return False
        base = self.aliases.get(name)
        return base is not None and self.is_bool(base, seen + (name,))

    def fragment(self, text, offset):
        ts = tokens(text)
        if not ts:
            return text
        # Generated declarations and binders must not capture source names,
        # including constants used as range endpoints.
        self.reserved.update(token.text for token in ts)
        binder_base = 'subset_value'
        while binder_base in self.reserved or binder_base + '?' in self.reserved:
            binder_base += '_'
        t = [token.text for token in ts] + ['']
        # Generic parameters are types within their declaration even though
        # they have no standalone type declaration for global discovery.
        generic_parameters = set()
        for j in range(len(ts) - 3):
            if t[j] not in {'enum', 'struct', 'fn', 'proc', 'type'} or t[j + 2] != '<':
                continue
            k = j + 3
            while k < len(ts) and re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*', t[k]):
                generic_parameters.add(t[k])
                k += 1
                if t[k] != ',':
                    break
                k += 1
        # Keep actual lowercase type declarations usable without treating
        # prose such as "type this" as declarations during global discovery.
        for j, token in enumerate(ts[:-1]):
            if token.text in {'type', 'enum', 'struct'}:
                prefix = text[text.rfind('\n', 0, token.start) + 1:token.start].strip()
                if prefix in {'', 'pub', 'ordered', 'pub ordered'} and re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*', t[j + 1]):
                    self.known.add(t[j + 1])

        def bound_start(i):
            if i >= len(ts):
                return False
            word = t[i]
            return (word == '-' and i + 1 < len(ts) and t[i + 1][:1].isdigit()) or word[:1].isdigit() or (
                re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*', word) is not None
                and word not in {'in', 'where', 'and', 'or', 'iff', 'when', 'unless',
                                 'ensure', 'assume', 'expect', 'cover', 'out', 'call',
                                 'then', 'else', 'proc', 'fn', 'type', 'true', 'false'})

        def pattern(i):
            if i >= len(ts):
                raise ValueError('missing pattern')
            if t[i] == '-':
                i += 1
            if t[i] not in {'..', '..='}:
                i += 1
                while t[i] == '::':
                    i += 2
                if t[i] == '(':
                    i += 1
                    if t[i] != ')':
                        i = pattern(i)
                        while t[i] == ',':
                            i = pattern(i + 1)
                    if t[i] != ')':
                        raise ValueError('unterminated payload pattern')
                    i += 1
            if t[i] in {'..', '..='}:
                op = i
                i += 1
                if bound_start(i) and ts[i].start == ts[op].end:
                    if t[i] == '-':
                        i += 1
                    i += 1
                    while t[i] == '::':
                        i += 2
            if t[i] == '|':
                return pattern(i + 1)
            return i

        def type_at(i):
            first = i
            if i >= len(ts) or not re.match(r'^[A-Za-z_]', t[i]):
                return None
            name = t[i]
            i += 1
            while t[i] == '::':
                name = t[i + 1]
                i += 2
            if name not in self.known and name not in generic_parameters:
                return None
            children = []
            if t[i] == '<':
                i += 1
                while True:
                    child = type_at(i)
                    if child is None:
                        return None
                    children.append(child)
                    i = child.end
                    if t[i] != ',':
                        break
                    i += 1
                if t[i] != '>':
                    return None
                i += 1
            base_end = i
            if t[i] != 'is':
                return TypeNode(first, base_end, i, children, base_name=name)
            is_token = i
            i += 1
            try:
                end = pattern(i)
            except (ValueError, IndexError):
                return None
            return TypeNode(first, base_end, end, children, is_token, i, name)

        def restricted(node):
            return node.is_token is not None or any(restricted(c) for c in node.children)

        def rewrite(node, definitions, alias_name=None):
            start = ts[node.first].start
            base_end = ts[node.base_end - 1].end
            base = text[start:base_end]
            local_edits = []
            for child in node.children:
                replacement = rewrite(child, definitions)
                local_edits.append((ts[child.first].start - start, ts[child.end - 1].end - start, replacement))
            for a, b, replacement in reversed(local_edits):
                base = base[:a] + replacement + base[b:]
            if node.is_token is None:
                return base
            pattern_text = text[ts[node.pattern_start].start:ts[node.end - 1].end]
            # A wildcard over a type parameter is unrestricted and needs no
            # generated alias that would escape its generic declaration.
            base_name = node.base_name
            if base_name in generic_parameters and pattern_text != '_':
                raise ValueError(f'{self.filename}: a restricted generic parameter requires manual migration')
            if pattern_text == '_' and base_name not in {'Bool', 'Int', 'Nat', 'String'}:
                if alias_name is None:
                    return base
            name = alias_name or self.fresh()
            binder = binder_base + ('?' if self.is_bool(base_name) else '')
            before_is = text[ts[node.base_end - 1].end:ts[node.is_token].start]
            after_is = text[ts[node.is_token].end:ts[node.pattern_start].start]
            declaration = f'{name} = {binder}: {base}{before_is} where invariant: {binder} is{after_is}{pattern_text}'
            if alias_name is not None:
                return declaration[len(name):].lstrip()
            definitions.append('type ' + declaration + '\n')
            self.created.append(name)
            self.aliases[name] = base_name
            return name

        item_starts = []
        brace = paren = 0
        item_start = 0
        pending_option = None
        for i, token in enumerate(ts):
            if brace == 0 and paren == 0:
                line = text.rfind('\n', 0, token.start) + 1
                if token.text == 'set_option':
                    end = i + 2
                    while end + 1 < len(ts) and t[end] in {'.', '::'}:
                        end += 2
                    # One token is the option value (string, integer, Bool).
                    if end + 1 < len(ts) and t[end + 1] == 'in':
                        pending_option = line if pending_option is None else pending_option
                if token.text == '#' and t[i + 1] == 'guard_msgs':
                    pending_option = line if pending_option is None else pending_option
                if token.text in {'type', 'enum', 'struct', 'proc', 'fn', 'const', 'expect', 'refine', 'mod', 'use', 'tested', 'trusted'}:
                    item_start = pending_option if pending_option is not None else line
                    pending_option = None
            item_starts.append(item_start)
            brace += (token.text == '{') - (token.text == '}')
            paren += (token.text == '(') - (token.text == ')')
        replacements = []
        insertions = {}
        i = 0
        while i < len(ts):
            node = type_at(i)
            if node is None:
                i += 1
                continue
            if not restricted(node):
                i = max(i + 1, node.end)
                continue
            # Type starts are type annotations, type/collection arguments,
            # an alias RHS, or standalone function-signature arguments.
            previous = t[i - 1] if i else ''
            if previous not in {':', ':=', '<', ',', '(', '->'}:
                i += 1
                continue
            definitions = []
            is_alias = i >= 3 and t[i - 1] == ':=' and t[i - 3] == 'type' and node.is_token is not None
            if is_alias:
                name = t[i - 2]
                replacement = rewrite(node, definitions, name)
                a = ts[i - 1].start
            else:
                replacement = rewrite(node, definitions)
                a = ts[node.first].start
            b = ts[node.end - 1].end
            replacements.append((a, b, replacement))
            if definitions:
                insertions.setdefault(item_starts[i], []).extend(definitions)
            i = node.end
        changes = replacements + [(at, at, ''.join(defs)) for at, defs in insertions.items()]
        for a, b, replacement in sorted(changes, reverse=True):
            self.edits.append({'start': offset + a, 'end': offset + b, 'replacement': replacement})
            text = text[:a] + replacement + text[b:]
        return text

    def migrate(self, source):
        if pathlib.Path(self.filename).suffix != '.md':
            return self.fragment(source, 0)
        changes = []
        fence = re.compile(r'^```([^\n]*)\n(.*?)^```[^\n]*$', re.M | re.S)
        for block in fence.finditer(source):
            language = block.group(1).strip()
            if language not in {'', 'fren'}:
                continue
            body = block.group(2)
            if language == '' and not re.search(r'\b(type|proc|enum|struct|fn|const)\s+[A-Za-z_]', body):
                continue
            result = self.fragment(body, block.start(2))
            if result != body:
                changes.append((block.start(2), block.end(2), result))
        for a, b, replacement in reversed(changes):
            source = source[:a] + replacement + source[b:]
        return source


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('files', nargs='*')
    parser.add_argument('--verify', nargs=2, metavar=('OLD_FREN', 'NEW_FREN'))
    parser.add_argument('--report', default='subset-migration-report.json')
    parser.add_argument('--dry-run', action='store_true')
    args = parser.parse_args()
    files = args.files or subprocess.check_output(['git', 'ls-files'], text=True).splitlines()
    paths = [pathlib.Path(name) for name in files if pathlib.Path(name).suffix in {'.fren', '.md', '.lean'}]
    sources = {path: path.read_text() for path in paths}
    declarations = re.compile(r'\b(?:type|enum|struct)\s+([A-Za-z_][A-Za-z0-9_]*)')
    known = {'Bool', 'Int', 'Nat', 'String', 'Set', 'Seq', 'Rel'}
    for source in sources.values():
        known.update(name for name in declarations.findall(source) if name[:1].isupper())
    reserved = set(known)
    aliases = {}
    for source in sources.values():
        for name, base in re.findall(r'\btype\s+(\w+)\s*:=\s*((?:\w+::)*\w+)', source):
            aliases[name] = base.split('::')[-1]
    changed = []
    report = {}
    for path, source in sources.items():
        migrator = Migrator(str(path), known, reserved, aliases)
        after = migrator.migrate(source)
        if after == source:
            continue
        changed.append((path, source, after))
        report[str(path)] = {'generated': migrator.created, 'edits': migrator.edits}
    def check(binary, path):
        result = subprocess.run([binary, 'check', str(path)], text=True, capture_output=True)
        return {'exit': result.returncode, 'stdout': result.stdout, 'stderr': result.stderr}
    if args.verify:
        for path, _, _ in changed:
            if path.suffix in {'.fren', '.md'}:
                report[str(path)]['before'] = check(args.verify[0], path)
    if not args.dry_run:
        for path, _, after in changed:
            path.write_text(after)
        if args.verify:
            for path, _, _ in changed:
                if path.suffix in {'.fren', '.md'}:
                    report[str(path)]['after'] = check(args.verify[1], path)
    pathlib.Path(args.report).write_text(json.dumps(report, indent=2) + '\n')
    for path, _, _ in changed:
        print(path)


if __name__ == '__main__':
    main()
