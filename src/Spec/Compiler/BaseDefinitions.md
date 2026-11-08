# Base definitions

The compiler's representations share item identities, source locations and
information for reporting errors. This chapter describes those foundations.
The [compiler overview](Overview.md) describes where they are used. An item
is a declaration such as a function or theory; a source file is the original
file presented to a front end.

## Item identities

An item path identifies a declaration within its enclosing modules and
items. A compiler-generated item also needs an identity even though the
user did not write its declaration.

**Dynamic semantics**

r[base.item.path]
An item's identity is its path, including its enclosing module and item.

r[base.item.generated]
A generated item's identity extends its parent's path with its kind and a
position-based index.

r[base.item.determinism]
The same files give the same item identities across runs and front ends.

For example, `f.{closure#0}` names a generated closure belonging to `f`;
`g.{closure#0}` belongs to a different parent. Generated binders use de
Bruijn indices and do not need generated item names.

## Files, spans and source maps

A span identifies a range in a source file. Byte offsets count UTF-8 bytes,
not characters or editor columns. A source map relates the text given to the
parser to the original file when the text is embedded in another document.

**Dynamic semantics**

r[base.span.file]
A span contains a file identity and a half-open byte range in that file.

r[base.span.bounds]
A span's start and end are ordered byte offsets within its file.

r[base.source-map.embedded]
A source map translates positions in Markdown Fren blocks and hosted
`fren { … }` bodies to positions in their original files.

r[base.source-map.utf16]
Conversion to UTF-16 columns occurs at an editor boundary.

For the UTF-8 text `aéz`, the bytes of `é` occupy `[1, 3)` and `z` starts
at byte 3. `[1, 1)` is an empty range; `[3, 1)` is not ordered. If an
unchanged block body starts at byte 100 of its file, its local range
`[1, 3)` maps to file range `[101, 103)`. A source map must account for
how its body was extracted; the example does not prescribe its representation.

**Proof obligations**

r[base.span.range-contract] spec::base_definitions::range_contract::{forward, empty, reversed, outside}
The following independent cases distinguish valid, empty, reversed and out-of-bounds
byte ranges. They do not bind a compiler span implementation.

```fren
pub mod spec
pub mod spec::base_definitions

pub fn range_valid?(lo: Int, hi: Int, size: Int) :=
  0 <= lo <= hi <= size

pub proc range_contract(size: Int) {
  require positive: size > 1
  expect forward: range_valid?(0, 1, size)
  expect empty: range_valid?(size, size, size)
  expect reversed: not range_valid?(1, 0, size)
  expect outside: not range_valid?(0, size + 1, size)
}
```

r[base.source-map.offset-contract] spec::base_definitions::offset_contract::{first, last}
For the unchanged body in the example, translation adds the body start to
each endpoint.

```fren
pub proc offset_contract(x: Int) {
  expect first: x + 1 - x = 1
  expect last: x + 3 - x = 3
}
```

## Origins

An origin records where a node came from for diagnostics and debugging. A
node may have been transformed several times since the user wrote it.

**Dynamic semantics**

r[base.origin.contents]
An origin records a source span, display names of bound variables, and the
chain of derivation steps that produced the node.

r[base.origin.table]
Expression and type nodes refer to origins in a per-item table.

r[base.origin.remap]
Moving a term between items remaps its origins into the target item's table.

r[base.origin.independence]
Origins do not determine structural equality, hashing or compiler behavior.

r[base.origin.occurrences]
Structurally equal expressions at distinct diagnostic occurrences remain
distinct occurrences.

For example, specialization may move an expression from `f` into a new
item. Its origin references must then refer to that item's table, while the
recorded source location still supports a message about the original
expression. A semantic choice used by a later pass is represented separately
from origin information.

## Diagnostics

A diagnostic is data about a problem; rendering presents that data to a
reader or tool. A label attaches an explanation to a source span. A
suggestion describes an edit and says how confidently it can be applied.

**Dynamic semantics**

r[base.diagnostic.contents]
A diagnostic contains a code, a primary span, labelled spans, notes and
suggestions with applicability levels.

r[base.diagnostic.suggestion]
A suggestion is an edit to the lossless syntax tree.

r[base.diagnostic.applicability]
Applicability distinguishes a machine-applicable suggestion from one that
may be wrong.

r[base.diagnostic.rendering]
Text and JSON rendering present the same diagnostic data.

For example, an error can point to a use as its primary span and label a
separate declaration with an explanation. A proposed replacement may be safe
to apply automatically, or may need a person's judgment. The applicability
level communicates that distinction to a client.

## S-expression versioning

Compiler representations have a machine-readable S-expression form. Its
version identifies the format used by saved data and consumers.

**Dynamic semantics**

r[base.sexp.version]
The S-expression format carries a format version.

r[base.sexp.saved-version]
The hosted front end's saved state and cache keys carry a format version.

The version is part of the format contract; this chapter does not prescribe
a version number, wire schema or compatibility policy.

> **Note:** The checked cases above establish only arithmetic facts about the
> examples. The base, source and diagnostic libraries and their bindings to
> contracts are future work. The remaining rules are listed as pending
> formalization; no production implementation or property test is claimed.
