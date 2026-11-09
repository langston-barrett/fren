# HIR and name resolution

The high-level intermediate representation (HIR) keeps surface expressions
but replaces each name use with its declaration. It sits between the
[structured AST](AstAndParsing.md) and type checking. This chapter specifies
single-file AST-to-HIR resolution, using the
[scope rules](../Language/NamesAndScope.md).

## 1. Input and result boundary

The current `FrenAst.Document` exposes declarations, parameters, written
paths, type annotations, expressions and match arms. Each written occurrence
has tokens with source spans. `FrenParse.parseFile` produces that document
or a parse failure. `FrenBase.ItemId` and `FrenBase.Binding` already supply
canonical item identities and nearest-first raw-index contexts.

**Proof obligations**

r[hir.input.complete]
The resolver consumes a successful file AST in the source domain, not a
parse failure, an expression root or a partial syntax tree.

r[hir.result.boundary]
Resolution returns either a resolved module or nonempty diagnostic data;
a result containing an unresolved name is not a successful resolved module.

A caller must supply the actual parsed document. Fabricated documents need
syntax validation before this boundary. The minimal public operation is a
function from that document to success or diagnostic failure, with no
caller-supplied resolution table or validity verdict. Its storage layout does not decide resolution. It need not
provide error recovery, a serializer, a generic pass framework or an API for
another module's private bodies. The typed textual-context adapter is
a parser client; moduleless resolution with an externally supplied module
is outside this input domain.

## 2. Minimal resolved information

A *resolved reference* denotes either an item path or a local slot in the
occurrence's context. The following is an interface inventory, not another
executable IR definition. An implementation may use recursive Lean datatypes
or a source-indexed result with complete resolved occurrence information.

| Component | Required information in a successful result |
| --- | --- |
| Module | Its canonical identity and declarations in source order. |
| Enumeration | Item identity and its ordered payload-free constructor identities. |
| Function | Item identity, ordered parameters, resolved written result type and expression body. |
| Global expectation | Item identity, ordered parameters and ordered labelled `assume`/`expect` bodies. |
| Parameter | Written name and span, resolved annotation, and whether `Bool` was implicit from `?`. |
| Type reference | Built-in `Bool`, built-in `Int`, or canonical enumeration identity, with its written occurrence. |
| Expression reference | Canonical item identity or natural local index, with its written path and span. |
| Match arm | Resolved constructor identity and body; no pattern binders in this source domain. |
| Other expression forms | Original literal values, operators, child structure and child order. |

The output keeps `if`, `let`, `match`, calls and parentheses; it does not
lower arithmetic or evaluate a function. The implementation may retain the
AST alongside resolved occurrence information instead of duplicating token
storage. Every consumer must be able to obtain the resolved target at each
semantic name occurrence without running lookup again.

The resolver's source-indexed result is also read into the shared expression
representation, a module of HIR expressions with one recursive datatype for
every phase from HIR to `flat`. There a local is its index, an item is its
canonical identity, and every surface form, parentheses included, is still a
node. Each node keeps an origin for messages: the span of its first token,
and for a binder its written name. Type checking takes this module as its
whole input: it does not read source text or run the parser or the resolver
again.

**Proof obligations**

r[hir.references.total]
Every expression path, call callee, named type and arm constructor has a
resolved target of its required category in a successful result.

r[hir.references.locals]
Each local reference has an index into the exact lexical context specified
by the Language chapter, pointing to the selected binder's entry.

r[hir.references.items]
An item reference uses its canonical module-and-item path, with a constructor
identity extending its enumeration's path by the written variant name.

r[hir.structure.preservation]
Resolution preserves declarations, parameters, expectation members, arms,
expression children, literal values and operators in their written order.

Expression references may denote a local or module item without establishing
that it has a value type or is callable. Type positions require types and
arm patterns require constructors, since those categories determine the
resolved representation. Arity, operand types, whether an expression item
is usable as a value, and whether a callee is callable belong to typing.
Thus the syntax `x(y)` can resolve both local references before failing in
typing. The resolver must not treat an expectation label as a local value.

## 3. Identity and source occurrences

Canonical item identity uses `FrenBase.ItemId.named`.
For module `signals`, enumeration `Light` and variant `Red`, the components
are `[signals, Light, Red]`, not the last segment alone. Display strings
are not identity keys. Local slot identity is contextual: adding a binder
moves an older reference from index `i` to `i + 1`.

**Proof obligations**

r[hir.identity.stable]
The same duplicate-free declarations give the same item identities across
runs and permutations of declaration order.

r[hir.identity.alpha]
Consistent capture-avoiding renaming of local binders and their uses leaves
the resolved local indices unchanged.

r[hir.origins.preserved]
Every resolved declaration, binder, type, expression and name use retains
its original file identity and half-open UTF-8 byte span, including separate
equal-spelling occurrences.

r[hir.origins.independent]
Source coordinates and written local names do not decide semantic reference
equality once resolution has selected the target.

Reordering declarations may change spans and output order. The identity
claim compares canonical targets, not whole output byte equality. Likewise,
index 0 in two different functions or sibling contexts is not one binder.
Moving an expression to another context requires reindexing under the
[binding laws](Bindings.md); an origin table alone cannot do it. Diagnostics
use retained occurrences even when semantic nodes compare equal.

## 4. Pass laws and primitive facts

The full pass laws concern actual `FrenAstToHir` decisions. A supplied
`resolved?` flag or a serialization roundtrip does not establish them.

**Proof obligations**

r[hir.laws.collection]
On a duplicate-free source file, collection enumerates exactly its module
items and constructors before resolving any use.

r[hir.laws.lookup]
Each successful reference is exactly the target selected by the Language
chapter's lexical and path rules, and each unresolved use causes failure.

r[hir.laws.scope]
Every successful local index is in scope at its occurrence, including under
lets and inside every match arm.

r[hir.laws.determinism]
Fixed input produces the same semantic targets and diagnostic data, with
observable declarations and diagnostics in source order.

A well-scoped result alone is insufficient: choosing the wrong in-scope
slot can capture a reference. The wrapper's `NearestName` obligation in the
Language chapter states first-match selection independently of bounds.
Canonical child identity injectivity does not establish traversal correctness.

**Dynamic semantics**

r[hir.primitive.slot] spec::hir::local_slot::{meaning, first, last, boundary, empty}
A raw local slot is in scope exactly below its context size.

```fren
pub mod spec
pub mod spec::hir

pub proc local_slot(size: Nat, index: Nat): (scoped?) {
    ensure meaning: scoped? iff index < size

    expect first: when size > 0 and index = 0, scoped?
    expect last: when size > 0 and index + 1 = size, scoped?
    expect boundary: when index = size, not scoped?
    expect empty: when size = 0, not scoped?
}
```

r[hir.primitive.identity] spec::hir::child_identity::{meaning, same, distinct_parent, distinct_name}
Two named child paths are equal exactly when both their canonical parents
and their final names are equal.

```fren
pub proc child_identity(parent: Int, name: Int, other_parent: Int, other_name: Int): (same?) {
    ensure meaning: same? iff parent = other_parent and name = other_name

    expect same: when parent = other_parent and name = other_name, same?
    expect distinct_parent: when parent != other_parent, not same?
    expect distinct_name: when name != other_name, not same?
}
```

Parent and name integers are equality atoms for this primitive table. They
are not hashes, serialized paths or a second item representation. In
particular, equal hash values do not establish equal parent identities.


## 5. Resolution cases and the typing boundary

These examples illustrate required name-resolution decisions.

| Source fragment in module `signals` | Required resolution result |
| --- | --- |
| `use_next(l: Light)` calls later `next(l)`; `Light` is declared last | Both type uses select `signals::Light`; the call selects `signals::next`. |
| `f(x: Int, y: Int)` has `let x := x + y in x + y` | Value indices `[1, 0]`; body indices `[0, 1]`. |
| `let fresh := fresh in fresh`, with no outer/item `fresh` | Failure on the value's `fresh`, not success from the body's binder. |
| `Light::Red` and `signals::Light::Red` | Same constructor identity. |
| `Signal::Red` alongside `Light::Red` | Different constructor identities. |
| Bare `Red`, with no declaration of that name | Unknown-name failure. |
| Two module items named `Light`, even of different kinds | Duplicate failure, no successful HIR. |
| Two parameters named `x`, or two `Red` variants in one enum | Duplicate failure. |
| `match l { Light::Red => (let z := 1 in z), Light::Green => z }` | Failure at the second arm's `z`; the first arm contributes no sibling slot. |

The Language chapter's unbound `y + 1` case must fail with `F0201` at `y`.
In contrast, this parsed input has no missing name:

```fren example
pub mod bad

pub enum Light { Red, Green }

pub fn f(l: Light): Int := l + 1  --~ error: type mismatch: expected `Int`, found `bad::Light`
```

Resolution succeeds with `l` at index 0 and result annotation `Int`.
Typing subsequently reports `F0304`; resolution does not reject the `+`
merely because it can see the enumeration annotation. This checked example
pins the established type diagnostic.
An empty or incomplete match can likewise resolve every written reference
before exhaustiveness fails. A fully resolved false expectation still needs
lowering and a solver verdict. No result here establishes those phases.

Implementation correspondence and proof coverage are recorded in the
[development coverage document](../../../docs/fren2-specification-coverage.md).
