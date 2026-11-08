# Types

A type describes which values an expression can produce. This chapter fixes
only the single-file [walking subset](../Compiler/AstAndParsing.md#walking-subset):
`Bool`, `Int`, payload-free enumerations and non-generic function signatures.
[THIR](../Compiler/Thir.md) specifies the next checker over resolved syntax.
Production walking typing is not implemented yet.

## Value types and signatures

An enumeration is nominal: its declaration determines its type, independently
of its variants' spellings. A function signature lists parameter types in
written order and one result type. Signatures are not value types in this
slice; functions cannot be stored in locals, passed as arguments or returned.

**Proof obligations**

r[types.walking.identity]
Value types are disjoint built-in `Bool`, built-in `Int`, and enumeration
types identified by their canonical `FrenBase.ItemId`.

r[types.walking.compatibility]
Two value types are compatible exactly when they are the same built-in or
are enumeration types with equal canonical identities.

r[types.walking.annotations]
Every parameter and function result annotation denotes its resolved value
type; an omitted parameter annotation supplies `Bool` only for a `?` name.

r[types.walking.suffix]
A parameter or let binder whose name ends in `?` has type `Bool`, including
when a parameter has an explicit annotation.

There are no coercions or integer subtypes here. `Light` and `Signal` remain
different even if both declare `Red`. A rendered path, final name or hash
cannot decide nominal equality. In particular, a built-in is not an enum
whose display happens to say `Int`. A written `b?: Int` resolves but fails
typing; the suffix does not overwrite the annotation.

## Expressions and local types

Write `Γ` for a nearest-first list of local value types, aligned with the
resolver's binder entries at that occurrence. `Γ[i]` is lookup at raw index
`i`, using the existing [binding context](../Compiler/Bindings.md#contexts-and-scope).

**Proof obligations**

r[types.expression.local]
A resolved local at index `i` has exactly the type stored at `Γ[i]`; absent
lookup is a static failure, not an inferred placeholder type.

r[types.expression.values]
Boolean literals have type `Bool`, decimal integer literals have type `Int`,
and a payload-free constructor value has its owning enumeration's type.

r[types.expression.items]
A module, enumeration declaration, global expectation or bare function is
not a value expression; a constructor is a value, not a function.

r[types.expression.call]
A call's resolved callee denotes a function, its argument count equals the
signature's parameter count, each argument is compatible with its positional
parameter type, and the call has the signature's result type.

r[types.expression.let]
A let value is typed in `Γ` and its body in that value's type prepended to
`Γ`; the let has the body's type.

r[types.expression.if]
An if condition has type `Bool`, both branches have compatible types, and
the if has that common type.

r[types.expression.match]
A match scrutinee has an enumeration type, each pattern is a constructor of
that enumeration, every arm body has one common compatible type, and the
match has that type.

r[types.expression.parentheses]
Parentheses preserve their enclosed expression's type.

No arm introduces a binder. Each arm starts with the incoming `Γ`, as do
siblings of other expressions. Both if branches and every written match
arm are checked even when an earlier condition or constructor would make
one unreachable. An empty match fails typing because this slice cannot
infer an arm result type. Duplicate and missing constructors are the
separate coverage obligation named in THIR; this typing relation alone
admits a nonempty incomplete or repeated-arm match with compatible bodies.
Calls through a local, enum, module, expectation or constructor fail even
when all arguments have types. No implicit application or constructor call
is inserted. All signatures are collected from resolved annotations before
bodies are checked, so a forward call has the same typing rule.

## Operators and conditions

These rules consume the AST's actual unary and binary operator variants.
Integer definedness, including division by zero, is separate from typing.

**Proof obligations**

r[types.operator.unary]
Unary minus takes `Int` and returns `Int`; `not` takes `Bool` and returns
`Bool`.

r[types.operator.binary]
The operand and result types of each binary operator follow this table.

| Operators | Left and right operands | Result |
| --- | --- | --- |
| `+`, `-`, `*`, `div`, `mod` | Both `Int` | `Int` |
| `<`, `<=`, `>`, `>=` | Both `Int` | `Bool` |
| `and`, `or`, `iff` | Both `Bool` | `Bool` |
| `=`, `!=` | Compatible value types | `Bool` |

r[types.declaration.result]
Every function body's type is compatible with its declared result type.

r[types.declaration.conditions]
Every global `assume` and `expect` body has type `Bool` in the expectation's
parameter context; member labels introduce no local slot.

The false S1 goal `next(l) != Light::Red` is well typed. Typing neither
rejects its falsity nor proves it true. The unknown `y` in `y + 1` already
fails resolution with `F0201`; it never reaches typing as a typed hole.

## Checked primitive decisions

The following contracts use a finite tag and integer equality atoms for
canonical enum identities. The atoms are not rendered paths or hashes.
They isolate raw compatibility and operator decisions, not a recursive IR,
lookup algorithm or walking typechecker. A result tag is constrained only
when the operands are accepted.

**Dynamic semantics**

r[types.primitive.compatibility] spec::types::compatible::{meaning, builtin, nominal, distinct, disjoint}
Compatibility compares tags and, only for nominal types, identity atoms.

```fren
pub mod spec
pub mod spec::types

pub enum ValueKind { Boolean, Integer, Nominal }
pub enum Unary { Negate, Not }
pub enum Binary { Add, Sub, Mul, Div, Mod, Lt, Le, Gt, Ge, And, Or, Iff, Eq, Ne }

pub proc compatible(left: ValueKind, right: ValueKind, left_id: Int, right_id: Int): (same?) {
    ensure meaning: same? iff left = right and (left != ValueKind::Nominal or left_id = right_id)

    expect builtin: when left = right and left != ValueKind::Nominal, same?
    expect nominal: when left = ValueKind::Nominal and right = left and left_id = right_id, same?
    expect distinct: when left = ValueKind::Nominal and right = left and left_id != right_id, not same?
    expect disjoint: when left != right, not same?
}
```

r[types.primitive.unary] spec::types::unary::{meaning, result_type, negate_bool, not_int}
A unary operator accepts exactly its table operand and preserves its tag.

```fren
pub proc unary(op: Unary, operand: ValueKind): (accepted?, result: ValueKind) {
    ensure meaning: accepted? iff (op = Unary::Negate and operand = ValueKind::Integer) or (op = Unary::Not and operand = ValueKind::Boolean)
    ensure result_type: when accepted?, result = operand

    expect negate_bool: when op = Unary::Negate and operand = ValueKind::Boolean, not accepted?
    expect not_int: when op = Unary::Not and operand = ValueKind::Integer, not accepted?
}
```

r[types.primitive.binary] spec::types::binary::{meaning, result_type, enum_add, mixed_equality, distinct_enums, same_enum}
A binary operator accepts exactly its table operands and returns its table
tag, including nominal identity comparison for equality.

```fren
pub proc binary(op: Binary, left: ValueKind, right: ValueKind, left_id: Int, right_id: Int): (
    accepted?,
    result: ValueKind,
) {
    ensure meaning: accepted? iff match op {
        Binary::Add => left = ValueKind::Integer and right = ValueKind::Integer,
        Binary::Sub => left = ValueKind::Integer and right = ValueKind::Integer,
        Binary::Mul => left = ValueKind::Integer and right = ValueKind::Integer,
        Binary::Div => left = ValueKind::Integer and right = ValueKind::Integer,
        Binary::Mod => left = ValueKind::Integer and right = ValueKind::Integer,
        Binary::Lt => left = ValueKind::Integer and right = ValueKind::Integer,
        Binary::Le => left = ValueKind::Integer and right = ValueKind::Integer,
        Binary::Gt => left = ValueKind::Integer and right = ValueKind::Integer,
        Binary::Ge => left = ValueKind::Integer and right = ValueKind::Integer,
        Binary::And => left = ValueKind::Boolean and right = ValueKind::Boolean,
        Binary::Or => left = ValueKind::Boolean and right = ValueKind::Boolean,
        Binary::Iff => left = ValueKind::Boolean and right = ValueKind::Boolean,
        Binary::Eq => left = right and (left != ValueKind::Nominal or left_id = right_id),
        Binary::Ne => left = right and (left != ValueKind::Nominal or left_id = right_id),
    }
    ensure result_type: when accepted?, result = match op {
        Binary::Add => ValueKind::Integer,
        Binary::Sub => ValueKind::Integer,
        Binary::Mul => ValueKind::Integer,
        Binary::Div => ValueKind::Integer,
        Binary::Mod => ValueKind::Integer,
        Binary::Lt => ValueKind::Boolean,
        Binary::Le => ValueKind::Boolean,
        Binary::Gt => ValueKind::Boolean,
        Binary::Ge => ValueKind::Boolean,
        Binary::And => ValueKind::Boolean,
        Binary::Or => ValueKind::Boolean,
        Binary::Iff => ValueKind::Boolean,
        Binary::Eq => ValueKind::Boolean,
        Binary::Ne => ValueKind::Boolean,
    }

    expect enum_add: when op = Binary::Add and left = ValueKind::Nominal, not accepted?
    expect mixed_equality: when op = Binary::Eq and left != right, not accepted?
    expect distinct_enums: when op = Binary::Ne and left = ValueKind::Nominal and right = left and left_id != right_id, not accepted?
    expect same_enum: when op = Binary::Eq and left = ValueKind::Nominal and right = left and left_id = right_id, accepted? and result = ValueKind::Boolean
}
```

Today's solver checks consequences of these independent contracts. There
is no production primitive or `impl` binding yet. The Lean wrapper proves
that actual binding-context membership gives a unique type and an in-scope
index; it does not prove traversal or whole-pass correctness.

## Diagnostic anchor and remaining evidence

This isolated example pins today's checker, not an implemented Fren2 pass.
Its `l` operand is on line 5, column 28 (zero-based byte span `[71, 72)`).

```fren example
pub mod bad

pub enum Light { Red, Green }

pub fn f(l: Light): Int := l + 1  --~ error: type mismatch: expected `Int`, found `bad::Light`
```

The required diagnostic is `F0304` at that operand, with canonical type
rendering `bad::Light`. The diagnostic uses `::`; `ItemId.render` is a
general debug display using dots and is not this type renderer.

- [ ] Bind the real compatibility and raw operator decisions to these
  contracts with genuine proofs after those functions exist, covering every
  AST operator and both nominal/builtin distinctions.
- [ ] Check the complete expression rules over the actual recursive checker,
  including rejected terms and context alignment, as specified in THIR.
- [ ] Restate recursive expression typing in Fren once Fren2 supports
  recursive expression datatypes and structurally recursive judgments over
  their ordered children; no Fren1 recursion extension is a prerequisite.
