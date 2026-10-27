# Global expectations

A procedure's [expectation](Procedures.md#members) is a claim about each of
its behaviours separately. A global expectation is a claim about procedures
as a whole: it can relate several behaviours of one procedure, or behaviours
of different procedures. It is written like a procedure, with parameters
and a block, and relates the procedures by [calling](Calls.md) them:

```
expectation := "expect" IDENT"(" [variable ("," variable)* [","]] ")" "{" member* "}"
             | "expect" IDENT ":" top
```

`expect n(x: T, ...) { ... }` claims that for all values of its
parameters, and all behaviours of the procedures it calls, its
assumptions imply each of its expectations. Its parameters are
quantified, as a procedure's inputs are: they may have any type, unbounded
ones included, and each is shown in a counterexample. Its block has the
members that a claim needs, and no others:

- `assume n: e` restricts the parameters, as a procedure's assumption
  does;
- `call w := p(...)` relates the procedure `p`, whose variables it reads
  as `w.x`, as a procedure's call does;
- `expect n: e` is a claim, and `cover n: e` a scenario that must be
  possible, as in a procedure;
- `let x: T := e` names an expression, and `use` imports names for the
  block, as in a procedure.

A global expectation constrains nothing, so it has no results, and no
`exists` or `ensure` member, nor an `out` member, which defines a result;
and nothing is determined by it, so no member is `det`. Each of these is
an error (`F0417`). It is an item, named like a procedure, but it is not
one: nothing can call it, and a call of it is an error, as a call of any
item that is not a procedure is. Its parameters, calls, constraints and
`let` variables share one namespace, as a procedure's do, and may
[shadow](Procedures.md#shadowing) the constants, functions and variants
of its module, written with `!`. Each procedure it calls must be declared,
and visible, before it.

```fren
pub mod lang
```

`lang::block_member` states which members a global expectation's block
accepts, and a result in its signature, which it does not:

```fren
pub enum BlockMember { Result, Exists, Let, Define, Assume, Ensure, Expect, Cover, Call, Use }

pub proc block_member(
    member: BlockMember,
    det?,                -- written with `det`
): (det accepted?) {
    use self::BlockMember::{Assume, Call, Cover, Define, Ensure, Exists, Expect, Let, Result, Use}

    ensure rule: accepted? iff (not det? and member in {Let, Assume, Expect, Cover, Call, Use})

    expect claims: when member in {Expect, Cover} and not det?, accepted?
    expect constrains_nothing: when member in {Result, Exists, Define, Ensure}, not accepted?
    expect determines_nothing: when det?, not accepted?
}
```

## The short form

`expect n: e`, without parameters or a block, is a claim about
[constants](Items.md#constants), such as `expect sane: MIN_TEMP <
MAX_TEMP`. It means what `expect n() { expect n: e }` means, and is
checked so, but it is reported by its own name, `n`, as a constraint of
its module is. `e` may end with a [`where` clause](Let.md), and may be a
[quantifier](Quantifiers.md#global-expectations) over values: `expect n:
forall (m: Method), E` claims `E` of every value `m` of `Method`.

## Example

`band` classifies a temperature (see [Calls](Calls.md#example)):

```
pub proc band(temp: Int, target: Int): (too_cold?, too_hot?) {
    ensure cold: too_cold? iff temp < target - 2
    ensure hot: too_hot? iff temp > target + 2
}

expect colder_is_cold(temp1: Int, temp2: Int, target: Int) {
    assume sorted: temp1 <= temp2

    call a := band(temp1, target)
    call b := band(temp2, target)

    expect colder: when b.too_cold?, a.too_cold?
}
```

`colder_is_cold` says that `band` is monotone: for the same target, a lower
temperature is at least as cold. It relates two behaviours of `band`, so it
cannot be an expectation of `band` itself. The calls share the parameter
`target`, so the claim is about two behaviours with the same target, and
the assumption says which temperatures it is about.

A global expectation can also say that two procedures agree. If
`fast_band` is meant to classify temperatures as `band` does:

```
expect same_band(temp: Int, target: Int) {
    call f := fast_band(temp, target)
    call b := band(temp, target)

    expect same: (f.too_cold? iff b.too_cold?) and (f.too_hot? iff b.too_hot?)
}
```

## Meaning

A global expectation means what its expectations mean in a procedure with
its parameters as inputs, its assumptions, its calls and its definitions,
and no outputs or guarantees (see [Procedures](Procedures.md#meaning)). With
`i` its parameters, `y` its calls' variables, `A(i)` its assumptions and
`I(i, y)` its calls' constraints, each expectation `E` holds if

  ∀ i y. A(i) ∧ I(i, y) ⇒ E(i, y)

with its definitions substituted. The assumptions of each call's
procedure are obligations on the call's arguments, as in any procedure,
which the global expectation's assumptions must discharge: the [call
check](../Check.md#call-assumptions) confirms that they do. So a global
expectation states its domain: the inputs it is about are those that its
assumptions admit, and each call is one that its procedure accepts.

All the calls share one [interpretation](Procedures.md#interpretations)
of the spec's abstract types and functions, and the global expectation
must hold under every interpretation. Its parameters are universally
quantified at the top of each query, as a procedure's inputs are, so no
bound on their types is needed.

A global expectation constrains nothing. It is not a procedure, and has no
[evidence](../Trace.md). The [checks](../Check.md#global-expectations)
confirm it: they are a procedure's, but for those of what it does not
have. Its assumptions must be satisfiable, as a procedure's must, or every
expectation would hold vacuously: the realizability check reports
contradictory ones (`F0602`).

## Migration

Global expectations were written with a leading `forall` before, whose
binders ranged over procedures' behaviours as well as over values: `expect
n: forall (a b: c) (m: M), E`. Each binder over a procedure stood for a
behaviour of it with inputs of its own, and the procedure's assumptions
were hypotheses. A binder over a procedure is an error now (`F0416`),
whose fix writes the global expectation with a block, and means what it
did:

- each binder `a: c` over a procedure becomes a parameter for each
  parameter `x` of `c`, named `a_x` and of `x`'s type as `c` writes it,
  and the call `call a := c(a_x, ...)`;
- each binder `m: M` over values becomes the parameter `m: M`;
- each assumption `s` of `c` becomes, for each binder `a` of `c`, the
  assumption `assume a_s: S`, where `S` is `s` as `c` writes it, with each
  parameter `x` of `c` written `a_x`;
- `E`, with any `where` clause, becomes the block's one expectation,
  `expect n: E`, which reads `a`'s variables as `a.x`, as before.

The parameters come in the order of the binders, and each binder's in the
order of its procedure's parameters; then the block has the procedures'
imports, the assumptions, the calls and the expectation, one to a line, with the comments of the
expectation's lines. Merging parameters that a condition ties together,
such as `a_target` and `b_target` under `when a.target = b.target`, is
left to the author.

The meaning is unchanged: the call `a` binds `a.x` to `a_x`, so the
parameters stand for the behaviour's inputs, which were quantified before;
the assumptions copy the procedure's, which were hypotheses before, and so
discharge the new call checks; and the types copied with the parameters
bring what they brought. The error is reported once each binder's type is
resolved, as a procedure or a type, so it is a static error, as an
[instance](Procedures.md#migration) is; `fren fix` makes its fix in the
rounds that need name resolution (see [Migrations](../Lint.md#migrations)).
A leading `forall` with binders over values alone is no error: it is the
short form's quantifier.

The fix copies text, so it is offered only where what it copies means the
same at the global expectation as in the procedure. What a text reads is
taken from its identifiers, as the lexer reads them, outside comments and
strings, each by its first component, but for those after a `.` or a
`::`, which name fields, methods and the items of paths; and what it
declares with `!`, from those written so. Both front ends read the texts
so, with one function, `Fren.Core.copiedOf`. The fix copies the `use`
members of each procedure with assumptions too, once each, before the
assumptions, since they may read the names that those import.

`lang::callee_fix` states, of one binder's procedure, whether its text can
be copied, and if not, why:

- it must be in the global expectation's module, since elsewhere its
  names may mean something else;
- its assumptions must read none of its own variables or calls but its
  parameters, such as a `let` that they may read, which the global
  expectation does not have, and must declare with `!` no name that a
  parameter has, whose uses would not be the parameter's;
- the names that its types and assumptions read, but its parameters,
  which the fix renames, must not be among those that the block declares
  as values, its parameters and its calls, which would hide them: in
  `forall (b: band) (LIM!: Int)`, a parameter `LIM` would hide the
  constant `LIM` that `band`'s assumption reads.

A text that declares with `!` a variable of the procedure's own, other
than a parameter, reads it too, so it is not copied either: at the global
expectation, the `!` would shadow nothing.

```fren
pub struct Copied {
    names: Set<Id>,      -- the identifiers it reads, each by its first component
    bangs: Set<Id>,      -- the names it declares with `!`
}

pub struct Callee {
    module: Id,          -- the procedure's module
    params: Set<Id>,     -- its parameters
    others: Set<Id>,     -- its other variables and its calls
    types: Copied,       -- what its parameters' types read
    assumes: Copied,     -- what its assumptions read and declare
}

pub enum CalleeFix { Fixable, OtherModule, NotClosed, Captured }

set_option fren.lint.undecidable "allow" in
set_option fren.evidence "tested" in
pub proc callee_fix(
    module: Id,          -- the global expectation's module
    block: Set<Id>,      -- the values that its block would declare: its parameters and calls
    callee: Callee,
): (det fix: CalleeFix) {
    -- A procedure's names are distinct.
    assume apart: forall (x: Id), when x in callee.params, not x in callee.others

    ensure rule: fix = (if callee.module != module then CalleeFix::OtherModule
        else if (exists (x: Id), x in callee.assumes.names and x in callee.others)
            or (exists (x: Id), x in callee.assumes.bangs and x in callee.params)
        then CalleeFix::NotClosed
        else if (exists (x: Id), (x in callee.types.names or x in callee.assumes.names) and not x in callee.params
            and x in block)
        then CalleeFix::Captured
        else CalleeFix::Fixable)

    expect elsewhere: when callee.module != module, fix = CalleeFix::OtherModule
    expect only_parameters: when callee.module = module and callee.assumes.names subset callee.params
        and callee.types.names subset callee.params and callee.assumes.bangs = {}, fix = CalleeFix::Fixable
}
```

`lang::migrated_param` names what the fix declares for one parameter, or
one assumption, `x` of the procedure of a binder `w`, and states when the
name is fresh: when it is not among `taken`, the other names that the
block declares and, for a parameter, the names in scope that it would
hide. The fix is offered when every binder's procedure is fixable and
every name it declares is fresh: the binders' names, the parameters, the
assumptions and the expectation, which share the block's namespace.
Otherwise the error has no fix, and its note says why: the first binder
whose procedure is not fixable, with the reason, or the first name that
is not fresh. `Fren.Core.globalFix` decides this for both front ends.

```fren
pub proc migrated_param(
    binder: Id,          -- the binder, without its `!`
    param: Id,           -- the procedure's parameter or assumption
    taken: Set<Id>,      -- the names it must not be
): (det name: Id, det fresh?) {
    out name := binder ++ "_" ++ param

    ensure rule: fresh? iff not name in taken

    expect untaken: when taken = {}, fresh?
}
```
