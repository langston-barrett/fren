# Unused

The lints of the `unused` group find what is declared but never used.
One of them, `unfulfilled_lint_expectations`, finds an expectation that
no lint fulfils, and is described with [expecting
lints](../Lint.md#expecting-lints).

## Unused imports

A `use` is *used* if a path in the same file and module resolves through
it: the path's first segment resolves (see
[Resolution](../Lang/Modules.md#resolution)) to the item it imports by name,
or to a variant of the enumeration it opens. Paths in expressions, types,
calls, global expectations, claims and `#fren_check` count. The paths of
`use` declarations do not, since they are absolute.

A declaration written with `!` that [shadows](../Lang/Procedures.md#shadowing)
a name the `use` brings in counts as such a path, since the `!` depends on
the import: without the `use`, the `!` would hide nothing, and be an error.
So `use self::Shape::Square` with `in Square!: Int` is used, `fren fix`
keeps it, and a glob that [`glob_imports`](Style.md#glob-imports) narrows keeps
that name. A `!` that hides a variable or binder instead, which hides the
import too, does not count.

Only uses in the same file count, even though a module's imports are
visible in later files that enter it (see [Modules and
visibility](../Lang/Modules.md#across-files)): in Lean, each file is
elaborated without seeing the files that import it. A Markdown spec read
by `#fren_md` counts as a file of its own, as it does for the `fren`
command.

Opening the same enumeration twice in a module counts once (see
[Resolution](../Lang/Modules.md#resolution)), so only the first such `use` can
be used, and the others are unused. `lint::unused_import` decides whether
a `use` is unused:

```fren
pub mod lint

pub proc unused_import(
    glob?,               -- it is `use ...::*`
    n_paths: Nat,        -- paths in its file and module whose first segment resolves to a name it brings into scope
    first?,              -- no earlier `use` in its file and module opens the same enumeration
): (det unused?) {
    ensure rule: unused? iff (n_paths = 0 or (glob? and not first?))

    expect named_used: when not glob? and n_paths > 0, not unused?
    expect repeated_glob: when glob? and not first?, unused?
}
```

The message is reported at the `use`'s path at the end of the file, and
suggests removing the `use`.

## Unused variables

`unused_variables` reports a variable of a procedure that nothing in the
procedure, or of a global expectation, mentions, a parameter of a defined
function that neither its body nor its [contract](../Lang/Items.md#contracts)
mentions, a
[quantifier's](../Lang/Quantifiers.md) bound name that its body never
mentions, including a binder of a global expectation's leading `forall`,
and a name of a [`let` or `where`](../Lang/Let.md) clause that
neither its body nor a later definition of the clause mentions. An input
that nothing mentions does not affect the procedure, and an output that
nothing mentions can take any value. A quantifier over a name that its
body does not mention is its body, since every type has a value, and a
definition that nothing mentions has no effect.

A variable is mentioned by a path in one of the procedure's constraints,
or in an argument of one of its calls, whose only segment is the
variable's name and that resolves to it: the argument `x` in `call w :=
c(x)` mentions `x`, but in `match s { Shape::Circle(x!) => x > 0, _ =>
true }`, the `x` of the arm is the binder that
[shadows](../Lang/Procedures.md#shadowing) the variable, so it does not
mention the variable, and neither does the `x` of the body of `forall
(x!: Mode), x = Mode::Off`. A parameter of a defined function is
mentioned as a variable is. A path in a definition of a `let` or
`where` counts, whether or not the name defined is mentioned, and so does
a later definition's mention of an earlier name of its clause: in `let k
:= x, m := k + 1 in x`, `m` is reported, but `k` is not, since `m`'s
definition mentions it. A name of a clause, or a bound name, is mentioned as a
variable is, so in `let k := 1, k! := 2 in k`, the first `k` is reported.
Mentions elsewhere, such as
through a call of the procedure in another one, do not count: they
cannot constrain the variable. The variables of the procedure's own
calls are not reported, and neither are the variables of a procedure,
or of a global expectation, with a static error.

The message is reported at the variable's declaration, in the order of
declaration. A name of a clause, or a bound name, has no fix, as a
variable has none: it may be meant to be mentioned. A name that starts
with `_`, such as `_m` in `forall (_m: Mode), p?` or `_k` in `let _k := x
in y`, is reported like any other, as are the binders of global
expectations: unlike Rust, Fren has no `_` prefix that opts a name out,
but for a [closure's](../Lang/HigherOrder.md#arguments) parameter, below.

### Scopes

The lints of local definitions and quantifiers, here and in the chapters
after this one, read an expression through a model of its scopes: a tree
of a few nodes, `Node`, over a few names, `Local`, small enough for the
solver to check every claim about it over every tree. A node is a part of
the expression, such as an operator, an application, a clause's body or a
quantifier's body; its children are its parts; it *declares* the names
whose scope it is, as a quantifier's body declares its bound names and a
`match` arm's body its pattern's binders; and it *mentions* the names
written as paths of one segment directly in it. A node that is only a
name, `x`, mentions it and is a `path` of it.

```fren
pub enum Node { N0, N1, N2, N3 }
pub enum Local { A, B, C }

pub struct Tree {
    root: Node,
    children: Rel<Node, Node>,
    declares: Rel<Node, Local>,
    mentions: Rel<Node, Local>,
    paths: Rel<Node, Local>,
}
```

`lint::scope` computes, from a tree, its nodes, the names declared
anywhere in it, and its *free* names: those it mentions where neither the node of the mention nor one around
it declares them, which so mean what they mean outside
the tree. A mention below a node that declares its name means that
declaration, as the body's `x` does in `forall (x!: Mode), x = Mode::Off`:

```fren
pub proc scope(t: Tree): (det nodes: Set<Node>, det declared: Set<Local>, det free: Set<Local>) {
    -- The mentions in or below a node that declares their names.
    let hidden: Rel<Node, Local> := (t.children.closure.inverse join t.declares) union t.declares
    out nodes := t.children.closure.image({t.root}) union {t.root}
    out declared := t.declares.image(nodes)
    out free := (t.mentions minus hidden).image(nodes)

    expect mentioned: free subset t.mentions.range
    expect declared_hides: free inter t.declares.image({t.root}) = {}
}
```

A quantifier's bound name is unused if its body's tree does not have it
free. `lint::unused_bound` states this, for the bound names `names`. Its
definition reads its call, so the call is written first, against
[the order of members](Restriction.md#the-order-of-members), and the
procedure expects that lint:

```fren
set_option fren.lint.arbitrary_source_item_ordering "expect" in
pub proc unused_bound(names: Set<Local>, body: Tree): (det unused: Set<Local>) {
    call s := scope(body)

    out unused := names minus s.free

    expect shadowed: when body.children = {(Node::N0, Node::N1)} and body.root = Node::N0
        and body.declares = {(Node::N1, Local::A)} and body.mentions = {(Node::N1, Local::A)},
        unused = names
}
```

A [closure's](../Lang/HigherOrder.md#arguments) parameter that its body
does not mention is reported too, at the parameter: the closure's value
does not depend on it. Its function type fixes how many parameters it
has, so a closure that ignores an argument cannot drop the parameter, and
writes `_` in its place, which declares no name, or a name that starts
with `_`, such as `_count`, which says what the argument is; neither is
reported, as in Rust. `lint::unused_closure_params` states this, for the
closure's parameters `names`, of which those written with a name that
starts with `_` are `opted_out`:

```fren
-- Whether a closure's parameter written `name` is left out of
-- `unused_variables`: a name that starts with `_`. `_` alone declares no
-- name, so it is no parameter of `names`.
pub fn opted_out?(name: String) := name.starts_with?("_")

-- The name that a closure's parameter is written with.
fn written_name(Local): String

set_option fren.lint.arbitrary_source_item_ordering "expect" in
pub proc unused_closure_params(
    names: Set<Local>,
    opted_out: Set<Local>,           -- the parameters left out
    body: Tree,
): (det unused: Set<Local>) {
    call s := scope(body)

    -- The parameters left out are those written with a leading `_`.
    assume left_out: forall (x: Local), x in opted_out iff opted_out?(written_name(x))

    out unused := (names minus opted_out) minus s.free

    expect mentioned_kept: unused inter s.free = {}
}
```

The definitions of a clause are at positions, `DefIndex`, in order, each
declaring one name and mentioning the names that its expression has free;
the body mentions its own free names. A definition is used if the body
mentions its name and no later definition declares the name again, or a
later definition mentions it and none between them declares it again,
since a mention means the last declaration before it.
`lint::unused_definitions` states whether the definition at `k` is reported:

```fren
pub ordered enum DefIndex { P0, P1, P2, P3 }

pub proc unused_definitions(
    names: Rel<DefIndex, Local>,         -- the name each definition declares
    uses: Rel<DefIndex, Local>,          -- the names free in each definition's expression
    body: Set<Local>,                    -- the names free in the body
    k: DefIndex,
): (det unused?) {
    assume one_name: forall (p: DefIndex) (a b: Local), when (p, a) in names and (p, b) in names, a = b
    assume earlier: uses.domain subset names.domain

    ensure rule: unused? iff (k in names.domain and not (exists (x: Local),
        (k, x) in names and ((x in body and not (exists (m: DefIndex), k < m and (m, x) in names))
        or (exists (j: DefIndex), k < j and (j, x) in uses
        and not (exists (m: DefIndex), k < m < j and (m, x) in names)))))

    expect declared_only: when unused?, k in names.domain
    expect used_by_body: when names = {(DefIndex::P0, Local::A)} and body = {Local::A}, not unused?
    expect hidden_by_later: when names = {(DefIndex::P0, Local::A), (DefIndex::P1, Local::A)} and uses = {}
        and body = {Local::A} and k = DefIndex::P0, unused?
}
```

Both front ends compute these from their syntax trees, as their mentions
(`Reqs/Lang/Expressions#mentions`) are, and decide a clause's with
`clauseMentions`. The procedures of these chapters over trees are
`tested` against the ui tests of local definitions and quantifiers, not
proved against the code: the functions in `FrenCore` that decide the
lints take facts that each front end reads from its own syntax tree, not
a tree of this model, so no `impl` can relate the two until expressions
are modelled in Fren itself; and a tree's relations have too many values
for `decide`. Where a procedure is over finite data that the code takes
as it is, as [where a quantifier goes in
parentheses](Style/Let.md#operands-at-each-variant) is, it is proved.

## Dead code

`dead_code` reports a private enumeration, record, abstract type, type
alias, function or constant that no path in its file resolves to. A path
to a variant uses its enumeration, and so does a path through it, such as
`Mode::Heat`. A function is used by applying it, and a record, abstract
type or type alias by naming it, as a type, or, for a
record, in a record literal. As for [unused
imports](#unused-imports), paths in `use` declarations do not count, and
only uses in the same file count, even though a private item is visible
from its module's descendants, which later files may enter. Uses in Lean
code do not count either. A use counts even when it is in an item that is
itself unused.

Procedures and global expectations are never dead: each is a guarantee,
or a claim about guarantees, in its own right, and is checked and
[traced](../Trace.md) whether or not anything uses it. Nor is a
[trait](../Lang/Traits.md), whose expectations are checked whether or not
anything uses it, nor its methods and laws, which are its interface. `pub` items may be used
by other files. `lint::Named` is what a name can name, which the
[naming conventions](NonstandardStyle.md#naming-conventions) also use. `lint::dead_item`
states this:

```fren
pub enum Named {
    Module,
    Component,
    Variable,
    Field,
    Binder,
    Function,
    Instance,
    Constraint,
    Global,
    Enumeration,
    Variant,
    Record,
    AbstractType,
    TypeAlias,
    Constant,
    Trait,
    Law,
}

use self::Named::{AbstractType, Component, Constant, Enumeration, Function, Record, TypeAlias}

pub proc dead_item(
    what: Named,
    pub?,
    n_uses: Nat,         -- paths in its file that resolve to it, to one of its variants, or through it
): (det dead?) {
    ensure rule: dead? iff (what in {
        Enumeration,
        Record,
        AbstractType,
        TypeAlias,
        Function,
        Constant,
    } and not pub? and n_uses = 0)

    expect public_lives: when pub?, not dead?
    expect components_live: when what = Component, not dead?
}
```

The message is reported at the item's name, at the end of the file.

## Unused assumptions

`unused_assumption` reports an assumption of a procedure that mentions
only inputs, one or more, none of them used. An input is *used* when
something mentions it: a constraint other than an assumption, cover goals
among them, as for an [unused variable](#unused-variables); a definition;
an argument of one of the procedure's calls; or a
[call](../Lang/Calls.md) of the procedure in the same file, which gives
each of its parameters, and whose precondition check has the procedure's
assumptions as hypotheses. A global expectation that reads an input
through the call's binder, as `a.x` after `call a := p(...)`, uses it
through that call, since only a call binds a procedure. A
[refinement](../Lang/Refinement.md) whose abstraction is the procedure is
not a use: it checks only the abstraction's guarantees, and introduces
none of its assumptions, so removing one changes no verdict of the
refinement. An input is also used when another assumption mentions it and a
used variable, since the assumption constrains the two together, and so
on transitively: with `assume a: n > 0`, `assume b: m = 2 * n` and `ensure r:
y = m`, `m` is used, so `n` is, and without `a`, `y > 0` would not follow.
An uninterpreted function links assumptions in the same way as a
variable, through its values: it is *used* when one of the above applies
it, and an assumption that applies a used function is used, as is an
input it mentions. With `assume a: n = 3 and g(n) > 0` and `ensure r: y =
g(3)`, `a` says that `g(3) > 0`, so it is used. A constant's value and a
defined function's body apply no uninterpreted function, so they link
nothing. With these rules, removing a reported assumption together with
the reported assumptions it is linked to never makes a check fail. Alone,
it may: with `assume a: n >= 0 and n < q.len` and `assume b: q[n] > 0`,
both are reported, but `a` guards the index in `b`, so `b` without `a` is
not defined (`F0611`). So the message names the reported assumptions
linked to it. The variables `V` and functions of such a group are
mentioned by nothing else, so a check over the procedure is `forall U V,
A(V) and B(U) implies C(U)`, with `A` the group's assumptions, which is
`(exists V, A(V)) implies (forall U, B(U) implies C(U))`, for every
interpretation of the functions. Since `B` and `C` apply none of `A`'s
functions, `exists V, A(V)` can be made
to hold by changing only those, unless `A` is unsatisfiable, and then the
assumptions' satisfiability check already fails (`F0602`). The group
can also bound the size of an abstract type, as `k1 != k2` does, but that
is safe too: given a counterexample to a check without it, add a fresh
value to the type, extend each uninterpreted function to it, and give
`k1` an old value and `k2` the new one. Nothing else mentions them, so
the counterexample still fails, and the assumption now holds. An unused
input does not affect the procedure, as for an [unused variable](#unused-variables), but
`unused_variables` does not report it, since the assumption mentions it:
this is what is left after the last guarantee that used the input is
removed. As for [dead code](#dead-code), only the file's global
expectations and calls count. There is no fix: removing
the inputs would change the procedure's interface.
`lint::unused_assumption` states when it fires, over what each assumption
links, by its position: the variables of the procedure that it mentions
and the uninterpreted functions that it applies. `lint::reached` is the
assumptions that a set of links reaches: those that link one of them, and
those that share a link with one reached, transitively, through the
closure of the relation of sharing a link. An assumption is used when
what the procedure's members other than its assumptions mention or apply
reaches it, or what the file reads of the procedure does. The file uses
the procedure in calls and in `refines` claims; a call gives each input a
value, and its precondition check has the procedure's assumptions as
hypotheses ([calls](../Lang/Calls.md)), so where the file calls it, every
input is read. A `refines` claim checks only its abstraction's
guarantees, and introduces none of its assumptions
([refinement](../Lang/Refinement.md)), so it reads no input:

```fren
-- What links assumptions: a variable of the procedure, or an uninterpreted
-- function, by its name.
pub enum Link { Var(String), Fn(String) }

-- The assumptions, by their positions, that `used` reaches.
set_option fren.lint.undecidable "allow" in
pub fn reached(links: Rel<Int, Link>, used: Set<Link>): Set<Int> :=
    direct union (links join links.inverse).closure.image(direct)
    where direct := links.inverse.image(used)

-- How the file uses the procedure: in a call, or as the abstraction of a
-- `refines` claim.
pub enum ProcUse { Call, Refines }

-- Whether a use checks the procedure's assumptions: a call's precondition
-- check has them as hypotheses, and a `refines` claim introduces none.
pub fn checks_assumptions?(u: ProcUse) := u = ProcUse::Call

-- Whether the file reads every input of the procedure: where a use checks
-- its assumptions.
pub fn reads_inputs?(uses: Set<ProcUse>) := exists (u: ProcUse), u in uses and checks_assumptions?(u)

set_option fren.lint.undecidable "allow" in
pub proc unused_assumption(
    links: Rel<Int, Link>,       -- what each assumption of the procedure links, by its position
    inputs: Set<Link>,           -- the procedure's inputs, each a `Var`
    mentioned: Set<Link>,        -- what its members other than its assumptions mention or apply
    uses: Set<ProcUse>,          -- how the file uses the procedure
    k: Int,                      -- the position of the assumption
): (det fires?) {
    ensure rule: fires? iff ((exists (x: String), (k, Link::Var(x)) in links)
        and (forall (x: String), when (k, Link::Var(x)) in links, Link::Var(x) in inputs)
        and not k in reached(
            links,
            mentioned union (if reads_inputs?(uses) then inputs else {})
        ))
    -- A `refines` claim alone reads no input; a call reads them all.
    expect refines_reads_nothing: when uses = {ProcUse::Refines}, not reads_inputs?(uses)
    expect call_reads: when ProcUse::Call in uses, reads_inputs?(uses)
}
```

Both front ends decide in two steps: with what the procedure's members
mention, where they elaborate it, and with the inputs that the file reads,
among the assumptions that the first step leaves, at the end of the file.
That is the same as one step with both, since each assumption that the
first step leaves links an input.

The message is reported at the assumption's name, at the end of the
file.

## Unused lint settings

`unused_lint_setting` reports a [lint setting](../Lint.md#setting-levels),
a `set_option` of a lint or a group, that is in effect at no item for any
of the lints it sets. A setting is in effect from where it is to the end
of the file, or with `in`, in its item, except where a later setting
replaces it for a lint. So a setting has no effect when, before any item:

- a later setting of the same lint or group replaces it, as in `set_option
  L "allow" in set_option L "warn" in item`, where the inner one wins, or
  in two settings at the top level with no item between them;
- a setting of its group replaces it, since that sets each of its lints;
- the file ends, as for a setting after the last item.

A setting of a lint after one of its group, as `set_option
fren.lint.pedantic "warn"` and then `set_option fren.lint.match_same_arms
"allow"`, is not reported: the group's is still in effect for its other
lints. A check, such as `#fren_check`, is not an item here, since no lint
is about it. A setting of `unfulfilled_lint_expectations` or
`unused_lint_setting` is also in effect at a later setting, whose messages
take their level from it, and so is a `forbid`, which decides whether a
later setting is accepted. A setting to `expect` is not reported: if
nothing fulfils it, `unfulfilled_lint_expectations` reports it.

A replaced `deny` is the most dangerous case, since the lint it denies is
then not an error after all: the message says which setting undoes it.
The message is reported at the setting, at the end of the file. The fix
removes it, as the [fix](../Lint.md#fixing-lints) of
`unfulfilled_lint_expectations` does: since it is in effect at no item,
every item keeps its levels, and since it is in effect at no setting
either, every setting keeps its messages and is accepted or not as
before. `lint::unused_lint_setting` states when it fires:

```fren
pub proc unused_lint_setting(
    n_places: Nat,       -- items and later settings where it is in effect for a lint it sets
    expect?,             -- it is to `expect`
): (det fires?) {
    ensure rule: fires? iff (n_places = 0 and not expect?)
}
```
