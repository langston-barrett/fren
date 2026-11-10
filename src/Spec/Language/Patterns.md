# Patterns and matching

A match selects one of its arms by the constructor of the value it matches.
This chapter defines the patterns of the Core, how an arm is selected, and the
static checks that a match has an arm for every constructor of its
enumeration and no arm written twice for one constructor.
[Resolution](NamesAndScope.md) supplies identities, types and the Core's
forms, and turns a written pattern into a constructor identity;
[Core typing](Types.md) supplies the typing of a match; the [syntax](../Compiler/AstAndParsing.md#source-forms) admits only
patterns that name a variant. A later compiler chapter owns the translation
of a match into decision code. The [THIR](../Compiler/Thir.md#coverage-correspondence),
[evaluator](../Compiler/Evaluator.md#arm-selection),
[SMT](../Compiler/Smt.md#9-arm-selection-in-confirmation) and
[match compilation](../Compiler/MatchCompilation.md) chapters relate the
production code to the definitions here.

## Overview

The chapter's judgments, and the Fren definitions that state them:

| Judgment | Meaning | Fren |
| --- | --- | --- |
| `Σ ⊢ c pat a` | the pattern c is a constructor of the enumeration a | `entry` (checked by `arm_patterns?`) |
| `arms ▷ c ⇒ e` | the arms select the arm with body e for constructor c | `select` |
| `Σ ⊢ arms cover a` | every constructor of a has at least one arm | `covered?` |
| `arms reachable` | no arm repeats the pattern of an earlier arm | `reachable?` |
| `Σ; Γ ⊢ match s { arms } : τ admitted` | the match is typed, its arms cover and none is repeated | `match_admitted?` |
| `Σ; Γ ⊢ e : τ admitted` | e is typed and every match in it is admitted | `derivation_admitted?` |
| `⊢ (Σ, ds) admitted` | the program is typed and every match in it is admitted | `prog_admitted?` |

In outline, `select` gives, for a constructor c, the first arm written for c.
The [dynamic semantics](DynamicSemantics.md#r-dynamics.match.selection) is
stated for matches with
[distinct arms](StaticSemantics.md#r-statics.match.distinct), where the
arm of c is unique and is the one that `select` gives. Its
[table evaluator](DynamicSemantics.md#r-dynamics.table.differences) also
gives a value to a typed match with a repeated arm, and runs the last arm
written for c, so the two [agree](#r-patterns.matching.dynamics)
when no arm is repeated and can disagree on a typed match whose scrutinee's
constructor has a repeated arm. Such a match is a static error, so the
disagreement is reached by no admitted program; that the two functions
differ there is open. A match has two checks, once the typing rules have admitted the patterns of
the arms: every constructor of the scrutinee's enumeration is the pattern of
at least one arm, which is the
[coverage of the static semantics](StaticSemantics.md#r-statics.definedness.coverage),
and no arm repeats the pattern of an earlier arm, which is an error of its
own. Together they say that every constructor is the pattern of exactly one
arm:

```text
  select     : Arms × Item → Option Arm
  covered?   : Symb × Item × Arms → Bool
  reachable? : Arms → Bool

  select(arms, c) = the first arm with pattern c, if there is one
  reachable?(arms)  iff  no arm has the pattern of an earlier arm
  covered?(Σ, a, arms)  iff  every constructor of a selects an arm
  admitted               iff  typed, covered?(Σ, a, arms) and reachable?(arms)
```

The laws are the properties [determinism of selection](#r-patterns.matching.selection-laws),
[order independence](#r-patterns.matching.order-free),
[soundness and completeness of the checks](#r-patterns.coverage.characterized),
[typing of the selected arm](#r-patterns.matching.preservation),
[selection by an admitted match](#r-patterns.matching.admitted-selects) and
[admission of a nested match](#r-patterns.admission.layer). Coverage is
decidable: the [check](#r-patterns.coverage.checker) is a function that
recurses over finite lists, because patterns carry no payload and the
inventory of an enumeration is finite.

## Patterns

r[patterns.syntax.form] spec::patterns::Pattern
A pattern is a constructor: the identity that resolution gives to a written
qualified variant path. A pattern binds no local and takes no payload, and
the grammar has no wildcard, literal, alternative or nested pattern, so
that a written pattern and its constructor identity are the same thing. The
[arm form](NamesAndScope.md#r-names.core.syntax) of the Core, `ArmF`, pairs a
pattern with a body.

```text
  p  ::=  a::c         a variant path, resolved to the identity of c
  arm ::=  p ⇒ e
```

```fren
pub mod spec
pub mod spec::patterns

use spec::names::{ArmF, CoreF, Ctx, ItemId, ItemKind, Symb, Ty, entry, length, member?, symb_ok?}

use spec::surface::Snoc

use spec::types::{
    Decl,
    Row,
    Typing,
    annotate,
    arm_bodies?,
    arm_patterns?,
    decl_ok?,
    derivation?,
    match_rule?,
    prog_ok?,
}

use spec::surface::Snoc::{Empty, Extend}

pub type Pattern := ItemId
```

r[patterns.typing.pattern]
A pattern has the enumeration that owns it as its type. The rule that types
a match requires each arm's pattern to have the type of the scrutinee, which
the [match typing](Types.md#r-types.expression.match) states as
`arm_patterns?`. This chapter has no pattern judgment of its own: its
properties take that typing as a hypothesis.

```text
  Σ(c) = constructor of a
  ───────────────────────
  Σ ⊢ c pat a
```

## Matching

r[patterns.matching.select] spec::patterns::{select, occurrences}
The arms of a match are a snoc sequence in written order, so the newest entry
is the last arm written. For a constructor c, `select` gives the first arm
written for c, if there is one: it consults the earlier arms before the
newest. This is the selection of this chapter and of the production
`FrenHirToThir.selectArm`; it is proved to be the selection of the
[dynamic semantics' table evaluator](#r-patterns.matching.dynamics) when no arm is repeated,
and can differ from it for a constructor that has a repeated arm. `occurrences` counts the arms written for c.

```text
  arms = c₀ ⇒ e₀ | … | cₘ ⇒ eₘ     k least with cₖ = c
  ─────────────────────────────────────────────────────
  arms ▷ c ⇒ eₖ
```

```fren
pub fn select<E>(arms: Snoc<ArmF<E>>, constructor: ItemId): Option<ArmF<E>> := match arms {
    Empty => Option::None,
    Extend(earlier, arm) => match select(earlier, constructor) {
        Option::Some(found) => Option::Some(found),
        Option::None => if arm.constructor = constructor then Option::Some(arm) else Option::None,
    },
}

pub fn occurrences<E>(arms: Snoc<ArmF<E>>, constructor: ItemId): Int := match arms {
    Empty => 0,
    Extend(earlier, arm) =>
        occurrences(earlier, constructor) + (if arm.constructor = constructor then 1 else 0),
}
```

r[patterns.matching.selection-laws] spec::patterns::selection_laws::{sound, complete, first_wins}
Selection is a function, so a value selects at most one arm. It selects an arm
exactly when some arm is written for the value's constructor, and that arm has
the constructor as its pattern. An earlier arm for the constructor wins over a
later one.

```fren
set_option fren.evidence "random" in
pub proc selection_laws(
    arms: Snoc<ArmF<Typing>>,
    earlier: Snoc<ArmF<Typing>>,
    last: ArmF<Typing>,
    constructor: ItemId,
    found: ArmF<Typing>,
): (holds?) {
    ensure output: holds?
    ensure sound: when select(arms, constructor) = Option::Some(found),
        found.constructor = constructor and occurrences(arms, constructor) > 0
    ensure complete: when occurrences(arms, constructor) > 0,
        select(arms, constructor) is Option::Some(_)
    ensure first_wins: when occurrences(earlier, constructor) > 0,
        select(Extend(earlier, last), constructor) = select(earlier, constructor)
}
```

r[patterns.matching.order-free] spec::patterns::arm_order::swap
Two arms with different patterns can be written in either order: swapping
them changes no selection. The property is stated for the two newest arms of
a match, which are the arms that selection consults last.

```fren
set_option fren.evidence "random" in
pub proc arm_order(
    earlier: Snoc<ArmF<Typing>>,
    first: ArmF<Typing>,
    second: ArmF<Typing>,
    constructor: ItemId,
): (holds?) {
    ensure output: holds?
    ensure swap: when first.constructor != second.constructor,
        select(Extend(Extend(earlier, first), second), constructor)
        = select(Extend(Extend(earlier, second), first), constructor)
}
```

## Coverage

r[patterns.coverage.covered] spec::patterns::{inventory, each_covered?, covered?}
Arms *cover* an enumeration when each constructor that Σ lists for it is the
pattern of at least one arm, as the
[static semantics](StaticSemantics.md#r-statics.definedness.coverage)
defines coverage. A constructor with no arm is *missing*. A constructor with
several arms is *repeated*, which coverage allows and a
[separate rule](#r-patterns.coverage.repeated) rejects. The *inventory* of
an owner is the constructors that Σ lists for it, and an owner that Σ does
not bind as an enumeration has none and is not covered.

```text
  Σ(a) = enumeration listing c₀, …, cₙ
  occurrences(arms, cₖ) ≥ 1   (each k)
  ────────────────────────────────────
  Σ ⊢ arms cover a
```

```fren
pub fn inventory(symb: Symb, owner: ItemId): Snoc<ItemId> := match entry(symb, owner) {
    Option::Some(ItemKind::Enumeration(constructors)) => constructors,
    _ => Empty,
}

pub fn each_covered?<E>(constructors: Snoc<ItemId>, arms: Snoc<ArmF<E>>) := match constructors {
    Empty => true,
    Extend(earlier, constructor) =>
        occurrences(arms, constructor) > 0 and each_covered?(earlier, arms),
}

pub fn covered?<E>(symb: Symb, owner: ItemId, arms: Snoc<ArmF<E>>) := match entry(symb, owner) {
    Option::Some(ItemKind::Enumeration(constructors)) => each_covered?(constructors, arms),
    _ => false,
}
```

r[patterns.coverage.checker] spec::patterns::{uncovered, repeats}
The checks compute the two lists that a rejected match reports. `uncovered`
lists the inventory's constructors that no arm names, in inventory order.
`repeats` lists the pattern of each arm that an earlier arm already names, in
written order.

```fren
pub fn uncovered<E>(constructors: Snoc<ItemId>, arms: Snoc<ArmF<E>>): Snoc<ItemId> :=
    match constructors {
        Empty => Empty,
        Extend(earlier, constructor) =>
            if occurrences(arms, constructor) = 0
            then Extend(uncovered(earlier, arms), constructor)
            else uncovered(earlier, arms),
    }

pub fn repeats<E>(arms: Snoc<ArmF<E>>): Snoc<ItemId> := match arms {
    Empty => Empty,
    Extend(earlier, arm) =>
        if occurrences(earlier, arm.constructor) > 0
        then Extend(repeats(earlier), arm.constructor)
        else repeats(earlier),
}
```

r[patterns.coverage.reachable] spec::patterns::{first_index, reachable?, reachability::agrees}
An arm is *reachable* when it is the first arm written for its pattern, that
is, when its position, counting from 0 at the oldest arm, is the least
position of an arm with that pattern; otherwise no value selects it, because
selection takes the first. `first_index` computes the least position of an
arm for a constructor, and `reachable?` says that every arm is at the least
position of its own pattern. This is stated by position, not through the
check: the check `repeats` is empty exactly when every arm is reachable.

```text
  arms = c₀ ⇒ e₀ | … | cₘ ⇒ eₘ     k least with cₖ = cᵢ   (each i, with k = i)
  ─────────────────────────────────────────────────────────────────────────
  arms reachable
```

```fren
pub fn first_index<E>(arms: Snoc<ArmF<E>>, constructor: ItemId): Option<Int> := match arms {
    Empty => Option::None,
    Extend(earlier, arm) => match first_index(earlier, constructor) {
        Option::Some(index) => Option::Some(index),
        Option::None =>
            if arm.constructor = constructor then Option::Some(length(earlier)) else Option::None,
    },
}

pub fn reachable?<E>(arms: Snoc<ArmF<E>>) := match arms {
    Empty => true,
    Extend(earlier, arm) =>
        first_index(Extend(earlier, arm), arm.constructor) = Option::Some(length(earlier))
        and reachable?(earlier),
}

set_option fren.evidence "random" in
pub proc reachability(arms: Snoc<ArmF<Typing>>): (holds?) {
    ensure output: holds?
    ensure agrees: repeats(arms) = Empty iff reachable?(arms)
}
```

r[patterns.coverage.repeated]
A match with a repeated arm is rejected: an arm that is not reachable is a
static error, whether or not the arms cover the scrutinee's enumeration.
This error is separate from coverage, which a match with a repeated arm can
still meet. The static semantics states the same rule as
[distinct arms](StaticSemantics.md#r-statics.match.distinct), with a
definition of its own, `arms_distinct?`; that it agrees with `reachable?`
is not proved. This chapter
states the rule as a premise of [admission](#r-patterns.coverage.admitted).

r[patterns.coverage.diagnostic]
A match that does not cover its scrutinee's enumeration is rejected with an
error that names the enumeration and the missing constructors in declaration
order (`uncovered`), and a match with a repeated arm is rejected with an
error for the repeated patterns in written order (`repeats`).
A match on a type that is not an enumeration has no coverage error here: its
owner has no constructors to cover, and the typing rules reject it. The error
has no catalogue code yet, and its rendering and its source position are not
specified here; the [THIR chapter](../Compiler/Thir.md#coverage-correspondence)
relates today's checks to the two lists.

r[patterns.coverage.admitted] spec::patterns::match_admitted?
A match is admitted when it is typed by the [match rule](Types.md#r-types.expression.match),
its arms cover the scrutinee's enumeration, and none of its arms is repeated.
Typing depends on neither check, as
[stated for typing](Types.md#r-types.judgment.coverage-separate),
so an unadmitted match can still be typed.

```text
  Σ; Γ ⊢ match s { arms } : τ   Σ; Γ ⊢ s : Nominal(a)   Σ ⊢ arms cover a   arms reachable
  ──────────────────────────────────────────────────────────────────────────────────────
  Σ; Γ ⊢ match s { arms } : τ admitted
```

```fren
pub fn match_admitted?(symb: Symb, ctx: Ctx, scrutinee: Typing, arms: Snoc<ArmF<Typing>>, ty: Ty) :=
    match_rule?(symb, ctx, scrutinee, arms, ty)
    and match scrutinee.ty {
        Ty::Nominal(owner) => covered?(symb, owner, arms),
        _ => false,
    }
    and reachable?(arms)
```

r[patterns.coverage.characterized] spec::patterns::{inventory_selected?, targets_listed?, exactly_once?, coverage_characterized::{listed, characterized, agrees, once}}
The checks are sound and complete for the statement that a match selects an
arm for every constructor and has no unreachable arm. Take a well-formed Σ
and an enumeration with constructors c₀, …, cₙ. The arms cover the
enumeration exactly when each cₖ selects an arm. They cover it with every
arm reachable exactly when `uncovered` and `repeats` are both empty. When
the patterns of the arms are all constructors of the enumeration, as typing
guarantees, that is exactly when each cₖ is the pattern of exactly one arm,
which `exactly_once?` states. Since `covered?` and `reachable?` are
functions, both checks are decidable.

```fren
pub fn inventory_selected?<E>(constructors: Snoc<ItemId>, arms: Snoc<ArmF<E>>) :=
    match constructors {
        Empty => true,
        Extend(earlier, constructor) =>
            select(arms, constructor) is Option::Some(_)
            and inventory_selected?(earlier, arms),
    }

pub fn targets_listed?<E>(constructors: Snoc<ItemId>, arms: Snoc<ArmF<E>>) := match arms {
    Empty => true,
    Extend(earlier, arm) =>
        member?(constructors, arm.constructor) and targets_listed?(constructors, earlier),
}

pub fn exactly_once?<E>(constructors: Snoc<ItemId>, arms: Snoc<ArmF<E>>) := match constructors {
    Empty => true,
    Extend(earlier, constructor) =>
        occurrences(arms, constructor) = 1 and exactly_once?(earlier, arms),
}

set_option fren.evidence "random" in
pub proc coverage_characterized(
    symb: Symb,
    owner: ItemId,
    constructors: Snoc<ItemId>,
    arms: Snoc<ArmF<Typing>>,
): (holds?) {
    ensure output: holds?
    ensure listed: when symb_ok?(symb) and arm_patterns?(symb, arms, owner)
        and entry(symb, owner) = Option::Some(ItemKind::Enumeration(constructors)),
        targets_listed?(constructors, arms)
    ensure characterized: when entry(symb, owner) = Option::Some(ItemKind::Enumeration(constructors)),
        covered?(symb, owner, arms) iff inventory_selected?(constructors, arms)
    ensure agrees: when entry(symb, owner) = Option::Some(ItemKind::Enumeration(constructors)),
        covered?(symb, owner, arms) and reachable?(arms)
        iff uncovered(constructors, arms) = Empty and repeats(arms) = Empty
    ensure once: when targets_listed?(constructors, arms)
        and entry(symb, owner) = Option::Some(ItemKind::Enumeration(constructors)),
        covered?(symb, owner, arms) and reachable?(arms) iff exactly_once?(constructors, arms)
}
```

r[patterns.coverage.empty] spec::patterns::empty_enumeration::unadmitted
A well-formed Σ may bind an enumeration with no constructors. The empty
sequence of arms covers such an enumeration, but the match rule requires at
least one arm, and a pattern would be a constructor that the enumeration does
not list, so no match on a value of it is admitted. The source language forbids empty enumerations, so
this case does not arise from source programs.

```fren
set_option fren.evidence "random" in
pub proc empty_enumeration(
    symb: Symb,
    ctx: Ctx,
    scrutinee: Typing,
    arms: Snoc<ArmF<Typing>>,
    ty: Ty,
    owner: ItemId,
): (holds?) {
    ensure output: holds?
    ensure unadmitted: when symb_ok?(symb)
        and entry(symb, owner) = Option::Some(ItemKind::Enumeration(Empty))
        and scrutinee.ty = Ty::Nominal(owner),
        not match_admitted?(symb, ctx, scrutinee, arms, ty)
}
```

## Properties

r[patterns.matching.preservation] spec::patterns::selection_typed::{body, pattern}
The arm that a value selects has the match's type: when every arm body is
typed at τ in Γ and every pattern has the scrutinee's type, the selected arm
has a body typed at τ in Γ and a pattern of that type.

```fren
set_option fren.evidence "random" in
pub proc selection_typed(
    symb: Symb,
    arms: Snoc<ArmF<Typing>>,
    owner: ItemId,
    constructor: ItemId,
    ctx: Ctx,
    ty: Ty,
    found: ArmF<Typing>,
): (holds?) {
    ensure output: holds?
    ensure body: when arm_bodies?(arms, ctx, ty) and select(arms, constructor) = Option::Some(found),
        found.body.ctx = ctx and found.body.ty = ty
    ensure pattern: when arm_patterns?(symb, arms, owner)
        and select(arms, constructor) = Option::Some(found),
        entry(symb, found.constructor) = Option::Some(ItemKind::Constructor(owner))
}
```

r[patterns.matching.admitted-selects] spec::patterns::{selected_typed?, admitted_selects_typed::selected}
An admitted match selects an arm for every constructor of its scrutinee's
enumeration, and that arm's body has the match's type. The chapter has no
values or evaluation step, so this is a statement about the typing of the
selected arm, not a proof of type safety.

```fren
pub fn selected_typed?(arms: Snoc<ArmF<Typing>>, constructor: ItemId, ctx: Ctx, ty: Ty) :=
    match select(arms, constructor) {
        Option::Some(found) => found.body.ctx = ctx and found.body.ty = ty,
        Option::None => false,
    }

set_option fren.evidence "random" in
pub proc admitted_selects_typed(
    symb: Symb,
    ctx: Ctx,
    scrutinee: Typing,
    arms: Snoc<ArmF<Typing>>,
    ty: Ty,
    owner: ItemId,
    constructor: ItemId,
): (holds?) {
    ensure output: holds?
    ensure selected: when symb_ok?(symb) and match_admitted?(symb, ctx, scrutinee, arms, ty)
        and scrutinee.ty = Ty::Nominal(owner)
        and entry(symb, constructor) = Option::Some(ItemKind::Constructor(owner)),
        selected_typed?(arms, constructor, ctx, ty)
}
```

r[patterns.matching.dynamics] spec::patterns::{selected_value, dynamics_selection::{agrees, runs_last, selects_first}}
The [dynamic semantics](DynamicSemantics.md#r-dynamics.match.selection) is
defined for the typed programs with
[distinct arms](StaticSemantics.md#r-statics.match.distinct), where at
most one arm has the scrutinee's constructor. Its
[table evaluator](DynamicSemantics.md#r-dynamics.table.differences) is
defined for every typed program, and it runs the arm written last when
several arms have the scrutinee's constructor: its `arm_value`
consults the newest arm first. `select` takes the arm written first.
`selected_value` is the value that the arm `select` gives would have, read
from the same row values as `arm_value` reads.

When no arm repeats the pattern of an earlier arm, the two agree: `arm_value`
is `selected_value` for every constructor, whether or not an arm is written
for it. When the scrutinee's constructor has a repeated arm they can
disagree. For two arms with the one constructor, `arm_value` is the value of the second arm's body and
`selected_value` the value of the first's, and these differ whenever the
bodies' values do. Such a match can be typed, since
[typing ignores repeated arms](Types.md#r-types.judgment.coverage-separate),
and the table evaluator gives it a value. This chapter
[rejects](#r-patterns.coverage.repeated) the match, as the static
semantics does, and the step relation of the dynamic semantics is not
stated of it, so no admitted program reaches the disagreement; the table
evaluator does not use that check.

That the two functions differ is open. `select`, and with it the production
`FrenHirToThir.selectArm` that the evaluator and confirmation call, is not
equal to the table evaluator's selection on a typed match with a repeated
arm, and gives another value when the scrutinee's constructor has repeated arms whose
bodies' values differ. This
chapter does not change the table evaluator; bringing the two to one
choice belongs to the unit that aligns the evaluators.

```fren
use spec::denotation::Value

use spec::dynamics::{arm_value, value_at}

use spec::types::Arm

pub fn selected_value(
    prior: Snoc<Option<Value>>,
    arms: Snoc<Arm>,
    constructor: ItemId
): Option<Value> := match select(arms, constructor) {
    Option::Some(found) => value_at(prior, found.body),
    Option::None => Option::None,
}

set_option fren.evidence "random" in
pub proc dynamics_selection(
    prior: Snoc<Option<Value>>,
    arms: Snoc<Arm>,
    first: Arm,
    second: Arm,
    constructor: ItemId,
): (holds?) {
    ensure output: holds?
    ensure agrees: when reachable?(arms),
        arm_value(prior, arms, constructor) = selected_value(prior, arms, constructor)
    ensure runs_last: when first.constructor = constructor and second.constructor = constructor,
        arm_value(prior, Extend(Extend(Empty, first), second), constructor) = value_at(prior, second.body)
    ensure selects_first: when first.constructor = constructor and second.constructor = constructor,
        selected_value(prior, Extend(Extend(Empty, first), second), constructor) = value_at(prior, first.body)
}
```

## Admission of nested matches

r[patterns.admission.layer] spec::patterns::{layer_admitted?, rows_admitted?, derivation_admitted?, table_admission::{newest, rest}}
A match can occur in any child position of an expression, so admission is
stated over the [derivation table](Types.md#r-types.derivation.table), whose
rows hold every written occurrence: a table is *admitted* when the layer of
each of its rows is. A layer is admitted when it is not a match or its match
is admitted at the row's context and type. An expression is typed and admitted
when some valid table for it is admitted.

```text
  Σ; Γ ⊢ e : τ   Σ; Δ ⊢ match s { arms } : σ admitted   (each match in e, at its Δ and σ)
  ──────────────────────────────────────────────────────────────────────────────────
  Σ; Γ ⊢ e : τ admitted
```

```fren
pub fn layer_admitted?(symb: Symb, ctx: Ctx, form: CoreF<Typing>, ty: Ty) := match form {
    CoreF::Match(scrutinee, arms) => match_admitted?(symb, ctx, scrutinee, arms, ty),
    _ => true,
}

pub fn rows_admitted?(symb: Symb, rows: Snoc<Row>) := match rows {
    Empty => true,
    Extend(earlier, row) =>
        rows_admitted?(symb, earlier)
        and match annotate(earlier, row.form) {
            Option::Some(form) => layer_admitted?(symb, row.ctx, form, row.ty),
            Option::None => false,
        },
}

pub fn derivation_admitted?(symb: Symb, rows: Snoc<Row>, ctx: Ctx, ty: Ty) :=
    derivation?(symb, rows, ctx, ty) and rows_admitted?(symb, rows)

set_option fren.evidence "random" in
pub proc table_admission(
    symb: Symb,
    earlier: Snoc<Row>,
    row: Row,
    scrutinee: Typing,
    arms: Snoc<ArmF<Typing>>,
): (holds?) {
    ensure output: holds?
    ensure newest: when rows_admitted?(symb, Extend(earlier, row))
        and annotate(earlier, row.form) = Option::Some(CoreF::Match(scrutinee, arms)),
        match_admitted?(symb, row.ctx, scrutinee, arms, row.ty)
    ensure rest: when rows_admitted?(symb, Extend(earlier, row)),
        rows_admitted?(symb, earlier)
}
```

r[patterns.admission.program] spec::patterns::{decl_admitted?, decls_admitted?, prog_admitted?, program_admission::{typed, bodies}}
A declaration is admitted when it is well typed and the table of its body is
admitted, and a program when it is well typed and every declaration is
admitted, so that every match in a program is admitted.

```text
  ⊢ (Σ, ds) ok   Σ ⊢ d admitted (each d in ds)
  ────────────────────────────────────────────
  ⊢ (Σ, ds) admitted
```

```fren
pub fn decl_admitted?(symb: Symb, decl: Decl) :=
    decl_ok?(symb, decl)
    and match decl {
        Decl::Function(_, body) => rows_admitted?(symb, body),
        Decl::Condition(_, body) => rows_admitted?(symb, body),
    }

pub fn decls_admitted?(symb: Symb, decls: Snoc<Decl>) := match decls {
    Empty => true,
    Extend(earlier, decl) => decl_admitted?(symb, decl) and decls_admitted?(symb, earlier),
}

pub fn prog_admitted?(symb: Symb, decls: Snoc<Decl>) :=
    prog_ok?(symb, decls) and decls_admitted?(symb, decls)

set_option fren.evidence "random" in
pub proc program_admission(symb: Symb, earlier: Snoc<Decl>, item: ItemId, body: Snoc<Row>): (
    holds?,
) {
    ensure output: holds?
    ensure typed: when prog_admitted?(symb, Extend(earlier, Decl::Function(item, body))),
        prog_ok?(symb, Extend(earlier, Decl::Function(item, body)))
    ensure bodies: when prog_admitted?(symb, Extend(earlier, Decl::Function(item, body))),
        rows_admitted?(symb, body)
}
```

## Examples

r[patterns.examples.matching] spec::patterns::{INT, SCRUTINEE, LIGHT_ARMS, MISSING_ARMS, REPEATED_ARMS, FOREIGN_ARMS, NO_ARMS, pattern_examples::valid}
The examples use the environment `SYMB` of [the Core examples](Types.md#r-types.examples.derivations),
whose enumeration `M::Light` has the constructors `Red` and `Green` and whose
enumeration `M::Signal` has the constructor `Red`. Every arm body is an
integer in the empty context, and the scrutinee has the type `Nominal(M::Light)`.
Its inventory is read from `SYMB`. In the judgments, `Σ` is `SYMB` and `·`
the empty context.

```text
  Σ; · ⊢ match s { Red ⇒ 1 | Green ⇒ 2 } : Int admitted      Red ▷ Red ⇒ 1
  Σ ⊬ Red ⇒ 1 cover M::Light                                 missing: Green; Green ▷ none
  Σ ⊢ Red ⇒ 1 | Red ⇒ 2 | Green ⇒ 3 cover M::Light           not admitted: repeated: Red; Red ▷ Red ⇒ 1
  Σ ⊬ Signal::Red ⇒ 1 | Green ⇒ 2 : arms of M::Light         Signal::Red is no pattern of M::Light
  Σ ⊬ (no arms) cover M::Light                               missing: Red, Green
```

The procedure `pattern_examples` states each of these. The last example is
also not typed, because the match rule needs an arm, so it is not admitted.

```fren
use spec::names::{LIGHT, LIGHT_GREEN, LIGHT_RED, one, three, two}

use spec::types::{SIGNAL_RED, SYMB}

pub const INT: Typing := Typing { ctx := Empty, ty := Ty::Integer }

pub const SCRUTINEE: Typing := Typing { ctx := Empty, ty := Ty::Nominal(LIGHT) }

pub const LIGHT_ARMS: Snoc<ArmF<Typing>> := two(
    ArmF { constructor := LIGHT_RED, body := INT },
    ArmF { constructor := LIGHT_GREEN, body := INT }
)

pub const MISSING_ARMS: Snoc<ArmF<Typing>> := one(ArmF { constructor := LIGHT_RED, body := INT })

pub const REPEATED_ARMS: Snoc<ArmF<Typing>> := three(
    ArmF { constructor := LIGHT_RED, body := INT },
    ArmF { constructor := LIGHT_RED, body := INT },
    ArmF { constructor := LIGHT_GREEN, body := INT }
)

pub const FOREIGN_ARMS: Snoc<ArmF<Typing>> := two(
    ArmF { constructor := SIGNAL_RED, body := INT },
    ArmF { constructor := LIGHT_GREEN, body := INT }
)

pub const NO_ARMS: Snoc<ArmF<Typing>> := Empty

-- The examples are constant judgments, which the wrapper evaluates.
set_option fren.lint.assertions_on_constants "allow" in
set_option fren.evidence "random" in
pub proc pattern_examples(): (holds?) {
    ensure output: holds?
    ensure valid: match_admitted?(SYMB, Empty, SCRUTINEE, LIGHT_ARMS, Ty::Integer)
        and select(LIGHT_ARMS, LIGHT_RED) = Option::Some(
            ArmF {
                constructor := LIGHT_RED,
                body := INT,
            }
        )
        and reachable?(LIGHT_ARMS)
        and not covered?(SYMB, LIGHT, MISSING_ARMS)
        and uncovered(inventory(SYMB, LIGHT), MISSING_ARMS) = one(LIGHT_GREEN)
        and select(MISSING_ARMS, LIGHT_GREEN) = Option::None
        and covered?(SYMB, LIGHT, REPEATED_ARMS)
        and repeats(REPEATED_ARMS) = one(LIGHT_RED)
        and not reachable?(REPEATED_ARMS)
        and match_rule?(SYMB, Empty, SCRUTINEE, REPEATED_ARMS, Ty::Integer)
        and not match_admitted?(SYMB, Empty, SCRUTINEE, REPEATED_ARMS, Ty::Integer)
        and select(REPEATED_ARMS, LIGHT_RED) = Option::Some(
            ArmF {
                constructor := LIGHT_RED,
                body := INT,
            }
        )
        and not arm_patterns?(SYMB, FOREIGN_ARMS, LIGHT)
        and not covered?(SYMB, LIGHT, FOREIGN_ARMS)
        and not match_admitted?(SYMB, Empty, SCRUTINEE, FOREIGN_ARMS, Ty::Integer)
        and uncovered(inventory(SYMB, LIGHT), FOREIGN_ARMS) = one(LIGHT_RED)
        and uncovered(inventory(SYMB, LIGHT), NO_ARMS) = two(LIGHT_RED, LIGHT_GREEN)
        and not covered?(SYMB, LIGHT, NO_ARMS)
        and not match_rule?(SYMB, Empty, SCRUTINEE, NO_ARMS, Ty::Integer)
        and not match_admitted?(SYMB, Empty, SCRUTINEE, NO_ARMS, Ty::Integer)
}
```

r[patterns.examples.nested] spec::patterns::{sum_table, BOTH_POSITIONS, ONE_POSITION, nested_examples::valid}
A match nested as the operand of an addition is found through its table. With
the one arm `Red ⇒ 1` the expression below is typed, because typing does not
need coverage, but it is not admitted; with both arms it is admitted.

```text
  Σ; · ⊢ (match Red { Red ⇒ 1 }) + (…) : Int              typed, not admitted
  Σ; · ⊢ (match Red { Red ⇒ 1 | Green ⇒ 2 }) + (…) : Int  typed and admitted
```

| Row | Layer | Context | Type |
| --- | --- | --- | --- |
| 0 | `M::Light::Red` | `·` | `Nominal(M::Light)` |
| 1 | `1` | `·` | Int |
| 2 | `2` | `·` | Int |
| 3 | `match row 0 { M::Light::Red ⇒ row 1 [\| M::Light::Green ⇒ row 2] }` | `·` | Int |
| 4 | `row 3 + row 3` | `·` | Int |

```fren
use spec::names::four

use spec::surface::BinaryOp

use spec::types::row

pub fn sum_table(arms: Snoc<ArmF<Int>>): Snoc<Row> := Extend(
    four(
        row(CoreF::Constructor(LIGHT_RED), Empty, Ty::Nominal(LIGHT)),
        row(CoreF::IntegerLiteral(1), Empty, Ty::Integer),
        row(CoreF::IntegerLiteral(2), Empty, Ty::Integer),
        row(CoreF::Match(0, arms), Empty, Ty::Integer)
    ),
    row(CoreF::Binary(BinaryOp::Add, 3, 3), Empty, Ty::Integer)
)

pub const BOTH_POSITIONS: Snoc<ArmF<Int>> := two(
    ArmF { constructor := LIGHT_RED, body := 1 },
    ArmF { constructor := LIGHT_GREEN, body := 2 }
)

pub const ONE_POSITION: Snoc<ArmF<Int>> := one(ArmF { constructor := LIGHT_RED, body := 1 })

-- The examples are constant judgments, which the wrapper evaluates.
set_option fren.lint.assertions_on_constants "allow" in
set_option fren.evidence "random" in
pub proc nested_examples(): (holds?) {
    ensure output: holds?
    ensure valid: derivation_admitted?(SYMB, sum_table(BOTH_POSITIONS), Empty, Ty::Integer)
        and derivation?(SYMB, sum_table(ONE_POSITION), Empty, Ty::Integer)
        and not rows_admitted?(SYMB, sum_table(ONE_POSITION))
}
```

## Informative source examples

These source programs are checked, with the diagnostics they expect, by
both of today's front ends. They are informative: the translation from
source programs to the Core is not yet specified. In them a constructor
with no arm, an arm repeated for a constructor, and a pattern of another
enumeration are each rejected, as the rules of this chapter require.

```fren example
--@ reference: patterns.coverage.diagnostic
pub mod bad

pub enum Light { Red, Green }

pub fn f(l: Light): Int := match l { Light::Red => 1 }  --~ error: non-exhaustive match: `bad::Light::Green` not covered
```

```fren example
--@ reference: patterns.coverage.repeated
pub mod bad

pub enum Light { Red, Green }

pub fn f(l: Light): Int := match l { Light::Red => 1, Light::Red => 2, Light::Green => 3 }  --~ error: unreachable arm
```

```fren example
--@ reference: patterns.typing.pattern
pub mod bad

pub enum Light { Red, Green }
pub enum Signal { Red }

pub fn f(l: Light): Int := match l { Signal::Red => 1, Light::Green => 2 }  --~ error: expected a variant of `bad::Light`, but this is a variant of `bad::Signal`
```
