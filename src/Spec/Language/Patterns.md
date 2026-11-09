# Patterns and matching

A match selects one of its arms by the constructor of its scrutinee. This
chapter defines the patterns of the Core, how an arm is selected, and the
static check that a match has an arm for every constructor of its
enumeration and no arm that can never be selected. [Core typing](Types.md)
supplies identities, types and the typing of a match;
[resolution](NamesAndScope.md) turns a written pattern into a constructor
identity; the [syntax](../Compiler/AstAndParsing.md#source-forms) admits only
patterns that name a variant. [Expression obligations](Expressions.md) and
verification assume the checks of this chapter, and a later compiler chapter
owns the translation of a match into decision code.

## Overview

The chapter's judgments, and the Fren definitions that state them:

| Judgment | Meaning | Fren |
| --- | --- | --- |
| `Σ ⊢ c pat a` | the pattern c is a constructor of the enumeration a | `pattern_rule?` |
| `arms ▷ c ⇒ e` | the arms select the arm with body e for constructor c | `select` |
| `Σ ⊢ arms cover a` | every constructor of a has exactly one arm | `covered?` |
| `Σ; Γ ⊢ match s { arms } : τ admitted` | the match is typed and its arms cover | `match_admitted?` |

In outline, a match on a constructor c takes the first arm written for c, and
the check on a match is exactly that every constructor of the scrutinee's
enumeration is the pattern of one arm, for arms whose patterns the typing rules
have admitted:

```text
  select   : Arms × Item → Option Arm
  covered? : Symb × Item × Arms → Bool

  select(arms, c) = the first arm with pattern c, if there is one
  covered?(Σ, a, arms)  iff  every constructor of a is the pattern of one arm
  covered?(Σ, a, arms)  and  Σ(c) = constructor of a
                        implies  select(arms, c) exists, and no other arm
                                 has the pattern c
```

The laws are the properties [determinism of selection](#r-patterns.matching.selection-laws),
[written order](#r-patterns.matching.written-order),
[exhaustiveness](#r-patterns.coverage.exhaustive),
[soundness and completeness of the check](#r-patterns.coverage.characterized),
[typing of the selected arm](#r-patterns.matching.preservation) and
[progress of an admitted match](#r-patterns.matching.progress). Coverage is
decidable: the [check](#r-patterns.coverage.checker) is a function that
recurses over finite lists, because patterns carry no payload and the
inventory of an enumeration is finite.

## Patterns

r[patterns.syntax.form] spec::patterns::Pattern
A pattern is a constructor: the identity that resolution gives to a written
qualified variant path. A pattern binds no local and takes no payload, and
the grammar has no wildcard, literal, alternative or nested pattern, so
that a written pattern and its constructor identity are the same thing. The
[arm form](Types.md#r-types.expression.syntax) of the Core, `ArmF`, pairs a
pattern with a body.

```text
  p  ::=  a::c         a variant path, resolved to the identity of c
  arm ::=  p ⇒ e
```

```fren
pub mod spec
pub mod spec::patterns

use spec::types::{
    ArmF,
    Ctx,
    ItemId,
    ItemKind,
    Snoc,
    Symb,
    Ty,
    Typing,
    arm_bodies?,
    arm_patterns?,
    entry,
    length,
    lookup,
    match_rule?,
    member?,
    symb_ok?,
}

use spec::types::Snoc::{Empty, Extend}

pub type Pattern := ItemId
```

r[patterns.typing.pattern] spec::patterns::pattern_rule?
A pattern has the enumeration that owns it as its type. The rule that types
a match requires each arm's pattern to have the type of the scrutinee,
which the [match typing](Types.md#r-types.expression.match) states as
`arm_patterns?`; a pattern with a constructor of another enumeration is
rejected.

```text
  Σ(c) = constructor of a
  ───────────────────────
  Σ ⊢ c pat a
```

```fren
pub fn pattern_rule?(symb: Symb, pattern: Pattern, owner: ItemId) :=
    entry(symb, pattern) = Option::Some(ItemKind::Constructor(owner))
```

r[patterns.typing.arms] spec::patterns::pattern_arms::{step, empty, unique}
The arms of a match have the type of the scrutinee when each arm's pattern
does, and a pattern has at most one type.

```fren
expect pattern_arms(
    symb: Symb,
    earlier: Snoc<ArmF<Typing>>,
    arm: ArmF<Typing>,
    owner: ItemId,
    other: ItemId,
) {
    expect step: arm_patterns?(symb, Extend(earlier, arm), owner)
        iff pattern_rule?(symb, arm.constructor, owner) and arm_patterns?(symb, earlier, owner)
    expect empty: arm_patterns?(symb, Empty, owner)
    expect unique: not pattern_rule?(symb, arm.constructor, owner)
        or not pattern_rule?(symb, arm.constructor, other) or owner = other
}
```

## Matching

r[patterns.matching.select] spec::patterns::{select, occurrences}
The arms of a match are a snoc sequence in written order, so the newest entry
is the last arm written. A value built with constructor c selects the first
arm written for c, if there is one; `select` consults the earlier arms before
the newest. `occurrences` counts the arms written for c.

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
the constructor as its pattern; an earlier arm for the constructor wins over a
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

r[patterns.matching.written-order] spec::patterns::{first_index, select_position::first}
The first arm for c is the arm of least written position, counting from 0 at
the oldest arm, which is how the source reads. `first_index` computes that
position, and selection agrees with it.

```fren
pub fn first_index<E>(arms: Snoc<ArmF<E>>, constructor: ItemId): Option<Int> := match arms {
    Empty => Option::None,
    Extend(earlier, arm) => match first_index(earlier, constructor) {
        Option::Some(index) => Option::Some(index),
        Option::None =>
            if arm.constructor = constructor then Option::Some(length(earlier)) else Option::None,
    },
}

set_option fren.evidence "random" in
pub proc select_position(arms: Snoc<ArmF<Typing>>, constructor: ItemId): (holds?) {
    ensure output: holds?
    ensure first: select(arms, constructor) = match first_index(arms, constructor) {
        Option::Some(index) => lookup(arms, index),
        Option::None => Option::None,
    }
}
```

## Coverage

r[patterns.coverage.covered] spec::patterns::{exact_cover?, covered?}
Arms *cover* an enumeration when each constructor that Σ lists for it is the
pattern of exactly one arm. A constructor with no arm is *missing*. A
constructor with several arms is *repeated*: every arm after the first for it
is unreachable, because selection takes the first. The inventory is read from
Σ, so an owner that Σ does not bind as an enumeration is not covered.

```text
  Σ(a) = enumeration listing c₀, …, cₙ
  occurrences(arms, cₖ) = 1   (each k)
  ────────────────────────────────────
  Σ ⊢ arms cover a
```

```fren
pub fn exact_cover?<E>(constructors: Snoc<ItemId>, arms: Snoc<ArmF<E>>) := match constructors {
    Empty => true,
    Extend(earlier, constructor) =>
        occurrences(arms, constructor) = 1 and exact_cover?(earlier, arms),
}

pub fn covered?<E>(symb: Symb, owner: ItemId, arms: Snoc<ArmF<E>>) := match entry(symb, owner) {
    Option::Some(ItemKind::Enumeration(constructors)) => exact_cover?(constructors, arms),
    _ => false,
}
```

r[patterns.coverage.checker] spec::patterns::{uncovered, repeats, production_missing, production_repeated, check_coverage::{missing, repeated}}
The check computes the two lists that a rejected match reports. `uncovered`
lists the inventory's constructors that no arm names, in inventory order.
`repeats` lists the pattern of each arm that an earlier arm already names, in
written order. The functions `production_missing` and `production_repeated` stand for the
two lists that the production function `FrenHirToThir.coverage` computes from
an inventory and the arms' targets; the wrapper interprets them by that
function, and `check_coverage` states that they are `uncovered` and `repeats`.
The production check's choice of inventory, its extraction of the arms'
targets and its final verdict are not bound here. The wrapper instantiates the
generic function at the specification's own identities, with decidable
equality; that the production instance at the compiler's item identities
agrees with it rests on their equality being lawful, which is not proved
here.

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

pub fn production_missing(Snoc<ItemId>, Snoc<ArmF<Typing>>): Snoc<ItemId>

pub fn production_repeated(Snoc<ArmF<Typing>>): Snoc<ItemId>

set_option fren.evidence "random" in
pub proc check_coverage(constructors: Snoc<ItemId>, arms: Snoc<ArmF<Typing>>): (holds?) {
    ensure output: holds?
    ensure missing: production_missing(constructors, arms) = uncovered(constructors, arms)
    ensure repeated: production_repeated(arms) = repeats(arms)
}
```

r[patterns.coverage.diagnostic] spec::patterns::{CoverageError, coverage_error, coverage_error_none::{accepted, rejected}}
A match that does not cover its scrutinee's enumeration is rejected with an
error that names the enumeration, the missing constructors in declaration
order and the repeated patterns in written order. The compiler reports the error at the first repeated arm when there is one,
and otherwise at the `match` keyword; source positions are outside the Core. A match on a type that
is not an enumeration has no coverage error here: its owner has no
constructors to cover, and the typing rules reject it. The error has no
catalogue code yet, and its rendering is not specified here.

```fren
pub struct CoverageError { owner: ItemId, missing: Snoc<ItemId>, repeated: Snoc<ItemId> }

pub fn coverage_error<E>(symb: Symb, owner: ItemId, arms: Snoc<ArmF<E>>): Option<CoverageError> :=
    match entry(symb, owner) {
        Option::Some(ItemKind::Enumeration(constructors)) =>
            if exact_cover?(constructors, arms) then Option::None
            else Option::Some(
                CoverageError {
                    owner,
                    missing := uncovered(constructors, arms),
                    repeated := repeats(arms),
                }
            ),
        _ => Option::None,
    }
```

```fren
expect coverage_error_none(
    symb: Symb,
    owner: ItemId,
    constructors: Snoc<ItemId>,
    arms: Snoc<ArmF<Typing>>,
) {
    expect accepted: when entry(symb, owner) = Option::Some(ItemKind::Enumeration(constructors))
        and covered?(symb, owner, arms), coverage_error(symb, owner, arms) = Option::None
    expect rejected: when entry(symb, owner) = Option::Some(ItemKind::Enumeration(constructors))
        and not covered?(symb, owner, arms),
        coverage_error(symb, owner, arms) = Option::Some(
            CoverageError {
                owner,
                missing := uncovered(constructors, arms),
                repeated := repeats(arms),
            }
        )
}
```

r[patterns.coverage.admitted] spec::patterns::match_admitted?
A match is admitted when it is typed by the [match rule](Types.md#r-types.expression.match)
and its arms cover the scrutinee's enumeration. Typing does not depend on
coverage, as [stated for typing](Types.md#r-types.judgment.coverage-separate),
so an unadmitted match can still be typed; verification and evaluation start
from admitted matches only.

```text
  Σ; Γ ⊢ match s { arms } : τ   Σ; Γ ⊢ s : Nominal(a)   Σ ⊢ arms cover a
  ─────────────────────────────────────────────────────────────────────
  Σ; Γ ⊢ match s { arms } : τ admitted
```

```fren
pub fn match_admitted?(symb: Symb, ctx: Ctx, scrutinee: Typing, arms: Snoc<ArmF<Typing>>, ty: Ty) :=
    match_rule?(symb, ctx, scrutinee, arms, ty)
    and match scrutinee.ty {
        Ty::Nominal(owner) => covered?(symb, owner, arms),
        _ => false,
    }
```

## Properties

r[patterns.matching.order-free] spec::patterns::{has_arm?, arm_order::unique}
When a constructor has exactly one arm, that arm is the arm selected for it,
wherever it is written, so the order of the arms of a covering match does not
change which arm any value selects.

```fren
pub fn has_arm?<E>(arms: Snoc<ArmF<E>>, arm: ArmF<E>) := match arms {
    Empty => false,
    Extend(earlier, other) => other = arm or has_arm?(earlier, arm),
}

set_option fren.evidence "random" in
pub proc arm_order(arms: Snoc<ArmF<Typing>>, arm: ArmF<Typing>): (holds?) {
    ensure output: holds?
    ensure unique: when has_arm?(arms, arm) and occurrences(arms, arm.constructor) = 1,
        select(arms, arm.constructor) = Option::Some(arm)
}
```

r[patterns.coverage.exhaustive] spec::patterns::exhaustive_selection::selects
In a well-formed Σ, when arms cover an enumeration, every constructor of that
enumeration selects an arm.

```fren
set_option fren.evidence "random" in
pub proc exhaustive_selection(
    symb: Symb,
    owner: ItemId,
    arms: Snoc<ArmF<Typing>>,
    constructor: ItemId,
): (holds?) {
    ensure output: holds?
    ensure selects: when symb_ok?(symb) and covered?(symb, owner, arms)
        and pattern_rule?(symb, constructor, owner),
        select(arms, constructor) is Option::Some(_)
}
```

r[patterns.coverage.characterized] spec::patterns::{inventory_selected?, targets_listed?, coverage_characterized::{agrees, characterized, listed}}
The check is sound and complete for the statement that a match selects an
arm for every constructor and has no unreachable arm. Take a well-formed Σ,
an enumeration with constructors c₀, …, cₙ, and arms whose patterns are all
constructors of the enumeration, as typing guarantees. The arms cover the
enumeration exactly when each cₖ selects an arm and no arm is repeated, which
is exactly when `uncovered` and `repeats` are both empty. The procedure
states this and, since `covered?` is a function, that coverage is decidable.

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
    ensure characterized: when targets_listed?(constructors, arms)
        and entry(symb, owner) = Option::Some(ItemKind::Enumeration(constructors)),
        covered?(symb, owner, arms)
        iff inventory_selected?(constructors, arms) and repeats(arms) = Empty
    ensure agrees: when targets_listed?(constructors, arms)
        and entry(symb, owner) = Option::Some(ItemKind::Enumeration(constructors)),
        covered?(symb, owner, arms)
        iff uncovered(constructors, arms) = Empty and repeats(arms) = Empty
}
```

r[patterns.matching.preservation] spec::patterns::{selected_typed?, selection_typed::{body, pattern}}
The arm that a value selects has the match's type: when every arm body is
typed at τ in Γ and every pattern has the scrutinee's type, the selected arm
has a body typed at τ in Γ and a pattern of that type.

```fren
pub fn selected_typed?(arms: Snoc<ArmF<Typing>>, constructor: ItemId, ctx: Ctx, ty: Ty) :=
    match select(arms, constructor) {
        Option::Some(found) => found.body.ctx = ctx and found.body.ty = ty,
        Option::None => false,
    }

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
        pattern_rule?(symb, found.constructor, owner)
}
```

r[patterns.matching.progress] spec::patterns::match_progress::selected
An admitted match on a value of its scrutinee's enumeration selects an arm,
and that arm's body has the match's type. The chapter has no values or evaluation step, so this is a statement about
the typing of the selected arm, not a proof of type safety.

```fren
set_option fren.evidence "random" in
pub proc match_progress(
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
        and scrutinee.ty = Ty::Nominal(owner) and pattern_rule?(symb, constructor, owner),
        selected_typed?(arms, constructor, ctx, ty)
}
```

r[patterns.matching.production] spec::patterns::{production_pick, production_selection::first}
The evaluator and the confirmation of a strict evaluation each pick an arm
with their own loop over the written arms, taking the first arm whose resolved
pattern is the scrutinee's constructor; the lowering of a match instead
lowers every arm into conditional branches and uses the last arm as the
fallback. That each agrees with `select` on an admitted match, and so with the
others, is not yet proved: no function
of the production code computes the selection by itself for the proof to bind.

Here `production_pick` stands for the arm that whichever production path is
considered picks, the evaluator, the confirmation or the lowering alike; the
equality is claimed only for an admitted match and a constructor of its
scrutinee's enumeration, where lowering's fallback arm cannot differ.

```fren
pub fn production_pick(Snoc<ArmF<Typing>>, ItemId): Option<ArmF<Typing>>

set_option fren.evidence "random" in
pub proc production_selection(
    symb: Symb,
    ctx: Ctx,
    scrutinee: Typing,
    arms: Snoc<ArmF<Typing>>,
    ty: Ty,
    owner: ItemId,
    constructor: ItemId,
): (holds?) {
    ensure output: holds?
    ensure first: when symb_ok?(symb) and match_admitted?(symb, ctx, scrutinee, arms, ty)
        and scrutinee.ty = Ty::Nominal(owner) and pattern_rule?(symb, constructor, owner),
        production_pick(arms, constructor) = select(arms, constructor)
}

trusted production_selection: "open: the evaluator and confirmation loops select inline and lowering builds branches, and no extracted function computes the selection that a proof could bind to select"
```

## Examples

r[patterns.examples.matching] spec::patterns::{LIGHT_ARMS, MISSING_ARMS, REPEATED_ARMS, FOREIGN_ARMS, NO_ARMS, pattern_examples::valid}
The examples use the environment `SYMB` of [the Core examples](Types.md#r-types.examples.derivations),
whose enumeration `M::Light` has the constructors `Red` and `Green` and whose
enumeration `M::Signal` has the constructor `Red`. The procedure
`pattern_examples` states that

- the arms `Red ⇒ 1 | Green ⇒ 2` cover `M::Light`, and `Red` selects the first;
- the arms `Red ⇒ 1` do not cover it: `Green` is missing, and `Green` selects no arm;
- the arms `Red ⇒ 1 | Red ⇒ 2 | Green ⇒ 3` do not cover it: `Red` is repeated,
  and `Red` selects the first arm for it;
- the arms `Signal::Red ⇒ 1 | Green ⇒ 2` have a pattern that is not a constructor of
  `M::Light`, so the pattern rule fails for it, and so does coverage, since `Red` is
  missing;
- no arms leave both constructors missing.

The chapter's wrapper proves each by evaluation.

```fren
use spec::types::{LIGHT, LIGHT_GREEN, LIGHT_RED, SIGNAL_RED, SYMB, one, three, two}

pub const LIGHT_ARMS: Snoc<ArmF<Int>> := two(
    ArmF { constructor := LIGHT_RED, body := 1 },
    ArmF { constructor := LIGHT_GREEN, body := 2 }
)

pub const MISSING_ARMS: Snoc<ArmF<Int>> := one(ArmF { constructor := LIGHT_RED, body := 1 })

pub const REPEATED_ARMS: Snoc<ArmF<Int>> := three(
    ArmF { constructor := LIGHT_RED, body := 1 },
    ArmF { constructor := LIGHT_RED, body := 2 },
    ArmF { constructor := LIGHT_GREEN, body := 3 }
)

pub const FOREIGN_ARMS: Snoc<ArmF<Int>> := two(
    ArmF { constructor := SIGNAL_RED, body := 1 },
    ArmF { constructor := LIGHT_GREEN, body := 2 }
)

pub const NO_ARMS: Snoc<ArmF<Int>> := Empty

-- The examples are constant judgments, which the wrapper evaluates.
set_option fren.lint.assertions_on_constants "allow" in
set_option fren.evidence "random" in
pub proc pattern_examples(): (holds?) {
    ensure output: holds?
    ensure valid: covered?(SYMB, LIGHT, LIGHT_ARMS)
        and select(LIGHT_ARMS, LIGHT_RED) = Option::Some(
            ArmF {
                constructor := LIGHT_RED,
                body := 1,
            }
        )
        and not covered?(SYMB, LIGHT, MISSING_ARMS)
        and uncovered(two(LIGHT_RED, LIGHT_GREEN), MISSING_ARMS) = one(LIGHT_GREEN)
        and select(MISSING_ARMS, LIGHT_GREEN) = Option::None
        and not covered?(SYMB, LIGHT, REPEATED_ARMS)
        and repeats(REPEATED_ARMS) = one(LIGHT_RED)
        and select(REPEATED_ARMS, LIGHT_RED) = Option::Some(
            ArmF {
                constructor := LIGHT_RED,
                body := 1,
            }
        )
        and not pattern_rule?(SYMB, SIGNAL_RED, LIGHT)
        and not covered?(SYMB, LIGHT, FOREIGN_ARMS)
        and uncovered(two(LIGHT_RED, LIGHT_GREEN), NO_ARMS) = two(LIGHT_RED, LIGHT_GREEN)
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
--@ reference: patterns.coverage.checker
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
