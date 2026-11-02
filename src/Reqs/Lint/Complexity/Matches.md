# Matches

## Trivial matches

`trivial_match` fires on a `match` of one arm, whose pattern binds no name:
`_`, the variant of an enumeration with one variant, without a payload or
with `_` for each of its values, or an or-pattern. A `match` is exhaustive
(see [Matches](../../Lang/Expressions.md#matches)), so that arm matches every
value of the scrutinee, and the `match` is the arm's body. Like Clippy's
`match_single_binding`, it is in `complexity`, and it is fixable. The fix
replaces the `match` with the body, which keeps the text it is written
with, and is put in parentheses where [fixes need them](../../Lint.md#parentheses-in-fixes):
`x = 2 * match e { _ =>
x - 1 }` becomes `x = 2 * (x - 1)`. The body's guard is the guard of the
`match` and its pattern's test, which every value passes, so it is the
guard of the `match`, where the fix puts the body. The fix only drops the
scrutinee, which removes what was evaluated, so no guard is weaker. It
does not fire where the arm has a [guard](../../Lang/Expressions.md#matches),
which may fail where the pattern matches, so the arm is not taken
everywhere. `lint::trivial_match` states when it fires, of a `match`
without guards:

```fren
pub mod lint

pub proc trivial_match(
    n_arms: Int,
    binds?,              -- the first arm's pattern binds a name
): (det fires?) {
    assume counts: n_arms >= 1

    ensure rule: fires? iff (n_arms = 1 and not binds?)
}
```

### Trivial matches, over the syntax of the semantics

In the [syntax of the semantics](../../Lang/Semantics.md#abstract-syntax),
a `match` of one arm without a guard is `Match(s, p, true, b, NoMatch)`
([Derived forms](../../Lang/Semantics.md#derived-forms)).
`trivial_match_fires?` fires on it where `p` is `_`, an or-pattern, or a
variant without a payload, and its fix is `b`. These patterns leave the
environment as it is wherever they match (`lang::bind`), since an
or-pattern binds nothing (`F0333`). A variant whose payload is `_` for
each of its values binds nothing either, but telling so looks along the
payload, which needs a recursion, so the function leaves it, and the
linter fires there besides. The guard `true` elaborates away, so the
function fires on `match s { _ if true => b }` too. The linter does not,
since the arm has a guard, and leaves it to
[`trivial_guard`](#trivial-guards), whose fix makes it a trivial `match`.
That is a rewrite, as [Fixes as
rewrites](../Rewrites.md) states for every such lint:

```fren
-- `p` is `_`, an or-pattern, or a variant without a payload: it binds no name.
pub fn binds_none?<V>(p: lang::Pattern<V>) :=
    p is lang::Pattern::Wildcard | lang::Pattern::Or(_, _) | lang::Pattern::Variant(_, lang::Pattern::Nil)

pub fn trivial_match_fires?<V>(e: lang::Expr<V>) := match e {
    lang::Expr::Match(_, p, g, _, rest) =>
        g = lang::Expr::Literal(lang::Value::True) and rest = lang::Expr::NoMatch and binds_none?(p),
    _ => false,
}

pub fn trivial_match_fix<V>(e: lang::Expr<V>): lang::Expr<V> := match e {
    lang::Expr::Match(_, p, g, b, rest) =>
        if g = lang::Expr::Literal(lang::Value::True) and rest = lang::Expr::NoMatch and binds_none?(p) then b
        else e,
    _ => e,
}
```

`lint::trivial_match` binds this to the linter. Where the arm's pattern
is one of those, the front ends read it as binding nothing (`read`), and
the linter fires, as the function does, and the fix is the body. Where
the pattern binds a name, the linter does not fire. That the front ends
read the pattern so, and the text of the fix, are trusted, and checked by
the ui tests in `test/ui/lints/methods.fren` and
`test/ui/lints/matches_table.fren`:

```fren
expect trivial_match_elaborated(
    binds?,
    s: lang::Expr<lang::Id>,
    p: lang::Pattern<lang::Id>,
    b: lang::Expr<lang::Id>,
) {
    use lang::Expr::{Literal, Match, NoMatch}

    assume read: when binds_none?(p), not binds?

    call t := trivial_match(1, binds?)

    let arm: lang::Expr<lang::Id> := Match(s, p, Literal(lang::Value::True), b, NoMatch)

    expect fires: when binds_none?(p), t.fires? and trivial_match_fires?(arm) and trivial_match_fix(arm) = b
    expect binds: when binds?, not t.fires?
}
```

Where it fires, the fix [agrees](../Meaning.md#fixes-that-agree) with the
`match`, in every interpretation and environment. Where the scrutinee is
well-defined and the pattern matches it, the `match` is the body, in the
environment as it is. Where the pattern does not match, it is `NoMatch`,
which is undefined, as the `match` is where the scrutinee is undefined.
The static rules accept only a `match` whose arms cover the type, so a
well-typed `match` never reaches `NoMatch`, but the fix agrees without
that. `src/Impls/Rewrites.lean` proves this in Lean, for every
expression, interpretation and environment; `fren check` tests it:

```fren
set_option fren.evidence "random" in
pub proc trivial_match_keeps_meaning(e: lang::Expr<lang::Id>, i: lang::Interp, env: lang::Env) {
    ensure agrees: when trivial_match_fires?(e),
        agrees?(
            lang::eval(i, env, trivial_match_fix(e)),
            lang::eval(i, env, e)
        )
}
```

The fix writes the body, an operand. Once the operands are fixed, it does
not fire, so the fix leaves nothing to fix. The fix alone need not: the
fix of a trivial `match` whose body is another is that one, which fires
again (`kept`). And a `match` around it may start firing once it is
fixed: an arm whose `rest` is a trivial `match` of `NoMatch` does not
fire, but the fix of its `rest` makes it `NoMatch` (`around`):

```fren
expect trivial_match_refires(
    s: lang::Expr<lang::Id>,
    t: lang::Expr<lang::Id>,
    b: lang::Expr<lang::Id>,
) {
    use lang::Expr::{Literal, Match, NoMatch}
    use lang::Pattern::Wildcard
    use lang::Value::True

    let inner: lang::Expr<lang::Id> := Match(t, Wildcard, Literal(True), NoMatch, NoMatch)

    expect kept: trivial_match_fires?(
        trivial_match_fix(
            Match(
                s,
                Wildcard,
                Literal(True),
                Match(t, Wildcard, Literal(True), b, NoMatch),
                NoMatch
            )
        )
    )
    expect around: not trivial_match_fires?(Match(s, Wildcard, Literal(True), b, inner))
        and trivial_match_fires?(
            Match(s, Wildcard, Literal(True), b, trivial_match_fix(inner))
        )
}
```

## Matches that give back the scrutinee

`needless_match` fires on a `match` each of whose arms gives back the
value it matches: `E::V => E::V`, for a variant without a payload, or
`E::V(a, b) => E::V(a, b)`, whose body builds the variant that its
pattern names, with the pattern's binders, in order and none of them `_`,
written the same as its arguments. The variants are compared as they
resolve, so `V`, brought into scope by `use`, is `E::V`. An arm with an
or-pattern or a [guard](../../Lang/Expressions.md#matches) gives back
nothing, the second since where its guard fails, a later arm gives the
value, and a `_` arm gives back its value only if
its body is written the same as the scrutinee. It does not fire where
[`trivial_match`](#trivial-matches) does, whose fix is the body. It is
fixable: the fix replaces the `match` with its scrutinee, which keeps the
text it is written with, but for parentheses around it, and is put in
parentheses where [fixes need them](../../Lint.md#parentheses-in-fixes): `t = match (s) {
...}` becomes `t = s`.

The `match` has the value of the body of the first arm that matches.
`E::V(a, b)` matches only a scrutinee that is `V` with the payload `a` and
`b`, so the body `E::V(a, b)` is the scrutinee, as is the body of a `_`
arm written the same as it. The `match` and its scrutinee have the same
type, since each arm builds a value of the scrutinee's enumeration. The
fix evaluates the scrutinee where the `match` did, under its guard, and
only drops the bodies, which index nothing, so no guard is weaker.
`lint::needless_match` states when it fires:

```fren
set_option fren.evidence "enumerated" in
pub proc needless_match(
    given_back?,         -- each arm but `_` gives back the variant it matches, with its binders in order
    wildcard?,           -- there is a `_` arm
    scrutinee_back?,     -- the `_` arm's body is written the same as the scrutinee
    trivial?,            -- `trivial_match` fires on the `match`
): (det fires?) {
    ensure rule: fires? iff (given_back? and (not wildcard? or scrutinee_back?) and not trivial?)
}
```

## Trivial guards

`trivial_guard` fires on a [guard](../../Lang/Expressions.md#matches) of
a `match` arm, or of an arm of a [table over a
scrutinee](../../Lang/Expressions.md#tables-over-a-scrutinee), that is,
without parentheses, the literal `true` or `false`. An arm whose guard is
`true` is taken wherever its pattern matches and no earlier arm is taken,
as it is without the guard. An arm whose guard is `false` is never taken:
it is passed over everywhere, as an arm whose pattern does not match is,
so the arms after it are tried as if it were not there. The
[reachability check](../../Check.md#reachability) reports such an arm
too, but only with the solver; the lint says why without it. It is
reported at the guard, and it is fixable:

- The fix of `true` removes the guard, from the end of the arm's pattern.
- The fix of `false` removes the arm: up to the next arm, or, for the last
  arm, from the end of the arm before it, with the comma between them.

Either fix is given only where the [static
rules](../../Lang/Expressions.md#matches) accept the `match` after it, so
that the fix never makes an error. The static rules count an arm with a
guard as if it had none for exhaustiveness, but not for reachability: an
arm with a guard hides nothing from the arms after it. So without the
guard `true`, an arm after it can be unreachable (`F0318`), as `E::A`
after `E::A if true`, and without the arm whose guard is `false`, the
`match` can be no longer exhaustive (`F0317`). Neither fix is given where
the text it removes has a comment, which it would drop. Clippy has no
such lint; `trivial_guard` is in `complexity`, as `redundant_guards` is.

`lint::trivial_guard` states when it fires on an arm, and its fix, from
the arm's guard, whether its pattern matches a value of the scrutinee,
and what the static rules say of the `match` after the fix, and checks
that the fix keeps what the arm does at that value, as
[`lang::guarded_match`](../../Lang/Expressions.md#matches) reads it: the
guard `true` changes nothing, and an arm whose guard is `false` is never
the one taken, so the `match` takes the arm it takes without it:

```fren
-- A guard as `trivial_guard` reads it, without the parentheses around it:
-- none, the literal `true` or `false`, or another expression, with its
-- value at the scrutinee's value.
pub enum Guard { Absent, Literal(Bool), Other(Bool) }

-- What `trivial_guard`'s fix does.
pub enum GuardFix { Unchanged, DropGuard, DropArm }

pub fn guard_holds?(g: Guard) := match g {
    Guard::Absent => true,
    Guard::Literal(b?) => b?,
    Guard::Other(b?) => b?,
}

-- What an arm does at a value of the scrutinee (`lang::ArmAt`), from
-- whether its pattern matches the value, and its guard.
pub fn arm_at(matches?, g: Guard): lang::ArmAt := if not matches? then lang::ArmAt::NoMatch
    else if guard_holds?(g) then lang::ArmAt::Taken else lang::ArmAt::GuardFails

pub proc trivial_guard(
    guard: Guard,            -- the arm's guard
    matches?,                -- the arm's pattern matches a value of the scrutinee
    accepted?,               -- the static rules accept the `match` after the fix (`lang::match_arms`)
    commented?,              -- the text that the fix removes has a comment
): (det fires?, det fix: GuardFix) {
    ensure rule: fires? iff guard is Guard::Literal(_)
    ensure fixed: fix = (if not fires? or not accepted? or commented? then GuardFix::Unchanged
        else if guard = Guard::Literal(true) then GuardFix::DropGuard else GuardFix::DropArm)

    -- Without the guard, the arm does what it did.
    expect drop_guard: when fix = GuardFix::DropGuard, arm_at(matches?, guard) = arm_at(matches?, Guard::Absent)
    -- The arm is never taken, so the arms after it are tried, as without it.
    expect drop_arm: when fix = GuardFix::DropArm, arm_at(matches?, guard) != lang::ArmAt::Taken
    expect other_kept: when guard is Guard::Absent | Guard::Other(_), fix = GuardFix::Unchanged
}
```

`lint::trivial_guard_dropped` checks the fix of `false` in a `match`:
at every value of the scrutinee, the arm taken, the first whose pattern
matches and whose guard holds (`lang::guarded_match`), is the one taken
without an arm whose guard is `false`, for every `match` of up to four
arms:

```fren
-- An arm at a value of the scrutinee: whether its pattern matches it, and
-- its guard.
pub struct ArmGuard { matches?, guard: Guard }

pub fn taken_at?(arms: Seq<ArmGuard>, s: Slot) := pos(s) < arms.len
    and arm_at(arms[pos(s)].matches?, arms[pos(s)].guard) = lang::ArmAt::Taken

-- Whether arm `s` is the arm taken, of the arms but `k` where `skip?`.
pub fn first_taken?(arms: Seq<ArmGuard>, s: Slot, k: Slot, skip?) := taken_at?(arms, s) and not (skip? and s = k)
    and (forall (r: Slot), when pos(r) < pos(s) and not (skip? and r = k), not taken_at?(arms, r))

proc trivial_guard_dropped(arms: Seq<ArmGuard>, k: Slot) {
    assume size: arms.len <= 4
    assume dropped: pos(k) < arms.len and arms[pos(k)].guard = Guard::Literal(false)

    expect same_arm: forall (s: Slot), first_taken?(arms, s, k, false) iff first_taken?(arms, s, k, true)
}
```

The refinements below check the fix of `true` on one example. An
example of `false` would fail the reachability check, whose finding the
lint repeats, so `lint::trivial_guard_dropped` is that fix's claim:

```fren
pub enum Mode { Idle, Run(Int), Halt }

set_option fren.lint.trivial_guard "allow" in
pub proc trivial_guard_written(m: Mode): (det v: Int) {
    out v := match m {
        Mode::Idle => 1,
        Mode::Run(n) if true => n,
        _ => 0,
    }
}

pub proc trivial_guard_fixed(m: Mode): (det v: Int) {
    out v := match m {
        Mode::Idle => 1,
        Mode::Run(n) => n,
        _ => 0,
    }
}

expect trivial_guard_sound(m: lint::Mode) {
    use lint
    call concrete := trivial_guard_fixed(m)
    refines concrete trivial_guard_written(m)
}
expect trivial_guard_complete(m: lint::Mode) {
    use lint
    call concrete := trivial_guard_written(m)
    refines concrete trivial_guard_fixed(m)
}
```

### Trivial guards, over the syntax of the semantics

In the [syntax of the semantics](../../Lang/Semantics.md#abstract-syntax),
an arm of a `match` is `Match(s, p, g, b, rest)`, where `rest` is the
`match` of the arms after it, and an arm without a guard has the guard
`true` ([Derived forms](../../Lang/Semantics.md#derived-forms)). So the
guard `true` elaborates away: the arm with it and the arm without it are
one expression, and the fix that drops it writes the same expression.
`trivial_guard_fires?` fires on the guard `false`, and its fix is `rest`.
That is a rewrite, as [Fixes as rewrites](../Rewrites.md) states for
every such lint:

```fren
pub fn trivial_guard_fires?<V>(e: lang::Expr<V>) := match e {
    lang::Expr::Match(_, _, g, _, _) => g = lang::Expr::Literal(lang::Value::False),
    _ => false,
}

pub fn trivial_guard_fix<V>(e: lang::Expr<V>): lang::Expr<V> := match e {
    lang::Expr::Match(_, _, g, _, rest) => if g = lang::Expr::Literal(lang::Value::False) then rest else e,
    _ => e,
}

-- An arm's guard as elaborated: `true` where it has none, the literal, or
-- `g`, the guard written otherwise.
fn guard_of<V>(guard: Guard, g: lang::Expr<V>): lang::Expr<V> := match guard {
    Guard::Absent => lang::Expr::Literal(lang::Value::True),
    Guard::Literal(b?) => lang::Expr::Literal(lang::truth(b?)),
    Guard::Other(_) => g,
}
```

`lint::trivial_guard` binds this to the linter. The linter reads a guard
without the parentheses around it, so a guard that it reads as another
expression does not elaborate to a literal (`plain`). For every guard
but `true`, it fires exactly where `trivial_guard_fires?` does. On
`true`, the function does not fire, and the linter's fix drops a guard
that elaborates away. Where the linter drops the arm, the fix is what
`trivial_guard_fix` writes. That the front ends read the guard so, and
what the fix removes from the text, are trusted, and checked by the ui
tests in `test/ui/lints/guards.fren`:

```fren
expect trivial_guard_elaborated(
    guard: Guard,
    matches?,
    accepted?,
    commented?,
    s: lang::Expr<lang::Id>,
    p: lang::Pattern<lang::Id>,
    g: lang::Expr<lang::Id>,
    b: lang::Expr<lang::Id>,
    rest: lang::Expr<lang::Id>,
) {
    use lang::Expr::{Literal, Match}

    assume plain: not (g is Literal(lang::Value::True) | Literal(lang::Value::False))

    call t := trivial_guard(guard, matches?, accepted?, commented?)

    let arm: lang::Expr<lang::Id> := Match(s, p, guard_of(guard, g), b, rest)

    expect fires: when guard != Guard::Literal(true), t.fires? iff trivial_guard_fires?(arm)
    expect true_guard: when guard = Guard::Literal(true), t.fires? and not trivial_guard_fires?(arm)
    expect drop_arm: when t.fix = GuardFix::DropArm, trivial_guard_fix(arm) = rest
    expect drop_guard: when t.fix = GuardFix::DropGuard, Match(s, p, guard_of(Guard::Absent, g), b, rest) = arm
}
```

Where it fires, the fix [agrees](../Meaning.md#fixes-that-agree) with the
`match`, in every interpretation and environment. Where the scrutinee is
well-defined, the arm whose pattern matches it evaluates its guard,
`false`, and goes on to `rest`, as the arm whose pattern does not match
does. Elsewhere the `match` is undefined. `src/Impls/Rewrites.lean`
proves this in Lean, for every expression, interpretation and
environment, as it proves the other rewrites; `fren check` tests it:

```fren
set_option fren.evidence "random" in
pub proc trivial_guard_keeps_meaning(e: lang::Expr<lang::Id>, i: lang::Interp, env: lang::Env) {
    ensure agrees: when trivial_guard_fires?(e),
        agrees?(
            lang::eval(i, env, trivial_guard_fix(e)),
            lang::eval(i, env, e)
        )
}
```

The fix writes `rest`, an operand. Once the operands are fixed, it does
not fire, so the fix leaves nothing to fix. The fix alone need not. The
fix of two arms whose guards are `false` is the second, which fires
again (`kept`). And a `match` around it may start firing once it is
fixed: an arm whose guard is a `match` whose only arm has the guard
`false`, and whose `rest` is `false`, does not fire, but the fix of its
guard makes the guard `false` (`around`):

```fren
expect trivial_guard_refires(
    s: lang::Expr<lang::Id>,
    p: lang::Pattern<lang::Id>,
    q: lang::Pattern<lang::Id>,
    b: lang::Expr<lang::Id>,
    c: lang::Expr<lang::Id>,
    r: lang::Expr<lang::Id>,
) {
    use lang::Expr::{Literal, Match}
    use lang::Value::False

    let inner: lang::Expr<lang::Id> := Match(s, q, Literal(False), c, Literal(False))

    expect kept: trivial_guard_fires?(
        trivial_guard_fix(
            Match(s, p, Literal(False), b, Match(s, q, Literal(False), c, r))
        )
    )
    expect around: not trivial_guard_fires?(Match(s, p, inner, b, r))
        and trivial_guard_fires?(Match(s, p, trivial_guard_fix(inner), b, r))
}
```

## Redundant guards

`redundant_guards` fires on a guard that is, without parentheses, `x = v`
or `v = x`, where `x` is a binder of its arm's pattern and `v` is a value
that a pattern writes: an integer literal, negated or not, `true`,
`false`, a string literal, or a variant without a payload. A
[nested pattern](../../Lang/Patterns.md#kinds-of-pattern) with `v` in
place of `x` matches exactly the values that the pattern matches and the
guard lets through: `Shape::Circle(r) if r = 0` is `Shape::Circle(0)`.
A constant is not a pattern, so `x = LIMIT` is left alone, and so are a
variable and any other expression. It is Clippy's `redundant_guards`,
also in `complexity`. It fires only where the static rules accept the
`match` with the new pattern and without the guard: an arm with a guard
hides nothing from the arms after it, and one without it can, so with
`Shape::Circle(0)` an arm `Shape::Circle(0)` after it would be
unreachable (`F0318`). It does not fire on an arm with an or-pattern,
whose alternatives each bind the name.

It is reported at the guard, and it is fixable. Fren has no `@`
patterns, which would keep the name bound as well, so the fix writes `v`
in place of `x` in the pattern, and removes the guard. Where the body
mentions `x`, which is then `v` wherever the arm is taken, the fix also
writes `v` in place of each mention, a negative integer in parentheses.
It writes a variant by the path that names it from the arm, as
[`wildcard_single_variant`](../Pedantic/Matches.md#arms) does, and an
integer as its value. There is no fix where the arm's pattern or guard
has a comment, which it would drop, or where a mention of `x` in the
body is one that a value cannot replace: `x!`, which declares the name
again; `x.f`, `x(` and `x[`; `x :=`; one between `{` or `,` and `,` or
`}`, which may be a field of a record literal written with its name
alone; and any mention in a body with a comment, which may mention it in
prose. The lint finds the mentions as `collapsible_match` does, as names
outside string literals and comments that are not a path's later segment
or a field.

`lint::redundant_guards` states when it fires and its new pattern, over
the [model of patterns](../Style/Matches.md#patterns-as-the-lints-see-them),
where a value that a pattern writes, in a payload too, is an integer,
and checks the fix's meaning: the new pattern matches exactly the
values that the old one matches with the guard's comparison holding, and
the body, with `v` in place of its mention of `x`, has the value it had
there:

```fren
-- The operand of a guard `x = v` that is not the binder: a value that a
-- pattern writes, or another expression, such as a constant, with its
-- value.
pub enum GuardValue { Written(Int), Other(Int) }

pub fn guard_value(v: GuardValue): Int := match v {
    GuardValue::Written(c) => c,
    GuardValue::Other(c) => c,
}

-- `l` with the literal `c` in place of the binder named `n`.
pub fn leaf_with(l: Leaf, n: Int, c: Int): Leaf := match l {
    Leaf::Binder(k, _) => if k = n then Leaf::Lit(c) else l,
    _ => l,
}

pub fn pat_with(p: Pat, n: Int, c: Int): Pat := match p {
    Pat::Binder(k, _) => if k = n then Pat::Lit(c) else p,
    Pat::Variant(t, l, m) => Pat::Variant(t, leaf_with(l, n, c), leaf_with(m, n, c)),
    _ => p,
}

-- Whether the pattern `p` binds the name `n`.
pub fn binds_name?(p: Pat, n: Int) := n >= 0 and match p {
    Pat::Binder(k, _) => k = n,
    Pat::Variant(_, l, m) => leaf_name(l) = n or leaf_name(m) = n,
    _ => false,
}

-- The value that the name `n`, a binder of `p`, has where `p` matches `x`.
pub fn bound_value(p: Pat, n: Int, x: Val): Int := match p {
    Pat::Variant(_, l, _) => if leaf_name(l) = n then x.a else x.b,
    _ => x.n,
}

-- The body `b` with the integer `c` in place of its mention of `n`.
pub fn body_with(b: Body, n: Int, c: Int): Body := if body_names?(b, n) then Body {
    form := b.form + c,
    uses := Use::Nothing,
} else b

pub proc redundant_guards(
    pattern: Pat,            -- the arm's pattern
    name: Int,               -- the name that the guard compares
    value: GuardValue,       -- what the guard compares it with
    accepted?,               -- the static rules accept the `match` with the new pattern and without the guard
    body: Body,              -- the arm's body
    x: Val,                  -- a value of the scrutinee
    o: Int,                  -- the value of a name outside the pattern
): (det fires?, det fixed: Pat) {
    -- The binders of a pattern have distinct names (`lang::distinct_names`).
    assume distinct: match pattern {
        Pat::Variant(_, l, m) => leaf_name(l) < 0 or leaf_name(l) != leaf_name(m),
        _ => true,
    }

    ensure rule: fires? iff (binds_name?(pattern, name) and value is GuardValue::Written(_) and accepted?)
    ensure fix: fixed = (if fires? then pat_with(pattern, name, guard_value(value)) else pattern)

    -- The new pattern matches where the pattern and the guard did.
    expect same_values: when fires?,
        pat_matches?(fixed, x) iff (pat_matches?(pattern, x) and bound_value(pattern, name, x) = guard_value(value))
    -- There, the body with the value in place of the binder means what it did.
    expect same_body: when fires? and pat_matches?(fixed, x),
        body_value(body, name, bound_value(pattern, name, x), -1, 0, -1, 0, o)
        = body_value(
            body_with(body, name, guard_value(value)),
            -1,
            0,
            -1,
            0,
            -1,
            0,
            o
        )
    expect constant_kept: when value is GuardValue::Other(_), not fires?
}
```

The refinements below check the fix on one example, with a literal, a
variant, and a body that mentions the binder:

```fren
pub enum Strength { Low, High }
pub enum Probe { Read(Strength, Int), Off }

set_option fren.lint.redundant_guards "allow" in
pub proc redundant_guards_written(p: Probe, k: Int): (det v: Int, det w: Int) {
    out v := match p {
        Probe::Read(_, n) if n = 0 => 1,
        Probe::Read(l, n) if l = Strength::High => n + k,
        _ => 0,
    }
    out w := match k {
        j if j = -3 => j + 1,
        _ => 2,
    }
}

pub proc redundant_guards_fixed(p: Probe, k: Int): (det v: Int, det w: Int) {
    out v := match p {
        Probe::Read(_, 0) => 1,
        Probe::Read(Strength::High, n) => n + k,
        _ => 0,
    }
    out w := match k {
        -3 => (-3) + 1,
        _ => 2,
    }
}

expect redundant_guards_sound(p: lint::Probe, k: Int) {
    use lint
    call concrete := redundant_guards_fixed(p, k)
    refines concrete redundant_guards_written(p, k)
}
expect redundant_guards_complete(p: lint::Probe, k: Int) {
    use lint
    call concrete := redundant_guards_written(p, k)
    refines concrete redundant_guards_fixed(p, k)
}
```
