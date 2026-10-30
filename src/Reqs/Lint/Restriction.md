# Restriction

The lints of the `restriction` group each forbid something that is fine in
general, but that a project may want to rule out, so they are `allow` by
default. A [`pedantic`](Pedantic.md) lint is a judgement that is usually
right, even if it would fire on much that reads well as it is. A
restriction is not a judgement but a rule that a project chooses, such as
writing every string literal in ASCII, and the opposite rule is often as
good. So a project warns of the restrictions it chooses, one by one, as in
`-W non_ascii_literal`; warning of the whole group, `-W restriction`, is
seldom meant. They are ported from Clippy's `restriction` group, but for
`precedence`.

## Allowed lints

`allow_attributes` fires on a `set_option` that sets a lint or a group to
`allow`, as in `set_option fren.lint.glob_imports "allow"`, and is
fixable. The fix sets it to `expect` (see [Expecting
lints](../Lint.md#expecting-lints)), which silences the same messages where
it is in effect, and also makes `unfulfilled_lint_expectations` report the
setting once nothing there needs it. It is reported at the level string,
at the level of `allow_attributes` in effect before the setting, so
`set_option fren.lint.allow_attributes "allow"` is reported too, where the
lint is not allowed already.

The fix changes no guarantee, check, trace or generated declaration,
only which lint messages are reported: where the lint that the setting
allows fires, both levels report nothing, and where it does not, `expect`
adds a warning, `F0706`, which `allow` never gave. That warning is what the
rule asks for, since an `allow` that nothing needs hides the lints of what
is written later. `fren fix` makes its fixes until none is left, so if the
expectation is unfulfilled, the next pass removes the `set_option`, as the
fix of `unfulfilled_lint_expectations` does, which leaves the lint at the
level it had before, where it fired nowhere. For
`unfulfilled_lint_expectations` itself, `expect` means `allow`, so an
expectation of it is never fulfilled: there the lint fires, but has no
fix. `lint::allow_attributes` states this:

```fren
pub mod lint

set_option fren.evidence "enumerated" in
pub proc allow_attributes(
    requested: Level,    -- the level that the `set_option` sets
    unfulfilled?,        -- it sets `unfulfilled_lint_expectations` itself
): (
    det fires?,
    det fixed?,          -- the fix applies
) {
    ensure rule: fires? iff requested = Allow
    ensure fix: fixed? iff (fires? and not unfulfilled?)

    expect only_allow: when requested = Expect, not fires?
}
```

## Wildcard arms

`wildcard_enum_match_arm` fires on the `_` arm without a
[guard](../Lang/Expressions.md#matches) of a
[`match`](../Lang/Expressions.md#matches) on an enumeration whose patterns
are all flat, as [`wildcard_single_variant`](Pedantic/Matches.md#arms) does, and
is fixable. As for that lint, the variants that `_` matches are those that
no arm without a guard names, and it does not fire on a [table over a
scrutinee](../Lang/Expressions.md#tables-over-a-scrutinee) that has an arm
with a guard (see [Arms](Pedantic/Matches.md#arms)). The fix replaces
`_` with an or-pattern of the variants it matches, in the order of their
enumeration, each written as
[`wildcard_single_variant`](Pedantic/Matches.md#arms) writes one: `E::V`, or
`E::V(_, _)` with one `_` for each value of its payload, written as another
pattern of the `match` writes its variant's path, or as `V` or `E::V` if one
of those names it. If one of them has no such path, the lint has no fix. A
variant added to the enumeration later then makes the `match`
non-exhaustive, a static error, rather than being matched by `_` without
notice.

The arm matches the same variants as before, and its body's guard, that no
earlier arm matches, is then the test of those variants, which means the
same, since the `match` is exhaustive and names no variant twice. Where `_`
matches one variant, `wildcard_single_variant` fires too, with the same
fix, and as for it, if `fren fix` also removes an arm that has the body of
the `_` arm (`match_same_arms`), `wildcard_enum_match_arm` is not fixed.
Clippy's `wildcard_enum_match_arm` leaves a `_` of one variant to
`match_wildcard_for_single_variants`, but Fren's counterpart of that is
`pedantic`, which a project may leave allowed. `lint::wildcard_enum_match_arm`
states when it fires, and when it has a fix:

```fren
pub proc wildcard_enum_match_arm(
    wildcard?,           -- the arm is `_`
    n_unnamed: Nat,      -- variants it matches that no pattern names, written as the other arms write theirs, `V` or `E::V`
): (
    det fires?,
    det fixed?,          -- it has a fix
) {
    ensure rule: fires? iff wildcard?
    ensure fix: fixed? iff (wildcard? and n_unnamed = 0)
}
```

## Literals

The level that applies to these lints is the one in effect at the item that
the literal is in, as for [`invisible_characters`](Suspicious/Literals.md#invisible-characters).
Each is reported once for a literal, at it.

`needless_raw_strings` fires on a raw string literal, `r"..."` or
`r#"..."#`, whose contents have no `\` and no `"`, and is fixable. A raw
literal is for contents that would need escapes, but these need none. The
fix is the ordinary literal of the same contents, `"..."`, which has the
same value: without a `\`, it has no escape, and without a `"`, nothing
ends it early (see [Literals](../Lang/Lexical.md#literals)).
`lint::needless_raw_strings` states when it fires:

```fren
set_option fren.evidence "enumerated" in
pub proc needless_raw_strings(
    raw?,                -- the literal is raw
    backslash?,          -- its contents have a `\`
    quote?,              -- they have a `"`
): (det fires?) {
    ensure rule: fires? iff (raw? and not backslash? and not quote?)
}
```

`non_ascii_literal` fires on a string literal that has a character beyond
ASCII, from U+0080 on, and is fixable. Such a character may look like
another, or not display in every font. The fix writes each as an escape,
`\uHHHH`, as the fix of `invisible_characters` does: a raw literal becomes
an ordinary one, with `\\` and `\"` for its `\` and `"`. The value stays
the same. A literal's escapes are only Lean's, of which `\uHHHH`, with four
digits, is the only one beyond `\xHH`, so a character beyond U+FFFF, up to
U+2FFFF, has no escape: Lean has neither `\u{...}` nor surrogate pairs,
which are not characters. A literal with such a character has no fix, and
the message names it. `lint::non_ascii_literal` states which characters it
reports, and which an escape can write, by code point:

```fren
pub proc non_ascii_literal(
    code: Nat,           -- the code point of a character of the literal
): (
    det fires?,
    det escapable?,         -- `\uHHHH` can write it
) {
    ensure rule: fires? iff code >= 128
    ensure escape: escapable? iff code <= 65535

    expect ascii: when code < 128, not fires?
}
```

The literal is fixed when it fires on some character, and each that it
fires on is escapable. A literal with an invisible character is non-ASCII
too, so `invisible_characters` fires on it as well: the two fixes overlap,
and `fren fix` makes one in each pass, until both are made.

## Names

These lints are reported where the name is declared, at the level in
effect there, as the [lints on names](Style.md#names) are, and have no
fix, for the same reason.

`module_name_repetitions` fires on an item, a module, a procedure, an
enumeration, a record, an abstract type, a function, a constant or a
global expectation, whose name's [words](Style.md#names) contain those of
its module's last segment, one after another, in any case, and others,
such as `ClimateMode` and `climate_reading` in the module `climate`: a path
to the item names the module already, as `climate::ClimateMode` does. A
name that is only the module's is left to
[`module_inception`](Style.md#names), for a module, and is a fine name for
another item. Clippy fires only on a public item, and only on a name that
starts or ends with the module's. `lint::module_name_repetitions` states
when it fires:

```fren
pub proc module_name_repetitions(
    n_words: Nat,        -- the words of the item's name
    n_module_words: Nat,    -- the words of its module's last segment
    contains?,           -- the item's words have the module's, one after another, in any case
): (det fires?) {
    ensure rule: fires? iff (contains? and n_words > n_module_words)
}
```

`min_ident_chars` fires on a declared name of one character, without a
final `?`, other than `_`, such as `x` or `a?`: it says little of what it
names. Fren's identifiers never end in `!`, which Clippy also ignores.
Clippy fires on names shorter than its threshold, one by default, and by
default also allows `i`, `j`, `x`, `y`, `z`, `w` and `n`, which Fren does
not. `lint::min_ident_chars` states when it fires:

```fren
pub proc min_ident_chars(
    name: String,        -- the declared name, without a final `?`
): (det fires?) {
    ensure rule: fires? iff (name.len = 1 and name != "_")
}
```

## Long paths

`absolute_paths` fires on a path of three or more segments to an item, or
to a variant, written in an expression, a pattern or a type, such as
`climate::Mode::Heat`, rather than imported by a [`use`](../Lang/Modules.md#use-declarations),
which it never fires on. It has no fix, and its message suggests the `use`
of the item, or for a variant of its enumeration, by its path from the root
module, and how to write the path after it: `use climate::Mode`, then
`Mode::Heat`. Clippy's default limit is two `::`, as here. A leading
`self` counts as a segment, unlike in Clippy, which does not count it:
`self::sensors::Probe` has three. A path is counted once, where it is
written, even where it is elaborated again, as the condition of a `when`
is for its [trigger](../Lang/Procedures.md#triggers). `lint::absolute_paths` states when it fires:

```fren
pub proc absolute_paths(
    n_segments: Int,     -- the path's segments
): (det fires?) {
    assume counts: n_segments >= 1

    ensure rule: fires? iff n_segments >= 3
}
```

## Precedence

`precedence` fires on an `and` that is an operand of an `or` without
parentheses, as in `a? or b? and c?`, and on a `join` or an `inter` that is
an operand of a `union` or a `minus` without them, as in `s minus t inter
u`, and is fixable. The fix puts the operand in parentheses, `a? or (b? and
c?)`, which shows what the precedence already means, so it keeps the
meaning and the guards. `and` binding more tightly than `or` is a near
universal convention, so this is a rule a project chooses, not a mistake;
but there is no such convention from mathematics for `minus` and `inter`.
The fixes of other lints add only the parentheses that
[`lang::operand`](../Lang/Expressions.md#operators) requires, so they can
write `a? or b? and d?`. Fren's own Reqs write these parentheses, so a
project may want the rule too. Clippy's `precedence` is about arithmetic,
shifts and bits, which Fren does not have, and is in its `complexity`
group. `lint::precedence` states when it fires:

```fren
pub proc precedence(
    outer: InfixOp,      -- the operator
    inner: InfixOp,      -- the outermost operator of its operand
    parenthesized?,      -- the operand is in parentheses
): (det fires?) {
    use self::InfixOp::{And, Inter, Join, Minus, Or, Union}

    ensure rule: fires? iff (not parenthesized?
        and ((outer = Or and inner = And) or (outer in {Union, Minus} and inner in {Inter, Join})))
}
```

## The order of members

`arbitrary_source_item_ordering` fires on a procedure whose members are
not in this order: `use`, `assume`, `exists`, `let` and `out`, `call`,
`ensure`, `expect`, then `cover`. Only kinds are ordered: the members of
one kind may be in any order, and a `let` and an `out`, which defines a
result as a `let` defines a private variable, are of one kind. A `set_option
fren.evidence ... in` is part of the member after it. The order reads as
a contract, after the signature, which gives the procedure's parameters
and results: what it assumes of its parameters, then the variables it
chooses or defines, the procedures it calls, and what it guarantees and
claims of them. An `assume` mentions only parameters, so it comes first,
before a definition that relies on it for its definedness, such as `let
y := q[i]`. A call's arguments may mention a `let`, and the guarantees its
variables, so `call` comes between the two, and cover goals, which claim
that a scenario can happen, come last. Like Clippy's lint of the same
name, which orders the items of a module, it is in `restriction`: Fren
accepts members in any order, and a procedure can read better with a
constraint next to the variable it is about. The message is reported once
for each procedure, at the first member written after one of a later
kind, and names both kinds. [`fren fmt`](../Fmt.md) never reorders
members: it changes only the layout, and ordering them is the lint's. The
procedures of these chapters write their members in this order, but for
`lint::unused_bound`, whose definition reads its call, and which expects
the lint.

Order matters to what a procedure means in one place only: a call's
argument may mention another call's variable only if that call is
declared earlier (see [Call variables](../Lang/Calls.md#call-variables)).
Elsewhere, a member may mention a variable declared after it. The fix
puts the members in order, and keeps the members of each kind in the order
they are written in, so it keeps the calls in order, and with them what
the procedure means. It rewrites no expression, so it keeps every guard.
It also never leaves a mention above what it mentions, so that the
procedure reads from the top down: it is offered only when, in the new
order, each variable or call that a definition or a call's argument
mentions is declared before it. So `call w` before `let y: Int := w.z` is
reported, but not fixed, since `let` comes before `call`. A parameter or
a result is declared in the signature, before every member, so a mention
of one is always kept.

Each member moves with the whole lines it is written on: from the line
after the previous member, or after the `{`, so with the comments above
it, to the end of its last line, so with a comment after it there, and
with the blank lines before it, but for the member that comes first, which
gives its blank lines to the member written first. The fix is offered only
when each member starts its line, and only a comment follows it on its
last one.

`lint::rank` is a kind's place in the order. `lint::arbitrary_source_item_ordering`
states the lint over a procedure's members, as written: their kinds, and
the mentions of one member by another's definition or arguments, each by
the two members' positions. It gives whether the lint fires, at which
member, and whether the new order keeps every mention after what it
mentions. Its quantifiers range over positions, unbounded, so it is
outside the [decidable core](../Lang/Decidability.md), and its
implementation is proved in Lean of the lint's code, for every number of
members and mentions. The solver does not decide its own checks, such as
whether it is realizable, over unbounded sequences, so they are checked by
[testing](../Check.md#checking-by-testing).

```fren
pub enum MemberKind { Use, Assumption, Exists, Let, Define, Call, Guarantee, Expectation, Cover }

pub fn rank(kind: MemberKind): Int := match kind {
    MemberKind::Use => 0,
    MemberKind::Assumption => 1,
    MemberKind::Exists => 2,
    MemberKind::Let | MemberKind::Define => 3,
    MemberKind::Call => 4,
    MemberKind::Guarantee => 5,
    MemberKind::Expectation => 6,
    MemberKind::Cover => 7,
}

-- The definition or an argument of the member at `mentioner` mentions the
-- member at `mentioned`.
pub struct Mention { mentioner: Int, mentioned: Int }

set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
pub proc arbitrary_source_item_ordering(
    kinds: Seq<MemberKind>,      -- the members' kinds, in the order written
    mentions: Set<Mention>,
): (
    det fires?,
    det first: Int,              -- where it is reported, or `-1`
    det keeps_mentions?,         -- in order, each mention comes after what it mentions
) {
    assume positions: forall (m: Mention), when m in mentions,
        0 <= m.mentioner < kinds.len and 0 <= m.mentioned < kinds.len

    -- Some member is written after one of a later kind.
    ensure rule: fires? iff (exists (i: Int), 0 < i < kinds.len and rank(kinds[i - 1]) > rank(kinds[i]))
    -- The first such member; the members before it are in order.
    ensure at_first: if fires?
        then 0 < first < kinds.len and rank(kinds[first - 1]) > rank(kinds[first])
        and (forall (i: Int), when 0 < i < first, rank(kinds[i - 1]) <= rank(kinds[i]))
        else first = -1
    -- In order, a member comes before another of a later kind, and before a
    -- later one of its own kind.
    ensure kept: keeps_mentions? iff (forall (m: Mention), when m in mentions and m.mentioner != m.mentioned,
        rank(kinds[m.mentioned]) < rank(kinds[m.mentioner])
        or (rank(kinds[m.mentioned]) = rank(kinds[m.mentioner]) and m.mentioned < m.mentioner))
}
```

The [refinements](../Lang/Refinement.md) below check the fix of a
procedure with a member of each kind, in reverse order: a procedure as
written, one as fixed, and a refinement each way, so that the solver
checks that the two meet the same behaviours.

```fren
set_option fren.lint.arbitrary_source_item_ordering "allow" in
pub proc member_order_written(group: Group): (det shown: Severity, det error?) {
    cover warns: shown = Warning
    expect never_info: shown != Info
    ensure rule: shown = warned.result and (spare? iff error?)
    call warned := severity(Level::Warn)
    out error? := is_error?
    let is_error? := shown = Error
    exists spare?
    assume known: group != Group::Decidability
    use view::Severity::{Error, Info, Warning}
}

pub proc member_order_fixed(group: Group): (det shown: Severity, det error?) {
    use view::Severity::{Error, Info, Warning}
    assume known: group != Group::Decidability
    exists spare?
    let is_error? := shown = Error
    out error? := is_error?
    call warned := severity(Level::Warn)
    ensure rule: shown = warned.result and (spare? iff error?)
    expect never_info: shown != Info
    cover warns: shown = Warning
}

-- `spare?` and `is_error?` are private to each, so each refinement binds them.
set_option fren.lint.assertions_on_constants "allow" in
set_option fren.lint.eq_op "allow" in
set_option fren.lint.absurd_extreme_comparisons "allow" in
expect member_order_sound(group: lint::Group) {
    use lint
    use view
    assume spec_known: (group) != lint::Group::Decidability
    call concrete := member_order_fixed(group)
    call warned := severity(Level::Warn)
    expect rule: (concrete.shown) = warned.result and ((concrete.error?) iff (concrete.error?))
    expect is_error_definition: (concrete.error?) = ((concrete.shown) = view::Severity::Error)
    expect error_definition: concrete.error? = (concrete.error?)
}
set_option fren.lint.assertions_on_constants "allow" in
set_option fren.lint.eq_op "allow" in
set_option fren.lint.absurd_extreme_comparisons "allow" in
expect member_order_complete(group: lint::Group) {
    use lint
    use view
    assume spec_known: (group) != lint::Group::Decidability
    call concrete := member_order_written(group)
    call warned := severity(Level::Warn)
    expect rule: (concrete.shown) = warned.result and ((concrete.error?) iff (concrete.error?))
    expect is_error_definition: (concrete.error?) = ((concrete.shown) = view::Severity::Error)
    expect error_definition: concrete.error? = (concrete.error?)
}
```

## Functions applied once

`single_call_fn` fires on a private [defined
function](../Lang/Items.md#defined-functions) that exactly one path in its
file applies. Uses are counted as for [dead code](Unused.md#dead-code): a
function is used by applying it, and only uses in the same file count, not
those in Lean code, nor in later files that enter its module. A function
applied once names nothing that is shared, and its body could be written
in place of the application, with the arguments in place of the
parameters. Like Clippy's lint of the same name, it is in `restriction`: a
function can name a computation well even where it is applied once. The
message is reported at the function's name, at the end of the file, and
suggests writing its body in place. There is no fix: it would have to put
each argument in place of its parameter, in parentheses where it needs
them, and remove the function, which later files that enter its module
may also apply.
`lint::single_call_fn` states when it fires:

```fren
pub proc single_call_fn(
    pub?,
    defined?,            -- it has a body, `:= e`
    n_uses: Nat,         -- paths in its file that resolve to it
): (det fires?) {
    ensure rule: fires? iff (defined? and not pub? and n_uses = 1)

    expect public_never: when pub?, not fires?
}
```
