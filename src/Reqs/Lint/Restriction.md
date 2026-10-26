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

pub comp allow_attributes {
    in requested: Level  -- the level that the `set_option` sets
    in unfulfilled?      -- it sets `unfulfilled_lint_expectations` itself
    pub det out fires?
    pub det out fixed?   -- the fix applies

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
no arm without a guard names. The fix replaces
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
pub comp wildcard_enum_match_arm {
    in wildcard?         -- the arm is `_`
    in n_unnamed: Int    -- variants it matches that no pattern names, written as the other arms write theirs, `V` or `E::V`
    pub det out fires?
    pub det out fixed?   -- it has a fix

    assume counts: n_unnamed >= 0

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
pub comp needless_raw_strings {
    in raw?              -- the literal is raw
    in backslash?        -- its contents have a `\`
    in quote?            -- they have a `"`
    pub det out fires?

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
pub comp non_ascii_literal {
    in code: Int         -- the code point of a character of the literal
    pub det out fires?
    pub det out escapable?  -- `\uHHHH` can write it

    assume code_point: code >= 0

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

`module_name_repetitions` fires on an item, a module, a component, an
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
pub comp module_name_repetitions {
    in n_words: Int      -- the words of the item's name
    in n_module_words: Int  -- the words of its module's last segment
    in contains?         -- the item's words have the module's, one after another, in any case
    pub det out fires?

    assume counts: n_words >= 0 and n_module_words >= 0

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
pub comp min_ident_chars {
    in name: String      -- the declared name, without a final `?`
    pub det out fires?

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
is for its [trigger](../Lang/Components.md#triggers). `lint::absolute_paths` states when it fires:

```fren
pub comp absolute_paths {
    in n_segments: Int   -- the path's segments
    pub det out fires?

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
pub comp precedence {
    use self::InfixOp::{And, Inter, Join, Minus, Or, Union}
    in outer: InfixOp    -- the operator
    in inner: InfixOp    -- the outermost operator of its operand
    in parenthesized?    -- the operand is in parentheses
    pub det out fires?

    ensure rule: fires? iff (not parenthesized?
        and ((outer = Or and inner = And) or (outer in {Union, Minus} and inner in {Inter, Join})))
}
```

## The order of members

`arbitrary_source_item_ordering` fires on a component whose members are
not in this order: `use`, `in`, `out`, defined or not, `assume`, `inst`,
`ensure`, `expect`, then `cover`. Only kinds are ordered: the members of one kind may
be in any order. A `set_option fren.evidence ... in` is part of the member
after it. The components of these chapters, and of the others, write
their members in this order. When the lint was added, all but two did:
`cli::logic` had an `assume` between two `ensure`s, and
`lang::punctuator_end` a defined output after an `assume`. Both are now
in order, which changes what neither means. Like Clippy's lint of the
same name, which orders the items of a module, it is in `restriction`:
Fren accepts members in any order, and a component can read better with a
constraint next to the variable it is about. The message is reported once for each
component, at the first member written after one of a later kind, and
names both kinds.

Order matters to what a component means in one place only: an instance's
binding may mention another instance's variable only if that instance is
declared earlier (see [Instance variables](../Lang/Instances.md#instance-variables)).
Elsewhere, a member may mention a variable declared after it. The fix
puts the members in order, and keeps the members of each kind in the order
they are written in, so it keeps the instances in order, and with them
what the component means. It rewrites no expression, so it keeps every
guard. It also never leaves a mention above what it mentions, so that the
component reads from the top down: it is offered only when, in the new
order, each variable or instance that a defined output's definition or an
instance's binding mentions is declared before it. So `inst w` before
`out y: Int := w.z` is reported, but not fixed, since `out` comes before
`inst`.

Each member moves with the whole lines it is written on: from the line
after the previous member, or after the `{`, so with the comments above
it, to the end of its last line, so with a comment after it there, and
with the blank lines before it, but for the member that comes first, which
gives its blank lines to the member written first. The fix is offered only
when each member starts its line, and only a comment follows it on its
last one.

`lint::rank` is a kind's place in the order. `lint::arbitrary_source_item_ordering`
states when it fires, on two members written one after the other, and
`lint::mention_kept` when the new order keeps a mention after what it
mentions:

```fren
pub enum MemberKind { Use, Input, Output, Assumption, Instance, Guarantee, Expectation, Cover }

pub fn rank(kind: MemberKind): Int := match kind {
    MemberKind::Use => 0,
    MemberKind::Input => 1,
    MemberKind::Output => 2,
    MemberKind::Assumption => 3,
    MemberKind::Instance => 4,
    MemberKind::Guarantee => 5,
    MemberKind::Expectation => 6,
    MemberKind::Cover => 7,
}

pub comp arbitrary_source_item_ordering {
    in first: MemberKind     -- a member
    in second: MemberKind    -- the member written after it
    pub det out fires?

    ensure rule: fires? iff rank(first) > rank(second)

    expect same_kind: when first = second, not fires?
}

pub comp mention_kept {
    in mentioner: MemberKind     -- a defined output or an instance
    in mentioned: MemberKind     -- what its definition or a binding mentions
    in earlier?                  -- the mentioned member is written before the other
    pub det out kept?

    ensure rule: kept? iff (rank(mentioned) < rank(mentioner) or (rank(mentioned) = rank(mentioner) and earlier?))

    expect instances_in_order: when mentioner = MemberKind::Instance and mentioned = MemberKind::Instance,
        kept? iff earlier?
}
```

The [refinements](../Lang/Refinement.md) below check the fix of a
component with a member of each kind, an instance among them, in reverse
order: a component as written, one as fixed, and a refinement each way, so
that the solver checks that the two meet the same behaviours.

```fren
set_option fren.lint.arbitrary_source_item_ordering "allow" in
pub comp member_order_written {
    expect never_info: shown != Severity::Info
    ensure rule: shown = warned.result
    inst warned: severity { level := Level::Warn }
    assume known: group != Group::Decidability
    pub det out shown: Severity
    in group: Group
}

pub comp member_order_fixed {
    in group: Group
    pub det out shown: Severity
    assume known: group != Group::Decidability
    inst warned: severity { level := Level::Warn }
    ensure rule: shown = warned.result
    expect never_info: shown != Severity::Info
}

refine member_order_sound: member_order_fixed refines member_order_written
refine member_order_complete: member_order_written refines member_order_fixed
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
pub comp single_call_fn {
    in pub?
    in defined?          -- it has a body, `:= e`
    in n_uses: Int       -- paths in its file that resolve to it
    pub det out fires?

    assume counts: n_uses >= 0

    ensure rule: fires? iff (defined? and not pub? and n_uses = 1)

    expect public_never: when pub?, not fires?
}
```
