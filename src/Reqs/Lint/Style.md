# Style

The lints of the `style` group find a clearer way to write the same
thing, and `fren fix` fixes each of them but the lints of
[names](#names), whose fixes would rename, and `assertions_on_constants`,
which finds a constraint that says nothing about the variables.
Its subchapters have the lints of [pattern tests and chained
comparisons](Style/Comparisons.md), of [pattern tests written
out](Style/PatternTests.md), of [natural numbers](Style/Naturals.md)
and of [records](Style/Records.md).

## Glob imports

`use E::*` brings every variant of `E` into scope, including variants
added later, so a reader cannot tell where a name comes from, and adding a
variant to one enumeration can make a name in another module
[ambiguous](../Lang/Modules.md#resolution). `glob_imports` reports every
`use ...::*`. Its message suggests importing by name the variants the file
uses through it, or writing them qualified, as in `Mode::Heat`.

A glob import that is unused is reported by both `glob_imports` and
[`unused_imports`](Unused.md#unused-imports).

## Conditionals

`unless_not` and `collapsible_when` report a conditional that reads more
simply written another way, in the same places as
[`nonminimal_bool`](Complexity.md#simpler-bool-expressions), and suggest the rewritten
form, which keeps the meaning and the guards (see
[Expressions](../Lang/Expressions.md#sequences)). A condition is a
*negation* if it is `not A` or `a != b`; the condition it negates is `A`,
or `a = b`. [`if_not_else`](Pedantic.md#negated-conditions), in the
`pedantic` group, is a third such lint.

- `unless_not` fires on `unless C, D` where `C` is a negation: `unless not
  A, D` becomes `when A, D`, and `unless a != b, D` becomes `when a = b,
  D`. It does not fire on any other condition, such as `unless x < 3, D`:
  saying when `D` need not hold is what `unless` is for. `D` is guarded by
  `not C` before, and by the condition `C` negates after, which is the
  same.
- `collapsible_when` fires on a conditional whose body is a conditional
  with the same keyword: `when A, when B, D` becomes `when A and B, D`, and
  `unless A, unless B, D` becomes `unless A or B, D`. It does not fire on a
  nest of `when` and `unless`, such as `unless A, when B, D`, which keeps
  apart an exception and a case, as `modules::resolve` does (see
  [Resolution](../Lang/Modules.md#resolution)). The guards are the same: `B`
  is guarded by `A` in `A and B`, as it is in `when A, when B, D`, and `D`
  by `A` and `B`. For `unless`, `B` is guarded by `not A` in `A or B`, and
  `D` by `not A` and `not B`, which is `not (A or B)`.

`A`, `B` and the other operands keep their text, in parentheses where
[fixes need them](../Lint.md#parentheses-in-fixes), as for `nonminimal_bool`: `unless a? iff b?, unless c?, d?` becomes
`unless (a? iff b?) or c?, d?`. That each rewritten form means what the
expression means is proved in Lean, over the model of expressions of
[`nonminimal_bool`](Complexity.md#simpler-bool-expressions), with each lint's rules
alone, so that the fix of one lint makes none of the changes another
suggests.

What these lints and `if_not_else` look at in an operand is its outermost
operator, `lint::Head`: `Not` for `not A`, `Unequal` for `a != b`, `If`,
`When` and `Unless` for the conditionals, and `Other` for the rest.
`lint::unless_not` and `lint::collapsible_when` state when they fire:

```fren
pub mod lint

pub enum Head { Not, Unequal, If, When, Unless, Other }

pub proc unless_not(
    unless?,             -- the conditional is `unless`, rather than `when`
    condition: Head,
): (det fires?) {
    ensure rule: fires? iff (unless? and condition in {Head::Not, Head::Unequal})

    expect other: when condition = Head::Other, not fires?
}

set_option fren.evidence "enumerated" in
pub proc collapsible_when(
    unless?,             -- the conditional is `unless`, rather than `when`
    body: Head,
): (det fires?) {
    ensure rule: fires? iff body = (if unless? then Head::Unless else Head::When)

    expect mixed: when unless? and body = Head::When, not fires?
}
```

## Empty collections

`length_zero` fires on a comparison of a string's or sequence's `len` with
`0` or `1` that says that it is empty, or that it is not. A length is never
negative, so `n = 0`, `n <= 0` and `n < 1` each say that it is empty, and
become `s = ""`, or `q = []`, and `n != 0`, `n > 0` and `n >= 1` each say
that it is not, and become `s != ""`. So does each with the length on the
right: `0 < s.len` is `s.len > 0`. `card_zero` is the same for a set's or
relation's `card`, with `{}`. Both are fixable. The fix keeps the
receiver's text, without the parentheses a receiver may need, and puts it
in parentheses where [fixes need them](../Lint.md#parentheses-in-fixes), so
`(a ++ b).len = 0` becomes `a ++ b = ""`. Other comparisons with `0`
or `1` are left as they are, and so is a comparison within a [chained
comparison](../Lang/Expressions.md#chained-comparisons), where the fix
would break the chain; those that always hold or never do, such as
`n >= 0`, are
[`absurd_extreme_comparisons`'s](Suspicious/Comparisons.md).
`lint::Comparison` is the comparison operators, and `lint::length_zero`
states which comparisons they fire on:

```fren
pub enum Comparison { Eq, Ne, Lt, Le, Gt, Ge }

use self::Comparison::{Eq, Ge, Gt, Le, Lt, Ne}

pub proc length_zero(
    op: Comparison,
    bound: Int,          -- the literal compared with
    left?,               -- the length is the left operand, rather than the right
): (
    det fires?,
    det empty?,          -- the fix says that it is empty, rather than not
) {
    ensure rule: fires? iff (if left?
        then (bound = 0 and op in {Eq, Ne, Le, Gt}) or (bound = 1 and op in {Lt, Ge})
        else (bound = 0 and op in {Eq, Ne, Ge, Lt}) or (bound = 1 and op in {Gt, Le}))
    ensure fix: empty? iff (if left? then op in {Eq, Le, Lt} else op in {Eq, Ge, Gt})

    expect not_negative: when op = Lt and bound = 0 and left?, not fires?
}
```

Each fix is exact: where the lint fires, the comparison of a length `n`
holds exactly when the fix does, `n = 0` if it says that the collection is
empty and `n != 0` if not. `compares?` is the value of a comparison:

```fren
fn compares?(op: Comparison, a: Int, b: Int) := match op {
    Eq => a = b,
    Ne => a != b,
    Lt => a < b,
    Le => a <= b,
    Gt => a > b,
    Ge => a >= b,
}

proc length_zero_exact(
    op: Comparison,
    bound: Int,
    left?,
    n: Nat,              -- the length
) {
    call p := length_zero(op, bound, left?)

    expect exact: when p.fires?,
        compares?(op, if left? then n else bound, if left? then bound else n) iff (p.empty? iff n = 0)
}
```

`lint::length_zero_keeps_meaning` states the fixes as laws, for strings,
sequences, sets and relations (see [Fixing lints](../Lint.md#fixing-lints)):

```fren
set_option fren.lint.length_zero "expect" in
set_option fren.lint.card_zero "expect" in
pub proc length_zero_keeps_meaning(s: String, q: Seq<Int>, t: Set<Int>, r: Rel<Bool, Bool>) {
    expect string_length_zero: ((s.len = 0) iff s = "") and ((s.len <= 0) iff s = "") and ((s.len > 0) iff s != "")
    expect sequence_length_zero: ((q.len = 0) iff q = []) and ((q.len <= 0) iff q = []) and ((q.len > 0) iff q != [])
    expect length_one: ((s.len < 1) iff s = "") and ((s.len >= 1) iff s != "") and ((s.len != 0) iff s != "")
    expect length_right: ((0 = q.len) iff q = []) and ((0 < q.len) iff q != []) and ((1 > q.len) iff q = [])
    expect card_zero: ((t.card = 0) iff t = {}) and ((t.card <= 0) iff t = {}) and ((t.card > 0) iff t != {})
    expect relation_card_zero: ((r.card = 0) iff r = {}) and ((r.card <= 0) iff r = {}) and ((r.card > 0) iff r != {})
}
```

`length_zero` also fires on `s.at(0) = ""` and `q.at(0) = []`, and on
`!=`, with the literal on either side. The first character, or element, is
the empty one exactly when there is none: `s.at(0)` is `""` unless `0 <
s.len`, and otherwise a string of one character, which is not `""`. So
`s.at(0) = ""` becomes `s = ""`, and `s.at(0) != ""` becomes `s != ""`, and
likewise for sequences, whose `q.at(0)` is `[]` or `[q[0]]`. The fix keeps
the receiver's text, and it and the fix are put in parentheses where
[fixes need them](../Lint.md#parentheses-in-fixes); it evaluates the receiver where `at` did, so it keeps the
guards. `lint::first_empty` states the value, which its `impl` proves for
strings:

```fren
pub proc first_empty(s: String): (
    det empty?,          -- `s.at(0) = ""`
) {
    ensure rule: empty? iff s = ""
}
```

## Trivial patterns

`trivial_pattern` fires on `s.matches?(p)`, where the
[pattern](../Lang/Expressions.md#patterns) `p` is a nonempty string `lit`,
written with characters that are not special and escapes `\c`, with `.*`
at its start, its end, both or neither, and is fixable:

| Pattern | Fix |
|---|---|
| `lit` | `s = "lit"` |
| `lit.*` | `s.starts_with?("lit")` |
| `.*lit` | `s.ends_with?("lit")` |
| `.*lit.*` | `s.contains?("lit")` |

The fix writes `lit` as a string literal that is not raw, with each `\c` as
the character `c`, and with the escapes that a [literal](../Lang/Lexical.md#literals)
needs: `\\` for `\`, `\"` for `"`, `\n` and `\t`, and `\xHH` for the other
control characters. So `s.matches?(r"a\.b.*")` becomes
`s.starts_with?("a.b")`. The receiver keeps the text it is written with; in
`s = "lit"`, it is written without the parentheses a receiver may need, and
it and the equation are put in parentheses where [fixes need them](../Lint.md#parentheses-in-fixes). The fix evaluates the
receiver where the pattern did, and nothing else, so it keeps every guard.

Clippy's `trivial_regex` is in its `nursery` group, because of the quirks
of Rust's `regex` crate. Fren's patterns have none: a pattern always
matches the whole string, and has no flags, anchors or classes of
characters such as `\d`. So `trivial_pattern` is in `style`. For
[decidability](../Lang/Decidability.md#strings), the four forms are the same:
`matches?` with a literal pattern, `starts_with?`, `ends_with?` and
`contains?` with a constant, and an equation with a constant are each in
the decidable core, so the fix never changes whether a procedure is
decidable.

`lint::trivial_pattern` states when it fires, from the value of the
literal, and which fix it makes:

```fren
pub enum PatternFix { Equality, StartsWith, EndsWith, Contains }

pub proc trivial_pattern(
    pattern: String,         -- the value of the literal
): (det fires?, det fix: PatternFix) {
    ensure rule: fires? iff pattern.matches?(r"(\.\*)?([^\\.\[\]()*+?{}|^]|\\[\\.\[\]()*+?{}|^-])+(\.\*)?")
    ensure which: fix = if pattern.starts_with?(".*") then (if pattern.ends_with?(".*") then PatternFix::Contains
        else PatternFix::EndsWith)
        else if pattern.ends_with?(".*") then PatternFix::StartsWith
        else PatternFix::Equality

    expect not_everything: when pattern = ".*", not fires?
    expect classes_kept: when pattern = "[a-z]", not fires?
}
```

## Classes of characters

`manual_pattern_char_comparison` fires on a [pattern](../Lang/Expressions.md#patterns)
of `matches?` with an alternation of two or more single characters, such as
`a|b|c`, either the whole pattern or the whole of a pair of parentheses,
and is fixable. A single character is one that is not special, or `\c`
for a special `c`. The fix writes each such alternation as the class of
its characters, without the parentheses: `s.matches?(r"(a|\.)+")` becomes
`s.matches?(r"[a.]+")`. An alternation matches what one of its
alternatives matches, here one of the characters, and so does the class,
which is an atom, like the parentheses it replaces, so a repetition after
them repeats it. Only the literal changes, so the fix keeps the guards.
Each alternation in the literal is fixed, and the message is reported once,
at the literal.

In a class, `]` ends it, `^` first negates it, `-` between two characters
makes a range, and `\c` is `c` for any character `c`. So the fix writes
`\`, `]`, `^` and `-` escaped, and every other character as itself, `.`
and `|` included, which are not special in a class. The new literal is
raw, with the delimiters of the old one, if the old one is raw and the
pattern has no `"`; otherwise it is not raw, with the escapes of
[`trivial_pattern`](#trivial-patterns)'s fix.

`lint::manual_pattern_char_comparison` states when it fires, and
`lint::class_char` how the fix writes a character in the class:

```fren
pub proc manual_pattern_char_comparison(
    n_alternatives: Int,     -- the alternatives of the alternation
    single?,                 -- each is a single character
): (det fires?) {
    ensure rule: fires? iff (n_alternatives >= 2 and single?)
}

pub proc class_char(
    c: String,           -- a character
): (
    det escaped?,         -- the fix writes it `\c`, rather than `c`
) {
    assume one: c.len = 1

    ensure rule: escaped? iff c in {"\\", "]", "^", "-"}
}
```

## Boolean types

A name that ends in `?` is a `Bool`, so the parameter `ready?: Bool` is
the same as `ready?` (see [Boolean names](../Lang/Types.md#boolean-names)).
`redundant_bool_type` fires on a `: Bool` that the rule implies: on a
variable of a procedure, a parameter, a result or an `exists` or `let`
variable, on a field of a record, on a parameter of a defined function, and on a function's result type. It is
reported at `: Bool`, and the fix removes it, with the spaces before it,
from the end of the name, or of the `)` before a result type: `fn ok?(n:
Int): Bool := n > 0` becomes `fn ok?(n: Int) := n > 0`. A declaration has no
guard. `lint::redundant_bool_type` states when it fires, from a declaration
that [`lang::bool_naming`](../Lang/Types.md#boolean-names) accepts:

```fren
use lang::Annot

pub proc redundant_bool_type(
    name: String,        -- the declared name
    annot: Annot,
): (det fires?) {
    ensure rule: fires? iff (name.ends_with?("?") and annot = Annot::BoolTy)

    expect written: when fires?, annot != Annot::Missing
}
```

## Matches that are memberships

`match_like_membership` looks at the arms of a
[`match`](../Lang/Expressions.md#matches) as written, as the [match
lints](Pedantic/Matches.md#arms) of the `pedantic` group do.

`match_like_membership` fires on a `match` on `x` whose bodies are the
literals `true` and `false`, each at least once, and whose patterns bind
no name. It says whether `x` is one of the values whose arms are `true`.
If no `_` arm is `true`, and there is a `_` arm or no more alternatives are
`true` than `false`, the fix tests for the alternatives whose arms are
`true`; otherwise, for those whose arms are `false`, negated. Where that is
one alternative, a variant without a payload or a literal, as
[`is_equality`](Style/Comparisons.md#pattern-tests) asks, the fix is the
equation `x = E::A`, or `x != E::A`, negated. Otherwise it is a [pattern
test](../Lang/Expressions.md#pattern-tests) of those alternatives, `x is
E::A | E::B` or `x is E::A(_) | E::B`, or `not x is ...`, negated, so the
two lints never undo each other: a test of several values is a pattern
test, not a membership, as
[`manual_pattern_test`](Style/PatternTests.md)
also writes it. This is Clippy's `match_like_matches_macro`, also in
`style`, and its `redundant_pattern_matching`: `match s { Shape::Circle(_)
=> true, _ => false }` becomes `s is Shape::Circle(_)`.

An arm is matched only where no earlier arm matches, so the alternatives
of one body stand for the values they match only if no arm of the other
body comes before them and overlaps them. Each pattern that is `_`, a
variant whose payload's patterns are all `_`, `true`, `false` or a
literal, or an or-pattern of these, overlaps another only where one
contains the other, and then the later one is never reached, an error.
So the lint fires on any order of such arms. Otherwise, with a range or a
nested pattern, it fires only where the arms it lists all come before the
arms of the other body: `match n { 0..=9 => true, _ => false }` becomes
`n is 0..=9`. Without a `_` arm, it then lists those that come first. A
pattern that binds a name, such as `Shape::Circle(r) => true`, keeps it
from firing, since a pattern test binds none. The alternatives are written
as the patterns write them, so a variant brought into scope by `use`
stays unqualified, and `x` and the result are in parentheses where [fixes
need them](../Lint.md#parentheses-in-fixes). The bodies are literals,
which guard nothing, and `x` is evaluated as before. It does not fire on
a `match` with a [guard](../Lang/Expressions.md#matches), which a
membership or a pattern test has no place for. A `match` whose arms
are all `true`, or all `false`, is left to
[`match_same_arms`](Pedantic/Matches.md#arms).
`lint::match_like_membership` states when it fires, when its fix is
negated, and when it is a pattern test:

```fren
pub proc match_like_membership(
    bool_bodies?,        -- every body is `true` or `false`, and each is some body
    binds?,              -- some pattern binds a name
    disjoint?,           -- each pattern is `_`, a variant whose payload's patterns are `_`, a literal, or an or-pattern of these
    true_first?,         -- every arm whose body is `true` comes before every arm but `_` whose body is `false`
    false_first?,        -- and the other way round
    equatable_true?,     -- each alternative of the arms whose body is `true` is a variant without a payload or a literal
    equatable_false?,    -- and of those whose body is `false`
    wildcard?,           -- there is a `_` arm
    wildcard_true?,      -- its body is `true`
    n_true: Nat,         -- alternatives of arms whose body is `true`
    n_false: Nat,        -- and of arms whose body is `false`
): (
    det fires?,
    det negated?,         -- the fix is negated, of the `false` alternatives
    det pattern_test?,         -- the fix is a pattern test, rather than an equation
) {
    ensure negated: negated? iff (if wildcard? then wildcard_true? else if disjoint? then n_true > n_false else false_first?)
    ensure rule: fires? iff (bool_bodies? and not binds? and (disjoint? or (if negated? then false_first? else true_first?)))
    ensure test: pattern_test? iff not (if negated? then equatable_false? and n_false = 1 else equatable_true? and n_true = 1)

    expect fewer_listed: when not wildcard? and disjoint? and negated?, n_false < n_true
    expect several_tested: when not negated? and n_true >= 2, pattern_test?
}
```

The [refinements](Style/Comparisons.md#pattern-tests) check its fixes to
a pattern test.

## Bindings

`redundant_bindings` fires on a field of a record literal written `x :=
x`, and is fixable. The fix is `x`, which means `x := x` by definition
(see [Records](../Lang/Expressions.md#records)), so it keeps the meaning
and the guards. It fired on an instance's binding `x := x` too, before
instances were calls, whose arguments are positional. The name and the expression after `:=` are compared as
[written the same](../Lint.md#written-the-same), so a comment next to
either is not part of it: `x := /- c -/ x` and `x := x -- c` fire too,
and the fix removes a comment between the name and the expression.
`lint::redundant_bindings` states when it fires, from the texts of the
name and of the expression, each in the form that comparison uses:

```fren
pub proc redundant_bindings(
    name: String,        -- the name bound, or the field given
    value: String,       -- the expression after `:=`
): (det fires?) {
    ensure rule: fires? iff value = name
}
```

In a [record update](Style/Records.md#fields-of-updates), it also fires
on a field `x := r.x`, copied from the updated value `r`.

## Negations

`double_neg` fires on a negation of a negation, `- -x`, through
parentheses, as in `-(-x)` and `-(-(x))`: it is `x`, which is its fix.
`neg_multiply` fires on a product with `-1`, the negation of the literal
`1`, through parentheses: `x * -1` and `-1 * x` are `-x`, which is its fix.
`Int` is the integers, without overflow, so both fixes are exact. Both are
fixable:

```fren
set_option fren.evidence "enumerated" in
pub proc double_neg(
    negated_operand?,    -- the operand of the negation, through parentheses, is a negation
): (det fires?) {
    ensure rule: fires? iff negated_operand?
}

set_option fren.evidence "enumerated" in
pub proc neg_multiply(
    left_minus_one?,     -- the left operand, through parentheses, is `-1`
    right_minus_one?,    -- the right operand is
): (
    det fires?,
    det negate_left?,         -- the fix negates the left operand, rather than the right
) {
    ensure rule: fires? iff (left_minus_one? or right_minus_one?)
    ensure fix: negate_left? iff right_minus_one?
}
```

Each of these fixes, and that of
[`int_plus_one`](Complexity/Comparisons.md#off-by-one-comparisons), writes its operands
with the text they are written with, and the operands and the fix itself
in parentheses where [fixes need them](../Lint.md#parentheses-in-fixes), as for
[`nonminimal_bool`](Complexity.md#simpler-bool-expressions): `2 * - -(x + y)` becomes `2
* (x + y)`, `(a + b) * -1` becomes `-(a + b)`, and `(x) >= y + 1` becomes
`x > y`. A negation of an operand that starts with `-` is written with a
space, `- -y`, since `--` starts a comment. No fix adds or removes an
`and`, `or`, `when`, `unless`, `if` or `match`, and each operand is
evaluated where it was, so the guards are kept.

## Names

Five lints find a declared name that says less than it could, or says it
twice. Like the [naming conventions](NonstandardStyle.md#naming-conventions),
each is reported where the name is declared, at the level in effect there,
and nowhere else. None is fixable: renaming would rename every path to the
name, in files that `fren fix` may not read.

`module_inception` fires on a module whose last segment repeats its
parent's, as in `mod lint::lint`, so that every path to it, or to an item
in it, repeats the name. It is reported at the segment that declares the
module. `lint::module_inception` states when it fires:

```fren
pub proc module_inception(
    name: String,        -- the module's last segment
    parent: String,      -- its parent's last segment, or `""` for a top-level module
): (det fires?) {
    ensure rule: fires? iff name = parent

    expect top_level: when parent = "" and name != "", not fires?
}
```

The *words* of a name are split at `_`, and before an uppercase letter
that follows a lowercase letter or a digit, so that `HeatMode` is `Heat`
and `Mode`, and `HTTPStatus` is one word. `enum_variant_names` fires in two
cases, and its message names the word:

- On an enumeration of two or more variants, each of two or more words,
  that all start, or all end, with the same word, as in `enum Mode {
  ModeHeat, ModeCool }` and `enum Climate { HeatMode, CoolMode }`. It is
  reported at the enumeration's name. A variant of one word is the shared
  word alone, which could not be removed from it.
- On a variant whose words contain those of its enumeration's name, one
  after another, and others, as `HighFan` does in `enum Fan { Low, HighFan
  }`: a path to a variant names its enumeration already, as `Fan::HighFan`
  does. It is reported at the variant.

Since `HTTPStatus` is one word, `enum S { HTTPStatus, FTPStatus }` shares
no word, and `enum_variant_names` does not fire on it until the renames
that [`upper_case_acronyms`](#names) suggests, `HttpStatus` and
`FtpStatus`, are made.

Clippy's `enum_variant_names` fires on enumerations of three or more
variants by default, and only on a variant that starts or ends with its
enumeration's name. `lint::enum_variant_names` and
`lint::variant_has_enum_name` state when it fires:

```fren
pub proc enum_variant_names(
    n_variants: Nat,
    shared_first?,       -- every variant has two or more words, and all have the same first word
    shared_last?,        -- every variant has two or more words, and all have the same last word
): (det fires?) {
    ensure rule: fires? iff (n_variants >= 2 and (shared_first? or shared_last?))
}

pub proc variant_has_enum_name(
    n_words: Nat,        -- the words of the variant's name
    n_enum_words: Nat,    -- the words of its enumeration's name
    contains?,           -- the variant's words have the enumeration's, one after another
): (det fires?) {
    ensure rule: fires? iff (contains? and n_words > n_enum_words)

    expect same_name: when n_words = n_enum_words, not fires?
}
```

`upper_case_acronyms` fires on the name of an enumeration, a variant, a
record or an abstract type that is in `CamelCase`, and so accepted by
`non_camel_case_types`, but has three or more uppercase letters in a row,
such as `HTTPStatus`. Its message suggests the name with each such run in
lower case but for its first letter, and for its last if a lowercase
letter follows the run, since that letter starts the next word:
`HTTPStatus` becomes `HttpStatus`, `HTTP2` becomes `Http2`, and `IOError`
becomes `IoError`. Two uppercase letters in a row, as in `IO` and `UserID`,
are left as they are. Clippy, by default, fires only on a name all in
upper case, such as `HTTP`; Fren fires as Clippy's
`upper-case-acronyms-aggressive` setting does. `lint::upper_case_acronyms`
states when it fires. Its pattern is that of `CamelCase` in
[`lint::in_case`](NonstandardStyle.md#naming-conventions), `[A-Z][^_]*`,
with three uppercase letters in a row, written as one pattern rather than
two, whose intersection the solver is slow to decide:

```fren
pub proc upper_case_acronyms(what: Named, name: String): (det fires?) {
    call c := naming_case(what)

    ensure rule: fires? iff (c.case = Camel and name.matches?(r"[A-Z]([^_]*[A-Z])?[A-Z][A-Z][^_]*"))

    expect constants: when what = Named::Constant, not fires?
}
```

`just_underscores_and_digits` fires on a name made only of `_` and digits,
other than the wildcard `_`, before a final `?` if it has one. An
[identifier](../Lang/Lexical.md#identifiers) starts with a letter or `_`, so
such a name starts with `_`, as `_1`, `__` and `_2?` do, and both front
ends accept one wherever a name is declared: for a module, a procedure, a
variable, a parameter, a field, a binder, a function, a call, a
constraint, a global expectation, an enumeration, a variant, a record, an
abstract type or a constant. A name in `CamelCase` or `UPPER_CASE` starts
with a letter, so `non_camel_case_types` or `non_upper_case_constants`
reports such a name too, where it is in one of those cases.

`disallowed_names` fires on a name that is a placeholder: `foo`, `baz` or
`quux`, in any case, such as `Foo` or `FOO`, before a final `?` if it has
one. These are Clippy's default `disallowed-names`. Clippy's list no longer
has `bar`, which is a word, as in a bar of a chart, and Fren's does not
either.

```fren
pub proc just_underscores_and_digits(name: String): (det fires?) {
    ensure rule: fires? iff (name.matches?(r"[_0-9]+[?]?") and name != "_")
}

pub proc disallowed_names(name: String): (det fires?) {
    ensure rule: fires? iff name.matches?(r"([Ff][Oo][Oo]|[Bb][Aa][Zz]|[Qq][Uu][Uu][Xx])[?]?")
}
```

## Constant constraints

`assertions_on_constants` fires on an assumption, guarantee,
expectation or cover goal, of a procedure or [global](../Lang/Global.md), whose
expression mentions no variable and no uninterpreted function (see
[Mentions](../Lang/Expressions.md#mentions)), as
[`constant_output`](Complexity.md#constant-outputs) does on a
definition, such as `ensure r: true` or `expect e: LIMIT > 0`. An
application of an uninterpreted function counts, since its value depends
on the [interpretation](../Lang/Procedures.md#interpretations).

Such a constraint is the same in every behaviour. If it is always true,
it says nothing. If it is always false, a guarantee makes its procedure
unrealizable, an assumption makes every guarantee hold vacuously, and an
expectation always fails. The message says which where the expression is
written `true` or `false`, in parentheses or not; otherwise only the
solver could tell, and a lint never asks it, so the message says that the
constraint mentions no variable. It has no fix: removing a constraint
changes the checks, and what traces and claims name.
[`duplicate_constraint`](Suspicious.md#repeated-constraints) removes one
too, but only a repeat of an earlier constraint of its kind, written the
same: the one it repeats stays, with its checks and its name, so all that
goes is a second copy, which checks nothing more. A constant constraint
repeats nothing, so removing it would lose its checks and its name.
`lint::assertions_on_constants` states when it fires, from what the
expression mentions, as [`lang::mentions`](../Lang/Expressions.md#mentions)
gives it:

```fren
pub proc assertions_on_constants(
    mentioned: Set<lang::Mention>,    -- what the expression mentions
): (det fires?) {
    ensure rule: fires? iff mentioned = {}
}
```

What it fires on is the same in every behaviour, by
[`mentions_nothing`](Meaning.md#expressions-that-mention-nothing), where each
of its layers that is evaluated is specified, as the [definedness
check](../Check.md#definedness) ensures of a spec that passes its checks.
Here `p` is the root layer of the expression in one environment and `q` the
same layer, with the same parts' values, in any other:

```fren
expect constant_constraint(
    c_mentioned: Set<lang::Mention>,
    p_program: lang::Program,
    p_head: lang::Head,
    p_env: lang::Env,
    p_values: Seq<lang::Value>,
    p_parts_mentioned: Set<lang::Mention>,
    p_undefined_parts: Set<Int>,
    q_program: lang::Program,
    q_head: lang::Head,
    q_env: lang::Env,
    q_values: Seq<lang::Value>,
    q_parts_mentioned: Set<lang::Mention>,
    q_undefined_parts: Set<Int>,
) {
    assume p_leaves: when p_head is lang::Head::Literal(_) | lang::Head::Bound(_) | lang::Head::Constant(_) | lang::Head::Variable(_),
        p_parts_mentioned = {}
    assume q_leaves: when q_head is lang::Head::Literal(_) | lang::Head::Bound(_) | lang::Head::Constant(_) | lang::Head::Variable(_),
        q_parts_mentioned = {}
    call c := assertions_on_constants(c_mentioned)
    call p := lang::node(p_program, p_head, p_env, p_values, p_parts_mentioned, p_undefined_parts)
    call q := lang::node(q_program, q_head, q_env, q_values, q_parts_mentioned, q_undefined_parts)
    expect constant_constraint: when c.fires? and p.mentioned = c.mentioned and p.specified? and q.program = p.program and q.head = p.head
        and q.values = p.values,
        q.value = p.value
}
```
