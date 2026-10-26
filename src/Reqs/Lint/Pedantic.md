# Pedantic

The lints of the `pedantic` group are matters of judgement, or would fire
on much that reads well as it is, so they are `allow` by default. This
chapter has the lints of expressions and of literals, and its subchapters
the others: those of [matches](Pedantic/Matches.md), of [records and
functions](Pedantic/Records.md), of [source text](Pedantic/Text.md) and of
[comparisons](Pedantic/Comparisons.md).

Where a lint rewrites an expression, its section checks the rewrite with
[refinement](../Lang/Refinement.md): a component `lint::R_written`
computes the expression as written, a component `lint::R_fixed` computes
its fix, and the refinements `R_sound`, that the fixed one refines the
written one, and `R_complete`, the converse, make the solver check that
the two agree on every input. Each operand of the rewrite is an input, and
stands for any expression of its type: expressions are pure, so a rewrite
that holds for every value of its operands holds for every expression. An
input is always defined, so these checks are of the values alone; the
prose says why each fix also keeps the guards.

## Membership chains

`membership_chain`, `allow` by default, fires on a disjunction of
three or more equations of one expression with others, `x = a or x = b or x
= c`, whose fix is `x in {a, b, c}`, and on its De Morgan dual, a
conjunction of three or more disequations, `x != a and x != b and x != c`,
whose fix is `not x in {a, b, c}`. It fires only where some value is not
one that a pattern writes, such as a variable, a constant or a computed
value, as in `x = 1 or x = 2 or x = y`: a membership is for a collection of
values. Where each value is an integer literal, a string literal, `true`,
`false` or a variant without a payload, the chain is a [pattern
test](../Lang/Expressions.md#pattern-tests) written out, which
[`manual_pattern_test`](Style/Comparisons.md#pattern-tests-written-out)
reports, with the fix `x is a | b | c`, and this lint does not fire, so the
two never fire on the same chain.

In the chain, each operand is guarded by those before it (see
[Expressions](../Lang/Expressions.md#sequences)): `x = b` by `not x = a`, and
`x != b` by `x != a`. In the fix, each value is evaluated where the chain
is. A comparison of `x` with values, with `=`, `!=` or `in`, is defined
wherever `x` and the values are, and `x` and the first value are evaluated
where the chain is in either form, so the fix keeps their guards, but not
those of the later values. So the lint does not fire if a value after the
first indexes a sequence, which might be out of range: `x = 1 or x = q[0] or
x = 2` is left as it is. `lint::membership_chain` states when it fires,
from the number of operands of the chain, whether they all equate, or
disequate, the same expression, written the same way, on their left,
whether a later value indexes a sequence, and whether each value is one
that a pattern writes:

```fren
pub mod lint

pub comp membership_chain {
    in n: Int            -- operands of the chain of `or`, or of `and`
    in same_left?        -- each is an equation, or for `and` a disequation, with the same left operand
    in later_indexes?    -- a value after the first indexes a sequence
    in patterns?         -- each value is one that a pattern writes
    pub det out fires?

    assume counts: n >= 2

    ensure rule: fires? iff (same_left? and n >= 3 and not later_indexes? and not patterns?)
}
```

`lint::membership_chain_keeps_meaning` states both fixes as laws (see
[Fixing lints](../Lint.md#fixing-lints)):

```fren
set_option fren.lint.membership_chain "expect" in
pub comp membership_chain_keeps_meaning {
    in x: Int
    in y: Int
    in z: Int
    in w: Int

    expect chain: (x = y or x = z or x = w) iff x in {y, z, w}
    expect dual: (x != y and x != z and x != w) iff not x in {y, z, w}
}
```

## Definable outputs

`definable_output`, `allow` by default, fires on an output, not defined,
that exactly one guarantee constrains, unconditionally, as `x = e` or
`x? iff e`, where `e` does not mention `x`: the guarantee could be its
definition. [`lint::output_lints`](Complexity.md#constant-outputs) states
when it fires, with `constant_output`.

## Negated conditions

`if_not_else`, `allow` by default, fires on `if C then A else B` where
`C` is a [negation](Style.md#conditionals): `if not C then A else B`
becomes `if C then B else A`, and `if a != b then A else B` becomes `if a
= b then B else A`. It does not fire when `B` is itself an `if`, since
swapping the branches would break a chain of `else if`. `A` is guarded by
`not C`, and `B` by `C`, before and after. It is `pedantic`, as its Clippy
counterpart is. It fires in the same places as the [lints on
conditionals](Style.md#conditionals) of the `style` group, and writes its
operands as they do. `lint::if_not_else` states when it fires, from the
[`lint::Head`](Style.md#conditionals) of the condition and of the `else`
branch:

```fren
pub comp if_not_else {
    in condition: Head
    in else_branch: Head
    pub det out fires?

    ensure rule: fires? iff (condition in {Head::Not, Head::Unequal} and else_branch != Head::If)

    expect chain: when else_branch = Head::If, not fires?
}
```

## Boolean equality

`bool_equality`, `allow` by default, follows the rules of the [lints on
operators](Complexity/Comparisons.md#double-comparisons) for its fix, and fires on `a = b`
where both operands
are `Bool`s, and its fix is `a iff b`, which means the same and says that
the two are equivalent. `iff` binds more loosely than `=`, so the fix may
need parentheses that the equation did not: `a? = b? and c?` becomes `(a?
iff b?) and c?`. The fix evaluates the same operands under the same guard.
It does not fire on `!=`, or where an operand is `true` or `false`, which
[`nonminimal_bool`](Complexity.md#simpler-bool-expressions) simplifies:

```fren
pub comp bool_equality {
    use self::Comparison::Eq
    in op: Comparison
    in bools?            -- both operands are `Bool`s
    in literal?          -- an operand is `true` or `false`
    pub det out fires?

    ensure rule: fires? iff (op = Eq and bools? and not literal?)
}
```

## Relations to one value

`zero_sized_map_values`, `allow` by default, fires on a relation type
`Rel(A, B)`, wherever a type is written, whose `B` is an enumeration with
one variant and no payload, and so has exactly one value. Such a relation
pairs each `A` it relates with that one value, so it says only which `A`s it
relates, as `Set(A)` does, which the message suggests. It has no fix: the
expressions that build and read the relation would change too.
`lint::zero_sized_map_values` states when it fires:

```fren
pub comp zero_sized_map_values {
    in enum?             -- `B` is an enumeration
    in n_variants: Nat   -- its variants
    in payload?          -- one of them has a payload
    pub det out fires?

    ensure rule: fires? iff (enum? and n_variants = 1 and not payload?)
}
```

## Names

`many_single_char_names` and `similar_names` look at the names that an
item declares: the variables and instances of a component, the
parameters of a defined function, the binders of a global expectation, and
the binders of the `match` arms, the bound names of the quantifiers and
the names of the `let` and `where` clauses in each of them. Each name counts once,
however many times it is declared: `x` and a later `x!` that
[shadows](../Lang/Components.md#shadowing) it are one name. A final `?` is
not counted. Neither lint has a fix: only the writer knows what a name stands
for.

`many_single_char_names`, `allow` by default, fires on a component,
function or global expectation that declares more than four names of one
character, as Clippy's does by default. Its message is reported at the
item's name, and lists them. `lint::many_single_char_names` states when it
fires:

```fren
pub comp many_single_char_names {
    in n: Nat            -- names of one character that the item declares
    pub det out fires?

    ensure rule: fires? iff n > 4
}
```

`similar_names`, `allow` by default, fires on two names that one item
declares, each of three or more characters, one of which is the other
with one character substituted, inserted or deleted, such as `level` and
`levels`, or `user` and `used`. Its message is reported at the later of
the two, once for each name, and names the earlier. Following Clippy, it
does not fire on names that differ only in a digit, such as `x1` and
`x2`, or in a substituted character that is a word of its own in both,
between `_`s or the name's ends, such as `a_mentions?` and `b_mentions?`:
both name a series on purpose. Nor does it fire on the pairs that Clippy
allows and that apply to Fren: `lhs` and `rhs`, `set` and `get`, `args` and
`arms`, and `lit` and `lint`. `lint::similar_names` states when it fires:

```fren
pub comp similar_names {
    in len_a: Nat        -- characters of each name, without a final `?`
    in len_b: Nat
    in one_edit?         -- one is the other with one character substituted, inserted or deleted
    in digits?           -- the characters that differ are digits
    in word?             -- a character is substituted for another, each a word of its name
    in allowed?          -- the pair is one that Clippy allows, such as `lhs` and `rhs`
    pub det out fires?

    ensure rule: fires? iff (len_a >= 3 and len_b >= 3 and one_edit? and not digits? and not word? and not allowed?)

    expect series: when digits?, not fires?
}
```

## Long items

`too_many_lines`, `allow` by default, fires on a component or defined
function of more than 100 lines, as Clippy's does by default. Its lines
run from the line of its name to its end: a component's closing `}`, and
a function's last token, which is the `)` when its body is in parentheses.
A line counts if it has a character other than whitespace outside
[comments](../Lang/Lexical.md#comments):

- a blank line does not count, nor does one of only whitespace;
- a line comment, `--` to the end of the line, does not count, so a line
  of only a comment does not, but a line of code before one does;
- a block comment, `/-` to `-/`, may span lines and nests, `/- /- -/ -/`,
  and only what is outside it counts, so code after a `-/` does;
- a `--` or `/-` in a string literal starts no comment.

Its message is reported at the item's name. It has no fix: how to split an
item into smaller ones, as instances or functions, is the writer's choice.
`lint::too_many_lines` states when it fires:

```fren
pub comp too_many_lines {
    in n_lines: Nat      -- lines of the item with code
    pub det out fires?

    ensure rule: fires? iff n_lines > 100
}
```

## Ranges of methods

`invalid_upcast_comparisons`, `allow` by default, fires on a comparison of
a call of a method with an integer literal, on either side, whose value
is fixed because the method's values have a least one. Fren has no casts,
whose ranges Clippy's lint of the same name looks at, but these methods
give an `Int` that is never below a bound:

| Method | Least value | Why |
|---|---|---|
| `x.abs` | `0` | it is `x` or `-x`, whichever is not negative |
| `s.index_of(t, i)`, of a string or a sequence | `-1` | it is a position, which is never negative, or `-1` |

So `x.abs >= 0` is always `true`, `x.abs < 0` always `false`, and so are
`s.index_of(t, i) >= -1` and `s.index_of(t, i) < -1`, and every
comparison with a literal below the least value, such as `x.abs > -3` or
`-2 = s.index_of(t, i)`. A comparison with the least value that a call
can equal, such as `x.abs > 0` or `s.index_of(t, i) = -1`, is not fixed,
and neither is a comparison with a bound above it. The message says what
the comparison always is.

The other methods that give an `Int` are left out. `len` and `card` are
never negative either, but
[`absurd_extreme_comparisons`](Suspicious/Comparisons.md) fires on their
comparisons with a literal, and [`length_zero` and
`card_zero`](Style.md#empty-collections) on those that say whether the
collection is empty. `min` and `max` have no least value of their own,
since `x.min(y)` is `x` or `y`, which may be any `Int`. A `Nat` is never
negative whatever gives it, so that is its type's range, not a method's:
no lint reports `n >= 0`, for `n: Nat`, yet. `absurd_extreme_comparisons`,
which looks at lengths for the same reason, is its natural owner once it
covers `Nat`s, so `invalid_upcast_comparisons` leaves it alone, and the
two never fire on one comparison.
Nor does the lint fire on an `Int` that is not a call, such as an input
`x` in `x >= 0`. Where it fires, [`manual_method`](Complexity/Methods.md#searches)
never does, since its comparisons of `index_of` are with `-1` or `0`, by
operators that the least value does not fix. A search from a negative
position, as in `s.index_of(t, -1) >= -1`, is also
[`negative_position`'s](Suspicious/Methods.md), which reports the argument,
and this lint the comparison. Two comparisons of one call joined by `and` or `or`, as in
`x.abs >= 0 and -1 > x.abs`, may also be
[`contradictory_comparisons`'s](Suspicious/Comparisons.md), which reports
the pair, and this lint each comparison, as `absurd_extreme_comparisons`
does with that lint on lengths. `abs` is a method of `Int`
and `Nat` only: on a record, `r.abs` reads a field, and on an instance, a
variable, so the lint looks at what the elaborator calls `abs`.

There is no fix, as for [`eq_op`](Suspicious/Expressions.md#operands-written-the-same)
and the other lints whose message gives a comparison's value: the bound
or the operator is probably not the one meant, and writing the value
would keep the mistake and hide it. `lint::invalid_upcast_comparisons`
states when it fires, from the least value of the method:

```fren
pub comp invalid_upcast_comparisons {
    in op: Comparison
    in bound: Int        -- the literal compared with
    in lowest: Int       -- the least value of the method
    in left?             -- the call is the left operand, rather than the right
    pub det out fires?
    pub det out value?   -- what the comparison always is, where it fires

    ensure rule: fires? iff (bound < lowest or (bound = lowest and (if left? then op in {Lt, Ge} else op in {Gt, Le})))
    ensure fixed: value? iff (if left? then op in {Ne, Gt, Ge} else op in {Ne, Lt, Le})
}
```

The value is exact: where the lint fires, the comparison has it for each
value of the call, from the least on:

```fren
comp invalid_upcast_exact {
    in op: Comparison
    in bound: Int
    in lowest: Int
    in left?
    in n: Int            -- the call's value

    assume range: n >= lowest

    inst p: invalid_upcast_comparisons { op, bound, lowest, left? }

    expect exact: when p.fires?, compares?(op, if left? then n else bound, if left? then bound else n) iff p.value?
}
```

The [refinements](../Lang/Refinement.md) below check the value that the
message gives, and with it the least values of the table, for a call of
each method: a component that compares the calls as written, one with
the values instead, and a refinement each way, so that the solver checks
that the two agree for every value of the inputs. `index_of` is outside
the [decidable core](../Lang/Decidability.md#strings), so the written form
opts out, and the values make the inputs unused:

```fren
set_option fren.lint.invalid_upcast_comparisons "allow" in
set_option fren.lint.undecidable "allow" in
pub comp invalid_upcast_written {
    in x: Int
    in s: String
    in t: String
    in i: Int
    pub det out nonnegative? := x.abs >= 0
    pub det out negative? := -1 >= x.abs
    pub det out found_or_not? := s.index_of(t, i) > -2
    pub det out below? := s.index_of(t, i) < -1
}

set_option fren.lint.constant_output "allow" in
set_option fren.lint.unused_variables "allow" in
pub comp invalid_upcast_fixed {
    in x: Int
    in s: String
    in t: String
    in i: Int
    pub det out nonnegative? := true
    pub det out negative? := false
    pub det out found_or_not? := true
    pub det out below? := false
}

refine invalid_upcast_sound: invalid_upcast_fixed refines invalid_upcast_written
refine invalid_upcast_complete: invalid_upcast_written refines invalid_upcast_fixed
```

## Operands that can be dropped

`overly_complex_bool_expr`, `allow` by default, fires on an `and` or an
`or` with an operand that can be dropped, its operands compared as
[written the same](../Lint.md#written-the-same), in either order:

| Rule | Written | Fix |
|---|---|---|
| absorption | `a or (a and b)`, `a or (b and a)`, `(a and b) or a`, `(b and a) or a` | `a` |
| absorption | `a and (a or b)`, `a and (b or a)`, `(a or b) and a`, `(b or a) and a` | `a` |
| contradiction | `a and not a`, `not a and a` | `false` |
| excluded middle | `a or not a`, `not a or a` | `true` |

The fix is in parentheses where [fixes need
them](../Lint.md#parentheses-in-fixes). Where the expression is an
operand in parentheses of its own, the fix replaces them too, so that
`((a? or b?) and a?) or c?` becomes `a? or c?`, not `(a?) or c?`. The lint looks at the operands of the operator alone: in
`a or (a and b and c)`, the right operand is `(a and b) and c`, whose
operands are not `a`. Its Clippy counterpart is in `correctness`.

The fix keeps the guards. It drops operands that the expression as written
evaluates, which removes evaluations and adds none. What stays, `a`, is
evaluated in the fix wherever the expression is, under its guard `G`. As
written, `a` is evaluated under `G` where it is written first, as in `a or
(a and b)` and `(a and b) or a`. In `(b and a) or a`, it is evaluated under
`G and b`, and under `G and not (b and a)`, and wherever `G` holds, one of
these holds, whatever the value of `a`; so does one of `G and not b` and
`G and (b or a)`, in `(b or a) and a`. So no guard of `a` is weaker.

[`eq_op`](Suspicious/Expressions.md#operands-written-the-same) reports an
operator whose operands are written the same, and this lint one whose
operands are not, so no expression is reported by both. It does not fire
where the negation `not a` has a simpler form that
[`nonminimal_bool`](Complexity.md#simpler-bool-expressions) reports, as in `x
= 1 and not x = 1`: its fix, `x = 1 and x != 1`, is
[`contradictory_comparisons`](Suspicious/Comparisons.md) when the values
are integers. `lint::overly_complex_bool_expr` states when it fires, and by
which rule:

```fren
pub enum BoolRule { Absorption, Contradiction, ExcludedMiddle }

pub comp overly_complex_bool_expr {
    in conj?             -- the operator is `and`, rather than `or`
    in absorbs?          -- an operand is `p and q`, in an `or`, or `p or q`, in an `and`, with `p` or `q` written the same as the other operand
    in negates?          -- an operand is `not p`, with `p` written the same as the other operand
    in simpler_negation?  -- `nonminimal_bool` rewrites that `not p`
    pub det out fires?
    pub det out kind: BoolRule

    ensure rule: fires? iff (absorbs? or (negates? and not simpler_negation?))
    ensure kind_rule: kind = if absorbs? then BoolRule::Absorption
        else if conj? then BoolRule::Contradiction else BoolRule::ExcludedMiddle
}
```

Each case of the table is an output of these components, and each rule a
pair of them:

```fren
set_option fren.lint.overly_complex_bool_expr "allow" in
pub comp absorption_written {
    in a?
    in b?
    pub det out or_first? := a? or (a? and b?)
    pub det out or_first_swapped? := a? or (b? and a?)
    pub det out or_last? := (a? and b?) or a?
    pub det out or_last_swapped? := (b? and a?) or a?
    pub det out and_first? := a? and (a? or b?)
    pub det out and_first_swapped? := a? and (b? or a?)
    pub det out and_last? := (a? or b?) and a?
    pub det out and_last_swapped? := (b? or a?) and a?
}

set_option fren.lint.unused_variables "allow" in
pub comp absorption_fixed {
    in a?
    in b?
    pub det out or_first? := a?
    pub det out or_first_swapped? := a?
    pub det out or_last? := a?
    pub det out or_last_swapped? := a?
    pub det out and_first? := a?
    pub det out and_first_swapped? := a?
    pub det out and_last? := a?
    pub det out and_last_swapped? := a?
}

refine absorption_sound: absorption_fixed refines absorption_written
refine absorption_complete: absorption_written refines absorption_fixed

set_option fren.lint.overly_complex_bool_expr "allow" in
pub comp contradiction_written {
    in a?
    pub det out first? := a? and not a?
    pub det out last? := not a? and a?
}

set_option fren.lint.constant_output "allow" in
set_option fren.lint.unused_variables "allow" in
pub comp contradiction_fixed {
    in a?
    pub det out first? := false
    pub det out last? := false
}

refine contradiction_sound: contradiction_fixed refines contradiction_written
refine contradiction_complete: contradiction_written refines contradiction_fixed

set_option fren.lint.overly_complex_bool_expr "allow" in
pub comp excluded_middle_written {
    in a?
    pub det out first? := a? or not a?
    pub det out last? := not a? or a?
}

set_option fren.lint.constant_output "allow" in
set_option fren.lint.unused_variables "allow" in
pub comp excluded_middle_fixed {
    in a?
    pub det out first? := true
    pub det out last? := true
}

refine excluded_middle_sound: excluded_middle_fixed refines excluded_middle_written
refine excluded_middle_complete: excluded_middle_written refines excluded_middle_fixed
```

## Branches sharing code

`branches_sharing_code`, `allow` by default, fires on `if C then A op X
else B op X`, where `op` is one binary operator in both branches and `X`
is written the same in both, and on its mirror, `if C then X op A else X
op B`. The fix moves `X` out of the `if`: `(if C then A else B) op X`, or
`X op (if C then A else B)`. The `if` is in parentheses, as
`lang::operand` requires of a conditional operand, and the whole is in
parentheses where [fixes need them](../Lint.md#parentheses-in-fixes); `A`
and `B` keep the parentheses they are written with. If both operands of
the branches are written the same, so are the branches, which
[`same_branches`](Suspicious/Expressions.md#branches-written-the-same)
reports, and this lint does not fire. Nor does it fire where the fix would
be outside the arithmetic that Fren accepts. For `*`, that is where `X`
mentions a variable or an uninterpreted function, and so does the `if` it
moves out, in `C`, `A` or `B` (see [Linear
arithmetic](../Lang/Expressions.md#linear-arithmetic)): `if a? then 3 * x
else 2 * x` would become `(if a? then 3 else 2) * x`, a product of two
operands that mention variables, but `if a? then x * 2 else y * 2` becomes
`(if a? then x else y) * 2`. For `div` and `mod`, it is where `X` is on
the left, since the `if` would be the divisor, which must be a literal or
a constant (see [Division and remainder](../Lang/Expressions.md#division-and-remainder)): `if a? then
x div 2 else y div 2` becomes `(if a? then x else y) div 2`, but `if a?
then x div 2 else x div 3` is left as it is. Its Clippy counterpart,
of the same name, is in `nursery`.

The fix keeps the meaning: an operator's value depends only on the values
of its operands, and the `if` picks the value of `A` or of `B` as before.
It keeps the guards. `X` is guarded by `C` in one branch and by `not C` in
the other, so it is evaluated wherever the conditional is; in the fix it
is evaluated there too, and has the same value. Under `and` and `or`, an
`X` on the right is also guarded by the left operand, `A` under `C` and
`B` under `not C`, and in the fix by `if C then A else B`, which holds
exactly where one of those does. `A` and `B` keep their guards, `C` and
`not C`, and under `and` and `or`, with `X` on the left, `X` as well.
`lint::branches_sharing_code` states when it fires:

```fren
pub comp branches_sharing_code {
    in same_op?          -- both branches apply the same binary operator
    in shared_left?      -- their left operands are written the same
    in shared_right?     -- their right operands are written the same
    in nonlinear?        -- the fix is outside Fren's arithmetic: `*` where the `if` and `X` both mention a variable or an uninterpreted function, or `div` or `mod` by the `if`
    pub det out fires?

    ensure rule: fires? iff (same_op? and shared_left? != shared_right? and not nonlinear?)

    expect same_branches: when shared_left? and shared_right?, not fires?
}
```

The refinements check both forms, on integers, with `-`, which is not
commutative, and on `Bool`s, with `and` and `or`, whose operands are
guarded:

```fren
set_option fren.lint.branches_sharing_code "allow" in
pub comp branches_sharing_code_written {
    in c?
    in a: Int
    in b: Int
    in x: Int
    in p?
    in q?
    in y?
    pub det out right: Int := if c? then a - x else b - x
    pub det out left: Int := if c? then x - a else x - b
    pub det out right_and? := if c? then p? and y? else q? and y?
    pub det out left_or? := if c? then y? or p? else y? or q?
}

pub comp branches_sharing_code_fixed {
    in c?
    in a: Int
    in b: Int
    in x: Int
    in p?
    in q?
    in y?
    pub det out right: Int := (if c? then a else b) - x
    pub det out left: Int := x - (if c? then a else b)
    pub det out right_and? := (if c? then p? else q?) and y?
    pub det out left_or? := y? or (if c? then p? else q?)
}

refine branches_sharing_code_sound: branches_sharing_code_fixed refines branches_sharing_code_written
refine branches_sharing_code_complete: branches_sharing_code_written refines branches_sharing_code_fixed
```

## Raw string literals

`needless_raw_string_hashes`, `allow` by default, fires on a raw string
[literal](../Lang/Lexical.md#literals), `r#"..."#`, with more `#`s than it
needs. A raw literal with `n` `#`s ends at the first `"` followed by `n`
`#`s, so it needs one `#` more than the longest run of `#` directly after
a `"` in its body, and none if its body has no `"`. The fix writes that
many: `r#"a.*"#` becomes `r"a.*"`, and `r##"say "hi""##` becomes `r#"say
"hi""#`. The body is the same, so the value is, and a literal has no
guard of its own. Its level is the one in effect at the item the literal
is in, as for [`invisible_characters`](Suspicious/Literals.md#invisible-characters).
`lint::needless_raw_string_hashes` states when it fires, and how many `#`s
the fix writes:

```fren
pub comp needless_raw_string_hashes {
    in hashes: Int       -- the `#`s around the literal
    in longest: Int      -- the longest run of `#` after a `"` in its body, or `-1` if it has no `"`
    pub det out fires?
    pub det out fewest: Int  -- the `#`s that the fix writes

    -- The literal ends where its `#`s say: no `"` in its body is followed by as many.
    assume counts: -1 <= longest < hashes

    ensure fewest_rule: fewest = longest + 1
    ensure rule: fires? iff hashes > fewest

    expect enough: fewest <= hashes
    expect no_quote: when longest = -1, fewest = 0
}
```

The fix is lexical, so the refinements check the examples above, whose
values are constants:

```fren
set_option fren.lint.constant_output "allow" in
set_option fren.lint.needless_raw_string_hashes "allow" in
pub comp raw_hashes_written {
    pub det out pattern: String := r#"a.*"#
    pub det out quote: String := r##"say "hi""##
}

set_option fren.lint.constant_output "allow" in
pub comp raw_hashes_fixed {
    pub det out pattern: String := r"a.*"
    pub det out quote: String := r#"say "hi""#
}

refine raw_hashes_sound: raw_hashes_fixed refines raw_hashes_written
refine raw_hashes_complete: raw_hashes_written refines raw_hashes_fixed
```
