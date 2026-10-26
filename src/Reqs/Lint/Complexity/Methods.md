# Methods

## Chains of methods

`redundant_method_chain` fires on a chain of methods without arguments,
`e.m1.m2...`, that has a shorter form with the same value, and is fixable.
The shorter form rewrites each pair of methods in this table, until none is
left:

| Written | Shorter form | Since |
|---|---|---|
| `q.rev.rev` | `q` | reversing twice gives the elements back in their order |
| `r.inverse.inverse` | `r` | swapping the members of each pair twice gives the pair back |
| `r.closure.closure` | `r.closure` | the transitive closure is idempotent: a chain of pairs of `r.closure` joins chains of pairs of `r` into one |
| `r.inverse.domain` | `r.range` | the first members of the pairs `(b, a)` are the second members of the pairs `(a, b)` |
| `r.inverse.range` | `r.domain` | and the other way around |
| `r.inverse.card` | `r.card` | swapping the members of a pair is one-to-one, so the pairs are as many |
| `q.rev.len` | `q.len` | reversing keeps every element |
| `r.closure.domain` | `r.domain` | `r` is within `r.closure`, and a chain from `a` starts with a pair `(a, b)` of `r` |
| `r.closure.range` | `r.range` | and a chain to `c` ends with a pair `(b, c)` of `r` |

Each holds for every relation and sequence, empty ones included: the
inverse and the closure of an empty relation are empty, and so are its
domain and range, and `[].rev` is `[]`. Each rewrite shortens the chain, so
rewriting ends, and the form it ends with does not depend on which pair is
rewritten first: where two pairs overlap, as in `r.inverse.inverse.domain`,
either order gives `r.domain`. The message is reported once, at the whole
chain. The fix replaces it with its shorter form, in which the receiver
keeps the text it is written with. When no method is left, the receiver
alone is written without the parentheses a receiver may need, and put in
parentheses where [fixes need them](../../Lint.md#parentheses-in-fixes), so `(a ++ b).rev.rev = c`
becomes `a ++ b = c`. A method has no guard of its own, and the fix
evaluates the receiver where the chain did, so it keeps every guard: it
only stops evaluating methods, which index nothing.

`lint::method_chain` states the rewrite of a pair, `e.inner.outer`: to `e`,
to `e.single`, or none:

```fren
pub mod lint

use lang::Method

pub enum ChainFix { Keep, Receiver, Single }

pub comp method_chain {
    use lang::Method::{Card, Closure, Domain, Inverse, Len, Range, Rev}
    in inner: Method     -- the method of `e.inner`
    in outer: Method     -- the method called on `e.inner`
    pub det out fix: ChainFix
    pub det out single: Method  -- for `Single`, the method of the shorter form

    ensure rule: fix = if inner = outer and inner in {Rev, Inverse} then ChainFix::Receiver
        else if (inner = Inverse and outer in {Domain, Range, Card}) or (inner = Rev and outer = Len)
        or (inner = Closure and outer in {Closure, Domain, Range}) then ChainFix::Single
        else ChainFix::Keep
    ensure shorter: single = if inner = Inverse and outer = Domain then Range
        else if inner = Inverse and outer = Range then Domain
        else outer

    expect receiver_twice: when fix = ChainFix::Receiver, inner = outer
    expect closure_kept: when inner = Closure and fix = ChainFix::Single, single = outer
}
```

## Searches

`manual_method` fires on a search written with `index_of`, `slice` or `at`
that a [method](../../Lang/Expressions.md#methods) says directly, on a string
or a sequence, whose methods have the same values:

| Written | Fix |
|---|---|
| `s.index_of(t, 0) >= 0`, `s.index_of(t, 0) > -1`, `s.index_of(t, 0) != -1` | `s.contains?(t)` |
| `s.index_of(t, 0) < 0`, `s.index_of(t, 0) <= -1`, `s.index_of(t, 0) = -1` | `not s.contains?(t)` |
| `s.index_of(t, 0) = 0` | `s.starts_with?(t)` |
| `s.slice(0, t.len) = t` | `s.starts_with?(t)` |
| `s.at(0) = t`, `s.at(0) != t` | `s.starts_with?(t)`, `not s.starts_with?(t)` |
| `s.at(s.len - 1) = t`, `s.at(s.len - 1) != t` | `s.ends_with?(t)`, `not s.ends_with?(t)` |
| `s.slice(i, 1)` | `s.at(i)` |

The bound, or the `t` that the slice or `at` is compared with, may be on the
left. For the slice, the receiver of `len` is [written the
same](Comparisons.md) as the other operand, or is it in parentheses, and for
`at`, as the receiver of `at`. For `at`, `t` is a string literal of one
character, such as `"a"` or `"\n"`, or a sequence literal of one element,
such as `[x]`. The last row is not a comparison: it fires on any `slice`
whose length is written `1`.

`s.index_of(t, 0)` is the first position at which `t` occurs in `s`, which
is at least `0`, or `-1` if there is none. If `t` is `""`, it is `0`, since
`0 <= 0 <= s.len`, and `""` occurs in every `s`, as its prefix. If `s` is
shorter than `t`, `t` occurs nowhere in it, and it is `-1`. So the index is
at least `0` exactly when `t` occurs in `s`, which is `s.contains?(t)`, and
it is `0` exactly when `t` occurs at position `0`, which is
`s.starts_with?(t)`. `s.slice(0, t.len)` is the first `t.len` elements of
`s`, or all of `s` if it is shorter, and `""` if `t` is `""` (`n > 0`
fails) or `s` is (`0 < s.len` fails). It is `t` exactly when `t` is a
prefix of `s`: if `t` is `""`, both are `""`, and if `s` is shorter than
`t`, so is the slice. Every method is total, and the fix evaluates `s` and
`t` where the comparison did, so it keeps the guards.

`s.slice(i, 1)` is `""` unless `0 <= i < s.len`, since `n > 0` holds, and
then the one character at `i`, since a slice is cut short only at the end
of `s`. That is `s.at(i)` for every `i`, negative ones and those past the
end included. So `s.at(0)` is `""` if `s` is, and its first character
otherwise; it is never `t`, of one character, if `s` is `""`, and `t` is
then not a prefix of `s`; otherwise it is `t` exactly when `t` is a prefix
of `s`. `s.at(s.len - 1)` is `s.at(-1)`, which is `""`, if `s` is `""`, and
its last character otherwise, so likewise it is `t` exactly when `t` is a
suffix of `s`. For a sequence, `q.at(i)` is `[q[i]]` or `[]` and `t` is
`[x]`, and the same argument holds element by element. `t` must have one
character: `s.at(0)` is never `"ab"`, though `"ab"` may be a prefix of `s`,
and `s.at(0) = ""` says that `s` is empty, which is
[`length_zero`](../Style.md#empty-collections)'s. `lint::one_character` states
these values, comparing the slice with any string `u`, which its `impl`
proves for strings from the meaning of the methods in Lean:

```fren
set_option fren.lint.undecidable "allow" in
pub comp one_character {
    in s: String
    in t: String         -- a string of one character
    in i: Int
    in u: String         -- any string
    pub det out first?   -- `s.at(0) = t`
    pub det out last?    -- `s.at(s.len - 1) = t`
    pub det out slice?   -- `s.slice(i, 1) = u`

    assume one: t.len = 1

    ensure first: first? iff s.starts_with?(t)
    ensure last: last? iff s.ends_with?(t)
    ensure sliced: slice? iff s.at(i) = u
}
```

`lint::index_test` states which comparisons of `index_of` fire, from the
operator and the bound, with the call on the left, and checks each against
every value that the call can take:

```fren
pub enum IndexTest { Found, Absent, AtStart, Other }

pub comp index_test {
    use self::Comparison::{Eq, Ge, Gt, Le, Lt, Ne}
    use self::IndexTest::{Absent, AtStart, Found, Other}
    in op: Comparison
    in bound: Int
    in position: Int     -- any value of `s.index_of(t, 0)`
    pub det out test: IndexTest

    assume positions: position >= -1

    ensure rule: test = match op {
        Ge => if bound = 0 then Found else Other,
        Gt | Ne => if bound = -1 then Found else Other,
        Lt => if bound = 0 then Absent else Other,
        Le => if bound = -1 then Absent else Other,
        Eq => if bound = -1 then Absent else if bound = 0 then AtStart else Other,
    }

    expect found: when test = Found, compares?(op, position, bound) iff position >= 0
    expect absent: when test = Absent, compares?(op, position, bound) iff position = -1
    expect at_start: when test = AtStart, compares?(op, position, bound) iff position = 0
}
```

The fix can bring a spec into the [decidable core](../../Lang/Decidability.md).
`index_of`, and `slice` of a sequence, are outside it unless every operand
is a constant, but `contains?` and `starts_with?` of a string are in it
when `t` is a constant, and `starts_with?` of a sequence is in it when `t`
is a literal. So on strings, each fix of `index_of` with a constant `t`
brings the comparison into the core, and the fix of `slice` changes
nothing, since `s.slice(0, t.len) = t` is already in the core when `t` is a
constant. On sequences, the fixes to `starts_with?` with a literal `t` do,
and those to `contains?` do not, since `contains?` of a sequence is outside
the core too. On strings, the fix of `s.at(s.len - 1) = t`, whose position
is not a constant, brings it into the core, that of `s.at(0) = t` changes
nothing, and so does that of `slice`, since `at` and `slice` are in the
core together.

## Whole slices

`redundant_slicing` fires on `s.slice(0, s.len)`, of a string or a
sequence, where the receiver of `len` is written the same as that of
`slice`, or is it in parentheses, and is fixable. Its fix is the receiver,
which keeps the text it is written with, and is put in parentheses where
[fixes need them](../../Lint.md#parentheses-in-fixes), or where it is a receiver: `(a ++ b).slice(0, (a ++ b).len).len` becomes `(a ++
b).len`. If `s` is `""`, the slice is `""`, which is `s`, since `0 <
s.len` fails; otherwise it is the `s.len` characters from position `0`,
which are all of `s`. So the fix has the slice's value for every `s`. It
evaluates the receiver where the slice did, and nothing else, so it keeps
the guards, and it brings the expression into the [decidable
core](../../Lang/Decidability.md#strings), where a slice whose length is not
a constant is not. `lint::redundant_slicing` states when it fires, and the
value of the slice, compared with any string `u`, which its `impl` proves
for strings:

```fren
set_option fren.lint.undecidable "allow" in
pub comp redundant_slicing {
    in whole?            -- it is written `s.slice(0, s.len)`, the receivers written the same
    in s: String
    in i: Int            -- the position
    in n: Int            -- the length
    in u: String         -- any string
    pub det out fires?
    pub out slice?       -- `s.slice(i, n) = u`

    assume written: when whole?, i = 0 and n = s.len

    ensure rule: fires? iff whole?
    ensure value: when fires?, slice? iff s = u
}
```
