# Methods and indexes

## Indexes

`index_after_use` fires on `a and b`, where `a` indexes a sequence `q` and
`b` bounds it: it mentions `q.len`, or compares `q` with `[]`. The index is
probably meant to be guarded by `b`, but `and` guards its right operand by
its left (see [Expressions](../../Lang/Expressions.md#sequences)), so the
[definedness check](../../Check.md#definedness) fails. The fix swaps the
operands, which does not change the meaning. The lint looks only at the
text, never at the solver:

```fren
pub mod lint

set_option fren.evidence "enumerated" in
pub comp index_after_use {
    in indexes_left?     -- `a` indexes a sequence `q`
    in bounds_right?     -- `b` mentions `q.len`, or compares `q` with `[]`
    pub det out fires?

    ensure rule: fires? iff (indexes_left? and bounds_right?)
}
```

`negative_position` fires on a position written as a negative integer
literal, `-k` for a `k` other than `0`: the index of `q[-k]`, the first
argument of `at`, `slice` and `update`, and the second of `index_of`.
Fren has no negative indexing, so `q[-1]` is not the last element, as it
would be in Python: it is unspecified, which the definedness check reports
only as an index that may be out of range. The
[methods](../../Lang/Expressions.md#methods) are total, so `s.at(-1)` and
`s.slice(-3, 3)` are always `""`, `q.update(-1, x)` is always `q`, and
`s.index_of(t, -1)` is always `-1`, which no check reports. It is reported
at the index or the method call, and the message says what it is and
suggests counting from the end, as in `q[q.len - 1]` or `s.at(s.len - 1)`,
or, for `index_of`, searching from `0`. It has no fix, since which
position was meant is not certain. `lint::negative_position` states when
it fires:

```fren
pub comp negative_position {
    use lang::Method
    use lang::Method::{At, IndexOf, Slice, Update}
    in index?            -- the position is the index of `q[i]`, not an argument
    in method: Method    -- the method, for an argument
    in arg: Nat          -- the position of the argument, from 0
    in negative?         -- it is written `-k`, for an integer literal `k` other than `0`
    pub det out fires?

    ensure rule: fires? iff (negative? and (index? or match method {
        At | Slice | Update => arg = 0,
        IndexOf => arg = 1,
        _ => false,
    }))
}
```

## Empty arguments

`empty_argument` fires on a method applied to an empty argument, where
its value at that [edge](../../Lang/Expressions.md#methods) does not depend on
the receiver as it seems to. An argument is empty if it is written `""`
or `[]`, or, as the length of `slice`, `0`. Where `s` is the receiver, a
string or a sequence, and `e` the empty argument:

| Written | Value |
|---|---|
| `s.starts_with?(e)`, `s.ends_with?(e)`, `s.contains?(e)` | `true` |
| `s.replace(e, b)` | `b ++ s` |
| `s.replace_all(e, b)` | `s` |
| `s.index_of(e, i)` | `i` if `0 <= i <= s.len`, and `-1` otherwise |
| `s.slice(i, 0)` | `""`, or `[]` |

The message says what the expression is. It has no fix: the likely
mistake is the argument, and writing the value instead would keep the
mistake and hide it. `lint::empty_argument` states when it fires, from the
method and the position of an empty argument:

```fren
pub comp empty_argument {
    use lang::Method
    use lang::Method::{Contains, EndsWith, IndexOf, Replace, ReplaceAll, Slice, StartsWith}
    in method: Method
    in index: Nat        -- the position of the argument, from 0
    in empty?            -- it is written `""` or `[]`, or `0`
    pub det out fires?

    ensure rule: fires? iff (empty? and match method {
        StartsWith | EndsWith | Contains | Replace | ReplaceAll | IndexOf => index = 0,
        Slice => index = 1,
        _ => false,
    })
}
```

## Replacements

`no_effect_replace` fires on `s.replace(a, b)` and `s.replace_all(a, b)`,
where `a` and `b` are written the same, and is fixable: replacing an
occurrence of `a` with `a` leaves `s` as it was. At the
[edge](../../Lang/Expressions.md#methods) where `a` is `""`, `s.replace("",
"")` is `"" ++ s` and `s.replace_all("", "")` is `s`, which are both `s`,
so the fix is `s` for every `s` and `a`, of a string or, for `replace`, a
sequence; [`empty_argument`](#empty-arguments) fires there too. The
fix keeps the receiver's text, and puts it in parentheses where
[fixes need them](../../Lint.md#parentheses-in-fixes), or where it is a receiver. It only stops
evaluating `a` and `b`, so no guard is weaker, and it brings the expression
into the [decidable core](../../Lang/Decidability.md#strings), which `replace`
and `replace_all` are outside of. `lint::no_effect_replace` states when it
fires, and the values of the calls, compared with any string `u`, which its
`impl` proves for strings:

```fren
set_option fren.lint.undecidable "allow" in
pub comp no_effect_replace {
    in same?             -- the arguments are written the same
    in s: String         -- the receiver
    in a: String         -- the first argument
    in b: String         -- the second
    in u: String         -- any string

    assume written: when same?, a = b
    pub det out fires?
    pub out replaced?    -- `s.replace(a, b) = u`
    pub out replaced_all?  -- `s.replace_all(a, b) = u`

    ensure rule: fires? iff same?
    ensure first: when fires?, replaced? iff s = u
    ensure all: when fires?, replaced_all? iff s = u
}
```
