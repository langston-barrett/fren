# Records

These lints of the `style` group find a shorter way to write a record
literal or a record update. Both are fixable.

## Fields of updates

In a [record update](../../Lang/Expressions.md#record-updates) of `r`,
`redundant_bindings` fires on a field `x := x` as in a record literal,
and on a field `x := r.x`, which gives `x` the value the update reads
from `r` without it. It fires on `x := r.x` only when `r` is a name or a
dotted path of names, such as `s` or `c.s`, so that `r.x` reads the field
`x` of `r` whatever `r` is, and only when the update gives some other
field a value that is not such a copy: the fix removes the field, with the
comma before it, or for the first field, the comma after it, and an
update gives at least one field. `{ r with x := r.x }` alone is `r`, which
is left to a lint of its own, as Clippy's
`unnecessary_struct_initialization` is. Removing the field keeps the meaning,
since the update then reads `x` from `r`; it keeps the guards, since an
update's fields and its updated value are evaluated unguarded, and `r`
is still evaluated; and the update mentions what it did, since `r.x`
mentions only what `r` does. `lint::field_copy` states when it fires on
`x := r.x`, from the texts as [written](../../Lint.md#written-the-same):

```fren
pub mod lint

set_option fren.evidence "enumerated" in
pub proc field_copy(
    path?,       -- `r` is a name or a dotted path of names
    copy?,       -- the value is written the same as `r`, then `.`, then the field's name
    others?,     -- the update gives another field a value that is not such a copy
): (det fires?) {
    ensure rule: fires? iff (path? and copy? and others?)
}
```

The fix's meaning is checked by refinement, each way, for a record of
three fields:

```fren
pub struct Triple { a: Int, b: Int, c: Int }

set_option fren.lint.redundant_bindings "allow" in
pub proc field_copy_written(t: Triple, n: Int): (det u: Triple, det v: Triple) {
    out u := { t with a := t.a, b := n }
    out v := { t with b := n, c := t.c }
}

pub proc field_copy_fixed(t: Triple, n: Int): (det u: Triple, det v: Triple) {
    out u := { t with b := n }
    out v := { t with b := n }
}

expect field_copy_sound(t: lint::Triple, n: Int) {
    use lint
    call concrete := field_copy_fixed(t, n)
    refines concrete field_copy_written(t, n)
}
expect field_copy_complete(t: lint::Triple, n: Int) {
    use lint
    call concrete := field_copy_written(t, n)
    refines concrete field_copy_fixed(t, n)
}
```

## Record literals

`manual_record_update` fires on a [record literal](../../Lang/Expressions.md#records)
that reads more of its fields from one value `r` than it gives new
values, and gives at least one: each field `x := r.x` that reads from `r`
the field it gives is a copy. The fix is the [record
update](../../Lang/Expressions.md#record-updates) `{ r with ... }` of the
other fields, written as they are and in their order, which is shorter,
and stays right when a field is added to the record. With as many copies
as new values, as in `Point { x := n, y := p.y }`, the literal is about as
long and says as plainly what each field is, so the lint does not fire. `r` is a
value of the literal's own record, as the elaborator types it, so that
the update has the literal's type; for a value of another record with
fields of the same names, the lint does not fire. Of the values that
fields are copied from, by their text as
[written](../../Lint.md#written-the-same), `r` is the one with the most
copies, and the first of those with as many. A literal that copies every
field from `r` is `r`, which is left to a lint of its own, as Clippy's
`unnecessary_struct_initialization` is. Clippy has no lint like this
one, since Rust's struct update syntax is mostly used for many fields.

The fix keeps the meaning, since the update reads every field it does not
give from `r`. It keeps the guards, since a record literal's fields, an
update's fields and its updated value are all evaluated unguarded, and
`r`, evaluated once rather than once for each copy, has the same value
each time. The update mentions what the literal did: `r`, which each copy
mentions, and the other fields' values. `lint::manual_record_update`
states when it fires:

```fren
pub proc manual_record_update(
    n_fields: Nat,     -- the fields of the record
    n_copied: Nat,     -- the fields copied from `r`
): (det fires?) {
    assume within: n_copied <= n_fields

    ensure rule: fires? iff n_copied < n_fields < 2 * n_copied

    expect gives_some: when fires?, n_copied < n_fields
    expect copies_most: when fires?, n_fields - n_copied < n_copied
    expect copies_two: when fires?, n_copied >= 2
}
```

The fix's meaning is checked by refinement, each way:

```fren
set_option fren.lint.manual_record_update "allow" in
pub proc manual_record_update_written(t: Triple, n: Int): (det u: Triple, det v: Triple) {
    out u := Triple { a := n, b := t.b, c := t.c }
    out v := Triple { a := t.a, b := n + 1, c := t.c }
}

pub proc manual_record_update_fixed(t: Triple, n: Int): (det u: Triple, det v: Triple) {
    out u := { t with a := n }
    out v := { t with b := n + 1 }
}

expect manual_record_update_sound(t: lint::Triple, n: Int) {
    use lint
    call concrete := manual_record_update_fixed(t, n)
    refines concrete manual_record_update_written(t, n)
}
expect manual_record_update_complete(t: lint::Triple, n: Int) {
    use lint
    call concrete := manual_record_update_written(t, n)
    refines concrete manual_record_update_fixed(t, n)
}
```
