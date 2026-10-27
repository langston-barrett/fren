# Records and functions

## Record literals

`inconsistent_struct_constructor`, `allow` by default, fires on a record
literal whose fields are not written in the order that its record declares
them, as in `Cell { column := 2, row := 1 }` where `struct Cell { row:
Int, column: Int }`. The fix writes them in that order, each with the text
it is written with, as `row := 1` or `row` alone, and leaves the text
between them where it is. Where that text has a comment, the lint has no
fix, since the comment would no longer be by the field it is about. A
record literal is the value whose fields have the values given, whatever
their order, and an expression has no effects, so the order in which they
are written cannot change what it means. No field's value is guarded by
another's: each is guarded by the literal's guard, before the fix and
after. `lint::inconsistent_struct_constructor` states when it fires:

```fren
pub mod lint

set_option fren.evidence "enumerated" in
pub proc inconsistent_struct_constructor(
    in_order?,           -- the literal's fields are written in the order its record declares them
): (det fires?) {
    ensure rule: fires? iff not in_order?
}

pub struct Cell { row: Int, column: Int }

set_option fren.lint.inconsistent_struct_constructor "allow" in
pub proc inconsistent_struct_constructor_written(a: Int, b: Int, row: Int, column: Int): (
    det given: Cell,
    det named: Cell,
) {
    out given := Cell { column := b, row := a }
    out named := Cell { column, row }
}

pub proc inconsistent_struct_constructor_fixed(a: Int, b: Int, row: Int, column: Int): (
    det given: Cell,
    det named: Cell,
) {
    out given := Cell { row := a, column := b }
    out named := Cell { row, column }
}

refine inconsistent_struct_constructor_sound: inconsistent_struct_constructor_fixed refines inconsistent_struct_constructor_written
refine inconsistent_struct_constructor_complete: inconsistent_struct_constructor_written refines inconsistent_struct_constructor_fixed
```

## Field names

`struct_field_names`, `allow` by default, is
[`enum_variant_names`](../Style.md#names) for the fields of a record, and
both front ends decide it with the same functions. A field's name is in
`snake_case`, so its words are compared without its final `?`, and in
lower case, with each other and with those of its record's name. It fires
in two cases:

- On a record of two or more fields, each of two or more words, that all
  start, or all end, with the same word, as in `struct Pump { pump_on?,
  pump_speed: Int }`. It is reported at the record's name.
- On a field whose words contain those of its record's name, one after
  another, and others, as `heat_pump_speed` does in `struct HeatPump {
  heat_pump_speed: Int, on? }`. It is reported at the field.

A field is read from a value of its record, `pump.speed`, which says what
the field is of, so the shared word, or the record's name, says nothing.
Clippy's `struct_field_names` is `pedantic` too, and by default fires on
records of three or more fields. `lint::struct_field_names` and
`lint::field_has_record_name` state when it fires:

```fren
pub proc struct_field_names(
    n_fields: Nat,
    shared_first?,       -- every field has two or more words, and all have the same first word
    shared_last?,        -- every field has two or more words, and all have the same last word
): (det fires?) {
    ensure rule: fires? iff (n_fields >= 2 and (shared_first? or shared_last?))
}

pub proc field_has_record_name(
    n_words: Nat,        -- the words of the field's name
    n_record_words: Nat,    -- the words of its record's name
    contains?,           -- the field's words have the record's, one after another
): (det fires?) {
    ensure rule: fires? iff (contains? and n_words > n_record_words)

    expect same_name: when n_words = n_record_words, not fires?
}
```

## Many `Bool`s

`struct_excessive_bools`, `allow` by default, fires on a record with more
than 3 `Bool` fields, and `fn_params_excessive_bools`, `allow` by default,
on a function with more than 3 `Bool` parameters, defined or not. 3 is
Clippy's default for both. Each value of every `Bool` is allowed, so four
`Bool` fields allow 16 combinations, some of which are probably not
meant, and a call `f(true, false, true, true)` does not say which argument
is which. The message of `struct_excessive_bools` suggests an enumeration
of the combinations meant, and that of `fn_params_excessive_bools` an
enumeration, or a record of named `Bool` fields. Neither has a fix.
`lint::struct_excessive_bools` and `lint::fn_params_excessive_bools` state
when they fire:

```fren
pub proc struct_excessive_bools(
    n_bools: Nat,        -- the record's `Bool` fields
): (det fires?) {
    ensure rule: fires? iff n_bools > 3
}

pub proc fn_params_excessive_bools(
    n_bools: Nat,        -- the function's `Bool` parameters
): (det fires?) {
    ensure rule: fires? iff n_bools > 3
}
```
