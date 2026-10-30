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

expect inconsistent_struct_constructor_sound(a: Int, b: Int, row: Int, column: Int) {
    call concrete := inconsistent_struct_constructor_fixed(a, b, row, column)
    refines concrete inconsistent_struct_constructor_written(a, b, row, column)
}
expect inconsistent_struct_constructor_complete(a: Int, b: Int, row: Int, column: Int) {
    call concrete := inconsistent_struct_constructor_written(a, b, row, column)
    refines concrete inconsistent_struct_constructor_fixed(a, b, row, column)
}
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

## Function parameters given one function

`needless_higher_order`, `allow` by default, fires on a function parameter
of a private [higher-order function](../../Lang/HigherOrder.md) to which
every application in the file gives the same closure, [written the
same](../../Lint.md#written-the-same), whose body mentions no name but the
closure's own parameters: literals, operators and methods only, as
`|y| 2 * y`. The parameter is then the same function everywhere, and the
closure's body could be written in the function's body, where the
parameter is applied, without the parameter. A name that the closure
mentions might not mean the same there, or anything: a name of where the
closure is written (a variable, a binder, a parameter, a call or a name
of a `let` or `where`), an item declared after the function, which Fren's
declare-before-use rule hides from its body, or a name that the
function's own parameters shadow. So the lint asks that the closure
mention none, which is enough for the body to mean the same in the
function, and does not look for which names would. For the same reason
it does not fire where every application gives the same function's name,
nor on a lambda match, nor on a generic function, whose body is written
over its type parameters, where `|y| y + 1` need not type-check. It is
reported at the parameter. It does not fire on a public function, which
other files may apply, nor where nothing applies the function, which
[`dead_code`](../Unused.md#dead-code) reports. It has no fix, since it
changes the function's parameters, and with them every application. Clippy
has no such lint.

The names that a closure mentions are those its body has free, in the
[model of scopes](../Unused.md#scopes), but for the closure's own
parameters. For this lint, a node of the body's tree mentions every name
written directly in it whose meaning depends on where it is written: a
variable, the function that an application applies, the first segment of
a longer path (`m::f`, `E::V`), a record literal's type, a variant that a
pattern applies or writes with `::`, a constant that bounds a range
pattern, and each name in a type. A binder in the body, of a quantifier,
a `let`, a `match` arm, a pattern test or a closure inside it, declares
its names at the node whose scope they are. Each name is read whole, by
the lexer's rule for identifiers, so `y'` is not `y`. `free_names` is
`scope`'s `free`, as a function, which `lint::closure_names` checks:

```fren
-- The names that the tree `t` has free: those it mentions where neither
-- the node of the mention nor one around it declares them (`scope`).
pub fn free_names(t: Tree): Set<Local> :=
    (t.mentions minus ((t.children.closure.inverse join t.declares) union t.declares)).image(t.children.closure.image({t.root}) union {t.root})

-- The names that a closure of the parameters `params` and the body `body`
-- mentions, which may mean something else, or nothing, where the closure
-- is moved.
pub fn closure_names(params: Set<Local>, body: Tree): Set<Local> := free_names(body) minus params

set_option fren.lint.arbitrary_source_item_ordering "expect" in
pub proc closure_names_scope(params: Set<Local>, body: Tree): (det names: Set<Local>) {
    call s := scope(body)

    out names := closure_names(params, body)

    expect free: names = s.free minus params
    -- A closure that mentions only its parameters mentions no name.
    expect own: when s.free subset params, names = {}
}
```

`lint::needless_higher_order` states when it fires, from what each
application gives the parameter: its written form, and, as a closure, its
parameters and the tree of its body. A function's name, `g`, is the
closure `|x| g(x)`, whose body mentions `g`.

```fren
-- What an application gives a function parameter, as
-- `needless_higher_order` reads it: its written form, and the closure's
-- parameters and body.
pub struct GivenFunction { form: String, params: Set<Local>, body: Tree }

set_option fren.lint.undecidable "allow" in
pub proc needless_higher_order(
    given: Seq<GivenFunction>,       -- what each application in the file gives the parameter
    pub?,                            -- the function is public
    generic?,                        -- the function is generic
): (det fires?) {
    ensure rule: fires? iff (not pub? and not generic? and given != []
        and (forall (k: Int), when 0 <= k < given.len,
        closure_names(given[k].params, given[k].body) = {} and given[k].form = given[0].form))
}
```
