/-!
# Error codes

Every error and warning Fren reports, except internal errors, has a code,
explained by `fren --explain CODE` as rustc explains its codes: what is
wrong, an erroneous example, why, and the example fixed.

In each explanation, the first ```` ```fren ```` block is the erroneous
example and the others are fixed versions. `lake test` checks that the
erroneous example reports the code (with `args`, if they are not `none`),
and that the fixed versions do not.

Codes are grouped by hundreds: `F01xx` syntax, `F02xx` names and items,
`F03xx` types, `F04xx` instances and where variables may be mentioned,
`F05xx` traceability, `F06xx` the results of checks, `F07xx` lints and
their levels.
-/

namespace Fren.Core

structure ErrorCode where
  code : String
  /-- Markdown. -/
  explanation : String
  /-- The `fren` arguments that report the code on the erroneous example,
  before the file; `none` if it needs more than the example, such as other
  files. -/
  args : Option (List String) := some ["check"]
  deriving Inhabited

def errorCodes : Array ErrorCode := #[
  { code := "F0101", explanation := r#"A character that is not part of Fren's syntax.

Erroneous code example:

```fren
comp c { in x: Int req r: x > 0 $ }
```

Fren is lexed as Lean is, but uses only these symbols:

```text
::  ::*  ::{  :  :=  ,  (  )  {  }  =  !=  <  <=  >  >=  +  -  *
```

Comments start with `--`, not `#` or `//`. Remove the character, or replace
it with the Fren syntax for what you meant:

```fren
comp c { in x: Int pub out y? req r: y? iff x > 0 }
```
"# },
  { code := "F0102", explanation := r#"A block comment is not closed.

Erroneous code example:

```fren
/- A comment that never ends.
comp c {}
```

A block comment starts with `/-` and ends with `-/`. Block comments nest,
so each `/-` inside a comment needs its own `-/`.

```fren
/- A comment that ends. -/
comp c {}
```
"# },
  { code := "F0103", explanation := r#"A string literal is not closed.

Erroneous code example:

```fren
comp c {}
trusted c: "the hardware guarantees it
```

A string literal starts and ends with `"` on the same line. Inside it, write
`\"` for a quote and `\\` for a backslash.

```fren
comp c {}
trusted c: "the hardware guarantees it"
```
"# },
  { code := "F0104", explanation := r#"The parser found a token it did not expect.

Erroneous code example:

```fren
comp c { in x: Int, in y: Int }
```

The message says what was found and what was expected instead. Here, the
members of a component are not separated by commas.

```fren
comp c { in x: Int in y: Int }
```

See the grammar in Fren's reference manual (`Grammar.md`).
"# },
  { code := "F0105", explanation := r#"An operator from another language, which Fren does not have.

Erroneous code example:

```fren
comp c { in x: Int pub out y? req r: y? iff x == 1 }
```

Fren's operators are words where other languages use symbols:

- `=` for equality, not `==`
- `and`, `or` and `not`, not `&&`, `||` and `!`
- `when a, b` for implication, not `=>`

`!=` is inequality, as in other languages. There is no division.

```fren
comp c { in x: Int pub out y? req r: y? iff x = 1 }
```
"# },
  { code := "F0106", explanation := r#"The condition of `when` or `unless` is not followed by a comma.

Erroneous code example:

```fren
comp c { in x: Int pub out y: Int req r: when x > 1 y = 3 }
```

`when c, e` says that `e` holds whenever `c` does, and `unless c, e` that
`e` holds whenever `c` does not. The comma ends the condition.

```fren
comp c { in x: Int pub out y: Int req r: when x > 1, y = 3 }
```
"# },
  { code := "F0107", explanation := r#"A chain of `iff`s.

Erroneous code example:

```fren
comp c { in a? in b? pub out d? req r: d? iff a? iff b? }
```

`iff` is not associative, so `a iff b iff c` has no single obvious meaning.
Add parentheses to say which you mean.

```fren
comp c { in a? in b? pub out d? req r: d? iff (a? iff b?) }
```
"# },
  { code := "F0108", explanation := r#"A chain of comparisons.

Erroneous code example:

```fren
comp c { in x: Int pub out ok? req r: ok? iff 0 <= x <= 10 }
```

Comparisons do not chain as in mathematics: `0 <= x <= 10` would compare a
`Bool` with `10`. Split the chain with `and`.

```fren
comp c { in x: Int pub out ok? req r: ok? iff 0 <= x and x <= 10 }
```
"# },
  { code := "F0109", explanation := r#"`when` or `unless` is used as an operand without parentheses.

Erroneous code example:

```fren
comp c { in x: Int pub out y? req r: y? iff x > 0 and when x > 1, x > 2 }
```

`when` and `unless` have the lowest precedence, and their body extends as
far right as possible. Inside another expression, or as the value of an
instance's binding (where it would swallow the bindings after it), wrap
them in parentheses.

```fren
comp c { in x: Int pub out y? req r: y? iff (x > 0 and (when x > 1, x > 2)) }
```
"# },
  { code := "F0110", explanation := r#"An input is declared `pub`.

Erroneous code example:

```fren
comp c { pub in x: Int }
```

Inputs are always public: whoever instantiates the component binds them.
Only outputs are private by default, so only `out` takes `pub`.

```fren
comp c { in x: Int }
```
"# },
  { code := "F0111", explanation := r#"A name with a `.` whose first component is not an instance or a value.

Erroneous code example:

```fren
enum E { A, B }
comp c { in e: E pub out y? req r: y? iff e = E.A }
```

`a.b` means the variable `b` of the instance `a`, or the field or method
`b` of the value `a`, a variable or a constant. Paths, such as an item of a
module or a variant of an enum, are separated by `::`.

```fren
enum E { A, B }
comp c { in e: E pub out y? req r: y? iff e = E::A }
```
"# },
  { code := "F0112", explanation := r#"Lean code in a file given to the `fren` command.

Erroneous code example:

```fren
def limit := 10
```

The `fren` command checks Fren specs without Lean, so it accepts only Fren
items: `mod`, `use`, `enum`, `comp`, `tested` and `trusted`. Lean code,
including `impl`, belongs in a Lean file that opens `Fren.Lang`, checked by
`lake build`.

```fren
comp c { in x: Int pub out y? req r: y? iff x <= 10 }
```
"# },
  { code := "F0113", explanation := r#"A modifier on a member it does not apply to.

Erroneous code example:

```fren
comp c { det in x: Int }
```

`pub` and `det` apply only to outputs: `pub out` is visible to whoever
instantiates the component, and `det out` must be determined by the
inputs. Inputs are always public, and always determined.

```fren
comp c { in x: Int pub det out y: Int req r: y = x }
```
"# },
  { code := "F0114", explanation := r#"An input with a definition.

Erroneous code example:

```fren
comp c { in x: Int := 3 }
```

Inputs are chosen by the component's environment, so they cannot be
defined. Only an output can have a definition, `out x: T := e`, which
makes it stand for `e`. To say what an input equals, state it in an
assumption; to name an expression, define an output:

```fren
comp c { in x: Int out next: Int := x + 1 pub out y: Int req r: y = next }
```
"# },
  { code := "F0115", explanation := r#"An unknown escape in a string literal.

Erroneous code example:

```fren
const PATH: String := "C:\qux"
```

A string literal's escapes are Lean's: `\\`, `\"`, `\'`, `\n`, `\t`, `\r`,
`\xHH` and `\uHHHH`. Write `\\` for a backslash, or use a raw literal,
which has no escapes:

```fren
const PATH: String := r"C:\qux"
```
"# },
  { code := "F0116", explanation := r#"A character beyond U+2FFFF in a string literal.

Erroneous code example, with the character U+F0000:

```fren
const MARK: String := "󰀀"
```

A `String` has the characters of the solver's theory of strings, the code
points from 0 to U+2FFFF, so a literal may contain only those. Characters
beyond it, in the supplementary planes 3 to 16, are rarely used; write the
literal without them.
"# },
  { code := "F0117", explanation := r#"A pattern that does not parse.

Erroneous code example:

```fren
comp c { in s: String pub out p? req r: p? iff s.matches?(r"\d+") }
```

Patterns are a subset of POSIX extended regular expressions: characters,
`.`, classes such as `[a-z_]` and `[^0-9]`, `|`, `*`, `+`, `?`, `{m}`,
`{m,n}` and parentheses. `\` escapes one of `\ . [ ] ( ) * + ? { } | ^ -`.
There are no anchors, since the whole string must match, and no classes
such as `\d`:

```fren
comp c { in s: String pub out p? req r: p? iff s.matches?(r"[0-9]+") }
```
"# },
  { code := "F0118", explanation := r#"A reversed range in a pattern's class.

Erroneous code example:

```fren
comp c { in s: String pub out p? req r: p? iff s.matches?(r"[z-a]+") }
```

A range is written from the lower character to the higher, by code point,
so `[z-a]` would match nothing:

```fren
comp c { in s: String pub out p? req r: p? iff s.matches?(r"[a-z]+") }
```
"# },
  { code := "F0119", explanation := r#"A lexeme that Lean reads as one identifier, but that is not one of Fren's.

Erroneous code example:

```fren
comp c { in y: Int pub out z? req r: z? iff y!!=1 }
```

Fren's identifiers are ASCII letters, digits, `_` and `'`, with `.` between
components, an optional `?` at the end, and then an optional `!`, which
marks a declaration that shadows. Lean's are a superset: they may have `?`
and `!` anywhere after the first character, letters other than ASCII, such
as `α`, and quoted components, such as `«a b»`. So that a spec reads alike
in Lean and in the `fren` command, both report what Lean would read
differently. Here Lean reads `y!!` then `=`, so write spaces around `!=`:

```fren
comp c { in y: Int pub out z? req r: z? iff y != 1 }
```

An identifier such as `a?b` or `xα` needs another name, such as `a_b` or
`x_alpha`.
"# },
  { code := "F0120", explanation := r#"A number that is not an integer literal.

Erroneous code example:

```fren
const ONE: Int := 0_1
```

Integer literals are Lean's: decimal digits, or `0x`, `0b` or `0o` and the
digits of that base, with `_`s between the digits or after the base, as in
`1_000` or `0x_FF`, ending in a digit. Lean reads `0_1` as a number but
cannot give its value, so it is not an integer literal either:

```fren
const ONE: Int := 1
```

The `fren` command also reports this for other malformed numbers, such as
`1_`, `0x` or `0b2`. In Lean, Lean's own parser reports those first.
"# },
  { code := "F0201", explanation := r#"A name that is not in scope.

Erroneous code example:

```fren
comp c { in x: Int pub out y: Int req r: y = z }
```

A name in an expression is a variable of the component, an item declared
in or imported into the current module, or a variant opened with
`use E::*`. Check the spelling, declare the name, or import it with `use`.

```fren
comp c { in x: Int pub out y: Int req r: y = x }
```
"# },
  { code := "F0202", explanation := r#"An item that is private to another module.

Erroneous code example:

```fren
mod a
enum Hidden { H }

mod b
use a::Hidden
```

An item is visible in the module that declares it and that module's
submodules. Declare it `pub` to make it visible everywhere.

```fren
mod a
pub enum Hidden { H }

mod b
use a::Hidden
```
"# },
  { code := "F0203", explanation := r#"An enum has no variant of that name.

Erroneous code example:

```fren
enum Mode { Off, Heat }
comp c { in m: Mode pub out on? req r: on? iff m = Mode::Cool }
```

The message lists the enum's variants. Check the spelling, or add the
variant to the enum.

```fren
enum Mode { Off, Heat, Cool }
comp c { in m: Mode pub out on? req r: on? iff m = Mode::Cool }
```
"# },
  { code := "F0204", explanation := r#"A path continues after something that has no members.

Erroneous code example:

```fren
enum Mode { Off, Heat }
comp c { in m: Mode pub out on? req r: on? iff m = Mode::Heat::On }
```

Only modules (whose members are their items) and enums (whose members are
their variants) can be followed by `::`.

```fren
enum Mode { Off, Heat }
comp c { in m: Mode pub out on? req r: on? iff m = Mode::Heat }
```
"# },
  { code := "F0205", explanation := r#"A variant name that two enums opened with `*` both have.

Erroneous code example:

```fren
enum E { A, B }
enum F { A, C }
use E::*
use F::*
comp c { in e: E pub out y? req r: y? iff e = A }
```

`use E::*` brings `E`'s variants into scope. When two opened enums have a
variant of the same name, that name is ambiguous. Qualify it with its
enum's name.

```fren
enum E { A, B }
enum F { A, C }
use E::*
use F::*
comp c { in e: E pub out y? req r: y? iff e = E::A }
```
"# },
  { code := "F0206", explanation := r#"A name is defined twice in the same module.

Erroneous code example:

```fren
enum E { A }
enum E { B }
```

Each module has one namespace for its modules, enums and components. Rename
one of them, or move it to another module.

```fren
enum E { A }
enum F { B }
```
"# },
  { code := "F0207", explanation := r#"A name is imported twice, or imported and also defined, in the same module.

Erroneous code example:

```fren
mod a
pub enum Shown { S }

mod b
use a::Shown
use a::Shown
```

A `use` brings a name into the module's namespace, which holds each name
once. Remove the duplicate `use`, or rename the item that clashes with it.

```fren
mod a
pub enum Shown { S }

mod b
use a::Shown
```
"# },
  { code := "F0208", explanation := r#"A `mod` path goes through an item that is not a module.

Erroneous code example:

```fren
enum E { A }
mod E::inner
```

`mod a::b` declares the module `b` inside the module `a`. Here `E` is an
enum, so it cannot contain a module.

```fren
enum E { A }
mod outer::inner
```
"# },
  { code := "F0209", explanation := r#"`use ...::*` names something other than an enum.

Erroneous code example:

```fren
mod m
pub comp c {}

mod n
use m::*
```

`use E::*` opens the enum `E`, bringing its variants into scope. Modules
cannot be opened: import their items one by one.

```fren
mod m
pub comp c {}

mod n
use m::c
```
"# },
  { code := "F0210", explanation := r#"A name refers to the wrong kind of thing.

Erroneous code example:

```fren
enum E { A }
comp c { in e: E pub out y? req r: y? iff e = E }
```

The message says what was expected (a value, a type or a component) and what
the name actually is. Here, `E` is an enum, but a value was expected: one of
its variants.

```fren
enum E { A }
comp c { in e: E pub out y? req r: y? iff e = E::A }
```
"# },
  { code := "F0211", explanation := r#"A name that ends in `?` but is not a variable.

Erroneous code example:

```fren
enum Ready? { Yes, No }
```

A trailing `?` marks a `Bool` variable, so that conditions read as questions.
Modules, enums, variants, components, instances and constraints cannot end in
`?`.

```fren
enum Ready { Yes, No }
```
"# },
  { code := "F0212", explanation := r#"A built-in type is redefined.

Erroneous code example:

```fren
enum Int { Small, Big }
```

`Bool` and `Int` are built in. Name the enum something else.

```fren
enum Size { Small, Big }
```
"# },
  { code := "F0213", explanation := r#"A name is defined twice in the same component, enum, record, pattern or global expectation.

Erroneous code example:

```fren
comp c { in x: Int pub out x: Int }
```

A component's variables, instances and constraints share one namespace, an
enum's variants must be distinct, and so must the names a global expectation
binds. Rename one of them.

```fren
comp c { in x: Int pub out y: Int req r: y = x }
```
"# },
  { code := "F0214", explanation := r#"A `set_option fren.evidence` value that does not exist.

Erroneous code example:

```fren
set_option fren.evidence "testing" in
comp c { in x? pub det out y? req r: y? iff x? }
```

The evidence of a check is `"tested"`, to have it tested instead of asked of
the solver, or `"solver"`, the default (see `Reqs/Check`, "Checking by
testing").

```fren
set_option fren.evidence "tested" in
comp c { in x? pub det out y? req r: y? iff x? }
```
"# },
  { code := "F0215", explanation := r#"A `set_option fren.evidence` before something that has no checks to test.

Erroneous code example:

```fren
comp c {
  in x?
  pub out y?
  set_option fren.evidence "tested" in
  req r: y? iff x?
}
```

A requirement is not itself checked: the checks of a component are about
its expectations, instances, `det out`s and the component as a whole, so
the setting goes before one of those, or before the component.

```fren
set_option fren.evidence "tested" in
comp c {
  in x?
  pub out y?
  req r: y? iff x?
}
```
"# },
  { code := "F0216", explanation := r#"A `set_option` before a member, of an option other than `fren.evidence`.

Erroneous code example:

```fren
comp c {
  in x?
  pub out y?
  set_option fren.lint.nonminimal_bool "allow" in
  req r: y? iff x?
}
```

Within a component, only the evidence of a member's checks can be set
(see `Reqs/Check`, "Checking by testing"). Set other options, such as a
lint's level, before the component:

```fren
set_option fren.lint.nonminimal_bool "allow" in
comp c {
  in x?
  pub out y?
  req r: y? iff x?
}
```
"# },
  { code := "F0217", explanation := r#"A declaration hides a name in scope, but is not written with `!`.

Erroneous code example:

```fren
pub const RATE: Int := 2
set_option fren.lint.non_snake_case "allow" in
comp c { in RATE: Int pub out y: Int req r: y = RATE }
```

Within `c`, `RATE` is the input, not the constant: a component's variables
hide the items of its module, a function's parameters hide those of its
module, and a `match` arm's binders hide variables, parameters, other
binders and items. Shadowing is allowed, but must be explicit, so that a
reader knows which `RATE` a use means: the declaration that hides the name
is written with `!` directly after it, as `RATE!`, or `ready?!` for a
`Bool`. Its uses are written without `!`. This error replaces the lint
`shadowed_constants`, which was `F0713`.

Write the `!`:

```fren
pub const RATE: Int := 2
set_option fren.lint.non_snake_case "allow" in
comp c { in RATE!: Int pub out y: Int req r: y = RATE }
```

Or rename the variable:

```fren
pub const RATE: Int := 2
comp c { in rate: Int pub out y: Int req r: y = rate * RATE }
```
"# },
  { code := "F0218", explanation := r#"A declaration is written with `!`, but hides nothing.

Erroneous code example:

```fren
comp c { in x!: Int pub out y: Int req r: y = x }
```

`!` after a declared name says that it shadows a name in scope (see
`F0217`). No `x` is in scope where this `x` is declared, so there is
nothing to shadow; and items, constraints, fields and variants never
shadow. Remove the `!`:

```fren
comp c { in x: Int pub out y: Int req r: y = x }
```
"# },
  { code := "F0219", explanation := r#"A declaration's name, with its `!`, is one of Lean's tokens.

Erroneous code example:

```fren
pub enum Shape { Circle(Int), Square }
comp c { in s: Shape pub out p? req r: p? iff match s { Shape::Circle(s!) => s > 0, _ => false } }
```

Fren is lexed as Lean is, and Lean reads `s!` as a token of its own, not
as the name `s` followed by the `!` of shadowing (see `F0217`). It
reads `assert!`, `debug_assert!`, `f!`, `m!`, `panic!`, `println!`,
`reportDbgIssue!`, `reportEMatchIssue!`, `reportIssue!`, `unreachable!`
and `using!` alike. None of these names can be declared with
`!`, so that a spec means the same in Lean and to the `fren` command.
Rename the declaration:

```fren
pub enum Shape { Circle(Int), Square }
comp c { in s: Shape pub out p? req r: p? iff match s { Shape::Circle(r) => r > 0, _ => false } }
```
"# },
  { code := "F0301", explanation := r#"A variable has no type.

Erroneous code example:

```fren
comp c { in count }
```

A variable's type follows a colon. Only a `Bool` may omit it, and a `Bool`'s
name ends in `?`.

```fren
comp c { in count: Int }
```
"# },
  { code := "F0302", explanation := r#"A variable's name ends in `?`, but it is not a `Bool`.

Erroneous code example:

```fren
comp c { in n?: Int }
```

A variable's name ends in `?` if and only if it is a `Bool`, so that a reader
can tell conditions from values. Remove the `?`, or make it a `Bool`.

```fren
comp c { in n: Int }
```
"# },
  { code := "F0303", explanation := r#"A `Bool` variable's name does not end in `?`.

Erroneous code example:

```fren
comp c { in flag: Bool }
```

A variable's name ends in `?` if and only if it is a `Bool`. With the `?`,
the type can be left out.

```fren
comp c { in flag? }
```
"# },
  { code := "F0304", explanation := r#"An expression has the wrong type.

Erroneous code example:

```fren
comp c { in x: Int pub out y? req r: y? iff x }
```

Each operator takes operands of particular types: `and`, `or`, `iff`, `not`,
`when` and `unless` take `Bool`s, and arithmetic and `<`, `<=`, `>`, `>=`
take `Int`s. A constraint, and the condition of `if`, is a `Bool`. Compare
an `Int` with a number to make a `Bool`.

```fren
comp c { in x: Int pub out y? req r: y? iff x > 0 }
```
"# },
  { code := "F0305", explanation := r#"`=` or `!=` compares values of different types.

Erroneous code example:

```fren
enum Mode { Off, On }
comp c { in m: Mode pub out y? req r: y? iff m = 1 }
```

Both sides of `=` and `!=` must have the same type. Enums are not numbers:
compare an enum with one of its variants.

```fren
enum Mode { Off, On }
comp c { in m: Mode pub out y? req r: y? iff m = Mode::On }
```
"# },
  { code := "F0306", explanation := r#"The branches of `if` have different types.

Erroneous code example:

```fren
comp c { in b? pub out y: Int req r: y = if b? then 1 else true }
```

`if c then a else b` is `a` or `b`, so both must have the same type.

```fren
comp c { in b? pub out y: Int req r: y = if b? then 1 else 0 }
```
"# },
  { code := "F0307", explanation := r#"Two variables are multiplied.

Erroneous code example:

```fren
comp c { in x: Int pub out y: Int req r: y = x * x }
```

Fren's checks are decided by an SMT solver over linear integer arithmetic,
where nonlinear constraints are undecidable. One side of `*` must mention no
variable: it is built from literals and constants, such as `2`, `2 * 3` or
`(MAX - MIN)`.

```fren
comp c { in x: Int pub out y: Int req r: y = 2 * x }
```
"# },
  { code := "F0308", explanation := r#"A function or variant is applied to the wrong number of arguments, or a pattern has the wrong number of binders.

Erroneous code example:

```fren
type Name
fn arity(Name): Int

comp c { in x: Name pub out y: Int req r: y = arity(x, x) }
```

An application gives one argument for each of the function's parameters.

```fren
type Name
fn arity(Name): Int

comp c { in x: Name pub out y: Int req r: y = arity(x) }
```
"# },
  { code := "F0309", explanation := r#"A constant's value is not known.

Erroneous code example:

```fren
fn rate(Int): Int

const RATE: Int := rate(1)
```

A constant stands for a fixed value, but an uninterpreted function's value
is unknown, even at a fixed argument. A defined function's is known, so a
constant may apply one. Nor can a constant have an abstract type, which has
no literals. Make it an input of the components that use it:

```fren
fn rate(Int): Int

comp c { in r: Int pub out y: Int req r1: y = rate(r) }
```
"# },
  { code := "F0310", explanation := r#"A field or payload has an abstract type, or a set of one.

Erroneous code example:

```fren
type Name

struct User { name: Name, age: Int }
```

The values of a record or an enum are fully described by the spec, but an
abstract type's are not. Describe the value with a function of a type that
stands for the record instead, or make it an input:

```fren
type User

fn age(User): Int
```

`Set(Name)` is as abstract as `Name`, so a field of that type is an error too.
"# },
  { code := "F0311", explanation := r#"A record has a field of its own type.

Erroneous code example:

```fren
struct Chain { head: Int, rest: Chain }
```

A record has one way to build a value, so each value would contain another
without end, and there would be none. A recursive type is an enum with a
variant that does not contain it:

```fren
enum Chain { End, Link(Int, Chain) }
```
"# },
  { code := "F0312", explanation := r#"An enum whose every variant contains the enum itself.

Erroneous code example:

```fren
enum Stream { More(Int, Stream) }
```

Every value is built from finitely many variants, so a recursive enum
needs a variant whose payload does not contain it:

```fren
enum Stream { Done, More(Int, Stream) }
```
"# },
  { code := "F0313", explanation := r#"An output has an unbounded type.

Erroneous code example:

```fren
enum List { Nil, Cons(Int, List) }

comp c { in x: Int pub out l: List req r: l = List::Cons(x, List::Nil) }
```

A recursive enum, or a type containing one, has values of any size. The
realizability check asks whether outputs exist, which the solver cannot
decide in general for such values. Inputs may have unbounded types; an
output can describe the value by bounded parts:

```fren
enum List { Nil, Cons(Int, List) }

comp c { in l: List pub out head: Int req r: head = match l { List::Cons(h, _) => h, List::Nil => 0 } }
```
"# },
  { code := "F0314", explanation := r#"A record literal does not give each field exactly once.

Erroneous code example:

```fren
struct Point { x: Int, y: Int }

const ORIGIN: Point := Point { x := 0 }
```

A record literal gives every field of the record, once each, and nothing
else:

```fren
struct Point { x: Int, y: Int }

const ORIGIN: Point := Point { x := 0, y := 0 }
```
"# },
  { code := "F0315", explanation := r#"A field is read from something that has no field of that name.

Erroneous code example:

```fren
struct Point { x: Int, y: Int }

comp c { in p: Point pub out z: Int req r: z = p.z }
```

Only records have fields, and only those they declare:

```fren
struct Point { x: Int, y: Int }

comp c { in p: Point pub out z: Int req r: z = p.x }
```
"# },
  { code := "F0316", explanation := r#"A `match` on a value that is not of an enum.

Erroneous code example:

```fren
comp c { in x: Int pub out y: Int req r: y = match x { _ => 0 } }
```

`match` reads which variant a value of an enum is. For other types, use
`if`:

```fren
comp c { in x: Int pub out y: Int req r: y = if x > 0 then x else 0 }
```
"# },
  { code := "F0317", explanation := r#"A `match` does not cover every variant.

Erroneous code example:

```fren
enum Shape { Circle(Int), Square(Int), Empty }

comp c { in s: Shape pub out a: Int req r: a = match s { Shape::Circle(r) => 3 * r, Shape::Square(w) => w } }
```

A `match` has a value for every value of its scrutinee: an arm for each
variant, or a last arm `_` for the rest:

```fren
enum Shape { Circle(Int), Square(Int), Empty }

comp c { in s: Shape pub out a: Int req r: a = match s { Shape::Circle(r) => 3 * r, Shape::Square(w) => w, _ => 0 } }
```
"# },
  { code := "F0318", explanation := r#"An arm of a `match` that can never be chosen.

Erroneous code example:

```fren
enum Mode { Off, On }

comp c { in m: Mode pub out y: Int req r: y = match m { _ => 0, Mode::On => 1 } }
```

The first arm whose pattern matches is chosen, so an arm after `_`, an arm
for a variant that an earlier arm covers, and a `_` after arms for every
variant are never chosen. Remove the arm, or reorder the arms:

```fren
enum Mode { Off, On }

comp c { in m: Mode pub out y: Int req r: y = match m { Mode::On => 1, _ => 0 } }
```
"# },
  { code := "F0319", explanation := r#"A pattern that is not a variant of the scrutinee's enum.

Erroneous code example:

```fren
enum Mode { Off, On }
enum Fan { Slow, Fast }

comp c { in m: Mode pub out y: Int req r: y = match m { Fan::Slow => 1, _ => 0 } }
```

Each pattern names a variant of the enum being matched, or is `_`:

```fren
enum Mode { Off, On }
enum Fan { Slow, Fast }

comp c { in m: Mode pub out y: Int req r: y = match m { Mode::On => 1, _ => 0 } }
```
"# },
  { code := "F0320", explanation := r#"The arms of a `match` have different types.

Erroneous code example:

```fren
enum Mode { Off, On }

comp c { in m: Mode pub out y: Int req r: y = match m { Mode::On => 1, Mode::Off => false } }
```

A `match` has the value of one of its arms, so every arm has the same
type:

```fren
enum Mode { Off, On }

comp c { in m: Mode pub out y: Int req r: y = match m { Mode::On => 1, Mode::Off => 0 } }
```
"# },
  { code := "F0321", explanation := r#"A method that a type does not have.

Erroneous code example:

```fren
comp c { in s: String pub out n: Int req r: n = s.length }
```

The methods of `String` are `len`, `starts_with?`, `ends_with?` and
`contains?`. A method that returns a `Bool` ends in `?`:

```fren
comp c { in s: String pub out n: Int req r: n = s.len }
```
"# },
  { code := "F0322", explanation := r#"A method call on a value of a type without methods.

Erroneous code example:

```fren
comp c { in x: Int pub out p? req r: p? iff x.contains?(1) }
```

Only `String`s have methods. Use the operators of the type instead:

```fren
comp c { in x: Int pub out p? req r: p? iff x = 1 }
```
"# },
  { code := "F0323", explanation := r#"The argument of `matches?` is not a string literal.

Erroneous code example:

```fren
comp c { in s: String in p: String pub out m? req r: m? iff s.matches?(p) }
```

A pattern is parsed when the spec is checked, so it is written as a
literal at the call, usually a raw one. Only literals are patterns: a
variable's value would be matched literally, which no reader would expect.

```fren
comp c { in s: String pub out m? req r: m? iff s.matches?(r"[a-z]+") }
```
"# },
  { code := "F0324", explanation := r#"`{}` where nothing gives it a type.

Erroneous code example:

```fren
comp c { pub out n: Int req r: n = {}.card }
```

`{}` has no member to give its set a type, so it takes its type from where
it is written: the other operand of `=`, `!=`, `union`, `inter`, `minus`
or `subset`, the right of `in`, a binding, a field, a definition, an
argument or a constant. Write it where its type is known:

```fren
comp c { in s: Set(Int) pub out e? req r: e? iff s = {} }
```
"# },
  { code := "F0325", explanation := r#"The right of `in` is not a set of the left's type.

Erroneous code example:

```fren
comp c { in x: Int in s: Set(String) pub out p? req r: p? iff x in s }
```

`x in s` is membership: `s` must be a `Set(T)`, where `T` is the type of
`x`:

```fren
comp c { in x: Int in s: Set(Int) pub out p? req r: p? iff x in s }
```
"# },
  { code := "F0326", explanation := r#"The members of a set literal have different types.

Erroneous code example:

```fren
comp c { in s: Set(Int) pub out p? req r: p? iff s = {1, true} }
```

A set's members all have its element type, which the first member gives:

```fren
comp c { in s: Set(Int) pub out p? req r: p? iff s = {1, 2} }
```
"# },
  { code := "F0327", explanation := r#"A record or enum is the element type of a set within one of its own fields or payloads.

Erroneous code example:

```fren
enum Tree { Leaf, Node(Set(Tree)) }
```

A set's members have no order, so a value cannot be built from sets of
values of its own type. Give the variant a payload of the type itself:

```fren
enum Tree { Leaf, Node(Int, Tree, Tree) }
```
"# },
  { code := "F0328", explanation := r#"A relational operator is applied to operands of the wrong types.

Erroneous code example:

```fren
enum U { A, B }

enum R { X, Y }

comp c { in r: Rel(U, R) pub out p? req q: p? iff (U::A, U::B) in r.closure }
```

`r.closure` chains pairs `(a, b)`, `(b, c)`, so it needs a relation of a type
with itself, `Rel(A, A)`. `r join q` composes `r: Rel(A, B)` with
`q: Rel(B, C)`: the second type of `r` must be the first of `q`:

```fren
enum U { A, B }

enum R { X, Y }

comp c { in r: Rel(U, U) pub out p? req q: p? iff (U::A, U::B) in r.closure }
```
"# },
  { code := "F0329", explanation := r#"A pair is written outside a relation literal and the left of `in`.

Erroneous code example:

```fren
comp c { in x: Int pub out p? req q: p? iff (x, 1) = (1, x) }
```

There is no type of pairs. A pair is a member of a relation, written in a
relation literal, `{(a, b)}`, or tested with `(a, b) in r`:

```fren
comp c { in x: Int pub out p? req q: p? iff (x, 1) in {(1, x)} }
```
"# },
  { code := "F0332", explanation := r#"A value that is not a sequence is indexed.

Erroneous code example:

```fren
comp c { in s: Set(Int) pub out x: Int req r: x = s[0] }
```

Only a sequence, `Seq(T)`, has positions. A set has no order, so it has no
first member:

```fren
comp c { in s: Seq(Int) pub out x: Int req r: s.len > 0 and x = s[0] or s.len = 0 }
```
"# },
  { code := "F0333", explanation := r#"An alternative of an or-pattern binds a name.

Erroneous code example:

```fren
enum Shape { Circle(Int), Square(Int), Empty }

comp c { in s: Shape pub out a: Int req r: a = match s { Shape::Circle(n) | Shape::Square(n) => n, _ => 0 } }
```

An or-pattern matches any of its alternatives, so a name bound by one
would have no value when another matches. Ignore the payload with `_`, or
give each variant its own arm:

```fren
enum Shape { Circle(Int), Square(Int), Empty }

comp c { in s: Shape pub out a: Int req r: a = match s { Shape::Circle(n) => n, Shape::Square(n) => n, _ => 0 } }
```
"# },
  { code := "F0330", explanation := r#"A function's parameters are named, but it has no body, or it has a body, but a parameter has no name.

Erroneous code examples:

```fren
fn rate(n: Int): Int
fn double(Int): Int := 1
```

An uninterpreted function's parameters have types but no names, since
nothing mentions them. A defined function's body mentions its parameters,
so each is named, like a component's variable: `x: T`, or `x?` for a
`Bool`.

```fren
fn rate(Int): Int
fn double(n: Int): Int := 2 * n
```
"# },
  { code := "F0331", explanation := r#"A defined function's body applies the function itself, or an uninterpreted function.

Erroneous code examples:

```fren
type Name
fn arity(Name): Int

fn again(n: Int): Int := again(n)
fn rank(n: Name): Int := arity(n) + 1
```

A defined function's values are fully known, from those of its arguments,
so its body applies only defined functions declared before it. It cannot
apply itself, and it cannot apply an uninterpreted function, whose values
are unknown. Make such a value a parameter, and apply the uninterpreted
function where the defined one is applied:

```fren
type Name
fn arity(Name): Int

fn rank(a: Int): Int := a + 1

comp c { in n: Name pub out r: Int req def: r = rank(arity(n)) }
```
"# },
  { code := "F0401", explanation := r#"An assumption mentions a variable that is not an `in`.

Erroneous code example:

```fren
comp c { in x: Int pub out y: Int assume a: y > 0 req r: y = x }
```

Assumptions constrain the environment: the inputs the component may be
given. Outputs, and the variables of instances, belong to the system, which
must satisfy the requirements for every allowed input. To constrain an
output, use `req`.

```fren
comp c { in x: Int pub out y: Int assume a: x > 0 req r: y = x }
```
"# },
  { code := "F0402", explanation := r#"An instance's binding mentions an `out` of the component.

Erroneous code example:

```fren
comp sub { in a: Int pub out b: Int req r: b = a }
comp c { pub out o: Int inst s: sub { a := o } req r: o = 0 }
```

An instance's inputs are given by the component's environment: its own
inputs and the outputs of earlier instances. To relate an instance to an
output, write a `req`.

```fren
comp sub { in a: Int pub out b: Int req r: b = a }
comp c { in i: Int pub out o: Int inst s: sub { a := i } req r: o = s.b }
```
"# },
  { code := "F0403", explanation := r#"A private variable of an instance is mentioned.

Erroneous code example:

```fren
comp sub { in a: Int out hidden: Int req r: hidden = a }
comp c { in i: Int pub out o: Int inst s: sub { a := i } req r: o = s.hidden }
```

From outside a component, only its `in`s and `pub out`s can be mentioned.
Make the output `pub` if the component's users need it.

```fren
comp sub { in a: Int pub out shown: Int req r: shown = a }
comp c { in i: Int pub out o: Int inst s: sub { a := i } req r: o = s.shown }
```
"# },
  { code := "F0404", explanation := r#"A binding mentions an instance that is not declared before it.

Erroneous code example:

```fren
comp sub { in a: Int pub out b: Int req r: b = a }
comp c { in i: Int inst first: sub { a := second.b } inst second: sub { a := i } }
```

A binding may mention only instances declared before its own, so that
instances form no cycles. Reorder the instances.

```fren
comp sub { in a: Int pub out b: Int req r: b = a }
comp c { in i: Int inst second: sub { a := i } inst first: sub { a := second.b } }
```
"# },
  { code := "F0405", explanation := r#"An instance has no visible variable of that name.

Erroneous code example:

```fren
comp sub { in a: Int pub out b: Int req r: b = a }
comp c { in i: Int pub out o: Int inst s: sub { a := i } req r: o = s.c }
```

`w.x` names the variable `x` of the instance `w`, which must be an `in` or a
`pub out` of its component. The message lists them.

```fren
comp sub { in a: Int pub out b: Int req r: b = a }
comp c { in i: Int pub out o: Int inst s: sub { a := i } req r: o = s.b }
```
"# },
  { code := "F0406", explanation := r#"An instance binds the same input twice.

Erroneous code example:

```fren
comp sub { in a: Int }
comp c { inst s: sub { a := 1, a := 2 } }
```

Each input of an instance is bound exactly once. Remove one of the
bindings.

```fren
comp sub { in a: Int }
comp c { inst s: sub { a := 1 } }
```
"# },
  { code := "F0407", explanation := r#"An instance binds an `out` of its component.

Erroneous code example:

```fren
comp sub { in a: Int pub out b: Int req r: b = a }
comp c { inst s: sub { a := 1, b := 2 } }
```

An instance chooses its own outputs, as its component's requirements allow;
only its inputs are bound. To constrain an output, write a `req` about it.

```fren
comp sub { in a: Int pub out b: Int req r: b = a }
comp c { pub out o: Int inst s: sub { a := 1 } req r: o = s.b }
```
"# },
  { code := "F0408", explanation := r#"An instance binds a name that is not an input of its component.

Erroneous code example:

```fren
comp sub { in a: Int }
comp c { inst s: sub { a := 1, z := 2 } }
```

The message lists the component's inputs. Remove the binding, or correct
its name.

```fren
comp sub { in a: Int }
comp c { inst s: sub { a := 1 } }
```
"# },
  { code := "F0409", explanation := r#"An instance does not bind every input of its component.

Erroneous code example:

```fren
comp sub { in a: Int in b? }
comp c { inst s: sub { a := 1 } }
```

An instance binds each input of its component, with `x := e`, or with `x`
alone to bind it to the variable `x` of the same name.

```fren
comp sub { in a: Int in b? }
comp c { in b? inst s: sub { a := 1, b? } }
```
"# },
  { code := "F0410", explanation := r#"A function is applied to an output of the component.

Erroneous code example:

```fren
type Name
fn ok?(Name)

comp c { in x: Name pub out y: Name req r: ok?(y) }
```

The realizability check asks for outputs that meet the requirements. If an
output were a function's argument, that would quantify over the function's
arguments, which the solver cannot decide in general. So a function is
applied only to inputs and to the variables of instances. Apply it to the
inputs that the output depends on, and relate the output to the result:

```fren
type Name
fn ok?(Name)

comp c { in x: Name pub out y: Name pub out good? req r: y = x req g: good? iff ok?(x) }
```
"# },
  { code := "F0411", explanation := r#"Defined outputs whose definitions form a cycle.

Erroneous code example:

```fren
comp c { in x: Int out a: Int := b + x out b: Int := a pub out y: Int req r: y = a }
```

A defined output stands for its definition, so the checks replace it by
its definition. If a definition mentions its own output, directly or
through other definitions, the replacement never ends. Define one of them
from the inputs, or constrain it with a requirement instead:

```fren
comp c { in x: Int out a: Int := b + x out b: Int := x pub out y: Int req r: y = a }
```
"# },
  { code := "F0412", explanation := r#"A refinement whose components do not share the abstract one's interface.

Erroneous code example:

```fren
comp precise { in x: Int pub out y: Int req r: y = x }
comp rough { in x: Int pub out z: Int req r: z >= x }
refine fits: precise refines rough
```

`refine r: c refines a` relates `c` and `a` through `a`'s variables: each
input of `a` must be an input of `c`, and each output of `a` a public
output of `c`, with the same name and type (see `Reqs/Lang/Refinement`).
`precise` has no output `z`. Name the outputs alike:

```fren
comp precise { in x: Int pub out y: Int req r: y = x }
comp rough { in x: Int pub out y: Int req r: y >= x }
refine fits: precise refines rough
```
"# },
  { code := "F0413", explanation := r#"A refinement binds a name that is not a variable of the refined component.

Erroneous code example:

```fren
comp precise { in x: Int pub out y: Int req r: y = x }
comp rough { in x: Int pub out z: Int req r: z >= x }
refine fits: precise refines rough { w := y }
```

A refinement's bindings give variables of the refined component, the one
after `refines`, as expressions over the refining one's (see
`Reqs/Lang/Refinement`). `rough` has no variable `w`. The message lists
its variables; correct the name:

```fren
comp precise { in x: Int pub out y: Int req r: y = x }
comp rough { in x: Int pub out z: Int req r: z >= x }
refine fits: precise refines rough { z := y }
```
"# },
  { code := "F0414", explanation := r#"A refinement binds a variable of the refined component more than once.

Erroneous code example:

```fren
comp precise { in x: Int pub out y: Int req r: y = x }
comp rough { in x: Int pub out z: Int req r: z >= x }
refine fits: precise refines rough { z := y, z := y + 1 }
```

Each variable of the refined component is read as one expression, so a
refinement binds it at most once. Keep one binding:

```fren
comp precise { in x: Int pub out y: Int req r: y = x }
comp rough { in x: Int pub out z: Int req r: z >= x }
refine fits: precise refines rough { z := y }
```
"# },
  { code := "F0415", explanation := r#"A refinement's binding mentions a variable of the refining component that it cannot see.

Erroneous code example:

```fren
comp precise { in x: Int pub out y: Int req r: y = x }
comp rough { in n: Int pub out y: Int req r: y >= n }
refine fits: precise refines rough { n := y }
```

A binding sees the refining component from outside: its inputs and public
outputs, and no private output. A binding of an input of the refined
component sees only inputs, since the environment chooses the inputs
before the component chooses its outputs (see `Reqs/Lang/Refinement`).
Bind the input to an input:

```fren
comp precise { in x: Int pub out y: Int req r: y = x }
comp rough { in n: Int pub out y: Int req r: y >= n }
refine fits: precise refines rough { n := x }
```
"# },
  { code := "F0501", explanation := r#"A `tested` claim names a file that cannot be read.

Erroneous code example:

```fren
comp c {}
tested c: "tests/no_such_file.rs"
```

The files of a `tested` claim are read relative to the directory Fren runs
in, which is usually the project's root. Correct the path.
"# },
  { code := "F0502", explanation := r#"A `tested` claim names a file that does not say that it covers the component.

Erroneous code example:

```fren
comp c {}
tested c: "README.md"
```

A test names the components it covers with a comment containing
`fren-covers:` and their paths, such as `// fren-covers: climate::thermostat`.
The claim and the marker together make sure that neither goes stale. Add the
marker to the test.
"# },
  { code := "F0503", explanation := r#"A `trusted` claim has an empty justification.

Erroneous code example:

```fren
comp c {}
trusted c: ""
```

A `trusted` claim says why a component holds without a proof or a test, so
that a reader can judge it. Write the reason.

```fren
comp c {}
trusted c: "checked by hand against the datasheet"
```
"# },
  { code := "F0504", args := none, explanation := r#"A `fren-covers:` marker names something that is not a component.

Erroneous code example, in a test scanned by `fren trace --tests`:

```text
// fren-covers: climate::thermostatt
```

Markers name components by their full path, such as `climate::thermostat`.
Correct the name, or remove the marker.
"# },
  { code := "F0505", args := none, explanation := r#"A `fren-covers:` marker names a component, but no `tested` claim for it names the file.

Erroneous code example, in `tests/heat.rs`, scanned by `fren trace --tests`:

```text
// fren-covers: climate::thermostat
```

A marker says that a test covers a component, but the evidence is the
`tested` claim. Add one:

```fren
mod climate
pub comp thermostat {}
tested thermostat: "tests/heat.rs"
```

(The claim's file must exist and contain the marker.)
"# },
  { code := "F0506", args := some ["trace", "--require", "tested"], explanation := r#"A component's evidence is weaker than required.

Erroneous code example, with `fren trace --require tested`:

```fren
comp c { in x? pub out y? req r: y? iff x? }
```

`fren trace --require LEVEL`, or the Lean option `fren.requireEvidence`,
requires every component to have evidence at least `LEVEL`. From weakest to
strongest, the levels are `missing`, `trusted`, `tested`, `solver` and
`proved`: a `trusted` claim, a `tested` claim, an `impl` proved by the
solver, and an `impl` proved by Lean. A component without outputs has the
evidence of its weakest instance.
"# },
  { code := "F0507", args := none, explanation := r#"An evidence level that does not exist.

Erroneous code example:

```text
fren trace --require tests spec.fren
```

The levels are `trusted`, `tested`, `solver` and `proved`, weakest first.

```text
fren trace --require tested spec.fren
```
"# },
  { code := "F0601", explanation := r#"A component is not realizable: for some input, no outputs satisfy its requirements.

Erroneous code example:

```fren
comp c {
  in x: Int
  pub out y: Int
  req big: y > x
  req small: y < 0
}
```

A component must be implementable: for every input that its assumptions
allow, some outputs satisfy all of its requirements. The message gives an
input for which none do, and the requirements that conflict on it. Here,
when `x` is `0`, no `y` is both above `0` and below `0`.

Weaken one of the requirements, or, if such inputs cannot happen, add an
assumption that rules them out:

```fren
comp c {
  in x: Int
  pub out y: Int
  assume negative: x < -1
  req big: y > x
  req small: y < 0
}
```
"# },
  { code := "F0602", explanation := r#"A component's assumptions contradict each other.

Erroneous code example:

```fren
comp c {
  in x: Int
  pub out y?
  assume big: x > 10
  assume small: x < 5
  req r: y? iff x > 7
}
```

If no input satisfies the assumptions, every requirement holds vacuously,
and the component says nothing. The message names a smallest set of
assumptions that contradict each other. Weaken or remove one of them.

```fren
comp c {
  in x: Int
  pub out y?
  assume big: x > 10
  req r: y? iff x > 7
}
```
"# },
  { code := "F0603", explanation := r#"An expectation does not follow from the requirements.

Erroneous code example:

```fren
comp c {
  in x: Int
  pub out y: Int
  req r: y >= x
  expect positive: y > 0
}
```

An `expect` states a consequence of the assumptions, instances and
requirements, and is checked rather than required. The counterexample shows
inputs and public outputs that satisfy everything else but not the
expectation. Here, `x = 0, y = 0`.

Strengthen the requirements so that it follows, or correct the expectation:

```fren
comp c {
  in x: Int
  pub out y: Int
  assume nonneg: x >= 0
  req r: y > x
  expect positive: y > 0
}
```
"# },
  { code := "F0604", explanation := r#"An instance may be given inputs that its component's assumptions rule out.

Erroneous code example:

```fren
comp sub { in n: Int pub out m: Int assume nonneg: n >= 0 req r: m = n }
comp c { in i: Int pub out o: Int inst s: sub { n := i } req r: o = s.m }
```

A component's assumptions are obligations for whoever instantiates it: they
must follow from the instantiating component's assumptions, the instance's
bindings and earlier instances. The counterexample shows inputs for which
they may not.

```fren
comp sub { in n: Int pub out m: Int assume nonneg: n >= 0 req r: m = n }
comp c { in i: Int pub out o: Int assume nonneg: i >= 0 inst s: sub { n := i } req r: o = s.m }
```
"# },
  { code := "F0605", explanation := r#"The condition of a `when` or `unless` can never hold.

Erroneous code example:

```fren
comp c {
  in x: Int
  pub out y: Int
  assume pos: x > 0
  req r: y = x
  req never: when x < 0, y = 0
}
```

A constraint whose condition is always false holds vacuously, and says
nothing: usually a mistake in the condition or in the constraints that rule
it out, which the message names.

```fren
comp c {
  in x: Int
  pub out y: Int
  assume pos: x > 0
  req r: when x > 5, y = x
  req small: when x <= 5, y = 0
}
```
"# },
  { code := "F0606", explanation := r#"A constraint follows from the others (a warning).

Erroneous code example:

```fren
comp c {
  in x: Int
  pub out y: Int
  req y_def: y = x + 1
  req bigger: y > x
}
```

A requirement that follows from the assumptions, instances and other
requirements adds nothing, and an assumption that follows from the other
assumptions likewise. If it is meant as a consequence, make it an `expect`,
so that it is checked rather than assumed:

```fren
comp c {
  in x: Int
  pub out y: Int
  req y_def: y = x + 1
  expect bigger: y > x
}
```
"# },
  { code := "F0607", explanation := r#"A `det out` is not determined by the inputs.

Erroneous code example:

```fren
comp c {
  in x: Int
  pub det out y: Int
  req above: y >= x
  req below: y <= x + 1
}
```

A `det out` must have exactly one value for each input that the
assumptions allow. The message gives an input and two values the output
could take. Add requirements that pin it down, or remove `det`.

```fren
comp c {
  in x: Int
  pub det out y: Int
  req exact: y = x + 1
}
```
"# },
  { code := "F0608", args := none, explanation := r#"A check could not be decided (a warning).

The solver neither proved nor refuted the check's query within the time
limit, or gave up, so the check neither passed nor failed. The message says
which check, and why the solver stopped.

Raise the time limit with `fren check --timeout SECONDS` (the default is 10),
or simplify the constraints involved: large constants and many `if`s make
queries harder.
"# },
  { code := "F0609", args := some ["quickcheck"], explanation := r#"Testing found no outputs for an input (a warning).

Erroneous code example:

```fren
comp c {
  in x: Int
  pub out y: Int
  req above: y > x
  req below: y < x
}
```

`fren quickcheck` chose an input that the assumptions allow, and behaviours
of the instances, but its search found no outputs that satisfy the
requirements. The search tries only some values, so outputs may still
exist: run `fren check`, whose realizability check decides it. Here no `y`
is both above and below `x`, so `fren check` reports `F0601`. Weaken one
of the requirements:

```fren
comp c {
  in x: Int
  pub out y: Int
  req above: y > x
}
```
"# },
  { code := "F0611", explanation := r#"An index may be out of range where it is evaluated.

Erroneous code example:

```fren
comp first {
    in q: Seq(Int)
    pub out x: Int

    req r: x = q[0]
}
```

Out of range, `q[i]` is an unknown value, so the checks hold whatever it
is, but the constraint then says nothing useful: here, `x` is unconstrained
when `q` is empty. Fren asks whether `0 <= i < q.len` follows from the
conditions under which the index is evaluated, its guard, read from left
to right through `when`, `if`, `and`, `or` and `match`. Guard the index:

```fren
comp first {
    in q: Seq(Int)
    pub out x: Int

    req r: when q != [], x = q[0]
}
```
"# },
  { code := "F0610", args := some ["quickcheck"], explanation := r#"Testing found no admissible behaviour (a warning).

Erroneous code example:

```fren
comp c {
  in x: Int
  pub out pos?
  assume never: x > 0 and x < 0
  req r: pos? iff x > 0
}
```

None of `fren quickcheck`'s tests found an input that the assumptions
allow, with behaviours of the instances and outputs that meet the
component, so none of the component's checks were tested. Either the
assumptions or requirements cannot hold, as here, where `fren check`
reports `F0602`, or the search missed the values that satisfy them: then
raise `--tests`, or rely on `fren check`.

```fren
comp c {
  in x: Int
  pub out pos?
  assume small: x > -10 and x < 10
  req r: pos? iff x > 0
}
```
"# },
  { code := "F0612", args := some ["quickcheck"], explanation := r#"Testing never reached a check: its trigger held in no test (a warning).

Erroneous code example:

```fren
comp c {
  in x: Int
  pub out big?
  req r: big? iff x > 1000
  expect e: when 7 * x = 123459, big?
}
```

`fren quickcheck` found behaviours of the component, but in none of them
did the trigger of `e`, `7 * x = 123459`, hold: only `x = 17637` satisfies
it, and the search does not try that value. Where a trigger is false, the
constraint holds by its trigger alone, so those tests say nothing about
it, and its result is inconclusive. Testing searches for behaviours in
which the trigger holds, but tries only some values, and can miss them.
An instance assumption with a trigger gets no such search, since its
instance's inputs come from the bindings, so it reports this more often.
Raise `--tests`, rely on `fren check`, or widen the trigger:

```fren
comp c {
  in x: Int
  pub out big?
  req r: big? iff x > 1000
  expect e: when x > 2000, big?
}
```
"# },
  { code := "F0613", args := some ["mutate"], explanation := r#"No check rejects a mutant (a warning).

Erroneous code example:

```fren
comp c {
  in x: Int
  pub out pos?
  req r: pos? iff x > 0
  expect e: when x > 1, pos?
}
```

`fren mutate` changed the spec a little, here `x > 0` to `x >= 0`, and
every check that passes on the spec still passes. So nothing that the
spec expects depends on the change: either the spec says less than
intended, or an expectation is missing. Here the expectation says nothing
about `x = 0` or `x = 1`, where `x > 0` and its mutants differ. Add
expectations that pin the boundary down:

```fren
comp c {
  in x: Int
  pub out pos?
  req r: pos? iff x > 0
  expect e: when x > 1, pos?
  expect zero: when x = 0, not pos?
  expect one: when x = 1, pos?
}
```

A mutant that means what the spec means, such as `x >= 1`, cannot be
rejected. When the solver shows that a mutant is equivalent, it is not
reported; when it cannot tell, the warning says so.
"# },
  { code := "F0614", args := some ["mutate", "--by", "both"], explanation := r#"Testing does not reject a mutant that the checks reject (a warning).

Erroneous code example:

```fren
comp c {
  in xs: Seq(Int)
  pub out big?
  req r: big? iff xs.len > 4
  expect e: when xs.len = 5, big?
}
```

With `--by both`, `fren mutate` checks each mutant with the solver and by
testing, as `fren quickcheck` does. Here the checks reject the mutant
`xs.len > 5`: the solver finds a sequence of five elements, which breaks
the expectation. But none of testing's random behaviours has such a
sequence, so testing passes the mutant. The spec itself may be fine: the
warning is about testing's search, which a component whose evidence is
testing (`fren.evidence "tested"`) relies on. Raising `--tests` can help
where the search reaches such behaviours rarely; otherwise rely on `fren
check` for the component.
"# },
  { code := "F0701", explanation := r#"An import that nothing uses (the lint `unused_imports`, a warning by default).

Erroneous code example:

```fren
mod climate
pub enum Mode { Off, Heat }
use self::Mode::Heat
comp c { in m: Mode pub out off? req r: off? iff m = Mode::Off }
```

No path in the file resolves through the `use`, so it can be removed, as
`fren fix` does. Only paths in the same file count. Imports of the same enumeration's
variants by `*` count once, so a repeated `use E::*` is unused too.

```fren
mod climate
pub enum Mode { Off, Heat }
use self::Mode::Off
comp c { in m: Mode pub out off? req r: off? iff m = Off }
```

To keep the `use`, allow the lint for it:
`set_option fren.lint.unused_imports "allow" in use ...`.
"# },
  { code := "F0702", explanation := r#"A `use ...::*` (the lint `glob_imports`, a warning by default).

Erroneous code example:

```fren
pub enum Mode { Off, Heat }
use Mode::*
comp c { in m: Mode pub out off? req r: off? iff m = Off }
```

`use E::*` brings every variant of `E` into scope, including variants added
later, so a reader cannot tell where a name comes from, and a new variant
can make a name in another module ambiguous. Import the variants by name,
as `fren fix` does, or write them qualified:

```fren
pub enum Mode { Off, Heat }
use Mode::{Off}
comp c { in m: Mode pub out off? req r: off? iff m = Off }
```

```fren
pub enum Mode { Off, Heat }
comp c { in m: Mode pub out off? req r: off? iff m = Mode::Off }
```
"# },
  { code := "F0703", explanation := r#"A name that should be in `snake_case` (the lint `non_snake_case`, a warning by default).

Erroneous code example:

```fren
comp TempSensor { in t: Int pub out hot? req r: hot? iff t > 30 }
```

Modules, components, variables, instances, constraints and global
expectations are named in `snake_case`: no uppercase letters. A
variable's final `?` does not count.

```fren
comp temp_sensor { in t: Int pub out hot? req r: hot? iff t > 30 }
```
"# },
  { code := "F0704", explanation := r#"A name that should be in `CamelCase` (the lint `non_camel_case_types`, a warning by default).

Erroneous code example:

```fren
enum fan_speed { Low, High }
```

Enumerations and variants are named in `CamelCase`: starting with an
uppercase letter, with no `_`.

```fren
enum FanSpeed { Low, High }
```
"# },
  { code := "F0705", explanation := r#"A constant's name that should be in `UPPER_CASE` (the lint `non_upper_case_constants`, a warning by default).

Erroneous code example:

```fren
const max_temp: Int := 100
```

A constant's name starts with an uppercase letter and has no lowercase
letters, so that constants stand out from variables.

```fren
const MAX_TEMP: Int := 100
```
"# },
  { code := "F0706", explanation := r#"A lint was expected, but never fired (the lint `unfulfilled_lint_expectations`, a warning by default).

Erroneous code example:

```fren
set_option fren.lint.glob_imports "expect"
comp c { in x: Int pub out y: Int req r: y = x }
```

`set_option fren.lint.LINT "expect"` says that the lint fires where the
setting is in effect, and silences it there. Here, nothing after the
setting is a glob import. Remove the setting, as `fren fix` does, or move
it to where the lint fires:

```fren
comp c { in x: Int pub out y: Int req r: y = x }
```
"# },
  { code := "F0707", explanation := r#"A `set_option` names a lint that does not exist.

Erroneous code example:

```fren
set_option fren.lint.unused_import "allow"
```

The lints include `dead_code`, `glob_imports`, `non_camel_case_types`,
`non_snake_case`, `non_upper_case_constants`, `nonminimal_bool`,
`unfulfilled_lint_expectations`, `unused_imports` and `unused_variables`;
the error lists them all.

```fren
set_option fren.lint.unused_imports "allow"
```
"# },
  { code := "F0708", explanation := r#"A lint level that does not exist.

Erroneous code example:

```fren
set_option fren.lint.unused_imports "off"
```

A lint's level is `"allow"`, `"expect"`, `"warn"`, `"deny"` or `"forbid"`.

```fren
set_option fren.lint.unused_imports "allow"
```
"# },
  { code := "F0709", explanation := r#"A `set_option` changes the level of a forbidden lint.

Erroneous code example:

```fren
set_option fren.lint.glob_imports "forbid"
set_option fren.lint.glob_imports "allow"
```

Once a lint is `forbid`, by a `set_option` or on the command line with
`-F`, its level cannot be changed for the rest of the file, so that a
project can rule a lint out everywhere. Remove the later setting:

```fren
set_option fren.lint.glob_imports "forbid"
```
"# },
  { code := "F0710", explanation := r#"A variable or binder that nothing mentions (the lint `unused_variables`, a warning by default).

Erroneous code example:

```fren
comp c { in x: Int in spare: Int pub out y: Int req r: y = x }
```

No constraint of `c` mentions `spare`, so it does not affect `c`. An
output that nothing mentions can take any value. A binder of a global
expectation that its body never mentions is reported too. Remove the
variable, or mention it:

```fren
comp c { in x: Int pub out y: Int req r: y = x }
```
"# },
  { code := "F0711", explanation := r#"A private enumeration or constant that nothing in its file uses (the lint `dead_code`, a warning by default).

Erroneous code example:

```fren
const LIMIT: Int := 10
comp c { in x: Int pub out y: Int req r: y = x }
```

No path in the file resolves to `LIMIT`, and it is private, so no other
module can use it. Only uses in the same file count, and uses in Lean
code do not. Remove it, use it, or make it `pub`:

```fren
const LIMIT: Int := 10
comp c { in x: Int pub out y: Int req r: y = x + LIMIT }
```

Components and global expectations are never dead: each is a requirement
in its own right.
"# },
  { code := "F0712", explanation := r#"A `Bool` expression with a simpler form (the lint `nonminimal_bool`, a warning by default).

Erroneous code example:

```fren
comp c { in a? pub out b? req r: b? iff a? = true }
```

`a? = true` means `a?`. Likewise, `a? = false` means `not a?`, `not not
a?` means `a?`, `not (x < y)` means `x >= y`, and `if c? then true else
false` means `c?`. Write the simpler form, as `fren fix` does:

```fren
comp c { in a? pub out b? req r: b? iff a? }
```
"# },
  { code := "F0714", explanation := r#"A construct outside the decidable core (the lint `undecidable`, an error by default).

Erroneous code example:

```fren
comp c { in a: String in b: String pub out p? req r: p? iff a.starts_with?(b) }
```

Unless a spec opts out, every check is decidable: each query is in a
fragment of the solver's theories that has a decision procedure. For
strings, that is regular constraints with length. A method's argument is a
constant, strings are compared with constants or as whole variables, `++`
is the receiver of a method or compared with a constant, and no string
operation but `=` and `!=` mentions an output of an infinite type. A
construct outside it may make the solver give up. Stay in the core:

```fren
comp c { in a: String pub out p? req r: p? iff a.starts_with?("x") }
```

or opt out explicitly, accepting that a check may be inconclusive:

```fren
set_option fren.lint.undecidable "allow" in
comp c { in a: String in b: String pub out p? req r: p? iff a.starts_with?(b) }
```
"# },
{ code := "F0715", explanation := r#"A string's or sequence's length is compared with 0 (a warning, `length_zero`).

Example:

```fren
comp c { in s: String pub out p? req r: p? iff s.len = 0 }
```

That a string or sequence is empty says it more plainly: `s = ""`, or
`q = []`, and `s != ""` for `s.len > 0`. `fren fix` can fix this:

```fren
comp c { in s: String pub out p? req r: p? iff s = "" }
```
"# },
  { code := "F0716", explanation := r#"A set's or relation's `card` is compared with 0 (a warning, `card_zero`).

Example:

```fren
comp c { in s: Set(Int) pub out p? req r: p? iff s.card > 0 }
```

That a set is empty says it more plainly: `s = {}`, or `s != {}` for
`s.card > 0`. `fren fix` can fix this:

```fren
comp c { in s: Set(Int) pub out p? req r: p? iff s != {} }
```
"# },
  { code := "F0717", explanation := r#"Membership in a set of one member (a warning, `singleton_membership`).

Example:

```fren
comp c { in x: Int pub out p? req r: p? iff x in {1} }
```

`x in {a}` is `x = a`. `fren fix` can fix this:

```fren
comp c { in x: Int pub out p? req r: p? iff x = 1 }
```
"# },
  { code := "F0718", explanation := r#"A chain of `or` that equates one expression with three or more others (`membership_chain`, allowed by default).

Example:

```fren
set_option fren.lint.membership_chain "warn"

comp c { in x: Int pub out p? req r: p? iff (x = 1 or x = 2 or x = 3) }
```

The chain is a membership in a set literal. `fren fix` can fix this:

```fren
comp c { in x: Int pub out p? req r: p? iff x in {1, 2, 3} }
```
"# },
  { code := "F0719", explanation := r#"A defined output whose definition mentions no variable (a warning, `constant_output`).

Example:

```fren
comp c { in x: Int pub out limit: Int := 10 req r: x < limit }
```

The output is the same in every behaviour, so it is a constant, which every
component can share:

```fren
const LIMIT: Int := 10

comp c { in x: Int pub out p? req r: p? iff x < LIMIT }
```
"# },
  { code := "F0720", explanation := r#"An output that one requirement equates with other variables (`definable_output`, allowed by default).

Example:

```fren
set_option fren.lint.definable_output "warn"

comp c { in x: Int pub out y: Int req r: y = x + 1 }
```

The requirement could be the output's definition, which realizability
then never searches for:

```fren
comp c { in x: Int pub out y: Int := x + 1 }
```
"# },
  { code := "F0721", explanation := r#"An index on the left of an `and` whose right operand bounds the sequence (a warning, `index_after_use`).

Example:

```fren
comp c { in q: Seq(Int) pub out p? req r: p? iff (q[0] = 1 and q.len > 0) }
```

In `a and b`, `b` is guarded by `a`, so the index is evaluated whether or
not the bound holds, and the definedness check fails. Swapping the operands
does not change the meaning. `fren fix` can fix this:

```fren
comp c { in q: Seq(Int) pub out p? req r: p? iff (q.len > 0 and q[0] = 1) }
```
"# }
]

/-- The explanation of `code`. Codes are written `F0101`; lower case is
accepted, as are `0101` and `101`. -/
def explain? (code : String) : Option ErrorCode :=
  let digits := (code.toUpper.dropWhile (· == 'F')).toString
  let norm := "F" ++ String.ofList (List.replicate (4 - min 4 digits.length) '0') ++ digits
  errorCodes.find? (·.code == norm)

end Fren.Core
