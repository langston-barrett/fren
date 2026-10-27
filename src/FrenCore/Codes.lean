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
`F05xx` traceability, `F06xx` the results of checks, `F07xx` and `F08xx` lints and
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
comp c { in x: Int ensure r: x > 0 $ }
```

Fren is lexed as Lean is, but uses only these symbols:

```text
::  ::*  ::{  :  :=  ,  (  )  {  }  =  !=  <  <=  >  >=  +  -  *
```

Comments start with `--`, not `#` or `//`. Remove the character, or replace
it with the Fren syntax for what you meant:

```fren
comp c { in x: Int pub out y? ensure r: y? iff x > 0 }
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
comp c { in x: Int pub out y? ensure r: y? iff x == 1 }
```

Fren's operators are words where other languages use symbols:

- `=` for equality, not `==`
- `and`, `or` and `not`, not `&&`, `||` and `!`
- `when a, b` for implication, not `=>`

`!=` is inequality, as in other languages. There is no division.

```fren
comp c { in x: Int pub out y? ensure r: y? iff x = 1 }
```
"# },
  { code := "F0106", explanation := r#"The condition of `when` or `unless` is not followed by a comma.

Erroneous code example:

```fren
comp c { in x: Int pub out y: Int ensure r: when x > 1 y = 3 }
```

`when c, e` says that `e` holds whenever `c` does, and `unless c, e` that
`e` holds whenever `c` does not. The comma ends the condition.

```fren
comp c { in x: Int pub out y: Int ensure r: when x > 1, y = 3 }
```
"# },
  { code := "F0107", explanation := r#"A chain of `iff`s.

Erroneous code example:

```fren
comp c { in a? in b? pub out d? ensure r: d? iff a? iff b? }
```

`iff` is not associative, so `a iff b iff c` has no single obvious meaning.
Add parentheses to say which you mean.

```fren
comp c { in a? in b? pub out d? ensure r: d? iff (a? iff b?) }
```
"# },
  { code := "F0108", explanation := r#"A chained comparison with an operator that does not chain.

Erroneous code example:

```fren
comp c { in a? in b? pub out ok? ensure r: ok? iff a? = b? = true }
```

Only orderings chain: `0 <= x < 10` means `0 <= x and x < 10`. `=`,
`!=`, `in` and `subset` do not, since a chain of them has no single
obvious meaning: `a? = b? = true` could be `a? = b? and b? = true`, or
`(a? = b?) = true`, which differ. Split the chain with `and`, or put a
comparison in parentheses to compare its result, as in `(x < y) = p?`.

```fren
comp c { in a? in b? pub out ok? ensure r: ok? iff a? = b? and b? = true }
```

```fren
comp c { in x: Int in y: Int in p? pub out ok? ensure r: ok? iff (x < y) = p? }
```
"# },
  { code := "F0109", explanation := r#"`when`, `unless` or `let` is used as an operand without parentheses.

Erroneous code example:

```fren
comp c { in x: Int pub out y? ensure r: y? iff x > 0 and when x > 1, x > 2 }
```

`when`, `unless` and `let` have the lowest precedence, and their body
extends as far right as possible. Inside another expression, or as the
value of an instance's binding or of a definition (where it would swallow
the bindings or definitions after it), wrap them in parentheses.

```fren
comp c { in x: Int pub out y? ensure r: y? iff (x > 0 and (when x > 1, x > 2)) }
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
comp c { in e: E pub out y? ensure r: y? iff e = E.A }
```

`a.b` means the variable `b` of the instance `a`, or the field or method
`b` of the value `a`, a variable or a constant. Paths, such as an item of a
module or a variant of an enum, are separated by `::`.

```fren
enum E { A, B }
comp c { in e: E pub out y? ensure r: y? iff e = E::A }
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
comp c { in x: Int pub out y? ensure r: y? iff x <= 10 }
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
comp c { in x: Int pub det out y: Int ensure r: y = x }
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
comp c { in x: Int out next: Int := x + 1 pub out y: Int ensure r: y = next }
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
comp c { in s: String pub out p? ensure r: p? iff s.matches?(r"\d+") }
```

Patterns are a subset of POSIX extended regular expressions: characters,
`.`, classes such as `[a-z_]` and `[^0-9]`, `|`, `*`, `+`, `?`, `{m}`,
`{m,n}` and parentheses. `\` escapes one of `\ . [ ] ( ) * + ? { } | ^ -`.
There are no anchors, since the whole string must match, and no classes
such as `\d`:

```fren
comp c { in s: String pub out p? ensure r: p? iff s.matches?(r"[0-9]+") }
```
"# },
  { code := "F0118", explanation := r#"A reversed range in a pattern's class.

Erroneous code example:

```fren
comp c { in s: String pub out p? ensure r: p? iff s.matches?(r"[z-a]+") }
```

A range is written from the lower character to the higher, by code point,
so `[z-a]` would match nothing:

```fren
comp c { in s: String pub out p? ensure r: p? iff s.matches?(r"[a-z]+") }
```
"# },
  { code := "F0119", explanation := r#"A lexeme that Lean reads as one identifier, but that is not one of Fren's.

Erroneous code example:

```fren
comp c { in y: Int pub out z? ensure r: z? iff y!!=1 }
```

Fren's identifiers are ASCII letters, digits, `_` and `'`, with `.` between
components, an optional `?` at the end, and then an optional `!`, which
marks a declaration that shadows. Lean's are a superset: they may have `?`
and `!` anywhere after the first character, letters other than ASCII, such
as `α`, and quoted components, such as `«a b»`. So that a spec reads alike
in Lean and in the `fren` command, both report what Lean would read
differently. Here Lean reads `y!!` then `=`, so write spaces around `!=`:

```fren
comp c { in y: Int pub out z? ensure r: z? iff y != 1 }
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
  { code := "F0121", explanation := r#"`<-`, which is one token, as in Lean.

Erroneous code example:

```fren
comp c { in x: Int pub out p? ensure r: p? iff x <- 1 }
```

Fren is lexed as Lean is, and Lean has a token `<-`, so `x <- 1` is not
`x < -1`. To compare with a negation, write a space between `<` and `-`:

```fren
comp c { in x: Int pub out p? ensure r: p? iff x < -1 }
```
"# },
  { code := "F0122", explanation := r#"A chained comparison that orders both ways.

Erroneous code example:

```fren
comp c { in x: Int in y: Int pub out ok? ensure r: ok? iff 0 < x > y }
```

`<` and `<=` chain together, as in `0 <= x < 10`, and so do `>` and `>=`,
but a chain cannot mix the two directions: `0 < x > y` is more often a
mistake than a way to say that `x` is greater than both. Split it with
`and`.

```fren
comp c { in x: Int in y: Int pub out ok? ensure r: ok? iff 0 < x and x > y }
```
"# },
  { code := "F0128", explanation := r#"Spaces around the `..=` or `..` of a range pattern.

Erroneous code example:

```fren
comp c { in n: Int pub out y: Int ensure r: y = match n { 0 ..= 9 => 0, _ => 1 } }
```

A range is written without spaces around its `..=` or `..`, as a field read
is around its `.`, so that, in `n is 0..`, a bound on the next line is never
read as part of it:

```fren
comp c { in n: Int pub out y: Int ensure r: y = match n { 0..=9 => 0, _ => 1 } }
```

In Lean, Lean's own parser reports this, as a syntax error.
"# },
  { code := "F0129", explanation := r#"A range pattern without a bound that it needs.

Erroneous code example:

```fren
comp c { in n: Int pub out y: Int ensure r: y = match n { 0..= => 0, _ => 1 } }
```

The ranges are `a..=b`, `a..b`, `a..` and `..=b`: an inclusive range has
an upper bound, and an exclusive one a lower bound. For the integers below
`b`, write `..=` with the integer before `b`, as in `..=9` for those below
10:

```fren
comp c { in n: Int pub out y: Int ensure r: y = match n { ..=9 => 0, _ => 1 } }
```

In Lean, Lean's own parser reports this, as a syntax error.
"# },
  { code := "F0130", explanation := r#"`ordered` modifies an item other than an enum or a struct, or is written before `pub`.

Erroneous code example:

```fren
ordered fn f(Int): Int
```

`ordered` orders the variants of an enum as they are declared, and the
values of a struct by their fields, in the order declared, so that `<`,
`<=`, `>`, `>=`, `min` and `max` apply to its values. It applies only to
enums and structs, and is written after `pub`, as in `pub ordered enum
Level { Low, High }`. Remove it from any other item:

```fren
fn f(Int): Int
```
"# },
  { code := "F0131", explanation := r#"The binders of a quantifier are not in parentheses.

Erroneous code example:

```fren
enum Mode { Off, Heat }
comp c { pub out ok? ensure r: ok? iff (forall m: Mode, m = m) }
```

A quantifier's binders are written as a global expectation's are: each in
parentheses, `(x: T)`, or `(x y: T)` for several names of one type, and a
comma after the last.

```fren
enum Mode { Off, Heat }
comp c { in x: Mode pub out ok? ensure r: ok? iff (forall (m: Mode), m = x) }
```
"# },
  { code := "F0132", explanation := r#"A comma is missing after the binders of a quantifier.

Erroneous code example:

```fren
enum Mode { Off, Heat }
comp c { in x: Mode pub out ok? ensure r: ok? iff (exists (m: Mode) m = x) }
```

The binders of `forall` and `exists` end with a comma, before the body.
Add one.

```fren
enum Mode { Off, Heat }
comp c { in x: Mode pub out ok? ensure r: ok? iff (exists (m: Mode), m = x) }
```
"# },
  { code := "F0137", explanation := r#"A pattern type has a second pattern.

Erroneous code example:

```fren
comp c { in n: Int is 0.. is ..=9 }
```

A pattern type `T is P` has the values of `T` that match `P`, and its base
type `T` is never itself a pattern type, so `is` follows a type at most
once. Write one pattern that matches what both do:

```fren
comp c { in n: Int is 0..=9 }
```

In Lean, Lean's own parser reports this, as a syntax error.
"# },
  { code := "F0142", explanation := r#"`req`, where a member of a component is expected.

Erroneous code example:

```fren
comp c { in x: Int pub out y? req r: y? iff x > 0 }
```

A guarantee, what a component says the system must do, is written with
`ensure`, as an assumption is written with `assume`. `req` was its keyword
before, and is no longer a keyword: write `ensure` instead.

```fren
comp c { in x: Int pub out y? ensure r: y? iff x > 0 }
```

In Lean, Lean's own parser reports this, as a syntax error.
"# },
  { code := "F0155", explanation := r#"A type with its type arguments in parentheses.

Erroneous code example:

```fren
pub enum Option<T> { None, Some(T) }
comp c { in x: Option(Int) }
```

A type's arguments are written in angle brackets right after its name, as
in `Set<Int>`, `Rel<Int, Bool>` and `Option<Int>`. They were written in
parentheses before. The fix writes the whole type with angle brackets,
those of the types within it too:

```fren
pub enum Option<T> { None, Some(T) }
comp c { in x: Option<Int> }
```

A newtype's and a variant's parentheses hold a payload's types, not type
arguments, and stay parentheses, as in `struct Ms(Int)`.
"# },
  { code := "F0156", explanation := r#"Type parameters in parentheses.

Erroneous code example:

```fren
pub enum Option(T) { None, Some(T) }
```

A generic enumeration's, record's or function's type parameters are
written in angle brackets right after its name, as in `enum Option<T>`,
`struct Pair<A, B> { ... }` and `fn f<T>(x: T): T`. They were written in
parentheses before:

```fren
pub enum Option<T> { None, Some(T) }
```
"# },
  { code := "F0152", explanation := r#"A generic function's type parameter that is not a name.

Erroneous code example:

```fren
fn first<Set<T>>(s: Int): Int := s
```

A generic function's type parameters are names, written in angle brackets
right after its name and before its parameters, as in `fn f<T>(x: T): T`:

```fren
fn first<T>(x: T): T := x
```
"# },
  { code := "F0144", explanation := r#"A space before the `(` or `<` that opens what a name takes.

Erroneous code example:

```fren
fn f(Int): Int
comp c { in x: Int pub out y: Int ensure r: y = f (x) }
```

The `(` that opens a function's or a variant's arguments, a pattern's
binders, or a declaration's parameters or types, follows the name
directly, with no space, as in Lean, and so does the `<` that opens a
type's arguments, as in `Set<Int>` and `Option<Int>`, or a declaration's
type parameters, as in `enum Option<T>`. Remove the space:

```fren
fn f(Int): Int
comp c { in x: Int pub out y: Int ensure r: y = f(x) }
```

In Lean, Lean's own parser reports this, as a syntax error.
"# },
  { code := "F0143", explanation := r#"A function's body is written after its contract.

Erroneous code example:

```fren
fn pred(n: Int): Int
    assume positive: n > 0
    := n - 1
```

A function's contract follows its signature and, for a defined function,
its body: write the body, with its `:=`, before the first `assume` or
`ensure`.

```fren
fn pred(n: Int): Int := n - 1
    assume positive: n > 0
```

In Lean, Lean's own parser reports this, as a syntax error.
"# },
  { code := "F0140", explanation := r#"A pattern test has a guard.

Erroneous code example:

```fren
enum Shape { Circle(Int), Empty }
comp c { in s: Shape in ok? pub out y? ensure r: y? iff s is Shape::Circle(_) if ok? }
```

A guard, `if C`, belongs to a `match` arm, which it keeps from being taken
where `C` fails. A pattern test `e is P` has no arms, and a condition
beside its pattern is a conjunction:

```fren
enum Shape { Circle(Int), Empty }
comp c { in s: Shape in ok? pub out y? ensure r: y? iff (s is Shape::Circle(_) and ok?) }
```

In Lean, Lean's own parser reports this, as a syntax error.
"# },
  { code := "F0154", explanation := r#"A size bound of enumeration that is too large.

Erroneous code example:

```fren
set_option fren.enumeration.size 100 in
set_option fren.evidence "enumerated" in
comp c { in x: Int pub det out y: Int ensure r: y = x }
```

`fren.enumeration.size` bounds the size of the values that the checks set
to `"enumerated"` enumerate (see `Reqs/Check`, "Checking by
enumeration"). It is at most 64; the default, 3, is used instead. The
number of behaviours grows quickly with the bound, so a small one is
usually enough:

```fren
set_option fren.enumeration.size 5 in
set_option fren.evidence "enumerated" in
comp c { in x: Int pub det out y: Int ensure r: y = x }
```
"# },
  { code := "F0201", explanation := r#"A name that is not in scope.

Erroneous code example:

```fren
comp c { in x: Int pub out y: Int ensure r: y = z }
```

A name in an expression is a variable of the component, an item declared
in or imported into the current module, or a variant opened with
`use E::*`. Check the spelling, declare the name, or import it with `use`.

```fren
comp c { in x: Int pub out y: Int ensure r: y = x }
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
comp c { in m: Mode pub out on? ensure r: on? iff m = Mode::Cool }
```

The message lists the enum's variants. Check the spelling, or add the
variant to the enum.

```fren
enum Mode { Off, Heat, Cool }
comp c { in m: Mode pub out on? ensure r: on? iff m = Mode::Cool }
```
"# },
  { code := "F0204", explanation := r#"A path continues after something that has no members.

Erroneous code example:

```fren
enum Mode { Off, Heat }
comp c { in m: Mode pub out on? ensure r: on? iff m = Mode::Heat::On }
```

Only modules (whose members are their items) and enums (whose members are
their variants) can be followed by `::`.

```fren
enum Mode { Off, Heat }
comp c { in m: Mode pub out on? ensure r: on? iff m = Mode::Heat }
```
"# },
  { code := "F0205", explanation := r#"A variant name that two enums opened with `*` both have.

Erroneous code example:

```fren
enum E { A, B }
enum F { A, C }
use E::*
use F::*
comp c { in e: E pub out y? ensure r: y? iff e = A }
```

`use E::*` brings `E`'s variants into scope. When two opened enums have a
variant of the same name, that name is ambiguous. Qualify it with its
enum's name.

```fren
enum E { A, B }
enum F { A, C }
use E::*
use F::*
comp c { in e: E pub out y? ensure r: y? iff e = E::A }
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
comp c { in e: E pub out y? ensure r: y? iff e = E }
```

The message says what was expected (a value, a type or a component) and what
the name actually is. Here, `E` is an enum, but a value was expected: one of
its variants.

```fren
enum E { A }
comp c { in e: E pub out y? ensure r: y? iff e = E::A }
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
comp c { in x: Int pub out y: Int ensure r: y = x }
```
"# },
  { code := "F0214", explanation := r#"A `set_option fren.evidence` value that does not exist.

Erroneous code example:

```fren
set_option fren.evidence "testing" in
comp c { in x? pub det out y? ensure r: y? iff x? }
```

The evidence of a check is `"tested"`, to have it tested instead of asked of
the solver, `"enumerated"`, to have it decided by enumerating behaviours,
smallest first, `"enumerated+tested"`, to have it tested too where
enumeration is not complete, or `"solver"`, the default (see `Reqs/Check`,
"Checking by testing" and "Checking by enumeration").

```fren
set_option fren.evidence "tested" in
comp c { in x? pub det out y? ensure r: y? iff x? }
```
"# },
  { code := "F0215", explanation := r#"A `set_option fren.evidence` before something that has no checks to test.

Erroneous code example:

```fren
comp c {
  in x?
  pub out y?
  set_option fren.evidence "tested" in
  ensure r: y? iff x?
}
```

A guarantee is not itself checked: the checks of a component are about
its expectations, instances, `det out`s and the component as a whole, so
the setting goes before one of those, or before the component.

```fren
set_option fren.evidence "tested" in
comp c {
  in x?
  pub out y?
  ensure r: y? iff x?
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
  ensure r: y? iff x?
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
  ensure r: y? iff x?
}
```
"# },
  { code := "F0217", explanation := r#"A declaration hides a name in scope, but is not written with `!`.

Erroneous code example:

```fren
pub const RATE: Int := 2
set_option fren.lint.non_snake_case "allow" in
comp c { in RATE: Int pub out y: Int ensure r: y = RATE }
```

Within `c`, `RATE` is the input, not the constant. A component's
variables and instances, a function's parameters and a global
expectation's binders may hide the constants, functions and variants in
scope, and a `match` arm's binders may hide those and also variables,
parameters, instances, global expectations' binders and other binders.
Shadowing is allowed, but must be explicit, so that a
reader knows which `RATE` a use means: the declaration that hides the name
is written with `!` directly after it, as `RATE!`, or `ready?!` for a
`Bool`. Its uses are written without `!`. This error replaces the lint
`shadowed_constants`, which was `F0713`.

Write the `!`:

```fren
pub const RATE: Int := 2
set_option fren.lint.non_snake_case "allow" in
comp c { in RATE!: Int pub out y: Int ensure r: y = RATE }
```

Or rename the variable:

```fren
pub const RATE: Int := 2
comp c { in rate: Int pub out y: Int ensure r: y = rate * RATE }
```
"# },
  { code := "F0218", explanation := r#"A declaration is written with `!`, but hides nothing.

Erroneous code example:

```fren
comp c { in x!: Int pub out y: Int ensure r: y = x }
```

`!` after a declared name says that it shadows a name in scope (see
`F0217`). No `x` is in scope where this `x` is declared, so there is
nothing to shadow; and items, constraints, fields and variants never
shadow. Remove the `!`:

```fren
comp c { in x: Int pub out y: Int ensure r: y = x }
```
"# },
  { code := "F0219", explanation := r#"A declaration's name, with its `!`, is one of Lean's tokens.

Erroneous code example:

```fren
pub enum Shape { Circle(Int), Square }
comp c { in s: Shape pub out p? ensure r: p? iff match s { Shape::Circle(s!) => s > 0, _ => false } }
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
comp c { in s: Shape pub out p? ensure r: p? iff match s { Shape::Circle(r) => r > 0, _ => false } }
```
"# },
  { code := "F0220", explanation := r#"A declaration is named `true` or `false`.

Erroneous code example:

```fren
comp c { in true: Int pub out y: Int ensure r: y = 1 }
```

`true` and `false` are the literals of type `Bool` wherever an expression
is expected, so nothing could name a variable, item or other declaration
called `true` or `false`. Rename the declaration:

```fren
comp c { in t: Int pub out y: Int ensure r: y = t }
```
"# },
  { code := "F0221", explanation := r#"A declaration is named with one of Lean's keywords.

Erroneous code example:

```fren
struct Slot { at: Int }
```

Lean reads its keywords that have the shape of an identifier, such as
`at`, `for`, `by`, `fun` and `Type`, as keywords, so a spec read by Lean
could not use them as names. Fren reserves them in both front ends, and
no variable, item, field or other declaration can have one as its name.
Rename the declaration:

```fren
struct Slot { position: Int }
```
"# },
  { code := "F0341", explanation := r#"A definition of a `let` or `where` clause mentions itself or a later one.

Erroneous code example:

```fren
comp c { in x: Int pub out y? ensure r: y? iff big? where big? := x > limit, limit := 10 }
```

The definitions of a clause are read in order: each may mention the ones
before it, and the expression the clause belongs to may mention all of
them, but no definition mentions itself or a later one, so definitions are
never recursive. Define what a definition needs before it:

```fren
comp c { in x: Int pub out y? ensure r: y? iff big? where limit := 10, big? := x > limit }
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
comp c { in x: Int pub out y? ensure r: y? iff x }
```

Each operator takes operands of particular types: `and`, `or`, `iff`, `not`,
`when` and `unless` take `Bool`s, and arithmetic and `<`, `<=`, `>`, `>=`
take `Int`s or `Nat`s. A constraint, and the condition of `if`, is a
`Bool`. Compare an `Int` with a number to make a `Bool`. A `Nat` is
accepted where an `Int` is expected, but an `Int` is never accepted where
a `Nat` is: `n - 1` is an `Int`, even if `n` is a `Nat`.

```fren
comp c { in x: Int pub out y? ensure r: y? iff x > 0 }
```
"# },
  { code := "F0305", explanation := r#"`=` or `!=` compares values of different types.

Erroneous code example:

```fren
enum Mode { Off, On }
comp c { in m: Mode pub out y? ensure r: y? iff m = 1 }
```

Both sides of `=` and `!=` must have the same type. Enums are not numbers:
compare an enum with one of its variants.

```fren
enum Mode { Off, On }
comp c { in m: Mode pub out y? ensure r: y? iff m = Mode::On }
```
"# },
  { code := "F0306", explanation := r#"The branches of `if` have different types.

Erroneous code example:

```fren
comp c { in b? pub out y: Int ensure r: y = if b? then 1 else true }
```

`if c then a else b` is `a` or `b`, so both must have the same type, or
be a `Nat` and an `Int`, when the `Nat` is widened to an `Int`.

```fren
comp c { in b? pub out y: Int ensure r: y = if b? then 1 else 0 }
```
"# },
  { code := "F0307", explanation := r#"Two variables are multiplied.

Erroneous code example:

```fren
comp c { in x: Int pub out y: Int ensure r: y = x * x }
```

Fren's checks are decided by an SMT solver over linear integer arithmetic,
where nonlinear constraints are undecidable. One side of `*` must mention no
variable and no uninterpreted function: it is built from literals and
constants, such as `2`, `2 * 3` or `(MAX - MIN)`.

```fren
comp c { in x: Int pub out y: Int ensure r: y = 2 * x }
```
"# },
  { code := "F0308", explanation := r#"A function or variant is applied to the wrong number of arguments, or a pattern has the wrong number of binders.

Erroneous code example:

```fren
type Name
fn arity(Name): Int

comp c { in x: Name pub out y: Int ensure r: y = arity(x, x) }
```

An application gives one argument for each of the function's parameters.

```fren
type Name
fn arity(Name): Int

comp c { in x: Name pub out y: Int ensure r: y = arity(x) }
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

comp c { in r: Int pub out y: Int ensure r1: y = rate(r) }
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

`Set<Name>` is as abstract as `Name`, so a field of that type is an error too.
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

comp c { in x: Int pub out l: List ensure r: l = List::Cons(x, List::Nil) }
```

A recursive enum, or a type containing one, has values of any size. The
realizability check asks whether outputs exist, which the solver cannot
decide in general for such values. Inputs may have unbounded types; an
output can describe the value by bounded parts:

```fren
enum List { Nil, Cons(Int, List) }

comp c { in l: List pub out head: Int ensure r: head = match l { List::Cons(h, _) => h, List::Nil => 0 } }
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

comp c { in p: Point pub out z: Int ensure r: z = p.z }
```

Only records have fields, and only those they declare:

```fren
struct Point { x: Int, y: Int }

comp c { in p: Point pub out z: Int ensure r: z = p.x }
```
"# },
  { code := "F0316", explanation := r#"A `match` on a value of a type that patterns do not match.

Erroneous code example:

```fren
comp c { in s: Set<Int> pub out y: Int ensure r: y = match s { _ => 0 } }
```

`match` reads a value of an enum, a `Bool`, an `Int`, a `Nat` or a
`String`. For other types, use `if`:

```fren
comp c { in s: Set<Int> pub out y: Int ensure r: y = if s = {} then 0 else 1 }
```
"# },
  { code := "F0317", explanation := r#"A `match` does not cover every value.

Erroneous code example:

```fren
enum Shape { Circle(Int), Square(Int), Empty }

comp c { in s: Shape pub out a: Int ensure r: a = match s { Shape::Circle(r) => 3 * r, Shape::Square(w) => w } }
```

A `match` has a value for every value of its scrutinee: an arm for each
variant, or a last arm `_` for the rest. The error names the values that
no arm matches, as patterns. Nested patterns, literals and ranges cover
only the values they match, so a `match` on an `Int` covers every value
only with a last arm `_` or a binder, or ranges that together match every
integer, and one on a `String` only with a last arm `_` or a binder:

```fren
enum Shape { Circle(Int), Square(Int), Empty }

comp c { in s: Shape pub out a: Int ensure r: a = match s { Shape::Circle(r) => 3 * r, Shape::Square(w) => w, _ => 0 } }
```
"# },
  { code := "F0318", explanation := r#"An arm of a `match` that can never be chosen.

Erroneous code example:

```fren
enum Mode { Off, On }

comp c { in m: Mode pub out y: Int ensure r: y = match m { _ => 0, Mode::On => 1 } }
```

The first arm whose pattern matches is chosen, so an arm is never chosen
when the arms before it match every value its pattern matches: an arm after
`_`, an arm for a variant or literal that an earlier arm covers, a range
within earlier ranges, and a `_` after arms for every value. Likewise, an
alternative of an or-pattern, in an arm or in a pattern test such as
`s is Shape::Circle(_) | Shape::Circle(_)`, that matches only what earlier
ones match never matches. Remove the arm, or reorder the arms:

```fren
enum Mode { Off, On }

comp c { in m: Mode pub out y: Int ensure r: y = match m { Mode::On => 1, _ => 0 } }
```
"# },
  { code := "F0319", explanation := r#"A pattern that is not a variant of the scrutinee's enum.

Erroneous code example:

```fren
enum Mode { Off, On }
enum Fan { Slow, Fast }

comp c { in m: Mode pub out y: Int ensure r: y = match m { Fan::Slow => 1, _ => 0 } }
```

Each pattern names a variant of the enum being matched, or is `_`:

```fren
enum Mode { Off, On }
enum Fan { Slow, Fast }

comp c { in m: Mode pub out y: Int ensure r: y = match m { Mode::On => 1, _ => 0 } }
```
"# },
  { code := "F0320", explanation := r#"The arms of a `match` have different types.

Erroneous code example:

```fren
enum Mode { Off, On }

comp c { in m: Mode pub out y: Int ensure r: y = match m { Mode::On => 1, Mode::Off => false } }
```

A `match` has the value of one of its arms, so every arm has the same
type:

```fren
enum Mode { Off, On }

comp c { in m: Mode pub out y: Int ensure r: y = match m { Mode::On => 1, Mode::Off => 0 } }
```
"# },
  { code := "F0358", explanation := r#"The rows of a table have values of different types.

Erroneous code example:

```fren
comp c { in x: Int pub out y: Int ensure r: y = table { x > 0 => 1, _ => false } }
```

A table has the value of one of its rows, so every row's value has the
same type:

```fren
comp c { in x: Int pub out y: Int ensure r: y = table { x > 0 => 1, _ => 0 } }
```
"# },
  { code := "F0359", explanation := r#"A row of a table, or an arm of a table over a scrutinee, comes after its `_`.

Erroneous code example:

```fren
comp c { in x: Int pub out y: Int ensure r: y = table { _ => 0, x > 0 => 1 } }
```

`_` holds wherever no earlier row does, so a row after it could never be
reached. `_` is the last row:

```fren
comp c { in x: Int pub out y: Int ensure r: y = table { x > 0 => 1, _ => 0 } }
```

Likewise, the `_` arm without a guard of a table over a scrutinee is taken
wherever no other arm is, so it is the last arm.
"# },
  { code := "F0321", explanation := r#"A method that a type does not have.

Erroneous code example:

```fren
comp c { in s: String pub out n: Int ensure r: n = s.length }
```

The methods of `String` are `len`, `starts_with?`, `ends_with?` and
`contains?`. A method that returns a `Bool` ends in `?`:

```fren
comp c { in s: String pub out n: Int ensure r: n = s.len }
```
"# },
  { code := "F0322", explanation := r#"A method call on a value of a type without methods.

Erroneous code example:

```fren
comp c { in b? pub out p? ensure r: p? iff (b?).contains?(1) }
```

Only `Int`s, `String`s, sets, relations, sequences and the values of an
ordered enum have methods. Use the operators of the type instead:

```fren
comp c { in b? pub out p? ensure r: p? iff not b? }
```
"# },
  { code := "F0323", explanation := r#"The argument of `matches?` is not a string literal.

Erroneous code example:

```fren
comp c { in s: String in p: String pub out m? ensure r: m? iff s.matches?(p) }
```

A pattern is parsed when the spec is checked, so it is written as a
literal at the call, usually a raw one. Only literals are patterns: a
variable's value would be matched literally, which no reader would expect.

```fren
comp c { in s: String pub out m? ensure r: m? iff s.matches?(r"[a-z]+") }
```
"# },
  { code := "F0324", explanation := r#"`{}` where nothing gives it a type.

Erroneous code example:

```fren
comp c { pub out n: Int ensure r: n = {}.card }
```

`{}` and `[]` have no member to give them a type, so they take their type
from where they are written: they can only be checked against a type that
is given to them, as the other side of `=`, a binding, a field or an
argument gives one (`Reqs/Lang/Types#checking-and-synthesis`). Where an
expression must synthesize its own type, as a receiver must, they are an
error. Write them where their type is known:

```fren
comp c { in s: Set<Int> pub out e? ensure r: e? iff s = {} }
```
"# },
  { code := "F0325", explanation := r#"The right of `in` is not a set of the left's type.

Erroneous code example:

```fren
comp c { in x: Int in s: Set<String> pub out p? ensure r: p? iff x in s }
```

`x in s` is membership: `s` must be a `Set<T>`, where `T` is the type of
`x`:

```fren
comp c { in x: Int in s: Set<Int> pub out p? ensure r: p? iff x in s }
```
"# },
  { code := "F0326", explanation := r#"The members of a set literal have different types.

Erroneous code example:

```fren
comp c { in s: Set<Int> pub out p? ensure r: p? iff s = {1, true} }
```

A set's members all have its element type, which the first member gives:

```fren
comp c { in s: Set<Int> pub out p? ensure r: p? iff s = {1, 2} }
```
"# },
  { code := "F0327", explanation := r#"A record or enum is the element type of a set within one of its own fields or payloads.

Erroneous code example:

```fren
enum Tree { Leaf, Node(Set<Tree>) }
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

comp c { in r: Rel<U, R> pub out p? ensure q: p? iff (U::A, U::B) in r.closure }
```

`r.closure` chains pairs `(a, b)`, `(b, c)`, so it needs a relation of a type
with itself, `Rel<A, A>`. `r join q` composes `r: Rel<A, B>` with
`q: Rel<B, C>`: the second type of `r` must be the first of `q`:

```fren
enum U { A, B }

enum R { X, Y }

comp c { in r: Rel<U, U> pub out p? ensure q: p? iff (U::A, U::B) in r.closure }
```
"# },
  { code := "F0329", explanation := r#"A pair is written outside a relation literal and the left of `in`.

Erroneous code example:

```fren
comp c { in x: Int pub out p? ensure q: p? iff (x, 1) = (1, x) }
```

There is no type of pairs. A pair is a member of a relation, written in a
relation literal, `{(a, b)}`, or tested with `(a, b) in r`:

```fren
comp c { in x: Int pub out p? ensure q: p? iff (x, 1) in {(1, x)} }
```
"# },
  { code := "F0332", explanation := r#"A value that is not a sequence is indexed.

Erroneous code example:

```fren
comp c { in s: Set<Int> pub out x: Int ensure r: x = s[0] }
```

Only a sequence, `Seq<T>`, has positions. A set has no order, so it has no
first member:

```fren
comp c { in s: Seq<Int> pub out x: Int ensure r: s.len > 0 and x = s[0] or s.len = 0 }
```
"# },
  { code := "F0333", explanation := r#"An alternative of an or-pattern binds a name.

Erroneous code example:

```fren
enum Shape { Circle(Int), Square(Int), Empty }

comp c { in s: Shape pub out a: Int ensure r: a = match s { Shape::Circle(n) | Shape::Square(n) => n, _ => 0 } }
```

An or-pattern matches any of its alternatives, so a name bound by one,
at any depth, would have no value when another matches. Ignore the
payload with `_`, or give each variant its own arm:

```fren
enum Shape { Circle(Int), Square(Int), Empty }

comp c { in s: Shape pub out a: Int ensure r: a = match s { Shape::Circle(n) => n, Shape::Square(n) => n, _ => 0 } }
```
"# },
  { code := "F0334", explanation := r#"A pattern test binds a name where nothing could mention it.

Erroneous code example:

```fren
enum Shape { Circle(Int), Empty }

comp c { in s: Shape pub out big? ensure r: big? iff s is Shape::Circle(n) }
```

A pattern test, `e is P`, binds the names of its pattern only for what
follows it where it holds: the later operands of its chain of `and`, the
body of a `when`, and the `then` branch of an `if`, whose condition it is.
On its own, as here, under `or` or `not`, or as the condition of `unless`,
whose body holds where the pattern does not match, nothing could mention
them, so every binder is `_`. To test the variant, ignore the payload; to
read it, bind it where something follows the test:

```fren
enum Shape { Circle(Int), Empty }

comp c { in s: Shape pub out round? pub out big? ensure r: round? iff s is Shape::Circle(_)
    ensure b: big? iff s is Shape::Circle(n) and n > 10 }
```
"# },
  { code := "F0335", explanation := r#"A pattern test on a value of a type that patterns do not match.

Erroneous code example:

```fren
comp c { in s: Set<Int> pub out empty? ensure r: empty? iff s is _ }
```

`is` tests a value of an enum, a `Bool`, an `Int`, a `Nat` or a `String`
against a pattern. For other types, compare values with `=` or `in`:

```fren
comp c { in s: Set<Int> pub out empty? ensure r: empty? iff s = {} }
```
"# },
  { code := "F0348", explanation := r#"A pattern of another type than the value it matches.

Erroneous code example:

```fren
comp c { in n: Int pub out y: Int ensure r: y = match n { "zero" => 0, _ => 1 } }
```

A literal matches a value of its own type: an integer an `Int` or a `Nat`,
a string a `String`, and `true` and `false` a `Bool`. A range matches an
`Int` or a `Nat`, and a variant a value of its enum. Only `_` and binders match a value of any
type. Write a pattern of the value's type:

```fren
comp c { in n: Int pub out y: Int ensure r: y = match n { 0 => 0, _ => 1 } }
```
"# },
  { code := "F0349", explanation := r#"A range pattern that matches no integer.

Erroneous code example:

```fren
comp c { in n: Int pub out y: Int ensure r: y = match n { 9..=0 => 0, _ => 1 } }
```

`a..=b` matches the integers from `a` to `b`, and `a..b` those from `a` to
`b - 1`, so a range whose lower bound is above its upper one, or `a..a`,
matches none. Put the smaller bound first:

```fren
comp c { in n: Int pub out y: Int ensure r: y = match n { 0..=9 => 0, _ => 1 } }
```
"# },
  { code := "F0350", explanation := r#"A range pattern's bound that is not an integer or a constant of `Int` or `Nat`.

Erroneous code example:

```fren
comp c { in n: Int in m: Int pub out y: Int ensure r: y = match n { 0..=m => 0, _ => 1 } }
```

The bounds of a range are fixed: an integer literal, possibly negated, or
a constant of type `Int` or `Nat`. To compare with a variable, use `if`:

```fren
comp c { in n: Int in m: Int pub out y: Int ensure r: y = if 0 <= n and n <= m then 0 else 1 }
```
"# },
  { code := "F0351", explanation := r#"A constant as a range pattern's bound, whose value is not known where the range is checked.

Erroneous code example:

```fren
const MAX: Int := "abcde".len

comp c { in n: Int pub out y: Int ensure r: y = match n { 0..=MAX => 0, _ => 1 } }
```

Ranges are checked before the spec is: an empty range is an error, and
ranges count towards whether a `match` covers every value. So a constant
used as a bound has an integer constant expression as its value, built
from integer literals and such constants by `+`, `-`, `*`, `div`, `mod`,
`abs`, `min`, `max` and parentheses:

```fren
const MAX: Int := 2 * 5

comp c { in n: Int pub out y: Int ensure r: y = match n { 0..=MAX => 0, _ => 1 } }
```
"# },
  { code := "F0368", explanation := r#"A pattern that stands for too many cases.

Erroneous code example:

```fren
enum B { X, Y }
enum P { V(B, B, B, B, B, B, B, B, B) }

comp c { in p: P pub out y: Int ensure r: y = match p {
    P::V(B::X | B::Y, B::X | B::Y, B::X | B::Y, B::X | B::Y, B::X | B::Y, B::X | B::Y, B::X | B::Y, B::X | B::Y, B::X | B::Y) => 0,
    _ => 1,
} }
```

Whether each arm is reachable is decided for each case of its pattern:
each choice of one alternative of each of its or-patterns. Or-patterns
within several values of a payload multiply, so a pattern may stand for at
most 256 cases. Match fewer values with or-patterns, or match the payload
in the arm's body:

```fren
enum B { X, Y }
enum P { V(B, B, B, B, B, B, B, B, B) }

comp c { in p: P pub out y: Int ensure r: y = match p {
    P::V(_, _, _, _, _, _, _, _, B::X) => 0,
    _ => 1,
} }
```
"# },
  { code := "F0336", explanation := r#"The divisor of `div` or `mod` is not an integer literal or a constant, or is a constant whose value is not known when the spec is read.

Erroneous code example:

```fren
comp c { in x: Int in y: Int pub out q: Int := x div y }
```

Fren's checks are decided by an SMT solver over linear integer arithmetic,
which divides only by constants. The divisor of `div` and `mod` is an
integer literal or a constant, possibly negated, such as `2`, `-2` or `N`.
A constant's value must be an integer constant expression: built from
integer literals and such constants by `+`, `-`, `*`, `div`, `mod`, `abs`,
`min` and `max`, so that its value is known when the spec is read.

```fren
const N: Int := 2 * 4

comp c { in x: Int pub out q: Int := x div N }
```
"# },
  { code := "F0337", explanation := r#"The divisor of `div` or `mod` is `0`.

Erroneous code example:

```fren
comp c { in x: Int pub out r: Int := x mod 0 }
```

SMT-LIB leaves division by zero unspecified, and Lean makes it `0`, so the
two front ends would give `x mod 0` different meanings. Divide by a
constant other than `0`:

```fren
comp c { in x: Int pub out r: Int := x mod 2 }
```
"# },
  { code := "F0352", explanation := r#"Values of an enum or struct that is not ordered are compared with `<`, `<=`, `>` or `>=`.

Erroneous code example:

```fren
enum Level { Low, Middle, High }

comp c { in l: Level pub out high? ensure r: high? iff l > Level::Middle }
```

The order in which a plain enum's variants are listed is not part of its
meaning, so its values are not ordered. Declare the enum `ordered` to
order its variants as they are declared, or compare with `=` or `in`:

```fren
ordered enum Level { Low, Middle, High }

comp c { in l: Level pub out high? ensure r: high? iff l > Level::Middle }
```

Likewise, a struct, a newtype among them, is ordered only if it is
declared `ordered`, even when its fields' types are: `struct Ms(Int)` has
`=` and `!=`, and `ordered struct Ms(Int)` also `<`, `<=`, `>`, `>=`,
`min` and `max`, which compare its values as their fields compare. An
ordered struct with several fields orders its values by their fields, in
the order declared.
"# },
  { code := "F0353", explanation := r#"An ordered enum has a variant with a payload.

Erroneous code example:

```fren
ordered enum Size { Small, Custom(Int) }
```

An ordered enum orders its variants as they are declared, and does not
yet order values with payloads by their payloads, so only an enum without
payloads may be ordered. Remove the payload, or `ordered`:

```fren
ordered enum Size { Small, Large }
```
"# },
  { code := "F0354", explanation := r#"`min` or `max` of a value of an enum or struct that is not ordered.

Erroneous code example:

```fren
enum Level { Low, High }

comp c { in a: Level in b: Level pub out m: Level ensure r: m = a.max(b) }
```

Only `Int`s, `Nat`s, `String`s and the values of a type declared
`ordered` have `min` and `max`. Declare the enum `ordered` to order its
variants as they are declared, or a struct `ordered` to order its values
by their fields:

```fren
ordered enum Level { Low, High }

comp c { in a: Level in b: Level pub out m: Level ensure r: m = a.max(b) }
```
"# },
  { code := "F0356", explanation := r#"A quantifier with more than 256 instances.

Erroneous code example:

```fren
enum Nine { N(Bool, Bool, Bool, Bool, Bool, Bool, Bool, Bool, Bool) }
comp c { in x: Nine pub out ok? ensure r: ok? iff (exists (n: Nine), n = x) }
```

A quantifier is expanded into one instance for each combination of the
values of its bound names, which must be at most 256, counting those of
the quantifiers around it: `Nine` has 2^9 = 512 values. Quantify over a smaller type, or state the property of a variable:

```fren
enum Nine { N(Bool, Bool, Bool, Bool, Bool, Bool, Bool, Bool, Bool) }
comp c { in x: Nine in n: Nine pub out ok? ensure r: ok? iff n = x }
```
"# },
  { code := "F0330", explanation := r#"A function's parameters are named, but it has neither a body nor a contract, or it has one, but a parameter has no name.

Erroneous code examples:

```fren
fn rate(n: Int): Int
fn double(Int): Int := 1
fn half(Int): Int
    assume even: true
```

An uninterpreted function without a contract has parameters with types but
no names, since nothing mentions them. A defined function's body, and the
clauses of a function's contract, mention its parameters, so each is
named, like a component's variable: `x: T`, or `x?` for a `Bool`.

```fren
fn rate(Int): Int
fn double(n: Int): Int := 2 * n
fn half(n: Int): Int
    assume even: n mod 2 = 0
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

comp c { in n: Name pub out r: Int ensure ranked: r = rank(arity(n)) }
```
"# },
  { code := "F0380", explanation := r#"A precondition applies the function whose contract it is in.

Erroneous code example:

```fren
fn rate(n: Int): Int
    assume small: rate(n) < 10
```

A precondition says where the function may be applied, so it cannot
depend on the function's value. What the value gives is a postcondition,
written with `ensure`:

```fren
fn rate(n: Int): Int
    ensure small: rate(n) < 10
```
"# },
  { code := "F0381", explanation := r#"A postcondition applies the function whose contract it is in to other than its parameters.

Erroneous code example:

```fren
fn rate(n: Int): Int
    ensure grows: rate(n + 1) > rate(n)
```

A postcondition states what the function gives at its own arguments: the
function's value is written by applying it to its parameters, each by its
name, in order, as `rate(n)`. A relation between its values at different
arguments is stated where the function is applied, as an assumption of a
component:

```fren
fn rate(n: Int): Int
    ensure positive: rate(n) > 0

comp c {
    in n: Int
    pub out r: Int

    assume grows: rate(n + 1) > rate(n)

    ensure growth: r = rate(n + 1) - rate(n)

    expect positive: r > 0
}
```
"# },
  { code := "F0391", explanation := r#"Two arms of a table over a scrutinee, without guards, overlap.

Erroneous code example:

```fren
comp grade {
    in n: Int
    pub out g: Int

    ensure r: g = table n { ..=49 => 0, 50..=100 => 1, 100.. => 2 }
}
```

The arms of a table over a scrutinee are disjoint, so that its value
does not depend on their order: no two of them are taken at one value of
the scrutinee.
Two arms without guards whose patterns some value matches both overlap
everywhere that value is the scrutinee, so the static rules reject them,
naming such a value; here, both the second and the third arm match `100`.
A last arm `_` is taken wherever no other arm is, so it overlaps none.
Narrow one of the patterns, tell the arms apart with guards, or write a
`match`, which takes the first arm that matches:

```fren
comp grade {
    in n: Int
    pub out g: Int

    ensure r: g = table n { ..=49 => 0, 50..=99 => 1, 100.. => 2 }
}
```
"# },
  { code := "F0338", explanation := r#"`Nat` is an element type, or the type of a payload of a recursive enumeration.

Erroneous code example:

```fren
struct Stock { counts: Set<Nat> }
```

A `Nat` brings the constraint that it is at least 0. Within a set,
relation or sequence, or as a payload of a recursive enumeration, that
constraint would hold of every element, and for now Fren does not carry it
there. Use an `Int`, and say where it is used that it is at least 0, or
use the pattern type `Int is 0..`, which may be an element type outside
the decidable core:

```fren
struct Stock { counts: Set<Int> }

comp restock {
    in stock: Stock
    pub out more?

    assume counted: not -1 in stock.counts

    ensure rule: more? iff 0 in stock.counts
}
```
"# },
  { code := "F0339", explanation := r#"A record update of a value that is not a record.

Erroneous code example:

```fren
comp c { in n: Int pub out m: Int ensure r: m = { n with x := 1 } }
```

`{ r with x := e }` is `r` with a new value for its field `x`, so `r` must
be a record. A value of another type has no fields to update; write the
new value instead:

```fren
comp c { in n: Int pub out m: Int ensure r: m = 1 }
```
"# },
  { code := "F0340", explanation := r#"A record update gives a field that its record does not have, or gives a field more than once.

Erroneous code example:

```fren
struct Point { x: Int, y: Int }

comp c { in p: Point pub out q: Point ensure r: q = { p with z := 1, x := 1, x := 2 } }
```

An update gives new values to some of the fields of its record, each at
most once, and the other fields keep their values from `r`. Give each
field once, and only the record's fields:

```fren
struct Point { x: Int, y: Int }

comp c { in p: Point pub out q: Point ensure r: q = { p with x := 2 } }
```
"# },
  { code := "F0365", explanation := r#"A function is declared with the name of a built-in function.

Erroneous code example:

```fren
fn exactly_one?(a?, b?) := a? != b?
```

`exactly_one?` and `at_most_one?` are built-in functions, the cardinality
operators: `exactly_one?(a?, b?, c?)` holds when exactly one of its `Bool`
arguments is `true`, and `at_most_one?(a?, b?, c?)` when at most one is.
Their names are reserved. Apply the built-in function, or give your
function another name:

```fren
fn either?(a?, b?) := exactly_one?(a?, b?)
```
"# },
  { code := "F0367", explanation := r#"A cardinality operator is applied to no arguments.

Erroneous code example:

```fren
comp c { in a? in b? expect e: exactly_one?() }
```

`exactly_one?(...)` holds when exactly one of its `Bool` arguments is
`true`, and `at_most_one?(...)` when at most one is. Each counts its
arguments, so it needs at least one. Give it the `Bool`s to count:

```fren
comp c { in a? in b? expect e: at_most_one?(a?, b?) }
```
"# },
  { code := "F0342", explanation := r#"The definition of a `let` or `where` name does not have the type written for it.

Erroneous code example:

```fren
comp c { in x: Int pub out y? ensure r: let n: Int := x > 0 in y? iff n > 0 }
```

A definition `x: T := e` names the value of `e`, so `e` must have type `T`.
The type may also be left out, `x := e`, and is then the type of `e`. In
a `let`, `in` ends the last definition, so a membership there is written
in parentheses, as in `b? := (x in s)`. Write the type of the expression,
or correct the expression:

```fren
comp c { in x: Int pub out y? ensure r: let n: Int := x + 1 in y? iff n > 0 }
```
"# },
  { code := "F0361", explanation := r#"A newtype that does not have exactly one field.

Erroneous code example:

```fren
struct Pair(Int, Int)
```

`struct N(T)` declares a newtype: a type of its own, with the values of
`T`, its underlying type. A newtype has exactly one field, which has no
name. For several fields, declare a record with named fields:

```fren
struct Pair { first: Int, second: Int }
```
"# },
  { code := "F0362", explanation := r#"An operator that a newtype does not have.

Erroneous code example:

```fren
struct Ms(Int)

comp c { in t: Ms pub out d: Ms ensure r: d = t * Ms(2) }
```

A newtype has `=` and `!=`; the orderings `<`, `<=`, `>` and `>=` when
it is declared `ordered`; and `+` and `-` of two of its values when its
underlying type is an `Int`, `+` alone when it is a `Nat`, since `a.0 -
b.0` is an `Int`, which is never narrowed to a `Nat`. Any other operator
applies to its value, read with `.0`, and the result is built again:

```fren
struct Ms(Int)

comp c { in t: Ms pub out d: Ms ensure r: d = Ms(t.0 * 2) }
```
"# },
  { code := "F0363", explanation := r#"An operator whose operands are a newtype and another type.

Erroneous code example:

```fren
ordered struct Ms(Int)
struct Bytes(Int)

comp c { in t: Ms in n: Bytes pub out late? ensure r: late? iff t > n }
```

A newtype is a type distinct from every other, even from its underlying
type, so that its values are not mixed with others by mistake: an `Ms` is
not compared with a `Bytes`, nor with an `Int`, and no literal is an
`Ms`. Compare two values of one newtype, building one with `Ms(e)` if need
be, or compare their values, read with `.0`, if mixing them is meant:

```fren
ordered struct Ms(Int)
struct Bytes(Int)

comp c { in t: Ms in n: Bytes pub out late? ensure r: late? iff t > Ms(100) }
```
"# },
  { code := "F0364", explanation := r#"A newtype built as a record with named fields, or a record with named fields built as a newtype.

Erroneous code example:

```fren
struct Ms(Int)

comp c { pub out t: Ms ensure r: t = Ms { value := 5 } }
```

A newtype, declared `struct Ms(Int)`, has one field, which has no name: it
is built as `Ms(e)`, and its field read as `x.0`. A record with named
fields, declared `struct Point { x: Int, y: Int }`, is built as `Point {
x := 1, y := 2 }`, not as `Point(1, 2)`:

```fren
struct Ms(Int)

comp c { pub out t: Ms ensure r: t = Ms(5) }
```
"# },
  { code := "F0369", explanation := r#"A pattern on a type alias that names a pattern type.

Erroneous code example:

```fren
type Byte := Int is 0..=255
comp c { in n: Byte is ..=9 }
```

Pattern types are not nested: the base type of `T is P` is never itself a
pattern type, and an alias of one is that pattern type. Write one pattern
type, whose pattern matches what both patterns do:

```fren
type Byte := Int is 0..=255
comp c { in n: Int is 0..=9 }
```
"# },
  { code := "F0370", explanation := r#"A pattern type's pattern binds a name.

Erroneous code example:

```fren
type Any := Int is n
```

A pattern type's pattern binds no names: a name of one segment that is not
a variant, `true` or `false` would match every value and name it, which
means nothing in a type. Write `_` to match every value, or name a variant,
or a constant as a range's bound:

```fren
const MAX: Int := 9
type Digit := Int is 0..=MAX
```
"# },
  { code := "F0371", explanation := r#"A field of an ordered struct has a type that is not ordered.

Erroneous code example:

```fren
ordered struct Entry { key: Int, tags: Set<Int> }
```

An ordered struct orders its values by their fields, in the order
declared: first by the first field, then, where those are equal, by the
second, and so on. So each field's type must be ordered: an `Int`, a `Nat`,
a `String`, a pattern type or alias of one of these, or an enum or struct
declared `ordered`. A newtype's one field is its underlying type, which
must be ordered too. Declare the field's type `ordered`, if it can be,
drop the field, or declare the struct without `ordered`:

```fren
ordered struct Entry { key: Int, size: Nat }
```
"# },
  { code := "F0385", explanation := r#"A type written with the wrong number of type arguments.

Erroneous code example:

```fren
pub enum Option<T> { None, Some(T) }

comp c { in x: Option }
```

A generic type, declared with type parameters as `enum Option<T>`, is a
type only with a type argument for each parameter, as in `Option<Int>`.
Any other type, `Int` or an enumeration without type parameters, takes
none:

```fren
pub enum Option<T> { None, Some(T) }

comp c { in x: Option<Int> }
```
"# },
  { code := "F0386", explanation := r#"A variant or record of a generic type whose type arguments cannot be inferred.

Erroneous code example:

```fren
pub enum Option<T> { None, Some(T) }

comp c { pub out ok? ensure r: ok? iff Option::None = Option::None }
```

An expression never writes type arguments: they are inferred from the
instance expected where it is written, or from the values of its payload
or fields. Here neither side says which `Option` is meant. Write it where
an instance is expected, as of a variable of that type:

```fren
pub enum Option<T> { None, Some(T) }

comp c { in x: Option<Int> pub out ok? ensure r: ok? iff x = Option::None }
```
"# },
  { code := "F0387", explanation := r#"A type parameter written where it may not be.

Erroneous code example:

```fren
enum Bag<T> { Empty, Many(Set<T>) }
```

For now, a type parameter is a payload's or field's whole type, or an
argument of a generic type, as in `Option<T>`, but not an element type of
a set, relation or sequence. And a generic enumeration's payload of its own
type gives it its own type parameters, in order, as `List<T>` does within
`enum List<T> { Nil, Cons(T, List<T>) }`:

```fren
enum Bag<T> { Empty, One(T) }
```
"# },
  { code := "F0388", explanation := r#"A type parameter with the name of a type or an item.

Erroneous code example:

```fren
pub enum Mode { Off, On }

pub enum Option<Mode> { None, Some(Mode) }
```

Within its declaration, a type parameter's name must mean only the
parameter, so it cannot be the name of a built-in type, such as `Int`, or
of an item in scope. Rename it:

```fren
pub enum Mode { Off, On }

pub enum Option<T> { None, Some(T) }
```
"# },
  { code := "F0389", explanation := r#"A type argument of a recursive enumeration whose values bring a constraint.

Erroneous code example:

```fren
pub enum List<T> { Nil, Cons(T, List<T>) }

comp c { in xs: List<Int is 0..=9> }
```

A pattern type's constraint, or a constraint that a value of a record or
enumeration brings, would hold of every payload of a recursive
enumeration, at every depth, so for now a type argument of one brings none.
Give the argument no pattern, and say of the payloads that the spec reads
what it needs:

```fren
pub enum List<T> { Nil, Cons(T, List<T>) }

comp c { in xs: List<Int> }
```
"# },
  { code := "F0390", explanation := r#"An ordered struct with type parameters.

Erroneous code example:

```fren
ordered struct Pair<A, B> { fst: A, snd: B }
```

An ordered struct orders its values by their fields, so each field's type
must be ordered. A type parameter's type is not known until an instance
gives it, as `Pair<Int, Int>` does, so for now a struct with type
parameters cannot be declared `ordered`. Declare it without `ordered`, or
without type parameters:

```fren
ordered struct Pair { fst: Int, snd: Int }
```
"# },
  { code := "F0399", explanation := r#"A generic function without a body.

Erroneous code example:

```fren
fn pick<T>(a: T, b: T): T
```

SMT-LIB has no polymorphic `declare-fun`, so an uninterpreted function
cannot have type parameters, for now. A defined function may: each
application is unfolded at its type arguments, so the solver never sees a
polymorphic function. Define it:

```fren
fn pick<T>(a: T, b: T): T := a
```
"# },
  { code := "F0400", explanation := r#"A generic function's type arguments that cannot be inferred.

Erroneous code example:

```fren
pub enum Option<T> { None, Some(T) }

fn is_none?<T>(o: Option<T>) := o = Option::None

comp c { pub out ok? ensure r: ok? iff is_none?(Option::None) }
```

An application never writes type arguments: they are inferred from the
type expected where it is written, and from its arguments. Here neither
says which `Option` is meant. Give it an argument whose type is known, as
a variable's:

```fren
pub enum Option<T> { None, Some(T) }

fn is_none?<T>(o: Option<T>) := o = Option::None

comp c { in x: Option<Int> pub out ok? ensure r: ok? iff is_none?(x) }
```

A type parameter that no parameter's type nor the result's mentions could
never be inferred, and is an error where the function is declared.
"# },
  { code := "F0401", explanation := r#"An assumption mentions a variable that is not an `in`.

Erroneous code example:

```fren
comp c { in x: Int pub out y: Int assume a: y > 0 ensure r: y = x }
```

Assumptions constrain the environment: the inputs the component may be
given. Outputs, and the variables of instances, belong to the system, which
must satisfy the guarantees for every allowed input. To constrain an
output, use `ensure`.

```fren
comp c { in x: Int pub out y: Int assume a: x > 0 ensure r: y = x }
```
"# },
  { code := "F0402", explanation := r#"An instance's binding mentions an `out` of the component.

Erroneous code example:

```fren
comp sub { in a: Int pub out b: Int ensure r: b = a }
comp c { pub out o: Int inst s: sub { a := o } ensure r: o = 0 }
```

An instance's inputs are given by the component's environment: its own
inputs and the outputs of earlier instances. To relate an instance to an
output, write an `ensure`.

```fren
comp sub { in a: Int pub out b: Int ensure r: b = a }
comp c { in i: Int pub out o: Int inst s: sub { a := i } ensure r: o = s.b }
```
"# },
  { code := "F0403", explanation := r#"A private variable of an instance is mentioned.

Erroneous code example:

```fren
comp sub { in a: Int out hidden: Int ensure r: hidden = a }
comp c { in i: Int pub out o: Int inst s: sub { a := i } ensure r: o = s.hidden }
```

From outside a component, only its `in`s and `pub out`s can be mentioned.
Make the output `pub` if the component's users need it.

```fren
comp sub { in a: Int pub out shown: Int ensure r: shown = a }
comp c { in i: Int pub out o: Int inst s: sub { a := i } ensure r: o = s.shown }
```
"# },
  { code := "F0404", explanation := r#"A binding mentions an instance that is not declared before it.

Erroneous code example:

```fren
comp sub { in a: Int pub out b: Int ensure r: b = a }
comp c { in i: Int inst first: sub { a := second.b } inst second: sub { a := i } }
```

A binding may mention only instances declared before its own, so that
instances form no cycles. Reorder the instances.

```fren
comp sub { in a: Int pub out b: Int ensure r: b = a }
comp c { in i: Int inst second: sub { a := i } inst first: sub { a := second.b } }
```
"# },
  { code := "F0405", explanation := r#"An instance has no visible variable of that name.

Erroneous code example:

```fren
comp sub { in a: Int pub out b: Int ensure r: b = a }
comp c { in i: Int pub out o: Int inst s: sub { a := i } ensure r: o = s.c }
```

`w.x` names the variable `x` of the instance `w`, which must be an `in` or a
`pub out` of its component. The message lists them.

```fren
comp sub { in a: Int pub out b: Int ensure r: b = a }
comp c { in i: Int pub out o: Int inst s: sub { a := i } ensure r: o = s.b }
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
comp sub { in a: Int pub out b: Int ensure r: b = a }
comp c { inst s: sub { a := 1, b := 2 } }
```

An instance chooses its own outputs, as its component's guarantees allow;
only its inputs are bound. To constrain an output, write an `ensure` about it.

```fren
comp sub { in a: Int pub out b: Int ensure r: b = a }
comp c { pub out o: Int inst s: sub { a := 1 } ensure r: o = s.b }
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

comp c { in x: Name pub out y: Name ensure r: ok?(y) }
```

The realizability check asks for outputs that meet the guarantees. If an
output were a function's argument, that would quantify over the function's
arguments, which the solver cannot decide in general. So a function is
applied only to inputs and to the variables of instances. Apply it to the
inputs that the output depends on, and relate the output to the result:

```fren
type Name
fn ok?(Name)

comp c { in x: Name pub out y: Name pub out good? ensure r: y = x ensure g: good? iff ok?(x) }
```
"# },
  { code := "F0411", explanation := r#"Defined outputs whose definitions form a cycle.

Erroneous code example:

```fren
comp c { in x: Int out a: Int := b + x out b: Int := a pub out y: Int ensure r: y = a }
```

A defined output stands for its definition, so the checks replace it by
its definition. If a definition mentions its own output, directly or
through other definitions, the replacement never ends. Define one of them
from the inputs, or constrain it with a guarantee instead:

```fren
comp c { in x: Int out a: Int := b + x out b: Int := x pub out y: Int ensure r: y = a }
```
"# },
  { code := "F0412", explanation := r#"A refinement whose components do not share the abstract one's interface.

Erroneous code example:

```fren
comp precise { in x: Int pub out y: Int ensure r: y = x }
comp rough { in x: Int pub out z: Int ensure r: z >= x }
refine fits: precise refines rough
```

`refine r: c refines a` relates `c` and `a` through `a`'s variables: each
input of `a` must be an input of `c`, and each output of `a` a public
output of `c`, with the same name and type (see `Reqs/Lang/Refinement`).
`precise` has no output `z`. Name the outputs alike:

```fren
comp precise { in x: Int pub out y: Int ensure r: y = x }
comp rough { in x: Int pub out y: Int ensure r: y >= x }
refine fits: precise refines rough
```
"# },
  { code := "F0413", explanation := r#"A refinement binds a name that is not a variable of the refined component.

Erroneous code example:

```fren
comp precise { in x: Int pub out y: Int ensure r: y = x }
comp rough { in x: Int pub out z: Int ensure r: z >= x }
refine fits: precise refines rough { w := y }
```

A refinement's bindings give variables of the refined component, the one
after `refines`, as expressions over the refining one's (see
`Reqs/Lang/Refinement`). `rough` has no variable `w`. The message lists
its variables; correct the name:

```fren
comp precise { in x: Int pub out y: Int ensure r: y = x }
comp rough { in x: Int pub out z: Int ensure r: z >= x }
refine fits: precise refines rough { z := y }
```
"# },
  { code := "F0414", explanation := r#"A refinement binds a variable of the refined component more than once.

Erroneous code example:

```fren
comp precise { in x: Int pub out y: Int ensure r: y = x }
comp rough { in x: Int pub out z: Int ensure r: z >= x }
refine fits: precise refines rough { z := y, z := y + 1 }
```

Each variable of the refined component is read as one expression, so a
refinement binds it at most once. Keep one binding:

```fren
comp precise { in x: Int pub out y: Int ensure r: y = x }
comp rough { in x: Int pub out z: Int ensure r: z >= x }
refine fits: precise refines rough { z := y }
```
"# },
  { code := "F0415", explanation := r#"A refinement's binding mentions a variable of the refining component that it cannot see.

Erroneous code example:

```fren
comp precise { in x: Int pub out y: Int ensure r: y = x }
comp rough { in n: Int pub out y: Int ensure r: y >= n }
refine fits: precise refines rough { n := y }
```

A binding sees the refining component from outside: its inputs and public
outputs, and no private output. A binding of an input of the refined
component sees only inputs, since the environment chooses the inputs
before the component chooses its outputs (see `Reqs/Lang/Refinement`).
Bind the input to an input:

```fren
comp precise { in x: Int pub out y: Int ensure r: y = x }
comp rough { in n: Int pub out y: Int ensure r: y >= n }
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
comp c { in x? pub out y? ensure r: y? iff x? }
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
  { code := "F0601", explanation := r#"A component is not realizable: for some input, no outputs satisfy its guarantees.

Erroneous code example:

```fren
comp c {
  in x: Int
  pub out y: Int
  ensure big: y > x
  ensure small: y < 0
}
```

A component must be implementable: for every input that its assumptions
allow, some outputs satisfy all of its guarantees. The message gives an
input for which none do, one variable to a line, and the guarantees that
conflict on it. Here, when `x` is `0`, no `y` is both above `0` and below
`0`.

Each guarantee of the conflict has a note. Where it forces an output to
one value, and the rest of the conflict forces it to another, the note
says so, such as "`low` forces y = 0, but `high` forces y = 1". `fren
check --examples N` gives at most `N` such notes for each component
(default 1), or all of them with `all`. The other guarantees' notes say
whom they conflict with. Here neither guarantee forces `y`, so the notes
are "conflicts with `small`" and "conflicts with `big`".

Weaken one of the guarantees, or, if such inputs cannot happen, add an
assumption that rules them out:

```fren
comp c {
  in x: Int
  pub out y: Int
  assume negative: x < -1
  ensure big: y > x
  ensure small: y < 0
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
  ensure r: y? iff x > 7
}
```

If no input satisfies the assumptions, every guarantee holds vacuously,
and the component says nothing. The message names a smallest set of
assumptions that contradict each other. Weaken or remove one of them.

```fren
comp c {
  in x: Int
  pub out y?
  assume big: x > 10
  ensure r: y? iff x > 7
}
```
"# },
  { code := "F0603", explanation := r#"An expectation does not follow from the guarantees.

Erroneous code example:

```fren
comp c {
  in x: Int
  pub out y: Int
  ensure r: y >= x
  expect positive: y > 0
}
```

An `expect` states a consequence of the assumptions, instances and
guarantees, and is checked rather than required. The counterexample shows
inputs and public outputs that satisfy everything else but not the
expectation. Here, `x = 0, y = 0`.

Strengthen the guarantees so that it follows, or correct the expectation:

```fren
comp c {
  in x: Int
  pub out y: Int
  assume nonneg: x >= 0
  ensure r: y > x
  expect positive: y > 0
}
```
"# },
  { code := "F0604", explanation := r#"An instance may be given inputs that its component's assumptions rule out.

Erroneous code example:

```fren
comp sub { in n: Int pub out m: Int assume nonneg: n >= 0 ensure r: m = n }
comp c { in i: Int pub out o: Int inst s: sub { n := i } ensure r: o = s.m }
```

A component's assumptions are obligations for whoever instantiates it: they
must follow from the instantiating component's assumptions, the instance's
bindings and earlier instances. The counterexample shows inputs for which
they may not.

```fren
comp sub { in n: Int pub out m: Int assume nonneg: n >= 0 ensure r: m = n }
comp c { in i: Int pub out o: Int assume nonneg: i >= 0 inst s: sub { n := i } ensure r: o = s.m }
```
"# },
  { code := "F0605", explanation := r#"The condition of a `when` or `unless` can never hold.

Erroneous code example:

```fren
comp c {
  in x: Int
  pub out y: Int
  assume pos: x > 0
  ensure r: y = x
  ensure never: when x < 0, y = 0
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
  ensure r: when x > 5, y = x
  ensure small: when x <= 5, y = 0
}
```
"# },
  { code := "F0606", explanation := r#"A constraint follows from the others (a warning).

Erroneous code example:

```fren
comp c {
  in x: Int
  pub out y: Int
  ensure y_def: y = x + 1
  ensure bigger: y > x
}
```

A guarantee that follows from the assumptions, instances and other
guarantees adds nothing, and an assumption that follows from the other
assumptions likewise. If it is meant as a consequence, make it an `expect`,
so that it is checked rather than assumed:

```fren
comp c {
  in x: Int
  pub out y: Int
  ensure y_def: y = x + 1
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
  ensure above: y >= x
  ensure below: y <= x + 1
}
```

A `det out` must have exactly one value for each input that the
assumptions allow. The message gives an input and two values the output
could take. Add guarantees that pin it down, or remove `det`.

```fren
comp c {
  in x: Int
  pub det out y: Int
  ensure exact: y = x + 1
}
```
"# },
  { code := "F0608", args := none, explanation := r#"A check could not be decided (a warning).

The solver neither proved nor refuted the check's query within the time
limit or the resource limit, or gave up, so the check neither passed nor
failed. The message says which check, and why the solver stopped,
such as `RESOURCEOUT` for the resource limit.

Raise the time limit with `fren check --timeout SECONDS` (the default is 10),
or the resource limit with `--resource-limit N` (by default there is none),
or simplify the constraints involved: large constants and many `if`s make
queries harder.
"# },
  { code := "F0609", args := some ["quickcheck"], explanation := r#"Testing found no outputs for an input (a warning).

Erroneous code example:

```fren
comp c {
  in x: Int
  pub out y: Int
  ensure above: y > x
  ensure below: y < x
}
```

`fren quickcheck` chose an input that the assumptions allow, and behaviours
of the instances, but its search found no outputs that satisfy the
guarantees. The search tries only some values, so outputs may still
exist: run `fren check`, whose realizability check decides it. Here no `y`
is both above and below `x`, so `fren check` reports `F0601`. Weaken one
of the guarantees:

```fren
comp c {
  in x: Int
  pub out y: Int
  ensure above: y > x
}
```
"# },
  { code := "F0611", explanation := r#"An index may be out of range where it is evaluated.

Erroneous code example:

```fren
comp first {
    in q: Seq<Int>
    pub out x: Int

    ensure r: x = q[0]
}
```

Out of range, `q[i]` is an unknown value, so the checks hold whatever it
is, but the constraint then says nothing useful: here, `x` is unconstrained
when `q` is empty. Fren asks whether `0 <= i < q.len` follows from the
conditions under which the index is evaluated, its guard, read from left
to right through `when`, `if`, `and`, `or` and `match`. Guard the index:

```fren
comp first {
    in q: Seq<Int>
    pub out x: Int

    ensure r: when q != [], x = q[0]
}
```
"# },
  { code := "F0618", explanation := r#"A table may have no row that holds where it is evaluated.

Erroneous code example:

```fren
comp sign {
    in x: Int
    pub out s: Int

    ensure r: s = table { x > 0 => 1, x < 0 => -1 }
}
```

A table without a `_` row has no specified value where none of its rows
holds, so the checks hold whatever it is there, and the constraint says
nothing useful: here, `s` is unconstrained when `x` is `0`. Fren asks
whether some row's condition follows from the conditions under which the
table is evaluated, its guard, and the hypotheses of where it is written.
Add a row for the case, or end the table with `_ => e`:

```fren
comp sign {
    in x: Int
    pub out s: Int

    ensure r: s = table { x > 0 => 1, x < 0 => -1, x = 0 => 0 }
}
```
"# },
  { code := "F0619", explanation := r#"Two rows of a table may both hold where it is evaluated.

Erroneous code example:

```fren
comp grade {
    in score: Int
    pub out pass?

    ensure r: pass? iff table { score >= 50 => true, score >= 0 => false, _ => false }
}
```

A table has the value of its first row that holds, so where two rows hold
at once, their order decides the value, which is easy to misread: here,
both of the first two rows hold when `score` is `50`. Fren asks whether the
two conditions can hold together, under the table's guard and the
hypotheses of where it is written. Make the conditions exclusive:

```fren
comp grade {
    in score: Int
    pub out pass?

    ensure r: pass? iff table { score >= 50 => true, 0 <= score < 50 => false, _ => false }
}
```
"# },
  { code := "F0629", explanation := r#"An application of a function may not meet one of the function's preconditions.

Erroneous code example:

```fren
fn nth(q: Seq<Int>, i: Int): Int := q[i]
    assume in_range: 0 <= i < q.len

comp c { in q: Seq<Int> pub out y: Int ensure r: y = nth(q, 0) }
```

A function's preconditions say what its arguments must meet. At each
application, Fren asks whether each holds, given the conditions under
which the application is evaluated and the hypotheses of where it is
written: here, `q` may be empty. Where a precondition fails, the
application's value is not what the function is for, so the constraint
says nothing useful there. Guard the application, or assume what the
precondition needs:

```fren
fn nth(q: Seq<Int>, i: Int): Int := q[i]
    assume in_range: 0 <= i < q.len

comp c {
    in q: Seq<Int>
    pub out y: Int

    ensure r: when q != [], y = nth(q, 0)
    ensure e: when q = [], y = 0
}
```
"# },
  { code := "F0630", explanation := r#"A defined function's postcondition does not hold.

Erroneous code example:

```fren
fn pred(n: Int): Int := n - 1
    assume positive: n > 0
    ensure positive_result: pred(n) > 0
```

A defined function's postconditions are claims about its body, which Fren
checks for every value of the parameters that meets its preconditions:
here, `pred(1)` is 0. Correct the body or the postcondition, or add a
precondition that rules the case out:

```fren
fn pred(n: Int): Int := n - 1
    assume positive: n > 0
    ensure natural: pred(n) >= 0
```
"# },
  { code := "F0631", explanation := r#"An uninterpreted function's postconditions cannot all hold.

Erroneous code example:

```fren
fn rate(n: Int): Int
    ensure positive: rate(n) > 0
    ensure negative: rate(n) < 0
```

An uninterpreted function's postconditions are what is known of it, and
are assumed wherever it is applied. If for some arguments that meet its
preconditions no value meets them all, they contradict each other, and
every check that applies the function would pass. The same goes for a
postcondition that says nothing of the function's value and can be false.
Weaken one of them, or add a precondition that rules those arguments out:

```fren
fn rate(n: Int): Int
    ensure positive: rate(n) > 0
```
"# },
  { code := "F0632", explanation := r#"An uninterpreted function's preconditions contradict each other.

Erroneous code example:

```fren
fn rate(n: Int): Int
    assume positive: n > 0
    assume negative: n < 0
    ensure bounded: rate(n) < n
```

No arguments meet the preconditions, so the postconditions say nothing,
and no application of the function can meet its preconditions. Weaken or
remove one of them:

```fren
fn rate(n: Int): Int
    assume positive: n > 0
    ensure bounded: rate(n) < n
```
"# },
  { code := "F0625", explanation := r#"A `match` may have no arm that is taken where it is evaluated.

Erroneous code example:

```fren
comp sign {
    in x: Int
    pub out s: Int

    ensure r: s = match x { n if n > 0 => 1, n if n < 0 => -1 }
}
```

An arm with a guard is taken only where its guard holds, so a `match`
whose arms without guards do not cover every value may have no arm that is
taken. There it has no specified value, so the checks hold whatever it is,
and the constraint says nothing useful: here, `s` is unconstrained when
`x` is `0`. The static rules ignore guards, so Fren asks whether some arm's
pattern and guard follow from the conditions under which the `match` is
evaluated, and the hypotheses of where it is written. Add an arm for the
case, or end the `match` with an arm without a guard:

```fren
comp sign {
    in x: Int
    pub out s: Int

    ensure r: s = match x { n if n > 0 => 1, n if n < 0 => -1, _ => 0 }
}
```
"# },
  { code := "F0626", explanation := r#"An arm of a `match` is never taken.

Erroneous code example:

```fren
comp size {
    in x: Int
    pub out s: Int

    ensure r: s = match x { n if n > 10 => 2, n if n > 20 => 3, _ => 1 }
}
```

An arm is taken where its pattern matches, its guard holds and no earlier
arm is taken. Fren asks whether that can happen, under the conditions
under which the `match` is evaluated and the hypotheses of where it is
written, but the constraint that it is in, for each arm that has a guard
or follows one. Here, every `x`
above 20 is above 10, so the first arm takes it, and the second arm is
never taken. Correct the guards, or the order of the arms:

```fren
comp size {
    in x: Int
    pub out s: Int

    ensure r: s = match x { n if n > 20 => 3, n if n > 10 => 2, _ => 1 }
}
```
"# },
  { code := "F0627", explanation := r#"A row of a table is never the first that holds.

Erroneous code example:

```fren
comp size {
    in x: Int
    pub out s: Int

    ensure r: s = table { x >= 0 => 1, x < 0 => 0, _ => 2 }
}
```

A table has the value of its first row that holds, and a row `_` holds
wherever no earlier one does. Fren asks, for each row, whether it can be
the first that holds, under the conditions under which the table is
evaluated and the hypotheses of where it is written, but the constraint
that it is in. Here, one of the
first two rows always holds, so the `_` row never gives the table's
value. Remove the row, or correct the conditions before it:

```fren
comp size {
    in x: Int
    pub out s: Int

    ensure r: s = table { x >= 0 => 1, x < 0 => 0 }
}
```
"# },
  { code := "F0636", explanation := r#"Two arms of a table over a scrutinee may both be taken.

Erroneous code example:

```fren
enum Mode { Off, On(Int) }

comp level {
    in m: Mode
    pub out y: Int

    ensure r: y = table m { Mode::Off => 0, Mode::On(x) if x >= 0 => x, Mode::On(x) if x <= 0 => 1 }
}
```

The arms of a table over a scrutinee are disjoint, so that its value
does not depend on their order: no two of them are taken at one value of
the scrutinee.
Two arms without guards whose patterns overlap are a static error
(`F0391`); for two whose patterns overlap where one has a guard, Fren asks
whether both can be taken at once, under the conditions under which the
table is evaluated and the hypotheses of where it is written, but the
constraint that it is in. Here, both guards hold when `x` is 0. Make the
guards exclusive:

```fren
enum Mode { Off, On(Int) }

comp level {
    in m: Mode
    pub out y: Int

    ensure r: y = table m { Mode::Off => 0, Mode::On(x) if x > 0 => x, Mode::On(x) if x <= 0 => 1 }
}
```
"# },
  { code := "F0637", explanation := r#"A table over a scrutinee may have no arm that is taken where it is evaluated.

Erroneous code example:

```fren
comp sign {
    in n: Int
    pub out s: Int

    ensure r: s = table n { k if k > 0 => 1, k if k < 0 => -1 }
}
```

Its arms without guards are not exhaustive, so Fren asks whether some arm
is always taken, as for a `match` (`F0625`). Where none is, the table is an
unknown value, so the constraint says nothing useful there. Here, no arm
is taken when `n` is 0. Add an arm for it, or end the table with `_ => e`:

```fren
comp sign {
    in n: Int
    pub out s: Int

    ensure r: s = table n { k if k > 0 => 1, k if k < 0 => -1, _ => 0 }
}
```
"# },
  { code := "F0638", explanation := r#"An arm of a table over a scrutinee is never taken.

Erroneous code example:

```fren
comp size {
    in x: Int
    pub out s: Int

    assume small: x < 5

    ensure r: s = table x { n if n > 10 => 2, _ => 1 }
}
```

Fren asks of each arm that has a guard or follows one whether it can be
taken, as for a `match` (`F0626`), under the conditions under which the
table is evaluated and the hypotheses of where it is written, but the
constraint that it is in. Here, `x` is below 5, so the first arm is dead.
Correct its guard, or remove it:

```fren
comp size {
    in x: Int
    pub out s: Int

    assume small: x < 5

    ensure r: s = table x { n if n > 3 => 2, _ => 1 }
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
  ensure r: pos? iff x > 0
}
```

None of `fren quickcheck`'s tests found an input that the assumptions
allow, with behaviours of the instances and outputs that meet the
component, so none of the component's checks were tested. Either the
assumptions or guarantees cannot hold, as here, where `fren check`
reports `F0602`, or the search missed the values that satisfy them: then
raise `--tests`, or rely on `fren check`.

```fren
comp c {
  in x: Int
  pub out pos?
  assume small: x > -10 and x < 10
  ensure r: pos? iff x > 0
}
```
"# },
  { code := "F0612", args := some ["quickcheck"], explanation := r#"Testing never reached a check: its trigger held in no test (a warning).

Erroneous code example:

```fren
comp c {
  in x: Int
  pub out big?
  ensure r: big? iff x > 1000
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
  ensure r: big? iff x > 1000
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
  ensure r: pos? iff x > 0
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
  ensure r: pos? iff x > 0
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
  in xs: Seq<Int>
  pub out big?
  ensure r: big? iff xs.len > 4
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
  { code := "F0615", explanation := r#"A cover goal cannot be met: no behaviour that meets the component satisfies it.

Erroneous code example:

```fren
comp heater {
  in temp: Int
  pub out alarm?
  ensure r: alarm? iff temp > 100
  cover silent_overheat: temp > 100 and not alarm?
}
```

A cover goal states a scenario that the component must allow. Here `r`
sounds the alarm whenever `temp > 100`, so no behaviour has a high
temperature and a silent alarm, and the goal fails, naming the
constraints that rule it out. Either the guarantees are too strong,
and should be weakened so that the scenario is possible, or the goal is
wrong:

```fren
comp heater {
  in temp: Int
  pub out alarm?
  ensure r: alarm? iff temp > 100
  cover overheat: temp > 100 and alarm?
}
```
"# },
  { code := "F0616", args := some ["quickcheck"], explanation := r#"Testing found no behaviour in which a cover goal holds (a warning).

Erroneous code example:

```fren
comp c {
  in x: Int
  pub out big?
  ensure r: big? iff x > 1000
  cover exact: 7 * x = 123459 and big?
}
```

`fren quickcheck` found behaviours of the component, but in none of them
did the goal hold: only `x = 17637` satisfies it, and the search does not
try that value. A behaviour found would be a witness, and pass the goal,
but none found shows nothing, so its result is inconclusive. Raise
`--tests`, rely on `fren check`, which asks the solver, or widen the
goal:

```fren
comp c {
  in x: Int
  pub out big?
  ensure r: big? iff x > 1000
  cover large: x > 2000 and big?
}
```
"# },
  { code := "F0622", explanation := r#"A value given where a pattern type is declared may not match its pattern.

Erroneous code example:

```fren
type Byte := Int is 0..=255

comp c {
    in x: Int
    pub det out b: Byte := x
}
```

Where a pattern type `T is P` is declared, as the type of a defined output,
an argument, a field, a payload, a `let` definition, a function's result or
a constant, a value of `T` is accepted with the obligation that it matches
`P`, which the solver checks where the value is written, under the same
hypotheses as an index's definedness. The counterexample is a behaviour in
which the value does not match. Guard the value so that it matches, or add
an assumption that ensures it:

```fren
type Byte := Int is 0..=255

comp c {
    in x: Int
    pub det out b: Byte := if 0 <= x <= 255 then x else 0
}
```
"# },
  { code := "F0623", explanation := r#"An instance binds an input of a pattern type to a value that may not match its pattern.

Erroneous code example:

```fren
type Byte := Int is 0..=255

comp sub { in b: Byte pub out y: Int ensure r: y = b }

comp c {
    in x: Int
    inst w: sub { b := x }
}
```

An input of a pattern type is an assumption of its component, so an
instance's binding of it is checked, as the component's other assumptions
are. The counterexample is a behaviour in which the bound value does not
match. Bind the input to a value of its type, or add an assumption that
guarantees it:

```fren
type Byte := Int is 0..=255

comp sub { in b: Byte pub out y: Int ensure r: y = b }

comp c {
    in x: Byte
    inst w: sub { b := x }
}
```
"# },
  { code := "F0639", args := some ["quickcheck"], explanation := r#"A quantifier that testing cannot evaluate.

Erroneous code example:

```fren
set_option fren.lint.undecidable "allow" in
comp c {
  in s: Set<Int>
  pub out pos?
  ensure r: pos? iff (forall (x: Int), not (x in s) or x > 0)
}
```

Testing evaluates an unbounded quantifier, over a type whose values cannot
be listed, by enumerating each bound name's domain, which its guard gives:
the members of `s` in `x in s`, or the integers between the bounds of
`0 <= i < n`. The guard of a `forall` is the conditions of the `when`s at
the top of its body, and that of an `exists` the conjuncts of its body.
Here the bound name has no domain, so neither `fren quickcheck` nor `fren
check`, for a check set to be tested, can evaluate the quantifier. Guard
it, or leave the check to the solver:

```fren
set_option fren.lint.undecidable "allow" in
comp c {
  in s: Set<Int>
  pub out pos?
  ensure r: pos? iff (forall (x: Int), when x in s, x > 0)
}
```
"# },
  { code := "F0644", explanation := r#"A component with too many behaviours to enumerate.

Erroneous code example:

```fren
set_option fren.evidence "enumerated" in
comp c {
  in a: Int is 0..=99
  in b: Int is 0..=99
  in d: Int is 0..=99
  pub det out sum: Int := a + b + d
  expect e: sum >= 0
}
```

Enumeration searches every assignment of the component's variables up to
the size bound, smallest first (see `Reqs/Check`, "Checking by
enumeration"). The number of assignments is the product of each
variable's number of values, and of a second copy's where determinism is
enumerated; here a million. Above 65,536 none of the component's checks set
to enumeration is run. Narrow the types, lower `fren.enumeration.size`, or
have the solver check it:

```fren
comp c {
  in a: Int is 0..=99
  in b: Int is 0..=99
  in d: Int is 0..=99
  pub det out sum: Int := a + b + d
  expect e: sum >= 0
}
```
"# },
  { code := "F0645", explanation := r#"A component that cannot be enumerated.

Erroneous code example:

```fren
set_option fren.evidence "enumerated" in
comp c { in name: String pub out empty? ensure r: empty? iff name = "" }
```

Enumeration needs each variable's type to be enumerable: `Bool`, `Int`,
`Nat`, enumerations, records, newtypes, instances of generic types, pattern
types and abstract types, with what is within them enumerable too (see
`Reqs/Check`, "Checking by enumeration"). Strings, sets, relations and
sequences are not yet, nor can enumeration apply an uninterpreted function
with a contract, whose postconditions constrain its interpretations, or
evaluate an unbounded quantifier. None of the component's checks set to
enumeration is run. Have the solver or testing check it:

```fren
set_option fren.evidence "tested" in
comp c { in name: String pub out empty? ensure r: empty? iff name = "" }
```
"# },
  { code := "F0646", explanation := r#"Checks that hold for every behaviour up to the size bound.

Example:

```fren
set_option fren.evidence "enumerated" in
comp c { in x: Int pub det out y: Int := x + 1 expect e: y > x }
```

A check set to `"enumerated"` searches every behaviour up to the size
bound, `fren.enumeration.size` (see `Reqs/Check`, "Checking by
enumeration"). Where every variable has finitely many values, each within
the bound, that is every behaviour, and the check is decided. Here `x` is
an `Int`, so the expectation is only known to hold for `x` between -3
and 3: weaker than a proof, so it is reported, as information. With
`"enumerated+tested"`, random tests also look beyond the bound. A type of
finitely many values decides it:

```fren
set_option fren.evidence "enumerated" in
comp c { in x: Int is -3..=3 pub det out y: Int := x + 1 expect e: y > x }
```
"# },
  { code := "F0701", explanation := r#"An import that nothing uses (the lint `unused_imports`, a warning by default).

Erroneous code example:

```fren
mod climate
pub enum Mode { Off, Heat }
use self::Mode::Heat
comp c { in m: Mode pub out off? ensure r: off? iff m = Mode::Off }
```

No path in the file resolves through the `use`, so it can be removed, as
`fren fix` does. Only paths in the same file count. Imports of the same enumeration's
variants by `*` count once, so a repeated `use E::*` is unused too.

```fren
mod climate
pub enum Mode { Off, Heat }
use self::Mode::Off
comp c { in m: Mode pub out off? ensure r: off? iff m = Off }
```

To keep the `use`, allow the lint for it:
`set_option fren.lint.unused_imports "allow" in use ...`.
"# },
  { code := "F0702", explanation := r#"A `use ...::*` (the lint `glob_imports`, a warning by default).

Erroneous code example:

```fren
pub enum Mode { Off, Heat }
use Mode::*
comp c { in m: Mode pub out off? ensure r: off? iff m = Off }
```

`use E::*` brings every variant of `E` into scope, including variants added
later, so a reader cannot tell where a name comes from, and a new variant
can make a name in another module ambiguous. Import the variants by name,
as `fren fix` does, or write them qualified:

```fren
pub enum Mode { Off, Heat }
use Mode::{Off}
comp c { in m: Mode pub out off? ensure r: off? iff m = Off }
```

```fren
pub enum Mode { Off, Heat }
comp c { in m: Mode pub out off? ensure r: off? iff m = Mode::Off }
```
"# },
  { code := "F0703", explanation := r#"A name that should be in `snake_case` (the lint `non_snake_case`, a warning by default).

Erroneous code example:

```fren
comp TempSensor { in t: Int pub out hot? ensure r: hot? iff t > 30 }
```

Modules, components, variables, instances, constraints and global
expectations are named in `snake_case`: no uppercase letters. A
variable's final `?` does not count.

```fren
comp temp_sensor { in t: Int pub out hot? ensure r: hot? iff t > 30 }
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
comp c { in x: Int pub out y: Int ensure r: y = x }
```

`set_option fren.lint.LINT "expect"` says that the lint fires where the
setting is in effect, and silences it there. Here, nothing after the
setting is a glob import. Remove the setting, as `fren fix` does, or move
it to where the lint fires:

```fren
comp c { in x: Int pub out y: Int ensure r: y = x }
```
"# },
  { code := "F0707", explanation := r#"A `set_option` names a lint that does not exist.

Erroneous code example:

```fren
set_option fren.lint.unused_import "allow"
```

A lint option names a lint or a group of lints, such as `pedantic`. The
message lists them all.

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
project can rule a lint out everywhere. Neither can the level of its group,
which would change the lint's. Remove the later setting:

```fren
set_option fren.lint.glob_imports "forbid"
```
"# },
  { code := "F0710", explanation := r#"A variable or binder that nothing mentions (the lint `unused_variables`, a warning by default).

Erroneous code example:

```fren
comp c { in x: Int in spare: Int pub out y: Int ensure r: y = x }
```

No constraint of `c` mentions `spare`, so it does not affect `c`. An
output that nothing mentions can take any value. A binder of a global
expectation that its body never mentions is reported too, and so are a
name of a `let` or `where` that neither its body nor a later definition
mentions, and a quantifier's bound name that its body never mentions.
Remove the variable, or mention it:

```fren
comp c { in x: Int pub out y: Int ensure r: y = x }
```
"# },
  { code := "F0711", explanation := r#"A private enumeration or constant that nothing in its file uses (the lint `dead_code`, a warning by default).

Erroneous code example:

```fren
const LIMIT: Int := 10
comp c { in x: Int pub out y: Int ensure r: y = x }
```

No path in the file resolves to `LIMIT`, and it is private, so no other
module can use it. Only uses in the same file count, and uses in Lean
code do not. Remove it, use it, or make it `pub`:

```fren
const LIMIT: Int := 10
comp c { in x: Int pub out y: Int ensure r: y = x + LIMIT }
```

Components and global expectations are never dead: each is a guarantee
in its own right.
"# },
  { code := "F0712", explanation := r#"A `Bool` expression with a simpler form (the lint `nonminimal_bool`, a warning by default).

Erroneous code example:

```fren
comp c { in a? pub out b? ensure r: b? iff a? = true }
```

`a? = true` means `a?`. Likewise, `a? = false` means `not a?`, `not not
a?` means `a?`, `not (x < y)` means `x >= y`, `if c? then true else false`
means `c?`, `if c? then a? else false` means `c? and a?`, and `when true,
a?` means `a?`. Write the
simpler form, as `fren fix` does:

```fren
comp c { in a? pub out b? ensure r: b? iff a? }
```
"# },
  { code := "F0713", explanation := r#"A removed code: the lint `shadowed_constants`.

`F0713` was the lint `shadowed_constants`, which warned of a variable named
like a constant in scope. Shadowing is now explicit: a declaration that
hides a name in scope without `!` is the error `F0217`, and one written
with `!` that hides nothing is `F0218`. Nothing reports `F0713`, and the
code is not reused.
"#, args := none },
  { code := "F0714", explanation := r#"A construct outside the decidable core (the lint `undecidable`, an error by default).

Erroneous code example:

```fren
comp c { in a: String in b: String pub out p? ensure r: p? iff a.starts_with?(b) }
```

Unless a spec opts out, every check is decidable: each query is in a
fragment of the solver's theories that has a decision procedure. For
strings, that is regular constraints with length. A method's argument is a
constant, strings are compared with constants or as whole variables, `++`
is the receiver of a method or compared with a constant, and no string
operation but `=` and `!=` mentions an output of an infinite type. A
construct outside it may make the solver give up. Stay in the core:

```fren
comp c { in a: String pub out p? ensure r: p? iff a.starts_with?("x") }
```

or opt out explicitly, accepting that a check may be inconclusive:

```fren
set_option fren.lint.undecidable "allow" in
comp c { in a: String in b: String pub out p? ensure r: p? iff a.starts_with?(b) }
```
"# },
{ code := "F0715", explanation := r#"A string's or sequence's length is compared with 0 (a warning, `length_zero`).

Example:

```fren
comp c { in s: String pub out p? ensure r: p? iff s.len = 0 }
```

That a string or sequence is empty says it more plainly: `s = ""`, or
`q = []`, for `s.len = 0`, `s.len <= 0` and `s.len < 1`, and `s != ""` for
`s.len != 0`, `s.len > 0` and `s.len >= 1`, with the length on either side.
`fren fix` can fix this:

```fren
comp c { in s: String pub out p? ensure r: p? iff s = "" }
```
"# },
  { code := "F0716", explanation := r#"A set's or relation's `card` is compared with 0 (a warning, `card_zero`).

Example:

```fren
comp c { in s: Set<Int> pub out p? ensure r: p? iff s.card > 0 }
```

That a set is empty says it more plainly: `s = {}`, or `s != {}` for
`s.card > 0`, and so on, as for `len` (F0715). `fren fix` can fix this:

```fren
comp c { in s: Set<Int> pub out p? ensure r: p? iff s != {} }
```
"# },
  { code := "F0717", explanation := r#"Membership in a set of one member (a warning, `singleton_membership`).

Example:

```fren
comp c { in x: Int pub out p? ensure r: p? iff x in {1} }
```

`x in {a}` is `x = a`. `fren fix` can fix this:

```fren
comp c { in x: Int pub out p? ensure r: p? iff x = 1 }
```
"# },
  { code := "F0718", explanation := r#"A chain of `or` that equates one expression with three or more others, or of `and` that disequates it (`membership_chain`, allowed by default).

Example:

```fren
set_option fren.lint.membership_chain "warn"

comp c { in x: Int in y: Int pub out p? ensure r: p? iff (x = 1 or x = 2 or x = y) }
```

The chain is a membership in a set literal, and `x != 1 and x != 2 and x
!= y` is `not x in {1, 2, y}`. `fren fix` can fix this:

```fren
comp c { in x: Int in y: Int pub out p? ensure r: p? iff x in {1, 2, y} }
```

Where every value is one that a pattern writes, a literal or a variant
without a payload, the chain is a pattern test written out, which
`manual_pattern_test` (`F0805`) reports instead: `x = 1 or x = 2 or x = 3`
is `x is 1 | 2 | 3`.
"# },
  { code := "F0719", explanation := r#"A defined output whose definition mentions no variable (a warning, `constant_output`).

Example:

```fren
comp c { in x: Int pub out limit: Int := 10 ensure r: x < limit }
```

The output is the same in every behaviour, so it is a constant, which every
component can share:

```fren
const LIMIT: Int := 10

comp c { in x: Int pub out p? ensure r: p? iff x < LIMIT }
```
"# },
  { code := "F0720", explanation := r#"An output that one guarantee equates with other variables (`definable_output`, allowed by default).

Example:

```fren
set_option fren.lint.definable_output "warn"

comp c { in x: Int pub out y: Int ensure r: y = x + 1 }
```

The guarantee could be the output's definition, which realizability
then never searches for:

```fren
comp c { in x: Int pub out y: Int := x + 1 }
```
"# },
  { code := "F0721", explanation := r#"An index on the left of an `and` whose right operand bounds the sequence (a warning, `index_after_use`).

Example:

```fren
comp c { in q: Seq<Int> pub out p? ensure r: p? iff (q[0] = 1 and q.len > 0) }
```

In `a and b`, `b` is guarded by `a`, so the index is evaluated whether or
not the bound holds, and the definedness check fails. Swapping the operands
does not change the meaning. `fren fix` can fix this:

```fren
comp c { in q: Seq<Int> pub out p? ensure r: p? iff (q.len > 0 and q[0] = 1) }
```
"# },
  { code := "F0722", explanation := r#"An `unless` whose condition is a negation (a warning, `unless_not`).

Example:

```fren
comp c { in a? in b? pub out p? ensure r: unless not a?, p? iff b? }
```

`unless not A, D` is `when A, D`, and `unless a != b, D` is `when a = b,
D`. `fren fix` can fix this:

```fren
comp c { in a? in b? pub out p? ensure r: when a?, p? iff b? }
```
"# },
  { code := "F0723", explanation := r#"A `when` whose body is a `when`, or an `unless` whose body is an `unless` (a warning, `collapsible_when`).

Example:

```fren
comp c { in a? in b? pub out p? ensure r: when a?, when b?, p? }
```

`when A, when B, D` is `when A and B, D`, and `unless A, unless B, D` is
`unless A or B, D`. `fren fix` can fix this:

```fren
comp c { in a? in b? pub out p? ensure r: when a? and b?, p? }
```

A nest of `when` and `unless`, such as `unless A, when B, D`, is not
reported.
"# },
  { code := "F0724", explanation := r#"An `if` whose condition is a negation (`if_not_else`, allowed by default).

Example:

```fren
set_option fren.lint.if_not_else "warn"

comp c { in a? in x: Int pub out y: Int ensure r: y = if not a? then x else 0 }
```

`if not C then A else B` is `if C then B else A`, and `if a != b then A
else B` is `if a = b then B else A`. `fren fix` can fix this:

```fren
comp c { in a? in x: Int pub out y: Int ensure r: y = if a? then 0 else x }
```

An `if` whose `else` branch is an `if` is not reported, since swapping its
branches would break the chain of `else if`.
"# },
  { code := "F0725", explanation := r#"Two arms of a `match` with the same body (`match_same_arms`, allowed by default).

Example:

```fren
set_option fren.lint.match_same_arms "warn"

enum E { A, B, C }

comp c { in e: E pub out n: Int ensure r: n = match e { E::A => 1, E::B => 2, E::C => 1 } }
```

Arms whose patterns bind no names, and whose bodies are written the same,
are one arm with an or-pattern. An arm with the body of the `_` arm can be
removed, and a `match` whose arms all have one body is that body. `fren
fix` can fix this:

```fren
set_option fren.lint.match_same_arms "warn"

enum E { A, B, C }

comp c { in e: E pub out n: Int ensure r: n = match e { E::A | E::C => 1, E::B => 2 } }
```
"# },
  { code := "F0726", explanation := r#"A `match` whose arms are all `true` or `false` (a warning, `match_like_membership`).

Example:

```fren
enum E { A, B, C }

comp c { in e: E pub out p? ensure r: p? iff match e { E::A => true, E::B => true, E::C => false } }
```

The `match` says whether its scrutinee is one of the variants whose arms
are `true`, which a pattern test says directly. `fren fix` can fix this:

```fren
enum E { A, B, C }

comp c { in e: E pub out p? ensure r: p? iff e is E::A | E::B }
```

Where most variants are `true`, or the `_` arm is, the fix is a negated
test of those that are `false`, such as `e != E::C`, an equation for one
variant.
"# },
  { code := "F0728", explanation := r#"A `_` arm that matches only one variant (`wildcard_single_variant`, allowed by default).

Example:

```fren
set_option fren.lint.wildcard_single_variant "warn"

enum E { A, B, C }

comp c { in e: E pub out n: Int ensure r: n = match e { E::A => 1, E::B => 2, _ => 3 } }
```

A variant added to `E` later would be matched by `_` without notice. Named,
it makes the `match` non-exhaustive, a static error, so that the new
variant gets an arm of its own. `fren fix` can fix this:

```fren
set_option fren.lint.wildcard_single_variant "warn"

enum E { A, B, C }

comp c { in e: E pub out n: Int ensure r: n = match e { E::A => 1, E::B => 2, E::C => 3 } }
```
"# },
  { code := "F0727", explanation := r#"A chain of `if` whose tests are of which variant one scrutinee is (`if_chain_match`, allowed by default).

Example:

```fren
set_option fren.lint.if_chain_match "warn"

enum Mode { Heat, Cool, Off }

comp c { in m: Mode pub out y: Int ensure r: y = if m = Mode::Heat then 1 else if m = Mode::Cool then 2 else 0 }
```

The chain is a `match` on the scrutinee, with an arm for each test, and
`_` for the final `else`. If the tests name every variant, the final
`else` is never taken, and the `match` has no `_` arm. `fren fix` can fix
this:

```fren
enum Mode { Heat, Cool, Off }

comp c { in m: Mode pub out y: Int ensure r: y = match m { Mode::Heat => 1, Mode::Cool => 2, _ => 0 } }
```
"# },
  { code := "F0729", explanation := r#"Guarantees that constrain one output case by case on which variant one scrutinee is (`case_split_guarantees`, allowed by default).

Example:

```fren
set_option fren.lint.case_split_guarantees "warn"

enum Mode { Heat, Cool }

comp c {
    in m: Mode
    pub out y: Int
    ensure heat: when m = Mode::Heat, y = 1
    ensure cool: when m = Mode::Cool, y = 2
}
```

The guarantees say what one guarantee with a `match` says. `fren fix`
does not merge them, since traces, claims and `impl`s refer to
guarantees by name:

```fren
enum Mode { Heat, Cool }

comp c {
    in m: Mode
    pub out y: Int
    ensure rule: y = match m { Mode::Heat => 1, Mode::Cool => 2 }
}
```
"# },
  { code := "F0735", explanation := r#"A binding or field `x := x` (a warning, `redundant_bindings`).

Example:

```fren
comp sub { in x: Int pub out p? ensure r: p? iff x > 0 }

comp c { in x: Int inst s: sub { x := x } }
```

A binding of an instance, or a field of a record literal, `x` alone means
`x := x`. `fren fix` can fix this:

```fren
comp sub { in x: Int pub out p? ensure r: p? iff x > 0 }

comp c { in x: Int inst s: sub { x } }
```

In a record update of `r`, the lint also fires on a field `x := r.x`, which
gives `x` the value the update reads from `r` without it, and the fix
removes the field, when the update gives some other field a new value.
"# },
  { code := "F0736", explanation := r#"An operator whose two operands are written the same (a warning, `eq_op`).

Example:

```fren
comp c { in x: Int in y: Int pub out p? ensure r: p? iff (x < y or x = x) }
```

`x = x` is always `true`, so the guarantee says nothing. One operand is
probably a typo for another expression, which no rewrite can know, so
there is no fix. Write the operand meant:

```fren
comp c { in x: Int in y: Int pub out p? ensure r: p? iff (x < y or y = 0) }
```

The lint fires on `=`, `!=`, `<`, `<=`, `>`, `>=`, `iff`, `subset`, `and`,
`or`, `-`, `minus`, `inter` and `union`, whose value is then fixed or that
of the operand, but not on `+`, `*` or `++`, where `x + x` means something.
It also fires on `when c?, c?`, which is always `true`, and `unless c?,
c?`, which is `c?`: the body is probably a copy of the condition, pasted
where the consequent was meant. And it fires on an argument of
`exactly_one?` or `at_most_one?` written twice, as in `at_most_one?(a?,
b?, a?)`, which holds only where `a?` is `false`.
"# },
  { code := "F0737", explanation := r#"A conditional whose two branches are written the same, or a table whose rows' values are (a warning, `same_branches`).

Example:

```fren
comp c { in a? in x: Int pub out y: Int ensure r: y = if a? then x + 1 else x + 1 }
```

The condition decides nothing. Either one branch is not the one meant, or
the conditional is the branch. So does a table whose rows' values are all
written the same, as `table { a? => x + 1, _ => x + 1 }`. `fren fix` can
fix this:

```fren
comp c { in x: Int pub out y: Int ensure r: y = x + 1 }
```
"# },
  { code := "F0738", explanation := r#"A set or relation literal with an element written the same as an earlier one (a warning, `duplicate_elements`).

Example:

```fren
comp c { in x: Int pub out p? ensure r: p? iff x in {1, 2, 1} }
```

A set has no repeats, so `{1, 2, 1}` is `{1, 2}`. The repeat is probably a
typo for another element. A sequence literal, where a repeat means
something, is not reported. `fren fix` can fix this:

```fren
comp c { in x: Int pub out p? ensure r: p? iff x in {1, 2} }
```
"# },
  { code := "F0745", explanation := r#"A method applied to an empty argument, whose value then does not depend on the receiver as expected (a warning, `empty_argument`).

Example:

```fren
comp c { in s: String pub out p? ensure r: p? iff s.starts_with?("") }
```

Every string starts with `""`, so this is always `true`. The lint fires on
`starts_with?`, `ends_with?` and `contains?` of `""`, which are always
`true`; `s.replace("", b)`, which is `b ++ s`; `s.replace_all("", b)`,
which is `s`; `s.index_of("", i)`, which is `i` or `-1`; and `s.slice(i,
0)`, which is `""`; and the same for sequences, with `[]`. The argument is
probably not the one meant:

```fren
comp c { in s: String pub out p? ensure r: p? iff s.starts_with?("/") }
```
"# },
  { code := "F0730", explanation := r#"Two comparisons of the same operands that are one comparison (a warning, `double_comparison`).

Example:

```fren
comp c { in x: Int in y: Int pub out p? ensure r: p? iff (x < y or x = y) }
```

The operands may also be the other way around, as in `y > x`. Joined by
`or` or `and`, the two comparisons hold exactly when one other comparison
of the same operands does, as `a subset b and b subset a` is `a = b`.
`fren fix` can fix this:

```fren
comp c { in x: Int in y: Int pub out p? ensure r: p? iff x <= y }
```
"# },
  { code := "F0731", explanation := r#"An equation of two `Bool`s (`bool_equality`, allowed by default).

Example:

```fren
set_option fren.lint.bool_equality "warn"

comp c { in a? in b? pub out p? ensure r: p? = (a? and b?) }
```

On `Bool`s, `=` and `iff` agree, and `iff` says that the two are
equivalent. It binds more loosely, so the fix adds parentheses where they
are needed, as in `(a? iff b?) and c?`. `fren fix` can fix this:

```fren
comp c { in a? in b? pub out p? ensure r: p? iff (a? and b?) }
```
"# },
  { code := "F0732", explanation := r#"A search written with `index_of` or `slice` (a warning, `manual_method`).

Example:

```fren
comp c { in s: String pub out p? ensure r: p? iff s.slice(0, "ab".len) = "ab" }
```

`s.index_of(t, 0) >= 0` and `s.index_of(t, 0) != -1` are `s.contains?(t)`,
`s.index_of(t, 0) = 0` is `s.starts_with?(t)`, and so is `s.slice(0, t.len)
= t`, on strings and on sequences. `index_of` is outside the decidable
core, and `contains?` and `starts_with?` on a string are in it when their
argument is a constant, as is `starts_with?` on a sequence when its
argument is a literal. `fren fix` can fix this:

```fren
comp c { in s: String pub out p? ensure r: p? iff s.starts_with?("ab") }
```
"# },
  { code := "F0733", explanation := r#"A conditional operand whose `else` branch extends past the operator (a warning, `else_extends`).

Example:

```fren
comp c { in a? in x: Int in y: Int pub out n: Int ensure r: n = 2 * if a? then x else y + 1 }
```

A conditional is an atom, but its `else` branch extends as far right as
possible, so this is `2 * (if a? then x else (y + 1))`, not `(2 * if a?
then x else y) + 1`. Putting the branch in parentheses keeps the meaning
and shows where it ends. `fren fix` can fix this:

```fren
comp c { in a? in x: Int in y: Int pub out n: Int ensure r: n = 2 * if a? then x else (y + 1) }
```

If the other meaning was intended, put the conditional in parentheses
instead:

```fren
comp c { in a? in x: Int in y: Int pub out n: Int ensure r: n = (2 * if a? then x else y) + 1 }
```
"# },
  { code := "F0734", explanation := r#"An operation that leaves its operand as it is (a warning, `identity_op`).

Example:

```fren
comp c { in x: Int pub out n: Int ensure r: n = x * 1 }
```

`x + 0`, `0 + x`, `x - 0`, `x * 1`, `1 * x` and `x div 1` are `x`; `s ++ ""` and
`"" ++ s` are `s`, and so for `[]`; `a union {}`, `{} union a` and `a minus
{}` are `a`. `x + -y` is `x - y`, and `x - -y` is `x + y`. `fren fix` can
fix this:

```fren
comp c { in x: Int pub out n: Int ensure r: n = x }
```
"# },
  { code := "F0739", explanation := r#"Parentheses directly around parentheses (a warning, `double_parens`).

Example:

```fren
comp c { in x: Int pub out p? ensure r: p? iff ((x > 0)) }
```

One pair groups as well as two. `fren fix` can fix this:

```fren
comp c { in x: Int pub out p? ensure r: p? iff (x > 0) }
```
"# },
  { code := "F0740", explanation := r#"A negation of a negation (a warning, `double_neg`).

Example:

```fren
comp c { in x: Int pub out y: Int ensure r: y = -(-x) }
```

`-(-x)` is `x`. `fren fix` can fix this:

```fren
comp c { in x: Int pub out y: Int ensure r: y = x }
```
"# },
  { code := "F0741", explanation := r#"A non-strict comparison of integers with an operand off by one (a warning, `int_plus_one`).

Example:

```fren
comp c { in x: Int in y: Int pub out p? ensure r: p? iff x >= y + 1 }
```

Over the integers, `x >= y + 1` is `x > y`, and so are `x - 1 >= y` and
`y + 1 <= x`. `fren fix` can fix this:

```fren
comp c { in x: Int in y: Int pub out p? ensure r: p? iff x > y }
```
"# },
  { code := "F0742", explanation := r#"A product with `-1` (a warning, `neg_multiply`).

Example:

```fren
comp c { in x: Int pub out y: Int ensure r: y = x * -1 }
```

`x * -1` and `-1 * x` are `-x`. `fren fix` can fix this:

```fren
comp c { in x: Int pub out y: Int ensure r: y = -x }
```
"# },
  { code := "F0743", explanation := r#"A chain of methods with a shorter form (a warning, `redundant_method_chain`).

Example:

```fren
enum E { A, B }

comp c { in r: Rel<E, E> pub out p? ensure d: p? iff r.inverse.inverse.domain = {} }
```

The inverse of the inverse is the relation itself, and the domain of a
relation is the range of its inverse. The shorter chain means the same.
`fren fix` can fix this:

```fren
enum E { A, B }

comp c { in r: Rel<E, E> pub out p? ensure d: p? iff r.domain = {} }
```
"# },
  { code := "F0744", explanation := r#"A pattern with no operator but `.*` at its ends (a warning, `trivial_pattern`).

Example:

```fren
comp c { in s: String pub out p? ensure r: p? iff s.matches?(r"F0\.1.*") }
```

The pattern matches the strings that start with `F0.1`, which
`starts_with?` says plainly. `fren fix` can fix this:

```fren
comp c { in s: String pub out p? ensure r: p? iff s.starts_with?("F0.1") }
```
"# },
  { code := "F0746", explanation := r#"A `: Bool` that a name ending in `?` implies (a warning, `redundant_bool_type`).

Example:

```fren
comp c { in ready?: Bool pub out p? ensure r: p? iff ready? }
```

A name that ends in `?` is a `Bool`, so the type need not be written.
`fren fix` can fix this:

```fren
comp c { in ready? pub out p? ensure r: p? iff ready? }
```
"# },
  { code := "F0747", explanation := r#"A `match` of one arm that binds nothing (a warning, `trivial_match`).

Example:

```fren
enum E { A, B }

comp c { in e: E in x: Int pub out y: Int ensure r: y = 2 * match e { _ => x + 1 } }
```

The arm matches every value, so the `match` is its body. `fren fix` can
fix this:

```fren
comp c { in x: Int pub out y: Int ensure r: y = 2 * (x + 1) }
```
"# },
  { code := "F0748", explanation := r#"A module whose name repeats its parent's (a warning, `module_inception`).

Example:

```fren
pub mod climate::climate

pub comp sensor { in t: Int pub out hot? ensure r: hot? iff t > 30 }
```

Every path to the module, or to an item in it, repeats the name, as in
`climate::climate::sensor`. Declare the items in the parent, or give the
module a name of its own:

```fren
pub mod climate::sensors

pub comp sensor { in t: Int pub out hot? ensure r: hot? iff t > 30 }
```
"# },
  { code := "F0749", explanation := r#"Variants named with a word they all share, or with their enumeration's name (a warning, `enum_variant_names`).

Example:

```fren
pub enum Mode { HeatMode, CoolMode }
```

A path to a variant names its enumeration already, as `Mode::HeatMode`
does, so the shared word says nothing. Remove it:

```fren
pub enum Mode { Heat, Cool }
```
"# },
  { code := "F0750", explanation := r#"A name in `CamelCase` with an acronym in upper case (a warning, `upper_case_acronyms`).

Example:

```fren
pub enum HTTPStatus { Ok, NotFound }
```

Three or more uppercase letters in a row hide where one word ends and the
next starts. In `CamelCase`, an acronym is a word, with only its first
letter in upper case:

```fren
pub enum HttpStatus { Ok, NotFound }
```
"# },
  { code := "F0751", explanation := r#"A name made only of `_` and digits (a warning, `just_underscores_and_digits`).

Example:

```fren
comp c { in _1: Int pub out y: Int ensure r: y = _1 + 1 }
```

Such a name says nothing of what it names. Give it a name that does:

```fren
comp c { in reading: Int pub out y: Int ensure r: y = reading + 1 }
```
"# },
  { code := "F0752", explanation := r#"A placeholder name, such as `foo` (a warning, `disallowed_names`).

Example:

```fren
comp foo { in x: Int pub out y: Int ensure r: y = x + 1 }
```

`foo`, `baz` and `quux`, in any case, are placeholders, which say nothing
of what they name. Give it a name that does:

```fren
comp successor { in x: Int pub out y: Int ensure r: y = x + 1 }
```
"# },
  { code := "F0759", explanation := r#"A conditional that gives a `Bool` or its negation (a warning, `needless_bool_assign`).

Example:

```fren
comp c { in a? in b? pub out p? ensure r: p? iff if a? then b? else not b? }
```

`if C then X else not X` holds exactly when `C` and `X` agree, which is
`C iff X`, and `if C then not X else X` exactly when they differ, which is
`C != X`. `fren fix` can fix this:

```fren
comp c { in a? in b? pub out p? ensure r: p? iff (a? iff b?) }
```
"# },
  { code := "F0760", explanation := r#"A `match` that gives back its scrutinee (a warning, `needless_match`).

Example:

```fren
enum Shape { Dot, Circle(Int) }

comp c { in s: Shape pub out t: Shape ensure r: t = match s { Shape::Dot => Shape::Dot, Shape::Circle(r) => Shape::Circle(r) } }
```

Each arm builds the variant that it matched, with the values of its
payload in order, so the `match` is its scrutinee. `fren fix` can fix
this:

```fren
enum Shape { Dot, Circle(Int) }

comp c { in s: Shape pub out t: Shape ensure r: t = s }
```
"# },
  { code := "F0761", explanation := r#"A constraint that mentions no variable (a warning, `assertions_on_constants`).

Example:

```fren
const LIMIT: Int := 10

comp c { in x: Int pub out y: Int ensure r: y = x expect e: LIMIT > 0 }
```

The expectation is the same in every behaviour: it is always true, and
says nothing about the component, or always false, and always fails. A
guarantee that is always false makes the component unrealizable, and an
assumption that is always false makes it vacuous. Say something about the
variables, or remove the constraint:

```fren
comp c { in x: Int pub out y: Int ensure r: y = x expect e: y = x }
```

There is no fix, since removing a constraint changes the checks.
"# },
  { code := "F0762", explanation := r#"A binary operator directly followed by a negation and then a space (a warning, `suspicious_unary_op_formatting`).

Example:

```fren
comp c { in x: Int pub out p? ensure r: p? iff x >=- 1 }
```

`>=- 1` reads like one operator `>=-`, but it is `>=`, whose right operand
is `-1`. `fren fix` can fix this:

```fren
comp c { in x: Int pub out p? ensure r: p? iff x >= -1 }
```
"# },
  { code := "F0753", explanation := r#"A slice that is the whole of its receiver (a warning, `redundant_slicing`).

Example:

```fren
set_option fren.lint.undecidable "allow"

comp c { in s: String pub out p? ensure r: p? iff s.slice(0, s.len) = "x" }
```

`s.slice(0, s.len)` is `s`, for every string or sequence `s`, `""` and
`[]` included. `fren fix` can fix this:

```fren
comp c { in s: String pub out p? ensure r: p? iff s = "x" }
```
"# },
  { code := "F0754", explanation := r#"A replacement with what it replaces (a warning, `no_effect_replace`).

Example:

```fren
set_option fren.lint.undecidable "allow"

comp c { in s: String in a: String pub out p? ensure r: p? iff s.replace(a, a) = "x" }
```

Replacing `a` with `a` leaves `s` as it is, with `replace` or
`replace_all`, even where `a` is `""`. `fren fix` can fix this:

```fren
comp c { in s: String pub out p? ensure r: p? iff s = "x" }
```

If another replacement was meant, write it:

```fren
set_option fren.lint.undecidable "allow"

comp c { in s: String in a: String pub out p? ensure r: p? iff s.replace(a, "-") = "x" }
```
"# },
  { code := "F0755", explanation := r#"A test of a literal whose value the literal fixes (a warning, `const_is_empty`).

Example:

```fren
comp c { in s: String pub out p? ensure r: p? iff s = "x" or "x".len = 0 }
```

The length of a string or sequence literal is fixed, and so is whether a
set literal is empty, so the test is always `true` or always `false`. The
literal is probably not the one meant:

```fren
comp c { in s: String pub out p? ensure r: p? iff s = "x" or s.len = 0 }
```
"# },
  { code := "F0756", explanation := r#"An alternation of single characters in a pattern (a warning, `manual_pattern_char_comparison`).

Example:

```fren
comp c { in s: String pub out p? ensure r: p? iff s.matches?(r"(a|b|-)+") }
```

An alternation of single characters matches one of them, as a class does.
`fren fix` can fix this, escaping `\`, `]`, `^` and `-` in the class:

```fren
comp c { in s: String pub out p? ensure r: p? iff s.matches?(r"[ab\-]+") }
```
"# },
  { code := "F0757", explanation := r#"A range in a pattern one character short of an alphabet (a warning, `almost_complete_range`).

Example:

```fren
comp c { in s: String pub out p? ensure r: p? iff s.matches?(r"[a-y]+") }
```

A range includes both its ends, so `a-y` leaves out `z`. The lint fires on
`a-y`, `b-z`, `A-Y`, `B-Z` and `0-8`, but not on `1-9`, which is often
meant. `fren fix` can fix this:

```fren
comp c { in s: String pub out p? ensure r: p? iff s.matches?(r"[a-z]+") }
```
"# },
  { code := "F0768", explanation := r#"A constraint or global expectation written the same as an earlier one (a warning, `duplicate_constraint`).

Example:

```fren
comp c { in a? in b? pub out p? ensure r1: p? iff a? or b? ensure r2: p? iff a?  or  b? }
```

`r2` says what `r1` says. The redundancy check would report each as
following from the other, which invites removing both. Where the two are
of one kind, `fren fix` removes the later:

```fren
comp c { in a? in b? pub out p? ensure r1: p? iff a? or b? }
```

An `expect` that repeats an `ensure` or an `assume` is reported too, but not
fixed: it tests nothing, and was probably meant to say something
stronger. A cover goal written the same as an earlier cover goal is
reported and removed too, but a cover goal is not compared with a
constraint.
"# },
  { code := "F0769", explanation := r#"A string literal with an invisible character, or a string literal or comment with a bidirectional control (a warning, `invisible_characters`).

Example:

```fren
comp c { in s: String pub out p? ensure r: p? iff s = "a​b" }
```

The literal holds a zero width space, U+200B, between `a` and `b`. It
cannot be seen, so the literal looks like `"ab"`, which it is not. The
lint also fires on U+00AD and U+2060 in a literal, and on the
bidirectional controls, U+202A to U+202E and U+2066 to U+2069, and on
U+FEFF, in a literal or a comment, which can make text display in an
order other than the one it is read in. `fren fix` writes each in a
literal as an escape, so that a deliberate use stays and can be seen, and
removes it from a comment:

```fren
comp c { in s: String pub out p? ensure r: p? iff s = "a\u200Bb" }
```
"# },
  { code := "F0770", explanation := r#"A negative integer literal as a position (a warning, `negative_position`).

Example:

```fren
comp c { in s: String pub out p? ensure r: p? iff s.at(-1) = "." }
```

Fren has no negative indexing: `s.at(-1)` is not the last character, but
always `""`. Likewise, `s.slice(-3, 3)` is always `""`, `q.update(-1, x)`
is always `q`, `s.index_of(t, -1)` is always `-1`, and `q[-1]` is
unspecified. To count from the end, subtract from the length, which is
outside the decidable core:

```fren
set_option fren.lint.undecidable "allow" in
comp c { in s: String pub out p? ensure r: p? iff s.at(s.len - 1) = "." }
```
"# },
  { code := "F0763", explanation := r#"A comparison of a length that is always the same (a warning, `absurd_extreme_comparisons`).

Example:

```fren
comp c { in q: Seq<Int> pub out p? ensure r: p? iff q.len < 0 }
```

A `len` or `card` is never negative, so `q.len < 0` is always `false`, and
`q.len >= 0` and `q.len > -1` are always `true`. The bound or the operator
is probably not the one meant, which no rewrite can know, so there is no
fix. Write the comparison meant:

```fren
comp c { in q: Seq<Int> pub out p? ensure r: p? iff q.len < 3 }
```

The comparisons that say whether a collection is empty, such as `q.len >
0`, are `length_zero`'s and `card_zero`'s.

No value of an ordered enumeration is below its first variant or above its
last, so a comparison with one of them can be fixed too: with `pub ordered
enum Level { Low, High }`, `l >= Level::Low` is always `true`, and `l >
Level::High` always `false`.
"# },
  { code := "F0764", explanation := r#"An operation whose value ignores an operand (a warning, `erasing_op`).

Example:

```fren
comp c { in x: Int in y: Int pub out z: Int ensure r: z = x * 0 + y }
```

`x * 0` is always `0`, whatever `x` is, as `s inter {}` and `{} minus s`
are always `{}`, `x in {}` is always `false`, and `{} subset s` always
`true`. The literal is probably not the operand meant, so there is no
fix. Write the operand meant:

```fren
comp c { in x: Int in y: Int pub out z: Int ensure r: z = x * 2 + y }
```
"# },
  { code := "F0765", explanation := r#"A test of a chain of `else if` written the same as an earlier one (a warning, `ifs_same_cond`).

Example:

```fren
comp c { in x: Int pub out y: Int ensure r: y = if x > 0 then 1 else if x > 0 then 2 else 3 }
```

The branch of the second test is never taken: wherever the test holds, the
earlier branch is taken. One of the tests is probably not the one meant,
so there is no fix. Write the test meant:

```fren
comp c { in x: Int pub out y: Int ensure r: y = if x > 0 then 1 else if x < 0 then 2 else 3 }
```
"# },
  { code := "F0766", explanation := r#"Two comparisons that cannot both hold, or of which one always holds (a warning, `contradictory_comparisons`).

Example:

```fren
enum Mode { Heat, Cool, Off }

comp c { in m: Mode pub out on? ensure r: on? iff (m != Mode::Heat or m != Mode::Cool) }
```

`m` is never both `Mode::Heat` and `Mode::Cool`, so one of the two
comparisons always holds, and the guarantee says that `on?` always
holds. `and` and `or` are probably swapped, or a value is not the one
meant, so there is no fix. Write the comparisons meant:

```fren
enum Mode { Heat, Cool, Off }

comp c { in m: Mode pub out on? ensure r: on? iff (m != Mode::Heat and m != Mode::Cool) }
```

The lint also fires on comparisons of one operand with integers that no
integer meets, joined by `and`, as `x < 3 and x > 5`, and that every
integer meets, joined by `or`, as `x > 3 or x < 5`.
"# },
  { code := "F0767", explanation := r#"Two comparisons of one operand with integers, of which one implies the other (a warning, `redundant_comparisons`).

Example:

```fren
comp c { in x: Int pub out p? ensure r: p? iff (x < 3 and x < 5) }
```

Every `x` below `3` is below `5`, so the two comparisons are `x < 3`; with
`or`, they would be `x < 5`. `fren fix` can fix this:

```fren
comp c { in x: Int pub out p? ensure r: p? iff x < 3 }
```
"# },
  { code := "F0771", explanation := r#"A `match` of one pattern that binds nothing and `_` (`single_match_else`, allowed by default).

Example:

```fren
set_option fren.lint.single_match_else "warn"

enum Mode { Heat, Cool, Off }

comp c { in m: Mode in x: Int pub out y: Int ensure r: y = match m { Mode::Heat => x + 1, _ => x } }
```

The `match` tests whether `m` is `Mode::Heat`, which an `if` says
directly. For a pattern that `=` and `in` cannot write, such as
`Reply::Ok(_)` or `0..=9`, the `if` tests it with `is`. `fren fix` can fix
this:

```fren
enum Mode { Heat, Cool, Off }

comp c { in m: Mode in x: Int pub out y: Int ensure r: y = if m = Mode::Heat then x + 1 else x }
```
"# },
  { code := "F0772", explanation := r#"A record literal whose fields are not in the order its record declares them (`inconsistent_struct_constructor`, allowed by default).

Example:

```fren
set_option fren.lint.inconsistent_struct_constructor "warn"

struct Cell { row: Int, column: Int }

comp c { in x: Int pub out cell: Cell ensure r: cell = Cell { column := x, row := 0 } }
```

The order of the fields does not change the value, but the literal reads
more easily in the order of the declaration. `fren fix` can fix this:

```fren
struct Cell { row: Int, column: Int }

comp c { in x: Int pub out cell: Cell ensure r: cell = Cell { row := 0, column := x } }
```
"# },
  { code := "F0773", explanation := r#"An `and` or `or` with an operand that can be dropped (`overly_complex_bool_expr`, allowed by default).

Example:

```fren
set_option fren.lint.overly_complex_bool_expr "warn"

comp c { in a? in b? pub out p? ensure r: p? iff (a? or (a? and b?)) }
```

Wherever `a? and b?` holds, `a?` holds, so the `or` is `a?`. Likewise `a
and (a or b)` is `a`, `a and not a` is `false`, and `a or not a` is `true`;
the last two probably have an operand that is not the one meant. `fren
fix` can fix this:

```fren
comp c { in a? pub out p? ensure r: p? iff a? }
```
"# },
  { code := "F0774", explanation := r#"Fields named with a word they all share, or with their record's name (`struct_field_names`, allowed by default).

Example:

```fren
set_option fren.lint.struct_field_names "warn"

pub struct Pump { pump_on?, pump_speed: Int }
```

A field is read from a value of its record, as `p.pump_speed` is, so the
shared word says nothing. Remove it:

```fren
pub struct Pump { on?, speed: Int }
```
"# },
  { code := "F0775", explanation := r#"A function with more than 3 `Bool` parameters (`fn_params_excessive_bools`, allowed by default).

Example:

```fren
set_option fren.lint.fn_params_excessive_bools "warn"

pub fn allowed?(a?, b?, c?, d?) := a? and (b? or c? or d?)
```

A call such as `allowed?(true, false, true, false)` does not say which
argument is which. Replace some of them with an enumeration, or with a
record of named `Bool` fields:

```fren
pub struct Access { admin?, owner?, member?, guest? }

pub fn allowed?(access: Access) := access.admin? and (access.owner? or access.member? or access.guest?)
```
"# },
  { code := "F0776", explanation := r#"A record with more than 3 `Bool` fields (`struct_excessive_bools`, allowed by default).

Example:

```fren
set_option fren.lint.struct_excessive_bools "warn"

pub struct Door { open?, closed?, locked?, jammed? }
```

Every combination of the fields is allowed, such as a door both `open?`
and `closed?`, though few are meant. An enumeration of those that are
says so:

```fren
pub enum DoorState { Open, Closed, Locked, Jammed }

pub struct Door { state: DoorState }
```
"# },
  { code := "F0777", explanation := r##"A raw string literal with more `#`s than it needs (`needless_raw_string_hashes`, allowed by default).

Example:

```fren
set_option fren.lint.needless_raw_string_hashes "warn"

comp c { in s: String pub out p? ensure r: p? iff s.matches?(r#"a+b"#) }
```

A raw literal needs one `#` more than the longest run of `#` after a `"`
in it, and none without a `"`: `r#"..."#` is needed only for a body with a
`"`. `fren fix` can fix this:

```fren
comp c { in s: String pub out p? ensure r: p? iff s.matches?(r"a+b") }
```
"## },
  { code := "F0778", explanation := r#"An `if` whose branches share an operand (`branches_sharing_code`, allowed by default).

Example:

```fren
set_option fren.lint.branches_sharing_code "warn"

comp c { in fast? in x: Int pub out y: Int ensure r: y = if fast? then 2 * x + 1 else x + 1 }
```

Both branches add `1`, whichever is taken, so the `if` can choose the rest
alone. `fren fix` can fix this:

```fren
comp c { in fast? in x: Int pub out y: Int ensure r: y = (if fast? then 2 * x else x) + 1 }
```
"# },
  { code := "F0780", explanation := r#"A `set_option` that sets a lint or a group to `allow` (`allow_attributes`, allowed by default).

Example:

```fren
set_option fren.lint.allow_attributes "warn"
set_option fren.lint.glob_imports "allow"

enum E { A, B }

use self::E::*

comp c { in e: E pub out p? ensure r: p? iff e = A }
```

`"expect"` silences the lint too, and once nothing where it is in effect
needs it, `unfulfilled_lint_expectations` reports the setting, so that it
does not outlive its reason. `fren fix` can fix this:

```fren
set_option fren.lint.allow_attributes "warn"
set_option fren.lint.glob_imports "expect"

enum E { A, B }

use self::E::*

comp c { in e: E pub out p? ensure r: p? iff e = A }
```

Where the lint never fires, the expectation is unfulfilled, a warning that
`allow` never gave. For `unfulfilled_lint_expectations` itself, `"expect"`
means `"allow"`, so that setting has no fix.
"# },
  { code := "F0781", explanation := r#"A `_` arm of a `match` (`wildcard_enum_match_arm`, allowed by default).

Example:

```fren
set_option fren.lint.wildcard_enum_match_arm "warn"

enum E { A, B, C }

comp c { in e: E pub out n: Int ensure r: n = match e { E::A => 1, _ => 2 } }
```

A variant added to `E` later would be matched by `_` without notice. Named,
it makes the `match` non-exhaustive, a static error, so that the new
variant gets an arm of its own. `fren fix` can fix this:

```fren
set_option fren.lint.wildcard_enum_match_arm "warn"

enum E { A, B, C }

comp c { in e: E pub out n: Int ensure r: n = match e { E::A => 1, E::B | E::C => 2 } }
```
"# },
  { code := "F0782", explanation := r#"A raw string literal whose contents have no `\` and no `"` (`needless_raw_strings`, allowed by default).

Example:

```fren
set_option fren.lint.needless_raw_strings "warn"

comp c { in s: String pub out p? ensure r: p? iff s.matches?(r"[a-z]+") }
```

A raw literal is for contents that would need escapes in an ordinary one.
These need none, and the ordinary literal has the same value. `fren fix`
can fix this:

```fren
set_option fren.lint.needless_raw_strings "warn"

comp c { in s: String pub out p? ensure r: p? iff s.matches?("[a-z]+") }
```
"# },
  { code := "F0783", explanation := r#"A string literal with a character beyond ASCII (`non_ascii_literal`, allowed by default).

Example:

```fren
set_option fren.lint.non_ascii_literal "warn"

comp c { in s: String pub out p? ensure r: p? iff s = "café" }
```

A character beyond ASCII may look like another, or not display in every
font. As an escape, it reads the same everywhere. `fren fix` can fix this:

```fren
set_option fren.lint.non_ascii_literal "warn"

comp c { in s: String pub out p? ensure r: p? iff s = "caf\u00E9" }
```

A character beyond `U+FFFF` has no escape, since `\uHHHH` has four digits,
so a literal with one has no fix.
"# },
  { code := "F0784", explanation := r#"An item whose name contains its module's (`module_name_repetitions`, allowed by default).

Example:

```fren
set_option fren.lint.module_name_repetitions "warn"

mod climate

pub enum ClimateMode { Heat, Cool }
```

A path to the item names the module already, so `climate::ClimateMode`
says `climate` twice. Remove it from the item's name:

```fren
set_option fren.lint.module_name_repetitions "warn"

mod climate

pub enum Mode { Heat, Cool }
```
"# },
  { code := "F0785", explanation := r#"A declared name of one character (`min_ident_chars`, allowed by default).

Example:

```fren
set_option fren.lint.min_ident_chars "warn"

comp offset { in t: Int pub out level: Int ensure raised: level = t + 1 }
```

A name of one character says little of what it names. Give it a name that
says more:

```fren
set_option fren.lint.min_ident_chars "warn"

comp offset { in reading: Int pub out level: Int ensure raised: level = reading + 1 }
```
"# },
  { code := "F0786", explanation := r#"A path of three or more segments in an expression, pattern or type (`absolute_paths`, allowed by default).

Example:

```fren
set_option fren.lint.absolute_paths "warn"

mod house::climate

pub enum Mode { Heat, Cool }

mod house

comp c { in m: climate::Mode pub out p? ensure r: p? iff m = climate::Mode::Heat }
```

`climate::Mode::Heat` has three segments. Import the enumeration with
`use`, and write the shorter path:

```fren
set_option fren.lint.absolute_paths "warn"

mod house::climate

pub enum Mode { Heat, Cool }

mod house

use self::climate::Mode

comp c { in m: Mode pub out p? ensure r: p? iff m = Mode::Heat }
```
"# },
  { code := "F0787", explanation := r#"An `and` in an `or`, or a `join` or `inter` in a `union` or `minus`, without parentheses (`precedence`, allowed by default).

Example:

```fren
set_option fren.lint.precedence "warn"

comp c { in a? in b? in d? pub out p? ensure r: p? iff (a? or b? and d?) }
```

`and` binds more tightly than `or`, so this is `a? or (b? and d?)`
already. The parentheses say so to a reader who does not know the
precedence. `fren fix` can fix this:

```fren
set_option fren.lint.precedence "warn"

comp c { in a? in b? in d? pub out p? ensure r: p? iff (a? or (b? and d?)) }
```
"# },
  { code := "F0789", explanation := r#"A relation to a type of one value (`zero_sized_map_values`, allowed by default).

Example:

```fren
set_option fren.lint.zero_sized_map_values "warn"

enum Mark { Marked }

comp c { in r: Rel<Int, Mark> pub out p? ensure q: p? iff (1, Mark::Marked) in r }
```

`Mark` has one value, so `r` pairs each `Int` it relates with
`Mark::Marked`, and says only which `Int`s it relates. A set says the
same:

```fren
comp c { in s: Set<Int> pub out p? ensure q: p? iff 1 in s }
```
"# },
  { code := "F0790", explanation := r#"A record literal that copies each field of a value of its record (a warning, `unnecessary_struct_initialization`).

Example:

```fren
struct Point { x: Int, y: Int }

comp c { in p: Point pub out q: Point ensure r: q = Point { x := p.x, y := p.y } }
```

The literal reads each field of `p` into the same field, so it is `p`.
It fires only where `p` is a value of the record itself: a literal of
another record with the same fields converts, and an instance is not a
value. `fren fix` can fix this:

```fren
struct Point { x: Int, y: Int }

comp c { in p: Point pub out q: Point ensure r: q = p }
```
"# },
  { code := "F0791", explanation := r#"A lint setting that is in effect at no item (a warning, `unused_lint_setting`).

Example:

```fren
set_option fren.lint.disallowed_names "deny"
set_option fren.lint.style "allow"

comp c { in x: Int pub out y: Int ensure r: y = x }
```

The second setting sets `disallowed_names`, a lint of `style`, before any
item, so the first has no effect: the `deny` is undone. A setting at the
end of a file, after the last item, has no effect either. Remove the
setting, as `fren fix` does, or move it to where it was meant to apply:

```fren
set_option fren.lint.style "allow"

comp c { in x: Int pub out y: Int ensure r: y = x }
```

A setting of a lint after its group's is not reported, since it sets that
lint alone, nor is a setting to `expect`, which
`unfulfilled_lint_expectations` reports.
"# },
  { code := "F0792", explanation := r#"An assumption that constrains only inputs that nothing else mentions (a warning, `unused_assumption`).

Example:

```fren
comp c { in x: Int in n: Int pub out y: Int assume pos: n > 0 ensure r: y = x + 1 }
```

`pos` mentions `n`, so `unused_variables` does not report it, but nothing
else does: no guarantee, expectation, definition or binding, no other
assumption that ties it to a used variable, no global expectation of the
file that reads it, no instance of `c` in the file, and no refinement of
the file with `c` as its abstraction. This is what is left after the last
guarantee about an input is removed. Remove the assumption and the
input, or use them:

```fren
comp c { in x: Int pub out y: Int ensure r: y = x + 1 }
```

Assumptions that are reported and linked, by an input or a function, are removed
together: one may guard an index in another, which is not defined without
it. Each message names the others.
"# },
  { code := "F0793", explanation := r#"A global expectation whose binders fall into groups that nothing relates (a warning, `unrelated_binders`).

Example:

```fren
comp c { in x: Int pub out y: Int ensure r: y = x + 1 }

expect e: forall (a b: c), (when a.x = 0, a.y = 1) and (when b.x = 1, b.y = 2)
```

`e` is a conjunction, and neither of its operands mentions both `a` and
`b`, so `e` is two claims run together, one about each, and a
counterexample to one names a binder that has nothing to do with it. An
`or`, a `not`, a `when` and the other connectives relate every binder they
mention, so only an `and` at the top separates claims. Relate the binders,
or write one expectation for each claim:

```fren
comp c { in x: Int pub out y: Int ensure r: y = x + 1 }

expect e: forall (a: c), when a.x = 0, a.y = 1
expect f: forall (b: c), when b.x = 1, b.y = 2
```
"# },
  { code := "F0794", explanation := r#"A `.` between two letters or digits in a pattern (a warning, `literal_dot_in_pattern`).

Example:

```fren
comp c { in s: String pub out p? ensure r: p? iff s.matches?(r"v1.2") }
```

In a pattern, `.` matches any one character, so `v1.2` matches `v1x2`
too. Between two letters or digits, it is probably meant as a dot.
`fren fix` writes it as the class `[.]`, which a string literal that is
not raw can hold as it is, unlike `\.`:

```fren
comp c { in s: String pub out p? ensure r: p? iff s.matches?(r"v1[.]2") }
```
"# },
  { code := "F0795", explanation := r#"An item that declares many single-character names (`many_single_char_names`, allowed by default).

Example:

```fren
set_option fren.lint.many_single_char_names "warn"

comp total { in a: Int in b: Int in c: Int in d: Int pub out s: Int ensure r: s = a + b + c + d }
```

More than four names of one character, not counting a final `?`, are hard
to tell apart. Name them for what they stand for:

```fren
comp total { in apples: Int in pears: Int pub out fruit: Int ensure r: fruit = apples + pears }
```
"# },
  { code := "F0796", explanation := r#"Two names that differ by one character (`similar_names`, allowed by default).

Example:

```fren
set_option fren.lint.similar_names "warn"

comp c { in count: Int in counts: Int pub out p? ensure r: p? iff count < counts }
```

One is easily written, or read, for the other. Names that differ only in
a digit, such as `x1` and `x2`, or in a character that is a word of its
own, such as `a_len` and `b_len`, are a series on purpose, and are not
reported. Rename one:

```fren
comp c { in count: Int in limit: Int pub out p? ensure r: p? iff count < limit }
```
"# },
  { code := "F0797", explanation := r#"A component or defined function of more than 100 lines (`too_many_lines`, allowed by default).

Example:

```fren
set_option fren.lint.too_many_lines "warn"

comp c {
    in x: Int
"# ++ String.join ((List.range 50).map fun i => s!"    pub out y{i}: Int\n    ensure r{i}: y{i} = x + {i}\n") ++ r#"}
```

Its lines are counted from its name to its end, but not those that are
blank or only comments. Split it into smaller components, as instances:

```fren
comp part { in x: Int pub out y: Int ensure r: y = x + 1 }

comp whole { in x: Int pub out y: Int inst p: part { x } ensure r: y = p.y + 1 }
```
"# },
  { code := "F0798", explanation := r#"A comparison of a method's call that is always the same (`invalid_upcast_comparisons`, allowed by default).

Example:

```fren
set_option fren.lint.invalid_upcast_comparisons "warn"

comp c { in x: Int pub out p? ensure r: p? iff x.abs >= 0 }
```

`x.abs` is never below 0, and `s.index_of(t, i)` never below -1, so a
comparison of either with a bound below that is always `true` or always
`false`, and so are `x.abs >= 0` and `x.abs < 0`. The bound or the
operator is probably not the one meant, such as `>=` for `>`:

```fren
comp c { in x: Int pub out p? ensure r: p? iff x.abs > 0 }
```
"# },
  { code := "F0799", explanation := r#"A string literal that is not in Unicode NFC (`unicode_not_nfc`, allowed by default).

Example, where the `e` is followed by U+0301, a combining acute accent:

```fren
set_option fren.lint.unicode_not_nfc "warn"

comp c { in s: String pub out p? ensure r: p? iff s = "cafe"# ++ "\u0301" ++ r#"" }
```

Strings compare by code point, and text is usually in NFC, where `é` is
the one code point U+00E9, so the literal never equals it. Write it in
NFC, as the message suggests. `fren fix` does not, since that changes the
literal's value:

```fren
comp c { in s: String pub out p? ensure r: p? iff s = "café" }
```
"# },
  { code := "F0801", explanation := r#"A trailing comma on the line of the `}` or `]` that closes its list (`unnecessary_trailing_comma`, allowed by default).

Example:

```fren
set_option fren.lint.unnecessary_trailing_comma "warn"

enum Mode { Heat, Cool, }
```

A list ends with a comma only where its `}` or `]` starts a line, as
`fren fmt` writes it, so that an element is added by adding a line. `fren
fix` can fix this, by removing the comma:

```fren
enum Mode { Heat, Cool }

enum Fan {
    Low,
    High,
}
```
"# },
  { code := "F0802", explanation := r#"A pattern test of one variant without a payload, or of one literal (a warning, `is_equality`).

Example:

```fren
enum E { A, B, C(Int) }

comp c { in e: E pub out p? ensure r: p? iff e is E::A }
```

`=` compares with one value, and `is` tests against several, and against
the patterns that `=` cannot write, those with a payload and ranges.
`fren fix` can fix this:

```fren
enum E { A, B, C(Int) }

comp c { in e: E pub out p? ensure r: p? iff e = E::A }
```

A test of several values, or of a pattern with a payload, stays a test:

```fren
enum E { A, B, C(Int) }

comp c { in e: E pub out p? ensure r: p? iff e is E::A | E::C(_) }
```
"# },
  { code := "F0805", explanation := r#"Equations of one expression with values that patterns write, joined by `or` (a warning, `manual_pattern_test`).

Example:

```fren
comp c { in status: Int pub out retry? ensure r: retry? iff status = 429 or status = 503 }
```

A pattern test says that `status` is one of these values directly, and
extends to a range as it is, as in `status is 429 | 500..=599`. Each value
is an integer literal, a string literal or a variant without a payload.
`fren fix` can fix this:

```fren
comp c { in status: Int pub out retry? ensure r: retry? iff status is 429 | 503 }
```

A pattern test of the same expression joins the test, and the dual, `x !=
a and x != b`, becomes `not x is a | b`. A value that a pattern does not
write, such as a variable, is left to a membership: `x = a or x = y` stays.
"# },
  { code := "F0803", explanation := r#"A pattern test that is always `true` (a warning, `irrefutable_is`).

Example:

```fren
enum E { A, B(Int) }

comp c { in e: E pub out p? ensure r: p? iff e is E::A | E::B(_) }
```

The pattern names every variant of `E`, so it matches every value of `e`,
as `_` does. The pattern is probably not the one meant: name only the
variants to test for.

```fren
enum E { A, B(Int) }

comp c { in e: E pub out p? ensure r: p? iff e is E::B(_) }
```
"# },
  { code := "F0804", explanation := r#"Two comparisons that one chained comparison writes (a warning, `chainable_comparison`).

Example:

```fren
comp c { in i: Int in n: Int pub out p? ensure r: p? iff 0 <= i and i < n }
```

`0 <= i < n` means `0 <= i and i < n`, and puts `i` between its bounds. A
comparison is written the other way round to chain, so `i >= 0 and i < n`
fires too. `fren fix` can fix this:

```fren
comp c { in i: Int in n: Int pub out p? ensure r: p? iff 0 <= i < n }
```
"# },
  { code := "F0832", explanation := r#"A `match` on a binder of its arm that the arm's pattern can match instead (a warning, `collapsible_match`).

Example:

```fren
enum Shape { Circle(Int), Square(Int), Empty }
enum Reply { Ok(Shape), Err(Int) }

comp c {
    in r: Reply
    pub out n: Int
    ensure rule: n = match r { Reply::Ok(s) => match s { Shape::Circle(_) => 1, Shape::Square(_) => 2, _ => 0 }, _ => 0 }
}
```

The inner `match` reads the payload of `Reply::Ok`, and its `_` arm has
the body of the outer `_` arm, so a nested pattern says the same in one
`match`. `fren fix` can fix this:

```fren
enum Shape { Circle(Int), Square(Int), Empty }
enum Reply { Ok(Shape), Err(Int) }

comp c {
    in r: Reply
    pub out n: Int
    ensure rule: n = match r { Reply::Ok(Shape::Circle(_)) => 1, Reply::Ok(Shape::Square(_)) => 2, _ => 0 }
}
```
"# },
  { code := "F0833", explanation := r#"An or-pattern of integers that is one range (a warning, `manual_range_patterns`).

Example:

```fren
comp c { in n: Int pub out m: Int ensure r: m = match n { 1 | 2 | 3 => 1, _ => 0 } }
```

The alternatives match the integers from 1 to 3, without a gap, which the
range `1..=3` says at once. `fren fix` can fix this:

```fren
comp c { in n: Int pub out m: Int ensure r: m = match n { 1..=3 => 1, _ => 0 } }
```
"# },
  { code := "F0834", explanation := r#"An or-pattern with `_` among its alternatives (a warning, `wildcard_in_or_patterns`).

Example:

```fren
enum Signal { Stop, Slow, Go }

comp c { in s: Signal pub out m: Int ensure r: m = match s { Signal::Stop => 0, Signal::Slow | _ => 1 } }
```

`_` matches every value, so the other alternatives add nothing. `fren fix`
can fix this:

```fren
enum Signal { Stop, Slow, Go }

comp c { in s: Signal pub out m: Int ensure r: m = match s { Signal::Stop => 0, _ => 1 } }
```
"# },
  { code := "F0835", explanation := r#"A range of a `match` arm that overlaps an earlier arm's pattern, neither within the other (a warning, `match_overlapping_arm`).

Example:

```fren
comp c { in n: Int pub out m: Int ensure r: m = match n { 0..=10 => 1, 5..=15 => 2, _ => 3 } }
```

The integers from 5 to 10 are matched by the first arm, so the second
matches only those from 11 to 15, which its range does not say. Write the
ranges so that they do not overlap, or so that the earlier one is within
the later:

```fren
comp c { in n: Int pub out m: Int ensure r: m = match n { 0..=10 => 1, 11..=15 => 2, _ => 3 } }
```
"# },
  { code := "F0836", explanation := r#"Alternatives of one variant that differ in one value of its payload (`unnested_or_patterns`, allowed by default).

Example:

```fren
set_option fren.lint.unnested_or_patterns "warn"

enum Light { Red, Amber, Green }
enum Lamp { Lit(Light), Dark }

comp c { in l: Lamp pub out m: Int ensure r: m = match l { Lamp::Lit(Light::Red) | Lamp::Lit(Light::Amber) => 1, _ => 0 } }
```

An or-pattern nested in the payload says the same once. `fren fix` can fix
this:

```fren
enum Light { Red, Amber, Green }
enum Lamp { Lit(Light), Dark }

comp c { in l: Lamp pub out m: Int ensure r: m = match l { Lamp::Lit(Light::Red | Light::Amber) => 1, _ => 0 } }
```
"# },
  { code := "F0837", explanation := r#"A `match` on a `Bool` (`match_bool`, allowed by default).

Example:

```fren
set_option fren.lint.match_bool "warn"

comp c { in b? in x: Int pub out m: Int ensure r: m = match b? { true => x, false => 0 } }
```

An `if` says the same. `fren fix` can fix this:

```fren
comp c { in b? in x: Int pub out m: Int ensure r: m = if b? then x else 0 }
```
"# },
  { code := "F0838", explanation := r#"A chain of `if` that picks a value by conditions, as a table does (`manual_table`, allowed by default).

Example:

```fren
set_option fren.lint.manual_table "warn"

comp c { in x: Int pub out m: Int ensure r: m = if x > 10 then 2 else if x < 0 then 1 else 0 }
```

A table lists the cases one row each, and is checked for rows that may
both hold. `fren fix` does not rewrite the chain, since a chain whose tests
overlap would fail that check:

```fren
comp c { in x: Int pub out m: Int ensure r: m = table { x > 10 => 2, x < 0 => 1, _ => 0 } }
```
"# },
  { code := "F0758", explanation := r#"A decimal integer literal with a leading `0`, such as `010` (a warning, `zero_prefixed_literal`).

Example:

```fren
comp c { in x: Int pub out p? ensure r: p? iff x < 010 }
```

In C and some other languages, a leading `0` makes a literal octal, so a
reader may take `010` for 8. In Fren it is decimal, and `010` is 10. Write
it without the leading zeros, or, for octal, with `0o`. `fren fix` can fix
this:

```fren
comp c { in x: Int pub out p? ensure r: p? iff x < 10 }
```
"# },
  { code := "F0779", explanation := r#"A member of a component out of order (`arbitrary_source_item_ordering`, allowed by default).

Example:

```fren
set_option fren.lint.arbitrary_source_item_ordering "warn"

comp c {
    pub out p?
    in x: Int
    ensure r: p? iff x > 0
}
```

The members of a component are written in one order: `use`, `in`,
`assume`, `out`, `inst`, `ensure`, `expect`, then `cover`. `fren fix` can fix this,
unless a definition or a binding would then come before what it mentions:

```fren
comp c {
    in x: Int
    pub out p?
    ensure r: p? iff x > 0
}
```
"# },
  { code := "F0788", explanation := r#"A private defined function applied only once in its file (`single_call_fn`, allowed by default).

Example:

```fren
set_option fren.lint.single_call_fn "warn"

fn double(n: Int): Int := 2 * n

comp c { in x: Int pub out y: Int ensure r: y = double(x) }
```

A function applied once names nothing that is shared. Write its body in
place of the application, with the arguments in place of the parameters:

```fren
comp c { in x: Int pub out y: Int ensure r: y = 2 * x }
```
"# },
  { code := "F0840", explanation := r#"A conjunction that negates each pair of three or more operands (a warning, `manual_at_most_one`).

Example:

```fren
comp c { in a? in b? in c? pub out p? ensure r: p? iff not (a? and b?) and not (a? and c?) and not (b? and c?) }
```

The conjunction says that at most one of the operands holds, which
`at_most_one?` says directly, and without the pair that is easy to miss
among the conjuncts. With the disjunction of the operands as well, as in
`(a? or b? or c?) and ...`, it says that exactly one holds. `fren fix` can
fix this:

```fren
comp c { in a? in b? in c? pub out p? ensure r: p? iff at_most_one?(a?, b?, c?) }
```
"# },
  { code := "F0841", explanation := r#"A membership that names the first or last variants of an ordered enumeration (`manual_ordering`, allowed by default).

Example:

```fren
set_option fren.lint.manual_ordering "warn"

pub ordered enum Level { Low, Mid, High, Top }

comp c { in l: Level pub out p? ensure r: p? iff l in {Level::Low, Level::Mid} }
```

`Level::Low` and `Level::Mid` are the first two variants of `Level`, so the
membership is `l <= Level::Mid`. A chain of `l = V` joined by `or` is a
membership too, and one of `l != V` joined by `and` is the opposite, so
`l != Level::Top and l != Level::High` is `l < Level::High`. The two differ
once a variant is added among the ones named: the comparison takes it in,
and the membership does not, which is why the lint is allowed by default.
`fren fix` can fix this:

```fren
pub ordered enum Level { Low, Mid, High, Top }

comp c { in l: Level pub out p? ensure r: p? iff l <= Level::Mid }
```
"# },
  { code := "F0842", explanation := r#"A newtype built from the field of one, or the field of a newtype just built (a warning, `redundant_newtype_roundtrip`).

Example:

```fren
pub struct Ms(Int)

comp c { in x: Ms pub out y: Ms ensure r: y = Ms(x.0) }
```

`Ms(x.0)` is `x`, when `x` is an `Ms`, and `Ms(n).0` is `n`. Building a
newtype from the field of another, such as `Ms(b.0)` for `b` of `struct
Bytes(Int)`, converts between the two, and is left as it is. `fren fix`
can fix this:

```fren
pub struct Ms(Int)

comp c { in x: Ms pub out y: Ms ensure r: y = x }
```
"# },
  { code := "F0843", explanation := r#"A `min` or `max` with the least or greatest value of an ordered enumeration (a warning, `unnecessary_min_or_max`).

Example:

```fren
pub ordered enum Level { Low, Mid, High }

comp c { in l: Level pub out m: Level ensure r: m = l.max(Level::Low) }
```

No value is below `Level::Low`, so `l.max(Level::Low)` is always `l`, and
`l.min(Level::Low)` always `Level::Low`; with `Level::High`, the last
variant, `min` is always `l` and `max` always `Level::High`. `fren fix` can
fix this:

```fren
pub ordered enum Level { Low, Mid, High }

comp c { in l: Level pub out m: Level ensure r: m = l }
```
"# },
  { code := "F0810", explanation := r#"An `Int` that a constraint keeps at least 0 (a warning, `manual_nat`).

Example:

```fren
comp c { in n: Int pub out m: Int assume counts: n >= 0 ensure r: m = n + 1 }
```

A `Nat` input brings the assumption that it is at least 0 with its type,
and a `Nat` output the guarantee. Declare the variable a `Nat`, and
remove its bound, or the constraint if nothing else is left of it.
`fren fix` leaves this to the writer, since an instance or a refinement
in another file may need the `Int`:

```fren
comp c { in n: Nat pub out m: Int ensure r: m = n + 1 }
```

An instance must then bind the input to a `Nat`, since an `Int` is never
narrowed, so the lint does not fire where an instance or a refinement in
the same file keeps the variable an `Int`.
"# },
  { code := "F0811", explanation := r#"A conditional that is the absolute value (a warning, `manual_abs`).

Example:

```fren
comp c { in x: Int pub out y: Int ensure r: y = if x < 0 then -x else x }
```

`if x < 0 then -x else x`, and its forms with `<=`, `>`, `>=` and the
branches swapped, are `x.abs`. `fren fix` can fix this:

```fren
comp c { in x: Int pub out y: Int ensure r: y = x.abs }
```
"# },
  { code := "F0812", explanation := r#"A conditional that is the absolute value of a difference (a warning, `manual_abs_diff`).

Example:

```fren
comp c { in a: Int in b: Int pub out y: Int ensure r: y = if a > b then a - b else b - a }
```

`if a > b then a - b else b - a`, and its forms with `>=`, `<`, `<=` and
the branches swapped, are `(a - b).abs`. `fren fix` can fix this:

```fren
comp c { in a: Int in b: Int pub out y: Int ensure r: y = (a - b).abs }
```
"# },
  { code := "F0813", explanation := r#"A conditional that is `min` or `max` (a warning, `manual_min_max`).

Example:

```fren
comp c { in a: Int in b: Int pub out y: Int ensure r: y = if a < b then a else b }
```

`if a < b then a else b` is `a.min(b)`, and `if a < b then b else a` is
`a.max(b)`, and so with `<=`, `>` and `>=`. `fren fix` can fix this:

```fren
comp c { in a: Int in b: Int pub out y: Int ensure r: y = a.min(b) }
```
"# },
  { code := "F0814", explanation := r#"A conditional that keeps its operand between two bounds (a warning, `manual_clamp`).

Example:

```fren
comp c { in x: Int pub out y: Int ensure r: y = if x < 0 then 0 else if x > 9 then 9 else x }
```

Where the bounds are integer literals, the lower at most the upper, the
conditional is `x.max(0).min(9)`. `fren fix` can fix this:

```fren
comp c { in x: Int pub out y: Int ensure r: y = x.max(0).min(9) }
```
"# },
  { code := "F0815", explanation := r#"A remainder made non-negative by hand (a warning, `manual_rem_euclid`).

Example:

```fren
comp c { in x: Int pub out y: Int ensure r: y = (x mod 7 + 7) mod 7 }
```

`mod` is Euclidean: `x mod 7` is between 0 and 6 even where `x` is
negative, so adding the divisor and taking the remainder again changes
nothing. `fren fix` can fix this:

```fren
comp c { in x: Int pub out y: Int ensure r: y = x mod 7 }
```
"# },
  { code := "F0816", explanation := r#"A remainder by `1` or `-1` (a warning, `modulo_one`).

Example:

```fren
comp c { in x: Int pub out even? ensure r: even? iff x mod 1 = 0 }
```

Every integer is a multiple of `1`, so `x mod 1` is always `0`. The
divisor is probably not the one meant:

```fren
comp c { in x: Int pub out even? ensure r: even? iff x mod 2 = 0 }
```
"# },
  { code := "F0817", explanation := r#"A `min` and a `max` whose bounds leave one value (a warning, `min_max`).

Example:

```fren
comp c { in x: Int pub out y: Int ensure r: y = x.min(0).max(9) }
```

`x.min(0)` is at most 0, so its `max` with 9 is always 9; so too
`x.max(9).min(0)` is always 0. The bounds are probably swapped:

```fren
comp c { in x: Int pub out y: Int ensure r: y = x.max(0).min(9) }
```
"# },
  { code := "F0818", explanation := r#"A record literal that copies most of its fields from one value (a warning, `manual_record_update`).

Example:

```fren
struct Point { x: Int, y: Int, z: Int }

comp c { in p: Point pub out q: Point ensure r: q = Point { x := 0, y := p.y, z := p.z } }
```

The literal gives `x` a new value and reads `y` and `z` from `p`. The
update `{ p with x := 0 }` means the same, reads every field it does not
give from `p`, and stays right when a field is added. It fires when more
fields are copied than are given new values. `fren fix` can
fix this:

```fren
struct Point { x: Int, y: Int, z: Int }

comp c { in p: Point pub out q: Point ensure r: q = { p with x := 0 } }
```
"# },
  { code := "F0819", explanation := r#"A record update that gives every field (a warning, `needless_update`).

Example:

```fren
struct Point { x: Int, y: Int }

comp c { in p: Point pub out q: Point ensure r: q = { p with x := 0, y := 1 } }
```

The update reads nothing from `p`: it is the record literal of the same
fields. Write the literal, or leave out the fields that should keep `p`'s
values:

```fren
struct Point { x: Int, y: Int }

comp c { in p: Point pub out q: Point ensure r: q = Point { x := 0, y := 1 } }
```
"# },
  { code := "F0820", explanation := r#"A cover goal that some behaviour meets whatever the component says (a warning, `trivial_cover`).

Example:

```fren
comp c {
    in x: Int
    pub out y: Int
    ensure r: y = x + 1
    cover big: when x > 10, y > 11
}
```

A cover goal with a trigger holds wherever the trigger is false, so a
behaviour with `x <= 10` meets it. The lint also fires on a goal written
the same as an assumption or a guarantee, which every behaviour that
meets the component satisfies. Write the scenario as a conjunction:

```fren
comp c {
    in x: Int
    pub out y: Int
    ensure r: y = x + 1
    cover big: x > 10 and y > 11
}
```
"# },
  { code := "F0824", explanation := r#"A `let` or `where` clause whose body is the name of its last definition (a warning, `let_and_return`).

Example:

```fren
comp c { in x: Int pub out y: Int ensure r: y = (let d := x + 1 in d) }
```

The name says nothing that its definition does not, since nothing else
mentions it. Write the definition in place of the name, and drop the
definition, or the clause if it has no other. `fren fix` can fix this:

```fren
comp c { in x: Int pub out y: Int ensure r: y = x + 1 }
```
"# },
  { code := "F0825", explanation := r#"A definition `x! := x` of a `let` or `where` clause (a warning, `redundant_locals`).

Example:

```fren
comp c { in x: Int pub out y: Int ensure r: y = (let x! := x in x + 1) }
```

The definition names the value that `x` already has, so `x` means the
same with it and without it; perhaps another expression was meant. Remove
the definition, or the clause if it has no other. `fren fix` can fix this:

```fren
comp c { in x: Int pub out y: Int ensure r: y = x + 1 }
```
"# },
  { code := "F0826", explanation := r#"A run of `and` or `or` whose operands are one expression at each variant of an enumeration (a warning, `manual_forall`).

Example:

```fren
enum Mode { Heat, Cool, Off }

comp c { in s: Set<Mode> pub out p? ensure r: p? iff Mode::Heat in s and Mode::Cool in s and Mode::Off in s }
```

A `forall` over the enumeration says the same once, and an `exists` for
a run of `or`. It fires on three or more operands that name each variant
once, in a constraint without indexes or tables, whose guards the
quantifier might change. `fren fix` can fix this:

```fren
enum Mode { Heat, Cool, Off }

comp c { in s: Set<Mode> pub out p? ensure r: p? iff (forall (mode: Mode), mode in s) }
```
"# },
  { code := "F0827", explanation := r#"A quantifier over a type of one value (a warning, `trivial_quantifier`).

Example:

```fren
enum Solo { Only }

comp c { in s: Set<Solo> pub out p? ensure r: p? iff (forall (u: Solo), u in s) }
```

A `forall` or an `exists` over a type of one value is its body at that
value. Write the body with the value in place of the bound name. `fren
fix` can fix this, for a variant without a payload:

```fren
enum Solo { Only }

comp c { in s: Set<Solo> pub out p? ensure r: p? iff Solo::Only in s }
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
