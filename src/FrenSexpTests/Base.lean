module

public import FrenSexp.Name
meta import FrenSexp.Name

namespace Fren.SexpTests

open Sexp

private def ensure (ok : Bool) (message : String) : Except String Unit :=
  if ok then pure () else .error message

private def isResult [BEq α] (result : Except ε α) (value : α) : Bool :=
  match result with
  | .ok actual => actual == value
  | .error _ => false

private def failed (result : Except ε α) : Bool :=
  match result with
  | .ok _ => false
  | .error _ => true

private def roundTrip [ToSexp α] [FromSexp α] [BEq α] (value : α) :
    Except String Unit := do
  let text := encode value
  match fromSexp (toSexp value), decode (α := α) text with
  | .ok direct, .ok parsed =>
    ensure (direct == value && parsed == value) s!"round trip: {text}"
  | _, _ => .error s!"decode failed: {text}"

private def syntaxError (text : String) (position : Position)
    (expected : String) : Except String Unit := do
  match parse text with
  | .error e =>
    ensure (e.position == position && e.expected == expected)
      s!"syntax error for {repr text}: {repr e}"
  | .ok _ => .error s!"accepted invalid input: {repr text}"

private def typeError [FromSexp α] (_ : α → α) (text : String)
    (position : Position) (expected : String) : Except String Unit := do
  match decode (α := α) text with
  | .error e =>
    ensure (e.position == position && e.expected == expected)
      s!"type error for {repr text}: {repr e}"
  | .ok _ => .error s!"accepted invalid typed input: {repr text}"

private def parserTests : Except String Unit := do
  for n in [:128] do
    let c := Char.ofNat n
    let accepted := c.isAlpha || c.isDigit || "_-.:@/+".contains c
    ensure (isAtomChar c == accepted) s!"atom alphabet: {n}"
  for text in ["", "a b", "é", "😀", "a;b", "a\\b", "a(b)"] do
    ensure (Atom.ofString? text |>.isNone) s!"invalid atom: {text}"
  let specimen := "(prim add_int ((widen nat_int (bvar 1)) (bvar 0)) (ty int))"
  match parse ("; input only\n" ++ specimen ++ "; trailing comment") with
  | .ok value => ensure (render value == specimen) "issue example"
  | .error e => .error s!"issue example: {e}"
  ensure (isResult (parse "(; comment\n)") (.list #[])) "empty list/comment"
  ensure (isResult (parse "\t\r\n (a(b)\"c\") ")
    (.list #[symbol "a", .list #[symbol "b"], .string "c"]))
    "token boundaries/whitespace"
  ensure (render (.string "é😀\"\\\n\t\r") == "\"é😀\\\"\\\\\\n\\t\r\"")
    "exact string escaping"
  roundTrip "\u0000é😀;()\"\\\n\t\r«»"
  ensure (isResult (parse "\"a\nb\"") (.string "a\nb")) "literal LF in input"
  syntaxError "" {} "an atom, string or list"
  syntaxError ";é" { byteOffset := 3, column := 3 } "an atom, string or list"
  syntaxError "(a\n" { byteOffset := 3, line := 2, column := 1 }
    "a closing parenthesis"
  syntaxError "\"é😀\\q\"" { byteOffset := 8, column := 5 }
    "a string escape (quote, backslash, n or t)"
  syntaxError "\"é" { byteOffset := 3, column := 3 } "a closing double quote"
  syntaxError "\"\\" { byteOffset := 2, column := 3 }
    "a string escape (quote, backslash, n or t)"
  for text in [")", "é", "😀", "#", "'", "[a]"] do
    syntaxError text {} "an atom, string or list"
  for text in ["\"\\r\"", "\"\\u0041\"", "\"\\0\""] do
    syntaxError text { byteOffset := 2, column := 3 }
      "a string escape (quote, backslash, n or t)"
  syntaxError "a b" { byteOffset := 2, column := 3 } "end of input"
  syntaxError "(a !b)" { byteOffset := 3, column := 4 } "an atom, string or list"
  syntaxError "(\"é\n😀\" !)" { byteOffset := 11, line := 2, column := 4 }
    "an atom, string or list"

private def baseTests : Except String Unit := do
  roundTrip ()
  ensure (encode (some ()) == "(some unit)") "Unit field must remain present"
  for n in [0, 1, 9, 10, 123456789012345678901234567890] do roundTrip n
  for n in ([-123456789012345678901234567890, -1, 0, 1, 99] : List Int) do
    roundTrip n
  roundTrip true
  roundTrip false
  roundTrip (none : Option (Array Nat))
  roundTrip (some #[0, 1, 100])
  roundTrip (#[some #["é", "😀"], none, some #[]] : Array (Option (Array String)))
  roundTrip (#[] : Array Unit)
  ensure (isResult (decode (α := Nat) "00042") 42) "noncanonical decimal input"
  ensure (isResult (decode (α := Int) "-0") 0) "negative zero"
  for text in ["+1", "-1", "1_0", "1.0", "\"1\"", "(1)"] do
    typeError (id : Nat → Nat) text {} "a natural numeral"
  for text in ["+1", "-", "--1", "1_0", "\"-1\""] do
    typeError (id : Int → Int) text {} "an integer numeral"
  typeError (id : Unit → Unit) "()" {} "unit"
  typeError (id : Bool → Bool) "True" {} "true or false"
  typeError (id : String → String) "word" {} "a string"
  typeError (id : Array Nat → Array Nat) "none" {} "a list of array elements"
  for text in ["(none)", "(some)", "(some 1 2)"] do
    typeError (id : Option Nat → Option Nat) text {} "none or (some value)"
  typeError (id : Option Nat → Option Nat) "(other 1)"
    { byteOffset := 1, column := 2 } "some"
  typeError (id : Array (Option Nat) → Array (Option Nat))
    "(\n (some 2)\n (some nope))" { byteOffset := 19, line := 3, column := 8 }
    "a natural numeral"
  typeError (id : Array String → Array String) "; café\n(\"é😀\" bad)"
    { byteOffset := 18, line := 2, column := 7 } "a string"

private def constructorTests : Except String Unit := do
  for (source, target) in [("toBV", "to_bv"), ("ofNat2", "of_nat2"),
      ("ABC", "abc"), ("fooBar", "foo_bar"), ("foo_bar", "foo_bar"),
      ("x2Y", "x2_y"), ("URLValue", "urlvalue"), ("Unit", "unit")] do
    match constructorAtom (.str (.str .anonymous "Ignored") source) with
    | .ok a => ensure (a.val == target) s!"constructor: {source}"
    | .error e => .error e
  for name in [Lean.Name.anonymous, .num .anonymous 1,
      .str .anonymous "1foo", .str .anonymous "", .str .anonymous "é"] do
    ensure (failed (constructorAtom name)) "invalid constructor name"

private def nameTests : Except String Unit := do
  ensure (encode (`lang.scope.resolve : Lean.Name) == "lang.scope.resolve") "dotted name"
  ensure (encode (Lean.Name.str .anonymous "a.b") == "\"«a.b»\"") "dot in component"
  ensure (encode (Lean.Name.num `a 12) == "\"a.12\"") "numeric component"
  ensure (encode (Lean.Name.str `a "12") == "\"a.«12»\"") "numeric string component"
  ensure (encode Lean.Name.anonymous == "\"\"") "anonymous name"
  ensure (encode (Lean.Name.str .anonymous "") == "\"«»\"") "empty component"
  ensure (isResult (decode (α := Lean.Name) "\"12\"") (.num .anonymous 12))
    "numeric root component"
  ensure (isResult (decode (α := Lean.Name) "\"«12»\"") (.str .anonymous "12"))
    "quoted digit strings remain strings"
  let pieces := #["simple", "12", "", ".", "a.b", "a b", "a-b:@/+_", "é😀",
    "«", "»", "a»b", "\\", "\\»", "\";()", "\n\t\r", "_", "#0", "?u"]
  for first in pieces do
    let parent := Lean.Name.str .anonymous first
    roundTrip parent
    roundTrip (.num parent 0 : Lean.Name)
    for second in pieces do roundTrip (Lean.Name.str parent second)
  roundTrip (Lean.Name.num (.num .anonymous 42) 7)
  for text in ["\"a.\"", "\".a\"", "\"a..b\"", "\"«a\"", "\"«a»b\"",
      "\"«a\\\\q»\"", "\"«a\\\\\""] do
    ensure (failed (decode (α := Lean.Name) text)) s!"invalid name: {text}"

/-- Compare map contents, independent of buckets and iteration order. -/
private def sameMap [BEq κ] [Hashable κ] [BEq ν]
    (a b : Std.HashMap κ ν) : Bool :=
  a.size == b.size && a.toArray.all (fun (k, v) => b[k]? == some v)

private def mapTests : Except String Unit := do
  let entries := #[("é", 1), ("z", 2), ("😀", 3), ("a", 4), ("\n", 5), ("\"", 6)]
  let a := Std.HashMap.ofArray entries
  let b := Std.HashMap.ofArray entries.reverse
  ensure (sameMap a b) "map equality ignores insertion order"
  let text := "((\"\\\"\" 6) (\"\\n\" 5) (\"a\" 4) (\"z\" 2) (\"é\" 1) (\"😀\" 3))"
  ensure (encode a == text && encode b == text) "bytewise canonical map order"
  match fromSexp (toSexp a), decode (α := Std.HashMap String Nat) text with
  | .ok direct, .ok parsed =>
    ensure (sameMap a direct && sameMap a parsed) "map contents round trip"
  | _, _ => .error "map decoding"
  let numeric := Std.HashMap.ofArray #[(2, "two"), (10, "ten"), (1, "one")]
  ensure (encode numeric == "((1 \"one\") (10 \"ten\") (2 \"two\"))")
    "map sorting uses rendered keys, not numeric order"
  let empty : Std.HashMap Lean.Name (Option Unit) := {}
  ensure (encode empty == "()") "empty map"
  let names := empty.insert (Lean.Name.str `a "x.y") (some ()) |>.insert (.num `a 0) none
  match decode (α := Std.HashMap Lean.Name (Option Unit)) (encode names) with
  | .ok parsed => ensure (sameMap names parsed) "map with structured names and Unit"
  | .error e => .error s!"name map: {e}"
  typeError (id : Std.HashMap Nat String → Std.HashMap Nat String)
    "((1 \"é\")\n (01 \"x\"))" { byteOffset := 12, line := 2, column := 3 }
    "a unique map key"
  typeError (id : Std.HashMap Nat String → Std.HashMap Nat String)
    "((1 3))" { byteOffset := 4, column := 5 } "a string"
  typeError (id : Std.HashMap Nat String → Std.HashMap Nat String)
    "((1))" { byteOffset := 1, column := 2 } "a (key value) pair"

private def layoutTests : Except String Unit := do
  let text n := String.ofList (List.replicate n 'x')
  let at80 := Sexp.list #[symbol "f", .string (text 74)]
  ensure ((render at80).length == 80 && pretty at80 == render at80) "80-column boundary"
  let at81 := Sexp.list #[symbol "f", .string (text 75)]
  ensure (pretty at81 == "(f\n  \"" ++ text 75 ++ "\")") "81-column break"
  let closing := Sexp.list #[symbol "f", .string (text 76)]
  ensure (pretty closing == "(f\n  \"" ++ text 76 ++ "\"\n)")
    "closing parenthesis also respects the column limit"
  let unicode := Sexp.list #[symbol "f", .string (String.ofList (List.replicate 74 'é'))]
  ensure (pretty unicode == render unicode) "layout counts characters, not UTF-8 bytes"
  let nested := Sexp.list #[symbol "root", .list #[symbol "child", .string (text 70)],
    .list #[symbol "tail", .string "é😀"]]
  ensure (pretty nested == "(root\n  (child\n    \"" ++ text 70 ++ "\")\n  (tail \"é😀\"))")
    "nested layout counts indentation"
  let mut values := #[symbol "a", symbol "_-.:@/+", .list #[], .string "é😀\n\t\\\"", nested]
  for n in [:30] do
    let value := Sexp.list #[symbol "node", toSexp n, values[n % values.size]!]
    values := values.push value
  for value in values do
    ensure (isResult (parse (render value)) value) "AST one-line round trip"
    ensure (isResult (parse (pretty value)) value) "AST indented round trip"

/-- Build-time assertions; the same suite can also be called by an offline probe. -/
public def run : IO Unit := do
  let start ← IO.monoMsNow
  match parserTests *> baseTests *> constructorTests *> nameTests *> mapTests *> layoutTests with
  | .ok () =>
    let elapsed := (← IO.monoMsNow) - start
    IO.println s!"S-expression base tests passed ({elapsed} ms)"
  | .error e => throw (IO.userError e)

#eval run

end Fren.SexpTests
