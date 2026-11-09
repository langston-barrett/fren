import Fren.Impl
import Fren.Literate
import FrenParse
import Spec.Language.LexicalStructure

open Fren.Lang

#fren_md "Syntax.md"

#fren_check

namespace Spec.Language.Syntax

open FrenAst
open spec.grammar (Operator Separated Place Grouping)

/-! The chapter's checks run the actual parser, `FrenParse.parse`, and compare
it with the chapter's grammar and with its Fren definitions, run as written. -/

/-- A tree as text, with each operator, call and paren explicit. -/
partial def shape : Expr → String
  | .name path => "::".intercalate (path.tokens.filter (·.text != "::") |>.map (·.text))
  | .bool _ b => toString b
  | .integer _ n => toString n
  | .paren _ body _ => s!"(paren {shape body})"
  | .unary t _ body => s!"({t.text} {shape body})"
  | .binary l t _ r => s!"({t.text} {shape l} {shape r})"
  | .call f _ args _ _ => "(call " ++ shape f ++ (args.foldl (fun s e => s ++ " " ++ shape e) "") ++ ")"
  | .ifE _ c _ y _ n => s!"(if {shape c} {shape y} {shape n})"
  | .letE _ x _ v _ b => s!"(let {x.text} {shape v} {shape b})"
  | .matchE _ s _ arms _ => "(match " ++ shape s ++
      (arms.foldl (fun acc arm => acc ++ " (" ++ "".intercalate (arm.1.tokens.map (·.text)) ++
        " " ++ shape arm.2.2.1 ++ ")") "") ++ ")"

/-- The tree of an expression entry, or `none` if it is rejected. -/
def expr? (source : String) : Option String :=
  match FrenParse.parseExpression ⟨0⟩ source with
  | .ok { root := .expression e, .. } => some (shape e)
  | _ => none

def accepts (source : String) : Bool := (FrenParse.parseFile ⟨0⟩ source).toBool
def acceptsExpr (source : String) : Bool := (expr? source).isSome

/-- Every operator. `all_operators` proves the list complete. -/
def operators : List Operator :=
  [.Iff, .Or, .And, .Not, .Equal, .NotEqual, .Less, .LessEqual, .Greater, .GreaterEqual,
   .Add, .Subtract, .Multiply, .Divide, .Remainder, .Negate]

theorem all_operators (op : Operator) : op ∈ operators := by
  cases op <;> simp [operators]

def spelling (op : Operator) : String := spec.grammar.spelling op
def precedence (op : Operator) : Int := spec.grammar.precedence op
def isPrefix (op : Operator) : Bool := spec.grammar.«prefix?» op
def binaries : List Operator := operators.filter (!isPrefix ·)
def prefixes : List Operator := operators.filter isPrefix

/-- The AST's operator for a binary `Operator`. -/
def astBinary : Operator → Option BinaryOp
  | .Iff => some .iff | .Or => some .or | .And => some .and
  | .Equal => some .eq | .NotEqual => some .ne | .Less => some .lt | .LessEqual => some .le
  | .Greater => some .gt | .GreaterEqual => some .ge | .Add => some .add | .Subtract => some .sub
  | .Multiply => some .mul | .Divide => some .div | .Remainder => some .mod
  | .Not | .Negate => none

/-- Every token spelling that the lexer can give a punctuator, keyword or
contextual word; `operators_agree` checks these lists against the lexical
chapter's sets. -/
def punctuators : List String :=
  ["(", ")", "{", "}", ",", ":", "+", "-", "*", "=", "<", ">", "<=", ">=", "!=", ":=", "=>", "::"]
def grammarKeywords : List String :=
  ["mod", "pub", "enum", "fn", "expect", "iff", "and", "or", "div", "in", "if", "then", "else",
   "match", "let"]
def contextual : List String := ["assume", "not", "true", "false", "Bool", "Int"]

--@ reference: syntax.operator.table
/-- `syntax.operator.table`: the parser's binary operator table is the
chapter's, spelling for spelling and precedence for precedence, and no other
punctuator, keyword or contextual word, nor sample identifier, is a binary
operator. Its prefix operators are those of the table: each prefix
spelling, applied to a name, gives a unary node. -/
def operators_agree : Bool :=
  decide (spec.lexical.PUNCTUATORS = Fren.FinSet.ofList punctuators) &&
  decide (spec.lexical.GRAMMAR_KEYWORDS = Fren.FinSet.ofList grammarKeywords) &&
  decide (spec.lexical.CONTEXTUAL = Fren.FinSet.ofList contextual) &&
  binaries.all (fun op =>
    match FrenParse.binaryOperator (spelling op), astBinary op with
    | some (ast, p), some expected => ast == expected && (p : Int) == precedence op
    | _, _ => false) &&
  (punctuators ++ grammarKeywords ++ contextual ++ ["x", "_", "mod?", "div?", "1"]).all (fun s =>
    (FrenParse.binaryOperator s).isSome == binaries.any (spelling · == s)) &&
  prefixes.all (fun op => expr? (spelling op ++ " x") == some s!"({spelling op} x)")

#guard operators_agree

/-- The AST's prefix operator for an `Operator`. -/
def astUnary : Operator → Option UnaryOp
  | .Not => some .not | .Negate => some .neg
  | _ => none

/-- Whether the parser reads `spelling op` as the binary operator `op`. -/
def readsBinary (op : Operator) : Bool :=
  match FrenParse.binaryOperator (spelling op), astBinary op with
  | some (ast, _), some expected => ast == expected
  | _, _ => false

/-- The parser's precedence for `spelling op`, or 0 if it is no binary operator. -/
def readLevel (op : Operator) : Int :=
  ((FrenParse.binaryOperator (spelling op)).map fun (_, p) => (p : Int)).getD 0

/-- Whether the parser reads `spelling op` before an operand as the prefix operator `op`. -/
def readsUnary (op : Operator) : Bool :=
  match FrenParse.parseExpression ⟨0⟩ (spelling op ++ " x") with
  | .ok { root := .expression (.unary _ u (.name _)), .. } => some u == astUnary op
  | _ => false

--@ reference: syntax.operator.table
/- The parser's own table and prefix reading, bound to the chapter's operator
table for every operator. `FrenParse` does not expose these definitions'
bodies to the kernel, so each operator's case is evaluated by the compiled
parser (`native_decide`). -/
impl operator_reading: operator_reading for (op : Operator) {
  op := op, unary? := readsUnary op, binary? := readsBinary op, level := readLevel op
} by
  intro op _
  cases op <;> simp [fren_spec] <;> native_decide

/-- The tree that `grouping` gives `x first y second z` (or `first y second z`). -/
def groupingShape (first second : Operator) : Option String :=
  let (a, b) := (spelling first, spelling second)
  let left := if isPrefix first then s!"({a} y)" else s!"({a} x y)"
  match spec.grammar.grouping first second with
  | .Right => some (if isPrefix first then s!"({a} ({b} y z))" else s!"({a} x ({b} y z))")
  | .Left => some s!"({b} {left} z)"
  | .Rejected => none

def groupingSource (first second : Operator) : String :=
  (if isPrefix first then "" else "x ") ++ s!"{spelling first} y {spelling second} z"

--@ reference: syntax.operator.grouping
--@ reference: syntax.operator.non-associative
--@ reference: syntax.expression.extent
/-- `syntax.operator.grouping`, `syntax.operator.non-associative` and
`syntax.expression.extent`: for every operator followed by every binary
operator, the parser builds the tree that `grouping` gives, or rejects the
text when it says `Rejected`; for every operator followed by every prefix
operator, the parser accepts exactly what `admitted?` admits. -/
def groupings_agree : Bool :=
  operators.all (fun first =>
    binaries.all (fun second => expr? (groupingSource first second) == groupingShape first second) &&
    prefixes.all (fun second =>
      let source := (if isPrefix first then "" else "x ") ++ s!"{spelling first} {spelling second} y"
      acceptsExpr source ==
        spec.grammar.«admitted?» second (spec.grammar.operand_level first))) &&
  -- The longest extent of an `if`'s else branch and of a `let` body.
  expr? "a + if b then c else d + e" == some "(+ a (if b c (+ d e)))" &&
  expr? "x * let y := 1 in y + 2" == none &&
  expr? "(let y := 1 in y + 2) * x" == some "(* (paren (let y 1 (+ y 2))) x)" &&
  expr? "(a < b) <= c" == some "(<= (paren (< a b)) c)" &&
  expr? "a iff (b iff c)" == some "(iff a (paren (iff b c)))" &&
  -- The chapter's operator examples.
  expr? "base + 5 * 2" == some "(+ base (* 5 2))" && expr? "base - 5 - 2" == some "(- (- base 5) 2)" &&
  expr? "-x * 2" == some "(* (- x) 2)" && expr? "not x = y and true" == some "(and (not (= x y)) true)" &&
  expr? "a or b and c iff d" == some "(iff (or a (and b c)) d)" && expr? "- - x" == some "(- (- x))" &&
  expr? "a + not b" == none && expr? "-not b" == none && expr? "not a and b" == some "(and (not a) b)"

#guard groupings_agree

/-- A text that places `e` at `place`. -/
def placed (place : Place) (e : String) : String :=
  match place with
  | .Full => s!"fn f(w: Int): Int := {e}"
  | .Definition => s!"fn f(w: Int): Int := let v := {e} in v"
  | .ArmBody => s!"fn f(w: Int): Int := match w \{ E::A => {e} }"
  | .Scrutinee => s!"fn f(w: Int): Int := match {e} \{ E::A => 1 }"

--@ reference: syntax.expression.places
/-- `syntax.expression.places`: at each place, the parser accepts a bare
`let`, each prefix operator and each binary operator exactly as
`place_level`, `let_admitted?` and `admitted?` say, and always accepts a
`Primary`. -/
def places_agree : Bool :=
  [Place.Full, .Definition, .ArmBody, .Scrutinee].all fun place =>
    let level := spec.grammar.place_level place
    accepts (placed place "let u := w in u") == spec.grammar.«let_admitted?» level &&
    operators.all (fun op =>
      let e := if isPrefix op then s!"{spelling op} w" else s!"w {spelling op} w"
      accepts (placed place e) == spec.grammar.«admitted?» op level) &&
    ["w", "1", "true", "E::A", "g(w)", "(w + 1)", "if w then w else w", "match w { E::A => w }"].all
      (accepts <| placed place ·)

#guard places_agree

/-- A list of `items` items of `list`, then a comma if `trailing`. -/
def listSource (list : Separated) (items : Nat) (trailing : Bool) : String :=
  let (item, wrap) : String × (String → String) := match list with
    | .FunctionParameters => ("x: Int", fun s => s!"fn f({s}): Int := 1")
    | .ExpectationParameters => ("x: Int", fun s => s!"expect e({s}) \{}")
    | .Arguments => ("x", fun s => s!"fn f(x: Int): Int := g({s})")
    | .Variants => ("A", fun s => s!"enum E \{ {s} }")
    | .Arms => ("E::A => 1", fun s => s!"fn f(x: Int): Int := match x \{ {s} }")
  let items := ", ".intercalate (List.replicate items item)
  wrap (items ++ if trailing then "," else "")

--@ reference: syntax.list.policy
/-- `syntax.list.policy`: each list accepts zero, one, two or three items,
with or without a trailing comma, exactly as `accepts?` says. -/
def lists_agree : Bool :=
  [Separated.FunctionParameters, .ExpectationParameters, .Arguments, .Variants, .Arms].all fun list =>
    [0, 1, 2, 3].all fun items => [false, true].all fun trailing =>
      accepts (listSource list items trailing) == spec.grammar.«accepts?» list items trailing

#guard lists_agree

def typeShape : Ty → String
  | .bool _ => "Bool!"
  | .int _ => "Int!"
  | .named p => "".intercalate (p.tokens.map (·.text))

/-- The declarations of a file, as their kinds and names. -/
def declarations? (source : String) : Option (List String) :=
  match FrenParse.parseFile ⟨0⟩ source with
  | .ok { root := .declarations ds, .. } => some <| ds.toList.map fun
    | .moduleDecl v _ p => s!"{if v.isSome then "pub " else ""}mod " ++ "".intercalate (p.tokens.map (·.text))
    | .enumDecl v _ n _ vs _ _ =>
      s!"{if v.isSome then "pub " else ""}enum {n.text} " ++ ",".intercalate (vs.toList.map (·.text))
    | .function v _ n ps _ r _ b =>
      let param : Parameter → String := fun p =>
        p.name.text ++ (p.annotation.map (fun (_, t) => ":" ++ typeShape t)).getD ""
      s!"{if v.isSome then "pub " else ""}fn {n.text}(" ++ ",".intercalate (ps.values.toList.map param) ++
        s!"):{typeShape r} {shape b}"
    | .expectation _ n ps _ ms _ =>
      s!"expect {n.text}/{ps.values.size} " ++
        ";".intercalate (ms.toList.map fun m => s!"{m.keyword.text} {m.label.text} {shape m.body}")
  | _ => none

--@ reference: syntax.notation.trivia-sensitive
--@ reference: syntax.file.syntax
--@ reference: syntax.file.entry
--@ reference: syntax.path.syntax
--@ reference: syntax.path.contextual
--@ reference: syntax.type.syntax
--@ reference: syntax.module.syntax
--@ reference: syntax.enumeration.syntax
--@ reference: syntax.function.syntax
--@ reference: syntax.function.parameter
--@ reference: syntax.expectation.syntax
--@ reference: syntax.expression.syntax
--@ reference: syntax.literal.syntax
--@ reference: syntax.call.syntax
--@ reference: syntax.if.syntax
--@ reference: syntax.let.syntax
--@ reference: syntax.match.syntax
--@ reference: syntax.remainder.line
/-- The grammar's productions, each with texts that it accepts, with their
trees, and texts that it rejects. -/
def productions_agree : Bool :=
  -- `syntax.file.syntax` and `syntax.file.entry`
  declarations? "" == some [] && declarations? " -- only trivia\r\n" == some [] &&
  expr? "" == none && expr? "-- only trivia" == none &&
  expr? "x y" == none && declarations? "fn f(x: Int): Int := x x" == none &&
  declarations? "mod m pub mod n" == some ["mod m", "pub mod n"] &&
  -- `syntax.path.syntax`
  expr? "A::B::c" == some "A::B::c" && expr? "A::" == none && expr? "::a" == none &&
  -- `syntax.path.contextual`
  declarations? "enum E { Int, Bool, not, assume, true, false }" ==
    some ["enum E Int,Bool,not,assume,true,false"] &&
  declarations? "fn assume(not: Int, true: Int): Int := assume" == some ["fn assume(not:Int!,true:Int!):Int! assume"] &&
  expr? "E::true" == some "E::true" && expr? "true::x" == none && expr? "not::x" == none &&
  expr? "Bool::x" == some "Bool::x" && expr? "match x { true::A => 1 }" == some "(match x (true::A 1))" &&
  expr? "proc" == none && expr? "forall" == none && expr? "where" == none &&
  -- `syntax.type.syntax`
  declarations? "fn f(a: Bool, b: Int, c: E, d: Int::T, e: A::Int): Bool := a" ==
    some ["fn f(a:Bool!,b:Int!,c:E,d:Int::T,e:A::Int):Bool! a"] &&
  declarations? "fn f(x: Int::): Int := 1" == none &&
  -- `syntax.module.syntax`
  declarations? "pub mod a::b" == some ["pub mod a::b"] && declarations? "mod" == none &&
  -- `syntax.enumeration.syntax`
  declarations? "pub enum E { A, B, }" == some ["pub enum E A,B"] &&
  declarations? "enum E { A B }" == none && declarations? "enum E { A::B }" == none &&
  -- `syntax.function.syntax` and `syntax.function.parameter`
  declarations? "fn f(b?): Bool := b?" == some ["fn f(b?):Bool! b?"] &&
  declarations? "fn f(b?: Int): Int := 1" == some ["fn f(b?:Int!):Int! 1"] &&
  declarations? "fn f(b): Bool := b" == none && declarations? "fn f(x: Int) := x" == none &&
  declarations? "fn f(x: Int): Int" == none && declarations? "pub fn f(x: Int): Int := " == none &&
  -- `syntax.expectation.syntax`
  declarations? "expect e() {}" == some ["expect e/0 "] &&
  declarations? "expect e(x: Int,) { assume a: x > 0 expect b: x >= 0 }" ==
    some ["expect e/1 assume a (> x 0);expect b (>= x 0)"] &&
  declarations? "pub expect e() {}" == none && declarations? "expect e() { ensure a: true }" == none &&
  declarations? "expect e() { expect a true }" == none &&
  -- `syntax.notation.trivia-sensitive` and `syntax.call.syntax`
  ([" ", "\t", "\n", "\r\n", " -- c\n"].all fun gap =>
    expr? ("f" ++ gap ++ "(x)") == none && expr? ("A::f" ++ gap ++ "(x)") == none &&
    declarations? ("fn f" ++ gap ++ "(x: Int): Int := x") == none &&
    declarations? ("expect e" ++ gap ++ "() {}") == none &&
    expr? ("1 +" ++ gap ++ "(x)") == some "(+ 1 (paren x))") &&
  expr? "f(g(x), h(y))" == some "(call f (call g x) (call h y))" && expr? "unknown(x)" == some "(call unknown x)" &&
  expr? "f(x)(y)" == none && expr? "(f)(x)" == none && expr? "1(x)" == none &&
  expr? "f(let x := 1 in x)" == some "(call f (let x 1 x))" &&
  -- `syntax.literal.syntax`
  expr? "-1" == some "(- 1)" && expr? "true" == some "true" && expr? "x < -1" == some "(< x (- 1))" &&
  -- `syntax.if.syntax`
  expr? "if b then 1 else 2" == some "(if b 1 2)" && expr? "if b then 1" == none &&
  expr? "if b then let x := 1 in x else 2" == some "(if b (let x 1 x) 2)" &&
  -- `syntax.let.syntax`
  expr? "let x := 1 in let y := x in y" == some "(let x 1 (let y x y))" &&
  expr? "let x := a iff b in x" == some "(let x (iff a b) x)" &&
  expr? "a and (let x := true in x)" == some "(and a (paren (let x true x)))" &&
  expr? "a and let x := true in x" == none && expr? "let x = 1 in x" == none &&
  -- `syntax.match.syntax`
  expr? "match l {}" == some "(match l)" && expr? "match l { E::A => 1, }" == some "(match l (E::A 1))" &&
  expr? "match l { A => 1 }" == none && expr? "match l { E::A => 1 E::B => 2 }" == none &&
  expr? "match l { , }" == none && expr? "match f(l) { E::A => not a }" == some "(match (call f l) (E::A (not a)))" &&
  -- `syntax.remainder.line`
  (["\n", "\r\n", " -- c\n", "\n-- c\n"].all fun gap =>
    declarations? ("fn f(x: Int): Int := x" ++ gap ++ "mod m") == some ["fn f(x:Int!):Int! x", "mod m"] &&
    expr? ("x" ++ gap ++ "mod 2") == none && expr? ("(x" ++ gap ++ "mod 2)") == none) &&
  expr? "x mod\n2" == some "(mod x 2)" && expr? "x\rmod 2" == some "(mod x 2)" &&
  declarations? "fn f(x: Int): Int := x mod m" == some ["fn f(x:Int!):Int! (mod x m)"]

#guard productions_agree

/-- Nesting has no fixed bound: deep parentheses, prefixes and chains parse. -/
def nesting_agrees : Bool :=
  let n := 300
  acceptsExpr (String.ofList (List.replicate n '(') ++ "x" ++ String.ofList (List.replicate n ')')) &&
  acceptsExpr (" ".intercalate (List.replicate n "not") ++ " x") &&
  acceptsExpr (" + ".intercalate (List.replicate n "x")) &&
  acceptsExpr ("".intercalate (List.replicate n "f(") ++ "x" ++ String.ofList (List.replicate n ')'))

#guard nesting_agrees

-- Each `fren2` block of the chapter is accepted as a file, and each
-- `fren2 rejected` block is rejected, by the actual parser.
#eval show IO Unit from do
  let md ← IO.FS.readFile ("src" / "Spec" / "Language" / "Syntax.md")
  let mut seen := 0
  for block in Fren.Core.fencedBlocks md do
    let text := "\n".intercalate block.body.toList
    if block.info == "fren2" || block.info == "fren2 rejected" then
      seen := seen + 1
      unless accepts text == (block.info == "fren2") do
        throw <| IO.userError s!"Syntax.md:{block.line}: the parser does not agree with `{block.info}`"
  unless seen ≥ 8 do throw <| IO.userError s!"only {seen} example blocks found in Syntax.md"

end Spec.Language.Syntax
