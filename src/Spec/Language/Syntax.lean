import Fren.Impl
import Fren.Literate
import FrenParse
import Spec.Language.LexicalStructure

open Fren.Lang

#fren_md "Syntax.md"

#fren_check

namespace Spec.Language.Syntax

open FrenAst
abbrev SUnary := spec.surface.UnaryOp
abbrev SBinary := spec.surface.BinaryOp
abbrev Category := spec.surface.Category

/-! The chapter's checks run the actual parser, `FrenParse.parse`, against the
chapter as written: its `grammar` blocks, read from the Markdown and run as a
parsing expression grammar; its abstract syntax and printing functions; and
its example blocks. -/

/-! ## The chapter's text -/

/-- The chapter, read when the wrapper is elaborated. -/
def chapterPath : System.FilePath := "src" / "Spec" / "Language" / "Syntax.md"

/-- The bodies of the chapter's blocks with info string `info`, each with the
line of its fence. -/
def blocks (md info : String) : List (Nat × String) :=
  (Fren.Core.fencedBlocks md).toList.filterMap fun b =>
    if b.info == info then some (b.line, "\n".intercalate b.body.toList) else none

/-! ## The grammar, as data read from the chapter -/

/-- A parsing expression. -/
inductive G where
  | term (spelling : String)
  | nt (name : String)
  | seq (parts : List G)
  | alt (options : List G)
  | opt (g : G)
  | star (g : G)
  | plus (g : G)
  | neg (g : G)
  deriving Inhabited, Repr, BEq

/-- The lexemes of grammar notation: names, quoted strings, and `( ) | ? * + !`. -/
def notationTokens (text : String) : List String := Id.run do
  let mut out := []
  let mut cs := text.toList
  for _ in [:text.length + 1] do
    match cs with
    | [] => break
    | c :: rest =>
      if c == ' ' || c == '\n' then cs := rest
      else if c == '"' then
        let body := rest.takeWhile (· != '"')
        out := out ++ [String.ofList ('"' :: body)]
        cs := (rest.drop body.length).drop 1
      else if c.isAlpha then
        let name := cs.takeWhile Char.isAlphanum
        out := out ++ [String.ofList name]
        cs := cs.drop name.length
      else
        out := out ++ [String.singleton c]
        cs := rest
  return out

mutual
/-- `Alt := Seq ("|" Seq)*` -/
partial def parseAlt (ts : List String) : G × List String :=
  let (first, ts) := parseSeq ts
  let rec more (acc : List G) (ts : List String) : List G × List String :=
    match ts with
    | "|" :: rest => let (s, rest) := parseSeq rest; more (acc ++ [s]) rest
    | _ => (acc, ts)
  let (all, ts) := more [first] ts
  (if all.length == 1 then first else .alt all, ts)

/-- `Seq := Item*`, up to `|`, `)`, or the end. -/
partial def parseSeq (ts : List String) : G × List String :=
  let rec go (acc : List G) (ts : List String) : List G × List String :=
    match ts with
    | [] | "|" :: _ | ")" :: _ => (acc, ts)
    | _ => let (i, rest) := parseItem ts; go (acc ++ [i]) rest
  let (parts, ts) := go [] ts
  (if parts.length == 1 then parts.head! else .seq parts, ts)

/-- `Item := "!" Item | Atom ("?" | "*" | "+")*` -/
partial def parseItem (ts : List String) : G × List String :=
  match ts with
  | "!" :: rest => let (i, rest) := parseItem rest; (.neg i, rest)
  | _ =>
    let (a, ts) := parseAtom ts
    let rec suffixes (g : G) (ts : List String) : G × List String :=
      match ts with
      | "?" :: rest => suffixes (.opt g) rest
      | "*" :: rest => suffixes (.star g) rest
      | "+" :: rest => suffixes (.plus g) rest
      | _ => (g, ts)
    suffixes a ts

partial def parseAtom (ts : List String) : G × List String :=
  match ts with
  | "(" :: rest => let (g, rest) := parseAlt rest; (g, rest.drop 1)
  | t :: rest => (if t.startsWith "\"" then .term (t.drop 1).toString else .nt t, rest)
  | [] => (.seq [], [])
end

/-- The rules of a grammar block: a line that contains `::=` starts a rule,
and the lines after it continue it. -/
def rulesOfBlock (body : String) : List (String × G) := Id.run do
  let mut rules : List (String × String) := []
  for line in body.splitOn "\n" do
    match line.splitOn "::=" with
    | [lhs, rhs] => rules := rules ++ [(lhs.trimAscii.toString, rhs)]
    | _ => match rules.getLast? with
      | some (n, rhs) => rules := rules.dropLast ++ [(n, rhs ++ " " ++ line)]
      | none => pure ()
  return rules.map fun (n, rhs) => (n, (parseAlt (notationTokens rhs)).1)

/-! ## Running the grammar on the lexer's tokens -/

/-- A token, with what the trivia-sensitive terminals need of the trivia
before it. -/
structure Tok where
  text : String
  kind : LexicalKind
  touching : Bool

def toks (source : String) : Array Tok :=
  let lexed := FrenParse.tokenize ⟨0⟩ source
  lexed.tokens.mapIdx fun i t =>
    let before := match (if i == 0 then none else lexed.tokens[i - 1]?) with
      | some previous => lexed.tape.extract (previous.slice + 1) t.slice
      | none => #[]
    { text := t.text, kind := t.kind,
      touching := i > 0 && before.isEmpty }

/-- Whether a token is the terminal `spelling` of the grammar. -/
def terminal (spelling : String) (t : Tok) : Bool :=
  match spelling with
  | "Identifier" => t.kind == .identifier
  | "QuestionIdentifier" => t.kind == .identifier && t.text.endsWith "?"
  | "Numeral" => t.kind == .numeral
  | "TouchingOpen" => t.text == "(" && t.touching
  | _ => false

def classTerminals : List String :=
  ["Identifier", "QuestionIdentifier", "Numeral", "TouchingOpen"]

/-- Match `g` at token `i`: the position after the match and the rule
alternatives `(rule, index)` that it used, or `none` if it does not match. -/
partial def run (rules : List (String × G)) (ts : Array Tok) (g : G) (i : Nat) :
    Option (Nat × List (String × Nat)) :=
  match g with
  | .term s => match ts[i]? with
    | some t => if t.text == s && t.kind != .rejected then some (i + 1, []) else none
    | none => none
  | .nt n =>
    if classTerminals.contains n then
      match ts[i]? with
      | some t => if terminal n t then some (i + 1, []) else none
      | none => none
    else match rules.lookup n with
      | some (.alt options) =>
        options.zipIdx.findSome? fun (o, k) =>
          (run rules ts o i).map fun (j, used) => (j, (n, k) :: used)
      | some body => (run rules ts body i).map fun (j, used) => (j, (n, 0) :: used)
      | none => none
  | .seq parts => parts.foldlM (init := (i, [])) fun (j, used) p =>
      (run rules ts p j).map fun (k, more) => (k, used ++ more)
  | .alt options => options.findSome? (run rules ts · i)
  | .opt g => some ((run rules ts g i).getD (i, []))
  | .star g =>
    let rec loop (j : Nat) (used : List (String × Nat)) (fuel : Nat) : Nat × List (String × Nat) :=
      match fuel with
      | 0 => (j, used)
      | fuel + 1 => match run rules ts g j with
        | some (k, more) => if k == j then (j, used) else loop k (used ++ more) fuel
        | none => (j, used)
    some (loop i [] (ts.size + 1))
  | .plus g => run rules ts (.seq [g, .star g]) i
  | .neg g => if (run rules ts g i).isSome then none else some (i, [])

/-- Whether the grammar's `start` matches all of `source`'s tokens. -/
def grammarAccepts (rules : List (String × G)) (start source : String) : Bool :=
  let ts := toks source
  match run rules ts (.nt start) 0 with
  | some (j, _) => j == ts.size
  | none => false

def parserAccepts (entry : Entry) (source : String) : Bool :=
  (FrenParse.parse entry ⟨0⟩ source).toBool

/-- Every sequence of at most `n` of `pieces`, joined by spaces. -/
def sequences (pieces : List String) : Nat → List String
  | 0 => [""]
  | n + 1 => "" :: (sequences pieces n).flatMap fun s =>
      pieces.map fun p => if s.isEmpty then p else s ++ " " ++ p

/-- `count` seeded pseudo-random sequences of 5 to 14 of `pieces`. -/
def randomSequences (pieces : List String) (count seed : Nat) : List String := Id.run do
  let mut seed := seed
  let mut out := []
  for _ in [:count] do
    seed := (seed * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
    let len := 5 + seed / 2 ^ 40 % 10
    let mut text := ""
    for _ in [:len] do
      seed := (seed * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
      text := text ++ " " ++ pieces[seed / 2 ^ 33 % pieces.length]!
    out := text :: out
  return out

/-- Expression pieces: one of each kind of token, and the trivia-sensitive
`(` and `mod`, written touching or after a line ending. -/
def expressionPieces : List String :=
  ["x", "1", "true", "not", "-", "+", "*", "<", "=", "and", "iff", "(", ")", "f(", ",", "if",
   "then", "else", "let", ":=", "in", "match", "{", "}", "E::A", "=>", "%", "\n%", "mod", "\nmod"]

def smallExpressionPieces : List String :=
  ["x", "not", "-", "+", "<", "iff", "(", ")", "f(", ",", "if", "then", "else", "\n%", "mod"]

def declarationPieces : List String :=
  ["pub", "fn f(x: Int): Int :=", "fn f(", "x", "b?", ":", "Int", ")", "mod m", "\nmod", "mod", "%",
   "enum E {", "A", ",", "}", "expect e(", "{", "expect c:", "assume", "a:", ":="]

/-- The grammar of the chapter, from its `grammar` blocks. -/
def grammarOf (md : String) : List (String × G) :=
  (blocks md "grammar").flatMap fun (_, body) => rulesOfBlock body

/-- `syntax.file.syntax`, `syntax.path.syntax`, `syntax.declaration.syntax`,
`syntax.declaration.lists`, `syntax.expression.syntax`, `syntax.expression.extent`
and `syntax.notation.trivia-sensitive`: the chapter's grammar, run as written,
accepts exactly what the parser accepts. Bounded: as an `ExpressionEntry`,
every sequence of up to three of `expressionPieces` (30 pieces), every
sequence of up to five of `smallExpressionPieces` (15), and 3000 seeded random
sequences of 5 to 14 of `expressionPieces`; as a `File`, every sequence of up
to four of `declarationPieces` (22) and 3000 random ones of 5 to 14; every
`fren2` and `fren2 rejected` block; and `near`, texts near valid ones. -/
def grammarAgrees (md : String) (near : List String) : Option String := Id.run do
  let rules := grammarOf md
  let checks : List (Entry × String × List String) :=
    [(.expression, "ExpressionEntry", sequences expressionPieces 3 ++
        sequences smallExpressionPieces 5 ++ randomSequences expressionPieces 3000 7 ++ near),
     (.file, "File", sequences declarationPieces 4 ++ randomSequences declarationPieces 3000 11 ++
        ((blocks md "fren2") ++ (blocks md "fren2 rejected")).map (·.2))]
  for (entry, start, texts) in checks do
    for text in texts do
      if grammarAccepts rules start text != parserAccepts entry text then
        return some s!"the grammar and the parser disagree on {start} {repr text}"
  return none

/-! ## Abstract syntax -/

/-- An expression tree: the fixed point of the chapter's `ExprF`, as
`Tree.layer` and `Tree.ofLayer` show. -/
inductive Tree where
  | boolean (b : Bool)
  | integer (n : Nat)
  | name (path : List String)
  | call (path : List String) (args : List Tree)
  | unary (op : SUnary) (e : Tree)
  | binary (op : SBinary) (l r : Tree)
  | ifE (c t e : Tree)
  | letE (x : String) (v b : Tree)
  | matchE (s : Tree) (arms : List (List String × Tree))
  deriving Inhabited

/-- A tree's top node, as the chapter's `ExprF` over its subtrees. -/
def Tree.layer : Tree → spec.surface.ExprF Tree
  | .boolean b => .Boolean b
  | .integer n => .Integer n
  | .name p => .Name (Fren.Seq.ofList p)
  | .call p args => .Call (Fren.Seq.ofList p) (Fren.Seq.ofList args)
  | .unary op e => .Unary op e
  | .binary op l r => .Binary op l r
  | .ifE c t e => .If c t e
  | .letE x v b => .Let x v b
  | .matchE s arms => .Match s (Fren.Seq.ofList (arms.map fun (p, b) => ⟨Fren.Seq.ofList p, b⟩))

/-- A tree from its top node. -/
def Tree.ofLayer : spec.surface.ExprF Tree → Tree
  | .Boolean b => .boolean b
  | .Integer n => .integer n
  | .Name p => .name p.toList
  | .Call p args => .call p.toList args.toList
  | .Unary op e => .unary op e
  | .Binary op l r => .binary op l r
  | .If c t e => .ifE c t e
  | .Let x v b => .letE x v b
  | .Match s arms => .matchE s (arms.toList.map fun a => (a.variant.toList, a.body))

theorem Tree.ofLayer_layer (t : Tree) : Tree.ofLayer t.layer = t := by
  cases t <;> simp [Tree.layer, Tree.ofLayer, Fren.Seq.ofList, Fren.Seq.toList, Function.comp_def]

def unaryOps : List SUnary := [.Neg, .Not]
def binaryOps : List SBinary :=
  [.Add, .Sub, .Mul, .Div, .Mod, .Eq, .Ne, .Lt, .Le, .Gt, .Ge, .And, .Or, .Iff]

theorem all_binary (op : SBinary) : op ∈ binaryOps := by cases op <;> simp [binaryOps]
theorem all_unary (op : SUnary) : op ∈ unaryOps := by cases op <;> simp [unaryOps]

def pathOf (p : Path) : List String := p.tokens.filter (·.text != "::") |>.map (·.text)

def unaryOf : FrenAst.UnaryOp → SUnary
  | .neg => .Neg | .not => .Not

def binaryOf (op : FrenAst.BinaryOp) : SBinary :=
  match op with
  | .add => .Add | .sub => .Sub | .mul => .Mul | .div => .Div | .mod => .Mod | .eq => .Eq
  | .ne => .Ne | .lt => .Lt | .le => .Le | .gt => .Gt | .ge => .Ge | .and => .And | .or => .Or
  | .iff => .Iff

/-- `syntax.tree.productions`: the tree of each production of an expression. -/
partial def abstract : Expr → Tree
  | .name path => .name (pathOf path)
  | .bool _ b => .boolean b
  | .integer _ n => .integer n
  | .paren _ body _ => abstract body
  | .unary _ op body => .unary (unaryOf op) (abstract body)
  | .binary l _ op r => .binary (binaryOf op) (abstract l) (abstract r)
  | .call (.name path) _ args _ _ => .call (pathOf path) (args.toList.map abstract)
  | .call _ _ args _ _ => .call [] (args.toList.map abstract)
  | .ifE _ c _ t _ e => .ifE (abstract c) (abstract t) (abstract e)
  | .letE _ x _ v _ b => .letE x.text (abstract v) (abstract b)
  | .matchE _ s _ arms _ => .matchE (abstract s) (arms.toList.map fun a => (pathOf a.1, abstract a.2.2.1))

def spellBinary (op : SBinary) : String := spec.surface.binary_spelling op
def spellUnary (op : SUnary) : String := spec.surface.unary_spelling op

/-- A tree as fully parenthesized text, to compare trees. -/
partial def Tree.show : Tree → String
  | .boolean b => toString b
  | .integer n => toString n
  | .name p => "::".intercalate p
  | .call p args => "::".intercalate p ++ "(" ++ ", ".intercalate (args.map Tree.show) ++ ")"
  | .unary op e => s!"({spellUnary op} {e.show})"
  | .binary op l r => s!"({l.show} {spellBinary op} {r.show})"
  | .ifE c t e => s!"(if {c.show} then {t.show} else {e.show})"
  | .letE x v b => s!"(let {x} := {v.show} in {b.show})"
  | .matchE s arms => s!"(match {s.show} \{" ++
      ", ".intercalate (arms.map fun (p, b) => "::".intercalate p ++ " => " ++ b.show) ++ "})"

def tree? (source : String) : Option String :=
  match FrenParse.parseExpression ⟨0⟩ source with
  | .ok { root := .expression e, .. } => some (abstract e).show
  | _ => none

/-- The tree of a type (`syntax.path.syntax`). -/
def typeTree : Ty → spec.surface.TypeName
  | .bool _ => .Boolean
  | .int _ => .Integer
  | .named p => .Named (Fren.Seq.ofList (pathOf p))

def showType : spec.surface.TypeName → String
  | .Boolean => "Bool!" | .Integer => "Int!" | .Named p => "::".intercalate p.toList

def paramTree (p : Parameter) : spec.surface.Parameter :=
  ⟨p.name.text, match p.annotation with | some (_, t) => .some (typeTree t) | none => .none⟩

def showParam (p : spec.surface.Parameter) : String :=
  p.name ++ match p.annotation with | .some t => ":" ++ showType t | .none => ""

/-- The tree of a declaration (`syntax.tree.productions`). -/
def declTree : Decl → spec.surface.DeclarationF Tree
  | .moduleDecl v _ p => .Module v.isSome (Fren.Seq.ofList (pathOf p))
  | .enumDecl v _ n _ vs _ _ => .Enumeration v.isSome n.text (Fren.Seq.ofList (vs.toList.map (·.text)))
  | .function v _ n ps _ r _ b =>
    .Function v.isSome n.text (Fren.Seq.ofList (ps.values.toList.map paramTree)) (typeTree r) (abstract b)
  | .expectation _ n ps _ ms _ =>
    .Expectation n.text (Fren.Seq.ofList (ps.values.toList.map paramTree))
      (Fren.Seq.ofList (ms.toList.map fun m =>
        ⟨if m.kind == .assume then .Assume else .Expect, m.label.text, abstract m.body⟩))

def showDecl : spec.surface.DeclarationF Tree → String
  | .Module isPub p => s!"{if isPub then "pub " else ""}mod " ++ "::".intercalate p.toList
  | .Enumeration isPub n vs => s!"{if isPub then "pub " else ""}enum {n} " ++ ",".intercalate vs.toList
  | .Function isPub n ps r b =>
    s!"{if isPub then "pub " else ""}fn {n}(" ++ ",".intercalate (ps.toList.map showParam) ++
      s!"):{showType r} {b.show}"
  | .Expectation n ps ms =>
    s!"expect {n}(" ++ ",".intercalate (ps.toList.map showParam) ++ ") " ++
      ";".intercalate (ms.toList.map fun m =>
        s!"{match m.kind with | .Assume => "assume" | .Expect => "expect"} {m.label} {m.body.show}")

def decls? (source : String) : Option (List String) :=
  match FrenParse.parseFile ⟨0⟩ source with
  | .ok { root := .declarations ds, .. } => some (ds.toList.map (showDecl ∘ declTree))
  | _ => none

/-! ## Printing -/

/-- A tree printed by `syntax.print.roundtrip`: its text, its category and
whether it is open. -/
structure Printed where
  text : String
  category : Category
  isOpen : Bool

instance : Inhabited Printed := ⟨⟨"", .Primary, false⟩⟩

/-- `place` gets `child`, in parentheses where `fits?` says it does not fit. -/
def placed (child : Printed) (place : Category) (followed : Bool) : String :=
  if spec.surface.«fits?» child.category child.isOpen place followed then child.text
  else "(" ++ child.text ++ ")"

partial def Tree.print : Tree → Printed
  | .boolean b => ⟨toString b, .Primary, false⟩
  | .integer n => ⟨toString n, .Primary, false⟩
  | .name p => ⟨"::".intercalate p, .Primary, false⟩
  | .call p args =>
    ⟨"::".intercalate p ++ "(" ++ ", ".intercalate (args.map fun a => placed a.print .Expression false) ++ ")",
     .Primary, false⟩
  | .unary op e =>
    let e := e.print
    ⟨spellUnary op ++ " " ++ placed e (spec.surface.operand_category true op .Add false) false,
     spec.surface.category true op .Add, e.isOpen⟩
  | .binary op l r =>
    let (l, r) := (l.print, r.print)
    ⟨placed l (spec.surface.operand_category false .Neg op true) true ++ " " ++ spellBinary op ++ " " ++
      placed r (spec.surface.operand_category false .Neg op false) false,
     spec.surface.category false .Neg op, r.isOpen⟩
  | .ifE c t e =>
    ⟨s!"if {placed c.print .Expression false} then {placed t.print .Expression false} else " ++
      placed e.print .Expression false, .Primary, true⟩
  | .letE x v b =>
    ⟨s!"let {x} := {placed v.print .Iff false} in {placed b.print .Expression false}", .Expression, true⟩
  | .matchE s arms =>
    ⟨s!"match {placed s.print .Primary false} \{ " ++
      ", ".intercalate (arms.map fun (p, b) => "::".intercalate p ++ " => " ++ placed b.print .Iff false) ++
      " }", .Primary, false⟩

/-- A seeded pseudo-random tree of at most `depth` levels. -/
partial def randomTree (seed : Nat) : Nat → Tree × Nat
  | 0 => let s := (seed * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
    (match s / 2 ^ 33 % 4 with
      | 0 => .name ["x"] | 1 => .integer (s / 2 ^ 40 % 100) | 2 => .boolean (s / 2 ^ 41 % 2 == 0)
      | _ => .name ["E", "A"], s)
  | depth + 1 =>
    let s := (seed * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
    let pick := s / 2 ^ 33 % 12
    if pick < 2 then randomTree s 0 else
    let (a, s) := randomTree s depth
    let (b, s) := randomTree s depth
    let (c, s) := randomTree s depth
    match pick with
    | 2 => (.unary (unaryOps[s / 2 ^ 35 % 2]!) a, s)
    | 3 | 4 | 5 | 6 => (.binary (binaryOps[s / 2 ^ 35 % 14]!) a b, s)
    | 7 => (.ifE a b c, s)
    | 8 => (.letE "v" a b, s)
    | 9 => (.call ["f"] [a, b], s)
    | 10 => (.matchE a [(["E", "A"], b), (["E", "B"], c)], s)
    | _ => (.call ["g"] [a], s)

/-- `syntax.print.roundtrip`: printing a tree and parsing the text gives the
tree back, for well-formed trees, and not for ill-formed ones. Bounded: 3000 seeded random well-formed trees of depth at most 5, every
pair of binary operators and every unary operator around binary operands, and
seven ill-formed trees, one for each way to be ill formed. -/
def roundtrip_agrees : Bool := Id.run do
  let mut seed := 2026
  let mut trees : List Tree := []
  for _ in [:3000] do
    let (t, s) := randomTree seed 5
    seed := s
    trees := t :: trees
  let x := Tree.name ["x"]
  let y := Tree.name ["y"]
  let z := Tree.name ["z"]
  for a in binaryOps do
    for b in binaryOps do
      trees := .binary a (.binary b x y) z :: .binary a x (.binary b y z) :: trees
    for u in unaryOps do
      trees := .unary u (.binary a x y) :: .binary a (.unary u x) y :: .binary a x (.unary u y) :: trees
  -- Trees that are not well formed print to text that does not parse back.
  let illFormed : List Tree := [.call ["f"] [], .name [], .call [] [x],
    .matchE x [(["A"], y)], .letE "true" x y, .name ["E", "not"], .binary .Add (.name ["if"]) x]
  return trees.all (fun t => tree? t.print.text == some t.show) &&
    illFormed.all fun t => tree? t.print.text != some t.show

#guard roundtrip_agrees

/-- Texts near valid expressions: 1500 printed random trees, each also with
its parentheses dropped and with each of its first eight tokens dropped in
turn, which gives chains, bare operands and unfinished forms in every
context. -/
def nearExpressions : List String := Id.run do
  let mut seed := 4049
  let mut out := []
  for _ in [:1500] do
    let (t, s) := randomTree seed 4
    seed := s
    let text := t.print.text
    let words := text.splitOn " "
    out := out ++ [text, (text.replace "(" " ").replace ")" " "] ++
      (List.range (min 8 words.length)).map fun i => " ".intercalate (words.eraseIdx i)
  return out

/-! ## Operators -/

--@ reference: syntax.tree.operators
/-- `syntax.tree.operators`: the parser reads each binary spelling as that
operator, and at the precedence that orders the chapter's categories, and no
other punctuator or keyword as a binary operator; it reads each unary spelling
before an operand as that unary operator. -/
def operators_agree : Bool :=
  binaryOps.all (fun op =>
    match FrenParse.binaryOperator (spellBinary op) with
    | some (ast, p) => binaryOf ast == op &&
        (p : Int) == spec.surface.rank (spec.surface.category false .Neg op)
    | none => false) &&
  (["(", ")", "{", "}", ",", ":", ":=", "=>", "::", "not", "in", "if", "let", "x", "1", "assume"].all
    fun s => (FrenParse.binaryOperator s).isNone) &&
  unaryOps.all fun op => tree? (spellUnary op ++ " x") == some s!"({spellUnary op} x)"

#guard operators_agree

/-! ## Terminals -/

/-- The quoted terminals of a grammar. -/
partial def G.terminals : G → List String
  | .term s => [s]
  | .nt _ => []
  | .seq gs | .alt gs => gs.flatMap G.terminals
  | .opt g | .star g | .plus g | .neg g => g.terminals

/-- `syntax.expression.terminals`: the grammar's punctuator terminals are
exactly `PUNCTUATORS`, its keyword terminals exactly `GRAMMAR_KEYWORDS`, and
its other terminals exactly `CONTEXTUAL`; and each binary operator's spelling
is a terminal of the grammar rule named by its category (`CompareOp` for a
comparison). -/
def terminalsAgree (md : String) : Bool :=
  let rules := grammarOf md
  let ts := (rules.flatMap fun (_, g) => g.terminals).eraseDups
  let words := ts.filter fun t => t.toList.all Char.isAlpha
  decide (spec.lexical.PUNCTUATORS = Fren.FinSet.ofList (ts.filter fun t => !(t.toList.all Char.isAlpha))) &&
  decide (spec.surface.GRAMMAR_KEYWORDS = Fren.FinSet.ofList (words.filter fun w => FrenParse.keywords.contains w)) &&
  decide (spec.surface.CONTEXTUAL = Fren.FinSet.ofList (words.filter fun w => !(FrenParse.keywords.contains w))) &&
  binaryOps.all fun op =>
    let cat : Category := spec.surface.category false .Neg op
    let ruleName : String := match cat with
      | .Iff => "Iff" | .Or => "Or" | .And => "And" | .Comparison => "CompareOp"
      | .Sum => "Sum" | .Product => "Product" | _ => ""
    match rules.lookup ruleName with
    | some g => g.terminals.contains (spellBinary op)
    | none => false

/-! ## The chapter's examples -/

/-- The line of a byte offset, from 1. -/
def lineOf (text : String) (offset : Nat) : Nat :=
  ((String.fromUTF8! (text.toUTF8.extract 0 offset)).toList.filter (· == '\n')).length + 1

/-- Each `fren2 rejected` block is rejected with the diagnostic that its
`--~ error:` annotation states, on the annotated line. -/
def rejectedAgree (md : String) : Option String := Id.run do
  for (line, body) in blocks md "fren2 rejected" do
    let lines := body.splitOn "\n"
    let some (k, note) := lines.zipIdx.findSome? (fun (l, k) =>
        match l.splitOn "--~ error: " with | [_, msg] => some (k + 1, msg) | _ => none)
      | return some s!"Syntax.md:{line}: a rejected block has no `--~ error:` annotation"
    match FrenParse.parseFile ⟨0⟩ body with
    | .ok _ => return some s!"Syntax.md:{line}: the parser accepts a rejected block"
    | .error f =>
      unless lineOf body f.diagnostic.span.start == k && "expected " ++ f.diagnostic.expected == note do
        return some s!"Syntax.md:{line}: the parser says {f.diagnostic.render} on line {lineOf body f.diagnostic.span.start}"
  return none

/-- Each line `lhs -- rhs` of a `fren2 groups` block has the same tree on
both sides: the parser groups `lhs` as `rhs` writes with parentheses. -/
def groupsAgree (md : String) : Option String := Id.run do
  for (line, body) in blocks md "fren2 groups" do
    for l in body.splitOn "\n" do
      match l.splitOn " -- " with
      | [lhs, rhs] =>
        unless (tree? lhs).isSome && tree? lhs == tree? rhs do
          return some s!"Syntax.md:{line}: `{lhs}` does not group as `{rhs}`"
      | _ => return some s!"Syntax.md:{line}: `{l}` is not `lhs -- rhs`"
  return none

/-- Every alternative of every grammar rule that the chapter's `fren2` blocks
use, as `(rule, index)`. -/
def coveredBy (md : String) : List (String × Nat) :=
  let rules := grammarOf md
  (blocks md "fren2").flatMap fun (_, body) =>
    match run rules (toks body) (.nt "File") 0 with
    | some (_, used) => used
    | none => []

/-- The alternatives of each rule whose body is an alternation, or `(rule, 0)`. -/
def alternatives (md : String) : List (String × Nat) :=
  (grammarOf md).flatMap fun (n, g) => match g with
    | .alt options => (List.range options.length).map (n, ·)
    | _ => [(n, 0)]

/-- `syntax.tree.productions`: the trees of the productions, on examples of
each, and of every `fren2 groups` line. -/
def treesAgree (md : String) : Option String :=
  let expected : List (String × String) :=
    [("-1", "(- 1)"), ("not true", "(not true)"), ("007", "7"), ("A::B::c", "A::B::c"),
     ("((x))", "x"), ("f(g(x), (y))", "f(g(x), y)"), ("a - b - c", "((a - b) - c)"),
     ("if b then let x := 1 in x else 2", "(if b then (let x := 1 in x) else 2)"),
     ("match f(l) { E::A => not a, E::B => 1, }", "(match f(l) {E::A => (not a), E::B => 1})"),
     ("match l {}", "(match l {})")]
  match expected.find? fun (s, t) => tree? s != some t with
  | some (s, _) => some s!"the tree of `{s}` is {tree? s}"
  | none =>
    let files : List (String × List String) :=
      [("pub mod a::b\nenum E { A, B, }", ["pub mod a::b", "enum E A,B"]),
       ("fn f(a: Bool, b: Int, c: E, d: Int::T, e: A::Int, q?): Bool := (a)",
         ["fn f(a:Bool!,b:Int!,c:E,d:Int::T,e:A::Int,q?):Bool! a"]),
       ("expect e(x: Int,) { assume a: x > 0 expect b: x >= 0 }",
         ["expect e(x:Int!) assume a (x > 0);expect b (x >= 0)"])]
    match files.find? fun (s, t) => decls? s != some t with
    | some (s, _) => some s!"the trees of `{s}` are {decls? s}"
    | none => groupsAgree md

open Lean in
#eval show IO Unit from do
  let md ← IO.FS.readFile chapterPath
  if let some e := grammarAgrees md nearExpressions then throw <| IO.userError e
  unless terminalsAgree md do throw <| IO.userError "the grammar's terminals differ from the chapter's sets"
  if let some e := rejectedAgree md then throw <| IO.userError e
  if let some e := treesAgree md then throw <| IO.userError e
  -- `fren2` blocks parse; the grammar's every alternative is used by one.
  for (line, body) in blocks md "fren2" do
    unless parserAccepts .file body do throw <| IO.userError s!"Syntax.md:{line}: the parser rejects a `fren2` block"
  let missing := (alternatives md).filter fun a => a.1 != "ExpressionEntry" && !(coveredBy md).contains a
  unless missing.isEmpty do
    throw <| IO.userError s!"the `fren2` examples use no match of {missing}"

-- Named results, for the chapter's status lines: each re-reads the chapter.
def grammar_agrees : IO Bool := return (grammarAgrees (← IO.FS.readFile chapterPath) nearExpressions).isNone
def terminals_agree : IO Bool := return terminalsAgree (← IO.FS.readFile chapterPath)
def trees_agree : IO Bool := return (treesAgree (← IO.FS.readFile chapterPath)).isNone
def examples_cover : IO Bool := do
  let md ← IO.FS.readFile chapterPath
  return (alternatives md).all fun a => a.1 == "ExpressionEntry" || (coveredBy md).contains a

end Spec.Language.Syntax
