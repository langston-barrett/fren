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
its example blocks. Every check takes the chapter's text, so that the
mutation control below can run it on altered chapters. -/

/-! ## The chapter's text -/

def chapterPath : System.FilePath := "src" / "Spec" / "Language" / "Syntax.md"

/-- The bodies of the chapter's blocks with info string `info`, each with the
line of its fence. -/
def blocks (md info : String) : List (Nat × String) :=
  (Fren.Core.fencedBlocks md).toList.filterMap fun b =>
    if b.info == info then some (b.line, "\n".intercalate b.body.toList) else none

/-! ## The grammar, as data read from the chapter

A parsing expression, with an identity for each node that a choice or a
repetition makes, so that example coverage can name it. -/
inductive G where
  | term (spelling : String)
  | nt (name : String)
  | seq (parts : List G)
  | alt (id : String) (options : List G)
  | opt (id : String) (g : G)
  | star (id : String) (g : G)
  | plus (id : String) (g : G)
  | neg (g : G)
  deriving Inhabited, Repr, BEq

/-- The terminals that are classes of tokens, not spellings. -/
def classTerminals : List String := ["Identifier", "QuestionIdentifier", "Numeral", "TouchingOpen"]

/-- The lexemes of grammar notation: names, quoted strings, and `( ) | ? * + !`;
anything else is an error. -/
def notationTokens (text : String) : Except String (List String) := do
  let mut out := []
  let mut cs := text.toList
  for _ in [:text.length + 1] do
    match cs with
    | [] => break
    | c :: rest =>
      if c == ' ' || c == '\n' then cs := rest
      else if c == '"' then
        let body := rest.takeWhile (· != '"')
        if body.length == rest.length || body.isEmpty then
          throw s!"an unterminated or empty quoted terminal in `{text.trimAscii}`"
        out := out ++ [String.ofList ('"' :: body)]
        cs := (rest.drop body.length).drop 1
      else if c.isAlpha then
        let name := cs.takeWhile Char.isAlphanum
        out := out ++ [String.ofList name]
        cs := cs.drop name.length
      else if "()|?*+!".contains c then
        out := out ++ [String.singleton c]
        cs := rest
      else throw s!"the character `{c}` in `{text.trimAscii}` is no grammar notation"
  return out

/-- A recursive-descent reader of grammar notation, which numbers the nodes of
rule `rule` as it reads them. -/
structure Reader where
  rule : String
  next : Nat := 0

abbrev ReadM := StateT Reader (Except String)

def fresh : ReadM String := do
  let r ← get
  set { r with next := r.next + 1 }
  return s!"{r.rule}.{r.next}"

mutual
partial def readAlt (ts : List String) : ReadM (G × List String) := do
  let id ← fresh
  let (first, ts) ← readSeq ts
  let mut options := [first]
  let mut ts := ts
  repeat
    match ts with
    | "|" :: rest =>
      let (s, rest) ← readSeq rest
      options := options ++ [s]
      ts := rest
    | _ => break
  return (if options.length == 1 then first else .alt id options, ts)

partial def readSeq (ts : List String) : ReadM (G × List String) := do
  let mut parts := []
  let mut ts := ts
  repeat
    match ts with
    | [] | "|" :: _ | ")" :: _ => break
    | _ =>
      let (i, rest) ← readItem ts
      parts := parts ++ [i]
      ts := rest
  if parts.isEmpty then throw "an empty alternative"
  return (if parts.length == 1 then parts.head! else .seq parts, ts)

partial def readItem (ts : List String) : ReadM (G × List String) := do
  match ts with
  | "!" :: rest => let (i, rest) ← readItem rest; return (.neg i, rest)
  | _ =>
    let (a, ts) ← readAtom ts
    let mut g := a
    let mut ts := ts
    repeat
      match ts with
      | "?" :: rest => g := .opt (← fresh) g; ts := rest
      | "*" :: rest => g := .star (← fresh) g; ts := rest
      | "+" :: rest => g := .plus (← fresh) g; ts := rest
      | _ => break
    return (g, ts)

partial def readAtom (ts : List String) : ReadM (G × List String) := do
  match ts with
  | "(" :: rest =>
    let (g, rest) ← readAlt rest
    match rest with
    | ")" :: rest => return (g, rest)
    | _ => throw "a group without its `)`"
  | t :: rest =>
    if t.startsWith "\"" then return (.term (t.drop 1).toString, rest)
    else if t.front.isUpper then return (.nt t, rest)
    else throw s!"`{t}` is neither a quoted terminal nor a nonterminal"
  | [] => throw "an alternative that ends early"
end

/-- The nonterminals that a grammar names. -/
partial def G.names : G → List String
  | .term _ => []
  | .nt n => [n]
  | .seq gs | .alt _ gs => gs.flatMap G.names
  | .opt _ g | .star _ g | .plus _ g | .neg g => g.names

/-- The rules of the chapter's `grammar` blocks: a line that contains `::=`
starts a rule, and the lines after it continue it. Malformed notation, a rule
defined twice, a nonterminal that no rule defines, and a rule that `File` and
`ExpressionEntry` do not reach are errors. -/
def grammarOf (md : String) : Except String (List (String × G)) := do
  let mut raw : List (String × String) := []
  for (_, body) in blocks md "grammar" do
    for line in body.splitOn "\n" do
      match line.splitOn "::=" with
      | [lhs, rhs] => raw := raw ++ [(lhs.trimAscii.toString, rhs)]
      | [_] => match raw.getLast? with
        | some (n, rhs) => raw := raw.dropLast ++ [(n, rhs ++ " " ++ line)]
        | none => throw s!"`{line}` continues no rule"
      | _ => throw s!"`{line}` has more than one `::=`"
  let mut rules := []
  for (n, rhs) in raw do
    unless n.toList.all Char.isAlphanum && n.front.isUpper do throw s!"`{n}` is no nonterminal"
    if rules.any (·.1 == n) then throw s!"`{n}` is defined twice"
    let (g, rest) ← ((readAlt (← notationTokens rhs)).run' { rule := n })
    unless rest.isEmpty do throw s!"`{n}` has unread notation {rest}"
    rules := rules ++ [(n, g)]
  for (n, g) in rules do
    for m in g.names do
      unless classTerminals.contains m || rules.any (·.1 == m) do
        throw s!"`{n}` names `{m}`, which no rule defines"
  -- Every rule is reachable from the start nonterminals.
  let mut reached := ["File", "ExpressionEntry"]
  for _ in [:rules.length + 1] do
    reached := (reached ++ reached.flatMap fun r => ((rules.lookup r).map G.names).getD []).eraseDups
  for (n, _) in rules do
    unless reached.contains n do throw s!"`{n}` is unreachable from `File` and `ExpressionEntry`"
  for start in ["File", "ExpressionEntry"] do
    unless rules.any (·.1 == start) do throw s!"no rule defines `{start}`"
  return rules

/-! ## Running the grammar on the lexer's tokens -/

/-- A token, with whether trivia comes before it. -/
structure Tok where
  text : String
  kind : LexicalKind
  touching : Bool

def toks (source : String) : Array Tok :=
  let lexed := FrenParse.tokenize ⟨0⟩ source
  lexed.tokens.mapIdx fun i t =>
    let touching := match (if i == 0 then none else lexed.tokens[i - 1]?) with
      | some previous => previous.slice + 1 == t.slice
      | none => false
    { text := t.text, kind := t.kind, touching }

def terminal (spelling : String) (t : Tok) : Bool :=
  match spelling with
  | "Identifier" => t.kind == .identifier
  | "QuestionIdentifier" => t.kind == .identifier && t.text.endsWith "?"
  | "Numeral" => t.kind == .numeral
  | "TouchingOpen" => t.text == "(" && t.touching
  | _ => false

/-- Match `g` at token `i`: the position after the match and the choices and
repetitions that it used, or `none` if it does not match. -/
partial def run (rules : List (String × G)) (ts : Array Tok) (g : G) (i : Nat) :
    Option (Nat × List String) :=
  match g with
  | .term s => match ts[i]? with
    | some t => if t.text == s && t.kind != .rejected then some (i + 1, []) else none
    | none => none
  | .nt n =>
    if classTerminals.contains n then
      match ts[i]? with
      | some t => if terminal n t then some (i + 1, []) else none
      | none => none
    else (rules.lookup n).bind (run rules ts · i)
  | .seq parts => parts.foldlM (init := (i, [])) fun (j, used) p =>
      (run rules ts p j).map fun (k, more) => (k, used ++ more)
  | .alt id options =>
    options.zipIdx.findSome? fun (o, k) => (run rules ts o i).map fun (j, used) => (j, s!"{id}/{k}" :: used)
  | .opt id g => some <| match run rules ts g i with
    | some (j, used) => (j, id :: used)
    | none => (i, [])
  | .star id g =>
    let rec loop (j : Nat) (used : List String) (fuel : Nat) : Nat × List String :=
      match fuel with
      | 0 => (j, used)
      | fuel + 1 => match run rules ts g j with
        | some (k, more) => if k == j then (j, used) else loop k (used ++ id :: more) fuel
        | none => (j, used)
    some (loop i [] (ts.size + 1))
  | .plus id g => (run rules ts g i).bind fun (j, used) =>
      (run rules ts (.star id g) j).map fun (k, more) => (k, id :: used ++ more)
  | .neg g => if (run rules ts g i).isSome then none else some (i, [])

/-- `run` without the record of choices, for speed. -/
partial def matchAt (rules : List (String × G)) (ts : Array Tok) (g : G) (i : Nat) : Option Nat :=
  match g with
  | .term s => match ts[i]? with
    | some t => if t.text == s && t.kind != .rejected then some (i + 1) else none
    | none => none
  | .nt n =>
    if classTerminals.contains n then
      match ts[i]? with
      | some t => if terminal n t then some (i + 1) else none
      | none => none
    else (rules.lookup n).bind (matchAt rules ts · i)
  | .seq parts => parts.foldlM (init := i) fun j p => matchAt rules ts p j
  | .alt _ options => options.findSome? (matchAt rules ts · i)
  | .opt _ g => some ((matchAt rules ts g i).getD i)
  | .star _ g =>
    let rec loop (j : Nat) (fuel : Nat) : Nat :=
      match fuel with
      | 0 => j
      | fuel + 1 => match matchAt rules ts g j with
        | some k => if k == j then j else loop k fuel
        | none => j
    some (loop i (ts.size + 1))
  | .plus id g => (matchAt rules ts g i).bind (matchAt rules ts (.star id g) ·)
  | .neg g => if (matchAt rules ts g i).isSome then none else some i

def grammarAccepts (rules : List (String × G)) (start source : String) : Bool :=
  let ts := toks source
  matchAt rules ts (.nt start) 0 == some ts.size

def parserAccepts (entry : Entry) (source : String) : Bool :=
  (FrenParse.parse entry ⟨0⟩ source).toBool

/-! ## Inputs -/

def lcg (seed : Nat) : Nat := (seed * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

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
    seed := lcg seed
    let len := 5 + seed / 2 ^ 40 % 10
    let mut text := ""
    for _ in [:len] do
      seed := lcg seed
      text := text ++ " " ++ pieces[seed / 2 ^ 33 % pieces.length]!
    out := text :: out
  return out

def expressionPieces : List String :=
  ["x", "1", "true", "not", "-", "+", "*", "%", "<", "=", "and", "iff", "(", ")", "f(", ",", "if",
   "then", "else", "let", ":=", "in", "match", "{", "}", "E::A", "=>", "::", "\n%", "mod"]

def smallExpressionPieces : List String :=
  ["x", "not", "-", "<", "(", ")", "f(", "if"]

def declarationPieces : List String :=
  ["pub", "fn f(x: Int): Int :=", "fn f(", "x", "b?", ":", "Int", ")", "): Int :=", "mod m", "mod",
   "::", "%", "enum E {", "A", ",", "}", "expect e(", "expect e() {", "{", "expect c:", "assume",
   "a:", ":=", "let"]

/-- The texts near `text`: each with one token dropped, each with one token
written twice, and each with one matched pair of parentheses dropped. -/
def nearTexts (text : String) (pairsOnly : Bool := false) : List String :=
  let pieces := (FrenParse.tokenize ⟨0⟩ text).tape.toList.map (·.text)
  let tokenAt := pieces.zipIdx.filter fun (p, _) =>
    !(p.all fun c => c == ' ' || c == '\n' || c == '\t' || c == '\r') && !p.startsWith "--"
  let without (ks : List Nat) := String.join (pieces.zipIdx.filterMap fun (p, k) => if ks.contains k then none else some p)
  let doubled (k : Nat) := String.join (pieces.zipIdx.map fun (p, j) => if j == k then p ++ " " ++ p else p)
  -- Matched parentheses, by a stack of the open ones.
  let pairs := Id.run do
    let mut stack : List Nat := []
    let mut out : List (Nat × Nat) := []
    for (p, k) in pieces.zipIdx do
      if p == "(" then stack := k :: stack
      else if p == ")" then
        match stack with
        | o :: rest => out := (o, k) :: out; stack := rest
        | [] => pure ()
    return out
  if pairsOnly then pairs.map fun (o, c) => without [o, c] else
  (tokenAt.map fun (_, k) => without [k]) ++ (tokenAt.map fun (_, k) => doubled k) ++
    pairs.map fun (o, c) => without [o, c]

/-! ## Abstract syntax -/

/-- An expression tree: the fixed point of the chapter's `ExprF`, one
constructor for each of its constructors. -/
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

/-- `syntax.tree.productions`: the tree of each expression production. -/
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

def unaryName : SUnary → String | .Neg => "Neg" | .Not => "Not"
def binaryName : SBinary → String
  | .Add => "Add" | .Sub => "Sub" | .Mul => "Mul" | .Div => "Div" | .Mod => "Mod" | .Eq => "Eq"
  | .Ne => "Ne" | .Lt => "Lt" | .Le => "Le" | .Gt => "Gt" | .Ge => "Ge" | .And => "And"
  | .Or => "Or" | .Iff => "Iff"

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
  | .matchE s arms => .Match s (Fren.Seq.ofList (arms.map fun (p, b) => .mk! (Fren.Seq.ofList p) b))

/-- A tree from its top node: `Tree` is the fixed point of `ExprF`. -/
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

/-- `ExprF` maps over its subexpressions. -/
def mapLayer (f : α → β) : spec.surface.ExprF α → spec.surface.ExprF β
  | .Boolean b => .Boolean b
  | .Integer n => .Integer n
  | .Name p => .Name p
  | .Call p args => .Call p (Fren.Seq.ofList (args.toList.map f))
  | .Unary op e => .Unary op (f e)
  | .Binary op l r => .Binary op (f l) (f r)
  | .If c t e => .If (f c) (f t) (f e)
  | .Let x v b => .Let x (f v) (f b)
  | .Match s arms => .Match (f s) (Fren.Seq.ofList (arms.toList.map fun a => .mk! a.variant (f a.body)))

def pathText (p : Fren.Seq String) : String := "::".intercalate p.toList

/-- One `ExprF` node, whose subtrees are already written, in the chapter's
`fren2 trees` notation: the constructor's name and its fields. -/
def layerSexp : spec.surface.ExprF String → String
  | .Boolean b => s!"(Boolean {b})"
  | .Integer n => s!"(Integer {n})"
  | .Name p => s!"(Name {pathText p})"
  | .Call p args => s!"(Call {pathText p}" ++ String.join (args.toList.map (" " ++ ·)) ++ ")"
  | .Unary op e => s!"(Unary {unaryName op} {e})"
  | .Binary op l r => s!"(Binary {binaryName op} {l} {r})"
  | .If c t e => s!"(If {c} {t} {e})"
  | .Let x v b => s!"(Let {x} {v} {b})"
  | .Match s arms => s!"(Match {s}" ++
      String.join (arms.toList.map fun a => s!" (Arm {pathText a.variant} {a.body})") ++ ")"

partial def Tree.sexp (t : Tree) : String := layerSexp (mapLayer Tree.sexp t.layer)

def typeTree : Ty → spec.surface.TypeName
  | .bool _ => .Boolean
  | .int _ => .Integer
  | .named p => .Named (Fren.Seq.ofList (pathOf p))

def typeSexp : spec.surface.TypeName → String
  | .Boolean => "Boolean"
  | .Integer => "Integer"
  | .Named p => s!"(Named {pathText p})"

def paramTree (p : Parameter) : spec.surface.Parameter :=
  ⟨p.name.text, p.annotation.map (typeTree ·.2)⟩

def paramSexp (p : spec.surface.Parameter) : String :=
  match p.annotation with
  | some t => s!"(Parameter {p.name} {typeSexp t})"
  | none => s!"(Parameter {p.name})"

/-- The tree of a declaration (`syntax.tree.productions`), as the chapter's
`DeclarationF` over expression trees. -/
def declTree : Decl → spec.surface.DeclarationF Tree
  | .moduleDecl v _ p => .Module ⟨v.isSome, Fren.Seq.ofList (pathOf p)⟩
  | .enumDecl v _ n _ vs _ _ => .Enumeration ⟨v.isSome, n.text, Fren.Seq.ofList (vs.toList.map (·.text))⟩
  | .function v _ n ps _ r _ b =>
    .Function (.mk! v.isSome n.text (Fren.Seq.ofList (ps.values.toList.map paramTree)) (typeTree r) (abstract b))
  | .expectation _ n ps _ ms _ =>
    .Expectation (.mk! n.text (Fren.Seq.ofList (ps.values.toList.map paramTree))
      (Fren.Seq.ofList (ms.toList.map fun m =>
        .mk! (if m.kind == .assume then .Assume else .Expect) m.label.text (abstract m.body))))

/-- A `DeclarationF` node in the `fren2 trees` notation, read off its fields. -/
def declSexp : spec.surface.DeclarationF Tree → String
  | .Module d => s!"(Module {if d.public? then "pub " else ""}{pathText d.path})"
  | .Enumeration d =>
    s!"(Enumeration {if d.public? then "pub " else ""}{d.name}" ++ String.join (d.variants.toList.map (" " ++ ·)) ++ ")"
  | .Function d =>
    s!"(Function {if d.public? then "pub " else ""}{d.name}" ++
      String.join (d.parameters.toList.map (" " ++ paramSexp ·)) ++ s!" {typeSexp d.result} {d.body.sexp})"
  | .Expectation d =>
    s!"(Expectation {d.name}" ++ String.join (d.parameters.toList.map (" " ++ paramSexp ·)) ++
      String.join (d.members.toList.map fun m =>
        s!" (Member {match m.kind with | .Assume => "Assume" | .Expect => "Expect"} {m.label} {m.body.sexp})") ++ ")"

def exprSexp? (source : String) : Option String :=
  match FrenParse.parseExpression ⟨0⟩ source with
  | .ok { root := .expression e, .. } => some (abstract e).sexp
  | _ => none

def fileSexp? (source : String) : Option String :=
  match FrenParse.parseFile ⟨0⟩ source with
  | .ok { root := .declarations ds, .. } => some ("(File" ++ String.join (ds.toList.map fun d => " " ++ declSexp (declTree d)) ++ ")")
  | _ => none

/-- `syntax.tree.well-formed`: every call has an argument and every name is
an `Identifier` of the chapter (a word, not a keyword). -/
partial def Tree.wellFormed : Tree → Bool
  | .boolean _ | .integer _ => true
  | .name p => !p.isEmpty && p.all identifier
  | .call p args => !p.isEmpty && p.all identifier && !args.isEmpty && args.all Tree.wellFormed
  | .unary _ e => e.wellFormed
  | .binary _ l r => l.wellFormed && r.wellFormed
  | .ifE c t e => c.wellFormed && t.wellFormed && e.wellFormed
  | .letE x v b => identifier x && v.wellFormed && b.wellFormed
  | .matchE s arms => s.wellFormed && arms.all fun (p, b) => p.length >= 2 && p.all identifier && b.wellFormed
where
  identifier (w : String) : Bool := spec.surface.«identifier?» w

/-- Whether each declaration of a file is well formed (`syntax.tree.well-formed`). -/
def fileTrees? (source : String) : Option (List Bool) :=
  let ident (t : Token) := spec.surface.«identifier?» t.text
  let path (p : Path) := (p.head :: p.tail.toList.map (·.2)).all ident
  let ty : Ty → Bool := fun | .named p => path p | _ => true
  let param (p : Parameter) := ident p.name && (p.annotation.map (ty ·.2)).getD true
  match FrenParse.parseFile ⟨0⟩ source with
  | .ok { root := .declarations ds, .. } => some <| ds.toList.map fun
    | .moduleDecl _ _ p => path p
    | .enumDecl _ _ n _ vs _ _ => ident n && vs.all ident
    | .function _ _ n ps _ r _ b => ident n && ps.values.all param && ty r && (abstract b).wellFormed
    | .expectation _ n ps _ ms _ =>
      ident n && ps.values.all param && ms.all fun m => ident m.label && (abstract m.body).wellFormed
  | _ => none

def tree? (source : String) : Option Tree :=
  match FrenParse.parseExpression ⟨0⟩ source with
  | .ok { root := .expression e, .. } => some (abstract e)
  | _ => none

/-! ## Printing -/

structure Printed where
  text : String
  category : Category
  isOpen : Bool

instance : Inhabited Printed := ⟨⟨"", .Primary, false⟩⟩

def fitsBare (child : Printed) (place : Category) (followed : Bool) : Bool :=
  spec.surface.«fits?» child.category child.isOpen place followed

/-- `place` gets `child`, in parentheses where `fits?` says it does not fit. -/
def placed (child : Printed) (place : Category) (followed : Bool) : String :=
  if spec.surface.«fits?» child.category child.isOpen place followed then child.text
  else "(" ++ child.text ++ ")"

/-- The text of `syntax.property.unambiguous`. -/
partial def Tree.print : Tree → Printed
  | .boolean b => ⟨toString b, .Primary, false⟩
  | .integer n => ⟨toString n, .Primary, false⟩
  | .name p => ⟨"::".intercalate p, .Primary, false⟩
  | .call p args =>
    ⟨"::".intercalate p ++ "(" ++ ", ".intercalate (args.map fun a => placed a.print .Expression false) ++ ")",
     .Primary, false⟩
  | .unary op e =>
    let e := e.print
    let bare := fitsBare e (spec.surface.unary_category op) false
    ⟨spellUnary op ++ " " ++ placed e (spec.surface.unary_category op) false,
     spec.surface.unary_category op, bare && e.isOpen⟩
  | .binary op l r =>
    let (l, r) := (l.print, r.print)
    let bare := fitsBare r (spec.surface.right_category op) false
    ⟨placed l (spec.surface.left_category op) true ++ " " ++ spellBinary op ++ " " ++
      placed r (spec.surface.right_category op) false,
     spec.surface.binary_category op, bare && r.isOpen⟩
  | .ifE c t e =>
    ⟨s!"if {placed c.print .Expression false} then {placed t.print .Expression false} else " ++
      placed e.print .Expression false, .Primary, true⟩
  | .letE x v b =>
    ⟨s!"let {x} := {placed v.print .Iff false} in {placed b.print .Expression false}", .Expression, true⟩
  | .matchE s arms =>
    ⟨s!"match {placed s.print .Primary false} \{ " ++
      ", ".intercalate (arms.map fun (p, b) => "::".intercalate p ++ " => " ++ placed b.print .Iff false) ++
      " }", .Primary, false⟩

/-- A seeded pseudo-random well-formed tree of at most `depth` levels. -/
partial def randomTree (seed : Nat) : Nat → Tree × Nat
  | 0 => let s := lcg seed
    (match s / 2 ^ 33 % 4 with
      | 0 => .name ["x"] | 1 => .integer (s / 2 ^ 40 % 100) | 2 => .boolean (s / 2 ^ 41 % 2 == 0)
      | _ => .name ["E", "A"], s)
  | depth + 1 =>
    let s := lcg seed
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

def randomTrees (count depth seed : Nat) : List Tree := Id.run do
  let mut seed := seed
  let mut out := []
  for _ in [:count] do
    let (t, s) := randomTree seed depth
    seed := s
    out := t :: out
  return out

/-- A seeded pseudo-random file of declarations, printed, with every list
policy, `pub`, paths and member forms; one parameter in twenty has neither
a type nor a `?`, which no file may have. -/
def randomFile (seed : Nat) : String × Nat := Id.run do
  let mut s := seed
  let mut out := ""
  let pick (s : Nat) (n : Nat) : Nat := s / 2 ^ 33 % n
  s := lcg s
  for _ in [:1 + pick s 3] do
    s := lcg s
    let vis := if pick s 2 == 0 then "pub " else ""
    s := lcg s
    let trailing := if pick s 2 == 0 then "," else ""
    s := lcg s
    let params := Id.run do
      let mut ps := []
      let mut s := s
      for _ in [:1 + pick s 3] do
        s := lcg s
        ps := ps ++ [match pick s 20 with
          | 0 => "y" | 1 | 2 | 3 => "b?" | 4 | 5 => "b?: Bool" | 6 => "e: E::T" | _ => "x: Int"]
      return ", ".intercalate ps
    s := lcg s
    let (body, s') := randomTree s 3
    s := s'
    let body := body.print.text
    let (other, s'') := randomTree s 2
    s := lcg s''
    let other := other.print.text
    let expectParams := if pick s 3 == 0 then "" else params ++ trailing
    out := out ++ match pick s 4 with
      | 0 => s!"{vis}mod {if pick s 3 == 0 then "a::b" else "m"}\n"
      | 1 => s!"{vis}enum E \{ A, B{trailing} }\n"
      | 2 => s!"{vis}fn f({params}{trailing}): Int := {body}\n"
      | _ => s!"expect e({expectParams}) \{ assume a: {other} expect c: {body} }\n"
  return (out, s)

def randomFiles (count seed : Nat) : List String := Id.run do
  let mut seed := seed
  let mut out := []
  for _ in [:count] do
    let (f, s) := randomFile seed
    seed := s
    out := f :: out
  return out

/-! ## The checks -/

/-- For each pair of binary operators, an `if` whose `else` branch ends in the
first and is the left operand of the second, and the same at the start of an
`else`: dropping their parentheses makes the operators meet where an `else`
branch ends. -/
def elseTrees : List Tree :=
  let (x, y, z) := (Tree.name ["x"], Tree.name ["y"], Tree.name ["z"])
  binaryOps.flatMap fun a => binaryOps.map fun b =>
    .binary b (.ifE x y (.binary a x y)) (.binary b y z)

/-- Inputs for `grammar_agrees`, as (start nonterminal, text). Bounded: as
an `ExpressionEntry`, every sequence of up to three of `expressionPieces` (30),
every sequence of up to five of `smallExpressionPieces` (8), 1000 random
sequences of 5 to 14 of them, 500 printed random trees and the texts near
them; as a `File`, every sequence of up to three of `declarationPieces` (25),
1000 random sequences, 200 printed random files and the texts near them, and
the chapter's `fren2` and `fren2 rejected` blocks. -/
def grammarInputs (md : String) : List (String × String) :=
  let exprs := (randomTrees 500 4 4049 ++ elseTrees).map (·.print.text)
  let files := randomFiles 200 77
  -- Texts near valid ones first: they find a wrong rule soonest.
  ((exprs ++ exprs.flatMap nearTexts).map ("ExpressionEntry", ·)) ++
  ((files ++ files.flatMap nearTexts ++ ((blocks md "fren2") ++ (blocks md "fren2 rejected")).map (·.2)).map ("File", ·)) ++
  ((sequences expressionPieces 3 ++ sequences smallExpressionPieces 5 ++
      randomSequences expressionPieces 1000 7).map ("ExpressionEntry", ·)) ++
  ((sequences declarationPieces 3 ++ randomSequences declarationPieces 1000 11).map ("File", ·))

--@ reference: syntax.notation.trivia-sensitive
--@ reference: syntax.file.syntax
--@ reference: syntax.declaration.syntax
--@ reference: syntax.declaration.lists
--@ reference: syntax.expression.syntax
--@ reference: parsing.grammar.acceptance
/-- The chapter's grammar, read strictly and run as written, accepts exactly
what the parser accepts, on `grammarInputs`. -/
def grammar_agrees (md : String) (inputs : List (String × String)) : Except String Unit := do
  let rules ← grammarOf md
  for (start, text) in inputs do
    let entry := if start == "File" then Entry.file else .expression
    if grammarAccepts rules start text != parserAccepts entry text then
      throw s!"the grammar and the parser disagree on {start} {repr text}"

/-- The choices and repetitions of the grammar, but those of `ExpressionEntry`
and those under a `!`. -/
partial def G.choices : G → List String
  | .term _ | .nt _ | .neg _ => []
  | .seq gs => gs.flatMap G.choices
  | .alt id gs => (List.range gs.length).map (s!"{id}/{·}") ++ gs.flatMap G.choices
  | .opt id g | .star id g | .plus id g => id :: g.choices

/-- The chapter's `fren2` blocks use every choice and repetition of the
grammar: each alternative of each `|`, and each `?`, `*` and `+` at least once. -/
def examples_cover (md : String) : Except String Unit := do
  let rules ← grammarOf md
  let used := (blocks md "fren2").flatMap fun (_, body) =>
    match run rules (toks body) (.nt "File") 0 with
    | some (_, used) => used
    | none => []
  let missing := (rules.filter (·.1 != "ExpressionEntry")).flatMap (·.2.choices) |>.filter fun c => !(used.contains c)
  unless missing.isEmpty do throw s!"the `fren2` examples use no match of {missing}"

/-- `syntax.expression.terminals`: the grammar's punctuators are exactly
`PUNCTUATORS`, its keywords exactly `GRAMMAR_KEYWORDS`, and its other words
exactly `CONTEXTUAL`. -/
partial def G.terminals : G → List String
  | .term s => [s]
  | .nt _ => []
  | .seq gs | .alt _ gs => gs.flatMap G.terminals
  | .opt _ g | .star _ g | .plus _ g | .neg g => g.terminals

--@ reference: syntax.expression.terminals
def terminals_agree (md : String) : Except String Unit := do
  let rules ← grammarOf md
  let ts := (rules.flatMap fun (_, g) => g.terminals).eraseDups
  let isWord (t : String) := t.toList.all Char.isAlpha
  let words := ts.filter isWord
  unless decide (spec.lexical.PUNCTUATORS = Fren.FinSet.ofList (ts.filter fun t => !(isWord t))) do
    throw "the grammar's punctuators are not `PUNCTUATORS`"
  unless decide (spec.surface.GRAMMAR_KEYWORDS = Fren.FinSet.ofList (words.filter FrenParse.keywords.contains)) do
    throw "the grammar's keywords are not `GRAMMAR_KEYWORDS`"
  unless decide (spec.surface.CONTEXTUAL = Fren.FinSet.ofList (words.filter fun w => !(FrenParse.keywords.contains w))) do
    throw "the grammar's other words are not `CONTEXTUAL`"

--@ reference: syntax.tree.operators
/-- `syntax.tree.operators`: the parser reads each binary spelling as that
operator and no other punctuator or keyword as a binary operator, orders the
binary operators' precedences as the chapter's categories rank them, and reads
each unary spelling before an operand as that unary operator. -/
def operators_agree : Bool :=
  let prec (op : SBinary) : Option Nat := (FrenParse.binaryOperator (spellBinary op)).map (·.2)
  let rank (op : SBinary) : Int := spec.surface.rank (spec.surface.binary_category op)
  binaryOps.all (fun op => match FrenParse.binaryOperator (spellBinary op) with
    | some (ast, _) => binaryOf ast == op
    | none => false) &&
  binaryOps.all (fun a => binaryOps.all fun b =>
    match prec a, prec b with
    | some p, some q => (p < q) == (rank a < rank b)
    | _, _ => false) &&
  (["(", ")", "{", "}", ",", ":", ":=", "=>", "::", "not", "in", "if", "let", "mod", "x", "1", "assume"].all
    fun s => (FrenParse.binaryOperator s).isNone) &&
  unaryOps.all fun op => exprSexp? (spellUnary op ++ " x") == some s!"(Unary {unaryName op} (Name x))"

#guard operators_agree

--@ reference: syntax.property.unambiguous
--@ reference: parsing.grammar.trees
/-- `syntax.property.unambiguous`: the printed text of a well-formed tree
parses back to the tree, and dropping any pair of its parentheses gives a text
that is rejected or has another tree; ill-formed trees do not come back.
Bounded: 1000 seeded random trees of depth at most 5, every pair of binary
operators and every unary operator around binary operands, and seven
ill-formed trees. -/
def roundtrip_agrees : Bool := Id.run do
  let x := Tree.name ["x"]
  let y := Tree.name ["y"]
  let z := Tree.name ["z"]
  let mut trees := randomTrees 1000 5 2026
  for a in binaryOps do
    for b in binaryOps do
      trees := .binary a (.binary b x y) z :: .binary a x (.binary b y z) :: trees
    for u in unaryOps do
      trees := .unary u (.binary a x y) :: .binary a (.unary u x) y :: .binary a x (.unary u y) :: trees
  let illFormed : List Tree := [.call ["f"] [], .name [], .call [] [x],
    .matchE x [(["A"], y)], .letE "true" x y, .name ["E", "not"], .binary .Add (.name ["if"]) x]
  let same (t : Tree) (text : String) := (tree? text).map (·.sexp) == some t.sexp
  -- Dropping a matched pair of parentheses; calls' parentheses included.
  let minimal (t : Tree) := (nearTexts t.print.text true).all fun near =>
    near == t.print.text || !same t near
  return trees.all (fun t => same t t.print.text && minimal t) &&
    illFormed.all fun t => !t.wellFormed && !same t t.print.text

#guard roundtrip_agrees

/-- A declaration tree printed: its tokens, with each expression printed as
`syntax.property.unambiguous` says, and a trailing comma when `trailing`. -/
def declPrint (trailing : Bool) : spec.surface.DeclarationF Tree → String
  | .Module d => s!"{if d.public? then "pub " else ""}mod {pathText d.path}"
  | .Enumeration d =>
    s!"{if d.public? then "pub " else ""}enum {d.name} \{ " ++ ", ".intercalate d.variants.toList ++
      (if trailing then "," else "") ++ " }"
  | .Function d =>
    s!"{if d.public? then "pub " else ""}fn {d.name}(" ++ ", ".intercalate (d.parameters.toList.map paramText) ++
      (if trailing then "," else "") ++ s!"): {typeText d.result} := {d.body.print.text}"
  | .Expectation d =>
    s!"expect {d.name}(" ++ ", ".intercalate (d.parameters.toList.map paramText) ++
      (if trailing && !d.parameters.toList.isEmpty then "," else "") ++ ") { " ++
      " ".intercalate (d.members.toList.map fun m =>
        s!"{match m.kind with | .Assume => "assume" | .Expect => "expect"} {m.label}: {m.body.print.text}") ++ " }"
where
  typeText : spec.surface.TypeName → String
    | .Boolean => "Bool" | .Integer => "Int" | .Named p => pathText p
  paramText (p : spec.surface.Parameter) : String :=
    p.name ++ ((p.annotation.map fun t => ": " ++ typeText t).getD "")

/-- A seeded pseudo-random declaration tree, with random visibility, names,
paths, parameters, types and members. -/
def randomDecl (seed : Nat) : spec.surface.DeclarationF Tree × Nat := Id.run do
  let mut s := lcg seed
  let pick (s n : Nat) : Nat := s / 2 ^ 33 % n
  let names := ["a", "b", "c?", "next_step", "Bool", "Int", "T"]
  let name (s : Nat) := names[pick s 4]!
  let isPub := pick s 2 == 0
  s := lcg s
  let path := Fren.Seq.ofList ((List.range (1 + pick s 3)).map fun i => names[(pick s 7 + i) % 7]!)
  s := lcg s
  let types : List spec.surface.TypeName := [.Boolean, .Integer, .Named (Fren.Seq.ofList ["E"]),
    .Named (Fren.Seq.ofList ["Int", "T"])]
  let params := (List.range (1 + pick s 3)).map fun i =>
    let n := names[(pick s 5 + i) % 4]!
    let t := types[(pick s 11 + i) % 4]!
    (⟨n, if n.endsWith "?" && (pick s 13 + i) % 2 == 0 then none else some t⟩ : spec.surface.Parameter)
  s := lcg s
  let (body, s') := randomTree s 3
  let (other, s'') := randomTree s' 2
  s := lcg s''
  let decl : spec.surface.DeclarationF Tree := match pick s 4 with
    | 0 => .Module ⟨isPub, path⟩
    | 1 => .Enumeration ⟨isPub, name s, Fren.Seq.ofList (names.take (1 + pick s 3))⟩
    | 2 => .Function (.mk! isPub (name s) (Fren.Seq.ofList params) (types[pick s 4]!) body)
    | _ => .Expectation (.mk! (name s) (Fren.Seq.ofList (if pick s 3 == 0 then [] else params))
        (Fren.Seq.ofList [.mk! .Assume "a" other, .mk! .Expect "c" body]))
  return (decl, s)

--@ reference: syntax.tree.productions
--@ reference: parsing.grammar.declaration-trees
/-- `parsing.grammar.declaration-trees`: a generated declaration tree, printed
and parsed, gives back that tree, field for field. The trees are generated
independently of the parser. Bounded: 1000 seeded random files of one to three
declarations, with and without trailing commas. -/
def declarations_agree : Bool := Id.run do
  let mut seed := 9091
  for _ in [:1000] do
    let mut decls := []
    for _ in [:1 + seed / 2 ^ 33 % 3] do
      let (d, s) := randomDecl seed
      seed := s
      decls := decls ++ [d]
    let trailing := seed % 2 == 0
    let text := "\n".intercalate (decls.map (declPrint trailing))
    let expected := "(File" ++ String.join (decls.map fun d => " " ++ declSexp d) ++ ")"
    if fileSexp? text != some expected then return false
  return true

#guard declarations_agree

--@ reference: syntax.path.syntax
--@ reference: syntax.tree.productions
--@ reference: syntax.tree.well-formed
/-- `syntax.tree.productions` and `syntax.tree.well-formed`: each line of the
chapter's `fren2 trees` blocks has the tree it states, and the tree of every
expression that the parser accepts among `grammarInputs` is well formed. -/
def trees_agree (md : String) (inputs : List (String × String)) : Except String Unit := do
  for (line, body) in blocks md "fren2 trees" do
    for l in body.splitOn "\n" do
      let [text, expected] := l.splitOn " -- " | throw s!"Syntax.md:{line}: `{l}` is not `text -- tree`"
      let actual := if expected.startsWith "(File" then fileSexp? text else exprSexp? text
      unless actual == some expected do
        throw s!"Syntax.md:{line}: the tree of `{text}` is {actual}"
  for (start, text) in inputs do
    if start == "ExpressionEntry" then
      if let some t := tree? text then
        unless t.wellFormed do throw s!"the tree of {repr text} is not well formed"
    else if let some ds := fileTrees? text then
      unless ds.all id do throw s!"a declaration of {repr text} is not well formed"

--@ reference: syntax.expression.extent
/-- `syntax.expression.extent`: each line `lhs -- rhs` of a `fren2 groups`
block has the same tree on both sides. -/
def groups_agree (md : String) : Except String Unit := do
  for (line, body) in blocks md "fren2 groups" do
    for l in body.splitOn "\n" do
      let [lhs, rhs] := l.splitOn " -- " | throw s!"Syntax.md:{line}: `{l}` is not `lhs -- rhs`"
      unless (exprSexp? lhs).isSome && exprSexp? lhs == exprSexp? rhs do
        throw s!"Syntax.md:{line}: `{lhs}` does not group as `{rhs}`"

/-- The line of a byte offset, from 1. -/
def lineOf (text : String) (offset : Nat) : Nat :=
  ((String.fromUTF8! (text.toUTF8.extract 0 offset)).toList.filter (· == '\n')).length + 1

/-- Each `fren2` block is accepted, and each `fren2 rejected` block is
rejected, with the diagnostic that its `--~ error:` annotation states on the
annotated line; the sentence before the block names the rule it breaks. -/
def examples_agree (md : String) : Except String Unit := do
  for (line, body) in blocks md "fren2" do
    unless parserAccepts .file body do throw s!"Syntax.md:{line}: the parser rejects a `fren2` block"
  let ids := ((md.splitOn "\n").filter (·.startsWith "r[")).map fun l => ((l.drop 2).takeWhile (· != ']')).toString
  let lines := (md.splitOn "\n").toArray
  for (line, body) in blocks md "fren2 rejected" do
    let before := ((lines.extract 0 (line - 1)).toList.reverse.dropWhile (·.trimAscii.isEmpty)
      |>.takeWhile (!·.trimAscii.isEmpty)).getLast?
    unless before.any fun b => ids.any fun id => b.startsWith s!"`{id}`:" do
      throw s!"Syntax.md:{line}: no sentence before the rejected block names the rule it breaks"
    let some (k, note) := (body.splitOn "\n").zipIdx.findSome? (fun (l, k) =>
        match l.splitOn "--~ error: " with | [_, msg] => some (k + 1, msg) | _ => none)
      | throw s!"Syntax.md:{line}: a rejected block has no `--~ error:` annotation"
    match FrenParse.parseFile ⟨0⟩ body with
    | .ok _ => throw s!"Syntax.md:{line}: the parser accepts a rejected block"
    | .error f =>
      unless lineOf body f.diagnostic.span.start == k && "expected " ++ f.diagnostic.expected == note do
        throw s!"Syntax.md:{line}: the parser says {f.diagnostic.render} on line {lineOf body f.diagnostic.span.start}"

/-! ## Mutation control

Each of these changes to the chapter's grammar makes it wrong, and the checks
above must notice: the grammar check, the coverage check or the strict reader
fails on each. -/
def mutants : List (String × String × String) := [
  ("fn-no-trailing-comma", "Parameter (\",\" Parameter)* \",\"? \")\"\n", "Parameter (\",\" Parameter)* \")\"\n"),
  ("call-no-trailing-comma", "Expression (\",\" Expression)* \",\"? \")\"", "Expression (\",\" Expression)* \")\""),
  ("call-empty", "Path TouchingOpen Expression (\",\" Expression)* \",\"? \")\"", "Path TouchingOpen (Expression (\",\" Expression)* \",\"?)? \")\""),
  ("scrutinee-negation", "\"match\" Primary", "\"match\" Negation"),
  ("arm-expression", "Arm         ::= QualifiedPath \"=>\" Iff", "Arm         ::= QualifiedPath \"=>\" Expression"),
  ("arm-unqualified", "Arm         ::= QualifiedPath \"=>\" Iff", "Arm         ::= Path \"=>\" Iff"),
  ("no-compare-lookahead", "Sum (CompareOp Sum)? !CompareOp", "Sum (CompareOp Sum)?"),
  ("no-iff-lookahead", "Or (\"iff\" Or)? !\"iff\"", "Or (\"iff\" Or)?"),
  ("let-definition-expression", "\"let\" Identifier \":=\" Iff \"in\"", "\"let\" Identifier \":=\" Expression \"in\""),
  ("not-once", "Not         ::= \"not\" Not | Comparison", "Not         ::= \"not\" Comparison | Comparison"),
  ("negation-once", "Negation    ::= \"-\" Negation | Primary", "Negation    ::= \"-\" Primary | Primary"),
  ("expect-params-nonempty", "TouchingOpen (Parameter (\",\" Parameter)* \",\"?)? \")\"", "TouchingOpen Parameter (\",\" Parameter)* \",\"? \")\""),
  ("expect-params-no-trailing", "TouchingOpen (Parameter (\",\" Parameter)* \",\"?)? \")\"", "TouchingOpen (Parameter (\",\" Parameter)*)? \")\""),
  ("module-identifier", "\"pub\"? \"mod\" Path", "\"pub\"? \"mod\" Identifier"),
  ("typo", "| Primary\nPrimary", "| Primry\nPrimary"),
  ("unbalanced", "((\"+\" | \"-\") Product)*", "((\"+\" | \"-\") Product*"),
  ("else-optional", "\"then\" Expression \"else\" Expression", "\"then\" Expression (\"else\" Expression)?"),
  ("path-before-call", "Numeral | Call | Path |", "Numeral | Path | Call |"),
  ("member-iff", "Identifier \":\" Expression\n", "Identifier \":\" Iff\n"),
  ("pub-expect", "ExpectationDeclaration ::= \"expect\"", "ExpectationDeclaration ::= \"pub\"? \"expect\""),
  ("question-first", "Parameter              ::= Identifier \":\" Type | QuestionIdentifier", "Parameter              ::= QuestionIdentifier | Identifier \":\" Type"),
  ("question-any", "Parameter              ::= Identifier \":\" Type | QuestionIdentifier", "Parameter              ::= Identifier \":\" Type | Identifier"),
  ("sum-once", "Sum         ::= Product ((\"+\" | \"-\") Product)*", "Sum         ::= Product ((\"+\" | \"-\") Product)?"),
  ("or-once", "Or          ::= And (\"or\" And)*", "Or          ::= And (\"or\" And)?"),
  ("not-dropped", "Not         ::= \"not\" Not | Comparison", "Not         ::= Comparison"),
  ("ge-dropped", "\"<=\" | \">\" | \">=\"", "\"<=\" | \">\""),
  ("type-identifier", "Type          ::= Path", "Type          ::= Identifier"),
  ("enum-empty", "\"{\" Identifier (\",\" Identifier)* \",\"? \"}\"", "\"{\" (Identifier (\",\" Identifier)* \",\"?)? \"}\""),
  ("paren-iff", "| \"(\" Expression \")\" |", "| \"(\" Iff \")\" |"),
  ("remainder-dropped", "(\"*\" | \"div\" | \"%\")", "(\"*\" | \"div\")"),
  ("duplicate-rule", "CompareOp   ::=", "Sum         ::= Product\nCompareOp   ::="),
  ("unread-group", "((\"+\" | \"-\") Product)*", "((\"+\" | \"-\" Product)*"),
  ("stray-character", "Negation    ::= \"-\" Negation", "Negation    ::= \"-\" Negation ;"),
  ("unreachable-rule", "QualifiedPath ::=", "Unused        ::= Path\nQualifiedPath ::=")]

/-- Inputs for the mutation control: the chapter's blocks first, then texts
near printed trees and files, then every sequence of up to three pieces. -/
def mutantInputs (md : String) : List (String × String) :=
  let exprs := (elseTrees ++ randomTrees 200 4 4049).map (·.print.text)
  let files := randomFiles 100 77
  (((blocks md "fren2") ++ (blocks md "fren2 rejected")).map ("File", ·.2)) ++
  ((exprs ++ exprs.flatMap nearTexts).map ("ExpressionEntry", ·)) ++
  ((files ++ files.flatMap nearTexts).map ("File", ·)) ++
  ((sequences expressionPieces 3).map ("ExpressionEntry", ·)) ++
  ((sequences declarationPieces 3).map ("File", ·))

/-- Every mutant breaks a check; a mutant whose text is not found is an error. -/
def mutants_caught (md : String) (inputs : List (String × String)) : Except String Unit := do
  for (name, old, new) in mutants do
    unless (md.splitOn old).length == 2 do throw s!"the mutant `{name}` finds no `{old}` in the chapter"
    let m := md.replace old new
    let caught := (examples_cover m).toBool == false || (grammar_agrees m inputs).toBool == false
    unless caught do throw s!"no check catches the mutant `{name}`"

/-! ## Status names

Each `tested` or `lean` status of the chapter names a declaration that exists. -/
open Lean in
def statusNames (md : String) : List String :=
  (md.splitOn "\n").filterMap fun l =>
    match (l.trimAscii.toString.dropPrefix? "<!-- status: ").map (·.toString) with
    | some rest => match rest.splitOn " " with
      | [kind, name, "-->"] => if kind == "tested" || kind == "lean" then some name else none
      | _ => none
    | none => none

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let md ← IO.FS.readFile chapterPath
  let inputs := grammarInputs md
  let checks : List (String × (Unit → Except String Unit)) := [
      ("grammar_agrees", fun _ => grammar_agrees md inputs), ("terminals_agree", fun _ => terminals_agree md),
      ("trees_agree", fun _ => trees_agree md (inputs.take 80000)), ("groups_agree", fun _ => groups_agree md),
      ("examples_agree", fun _ => examples_agree md), ("examples_cover", fun _ => examples_cover md),
      ("mutants_caught", fun _ => mutants_caught md (mutantInputs md))]
  for (name, check) in checks do
    if let .error e := check () then throwError s!"{name}: {e}"
  for name in statusNames md do
    unless (← getEnv).contains name.toName do throwError s!"the status names `{name}`, which does not exist"

end Spec.Language.Syntax
