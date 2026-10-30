-- keep-sorted start
import FrenCli.Parse
import Lean.Elab.Term
-- keep-sorted end

/-!
# Fren quotations in Lean

`fren_expr!{ e }` is the tree (`Fren.Core.Tree`) of the Fren expression `e`,
which a lint's fix writes (`Reqs/Lint/Printing`). `e` is read by the
parser of the `fren` command, at Lean's elaboration time, so a quotation
means what the binary would read. In `e`, an antiquotation stands for a
subtree:

- `$x`, or `$(t)` for a Lean term `t`, is an expression: anything with a
  `Fren.Core.ToTree` instance, such as a `Tree`, or a `BText`, an
  expression as written with its precedence;
- `$xs,*`, among the arguments of an application or a method, or the
  elements of a set or sequence literal, is each of the array `xs`;
- in a pattern, `$p` is the `String` `p`, and `$ps|*` is the array of
  strings `ps`, as alternatives.

`$x` is a Lean identifier of one component: a `.` after it is Fren's, so
`$x.len` reads the field `len` of `x`'s tree. An antiquotation is Lean
syntax, read by Lean's parser where the quotation is, so in a macro it
refers to the macro's bindings. The text of `e` may not write
`fren_hole_`, which stands for the antiquotations in what the parser
reads, nor can an antiquotation be part of a name or a literal of an
expression; nor can `$xs,*` be operands of a chained comparison, which has
one operand between each two operators.

The parentheses written in `e` are not kept: `Tree.print` writes those that
the grammar needs. Nor is the layout of `e`. A quotation has no comments:
`--` is not read as one, so a `}`, a `"` or a `$` after it is the
quotation's.

The module is imported by `FrenCore.Lint`, which builds fixes with
`fren_expr!`; it needs only the parser, not the elaborator of the
`fren` command.
-/

namespace FrenCli.Quote

open Lean Elab Term Parser

/-! ## The text of a quotation -/

/-- The text of `s` from `i`, a string literal's opening `"`, past its
closing one. -/
partial def skipString (c : ParserContext) (s : ParserState) : ParserState :=
  let i := s.pos
  if h : c.atEnd i then s
  else
    let ch := c.get' i h
    let s := s.next' c i h
    if ch == '"' then s
    else if ch == '\\' then
      let j := s.pos
      if h' : c.atEnd j then s else skipString c (s.next' c j h')
    else skipString c s

/-- How many braces are open after `text`, where `depth` were before it,
outside its string literals. -/
def braceDepth (depth : Nat) (text : String) : Nat := Id.run do
  let mut depth := depth
  let mut inString := false
  let mut escaped := false
  for ch in text.toList do
    if inString then
      if escaped then escaped := false
      else if ch == '\\' then escaped := true
      else if ch == '"' then inString := false
    else if ch == '"' then inString := true
    else if ch == '{' then depth := depth + 1
    else if ch == '}' then depth := depth - 1
  return depth

/-- Fren text of a quotation, up to an antiquotation's `$` or to the `}`
that closes the quotation, where `depth` braces are open: braces nest, and
string literals are skipped. -/
partial def chunkFn (depth : Nat) : ParserFn := fun c s =>
  let rec go (depth : Nat) (s : ParserState) : ParserState :=
    let i := s.pos
    if h : c.atEnd i then s.mkUnexpectedError "unterminated Fren quotation: expected `}`"
    else
      let ch := c.get' i h
      if ch == '$' || (ch == '}' && depth == 0) then s
      else
        let s := s.next' c i h
        if ch == '"' then go depth (skipString c s)
        else go (if ch == '{' then depth + 1 else if ch == '}' then depth - 1 else depth) s
  go depth s

/-- Whether `c` can be in the name of an antiquotation, `$x`: a Lean
identifier of one component, since `.` after it is Fren's. -/
def isHoleChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\''

/-- The name of `$x`, as a Lean identifier, so that a quotation in a macro
gets the macro's scopes on it. -/
def holeNameFn : ParserFn := fun c s =>
  let s := rawFn (takeWhile1Fn isHoleChar "a name or `(` after `$`") false c s
  if s.hasError then s else
  match s.stxStack.back with
  | .atom info val => s.popSyntax.pushSyntax (Syntax.ident info val.toRawSubstring (.mkSimple val) [])
  | _ => s

/-- `,*` or `|*` after an antiquotation, or nothing, as an atom. -/
def spliceFn : ParserFn := fun c s =>
  let i := s.pos
  let j := c.next i
  if !c.atEnd i && !c.atEnd j && (c.get i == ',' || c.get i == '|') && c.get j == '*' then
    rawFn (fun c s => let s := s.next c s.pos; s.next c s.pos) false c s
  else s.pushSyntax (Syntax.atom .none "")

/-- An antiquotation: `$`, then a name or a Lean term in parentheses, and
`,*` or `|*` for a splice. Its term is Lean's own syntax, read by Lean's
parser. -/
def holeFn : ParserFn := fun c s =>
  let iniSz := s.stackSize
  let s := chFn '$' false c s
  if s.hasError then s else
  let i := s.pos
  let s := if !c.atEnd i && c.get i == '(' then
      (andthenFn (rawCh '(' (trailingWs := true)).fn (andthenFn (termParser).fn (rawCh ')').fn)) c s
    else holeNameFn c s
  if s.hasError then s else
  (spliceFn c s).mkNode `FrenCli.Quote.hole iniSz

/-- The text of a quotation, up to the `}` that closes it: Fren text, as
atoms, between antiquotations. -/
partial def bodyFn : ParserFn := fun c s =>
  let iniSz := s.stackSize
  let rec loop (depth : Nat) (s : ParserState) : ParserState :=
    let s := rawFn (chunkFn depth) false c s
    if s.hasError then s else
    let depth := braceDepth depth s.stxStack.back.getAtomVal
    let i := s.pos
    if !c.atEnd i && c.get i == '$' then
      let s := holeFn c s
      if s.hasError then s else loop depth s
    else s
  (loop 0 s).mkNode `FrenCli.Quote.body iniSz

/-- The Fren text of a quotation, with its antiquotations. -/
def body : Parser := { fn := bodyFn }

open PrettyPrinter in
@[combinator_formatter body] def body.formatter : Formatter := pure ()

open PrettyPrinter in
@[combinator_parenthesizer body] def body.parenthesizer : Parenthesizer := pure ()

/-- `fren_expr!{ e }`: the tree of the Fren expression `e` (`FrenCli.Quote`). -/
syntax (name := frenExpr) "fren_expr!{" body "}" : term

/-! ## Antiquotations -/

/-- What an antiquotation stands for. -/
inductive Splice where
  /-- One expression, or in a pattern, one string. -/
  | one
  /-- `$xs,*`: each of an array, as arguments or elements. -/
  | commas
  /-- `$ps|*`: each of an array of strings, as alternatives of a pattern. -/
  | bars
  deriving BEq, Inhabited

/-- An antiquotation: its Lean term, and what it stands for. -/
structure Hole where
  term : Term
  splice : Splice
  deriving Inhabited

/-- The start of the identifiers that stand for the antiquotations in the
text that the parser reads, which a quotation may not write itself. -/
def holePrefix : String := "fren_hole_"

/-- The identifier that stands for the `i`th antiquotation. -/
def holeName (i : Nat) : String := s!"{holePrefix}{i}"

/-- The antiquotation that an identifier of the text stands for, if it is
one (`holeName`). -/
def holeOf? (holes : Array Hole) (x : String) : Option Hole := do
  guard (x.startsWith holePrefix)
  let i ← (x.drop holePrefix.length).toString.toNat?
  holes[i]?

/-- The text of a quotation, `body`, with each antiquotation replaced by its
`holeName`, and the antiquotations. -/
def antiquotations (body : Syntax) : TermElabM (String × Array Hole) := do
  let mut out := ""
  let mut holes : Array Hole := #[]
  for part in body.getArgs do
    match part with
    | .atom _ text =>
      if (text.splitOn holePrefix).length > 1 then
        throwErrorAt part "a Fren quotation cannot write `{holePrefix}`, which stands for its antiquotations"
      -- What follows an antiquotation would otherwise run into its name.
      if !holes.isEmpty && text.toList.head?.any isHoleChar then
        throwErrorAt part "in a Fren quotation, an antiquotation stands for an expression, list elements or a pattern, \
          not for part of a name or a literal"
      out := out ++ text
    | stx =>
      let args := stx.getArgs
      -- `$`, the name or `(`, term and `)`, and the splice.
      let term : Term := ⟨if args.size == 3 then args[1]! else args[2]!⟩
      let splice := match args.back!.getAtomVal with
        | ",*" => Splice.commas
        | "|*" => .bars
        | _ => .one
      holes := holes.push { term, splice }
      out := out ++ holeName (holes.size - 1)
  return (out, holes)

/-! ## Reading the text -/

/-- The Fren expression `text`, as the `fren` command reads the expression
of a constraint (`Parser.top`), and the text as characters. -/
def parseExpr (text : String) : Except String (Expr × Array Char) := do
  let chars := text.toList.toArray
  let toks ← match lex chars with
    | .ok toks => pure toks
    | .error e => throw e.msg.headline
  let read : P Expr := do
    let e ← Parser.top
    let t ← Parser.peek
    unless t.tok == .eof do Parser.fail t "the end of the expression"
    return e
  match read.run' { toks, src := chars } with
  | .ok e => return (e, chars)
  | .error e => throw e.msg.headline

/-! ## Building the tree -/

/-- The declaration `n` of `FrenCore.Lint`, which imports this module, as
it is named where a quotation is elaborated. -/
def core (n : Name) : Term := mkCIdent n

/-- The text of `sp` in `src`. -/
def spanText (src : Array Char) (sp : Span) : String := String.ofList (src.extract sp.start sp.stop).toList

/-- `s`, a name or a literal of the quotation, which an antiquotation cannot
be part of. -/
def plain (s : String) : TermElabM String := do
  if (s.splitOn holePrefix).length > 1 then
    throwError "in a Fren quotation, an antiquotation stands for an expression, list elements or a pattern, not for \
      part of a name or a literal"
  return s

/-- The term of type `String` of `text`, part of a pattern or of a
quantifier's binders, with its antiquotations, each a `String`, or for
`$ps|*`, an array of them. -/
def textTerm (holes : Array Hole) (text : String) : TermElabM Term := do
  let mut parts : Array Term := #[]
  let mut rest := text
  repeat
    let pieces := rest.splitOn holePrefix
    let some first := pieces.head? | break
    if pieces.length == 1 then
      parts := parts.push (quote first)
      break
    parts := parts.push (quote first)
    let after := (rest.drop (first.length + holePrefix.length)).toString
    let digits := after.takeWhile Char.isDigit |>.toString
    let some h := holes[digits.toNat!]? | throwError "unknown antiquotation in a Fren quotation"
    parts := parts.push <| ← match h.splice with
      | .one => `(($h.term : String))
      | .bars => `(" | ".intercalate ($h.term : Array String).toList)
      | .commas => throwError "`$xs,*` cannot be in a pattern; write `$xs|*` for alternatives"
    rest := (after.drop digits.length).toString
  `(String.join [$parts,*])

mutual
/-- The term of type `Fren.Core.Tree` that builds `e`, read from `src`. -/
partial def treeOf (holes : Array Hole) (src : Array Char) (e : Expr) : TermElabM Term := do
  let go := treeOf holes src
  match e with
  | .path _ #[x] =>
    let parts := x.name.splitOn "."
    match holeOf? holes parts.head! with
    | some h =>
      unless h.splice == .one do throwError "`{h.term}` stands for several expressions, which only a list can have"
      parts.tail.foldlM (fun t f => do `($(core `Fren.Core.Tree.field) $t $(quote (← plain f))))
        (← `($(core `Fren.Core.ToTree.toTree) $h.term))
    | none => `($(core `Fren.Core.Tree.atom) $(quote (← plain x.name)))
  | .path sp _ | .num sp _ | .str sp _ | .bool sp _ => `($(core `Fren.Core.Tree.atom) $(quote (← plain (spanText src sp))))
  | .bin _ op a b => `($(core `Fren.Core.Tree.bin) $(quote op) $(← go a) $(← go b))
  | .not _ a => `($(core `Fren.Core.Tree.not) $(← go a))
  | .neg _ a => `($(core `Fren.Core.Tree.neg) $(← go a))
  | .when _ n c d => `($(core `Fren.Core.Tree.when) $(quote n) $(← go c) $(← go d))
  | .ite _ c a b => `($(core `Fren.Core.Tree.ite) $(← go c) $(← go a) $(← go b))
  | .is _ x p => `($(core `Fren.Core.Tree.test) $(← go x) $(← textTerm holes (spanText src p.span)))
  -- One operand for each place between operators: no splice.
  | .chain _ es ops => `($(core `Fren.Core.Tree.chain) [$(← es.mapM go),*] $(quote (ops.map (·.1)).toList))
  | .app _ fn args =>
    `($(core `Fren.Core.Tree.app) $(quote (← plain ("::".intercalate (fn.map (·.name)).toList))) $(← listOf holes src args))
  | .method _ r m args => `($(core `Fren.Core.Tree.method) $(← go r) $(quote (← plain m.name)) $(← listOf holes src args))
  | .field _ r f => `($(core `Fren.Core.Tree.field) $(← go r) $(quote (← plain f.name)))
  | .index _ q i => `($(core `Fren.Core.Tree.index) $(← go q) $(← go i))
  | .set _ es => `($(core `Fren.Core.Tree.set) $(← listOf holes src es))
  | .seq _ es => `($(core `Fren.Core.Tree.seq) $(← listOf holes src es))
  | .quant _ all bs body =>
    let binders := match bs[0]?, bs.back? with
      | some f, some l => spanText src { start := f.span.start, stop := l.span.stop }
      | _, _ => ""
    `($(core `Fren.Core.Tree.quant) $(quote all) $(← textTerm holes binders) $(← go body))
  | .block .. | .record .. | .update .. | .match .. | .matches .. | .pair .. | .«let» .. | .table .. | .closure .. =>
    throwError "a Fren quotation has no tree for `{spanText src e.span}`: `Fren.Core.Tree` has only operators, conditionals, \
      pattern tests, quantifiers, applications, field reads, indexes and set and sequence literals"

/-- The term of type `List Fren.Core.Tree` of `es`, each of the array of a
`$xs,*` among them. -/
partial def listOf (holes : Array Hole) (src : Array Char) (es : Array Expr) : TermElabM Term := do
  let mut parts : Array Term := #[]
  for e in es do
    match e with
    | .path _ #[x] =>
      match holeOf? holes x.name with
      | some { term, splice := .commas } =>
        parts := parts.push (← `(($term).toList.map $(core `Fren.Core.ToTree.toTree)))
        continue
      | _ => pure ()
    | _ => pure ()
    parts := parts.push (← `([$(← treeOf holes src e)]))
  `(List.flatten [$parts,*])
end

/-- The text of a quotation as written. -/
def reprintBody (body : Syntax) : String :=
  String.join (body.getArgs.toList.map fun part => match part with
    | .atom _ text => text
    | stx => (stx.reprint.getD "").trimAscii.toString)

@[term_elab frenExpr] def elabFrenExpr : TermElab := fun stx expected? => do
  let (text, holes) ← antiquotations stx[1]
  let (e, src) ← match parseExpr text with
    | .ok r => pure r
    | .error msg => throwErrorAt stx[1] "in the Fren quotation `{(reprintBody stx[1]).trimAscii}`: {msg}"
  let t ← withRef stx (treeOf holes src e)
  elabTerm (← `(($t : $(core `Fren.Core.Tree)))) expected?

end FrenCli.Quote
