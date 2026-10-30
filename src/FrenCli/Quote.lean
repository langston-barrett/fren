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

The parentheses written in `e` are not kept: `Tree.print` writes those that
the grammar needs. So is everything that the tree does not say: comments,
and the layout of `e`.

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

/-- The text of a quotation, up to the `}` that closes it: braces nest,
and string literals are skipped. -/
partial def bodyFn : ParserFn := fun c s =>
  let rec go (depth : Nat) (s : ParserState) : ParserState :=
    let i := s.pos
    if h : c.atEnd i then s.mkUnexpectedError "unterminated Fren quotation: expected `}`"
    else
      let ch := c.get' i h
      if ch == '}' && depth == 0 then s
      else
        let s := s.next' c i h
        if ch == '"' then go depth (skipString c s)
        else go (if ch == '{' then depth + 1 else if ch == '}' then depth - 1 else depth) s
  go 0 s

/-- The Fren text of a quotation, as one atom. -/
def body : Parser := { fn := rawFn bodyFn (trailingWs := false) }

open PrettyPrinter in
@[combinator_formatter body] def body.formatter : Formatter := Formatter.visitAtom .anonymous

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

/-- The identifier that stands for the `i`th antiquotation in the text that
the parser reads. -/
def holeName (i : Nat) : String := s!"fren_hole_{i}"

/-- The antiquotation that an identifier of the text stands for, if it is
one (`holeName`). -/
def holeOf? (holes : Array Hole) (x : String) : Option Hole := do
  guard (x.startsWith "fren_hole_")
  let i ← (x.drop 10).toString.toNat?
  holes[i]?

/-- Whether `c` can be in the name of an antiquotation, `$x`. -/
def isHoleChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\''

/-- `stx`, read from a part of the file that starts at `base`, with its
positions in the file, so that Lean sees what it mentions as mentioned
there. -/
partial def shifted (base : String.Pos.Raw) (stx : Syntax) : Syntax :=
  let shift (p : String.Pos.Raw) : String.Pos.Raw := ⟨base.byteIdx + p.byteIdx⟩
  let info : SourceInfo → SourceInfo
    | .original l p t q => .original l (shift p) t (shift q)
    | .synthetic p q c => .synthetic (shift p) (shift q) c
    | .none => .none
  match stx with
  | .node i k args => .node (info i) k (args.map (shifted base))
  | .atom i v => .atom (info i) v
  | .ident i r n p => .ident (info i) r n p
  | .missing => .missing

/-- The text of a quotation with each antiquotation replaced by its
`holeName`, and the antiquotations, where the text starts at `base` in the
file. -/
def antiquotations (text : String) (base : String.Pos.Raw) : TermElabM (String × Array Hole) := do
  let cs := text.toList.toArray
  let mut out := ""
  let mut holes : Array Hole := #[]
  let mut i := 0
  while i < cs.size do
    let ch := cs[i]!
    if ch == '"' then
      -- A string literal, copied as it is.
      let mut j := i + 1
      while j < cs.size && cs[j]! != '"' do j := j + (if cs[j]! == '\\' then 2 else 1)
      out := out ++ String.ofList (cs.extract i (j + 1)).toList
      i := j + 1
    else if ch != '$' then
      out := out.push ch
      i := i + 1
    else
      -- Where the antiquotation's term starts in the file.
      let at_ (k : Nat) : String.Pos.Raw := ⟨base.byteIdx + (String.ofList (cs.extract 0 k).toList).utf8ByteSize⟩
      let (term, next) ← if cs[i + 1]? == some '(' then do
          let mut depth := 0
          let mut j := i + 1
          repeat
            if j ≥ cs.size then throwError "unterminated antiquotation `$(` in a Fren quotation"
            if cs[j]! == '(' then depth := depth + 1
            if cs[j]! == ')' then
              depth := depth - 1
              if depth == 0 then break
            j := j + 1
          let inner := String.ofList (cs.extract (i + 2) j).toList
          match Parser.runParserCategory (← getEnv) `term inner with
          | .ok stx => pure (⟨shifted (at_ (i + 2)) stx⟩, j + 1)
          | .error e => throwError "in the antiquotation `$({inner})`: {e}"
        else do
          let name := String.ofList ((cs.extract (i + 1) cs.size).toList.takeWhile isHoleChar)
          if name.isEmpty then throwError "expected a name or `(` after `$` in a Fren quotation"
          let info := SourceInfo.original "".toRawSubstring (at_ (i + 1)) "".toRawSubstring (at_ (i + 1 + name.length))
          pure (⟨Syntax.ident info name.toRawSubstring (.mkSimple name) []⟩, i + 1 + name.length)
      let splice := match cs[next]?, cs[next + 1]? with
        | some ',', some '*' => Splice.commas
        | some '|', some '*' => .bars
        | _, _ => .one
      holes := holes.push { term, splice }
      out := out ++ holeName (holes.size - 1)
      i := next + (if splice == .one then 0 else 2)
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
def core (n : Name) : Term := mkIdent n

/-- The text of `sp` in `src`. -/
def spanText (src : Array Char) (sp : Span) : String := String.ofList (src.extract sp.start sp.stop).toList

/-- `s`, a name or a literal of the quotation, which an antiquotation cannot
be part of. -/
def plain (s : String) : TermElabM String := do
  if (s.splitOn "fren_hole_").length > 1 then
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
    let pieces := rest.splitOn "fren_hole_"
    let some first := pieces.head? | break
    if pieces.length == 1 then
      parts := parts.push (quote first)
      break
    parts := parts.push (quote first)
    let after := (rest.drop (first.length + 10)).toString
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
  | .chain _ es ops => `($(core `Fren.Core.Tree.chain) $(← listOf holes src es) $(quote (ops.map (·.1)).toList))
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

@[term_elab frenExpr] def elabFrenExpr : TermElab := fun stx expected? => do
  let written := stx[1].getAtomVal
  let (text, holes) ← antiquotations written (stx[1].getPos?.getD 0)
  let (e, src) ← match parseExpr text with
    | .ok r => pure r
    | .error msg => throwErrorAt stx[1] "in the Fren quotation `{written.trimAscii}`: {msg}"
  let t ← withRef stx (treeOf holes src e)
  elabTerm (← `(($t : $(core `Fren.Core.Tree)))) expected?

end FrenCli.Quote
