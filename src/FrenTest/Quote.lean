-- keep-sorted start
import FrenCore.Lint
-- keep-sorted end

/-!
# Printing fixes

The printer of the trees that fixes write (`Fren.Core.Tree.print`) and the
quotations that build them (`fren_expr!`), against `lint::printing`
(`Reqs/Lint/Printing`): what it writes reads back, by the parser of the
`fren` command, as the tree, and each pair of parentheses that it adds is
needed. `roundTrips` checks this on random trees, as a job of `lake test`;
the `#guard`s here check examples.

-- fren-covers: lint::printing
-/

namespace FrenTest.Quote

open Fren.Core
open FrenCli (Expr)

/-! ## Examples -/

def orAB : BText := { text := "a or b", prec := (BKind.bin "or").prec }
def open_ : BText := { text := "x + if p? then 1 else 2", prec := (BKind.bin "+").prec }
def alts : Array String := #["E::A", "E::B"]
def elems : Array BText := #[{ text := "1", prec := BKind.atom.prec }, { text := "when p?, q?", prec := 0 }]

-- An operand that binds more loosely than its operator is in parentheses.
#guard (fren_expr!{ $orAB and not $orAB }).print.text == "(a or b) and not (a or b)"
-- The parentheses written in a quotation are not kept.
#guard (fren_expr!{ (a) and ((b)) }).print.text == "a and b"
-- A left-associative operator needs them on its right only.
#guard (fren_expr!{ a - (b - c) }).print.text == "a - (b - c)"
#guard (fren_expr!{ (a - b) - c }).print.text == "a - b - c"
-- A non-associative one on both sides.
#guard (fren_expr!{ (a = b) = c }).print.text == "(a = b) = c"
-- An open-ended operand needs them only where something follows it.
#guard (fren_expr!{ a and $open_ }).print == { text := "a and x + if p? then 1 else 2", prec := 3, endsOpen := true }
#guard (fren_expr!{ $open_ and a }).print.text == "(x + if p? then 1 else 2) and a"
#guard (fren_expr!{ a and $open_ }).inSlot (binSlot "or" false) == "(a and x + if p? then 1 else 2)"
-- Splices of expressions and of a pattern's alternatives.
#guard (fren_expr!{ if $orAB then f($elems,*) else [$elems,*] }).print.text ==
  "if a or b then f(1, (when p?, q?)) else [1, (when p?, q?)]"
#guard (fren_expr!{ $orAB is $alts|* }).print.text == "(a or b) is E::A | E::B"
#guard (fren_expr!{ not $orAB is $(alts[0]!) }).print.text == "not (a or b) is E::A"
-- A receiver, an index, a negation of a negation and a quantifier.
#guard (fren_expr!{ $orAB.len = $(Tree.atom "3") }).print.text == "(a or b).len = 3"
#guard (fren_expr!{ $orAB.starts_with?("a") }).print.text == "(a or b).starts_with?(\"a\")"
#guard (fren_expr!{ q[$orAB] }).print.text == "q[a or b]"
#guard (fren_expr!{ - $(Tree.neg (.atom "x")) }).print.text == "- -x"
-- The quotation is read as the `fren` command reads it: a quantifier as
-- an operand needs parentheses, and the printer writes them again.
#guard (fren_expr!{ a and (forall (k: Int), $orAB) }).print.text == "a and (forall (k: Int), a or b)"
-- A chained comparison's operands are each in a comparison's slot.
#guard (fren_expr!{ 0 <= $orAB < n }).print.text == "0 <= (a or b) < n"

/-! ## Quotations that do not build a tree -/

/-- error: in a Fren quotation, an antiquotation stands for an expression, list elements or a pattern, not for part of a name or a literal -/
#guard_msgs in
example : Tree := fren_expr!{ E::$orAB }

/-- error: in the Fren quotation `a and`: expected an expression, found end of file -/
#guard_msgs in
example : Tree := fren_expr!{ a and }

/-- error: `elems` stands for several expressions, which only a list can have -/
#guard_msgs in
example : Tree := fren_expr!{ $elems,* and b }

/--
error: a Fren quotation has no tree for `match a { _ => 1 }`: `Fren.Core.Tree` has only operators, conditionals, pattern tests, quantifiers, applications, field reads, indexes and set and sequence literals
-/
#guard_msgs in
example : Tree := fren_expr!{ match a { _ => 1 } }

/-! ## The fixes that build trees -/

-- `is_equality`: the scrutinee is the left operand of `=`.
#guard (isEqualityMsg orAB "E::A").fixes[0]!.replacement == "(a or b) = E::A"
-- `single_match_else`: an equation, a membership or a pattern test, in an `if`.
#guard
  let arm (alts : Array String) (body : String) : ArmInfo :=
    { alts, binds := false, noPayload := true, equatable := true, body := { text := body, prec := BKind.atom.prec } }
  singleMatchElseFix? #[arm #["E::A", "E::B"] "1", arm #[] "2"] orAB none false == some "if (a or b) in {E::A, E::B} then 1 else 2"
-- `match_bool`: in parentheses as a left operand.
#guard
  let arm (body : String) : ArmInfo := { alts := #[], binds := false, noPayload := false, body := { text := body, prec := 9 } }
  matchBoolFix? #[.bool true, .bool false] #[arm "1", arm "2"] "c?" (binSlot "+" false) false == some "(if c? then 1 else 2)"

/-! ## Random trees -/

/-- A pseudo-random state: a linear congruential generator. -/
abbrev R := StateM Nat

def next (n : Nat) : R Nat := modifyGet fun s =>
  let s := (s * 6364136223846793005 + 1442695040888963407) % 18446744073709551616
  ((s / 65536) % n, s)

def pick (xs : Array α) [Inhabited α] : R α := return xs[← next xs.size]!

def atoms : Array String := #["a", "b?", "x", "1", "true", "\"s\"", "E::A"]
def patterns : Array String := #["E::A", "E::A | E::B", "1..=3", "_", "\"s\""]
def ops : Array String := binaryOps

/-- A random tree of depth at most `d`. An expression as written is a
random tree, printed. -/
partial def tree (d : Nat) : R Tree := do
  if d == 0 then return .atom (← pick atoms)
  let sub := tree (d - 1)
  match ← next 18 with
  | 0 | 1 => return .atom (← pick atoms)
  | 2 => let t ← sub; return .ofText t.print.toBText
  | 3 | 4 | 5 => return .bin (← pick ops) (← sub) (← sub)
  | 6 => return .not (← sub)
  | 7 => return .neg (← sub)
  | 8 => return .when ((← next 2) == 0) (← sub) (← sub)
  | 9 => return .ite (← sub) (← sub) (← sub)
  | 10 => return .test (← sub) (← pick patterns)
  | 11 =>
    let ops ← if (← next 2) == 0 then pure #["<", "<="] else pure #[">", ">="]
    return .chain [← sub, ← sub, ← sub] [← pick ops, ← pick ops]
  | 12 => return .app "f" [← sub, ← sub]
  | 13 => return .method (← sub) "m" [← sub]
  | 14 => return .field (← sub) "len"
  | 15 => return .index (← sub) (← sub)
  | 16 => return (if (← next 2) == 0 then Tree.set else Tree.seq) [← sub, ← sub]
  | _ => return .quant ((← next 2) == 0) "(k: Int)" (← sub)

/-! ## Reading back -/

/-- The text of `sp` in `src`. -/
def spanText (src : Array Char) (sp : FrenCli.Span) : String := String.ofList (src.extract sp.start sp.stop).toList

/-- The shape of an expression that the parser read from `src`, without
its spans and parentheses: a name with dots is the field reads that it
means. -/
partial def exprShape (src : Array Char) (e : Expr) : String :=
  let go := exprShape src
  let all (es : Array Expr) := " ".intercalate (es.map go).toList
  match e with
  | .bin _ op a b => s!"({op} {go a} {go b})"
  | .not _ a => s!"(not {go a})"
  | .neg _ a => s!"(neg {go a})"
  | .when _ n c d => s!"({if n then "unless" else "when"} {go c} {go d})"
  | .ite _ c a b => s!"(if {go c} {go a} {go b})"
  | .is _ x p => s!"(is {go x} {spanText src p.span})"
  | .chain _ es ops => s!"(chain {(ops.map (·.1)).toList} {all es})"
  | .app _ fn args => s!"(app {"::".intercalate (fn.map (·.name)).toList} {all args})"
  | .method _ r m args => s!"(method {go r} {m.name} {all args})"
  | .field _ r f => s!"(field {go r} {f.name})"
  | .index _ q i => s!"(index {go q} {go i})"
  | .set _ es => s!"(set {all es})"
  | .seq _ es => s!"(seq {all es})"
  | .quant _ all bs body =>
    let binders := match bs[0]?, bs.back? with
      | some f, some l => spanText src { start := f.span.start, stop := l.span.stop }
      | _, _ => ""
    s!"({if all then "forall" else "exists"} {binders} {go body})"
  | .path _ #[x] => match x.name.splitOn "." with
    -- A name's components, which are field reads of a variable, but not of
    -- `true` or `false`, which no variable is.
    | first :: fields =>
      if first == "true" || first == "false" then s!"(path {x.name})"
      else fields.foldl (fun r f => s!"(field {r} {f})") first
    | [] => x.name
  | e => spanText src e.span

/-- The shape of what `text` reads as, if it reads as an expression. -/
def readShape (text : String) : Option String :=
  match FrenCli.Quote.parseExpr text with
  | .ok (e, src) => some (exprShape src e)
  | .error _ => none

/-- The shape of a tree, in the form of `exprShape`, with each expression
as written as what it reads as. -/
partial def treeShape (t : Tree) : String :=
  let go := treeShape
  let all (ts : List Tree) := " ".intercalate (ts.map go)
  match t with
  | .written b _ _ => (readShape b.text).getD s!"<unreadable {b.text}>"
  | .bin op a b => s!"({op} {go a} {go b})"
  | .not a => s!"(not {go a})"
  | .neg a => s!"(neg {go a})"
  | .when n c d => s!"({if n then "unless" else "when"} {go c} {go d})"
  | .ite c a b => s!"(if {go c} {go a} {go b})"
  | .test e p => s!"(is {go e} {p})"
  | .chain es ops => s!"(chain {ops} {all es})"
  | .app f args => s!"(app {f} {all args})"
  | .method r m args => s!"(method {go r} {m} {all args})"
  | .field r m => s!"(field {go r} {m})"
  | .index q i => s!"(index {go q} {go i})"
  | .set es => s!"(set {all es})"
  | .seq es => s!"(seq {all es})"
  | .quant all bs body => s!"({if all then "forall" else "exists"} {bs} {go body})"

/-- The pairs of parentheses of `cs`, outside string literals, as the
positions of each `(` and its `)`. -/
def parenPairs (cs : Array Char) : Array (Nat × Nat) := Id.run do
  let mut open_ : Array Nat := #[]
  let mut out := #[]
  let mut i := 0
  while i < cs.size do
    let c := cs[i]!
    if c == '"' then
      i := i + 1
      while i < cs.size && cs[i]! != '"' do i := i + (if cs[i]! == '\\' then 2 else 1)
    else if c == '(' then open_ := open_.push i
    else if c == ')' then
      if let some j := open_.back? then
        out := out.push (j, i)
        open_ := open_.pop
    i := i + 1
  return out

/-- Whether the pair of parentheses from `i` to `j` in `cs` is one that
[Parentheses in fixes] keeps where the grammar would not need it
(`lint::printing`): around an open-ended form in a part of an atom, after
`(`, `[`, `{` or `,`, or around a conditional. -/
partial def keptForReading (cs : Array Char) (i j : Nat) : Bool :=
  let inner := String.ofList (cs.extract (i + 1) j).toList
  let before := ((cs.extract 0 i).toList.reverse.dropWhile Char.isWhitespace).head?
  let delimited := before.any ("([{,".contains ·)
  (delimited && endsOpen inner) || inner.startsWith "if "
    -- The parentheses of a call around such a pair, which removing either
    -- pair leaves.
    || (i + 1 < j && cs[i + 1]! == '(' && cs[j - 1]! == ')' && (parenPairs (cs.extract (i + 1) j)).contains (0, j - i - 2)
      && keptForReading cs (i + 1) (j - 1))

/-- The failures of `lint::printing` on `t`: what it prints must read back
as `t`, and without any pair of parentheses that it adds, but those that
`keptForReading` allows, it must read otherwise, or not at all. Its
`endsOpen` must be what the text says (`Fren.Core.endsOpen`). -/
def printingFailures (t : Tree) : Array String := Id.run do
  let p := t.print
  let want := treeShape t
  let mut out := #[]
  if readShape p.text != some want then
    out := out.push s!"`{p.text}` reads as {readShape p.text}, not {want}"
  if p.endsOpen != endsOpen p.text then
    out := out.push s!"`{p.text}` ends open by the printer: {p.endsOpen}, but by its text: {endsOpen p.text}"
  let cs := p.text.toList.toArray
  for (i, j) in parenPairs cs do
    if keptForReading cs i j then continue
    let without := String.ofList ((cs.extract 0 i) ++ (cs.extract (i + 1) j) ++ (cs.extract (j + 1) cs.size)).toList
    if readShape without == some want then
      out := out.push s!"`{p.text}` does not need the parentheses at {i}: `{without}` reads the same"
  return out

/-- `lint::printing` on `n` random trees of depth at most 4, from `seed`. -/
def roundTrips (n : Nat) (seed : Nat := 392) : Array String := Id.run do
  let mut failures := #[]
  let mut s := seed
  for _ in [0:n] do
    let (t, s') := (tree 4).run s
    s := s'
    failures := failures ++ printingFailures t
  return failures

#guard (roundTrips 200).isEmpty

end FrenTest.Quote
