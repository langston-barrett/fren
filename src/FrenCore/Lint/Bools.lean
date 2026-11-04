-- keep-sorted start
import FrenCore.Lexical
import FrenCore.Lint.Imports
import FrenCore.Lint.Text
import FrenCore.Simplify
-- keep-sorted end

/-!
# Boolean rewrites and expression text

Part of `FrenCore.Lint`, shared by both front ends.
-/

open Lean

namespace Fren.Core

/-! ## Simpler `Bool` expressions -/

/-! The rules, and the proof that they keep the meaning, are in
`FrenCore.Simplify`; this builds the text of the simpler form. -/

/-- The associativity of an operator (`lang::Assoc`). -/
inductive Assoc where
  | left
  | right
  | nonAssoc
  deriving Inhabited, BEq, Repr

/-- Whether an operand can be written without parentheses
(`lang::operand`). -/
def bareOperand (outer inner : Nat) (assoc : Assoc) (right : Bool) : Bool :=
  if inner > outer then true
  else if inner < outer then false
  else match assoc with
    | .left => !right
    | .right => right
    | .nonAssoc => false

/-- The shape of an expression, as the lints that rewrite it see it
(`ExLint`), and the operator lints. A method call's operands are its
receiver and then its arguments; another atom's are the expressions in it,
such as a function's arguments, which no operator lint relates. A pattern
test, `e is P`, has its scrutinee as its operand, and binds as a
comparison. A chained comparison of the operators `ops` binds as a comparison,
and its operands are each in a comparison's operand slot, but the rules do
not look inside it. A quantifier binds as loosely as `when`, with its body
in the slot of a `when`'s body; the rules do not look inside it either. -/
inductive BKind where
  | lit (b : Bool)
  | not
  | bin (op : String)
  /-- `when`, or `unless` if `negated`. -/
  | when (negated : Bool)
  | ite
  | neg
  | method (name : String)
  | patternTest
  | chain (ops : Array String)
  /-- A `let`, which binds as loosely as `when`; only its body is looked
  inside. -/
  | «let»
  /-- `forall` or `exists`, whose operand is its body. -/
  | quant
  | atom
  deriving Inhabited, BEq, Repr

/-- The binary operators (`Reqs/Lang/Expressions#operators`). -/
def binaryOps : Array String :=
  #["iff", "or", "and", "=", "!=", "<", "<=", ">", ">=", "in", "subset", "+", "-", "++", "union", "minus", "*", "div",
    "mod", "inter", "join"]

/-- Whether the text of an expression ends in an *open-ended* form: a
conditional, a `when`, an `unless`, a `let` or a quantifier that is not in
parentheses, brackets or braces, whose last operand extends as far right
as possible (`Reqs/Lint#fixing-lints`). Such a form starts at the first of these
keywords outside them, and ends where the text does. -/
def endsOpen (t : String) : Bool := Id.run do
  let cs := (withoutComments t).toList.toArray
  let mut depth : Nat := 0
  let mut i := 0
  while i < cs.size do
    let c := cs[i]!
    if c == '"' then
      -- A raw literal is `r`, some `#`, then `"`, and has no escapes.
      let hashes := ((cs.extract 0 i).toList.reverse.takeWhile (· == '#')).length
      let raw := i ≥ hashes + 1 && cs[i - hashes - 1]! == 'r'
      let closes (k : Nat) : Bool :=
        cs[k]! == '"' && (!raw || (List.range hashes).all fun h => cs[k + 1 + h]? == some '#')
      i := i + 1
      while i < cs.size && !closes i do
        i := i + (if !raw && cs[i]! == '\\' then 2 else 1)
      i := i + 1 + (if raw then hashes else 0)
    else if isWordChar c then
      let w := String.ofList ((cs.extract i cs.size).toList.takeWhile isWordChar)
      if depth == 0 && ["if", "when", "unless", "let", "forall", "exists"].contains w then return true
      i := i + w.length
    else
      if "([{".contains c then depth := depth + 1
      else if ")]}".contains c then depth := depth - 1
      i := i + 1
  return false

/-- Whether `cs[start:stop]`, which follows an expression, starts with an
infix operator, after whitespace and comments, which would take the
expression as its left operand, or the `.` or `[` that take it as a
receiver. It reads only the first 7 characters after the whitespace and
comments, one more than the longest operator, `subset`: a word that fills
them is longer than any operator, and a shorter one ends within them. -/
def startsWithOperatorIn (cs : Array Char) (start stop : Nat) : Bool :=
  let cs := ((withoutCommentsIn cs start stop (some 7)).toList.dropWhile Char.isWhitespace)
  let lexeme := match cs with
    | c :: d :: _ =>
      if isWordChar c then String.ofList (cs.takeWhile isWordChar)
      else if ["!=", "<=", ">=", "++", "=>", ":="].contains (String.ofList [c, d]) then String.ofList [c, d]
      else c.toString
    | [c] => c.toString
    | [] => ""
  binaryOps.contains lexeme || lexeme == "." || lexeme == "["

/-- Whether the text `after`, which follows an expression, starts with an
infix operator (`startsWithOperatorIn`). -/
def startsWithOperator (after : String) : Bool :=
  let cs := after.toList.toArray
  startsWithOperatorIn cs 0 cs.size

/-- The precedence of an expression's outermost operator, as
`lang::operand` uses it. A conditional counts as binding most loosely,
since its `else` extends as far right as possible. -/
def BKind.prec : BKind → Nat
  | .when _ | .ite | .«let» | .quant => 0
  | .bin "iff" => 1
  | .bin "or" => 2
  | .bin "and" => 3
  | .not => 4
  | .bin "+" | .bin "-" | .bin "++" | .bin "union" | .bin "minus" => 6
  | .bin "*" | .bin "div" | .bin "mod" | .bin "inter" | .bin "join" => 7
  | .bin _ | .patternTest | .chain _ => 5
  | .neg => 8
  | .lit _ | .method _ | .atom => 9

def BKind.assoc : BKind → Assoc
  | .bin "or" | .bin "and" | .bin "+" | .bin "-" | .bin "++" | .bin "union" | .bin "minus" | .bin "*" | .bin "div"
  | .bin "mod" | .bin "inter" | .bin "join" => .left
  | .not | .neg | .when _ | .quant => .right
  | _ => .nonAssoc

/-- An expression: its shape, where it is written in the text given to
`simplerBools` (without parentheses around it), and its operands. -/
inductive BNode (α : Type) where
  | mk (kind : BKind) (range : Range) (ref : α) (kids : Array (BNode α))
  deriving Inhabited

/-- Where an operand is: the precedence and associativity of its
operator, and whether it is on the right; `none` where any expression can
be written, as for a branch of `if`. -/
structure Slot where
  outer : Nat
  assoc : Assoc
  right : Bool
  deriving Inhabited

def BKind.slots : BKind → Array (Option Slot)
  | .when _ => #[some ⟨0, .nonAssoc, false⟩, some ⟨0, .right, true⟩]
  | .quant => #[some ⟨0, .right, true⟩]
  | .ite => #[none, none, none]
  | .«let» => #[none]
  | .not => #[some ⟨4, .right, true⟩]
  | .neg => #[some ⟨8, .right, true⟩]
  | k@(.bin _) => #[some ⟨k.prec, k.assoc, false⟩, some ⟨k.prec, k.assoc, true⟩]
  -- Its scrutinee, the left operand of a comparison.
  | k@.patternTest => #[some ⟨k.prec, k.assoc, false⟩]
  -- Each operand after the first is on the right of a comparison.
  | k@(.chain ops) => #[some ⟨k.prec, k.assoc, false⟩] ++ Array.replicate ops.size (some ⟨k.prec, k.assoc, true⟩)
  | _ => #[]

/-- An expression, rewritten: its text and precedence. -/
structure BText where
  text : String
  prec : Nat
  /-- It has the outermost operator of the expression it replaces, so it
  needs parentheses only where that does. -/
  sameKind : Bool := false
  deriving Inhabited

/-- `t` in `slot`, in parentheses if it needs them there: where
`lang::operand` requires them, and where it ends in an open-ended form
(`endsOpen`) and something follows it, which it would take into its last
operand. Something follows a left operand, its operator, and anything
does where `followed`; a right operand is followed by what follows the
expression it is in, which the caller decides when it places that. -/
def BText.inSlot (t : BText) (slot : Option Slot) (followed : Bool := false) : String :=
  let followed := followed || slot.any (!·.right)
  let bare := slot.all (fun s => bareOperand s.outer t.prec s.assoc s.right) && !(followed && endsOpen t.text)
  if bare then t.text else s!"({t.text})"

/-- `t` where the expression it replaces is written, as `inSlot`, but
without parentheses where that expression is written without them and `t`
has its outermost operator: a conditional can be written as the right
operand of an operator, since nothing follows its last operand. -/
def BText.inPlace (t : BText) (slot : Option Slot) (followed : Bool := false) : String :=
  if t.sameKind then t.text else t.inSlot slot followed

/-- Whether `t`, which replaces an expression in `slot` that is written
in parentheses, can drop them (`Reqs/Lint#parentheses-in-fixes`): only in
the slot of an operator's operand, and only where `inSlot` writes `t`
without them. Elsewhere, as the scrutinee of a `match`, the condition of
a table's row or an argument of an application, the parentheses may be the
construct's own, or needed by what follows, as the `{` of a `match` follows
its scrutinee, so they are kept. -/
def BText.dropsParens (t : BText) (slot : Option Slot) (followed : Bool) : Bool :=
  slot.isSome && t.inSlot slot followed == t.text

/-- A report of a lint that rewrites an expression (`ExLint`): where, a
label, and the rewritten form. -/
structure BoolReport (α : Type) where
  ref : α
  range : Range
  label : String
  replacement : String
  deriving Inhabited

/-- `n` as an `Ex`, as deep as `Ex.simplerForm` looks: its operands and
theirs. Below that, and for what it does not look inside, an atom. -/
def BNode.toEx : Nat → BNode α → Ex
  | 0, _ => .atom 0
  | d + 1, .mk kind _ _ kids =>
    let k (i : Nat) := (kids[i]?.map (BNode.toEx d)).getD (.atom 0)
    match kind with
    | .lit b => .lit b
    | .not => .not (k 0)
    | .neg => .neg (k 0)
    | .bin op => match BinOp.ofOp? op with
      | some o => .bin o (k 0) (k 1)
      | none => .atom 0
    | .when n => .when n (k 0) (k 1)
    | .ite => .ite (k 0) (k 1) (k 2)
    | .method _ | .patternTest | .chain _ | .«let» | .quant | .atom => .atom 0

/-- The text of a rewritten form, from the rewritten texts of the operands
and of theirs, as `Shape.build` builds the expression. -/
def Shape.text (rs : Array (BText × Array BText)) : Shape → BText
  | .same (.kid i) => (rs[i]?.map (·.1)).getD default
  | .same (.grandkid i j) => ((rs[i]?.map (·.2)).getD #[])[j]?.getD default
  | .not a => { text := s!"not {(a.text rs).inSlot (BKind.not.slots[0]?.join)}", prec := BKind.not.prec }
  | .bin op a b =>
    let k := BKind.bin op.op
    { text := s!"{(a.text rs).inSlot (k.slots[0]?.join)} {op.op} {(b.text rs).inSlot (k.slots[1]?.join)}", prec := k.prec }
  | .when n c d =>
    let k := BKind.when n
    { text := s!"{if n then "unless" else "when"} {(c.text rs).inSlot (k.slots[0]?.join)}, {(d.text rs).inSlot (k.slots[1]?.join)}"
      prec := k.prec }
  | .ite c a b => { text := s!"if {(c.text rs).text} then {(a.text rs).text} else {(b.text rs).text}", prec := BKind.ite.prec }

/-- Whether a rewritten form has the outermost operator of `k`. -/
def Shape.sameKind (k : BKind) (s : Shape) : Bool :=
  match k, s with
  | .when n, .when n' .. => n == n'
  | .ite, .ite .. => true
  | _, _ => false

/-- `r` with the parentheses directly around it, if it is directly in
parentheses within `outer`. -/
def parensAround? (src : Array Char) (outer r : Range) : Option Range := Id.run do
  let mut i := r.start
  while i > outer.start && src[i - 1]!.isWhitespace do i := i - 1
  let mut j := r.stop
  while j < outer.stop && src[j]!.isWhitespace do j := j + 1
  return if i > outer.start && src[i - 1]! == '(' && j < outer.stop && src[j]! == ')' then
    some { start := i - 1, stop := j + 1 } else none

/-- Whether `r` is directly in parentheses within `outer`. -/
def enclosed (src : Array Char) (outer r : Range) : Bool := (parensAround? src outer r).isSome

def textOf (src : Array Char) (r : Range) : String := String.ofList (src.extract r.start r.stop).toList

/-- Whether an infix operator follows `r` in `src` (`startsWithOperator`). -/
def followedAt (src : Array Char) (r : Range) : Bool :=
  startsWithOperatorIn src r.stop src.size

/-- `src` up to the end of the expression at `root`, so that what follows
that expression, which is not an operand of it, is not seen as following
the expressions in it (`followedAt`). It is `src` itself, not a copy, if
`src` already ends there, so that a caller that cuts `src` once can pass it
to each lint. -/
def upTo (src : Array Char) (root : Range) : Array Char :=
  if src.size ≤ root.stop then src else src.extract 0 root.stop

/-- What `simplifyNode` gives for an expression: its text rewritten, and
its operands', each computed only if it is read, and whether the rewritten
text is known to be the text as written. Most expressions have nothing to
rewrite, and then no text is built, which would copy the text of each
operand once for each expression around it. -/
structure Simplified where
  text : Thunk BText
  kids : Array (Thunk BText)
  /-- If `true`, `text` is the expression's text as written. If `false`, it
  may still be, and a caller compares the texts. -/
  asWritten : Bool
  deriving Inhabited

/-- The text of `n` rewritten by the rules of `l`, where `n` is in `slot`
within `parent`, and of its operands, with the reports of `l` in it, in
order. -/
partial def simplifyNode (l : ExLint) (src : Array Char) (n : BNode α) (slot : Option Slot) (parent : Range) :
    StateM (Array (BoolReport α)) Simplified := do
  let .mk kind range ref kids := n
  let mut results := #[]
  for k in kids, s in kind.slots do
    results := results.push (← simplifyNode l src k s range)
  let kidRange (k : BNode α) : Range := match k with | .mk _ kr .. => kr
  -- Each operand's text in the node: as written if it is known to be, else
  -- its rewritten text, in parentheses if it needs them there; and whether
  -- one differs from the text as written.
  let mut texts : Array (Option String) := #[]
  let mut changed := false
  for k in kids, r in results, s in kind.slots do
    if r.asWritten then
      texts := texts.push none
    else
      let kr := kidRange k
      let t := r.text.get
      let written := textOf src kr
      let t' := if t.text == written || enclosed src range kr then t.text else t.inPlace s (followedAt src kr)
      if t' != written then changed := true
      texts := texts.push (some t')
  -- The node as written, with its operands' simplified texts.
  let own : Thunk BText := if !changed then Thunk.mk fun _ => { text := textOf src range, prec := kind.prec, sameKind := true }
    else Thunk.mk fun _ => Id.run do
      let mut text := ""
      let mut pos := range.start
      for k in kids, t? in texts do
        let kr := kidRange k
        text := text ++ textOf src { start := pos, stop := kr.start } ++ t?.getD (textOf src kr)
        pos := kr.stop
      return { text := text ++ textOf src { start := pos, stop := range.stop }, prec := kind.prec, sameKind := true }
  let kidTexts := results.map (·.text)
  -- Decided by the rules, from what `n` is as written, as `Ex.simp` does.
  match (n.toEx 3).simplerForm l with
  | some (label, s) =>
    let t := { s.text (results.map fun r => (r.text.get, r.kids.map (·.get))) with sameKind := s.sameKind kind }
    let replacement := if enclosed src parent range then t.text else t.inPlace slot (followedAt src range)
    modify (·.push { ref, range, label, replacement })
    return { text := Thunk.pure t, kids := kidTexts, asWritten := false }
  | none => return { text := own, kids := kidTexts, asWritten := !changed }

/-- The reports of `l` in an expression written in `src`, in the order
they start, the outer of two that start together first: for each, the
rewritten form, which replaces the expression's range. Each lint rewrites
by its own rules alone, so its fix makes no change that another lint
suggests. -/
def simplerBools (l : ExLint) (src : Array Char) (root : BNode α) : Array (BoolReport α) :=
  let range := match root with | .mk _ r .. => r
  let ((), out) := (do discard (simplifyNode l (upTo src range) root none range) : StateM _ Unit).run #[]
  out.qsort fun a b => a.range.start < b.range.start || (a.range.start == b.range.start && a.range.stop > b.range.stop)

def ExLint.lint : ExLint → Lint
  | .nonminimalBool => .nonminimalBool
  | .unlessNot => .unlessNot
  | .collapsibleWhen => .collapsibleWhen
  | .ifNotElse => .ifNotElse

/-- The message of a report of `l`. -/
def rewriteMsg (l : ExLint) (r : BoolReport α) (fixable : Bool := false) : Msg :=
  let (headline, notes) : String × Array String := match l with
    | .nonminimalBool => ("this `Bool` expression can be simpler", #[])
    | .unlessNot => ("this `unless` has a negated condition",
      #["note: `unless not A, D` is `when A, D`, and `unless a != b, D` is `when a = b, D`"])
    | .collapsibleWhen => ("this conditional can be collapsed into the one in its body",
      #["note: `when A, when B, D` is `when A and B, D`, and `unless A, unless B, D` is `unless A or B, D`"])
    | .ifNotElse => ("this `if` has a negated condition",
      #["note: `if not C then A else B` is `if C then B else A`, and `if a != b then A else B` is `if a = b then B else A`"])
  { code? := some l.lint.code, headline, label? := some r.label
    notes := notes ++ (if fixable then #[fixHelp] else #[])
    fixes := #[{ msg := s!"write `{r.replacement}`", replacement := r.replacement }] }

/-- The reports of the lints that rewrite expressions (`ExLint`) in an
expression written in `src`, each with its lint and message. -/
def rewriteReports (src : Array Char) (root : BNode α) (fixable : Bool := false) : Array (Lint × α × Msg) :=
  let src := upTo src (match root with | .mk _ r .. => r)
  ExLint.all.flatMap fun l => (simplerBools l src root).map fun r => (l.lint, r.ref, rewriteMsg l r fixable)

def BNode.kind : BNode α → BKind | .mk k .. => k
def BNode.range : BNode α → Range | .mk _ r .. => r
def BNode.ref : BNode α → α | .mk _ _ a _ => a
def BNode.kids : BNode α → Array (BNode α) | .mk _ _ _ ks => ks

end Fren.Core
