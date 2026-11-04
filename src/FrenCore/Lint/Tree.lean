-- keep-sorted start
import FrenCore.Lint.Bools
-- keep-sorted end

/-!
# Printing lint fixes as expression trees

Part of `FrenCore.Lint`, shared by both front ends.
-/

open Lean

namespace Fren.Core

/-! ## Fixes as trees

A fix that rewrites an expression writes a `Tree`: operators applied to
operands, down to the expressions that it keeps as written. `fren_expr!`
(`FrenCli.Quote`) builds one from Fren's own syntax, and `Tree.print`
writes it with exactly the parentheses that the grammar needs
(`Reqs/Lint/Printing`), so that no fix decides them for itself. -/

/-- Where an operand that must be an atom is: the receiver of a field, a
method or an index, and a `match`'s scrutinee. -/
def receiverSlot : Slot := ⟨BKind.atom.prec, .left, false⟩

/-- The slot of a part of an atom other than a receiver: an argument of an
application or a method, a field of a record literal, an element of a
collection literal, an index, or a `match`'s scrutinee or arm's body.
These take any expression but an open-ended one, as a `when`'s condition
does (`Reqs/Lint#parentheses-in-fixes`). -/
def delimitedSlot : Slot := ⟨0, .nonAssoc, false⟩

/-- An expression that a fix writes (`lint::Tree`). -/
inductive Tree where
  /-- An expression as written, with its precedence, whether it ends in
  an open-ended form (`endsOpen`), and whether it can be a receiver
  without parentheses (`receivesText`): what the fix keeps of the
  expression it rewrites. `Tree.ofText` and `Tree.atom` give one. -/
  | written (t : BText) (endsOpen receivable : Bool)
  | bin (op : String) (a b : Tree)
  | not (a : Tree)
  | neg (a : Tree)
  /-- `when c, d`, or `unless c, d` if `negated`. -/
  | when (negated : Bool) (c d : Tree)
  | ite (c a b : Tree)
  /-- `e is P`, with the pattern as written. -/
  | test (e : Tree) (pattern : String)
  /-- `a < b <= c`: its operators, between its operands, of which there is
  one more. -/
  | chain (operands : List Tree) (ops : List String)
  /-- `f(a, b)`, an application of the path `f`. -/
  | app (fn : String) (args : List Tree)
  /-- `e.m(a, b)`. -/
  | method (recv : Tree) (name : String) (args : List Tree)
  /-- `e.x`, a field read, or a method call without arguments. -/
  | field (recv : Tree) (name : String)
  /-- `q[i]`. -/
  | index (q i : Tree)
  /-- `{a, b}`. -/
  | set (elems : List Tree)
  /-- `[a, b]`. -/
  | seq (elems : List Tree)
  /-- `forall (x: T), e`, or `exists` unless `all`, with its binders as
  written. -/
  | quant (all : Bool) (binders : String) (body : Tree)
  deriving Inhabited

/-- Whether `text`, an atom as written, can be followed without
parentheses by the `.` of a field read or a method call, if `dot`, or by
the `[` of an index: an integer, `true` and `false` cannot be; nor, before
`.`, a name that ends in `?`, which no identifier continues
(`Reqs/Lang/Lexical#identifiers`), or a path of more than one segment, as
`E::A` or `E::A'`, whose last segment would take in what follows the `.`
(`Reqs/Lang/Expressions`: `atom "." IDENT`). -/
def receivesText (text : String) (dot : Bool) : Bool :=
  let rev := text.toList.reverse
  let word := rev.takeWhile isWordChar
  let before := rev.drop word.length
  if text.isEmpty then false
  else if before.isEmpty && (text.front.isDigit || text == "true" || text == "false") then false
  else !(dot && !word.isEmpty && (word.head? == some '?' || before.take 2 == [':', ':']))

/-- An expression as written, with its precedence (`Tree.written`). -/
def Tree.ofText (t : BText) : Tree := .written t (endsOpen t.text) (receivesText t.text true)

/-- Text that is written as it is: a name, a literal, or an expression
that stays where it is written, with the parentheses it has there, which
the printer keeps. A negative literal, as `-1`, binds as a negation does. -/
def Tree.atom (text : String) : Tree :=
  let prec := if text.startsWith "-" then BKind.neg.prec else BKind.atom.prec
  .written { text, prec } false (receivesText text true)

/-- A `Tree`, written out: its text, its precedence, whether it ends in an
open-ended form outside parentheses, which would take in what follows it,
and whether it can be the receiver of a field read or a method call
without parentheses (`receivesText`). -/
structure Printed where
  text : String
  prec : Nat
  endsOpen : Bool
  receivable : Bool := true
  deriving Inhabited, BEq, Repr

/-- Whether `p` can be written without parentheses in `slot`, where
`followed` says that something follows it; a left operand is followed by
its operator (`Reqs/Lint#parentheses-in-fixes`). -/
def Printed.bare (p : Printed) (slot : Option Slot) (followed : Bool) : Bool :=
  slot.all (fun s => bareOperand s.outer p.prec s.assoc s.right) && !((followed || slot.any (!·.right)) && p.endsOpen)

/-- `p` in `slot`, in parentheses where it needs them (`Printed.bare`). -/
def Printed.inSlot (p : Printed) (slot : Option Slot) (followed : Bool := false) : String :=
  if p.bare slot followed then p.text else s!"({p.text})"

/-- Whether `p`, as the last operand of an expression, where it is in
`slot`, leaves that expression open-ended. -/
def Printed.leavesOpen (p : Printed) (slot : Option Slot) : Bool := p.bare slot false && p.endsOpen

/-- Whether `p` can be a receiver without parentheses, before the `.` of a
field read or a method call (`dot`), or the `[` of an index: where it can
be an operand there (`receiverSlot`), and is an atom that can take what
follows (`receivesText`). -/
def Printed.bareReceiver (p : Printed) (dot : Bool) : Bool :=
  p.bare (some receiverSlot) true && (if dot then p.receivable else p.receivable || receivesText p.text false)

/-- `p` as a receiver, before the `.` of a field read or a method call
(`dot`), or the `[` of an index: in parentheses where it needs them as an
operand (`receiverSlot`), and where it is an atom that cannot take what
follows (`receivesText`). -/
def Printed.asReceiver (p : Printed) (dot : Bool) : String :=
  if p.bareReceiver dot then p.text else s!"({p.text})"

/-- The text and precedence of `p`, as other fixes take them. -/
def Printed.toBText (p : Printed) : BText := { text := p.text, prec := p.prec }

/-- The slot of an operand of the binary operator `op`, on the `right`. -/
def binSlot (op : String) (right : Bool) : Option Slot :=
  let k := BKind.bin op
  some ⟨k.prec, k.assoc, right⟩

/-- `-` before `t`, with a space where `t` starts with `-`, which would
make `--`, a comment (`lint::negated`). -/
def negText (t : String) : String := if Fren.Str.startsWith t "-" then s!"- {t}" else s!"-{t}"

mutual
/-- `t` written out (`lint::print`): each operand in parentheses where it
needs them, in its operator's slot (`BKind.slots`), or for a part of an
atom, as a receiver (`receiverSlot`) or in a delimited slot
(`delimitedSlot`). -/
def Tree.print : Tree → Printed
  | .written t e r => { text := t.text, prec := t.prec, endsOpen := e, receivable := r }
  | .bin op a b =>
    let (pa, pb) := (a.print, b.print)
    { text := s!"{pa.inSlot (binSlot op false)} {op} {pb.inSlot (binSlot op true)}", prec := (BKind.bin op).prec
      endsOpen := pb.leavesOpen (binSlot op true) }
  | .not a =>
    let pa := a.print
    let s := BKind.not.slots[0]?.join
    { text := s!"not {pa.inSlot s}", prec := BKind.not.prec, endsOpen := pa.leavesOpen s }
  | .neg a =>
    let pa := a.print
    let s := BKind.neg.slots[0]?.join
    { text := negText (pa.inSlot s), prec := BKind.neg.prec, endsOpen := pa.leavesOpen s }
  | .when n c d =>
    let k := BKind.when n
    { text := s!"{if n then "unless" else "when"} {c.print.inSlot (k.slots[0]?.join)}, {d.print.inSlot (k.slots[1]?.join)}"
      prec := k.prec, endsOpen := true }
  | .ite c a b =>
    { text := s!"if {c.print.text} then {a.print.text} else {b.print.text}", prec := BKind.ite.prec, endsOpen := true }
  | .test e p =>
    { text := s!"{e.print.inSlot (BKind.patternTest.slots[0]?.join)} is {p}", prec := BKind.patternTest.prec
      endsOpen := false }
  | .chain es ops =>
    let k := BKind.chain ops.toArray
    let ps := Tree.printAll es
    let slot (i : Nat) : Option Slot := some ⟨k.prec, k.assoc, i > 0⟩
    let texts := ps.zipIdx.map fun (p, i) => p.inSlot (slot i) (i + 1 < ps.length)
    { text := (texts.head?.getD "") ++ String.join ((ops.zip texts.tail).map fun (op, t) => s!" {op} {t}"), prec := k.prec
      endsOpen := (ps.getLast?.map (·.leavesOpen (slot 1))).getD false }
  -- Without arguments, an application is written as its path, and a method
  -- call as a field read is.
  | .app f args =>
    { text := if args.isEmpty then f else s!"{f}({Tree.delimited args})", prec := BKind.atom.prec, endsOpen := false
      receivable := !args.isEmpty || receivesText f true }
  | .method r m args =>
    { text := s!"{r.print.asReceiver true}.{m}" ++ (if args.isEmpty then "" else s!"({Tree.delimited args})")
      prec := BKind.atom.prec, endsOpen := false, receivable := !args.isEmpty || !Fren.Str.endsWith m "?" }
  -- A name that ends in `?` takes no `.` after it.
  | .field r m =>
    { text := s!"{r.print.asReceiver true}.{m}", prec := BKind.atom.prec, endsOpen := false
      receivable := !Fren.Str.endsWith m "?" }
  | .index q i =>
    { text := s!"{q.print.asReceiver false}[{i.print.inSlot delimitedSlot}]", prec := BKind.atom.prec, endsOpen := false }
  | .set es => { text := s!"\{{Tree.delimited es}}", prec := BKind.atom.prec, endsOpen := false }
  | .seq es => { text := s!"[{Tree.delimited es}]", prec := BKind.atom.prec, endsOpen := false }
  | .quant all bs body =>
    { text := s!"{if all then "forall" else "exists"} {bs}, {body.print.inSlot (BKind.quant.slots[0]?.join)}"
      prec := BKind.quant.prec, endsOpen := true }

/-- Each of `ts` written out. -/
def Tree.printAll : List Tree → List Printed
  | [] => []
  | t :: ts => t.print :: Tree.printAll ts

/-- `ts`, separated by commas, each in a delimited slot. -/
def Tree.delimited : List Tree → String
  | [] => ""
  | [t] => t.print.inSlot delimitedSlot
  | t :: ts => s!"{t.print.inSlot delimitedSlot}, {Tree.delimited ts}"
end

/-- `t` written out in `slot`, in parentheses where it needs them there,
where `followed` says that something follows it. -/
def Tree.inSlot (t : Tree) (slot : Option Slot) (followed : Bool := false) : String := t.print.inSlot slot followed

/-- What an antiquotation of `fren_expr!` can be: an expression that a fix
writes. -/
class ToTree (α : Type) where
  toTree : α → Tree

instance : ToTree Tree := ⟨id⟩
instance : ToTree BText := ⟨Tree.ofText⟩

end Fren.Core
