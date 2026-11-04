-- keep-sorted start
import FrenCore.Lint.Tree
import FrenCore.Ty
-- keep-sorted end

/-!
# Suspicious expressions and repeated constraints

Part of `FrenCore.Lint`, shared by both front ends.
-/

open Lean

namespace Fren.Core

/-! ## Suspicious expressions -/

/-- An infix operator (`lint::InfixOp`). -/
inductive InfixOp where
  | iff
  | or
  | and
  | eq
  | ne
  | lt
  | le
  | gt
  | ge
  | «in»
  | subset
  | add
  | sub
  | concat
  | union
  | minus
  | mul
  | inter
  | join
  deriving Inhabited, BEq, DecidableEq, Repr

def InfixOp.all : Array InfixOp :=
  #[.iff, .or, .and, .eq, .ne, .lt, .le, .gt, .ge, .in, .subset, .add, .sub, .concat, .union, .minus, .mul, .inter,
    .join]

def InfixOp.op : InfixOp → String
  | .iff => "iff"
  | .or => "or"
  | .and => "and"
  | .eq => "="
  | .ne => "!="
  | .lt => "<"
  | .le => "<="
  | .gt => ">"
  | .ge => ">="
  | .in => "in"
  | .subset => "subset"
  | .add => "+"
  | .sub => "-"
  | .concat => "++"
  | .union => "union"
  | .minus => "minus"
  | .mul => "*"
  | .inter => "inter"
  | .join => "join"

def InfixOp.ofOp? (op : String) : Option InfixOp := InfixOp.all.find? (·.op == op)

/-- What `a OP a` always is (`lint::EqOpValue`). -/
inductive EqOpValue where
  | alwaysTrue
  | alwaysFalse
  | zero
  | empty
  | operand
  deriving Inhabited, BEq, DecidableEq, Repr

/-- What `a OP b` is when `a` and `b` are written the same, if `eq_op`
fires (`lint::eq_op`). -/
def eqOp (op : InfixOp) (same : Bool) : Option EqOpValue :=
  if !same then none else match op with
  | .eq | .le | .ge | .iff | .subset => some .alwaysTrue
  | .ne | .lt | .gt => some .alwaysFalse
  | .sub => some .zero
  | .minus => some .empty
  | .and | .or | .union | .inter => some .operand
  | .add | .mul | .concat | .in | .join => none

/-- `a OP a`, where `a` is the text of the left operand. -/
def eqOpMsg (op : InfixOp) (v : EqOpValue) (a : String) : Msg :=
  let label := match v with
    | .alwaysTrue => "always `true`"
    | .alwaysFalse => "always `false`"
    | .zero => "always `0`"
    | .empty => "always `{}`"
    | .operand => s!"the same as `{a}`"
  { code? := some "F0736", headline := s!"both operands of `{op.op}` are written the same", label? := some label
    notes := #["note: one of them is probably not the operand meant"] }

/-- Whether `same_branches` fires on `if c then a else b`
(`lint::same_branches`), from whether the condition's pattern tests bind
names, which the `then` branch sees and the `else` branch does not
(`lang::test_scope`), and whether the branches are written the same. -/
def sameBranches (binds same : Bool) : Bool := !binds && same

/-- The last lexeme of the text whose characters, reversed, are `rev`, after
any whitespace, and the characters before it, reversed. -/
def lastLexeme (rev : List Char) : String × List Char :=
  let rev := rev.dropWhile Char.isWhitespace
  match rev with
  | [] => ("", [])
  | c :: rest =>
    if isWordChar c then
      let w := rev.takeWhile isWordChar
      (String.ofList w.reverse, rev.drop w.length)
    else match rest with
      | d :: rest' =>
        if ["!=", "<=", ">=", "++", "=>", ":="].contains (String.ofList [d, c]) then (String.ofList [d, c], rest')
        else (c.toString, rest)
      | [] => (c.toString, [])

/-- The keywords that an expression can follow. -/
def exprKeywords : List String :=
  -- keep-sorted start
  ["and", "div", "else", "if", "iff", "in", "inter", "join", "match", "minus", "mod", "not", "or", "subset", "then",
    "union", "unless", "when"]
  -- keep-sorted end

/-- Where an expression that is written after the text `before`, not in
parentheses, is an operand: of the operator that `before` ends with, on
its right, or of `when` or `unless`, on its left. An expression not in
parentheses is never a left operand otherwise, as it is a conditional,
whose `else` extends as far right as possible. -/
def slotAfter (before : String) : Option Slot :=
  let (lx, rest) := lastLexeme (withoutComments before).toList.reverse
  let right (k : BKind) : Option Slot := some ⟨k.prec, k.assoc, true⟩
  match lx with
  | "when" | "unless" => some ⟨0, .nonAssoc, false⟩
  | "not" => right .not
  | "-" =>
    -- Infix after an operand, prefix otherwise.
    let prev := (lastLexeme rest).1
    let afterOperand := [")", "]", "}", "\""].contains prev ||
      (prev.any isWordChar && !exprKeywords.contains prev)
    right (if afterOperand then .bin "-" else .neg)
  | op => if (InfixOp.ofOp? op).isSome || op == "div" || op == "mod" then right (.bin op) else none

/-- `if c then a else a`, where `branch` is the text of `a` and `prec` its
precedence, and `before` and `after` the texts before and after the
conditional. The fix is the
branch, in parentheses where `lang::operand` requires them. -/
def sameBranchesMsg (branch : String) (prec : Nat) (before after : String) : Msg :=
  let replacement := BText.inSlot { text := branch, prec } (slotAfter before) (startsWithOperator after)
  { code? := some "F0737", headline := "both branches of `if` are written the same"
    label? := some s!"`{branch}` whatever the condition"
    fixes := #[{ msg := "remove the condition, which decides nothing", replacement }] }

/-- The positions of the written forms `forms` that are the same as an
earlier one (`lint::duplicate_elements`). -/
def repeatedForms (forms : Array String) : Array Nat :=
  (Array.range forms.size).filter fun i => (forms.extract 0 i).contains forms[i]!

/-- The elements of a literal that are written the same as an earlier one,
by their positions (`lint::duplicate_elements`). -/
def repeatedElements (texts : Array String) : Array Nat :=
  repeatedForms (texts.map writtenForm)

/-- Whether `duplicate_elements` fires (`lint::duplicate_elements`). -/
def duplicateElements (nRepeats : Nat) : Bool := nRepeats > 0

/-- A set or relation literal, at `lit` in `src`, whose elements, at
`elems`, repeat at `repeats` (`repeatedElements`). The fix removes each
repeat, with the separator before it. -/
def duplicateElementsMsg (src : Array Char) (lit : Range) (elems : Array Range) (repeats : Array Nat) : Msg := Id.run do
  -- An element as written, with the parentheses around it.
  let widen (r : Range) : Range := Id.run do
    let mut r := r
    for _ in [0:src.size] do
      match parensAround? src lit r with
      | some r' => r := r'
      | none => break
    return r
  let elems := elems.map widen
  let mut text := ""
  let mut pos := lit.start
  for i in repeats do
    -- A repeat is never the first element.
    let r : Range := { start := elems[i - 1]!.stop, stop := elems[i]!.stop }
    text := text ++ textOf src { start := pos, stop := r.start }
    pos := r.stop
  text := text ++ textOf src { start := pos, stop := lit.stop }
  let names := repeats.map fun i => textOf src elems[i]!
  let headline := if names.size == 1 then s!"`{names[0]!}` is repeated in this literal" else
    s!"{", ".intercalate (names.toList.map (s!"`{·}`"))} are repeated in this literal"
  return { code? := some "F0738", headline, label? := some "a literal with repeats"
           notes := #["note: a set has no repeats: `{a, a}` is `{a}`"]
           fixes := #[{ msg := "remove the repeats", replacement := text }] }

/-- Whether `empty_argument` fires on argument `index` of `m`, from whether
it is empty: `""`, `[]`, or `0` (`lint::empty_argument`). -/
def emptyArgument (m : Method) (index : Nat) (empty : Bool) : Bool :=
  empty && match m with
  | .startsWith | .endsWith | .contains | .replace | .replaceAll | .indexOf => index == 0
  | .slice => index == 1
  | _ => false

/-- Whether `empty_argument` sees an argument, written `t`, as empty. -/
def emptyArgumentText (t : String) : Bool := ["\"\"", "[]", "0"].contains (writtenForm t)

/-- `recv.m(args)`, as their texts, of a sequence if `seq`, rather than a
string, if `empty_argument` fires on it. -/
def emptyArgumentMsg? (m : Method) (seq : Bool) (recv : String) (args : Array String) : Option Msg := do
  guard ((args.mapIdx fun i a => emptyArgument m i (emptyArgumentText a)).any id)
  let kind := if seq then "sequence" else "string"
  let empty := if seq then "[]" else "\"\""
  let (headline, label) ← match m with
    | .startsWith => some (s!"every {kind} starts with `{empty}`", "always `true`")
    | .endsWith => some (s!"every {kind} ends with `{empty}`", "always `true`")
    | .contains => some (s!"every {kind} contains `{empty}`", "always `true`")
    | .replace => some (s!"replacing `{empty}` puts the replacement before the {kind}", s!"this is `{args[1]!} ++ {recv}`")
    | .replaceAll => some (s!"replacing each `{empty}` leaves the {kind} as it is", s!"this is `{recv}`")
    | .indexOf =>
      some (s!"`{empty}` occurs at every position", s!"this is `{args[1]!}` if `0 <= {args[1]!} <= {recv}.len`, and `-1` otherwise")
    | .slice => some (s!"a slice of length 0 is empty", s!"always `{empty}`")
    | _ => none
  return { code? := some Lint.emptyArgument.code, headline, label? := some label
           notes := #["note: the argument is probably not the one meant"] }

/-- What `when c, d` is, or `unless c, d` if `negated`, when `c` and `d`
are written the same, if `eq_op` fires (`lint::eq_op_conditional`). -/
def eqOpConditional (negated same : Bool) : Option EqOpValue :=
  if !same then none else if negated then some .operand else some .alwaysTrue

/-- `when c, c`, or `unless c, c` if `negated`, where `c` is the text of
the condition. -/
def eqOpConditionalMsg (negated : Bool) (v : EqOpValue) (c : String) : Msg :=
  let label := match v with
    | .alwaysTrue => "always `true`"
    | _ => s!"the same as `{c}`"
  { code? := some Lint.eqOp.code
    headline := s!"the condition and the body of `{if negated then "unless" else "when"}` are written the same"
    label? := some label, notes := #["note: the body is probably not the one meant"] }

/-! ## Repeated constraints -/

/-- The kind of a constraint, a cover goal or a global expectation
(`lint::ConstraintKind`). -/
inductive ConstraintKind where
  | assume
  | ensure
  | expect
  | cover
  deriving Inhabited, BEq, DecidableEq, Repr

/-- The keyword of a constraint of this kind, in a global expectation's
block if `global` (`preconditionKeyword`). -/
def ConstraintKind.keyword (global : Bool := false) : ConstraintKind → String
  | .assume => preconditionKeyword global
  | .ensure => "ensure"
  | .expect => "expect"
  | .cover => "cover"

/-- Whether `duplicate_constraint` fires on a constraint, from whether it is
written the same as an earlier one, and whether its fix removes it, from
their kinds (`lint::duplicate_constraint`). -/
def duplicateConstraint (earlier later : ConstraintKind) (same : Bool) : Bool × Bool :=
  (same, same && earlier == later)

/-- For each constraint written the same as an earlier one, from their
texts in order, its position and that of the first such
(`lint::duplicate_constraint`). -/
def repeatedConstraints (texts : Array String) : Array (Nat × Nat) :=
  -- `writtenSame`, with each text's form computed once, if at all.
  let chars := texts.map (·.toList)
  let plain := chars.map (!mayHaveComments ·)
  let forms := texts.map fun t => Thunk.mk fun _ => writtenForm t
  let same (j i : Nat) : Bool :=
    if plain[j]! && plain[i]! && !sameNonWhitespace chars[j]! chars[i]! then false
    else forms[j]!.get == forms[i]!.get
  (Array.range texts.size).filterMap fun i => ((Array.range i).find? (same · i)).map (i, ·)

/-- A constraint of kind `later`, written the same as the earlier `name`, of
kind `earlier`. When the two are of one kind, the fix removes the later.
`global` if they are a global expectation's. -/
def duplicateConstraintMsg (earlier later : ConstraintKind) (name : String) (global : Bool := false) : Msg :=
  let aConstraint := if earlier == .assume then aPrecondition global else s!"an `{earlier.keyword global}`"
  let notes := if earlier == later then #["help: remove it"]
    else if later == .expect then
      #[s!"note: an `expect` that repeats {aConstraint} tests nothing",
        "help: the expectation was probably meant to say something stronger"]
    else #["note: one of them is probably not the constraint meant"]
  { code? := some Lint.duplicateConstraint.code, headline := s!"this is written the same as `{name}`"
    label? := some s!"the same as `{name}`", notes }

/-! ## Negative positions -/

/-- Whether `negative_position` fires on a position written as a negative
integer literal, if `negative`: the index of `q[i]` if `index`, or else
argument `arg` of `m`, from 0 (`lint::negative_position`). -/
def negativePosition (index : Bool) (m : Method) (arg : Nat) (negative : Bool) : Bool :=
  negative && (index || match m with
    | .at | .slice | .update => arg == 0
    | .indexOf => arg == 1
    | _ => false)

/-- The digits of `t`, if it is written as a negative integer literal, `-k`
for `k` other than `0`. -/
def negativeLiteral? (t : String) : Option String :=
  let f := writtenForm t
  let k := (f.drop 1).toString
  if f.startsWith "-" && !k.isEmpty && k.all Char.isDigit && k.any (· != '0') then some k else none

/-- `q[-k]`, as the texts of `q` and `k`. -/
def negativeIndexMsg (q k : String) : Msg :=
  { code? := some Lint.negativePosition.code, headline := "a negative index does not count from the end"
    label? := some "a negative index"
    notes := #["note: Fren has no negative indexing: `q[i]` is unspecified unless `0 <= i < q.len`",
      s!"help: to count from the end, write `{q}[{q}.len - {k}]`"] }

/-- `recv.m(args)`, as their texts, of a sequence if `seq`, rather than a
string, if `negative_position` fires on an argument. -/
def negativeArgumentMsg? (m : Method) (seq : Bool) (recv : String) (args : Array String) : Option Msg := do
  let i ← (Array.range args.size).find? fun i => negativePosition false m i (negativeLiteral? args[i]!).isSome
  let k ← negativeLiteral? args[i]!
  let empty := if seq then "[]" else "\"\""
  let label ← match m with
    | .at | .slice => some s!"always `{empty}`"
    | .update => some s!"always `{recv}`"
    | .indexOf => some "always `-1`"
    | _ => none
  let call (as : Array String) := s!"{recv}.{m.name}({", ".intercalate as.toList})"
  let help := if m == .indexOf then s!"help: to search from the start, write `{call (args.set! i "0")}`"
    else s!"help: to count from the end, write `{call (args.set! i s!"{recv}.len - {k}")}`"
  return { code? := some Lint.negativePosition.code, headline := "a negative position does not count from the end"
           label? := some label, notes := #["note: Fren has no negative indexing", help] }

end Fren.Core
