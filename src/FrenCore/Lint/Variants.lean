-- keep-sorted start
import FrenCore.Lint.Model
import FrenCore.Lint.Text
-- keep-sorted end

/-!
# Variant tests, record updates and tables

Part of `FrenCore.Lint`, shared by both front ends.
-/

open Lean

namespace Fren.Core

/-! ## Tests of variants -/

/-- A test of which variant a scrutinee is, as `if_chain_match` and
`case_split_guarantees` read it: `x = E::V`, `x in {E::V, E::W}`, or an `or` of
such tests of one scrutinee, where each variant has no payload. -/
structure VariantTest where
  /-- The scrutinee's text. -/
  scrutinee : String
  enum : Name
  /-- Each variant it names, in order: its index, and its text. -/
  variants : Array (Nat × String)
  deriving Inhabited

/-- The scrutinee's text without whitespace: two tests are of the same
scrutinee if it is the same. -/
def VariantTest.key (t : VariantTest) : String := writtenForm t.scrutinee

/-- `a or b`, if both test the same scrutinee. -/
def VariantTest.or (a b : VariantTest) : Option VariantTest :=
  if a.key == b.key && a.enum == b.enum then some { a with variants := a.variants ++ b.variants } else none

/-- The pattern that matches what the test accepts: its variants, as an
or-pattern if there are several. -/
def VariantTest.pattern (t : VariantTest) : String := " | ".intercalate (t.variants.map (·.2)).toList

/-- The tests, if each is a test of the same scrutinee as the first. -/
def sameScrutinee (ts : Array (Option VariantTest)) : Option (Array VariantTest) := do
  let ts ← ts.mapM id
  let t ← ts[0]?
  if ts.all fun u => u.key == t.key && u.enum == t.enum then some ts else none

/-- The variants that the tests name, in order, that an earlier one names. -/
def repeatedVariants (ts : Array VariantTest) : Nat :=
  let vs := ts.flatMap (·.variants.map (·.1))
  ((Array.range vs.size).filter fun i => (vs.extract 0 i).contains vs[i]!).size

/-- The variants of an enumeration of `n` that the tests do not name, if no
variant is named twice. -/
def untestedVariants (n : Nat) (ts : Array VariantTest) : Nat := n - (ts.flatMap (·.variants)).size

/-- `e` as the body of a `match` arm, where a top-level `when`, `unless` or
quantifier (`conditional`) is in parentheses. -/
def armBody (e : String) (conditional : Bool) : String := if conditional then s!"({e})" else e

/-- The scrutinee as written after `match`, where a `{` would start the
arms: in parentheses if it has one. -/
def scrutineeText (s : String) : String := if s.contains '{' then s!"({s})" else s

/-- Whether `if_chain_match` fires on a chain of `n` tests, and whether its
fix has a `_` arm (`lint::if_chain_match`). -/
def ifChainMatch (n : Nat) (variantTests : Bool) (nRepeated nUntested : Nat) : Bool × Bool :=
  (variantTests && n ≥ 2 && nRepeated == 0, nUntested > 0)

/-- `if T1 then a else if T2 then b ... else z`, as its tests, the texts of
the arms' bodies, and that of `z` if the fix keeps it. -/
def ifChainMatchMsg (tests : Array VariantTest) (bodies : Array String) (final? : Option String) : Msg :=
  let arms := (tests.zip bodies).map fun (t, b) => s!"{t.pattern} => {b}"
  let arms := arms ++ (final?.map (s!"_ => {·}")).toArray
  let x := (tests[0]?.map (·.scrutinee)).getD ""
  { code? := some "F0727", headline := s!"this chain of `if` tests which variant `{x}` is"
    label? := some "a chain of `if`"
    notes := if final?.isNone then #["note: the tests name every variant, so the final `else` is never taken"] else #[]
    fixes := #[{ msg := "write it as a `match`"
                 replacement := s!"match {scrutineeText x} \{ {", ".intercalate arms.toList} }" }] }

/-- Whether `case_split_guarantees` fires on `n` requirements `when T, y = e`, for
one output `y` and one scrutinee (`lint::case_split_guarantees`). -/
def caseSplitGuarantees (n nRepeated : Nat) : Bool := n ≥ 2 && nRepeated == 0

/-- The requirements `when T, y OP e` of one output `y` and scrutinee, as
their names, tests and the texts of `e`, of which `nUntested` variants are
not tested. -/
def caseSplitGuaranteesMsg (y op : String) (cases : Array (Name × VariantTest × String)) (nUntested : Nat) : Msg :=
  let x := (cases[0]?.map (·.2.1.scrutinee)).getD ""
  let arms := cases.map fun (_, t, e) => s!"{t.pattern} => {e}"
  let arms := if nUntested > 0 then arms.push s!"_ => {y}" else arms
  let names := (cases.map fun (n, _, _) => s!"`{n}`").toList
  let named := match names.reverse with
    | last :: rest@(_ :: _) => s!"{", ".intercalate rest.reverse} and {last}"
    | _ => ", ".intercalate names
  { code? := some "F0729", headline := s!"{named} constrain `{y}` case by case on which variant `{x}` is"
    label? := some "one of the cases"
    notes := #[s!"help: state them as one guarantee, `{y} {op} match {scrutineeText x} \{ {", ".intercalate arms.toList} }`"]
      ++ (if nUntested > 0 then
          #[s!"note: `_ => {y}` leaves `{y}` unconstrained where no guarantee tests the variant, as they do"]
        else #[])
      ++ #["note: `fren fix` does not merge guarantees, which traces, claims and `impl`s name"] }

/-- Whether `redundant_bindings` fires on the binding, or field, `name :=
value`, as the texts of both (`lint::redundant_bindings`). -/
def redundantBinding (name value : String) : Bool := name == value

def redundantBindingMsg (x : String) (field : Bool) : Msg :=
  { code? := some "F0735", headline := s!"`{x} := {x}` is `{x}`", label? := some s!"`{x}` alone means this"
    notes := #[s!"note: a {if field then "field" else "binding"} `{x}` alone means `{x} := {x}`"]
    fixes := #[{ msg := s!"write `{x}`", replacement := x }] }

/-- Whether the updated value `base`, as written, is a name or a dotted path
of names, through which `base.f` reads the field `f` (`lint::field_copy`). -/
def pathText (base : String) : Bool :=
  !base.isEmpty && base.all fun c => c.isAlphanum || c == '_' || c == '.' || c == ':'

/-- Whether `redundant_bindings` fires on the field `field := value` of an
update of `base`, as the texts of the three, where `others` says whether
the update gives some other field a value that is not a copy
(`lint::field_copy`). -/
def fieldCopy (field value base : String) (others : Bool) : Bool :=
  pathText base && value == base ++ "." ++ field && others

def fieldCopyMsg (x base : String) : Msg :=
  { code? := some "F0735", headline := s!"`{x} := {base}.{x}` gives `{x}` the value it has in `{base}`"
    label? := some "the update keeps it without this"
    notes := #[s!"note: an update reads from `{base}` every field it does not give", "help: remove the field"] }

/-- Whether `manual_record_update` fires on a record literal of `nFields`
fields, `nCopied` of which are copied from one value: more than it gives
new values, and not all (`lint::manual_record_update`). -/
def manualRecordUpdate (nFields nCopied : Nat) : Bool :=
  nCopied < nFields && nFields < 2 * nCopied

/-- `fields` are the texts of the fields the update gives, in the order
written. -/
def manualRecordUpdateMsg (base : String) (nCopied : Nat) (fields : Array String) : Msg :=
  let update := s!"\{ {base} with {", ".intercalate fields.toList} }"
  { code? := some "F0818"
    headline := s!"this record literal copies {nCopied} {if nCopied == 1 then "field" else "fields"} from `{base}`"
    label? := some s!"the same as `{update}`"
    notes := #["note: an update reads from its updated value every field it does not give, so it stays right when a field is added"]
    fixes := #[{ msg := s!"write `{update}`", replacement := update }] }

/-- Whether `needless_update` fires on an update that gives `nGiven` of a
record's `nFields` fields (`lint::needless_update`). -/
def needlessUpdate (nFields nGiven : Nat) : Bool := nGiven == nFields

def needlessUpdateMsg (record base : String) : Msg :=
  { code? := some "F0819", headline := s!"this update gives every field of `{record}`"
    label? := some s!"reads nothing from `{base}`"
    notes := #[s!"help: write a record literal, `{record} \{ ... }`, with the same fields"] }

/-- Why `trivial_cover` fires on a cover goal (`lint::trivial_cover`). -/
inductive TrivialCover where
  /-- It has a trigger. -/
  | trigger
  /-- It is written the same as an assumption or a guarantee. -/
  | restates (kind : String) (name : Name)
  deriving Inhabited, BEq, Repr

/-- Why `trivial_cover` fires, if it does, from whether the goal has a
trigger and the first assumption or guarantee written the same, as its
kind and name (`lint::trivial_cover`). -/
def trivialCover (trigger : Bool) (same? : Option (String × Name)) : Option TrivialCover :=
  if trigger then some .trigger else same?.map fun (k, n) => .restates k n

def trivialCoverMsg (goal : Name) : TrivialCover → Msg
  | .trigger =>
    { code? := some "F0820", headline := s!"cover goal `{goal}` has a trigger"
      label? := some "met by any behaviour in which the trigger is false"
      notes := #["help: write the scenario as a conjunction, such as `c? and d?` for `when c?, d?`"] }
  | .restates k n =>
    { code? := some "F0820", headline := s!"cover goal `{goal}` is written the same as the {k} `{n}`"
      label? := some "holds in every behaviour that meets the procedure"
      notes := #["note: it is met unless the procedure allows no behaviour, which the vacuity check reports"] }

/-! ## Tables -/

/-- Whether `manual_table` fires on a chain of `n` tests, from whether
they are variant tests of one scrutinee, for `if_chain_match`
(`lint::manual_table`). -/
def manualTable (n : Nat) (variantTests : Bool) : Bool := n ≥ 2 && !variantTests

/-- A row's condition or value as written in a table, where a top-level
`when`, `unless` or quantifier, or a `let` (`open`), is in parentheses. -/
def rowPart (e : String) (open_ : Bool) : String := if open_ then s!"({e})" else e

/-- `if T1 then a else if T2 then b ... else z`, as its tests, the texts
of its branches, and that of `z`, each as a table writes it (`rowPart`). -/
def manualTableMsg (tests bodies : Array String) (final : String) : Msg :=
  let rows := (tests.zip bodies).map fun (t, b) => s!"{t} => {b}"
  { code? := some Lint.manualTable.code, headline := "this chain of `if` chooses a value by conditions, as a table does"
    label? := some "a chain of `if`"
    notes := #[s!"help: write it as a table, `table \{ {", ".intercalate (rows.push s!"_ => {final}").toList} }`",
      "note: a table is checked for rows that may both hold, which the chain does not need, so `fren fix` does not rewrite it"] }

/-- Whether `same_branches` fires on a table of `n` rows, from whether its
values are all written the same and whether it has a `_` row, and whether
it has a fix (`lint::same_rows`). -/
def sameRows (n : Nat) (same wildcard : Bool) : Bool × Bool := (same && (n ≥ 2 || wildcard), wildcard)

/-- A table whose rows all have the value `value`, which is `fixed` in
place of the table (`BText.inSlot`), with a fix if it has a `_` row. -/
def sameRowsMsg (value fixed : String) (wildcard : Bool) : Msg :=
  { code? := some Lint.sameBranches.code, headline := "every row of this table has a value written the same"
    label? := some s!"`{value}` whatever the conditions"
    notes := if wildcard then #[]
      else #["note: the table has no `_` row, so where no row holds its value is unspecified, and `fren fix` keeps it"]
    fixes := if wildcard then #[{ msg := "remove the conditions, which decide nothing", replacement := fixed }] else #[] }

end Fren.Core
