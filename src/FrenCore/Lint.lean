-- keep-sorted start
import FrenCore.Names
import FrenCore.Regex
import FrenCore.Simplify
-- keep-sorted end

/-!
# Lints

Lints (`Reqs/Lint`) as pure functions, shared by both front ends: their
levels, how settings combine, the import and naming lints, unused
variables, dead code, simpler `Bool` expressions, and expectations. Each
front end records what happened while elaborating a file (`UseRecord`,
`UsedName`, `ExpectationRecord`) and calls `importReports` and
`expectationReports` at its end.
-/

open Lean

namespace Fren.Core

inductive LintLevel where
  | allow
  | expect
  | warn
  | deny
  | forbid
  deriving Inhabited, BEq, DecidableEq, Repr

def LintLevel.all : Array LintLevel := #[.allow, .expect, .warn, .deny, .forbid]

def LintLevel.name : LintLevel → String
  | .allow => "allow"
  | .expect => "expect"
  | .warn => "warn"
  | .deny => "deny"
  | .forbid => "forbid"

def LintLevel.ofName? (s : String) : Option LintLevel := LintLevel.all.find? (·.name == s)

/-- The severity of a lint's message (`lint::severity`); `none` if it is
not reported. -/
def LintLevel.severity? : LintLevel → Option Severity
  | .allow | .expect => none
  | .warn => some .warning
  | .deny | .forbid => some .error

inductive Lint where
  | unusedImports
  | globImports
  | nonSnakeCase
  | nonCamelCaseTypes
  | nonUpperCaseConstants
  | unfulfilledExpectations
  | unusedVariables
  | deadCode
  | nonminimalBool
  | undecidable
  | lengthZero
  | cardZero
  | singletonMembership
  | membershipChain
  | constantOutput
  | definableOutput
  | indexAfterUse
  | unlessNot
  | collapsibleWhen
  | ifNotElse
  | matchSameArms
  | matchLikeMembership
  | wildcardSingleVariant
  | ifChainMatch
  | caseSplitReqs
  | redundantBindings
  | eqOp
  | sameBranches
  | duplicateElements
  | emptyArgument
  | doubleComparison
  | boolEquality
  | manualMethod
  | elseExtends
  | identityOp
  | doubleParens
  | doubleNeg
  | intPlusOne
  | negMultiply
  | redundantMethodChain
  | trivialPattern
  | redundantBoolType
  | trivialMatch
  deriving Inhabited, BEq, DecidableEq, Repr

def Lint.all : Array Lint :=
  #[.unusedImports, .globImports, .nonSnakeCase, .nonCamelCaseTypes, .nonUpperCaseConstants, .unfulfilledExpectations,
    .unusedVariables, .deadCode, .nonminimalBool, .undecidable, .lengthZero, .cardZero,
    .singletonMembership, .membershipChain, .constantOutput, .definableOutput, .indexAfterUse, .unlessNot,
    .collapsibleWhen, .ifNotElse, .matchSameArms, .matchLikeMembership, .wildcardSingleVariant, .ifChainMatch,
    .caseSplitReqs, .redundantBindings, .eqOp, .sameBranches, .duplicateElements, .emptyArgument, .doubleComparison,
    .boolEquality, .manualMethod, .elseExtends, .identityOp, .doubleParens, .doubleNeg, .intPlusOne, .negMultiply,
    .redundantMethodChain, .trivialPattern, .redundantBoolType, .trivialMatch]

def Lint.name : Lint → String
  | .unusedImports => "unused_imports"
  | .globImports => "glob_imports"
  | .nonSnakeCase => "non_snake_case"
  | .nonCamelCaseTypes => "non_camel_case_types"
  | .nonUpperCaseConstants => "non_upper_case_constants"
  | .unfulfilledExpectations => "unfulfilled_lint_expectations"
  | .unusedVariables => "unused_variables"
  | .deadCode => "dead_code"
  | .nonminimalBool => "nonminimal_bool"
  | .undecidable => "undecidable"
  | .lengthZero => "length_zero"
  | .cardZero => "card_zero"
  | .singletonMembership => "singleton_membership"
  | .membershipChain => "membership_chain"
  | .constantOutput => "constant_output"
  | .definableOutput => "definable_output"
  | .indexAfterUse => "index_after_use"
  | .unlessNot => "unless_not"
  | .collapsibleWhen => "collapsible_when"
  | .ifNotElse => "if_not_else"
  | .matchSameArms => "match_same_arms"
  | .matchLikeMembership => "match_like_membership"
  | .wildcardSingleVariant => "wildcard_single_variant"
  | .ifChainMatch => "if_chain_match"
  | .caseSplitReqs => "case_split_reqs"
  | .redundantBindings => "redundant_bindings"
  | .eqOp => "eq_op"
  | .sameBranches => "same_branches"
  | .duplicateElements => "duplicate_elements"
  | .emptyArgument => "empty_argument"
  | .doubleComparison => "double_comparison"
  | .boolEquality => "bool_equality"
  | .manualMethod => "manual_method"
  | .elseExtends => "else_extends"
  | .identityOp => "identity_op"
  | .doubleParens => "double_parens"
  | .doubleNeg => "double_neg"
  | .intPlusOne => "int_plus_one"
  | .negMultiply => "neg_multiply"
  | .redundantMethodChain => "redundant_method_chain"
  | .trivialPattern => "trivial_pattern"
  | .redundantBoolType => "redundant_bool_type"
  | .trivialMatch => "trivial_match"

def Lint.code : Lint → String
  | .unusedImports => "F0701"
  | .globImports => "F0702"
  | .nonSnakeCase => "F0703"
  | .nonCamelCaseTypes => "F0704"
  | .nonUpperCaseConstants => "F0705"
  | .unfulfilledExpectations => "F0706"
  | .unusedVariables => "F0710"
  | .deadCode => "F0711"
  | .nonminimalBool => "F0712"
  -- `F0713` was `shadowed_constants`, which explicit shadowing replaced
  -- (`F0217`); it is not reused.
  | .undecidable => "F0714"
  | .lengthZero => "F0715"
  | .cardZero => "F0716"
  | .singletonMembership => "F0717"
  | .membershipChain => "F0718"
  | .constantOutput => "F0719"
  | .definableOutput => "F0720"
  | .indexAfterUse => "F0721"
  | .unlessNot => "F0722"
  | .collapsibleWhen => "F0723"
  | .ifNotElse => "F0724"
  | .matchSameArms => "F0725"
  | .matchLikeMembership => "F0726"
  | .wildcardSingleVariant => "F0728"
  | .ifChainMatch => "F0727"
  | .caseSplitReqs => "F0729"
  | .redundantBindings => "F0735"
  | .eqOp => "F0736"
  | .sameBranches => "F0737"
  | .duplicateElements => "F0738"
  | .emptyArgument => "F0745"
  | .doubleComparison => "F0730"
  | .boolEquality => "F0731"
  | .manualMethod => "F0732"
  | .elseExtends => "F0733"
  | .identityOp => "F0734"
  | .doubleParens => "F0739"
  | .doubleNeg => "F0740"
  | .intPlusOne => "F0741"
  | .negMultiply => "F0742"
  | .redundantMethodChain => "F0743"
  | .trivialPattern => "F0744"
  | .redundantBoolType => "F0746"
  | .trivialMatch => "F0747"

/-- A group of lints (`lint::Group`). Each lint is in exactly one, whose
level it takes by default. -/
inductive Group where
  | unused
  | nonstandardStyle
  | style
  | complexity
  | suspicious
  | pedantic
  | decidability
  deriving Inhabited, BEq, DecidableEq, Repr

def Group.all : Array Group := #[.unused, .nonstandardStyle, .style, .complexity, .suspicious, .pedantic, .decidability]

def Group.name : Group → String
  | .unused => "unused"
  | .nonstandardStyle => "nonstandard_style"
  | .style => "style"
  | .complexity => "complexity"
  | .suspicious => "suspicious"
  | .pedantic => "pedantic"
  | .decidability => "decidability"

/-- The level of a group's lints by default (`lint::group_default`).
`undecidable`, alone in `decidability`, is denied, so that a spec opts out
of decidability explicitly (`Reqs/Lang/Decidability`); `pedantic` lints are
allowed, since they would fire on much that reads well as it is. -/
def Group.default : Group → LintLevel
  | .pedantic => .allow
  | .decidability => .deny
  | _ => .warn

def Group.ofName? (s : String) : Option Group := Group.all.find? (·.name == s)

def Lint.group : Lint → Group
  | .unusedImports | .unusedVariables | .deadCode | .unfulfilledExpectations => .unused
  | .nonSnakeCase | .nonCamelCaseTypes | .nonUpperCaseConstants => .nonstandardStyle
  | .globImports | .lengthZero | .cardZero | .unlessNot | .collapsibleWhen | .matchLikeMembership | .redundantBindings
  | .doubleNeg | .negMultiply | .trivialPattern | .redundantBoolType => .style
  | .nonminimalBool | .singletonMembership | .constantOutput | .doubleComparison | .manualMethod | .elseExtends
  | .identityOp | .doubleParens | .intPlusOne | .redundantMethodChain | .trivialMatch => .complexity
  | .indexAfterUse | .eqOp | .sameBranches | .duplicateElements | .emptyArgument => .suspicious
  | .membershipChain | .definableOutput | .ifNotElse | .matchSameArms | .wildcardSingleVariant | .ifChainMatch
  | .caseSplitReqs | .boolEquality => .pedantic
  | .undecidable => .decidability

def Lint.default (l : Lint) : LintLevel := l.group.default

def Group.members (g : Group) : Array Lint := Lint.all.filter (·.group == g)

def Lint.ofName? (s : String) : Option Lint := Lint.all.find? (·.name == s)

/-- What a lint option names: a lint, or a group of lints. -/
inductive LintTarget where
  | lint (l : Lint)
  | group (g : Group)
  deriving Inhabited, BEq, DecidableEq, Repr

def LintTarget.name : LintTarget → String
  | .lint l => l.name
  | .group g => g.name

/-- The lints a setting of the target sets. -/
def LintTarget.members : LintTarget → Array Lint
  | .lint l => #[l]
  | .group g => g.members

def LintTarget.group? : LintTarget → Option Group
  | .lint _ => none
  | .group g => some g

/-- Lint and group names are distinct, so at most one matches. -/
def LintTarget.ofName? (s : String) : Option LintTarget :=
  match Lint.ofName? s with
  | some l => some (.lint l)
  | none => (Group.ofName? s).map .group

/-- The Lean option that sets the lint's level, `fren.lint.NAME`. -/
def Lint.option (l : Lint) : Name := `fren.lint ++ Name.mkSimple l.name

/-- `fren.lint.NAME` as written in `set_option`. -/
def Lint.optionString (l : Lint) : String := s!"fren.lint.{l.name}"

/-- The Lean option that sets the level of each lint of the group. -/
def Group.option (g : Group) : Name := `fren.lint ++ Name.mkSimple g.name

def LintTarget.option : LintTarget → Name
  | .lint l => l.option
  | .group g => g.option

/-- `fren.lint.NAME` as written in `set_option`. -/
def LintTarget.optionString (t : LintTarget) : String := s!"fren.lint.{t.name}"

/-- One setting of a lint's level (`lint::setting`): whether it is
accepted, and the level after it. -/
def setLevel (current requested : LintLevel) : Bool × LintLevel :=
  let ok := current != .forbid || requested == .forbid
  (ok, if ok then requested else current)

/-- Whether a setting of a group is accepted, from the number of its lints
at `forbid` before it (`lint::group_setting`). If so, it sets each of them. -/
def groupAccepted (nForbidden : Nat) (requested : LintLevel) : Bool :=
  nForbidden == 0 || requested == .forbid

/-- Whether a setting of `t` to `requested` is rejected, given the levels of
the lints before it (`lint::setting`, `lint::group_setting`): if so, a lint
whose `forbid` rejects it. -/
def LintTarget.rejectedBy? (t : LintTarget) (levelOf : Lint → LintLevel) (requested : LintLevel) : Option Lint :=
  match t with
  | .lint l => if (setLevel (levelOf l) requested).1 then none else some l
  | .group g =>
    let forbidden := g.members.filter (levelOf · == .forbid)
    if groupAccepted forbidden.size requested then none else forbidden[0]?

/-- The level of a lint from Lean options set outside the file, where there
is no order: the lint's own option wins over its group's
(`lint::outside_options`). -/
def outsideLevel (dflt : LintLevel) (own? group? : Option LintLevel) : LintLevel :=
  match own?, group? with
  | some l, _ => l
  | none, some g => g
  | none, none => dflt

/-- The level of a lint from its default, the command line and a setting
in the file (`lint::effective`), and whether that setting is an error. -/
def effectiveLevel (dflt : LintLevel) (cli? src? : Option LintLevel) : LintLevel × Bool :=
  let afterCli := match cli? with
    | some c => (setLevel dflt c).2
    | none => dflt
  match src? with
  | some s => let (ok, l) := setLevel afterCli s; (l, !ok)
  | none => (afterCli, false)

/-- The level of a lint at some place, and where it comes from. -/
structure LevelInEffect where
  level : LintLevel
  /-- Set by the command line or a `set_option`, rather than the default. -/
  isSet : Bool := false
  /-- Set by a setting of this group, rather than of the lint. -/
  group? : Option Group := none
  /-- At `expect`: the expectation, an index into the file's expectations.
  `expect` with no expectation, as from options outside a Lean file, means
  `allow`. -/
  expectation? : Option Nat := none
  deriving Inhabited, Repr

def LevelInEffect.ofDefault (l : Lint) : LevelInEffect := { level := l.default }

/-- The level that decides what happens: `expect` without an expectation
is `allow`. -/
def LevelInEffect.effective (l : LevelInEffect) : LintLevel :=
  if l.level == .expect && l.expectation?.isNone then .allow else l.level

/-- The levels of every lint at some place. -/
abbrev Levels := Array (Lint × LevelInEffect)

def Levels.defaults : Levels := Lint.all.map fun l => (l, .ofDefault l)

def Levels.get (ls : Levels) (l : Lint) : LevelInEffect :=
  ((ls.find? (·.1 == l)).map (·.2)).getD (.ofDefault l)

def Levels.set (ls : Levels) (l : Lint) (v : LevelInEffect) : Levels :=
  if ls.any (·.1 == l) then ls.map fun (l', v') => (l', if l' == l then v else v') else ls.push (l, v)

/-- The levels set by command-line flags, in order: the last flag for a
lint wins, except that `forbid` always wins. A flag for a group is a flag
for each of its lints, in its place. -/
def Levels.ofFlags (flags : Array (LintTarget × LintLevel)) : Levels :=
  flags.foldl (init := Levels.defaults) fun ls (t, v) =>
    t.members.foldl (init := ls) fun ls l =>
      ls.set l { level := (setLevel (ls.get l).level v).2, isSet := true, group? := t.group? }

/-! ## Collections, outputs and indexes -/

/-- `c` with its operands swapped: `a OP b` is `b OP' a`. -/
def Comparison.mirror : Comparison → Comparison
  | .lt => .gt
  | .gt => .lt
  | .le => .ge
  | .ge => .le
  | c => c

/-- Whether `length_zero` and `card_zero` fire on a comparison of a length
`n` with `bound`, `n OP bound` if `lengthLeft` and `bound OP n` otherwise,
and whether the fix says that it is empty (`lint::length_zero`). -/
def lengthZero (op : Comparison) (bound : Int) (lengthLeft : Bool) : Bool × Bool :=
  match if lengthLeft then op else op.mirror with
  | .eq | .le => (bound == 0, true)
  | .ne | .gt => (bound == 0, false)
  | .lt => (bound == 1, true)
  | .ge => (bound == 1, false)

/-- A comparison of a length with `bound`, where `recv` is the text of the
collection and `empty` that of an empty one, such as `""`, `[]` or `{}`. -/
def lengthZeroMsg (card : Bool) (recv empty : String) (isEmpty : Bool) (bound : Int) : Msg :=
  let m := if card then "card" else "len"
  let fixed := s!"{recv} {if isEmpty then "=" else "!="} {empty}"
  { code? := some (if card then "F0716" else "F0715"), headline := s!"say whether it is empty with `{empty}`, not `{m}`"
    label? := some s!"compares a length with {bound}"
    fixes := #[{ msg := s!"compare with `{empty}`", replacement := fixed }] }

/-- `x in {a}`, as the texts of `x` and `a`. -/
def singletonMembershipMsg (x a : String) : Msg :=
  { code? := some "F0717", headline := "membership in a set of one member is equality", label? := some "a set of one"
    fixes := #[{ msg := "write it as an equation", replacement := s!"{x} = {a}" }] }

/-- Whether `membership_chain` fires on a chain of `n` operands of `or`, or
of `and`, which all equate, or for `and` disequate, the same left operand if
`sameLeft`, where `laterIndexes` says that a right operand but the first
indexes a sequence (`lint::membership_chain`). -/
def membershipChainFires (n : Nat) (sameLeft laterIndexes : Bool) : Bool := sameLeft && n ≥ 3 && !laterIndexes

/-- `x = a or x = b or ...`, or `x != a and x != b and ...` if `negated`, as
the texts of `x` and the others. -/
def membershipChainMsg (x : String) (vals : Array String) (negated : Bool) : Msg :=
  let set := s!"\{{", ".intercalate vals.toList}}"
  { code? := some "F0718", headline := s!"this is `{x}` {if negated then "not " else ""}in a set of {vals.size}"
    label? := some s!"a chain of `{if negated then "and" else "or"}`"
    fixes := #[{ msg := "write it as a membership"
                 replacement := if negated then s!"not {x} in {set}" else s!"{x} in {set}" }] }

/-- Whether `constant_output` and `definable_output` fire on an output
(`lint::output_lints`). -/
def outputLints (defined mentions : Bool) (nReqs : Nat) (equation : Bool) : Bool × Bool :=
  (defined && !mentions, !defined && nReqs == 1 && equation)

def constantOutputMsg (x : Name) : Msg :=
  { code? := some "F0719", headline := s!"defined output `{x}` is the same in every behaviour"
    label? := some "mentions no variable"
    notes := #["help: make it a `const`, which is shared by every component"] }

def definableOutputMsg (x : Name) (req : Name) : Msg :=
  { code? := some "F0720", headline := s!"`{req}` could be the definition of `{x}`"
    label? := some "constrained by one equation"
    notes := #[s!"help: write the expression as `{x}`'s definition, `out {x} := ...`, and remove `{req}`"] }

/-- Whether `index_after_use` fires (`lint::index_after_use`). -/
def indexAfterUse (indexesLeft boundsRight : Bool) : Bool := indexesLeft && boundsRight

/-- `a and b`, as their texts, where `b` bounds what `a` indexes. -/
def indexAfterUseMsg (a b : String) : Msg :=
  { code? := some "F0721", headline := "the bound comes after the index it guards", label? := some "indexed before it is bounded"
    notes := #["note: in `a and b`, `b` is guarded by `a`, not the other way around, so the index may be out of range"]
    fixes := #[{ msg := "put the bound first, which does not change the meaning", replacement := s!"{b} and {a}" }] }

/-! ## Tests of variants -/

/-- A test of which variant a scrutinee is, as `if_chain_match` and
`case_split_reqs` read it: `x = E::V`, `x in {E::V, E::W}`, or an `or` of
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
def VariantTest.key (t : VariantTest) : String := String.ofList (t.scrutinee.toList.filter (!·.isWhitespace))

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

/-- `e` as the body of a `match` arm, where a top-level `when` or `unless`
(`conditional`) is in parentheses. -/
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

/-- Whether `case_split_reqs` fires on `n` requirements `when T, y = e`, for
one output `y` and one scrutinee (`lint::case_split_reqs`). -/
def caseSplitReqs (n nRepeated : Nat) : Bool := n ≥ 2 && nRepeated == 0

/-- The requirements `when T, y OP e` of one output `y` and scrutinee, as
their names, tests and the texts of `e`, of which `nUntested` variants are
not tested. -/
def caseSplitReqsMsg (y op : String) (cases : Array (Name × VariantTest × String)) (nUntested : Nat) : Msg :=
  let x := (cases[0]?.map (·.2.1.scrutinee)).getD ""
  let arms := cases.map fun (_, t, e) => s!"{t.pattern} => {e}"
  let arms := if nUntested > 0 then arms.push s!"_ => {y}" else arms
  let names := (cases.map fun (n, _, _) => s!"`{n}`").toList
  let named := match names.reverse with
    | last :: rest@(_ :: _) => s!"{", ".intercalate rest.reverse} and {last}"
    | _ => ", ".intercalate names
  { code? := some "F0729", headline := s!"{named} constrain `{y}` case by case on which variant `{x}` is"
    label? := some "one of the cases"
    notes := #[s!"help: state them as one requirement, `{y} {op} match {scrutineeText x} \{ {", ".intercalate arms.toList} }`"]
      ++ (if nUntested > 0 then
          #[s!"note: `_ => {y}` leaves `{y}` unconstrained where no requirement tests the variant, as they do"]
        else #[])
      ++ #["note: `fren fix` does not merge requirements, which traces, claims and `impl`s name"] }

/-- Whether `redundant_bindings` fires on the binding, or field, `name :=
value`, as the texts of both (`lint::redundant_bindings`). -/
def redundantBinding (name value : String) : Bool := name == value

def redundantBindingMsg (x : String) (field : Bool) : Msg :=
  { code? := some "F0735", headline := s!"`{x} := {x}` is `{x}`", label? := some s!"`{x}` alone means this"
    notes := #[s!"note: a {if field then "field" else "binding"} `{x}` alone means `{x} := {x}`"]
    fixes := #[{ msg := s!"write `{x}`", replacement := x }] }

/-! ## Settings -/

/-- The note listing the lints, sorted by name. -/
def lintsNote : String :=
  s!"note: the lints are {", ".intercalate (((Lint.all.map (·.name)).qsort (· < ·)).map (s!"`{·}`")).toList}"

/-- The note for a lint that Fren had but removed, if `n` is one. -/
def removedLintNotes (n : String) : Array String :=
  if n == "shadowed_constants" then
    #["note: `shadowed_constants` was removed; shadowing without `!` is now an error (F0217)"]
  else #[]

/-- The note listing the groups of lints, sorted by name. -/
def groupsNote : String :=
  s!"note: the groups of lints are {", ".intercalate (((Group.all.map (·.name)).qsort (· < ·)).map (s!"`{·}`")).toList}"

/-- The names of the lints and of the groups. -/
def lintTargetNames : Array String := Lint.all.map (·.name) ++ Group.all.map (·.name)

/-- The message of the fix that replaces an unknown name with `s`, the
name of a lint or a group. -/
def similarLintMsg (s : String) : String :=
  s!"a {if (Group.ofName? s).isSome then "group" else "lint"} with a similar name exists: `{s}`"

def unknownLintMsg (n : String) : Msg :=
  { code? := some "F0707", headline := s!"unknown lint `{n}`", label? := some "no such lint"
    notes := removedLintNotes n ++ #[lintsNote, groupsNote]
    fixes := (similarStr n lintTargetNames).toArray.map fun s =>
      { msg := similarLintMsg s, replacement := s!"fren.lint.{s}" } }

def invalidLevelMsg (v : String) : Msg :=
  { code? := some "F0708", headline := s!"invalid lint level `{v}`", label? := some "not a lint level"
    notes := #["note: a lint level is `\"allow\"`, `\"expect\"`, `\"warn\"`, `\"deny\"` or `\"forbid\"`"]
    fixes := (similarStr v (LintLevel.all.map (·.name))).toArray.map fun s =>
      { msg := s!"a level with a similar name exists: `\"{s}\"`", replacement := s!"\"{s}\"" } }

/-- A setting of `t` to `requested` where its lint `l` is forbidden. -/
def forbiddenMsg (t : LintTarget) (l : Lint) (requested : LintLevel) : Msg :=
  match t with
  | .lint _ =>
    { code? := some "F0709", headline := s!"`{requested.name}` for `{l.name}` is incompatible with an earlier `forbid`"
      label? := some s!"cannot change the level of `{l.name}`"
      notes := #["note: once a lint is `forbid`, its level cannot be changed"] }
  | .group g =>
    { code? := some "F0709"
      headline := s!"`{requested.name}` for `{g.name}` is incompatible with an earlier `forbid` of `{l.name}`"
      label? := some s!"cannot change the level of `{l.name}`, which is in `{g.name}`"
      notes := #["note: once a lint is `forbid`, its level cannot be changed, so neither can its group's"] }

/-! ## Messages -/

/-- The note on the first message of each lint in a file: where its level
comes from. -/
def levelNotes (l : Lint) (lv : LevelInEffect) : Array String :=
  if lv.isSet then
    match lv.group? with
    | some g => #[s!"note: `{l.name}` is set to `{lv.level.name}` by its group, `{g.name}`"]
    | none => #[s!"note: `{l.name}` is set to `{lv.level.name}`"]
  else #[s!"note: `{l.name}` is `{lv.level.name}` by default",
    s!"help: to allow it, `set_option {l.optionString} \"allow\"`"]

/-- A lint's message, at a place where its level is `lv`. -/
structure LintReport (α : Type) where
  lint : Lint
  level : LevelInEffect
  /-- Where to report it, as the front end knows it. -/
  ref : α
  msg : Msg
  deriving Inhabited

/-- The messages that are reported, with the level note on the first of
each lint, and the severity of each; and the expectations that the others
fulfil. -/
def finishReports (rs : Array (LintReport α)) : Array (LintReport α × Severity) × Array Nat := Id.run do
  let mut out := #[]
  let mut fulfilled := #[]
  let mut noted : Array Lint := #[]
  for r in rs do
    match r.level.effective with
    | .allow => pure ()
    | .expect => fulfilled := fulfilled.push r.level.expectation?.get!
    | lv =>
      let msg := if noted.contains r.lint then r.msg else
        { r.msg with notes := r.msg.notes ++ levelNotes r.lint r.level }
      noted := noted.push r.lint
      out := out.push ({ r with msg }, lv.severity?.get!)
  return (out, fulfilled)

/-! ## Imports -/

/-- A `use` declared in the file being elaborated. -/
structure UseRecord where
  /-- Its scope: the module, or the path of the component containing it. -/
  module : Name
  /-- The full path of the imported item; for a glob, of the opened enum. -/
  target : Name
  glob : Bool
  /-- The levels of `unused_imports` and `glob_imports` at the `use`. -/
  unusedLevel : LevelInEffect
  globLevel : LevelInEffect
  deriving Inhabited, Repr

/-- A path's first segment `name`, in `module`, resolved through an
import of `target` (`glob` if by `use target::*`). -/
structure UsedName where
  module : Name
  target : Name
  glob : Bool
  name : Name
  deriving Inhabited, BEq, Repr

/-- The import that the first segment of a path in the scope `from_`
resolves through (`modules::resolve`), if it resolves through one: a named
import, or the enum opened by `*`. The `module` of the result is the scope
of that import: a component's imports shadow its module's scope. -/
def Table.importVia (t : Table) (from_ : Name) (segs : Array Name) : Option UsedName := do
  let n ← segs[0]?
  let comp := t.isComp from_ && (t.uses.getD from_ #[]).any (·.brings t n)
  if n == `self || (!comp && (t.declared? (t.moduleOf from_) n).isSome) then none
  let uses := if comp then t.uses.getD from_ #[] else t.uses.getD (t.moduleOf from_) #[]
  if let some u := uses.find? (fun u => !u.glob && u.target.getString! == n.toString) then
    return { module := u.scope, target := u.target, glob := false, name := n }
  let enums := uses.foldl (init := #[]) fun (acc : Array (Name × Name)) u =>
    if u.glob && !acc.any (·.1 == u.target) && ((t.enums.get? u.target).any (·.variants.contains n)) then
      acc.push (u.target, u.scope)
    else acc
  match enums with
  | #[(e, scope)] => return { module := scope, target := e, glob := true, name := n }
  | _ => none

/-- The import that the declaration `n`, written with `!` if `bang`, hides
a name through, if any: the declaration depends on it, so it counts as
used, by `unused_imports` and by a glob that `glob_imports` narrows
(`Reqs/Lint#unused-imports`). A local of `locals` that it hides instead
hides the import too, so the import is not needed. -/
def Table.shadowedImport? (t : Table) (scope : Name) (locals : Array (Name × String)) (n : Name) (bang : Bool) :
    Option UsedName :=
  if bang && !locals.any (·.1 == n) && (t.hidden? scope #[] n).isSome then t.importVia scope #[n] else none

/-- Whether a `use` is unused (`lint::unused_import`). -/
def unusedImport (glob : Bool) (nPaths : Nat) (first : Bool) : Bool :=
  nPaths == 0 || (glob && !first)

/-- The line on the messages of lints that `fren fix` fixes. -/
def fixHelp : String := "help: `fren fix` can fix this"

def unusedImportMsg (target : Name) (glob : Bool) (fixable : Bool := false) : Msg :=
  { code? := some (Lint.unusedImports.code)
    headline := s!"unused import `{showPath target}{if glob then "::*" else ""}`", label? := some "unused"
    notes := #["help: remove this `use`"] ++ (if fixable then #[fixHelp] else #[]) }

/-- `used`, without repeats, sorted as `fren fmt` sorts a group. -/
def sortedNames (used : Array Name) : Array Name :=
  let names := used.foldl (init := #[]) fun acc n => if acc.contains n then acc else acc.push n
  names.qsort (·.toString < ·.toString)

def globImportMsg (enum : Name) (used : Array Name) (fixable : Bool := false) : Msg :=
  let used := sortedNames used
  let e := enum.getString!
  let named := match used.toList with
    | [v] => s!"`use {showPath enum}::{v}`"
    | vs => s!"`use {showPath enum}::\{{", ".intercalate (vs.map toString)}}`"
  let example_ := (used[0]?.map toString).getD "Variant"
  { code? := some (Lint.globImports.code)
    headline := s!"`use {showPath enum}::*` imports every variant of `{e}`", label? := some "glob import"
    notes := #["note: a name opened with `*` does not say where it comes from, and a variant added later can make a name ambiguous"]
      ++ (if used.isEmpty then #[] else #[s!"help: import the variants used here by name: {named}"])
      ++ #[s!"help: or write them qualified, as in `{e}::{example_}`"]
      ++ (if fixable && !used.isEmpty then #[fixHelp] else #[]) }

/-- The names that paths resolve through a `use`. -/
def UseRecord.hits (u : UseRecord) (used : Array UsedName) : Array UsedName :=
  used.filter fun x => x.module == u.module && x.target == u.target && x.glob == u.glob

/-- The names that paths resolve through the glob `u`, without repeats and
sorted. -/
def UseRecord.globNames (u : UseRecord) (used : Array UsedName) : Array Name :=
  sortedNames ((u.hits used).map (·.name))

/-- The import lints of a file, in the order of its `use`s, each at the
`ref` of its `use`. With `fixable`, the messages that `fren fix` would fix
say so. -/
def importReports (uses : Array (UseRecord × α)) (used : Array UsedName) (fixable : Bool := false) :
    Array (LintReport α) := Id.run do
  let mut out := #[]
  for (u, ref) in uses, i in [0:uses.size] do
    let first := !(uses.extract 0 i).any fun (u', _) => u'.module == u.module && u'.glob && u'.target == u.target
    let unused := unusedImport u.glob (u.hits used).size first
    if unused then
      out := out.push { lint := .unusedImports, level := u.unusedLevel, ref, msg := unusedImportMsg u.target u.glob fixable }
    if u.glob then
      -- An unused glob is removed rather than imported by name.
      let msg := globImportMsg u.target (u.globNames used) (fixable && !unused)
      out := out.push { lint := .globImports, level := u.globLevel, ref, msg }
  return out

/-! ## Fixes -/

/-- What `fren fix` does with a `use` (`lint::ImportFix`). -/
inductive ImportFix where
  | keep
  | remove
  | byName
  deriving Inhabited, BEq, DecidableEq, Repr

/-- The fix of a `use` that is not in a group, from the lints that fire at
it and whether each is fixed (`lint::import_fix`). -/
def importFix (unused glob fixUnused fixGlob : Bool) (nUsed : Nat) : ImportFix :=
  if unused && fixUnused then .remove
  else if glob && fixGlob && !unused && nUsed > 0 then .byName
  else .keep

/-- Whether `fren fix` fixes lint `l`, from the lints given to `--only` and
to `--skip` (`lint::fix_selected`). -/
def fixSelected (only skip : Array Lint) (l : Lint) : Bool :=
  (only.isEmpty || only.contains l) && !skip.contains l

/-- The exit status of `fren fix` (`lint::fix_exit`). -/
def fixExit (check loaded allFixed : Bool) : UInt32 :=
  if !loaded then 2 else if check && !allFixed then 1 else 0

/-- The range to delete to remove `r` from `src`: with the rest of its line
if nothing else is on it. -/
def deletionRange (src : Array Char) (r : Range) : Range := Id.run do
  let blank (c : Char) := c == ' ' || c == '\t'
  let mut a := r.start
  while a > 0 && blank src[a - 1]! do a := a - 1
  let mut b := r.stop
  while b < src.size && blank src[b]! do b := b + 1
  let lineStart := a == 0 || src[a - 1]! == '\n'
  let lineEnd := b == src.size || src[b]! == '\n'
  if lineStart && lineEnd then
    return { start := a, stop := min src.size (b + 1) }
  -- What follows, such as a comment, moves to the start of the line.
  if lineStart then return { start := a, stop := b }
  return r

/-- `src` with `edits` applied. Of overlapping edits, the one that starts
first, or the longer of two that start together, wins. -/
def applyEdits (src : Array Char) (edits : Array (Range × String)) : String := Id.run do
  let sorted := edits.qsort fun (r, _) (r', _) => r.start < r'.start || (r.start == r'.start && r.stop > r'.stop)
  let mut out := ""
  let mut pos := 0
  for (r, s) in sorted do
    if r.start < pos then continue
    out := out ++ String.ofList (src.extract pos r.start).toList ++ s
    pos := r.stop
  return out ++ String.ofList (src.extract pos src.size).toList

/-! ## Naming conventions -/

inductive Case where
  | snake
  | camel
  | upper
  deriving Inhabited, BEq, DecidableEq, Repr

/-- What a declared name names (`lint::Named`). -/
inductive Named where
  | module
  | component
  | variable
  /-- A field of a record. -/
  | field
  /-- A binder of a `match` pattern. -/
  | binder
  | function
  | instance
  | constraint
  | global
  | enumeration
  | variant
  | record
  | abstractType
  | constant
  deriving Inhabited, BEq, DecidableEq, Repr

def Named.describe : Named → String
  | .module => "module"
  | .component => "component"
  | .variable => "variable"
  | .field => "field"
  | .binder => "binder"
  | .function => "function"
  | .instance => "instance"
  | .constraint => "constraint"
  | .global => "global expectation"
  | .enumeration => "enum"
  | .variant => "variant"
  | .record => "record"
  | .abstractType => "abstract type"
  | .constant => "constant"

/-- The case of a name (`lint::naming_case`). -/
def Named.case : Named → Case
  | .enumeration | .variant | .record | .abstractType => .camel
  | .constant => .upper
  | _ => .snake

def Case.lint : Case → Lint
  | .snake => .nonSnakeCase
  | .camel => .nonCamelCaseTypes
  | .upper => .nonUpperCaseConstants

def Case.describe : Case → String
  | .snake => "a snake case"
  | .camel => "a camel case"
  | .upper => "an upper case"

/-- Whether a name is in a case, from its letters (`lint::in_case`). -/
def inCase (c : Case) (startsUpper hasUpper hasLower hasUnderscore : Bool) : Bool :=
  match c with
  | .snake => !hasUpper
  | .camel => startsUpper && !hasUnderscore
  | .upper => startsUpper && !hasLower

def isUpperAscii (c : Char) : Bool := 'A' ≤ c && c ≤ 'Z'
def isLowerAscii (c : Char) : Bool := 'a' ≤ c && c ≤ 'z'

/-- The name without a variable's final `?`. -/
def baseName (s : String) : String := (s.dropEndWhile (· == '?')).toString

/-- Whether `s` is in case `c` (`lint::in_case`). A variable's final `?`
is neither a letter nor `_`, so it changes nothing. -/
def nameInCase (s : String) (c : Case) : Bool :=
  let cs := s.toList
  inCase c (cs.head?.any isUpperAscii) (cs.any isUpperAscii) (cs.any isLowerAscii) (cs.contains '_')

/-- The words of a name: split at `_` and before an uppercase letter that
follows a lowercase letter or a digit. -/
def words (s : String) : List String := Id.run do
  let mut out : Array String := #[]
  let mut cur := ""
  let mut prev : Option Char := none
  for c in s.toList do
    if c == '_' then
      out := out.push cur; cur := ""
    else
      if isUpperAscii c && prev.any (fun p => isLowerAscii p || p.isDigit) then
        out := out.push cur; cur := ""
      cur := cur.push c
    prev := some c
  return (out.push cur).toList.filter (!·.isEmpty)

/-- `s` converted to case `c`, keeping a final `?`. -/
def toCase (c : Case) (s : String) : String :=
  let q := String.ofList (s.toList.reverse.takeWhile (· == '?'))
  let ws := words (baseName s)
  let base := match c with
    | .snake => "_".intercalate (ws.map String.toLower)
    | .upper => "_".intercalate (ws.map String.toUpper)
    | .camel => String.join (ws.map fun w => (w.toLower.capitalize))
  base ++ q

/-- The naming lint for a declared name, if it is not in its case. -/
def namingMsg? (what : Named) (n : Name) : Option (Lint × Msg) :=
  let s := n.toString
  let c := what.case
  if nameInCase s c then none else
  let fixed := toCase c s
  let fixes := if fixed.isEmpty || fixed == s || (fixed.front.isDigit) || !nameInCase fixed c then #[]
    else #[{ msg := s!"rename it to `{fixed}`", replacement := fixed : Fix }]
  some (c.lint, {
    code? := some c.lint.code, headline := s!"{what.describe} `{s}` should have {c.describe} name"
    label? := some s!"not in {match c with | .snake => "snake_case" | .camel => "CamelCase" | .upper => "UPPER_CASE"}"
    fixes })

/-! ## Unused variables -/

/-- The message of `unused_variables` for a variable of a component
(`binder` false) or a binder of a global expectation. -/
def unusedVariableMsg (n : Name) (binder : Bool) (output : Bool) : Msg :=
  { code? := some Lint.unusedVariables.code
    headline := s!"unused {if binder then "binder" else "variable"} `{n}`", label? := some "never mentioned"
    notes := (if binder then #[] else if output then #["note: nothing constrains it, so it can take any value"]
        else #["note: nothing in its component depends on it"])
      ++ #[s!"help: remove it, or mention it in {if binder then "the expectation" else "a constraint"}"] }

/-- A parameter of a defined function that its body never mentions. -/
def unusedParamMsg (n : Name) : Msg :=
  { code? := some Lint.unusedVariables.code
    headline := s!"unused parameter `{n}`", label? := some "never mentioned"
    notes := #["note: the function's value does not depend on it", "help: remove it, or mention it in the body"] }

/-- The variables, or binders, of `declared` that `mentioned` does not
contain, in order. -/
def unmentioned (declared : Array (Name × α)) (mentioned : Array Name) : Array (Name × α) :=
  declared.filter fun (n, _) => !mentioned.contains n

/-! ## Dead code -/

/-- Whether an item is dead (`lint::dead_item`). -/
def deadItem (what : Named) (isPub : Bool) (nUses : Nat) : Bool :=
  match what with
  | .enumeration | .record | .abstractType | .function | .constant => !isPub && nUses == 0
  | _ => false

/-- A private enumeration, record, abstract type, function or constant declared in
the file being elaborated, with the level of `dead_code` there. -/
structure ItemRecord where
  what : Named
  path : Name
  level : LevelInEffect
  deriving Inhabited, Repr

/-- The item that a resolved path uses: an enumeration for its variants. -/
def Resolved.usedItem : Resolved → Name
  | .item i => i.path
  | .variant e _ => e.path

def deadCodeMsg (what : Named) (n : Name) : Msg :=
  { code? := some Lint.deadCode.code, headline := s!"{what.describe} `{n.getString!}` is never used"
    label? := some "never used"
    notes := #["note: it is private, and nothing in this file uses it", "help: remove it, or make it `pub`"] }

/-- The `dead_code` messages of a file's items, given the items that paths
in it resolve to or through. -/
def deadCodeReports (items : Array (ItemRecord × α)) (used : Array Name) : Array (LintReport α) :=
  items.filterMap fun (i, ref) =>
    if deadItem i.what false (used.count i.path) then
      some { lint := .deadCode, level := i.level, ref, msg := deadCodeMsg i.what i.path }
    else none

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
such as a function's arguments, which no operator lint relates. -/
inductive BKind where
  | lit (b : Bool)
  | not
  | bin (op : String)
  /-- `when`, or `unless` if `negated`. -/
  | when (negated : Bool)
  | ite
  | neg
  | method (name : String)
  | atom
  deriving Inhabited, BEq, Repr

/-- The binary operators (`Reqs/Lang/Expressions#operators`). -/
def binaryOps : Array String :=
  #["iff", "or", "and", "=", "!=", "<", "<=", ">", ">=", "in", "subset", "+", "-", "++", "union", "minus", "*", "inter",
    "join"]

/-- The precedence of an expression's outermost operator, as
`lang::operand` uses it. A conditional counts as binding most loosely,
since its `else` extends as far right as possible. -/
def BKind.prec : BKind → Nat
  | .when _ | .ite => 0
  | .bin "iff" => 1
  | .bin "or" => 2
  | .bin "and" => 3
  | .not => 4
  | .bin "+" | .bin "-" | .bin "++" | .bin "union" | .bin "minus" => 6
  | .bin "*" | .bin "inter" | .bin "join" => 7
  | .bin _ => 5
  | .neg => 8
  | .lit _ | .method _ | .atom => 9

def BKind.assoc : BKind → Assoc
  | .bin "or" | .bin "and" | .bin "+" | .bin "-" | .bin "++" | .bin "union" | .bin "minus" | .bin "*" | .bin "inter"
  | .bin "join" => .left
  | .not | .neg | .when _ => .right
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
  | .ite => #[none, none, none]
  | .not => #[some ⟨4, .right, true⟩]
  | .neg => #[some ⟨8, .right, true⟩]
  | k@(.bin _) => #[some ⟨k.prec, k.assoc, false⟩, some ⟨k.prec, k.assoc, true⟩]
  | _ => #[]

/-- An expression, rewritten: its text and precedence. -/
structure BText where
  text : String
  prec : Nat
  /-- It has the outermost operator of the expression it replaces, so it
  needs parentheses only where that does. -/
  sameKind : Bool := false
  deriving Inhabited

/-- `t` in `slot`, in parentheses if it needs them there. -/
def BText.inSlot (t : BText) (slot : Option Slot) : String :=
  match slot with
  | some s => if bareOperand s.outer t.prec s.assoc s.right then t.text else s!"({t.text})"
  | none => t.text

/-- `t` where the expression it replaces is written, as `inSlot`, but
without parentheses where that expression is written without them and `t`
has its outermost operator: a conditional can be written as the right
operand of an operator, since nothing follows its last operand. -/
def BText.inPlace (t : BText) (slot : Option Slot) : String :=
  if t.sameKind then t.text else t.inSlot slot

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
    | .method _ | .atom => .atom 0

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

/-- The text of `n` rewritten by the rules of `l`, where `n` is in `slot`
within `parent`, and of its operands, with the reports of `l` in it, in
order. -/
partial def simplifyNode (l : ExLint) (src : Array Char) (n : BNode α) (slot : Option Slot) (parent : Range) :
    StateM (Array (BoolReport α)) (BText × Array BText) := do
  let .mk kind range ref kids := n
  let mut results := #[]
  for k in kids, s in kind.slots do
    results := results.push (← simplifyNode l src k s range)
  let kidRange (k : BNode α) : Range := match k with | .mk _ kr .. => kr
  -- The node as written, with its operands' simplified texts.
  let mut text := ""
  let mut pos := range.start
  let mut changed := false
  for k in kids, (t, _) in results, s in kind.slots do
    let kr := kidRange k
    let written := textOf src kr
    let t' := if t.text == written || enclosed src range kr then t.text else t.inPlace s
    if t' != written then changed := true
    text := text ++ textOf src { start := pos, stop := kr.start } ++ t'
    pos := kr.stop
  text := if changed then text ++ textOf src { start := pos, stop := range.stop } else textOf src range
  let own : BText := { text, prec := kind.prec, sameKind := true }
  let kidTexts := results.map (·.1)
  -- Decided by the rules, from what `n` is as written, as `Ex.simp` does.
  match (n.toEx 3).simplerForm l with
  | some (label, s) =>
    let t := { s.text results with sameKind := s.sameKind kind }
    let replacement := if enclosed src parent range then t.text else t.inPlace slot
    modify (·.push { ref, range, label, replacement })
    return (t, kidTexts)
  | none => return (own, kidTexts)

/-- The reports of `l` in an expression written in `src`, in the order
they start, the outer of two that start together first: for each, the
rewritten form, which replaces the expression's range. Each lint rewrites
by its own rules alone, so its fix makes no change that another lint
suggests. -/
def simplerBools (l : ExLint) (src : Array Char) (root : BNode α) : Array (BoolReport α) :=
  let range := match root with | .mk _ r .. => r
  let ((), out) := (do discard (simplifyNode l src root none range) : StateM _ Unit).run #[]
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
  ExLint.all.flatMap fun l => (simplerBools l src root).map fun r => (l.lint, r.ref, rewriteMsg l r fixable)

/-! ## Matches -/

/-- Where an operand that must be an atom is: the receiver of a field, a
method or an index, and a `match`'s scrutinee. -/
def receiverSlot : Slot := ⟨BKind.atom.prec, .left, false⟩

/-- `r` with the parentheses directly around it in `src`. -/
partial def withParens (src : Array Char) (r : Range) : Range :=
  if enclosed src { start := 0, stop := src.size } r then Id.run do
    let mut i := r.start
    while src[i - 1]!.isWhitespace do i := i - 1
    let mut j := r.stop
    while src[j]!.isWhitespace do j := j + 1
    return withParens src { start := i - 1, stop := j + 1 }
  else r

/-- `ts` as a list in prose: `` `a` ``, `` `a` and `b` ``, `` `a`, `b` and `c` ``. -/
def proseList (ts : Array String) : String :=
  let qs := ts.map (s!"`{·}`")
  match qs.back? with
  | none => ""
  | some last => if qs.size == 1 then last else s!"{", ".intercalate qs.pop.toList} and {last}"

/-- `s` with each run of whitespace outside string literals dropped, or
made one space between two characters of identifiers, so that two texts
are the same if their lexemes are. -/
def bodyKey (s : String) : String := Id.run do
  let word (c : Char) := c.isAlphanum || c == '_' || c == '?'
  let mut out := ""
  let mut inStr := false
  let mut escaped := false
  let mut gap := false
  for c in s.toList do
    if inStr then
      out := out.push c
      if escaped then escaped := false
      else if c == '\\' then escaped := true
      else if c == '"' then inStr := false
    else if c.isWhitespace then gap := true
    else
      if gap && word c && (out.back?.any word) then out := out.push ' '
      gap := false
      out := out.push c
      if c == '"' then inStr := true
  return out

/-- An arm of a `match`, as the match lints see it. -/
structure ArmInfo where
  /-- The texts of its pattern's alternatives, as written; none for `_`. -/
  alts : Array String
  /-- Its pattern binds a name. -/
  binds : Bool
  /-- Each alternative is a variant without a payload. -/
  noPayload : Bool
  /-- Its body, as written, with the parentheses around it. -/
  body : BText
  deriving Inhabited

def ArmInfo.wildcard (a : ArmInfo) : Bool := a.alts.isEmpty

/-- The pattern as written, with ` | ` between alternatives. -/
def ArmInfo.pattern (a : ArmInfo) : String := if a.wildcard then "_" else " | ".intercalate a.alts.toList

/-- Whether `match_same_arms` fires on two arms (`lint::match_same_arms`). -/
def sameArmsFires (sameBody binds : Bool) : Bool := sameBody && !binds

/-- The fix of `match_same_arms` for a group of arms (`lint::ArmsFix`). -/
inductive ArmsFix where
  | merge
  | remove
  | replace
  deriving Inhabited, BEq, DecidableEq, Repr

/-- The fix for a group of arms with the same body, from whether it is
every arm of the `match` and whether one of them is `_`
(`lint::match_same_arms`). -/
def sameArmsFix (all wildcard : Bool) : ArmsFix :=
  if all then .replace else if wildcard then .remove else .merge

/-- The groups of arms that `match_same_arms` fires on, in order, each in
order: the arms that bind no names, by their bodies, where two or more have
one. -/
def sameArmGroups (arms : Array ArmInfo) : Array (Array Nat) := Id.run do
  let mut groups : Array (Array Nat) := #[]
  for a in arms, i in [0:arms.size] do
    let fires (g : Array Nat) :=
      let b := arms[g[0]!]!
      sameArmsFires (bodyKey b.body.text == bodyKey a.body.text) (b.binds || a.binds)
    match groups.findIdx? fires with
    | some j => groups := groups.modify j (·.push i)
    | none => if !a.binds then groups := groups.push #[i]
  return groups.filter (·.size ≥ 2)

/-- The fix of a group of `sameArmGroups`. -/
def groupFix (arms : Array ArmInfo) (g : Array Nat) : ArmsFix :=
  sameArmsFix (g.size == arms.size) (g.any (arms[·]!.wildcard))

/-- The arms of a group that its fix removes: all but `_`, or the first. -/
def groupRemoved (arms : Array ArmInfo) (g : Array Nat) : Array Nat :=
  if groupFix arms g == .remove then g.filter (!arms[·]!.wildcard) else g.extract 1 g.size

/-- The message of `match_same_arms` for a group, and the arm it is
reported at, the first that the fix removes. `slot` is where the `match`
is, for the body that replaces it. -/
def sameArmsMsg (arms : Array ArmInfo) (g : Array Nat) (slot : Option Slot) : Nat × Msg :=
  let fix := groupFix arms g
  let removed := groupRemoved arms g
  let first := arms[g[0]!]!
  let body := first.body.text
  let headline := if fix == .remove then "this arm has the same body as the `_` arm"
    else s!"this arm has the same body as the arm `{first.pattern}`"
  let others := (removed.extract 1 removed.size).map (arms[·]!.pattern)
  let so := if others.isEmpty then #[]
    else #[s!"note: so {if others.size == 1 then "does the arm" else "do the arms"} {proseList others}"]
  let help := match fix with
    | .merge => s!"help: merge them into one arm, `{" | ".intercalate (g.flatMap (arms[·]!.alts)).toList} => {body}`"
    | .remove => s!"help: remove {if removed.size == 1 then "it" else "them"}, so that `_` covers {if removed.size == 1 then "its" else "their"} variants too"
    | .replace => s!"help: replace the `match` with its body, `{first.body.inSlot slot}`"
  let notes := so ++ (if fix == .replace then #["note: every arm of the `match` has this body"] else #[]) ++ #[help]
  (removed[0]!, { code? := some Lint.matchSameArms.code, headline, label? := some "the same body", notes })

/-- The edits that fix `match_same_arms` in a `match` written at `range`,
where `slot` is, given each arm's range, its pattern's and its body's,
with the parentheses around it. An arm that the fixes remove is removed
with the `,` between it and a kept arm. -/
def sameArmsEdits (range : Range) (arms : Array ArmInfo) (armRanges patRanges bodyRanges : Array Range)
    (slot : Option Slot) : Array (Range × String) := Id.run do
  let groups := sameArmGroups arms
  if let some g := groups.find? (groupFix arms · == .replace) then
    -- The body of the first arm, without what is around it.
    let b := arms[g[0]!]!.body
    let bare := match slot with | some s => bareOperand s.outer b.prec s.assoc s.right | none => true
    let r := bodyRanges[g[0]!]!
    return #[({ start := range.start, stop := r.start }, if bare then "" else "("),
             ({ start := r.stop, stop := range.stop }, if bare then "" else ")")]
  let mut edits := #[]
  for g in groups do
    if groupFix arms g == .merge then
      edits := edits.push (patRanges[g[0]!]!, " | ".intercalate (g.flatMap (arms[·]!.alts)).toList)
  let removed := groups.flatMap (groupRemoved arms)
  let mut i := 0
  while i < arms.size do
    if !removed.contains i then i := i + 1; continue
    let mut j := i
    while j + 1 < arms.size && removed.contains (j + 1) do j := j + 1
    edits := edits.push <| if j + 1 < arms.size then ({ start := armRanges[i]!.start, stop := armRanges[j + 1]!.start }, "")
      else ({ start := armRanges[i - 1]!.stop, stop := armRanges[j]!.stop }, "")
    i := j + 1
  return edits

/-- Whether `match_like_membership` fires, and whether its fix is a
negated membership, of the variants whose arms are `false`
(`lint::match_like_membership`). -/
def matchMembership (boolBodies noPayloads wildcard wildcardTrue : Bool) (nTrue nFalse : Nat) : Bool × Bool :=
  (boolBodies && noPayloads, if wildcard then wildcardTrue else nTrue > nFalse)

/-- The fix of `match_like_membership`, if it fires, as the texts before
and after the scrutinee, which is `scrutinee` as written, with the
parentheses around it; `slot` is where the `match` is. -/
def membershipParts? (arms : Array ArmInfo) (scrutinee : BText) (slot : Option Slot) : Option (String × String) := do
  let lit (b : Bool) (a : ArmInfo) := a.body.text == toString b
  let boolBodies := arms.all (fun a => lit true a || lit false a) && arms.any (lit true) && arms.any (lit false)
  let wild? := arms.find? (·.wildcard)
  let named (b : Bool) := (arms.filter fun a => !a.wildcard && lit b a).flatMap (·.alts)
  let (fires, negated) := matchMembership boolBodies (arms.all (·.noPayload)) wild?.isSome (wild?.any (lit true))
    (named true).size (named false).size
  guard fires
  let vs := named !negated
  let (op, prec) := if vs.size == 1 then (s!" {if negated then "!=" else "="} {vs[0]!}", 5)
    else (s!" in \{{", ".intercalate vs.toList}}", if negated then 4 else 5)
  let bareScrutinee := bareOperand 5 scrutinee.prec .nonAssoc false
  let pre := (if negated && vs.size > 1 then "not " else "") ++ (if bareScrutinee then "" else "(")
  let post := (if bareScrutinee then "" else ")") ++ op
  let bare := match slot with | some s => bareOperand s.outer prec s.assoc s.right | none => true
  return if bare then (pre, post) else ("(" ++ pre, post ++ ")")

def membershipMsg (replacement : String) : Msg :=
  { code? := some Lint.matchLikeMembership.code, headline := "this `match` only tests which variant its scrutinee is"
    label? := some "each arm is `true` or `false`"
    fixes := #[{ msg := "write it as a comparison", replacement }] }

/-- Whether `wildcard_single_variant` fires on a `_` arm, from the number
of variants it covers (`lint::wildcard_single_variant`). -/
def wildcardSingle (nCovered : Nat) : Bool := nCovered == 1

/-- How a pattern in module `from_` names the variant `v` of the
enumeration `enum`, with `extra` shadowing, if one of these resolves to
it: a path that another pattern of the `match` writes, `siblings`, with
its last segment replaced; `V`; or `E::V`. -/
def Table.variantPath? (t : Table) (from_ : Name) (extra : Array Name) (enum v : Name) (siblings : Array (Array Name)) :
    Option (Array Name) :=
  let candidates := siblings.filterMap (fun s => if s.size ≥ 2 then some (s.pop.push v) else none)
    ++ #[#[v], #[Name.mkSimple enum.getString!, v]]
  candidates.find? fun segs => match t.resolvePath from_ segs extra with
    | .ok (.variant en idx) => en.path == enum && en.variants[idx]? == some v
    | _ => false

/-- A `_` arm that covers only the variant `v`, with the pattern that names
it, if one resolves. -/
def wildcardMsg (v : Name) (pattern? : Option String) : Msg :=
  { code? := some Lint.wildcardSingleVariant.code, headline := s!"`_` matches only `{showPath v}`"
    label? := some "matches one variant"
    notes := #[s!"note: named, a variant added later makes the `match` non-exhaustive, an error, rather than matched by `_`"]
    fixes := pattern?.toArray.map fun p => { msg := "name the variant", replacement := p } }

/-! ## Suspicious expressions -/

def isWordChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '?'

/-- The text `s` as the suspicious lints compare it, so that two texts are
*written the same* if these agree: without whitespace, but for one space
between two characters of names, numbers or keywords, and with string
literals as they are. -/
def writtenForm (s : String) : String := Id.run do
  let cs := s.toList.toArray
  let mut out : Array Char := #[]
  let mut i := 0
  let mut space := false
  while i < cs.size do
    let c := cs[i]!
    if c.isWhitespace then
      space := true
      i := i + 1
      continue
    if space && out.back?.any isWordChar && isWordChar c then out := out.push ' '
    space := false
    out := out.push c
    i := i + 1
    if c == '"' then
      while i < cs.size && cs[i]! != '"' do
        if cs[i]! == '\\' && i + 1 < cs.size then
          out := out.push cs[i]!
          i := i + 1
        out := out.push cs[i]!
        i := i + 1
      if i < cs.size then
        out := out.push cs[i]!
        i := i + 1
  return String.ofList out.toList

def writtenSame (a b : String) : Bool := writtenForm a == writtenForm b

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
(`lint::same_branches`). -/
def sameBranches (same : Bool) : Bool := same

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
  ["and", "else", "if", "iff", "in", "inter", "join", "match", "minus", "not", "or", "subset", "then", "union",
    "unless", "when"]
  -- keep-sorted end

/-- Where an expression that is written after the text `before`, not in
parentheses, is an operand: of the operator that `before` ends with, on
its right, or of `when` or `unless`, on its left. An expression not in
parentheses is never a left operand otherwise, as it is a conditional,
whose `else` extends as far right as possible. -/
def slotAfter (before : String) : Option Slot :=
  let (lx, rest) := lastLexeme before.toList.reverse
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
  | op => if (InfixOp.ofOp? op).isSome then right (.bin op) else none

/-- `if c then a else a`, where `branch` is the text of `a` and `prec` its
precedence, and `before` the text before the conditional. The fix is the
branch, in parentheses where `lang::operand` requires them. -/
def sameBranchesMsg (branch : String) (prec : Nat) (before : String) : Msg :=
  let replacement := BText.inSlot { text := branch, prec } (slotAfter before)
  { code? := some "F0737", headline := "both branches of `if` are written the same"
    label? := some s!"`{branch}` whatever the condition"
    fixes := #[{ msg := "remove the condition, which decides nothing", replacement }] }

/-- The elements of a literal that are written the same as an earlier one,
by their positions (`lint::duplicate_elements`). -/
def repeatedElements (texts : Array String) : Array Nat :=
  let forms := texts.map writtenForm
  (Array.range forms.size).filter fun i => (forms.extract 0 i).contains forms[i]!

/-- Whether `duplicate_elements` fires (`lint::duplicate_elements`). -/
def duplicateElements (nRepeats : Nat) : Bool := nRepeats > 0

/-- A set or relation literal, at `lit` in `src`, whose elements, at
`elems`, repeat at `repeats` (`repeatedElements`). The fix removes each
repeat, with the separator before it. -/
def duplicateElementsMsg (src : Array Char) (lit : Range) (elems : Array Range) (repeats : Array Nat) : Msg := Id.run do
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

/-! ## Operators and methods -/

/-- Whether `a OP b` holds, from how `a` compares with `b`
(`lint::comparison_holds`). -/
def Comparison.holds : Comparison → Ordering → Bool
  | .eq, o => o == .eq
  | .ne, o => o != .eq
  | .lt, o => o == .lt
  | .le, o => o != .gt
  | .gt, o => o == .gt
  | .ge, o => o != .lt

/-- The comparison that `a OP₁ b and a OP₂ b`, or with `or` if not `conj`,
is, if one is and it is neither of the two (`lint::double_comparison`). -/
def doubleComparison (conj : Bool) (first second : Comparison) : Option Comparison :=
  let both (o : Ordering) := if conj then first.holds o && second.holds o else first.holds o || second.holds o
  Comparison.all.find? fun c => c != first && c != second && [Ordering.lt, .eq, .gt].all fun o => c.holds o == both o

/-- `a OP₁ b and a OP₂ b`, or `or`, as the text of the comparison it is. -/
def doubleComparisonMsg (fixed : String) : Msg :=
  { code? := some Lint.doubleComparison.code, headline := s!"these two comparisons are `{fixed}`"
    label? := some "compares the same operands twice"
    fixes := #[{ msg := "write it as one comparison", replacement := fixed }] }

/-- Whether `bool_equality` fires on `a OP b` (`lint::bool_equality`). -/
def boolEquality (op : Comparison) (bools literal : Bool) : Bool := op == .eq && bools && !literal

/-- `a = b` on `Bool`s, as the text of `a iff b`. -/
def boolEqualityMsg (fixed : String) : Msg :=
  { code? := some Lint.boolEquality.code, headline := "equality of `Bool`s is `iff`"
    label? := some "compares two `Bool`s"
    notes := #["note: on `Bool`s, `=` and `iff` agree, and `iff` says that this is an equivalence"]
    fixes := #[{ msg := "write it with `iff`", replacement := fixed }] }

/-- What `s.index_of(t, 0) OP bound` says (`lint::IndexTest`). -/
inductive IndexTest where
  | found
  | absent
  | atStart
  | other
  deriving Inhabited, BEq, DecidableEq, Repr

/-- What `s.index_of(t, 0) OP bound` says, with the call on the left
(`lint::index_test`). -/
def indexTest (op : Comparison) (bound : Int) : IndexTest :=
  match op with
  | .ge => if bound == 0 then .found else .other
  | .gt | .ne => if bound == -1 then .found else .other
  | .lt => if bound == 0 then .absent else .other
  | .le => if bound == -1 then .absent else .other
  | .eq => if bound == -1 then .absent else if bound == 0 then .atStart else .other

/-- A search written with `index_of` or `slice`, as the text of the call of
`method` that it is. -/
def manualMethodMsg (method fixed : String) (slice : Bool) : Msg :=
  { code? := some Lint.manualMethod.code, headline := s!"this is a call of `{method}`"
    label? := some (if slice then "compares a prefix" else "compares a position")
    fixes := #[{ msg := s!"call `{method}`", replacement := fixed }] }

/-- Whether `else_extends` fires on a conditional that is an operand of an
operator of precedence `outer`, from the precedence `inner` of its `else`
branch (`lint::else_extends`). -/
def elseExtends (outer inner : Nat) (assoc : Assoc) (right : Bool) : Bool := !bareOperand outer inner assoc right

/-- A conditional that is an operand of `op`, as the text of its `else`
branch, and of the conditional with the branch in parentheses. -/
def elseExtendsMsg (op branch fixed : String) : Msg :=
  { code? := some Lint.elseExtends.code, headline := "the `else` branch extends past the operator"
    label? := some s!"the `else` branch is `{branch}`"
    notes := #[s!"note: the conditional is an operand of `{op}`, but its `else` branch extends as far right as possible"]
    fixes := #[{ msg := "put the `else` branch in parentheses, which keeps the meaning", replacement := fixed }] }

/-- An operator that `identity_op` looks at (`lint::IdentityOperator`). -/
inductive IdentityOperator where
  | add
  | sub
  | mul
  | concat
  | union
  | minus
  deriving Inhabited, BEq, DecidableEq, Repr

def IdentityOperator.ofOp? : String → Option IdentityOperator
  | "+" => some .add
  | "-" => some .sub
  | "*" => some .mul
  | "++" => some .concat
  | "union" => some .union
  | "minus" => some .minus
  | _ => none

/-- An operand, as `identity_op` sees it (`lint::IdentityOperand`):
`empty` is `""`, `[]` or `{}`. -/
inductive IdentityOperand where
  | zero
  | one
  | empty
  | negation
  | other
  deriving Inhabited, BEq, DecidableEq, Repr

/-- What `identity_op` writes for `a OP b` (`lint::Rewrite`): `flip` is
`a - y` for `a + -y`, and `a + y` for `a - -y`. -/
inductive Rewrite where
  | keepLeft
  | keepRight
  | flip
  | unchanged
  deriving Inhabited, BEq, DecidableEq, Repr

/-- What `identity_op` writes for `a OP b` (`lint::identity_op`). -/
def identityRewrite (op : IdentityOperator) (left right : IdentityOperand) : Rewrite :=
  match op with
  | .add => if right == .zero then .keepLeft else if left == .zero then .keepRight
    else if right == .negation then .flip else .unchanged
  | .sub => if right == .zero then .keepLeft else if right == .negation then .flip else .unchanged
  | .mul => if right == .one then .keepLeft else if left == .one then .keepRight else .unchanged
  | .concat | .union => if right == .empty then .keepLeft else if left == .empty then .keepRight else .unchanged
  | .minus => if right == .empty then .keepLeft else .unchanged

def identityOpMsg (fixed : String) (flip : Bool) : Msg :=
  { code? := some Lint.identityOp.code
    headline := if flip then "this negation can be the other operator" else "this operation has no effect"
    label? := some (if flip then "an operand that is a negation" else "leaves its other operand as it is")
    fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

/-- A message of an operator or method lint, whose first fix replaces the
text at `ref`. -/
structure OpReport (α : Type) where
  lint : Lint
  ref : α
  msg : Msg
  deriving Inhabited

def BNode.kind : BNode α → BKind | .mk k .. => k
def BNode.range : BNode α → Range | .mk _ r .. => r
def BNode.ref : BNode α → α | .mk _ _ a _ => a
def BNode.kids : BNode α → Array (BNode α) | .mk _ _ _ ks => ks

/-- `s` without whitespace: two expressions are written the same if this
is the same for both. -/
def squash (s : String) : String := String.ofList (s.toList.filter (!·.isWhitespace))

/-- `r` with the parentheses around it within `outer`, however many. -/
partial def withParensIn (src : Array Char) (outer r : Range) : Range :=
  match parensAround? src outer r with
  | some r' => withParensIn src outer r'
  | none => r

/-- The operand `k` of an expression at `outer`, as written: with its
parentheses. -/
def operandText (src : Array Char) (outer : Range) (k : BNode α) : String := textOf src (withParensIn src outer k.range)

/-- `k`, without the parentheses around it, and its precedence. -/
def BNode.text (src : Array Char) (k : BNode α) : BText := { text := textOf src k.range, prec := k.kind.prec }

/-- `left OP right`, for a binary operator `op`, each operand in
parentheses if it needs them there. -/
def binText (op : String) (left right : BText) : BText :=
  let k := BKind.bin op
  { text := s!"{left.inSlot (some ⟨k.prec, k.assoc, false⟩)} {op} {right.inSlot (some ⟨k.prec, k.assoc, true⟩)}"
    prec := k.prec }

/-- The text of `t`, which replaces `n`, in `slot` within `parent`: in
parentheses if it needs them there and `n` is not already in them. -/
def placed (src : Array Char) (n : BNode α) (slot : Option Slot) (parent : Range) (t : BText) : String :=
  if enclosed src parent n.range then t.text else t.inSlot slot

/-- The comparison `n` is, with its operands' texts squashed. -/
def comparisonOf? (src : Array Char) (n : BNode α) : Option (Comparison × String × String) := do
  let .bin op := n.kind | none
  let #[a, b] := n.kids | none
  let c ← Comparison.ofOp? op
  return (c, squash (textOf src a.range), squash (textOf src b.range))

/-- `double_comparison` on `n`, an `and` or an `or`, in `slot` within
`parent` (`lint::double_comparison`). -/
def doubleComparisonAt? (src : Array Char) (n : BNode α) (slot : Option Slot) (parent : Range) (conj : Bool) :
    Option (OpReport α) := do
  let #[l, r] := n.kids | none
  let .bin lop := l.kind | none
  let .bin rop := r.kind | none
  let #[a, b] := l.kids | none
  let op ← if lop == "subset" && rop == "subset" then do
      let #[c, d] := r.kids | none
      -- `a subset b and b subset a`.
      unless conj && squash (textOf src c.range) == squash (textOf src b.range)
        && squash (textOf src d.range) == squash (textOf src a.range) do none
      pure "="
    else do
      let (c1, a1, b1) ← comparisonOf? src l
      let (c2, a2, b2) ← comparisonOf? src r
      let c2 ← if a2 == a1 && b2 == b1 then pure c2 else if a2 == b1 && b2 == a1 then pure c2.mirror else none
      pure (← doubleComparison conj c1 c2).op
  let fixed := placed src n slot parent (binText op (a.text src) (b.text src))
  return { lint := .doubleComparison, ref := n.ref, msg := doubleComparisonMsg fixed }

/-- `bool_equality` on `n`, a comparison in `slot` within `parent`, where
`boolEq` says whether a comparison's operands are `Bool`s. -/
def boolEqualityAt? (src : Array Char) (boolEq : α → Bool) (n : BNode α) (slot : Option Slot) (parent : Range) :
    Option (OpReport α) := do
  let .bin op := n.kind | none
  let c ← Comparison.ofOp? op
  let #[a, b] := n.kids | none
  unless boolEquality c (boolEq n.ref) (a.kind matches .lit _ || b.kind matches .lit _) do none
  let fixed := placed src n slot parent (binText "iff" (a.text src) (b.text src))
  return { lint := .boolEquality, ref := n.ref, msg := boolEqualityMsg fixed }

/-- The integer that `n` is written as, if it is a literal or a negated one. -/
def intLiteral? (src : Array Char) (n : BNode α) : Option Int :=
  match n.kind with
  | .atom | .neg => (squash (textOf src n.range)).toInt?
  | _ => none

/-- `manual_method` on `n`, a comparison in `slot` within `parent`
(`lint::index_test`, `lint::manual_method`). -/
def manualMethodAt? (src : Array Char) (n : BNode α) (slot : Option Slot) (parent : Range) : Option (OpReport α) := do
  let .bin op := n.kind | none
  let c ← Comparison.ofOp? op
  let #[a, b] := n.kids | none
  -- The call, the other operand, and the comparison with the call on the left.
  let (call, other, c) := if a.kind matches .method _ then (a, b, c) else (b, a, c.mirror)
  let .method m := call.kind | none
  let #[recv, x, y] := call.kids | none
  let r := operandText src call.range recv
  let report (method fixed : String) (prec : Nat) (slice : Bool) : OpReport α :=
    let fixed := placed src n slot parent { text := fixed, prec }
    { lint := .manualMethod, ref := n.ref, msg := manualMethodMsg method fixed slice }
  if m == "index_of" then
    unless squash (textOf src y.range) == "0" do none
    let t := textOf src x.range
    match indexTest c (← intLiteral? src other) with
    | .found => return report "contains?" s!"{r}.contains?({t})" (BKind.method "").prec false
    | .absent => return report "contains?" s!"not {r}.contains?({t})" BKind.not.prec false
    | .atStart => return report "starts_with?" s!"{r}.starts_with?({t})" (BKind.method "").prec false
    | .other => none
  -- `s.slice(0, t.len) = t`.
  unless m == "slice" && c == .eq && squash (textOf src x.range) == "0" do none
  let o := squash (textOf src other.range)
  let len := squash (textOf src y.range)
  unless len == o ++ ".len" || len == s!"({o}).len" do none
  return report "starts_with?" s!"{r}.starts_with?({textOf src other.range})" (BKind.method "").prec true

/-- The `else` branch that ends a conditional: of the last conditional in a
chain of `else if`s written without parentheses. -/
partial def lastElse (src : Array Char) (n : BNode α) : Option (BNode α) := do
  let #[_, _, e] := n.kids | none
  if e.kind == .ite && !enclosed src n.range e.range then lastElse src e else some e

/-- `else_extends` on the operand `k`, a conditional, of `n`, a binary
operator, in `slot` (`lint::else_extends`). -/
def elseExtendsAt? (src : Array Char) (n k : BNode α) (slot : Slot) : Option (OpReport α) := do
  let .bin op := n.kind | none
  unless k.kind == .ite && !enclosed src n.range k.range do none
  let e ← lastElse src k
  unless !enclosed src k.range e.range && elseExtends slot.outer e.kind.prec slot.assoc slot.right do none
  let branch := textOf src e.range
  let fixed := textOf src { start := k.range.start, stop := e.range.start } ++ s!"({branch})"
    ++ textOf src { start := e.range.stop, stop := k.range.stop }
  return { lint := .elseExtends, ref := k.ref, msg := elseExtendsMsg op branch fixed }

/-- How `identity_op` sees the operand `k`. -/
def identityOperand (src : Array Char) (k : BNode α) : IdentityOperand :=
  match k.kind, squash (textOf src k.range) with
  | .neg, _ => .negation
  | .atom, "0" => .zero
  | .atom, "1" => .one
  | .atom, "\"\"" | .atom, "[]" | .atom, "{}" => .empty
  | _, _ => .other

/-- `identity_op` on `n`, a binary operator in `slot` within `parent`
(`lint::identity_op`). -/
def identityOpAt? (src : Array Char) (n : BNode α) (slot : Option Slot) (parent : Range) : Option (OpReport α) := do
  let .bin op := n.kind | none
  let o ← IdentityOperator.ofOp? op
  let #[a, b] := n.kids | none
  let (t, flip) ← match identityRewrite o (identityOperand src a) (identityOperand src b) with
    | .keepLeft => some (a.text src, false)
    | .keepRight => some (b.text src, false)
    | .flip =>
      let y ← b.kids[0]?
      some (binText (if o == .add then "-" else "+") (a.text src) (y.text src), true)
    | .unchanged => none
  let fixed := placed src n slot parent t
  return { lint := .identityOp, ref := n.ref, msg := identityOpMsg fixed flip }

/-- The messages of the operator and method lints in `n`, which is in
`slot` within `parent`, outermost first. -/
partial def opReportsIn (src : Array Char) (boolEq : α → Bool) (n : BNode α) (slot : Option Slot) (parent : Range) :
    Array (OpReport α) :=
  let slots := n.kind.slots
  let own := match n.kind with
    | .bin op =>
      let operands := (n.kids.zip slots).filterMap fun (k, s) => s.bind (elseExtendsAt? src n k ·)
      (if op == "and" || op == "or" then (doubleComparisonAt? src n slot parent (op == "and")).toArray else #[])
        ++ (boolEqualityAt? src boolEq n slot parent).toArray ++ (manualMethodAt? src n slot parent).toArray
        ++ (identityOpAt? src n slot parent).toArray ++ operands
    | _ => #[]
  own ++ (n.kids.mapIdx fun i k => opReportsIn src boolEq k (slots[i]?.join) n.range).flatten

/-- The messages of the operator and method lints in an expression written
in `src` (`Reqs/Lint/Complexity#comparisons`), where `boolEq` says whether a comparison
compares `Bool`s. -/
def opReports (src : Array Char) (boolEq : α → Bool) (root : BNode α) : Array (OpReport α) :=
  opReportsIn src boolEq root none root.range

/-! ## Arithmetic and parentheses -/

/-- Whether `double_parens` fires on `depth` pairs of parentheses, each
directly around the next (`lint::double_parens`). -/
def doubleParens (depth : Nat) : Bool := depth ≥ 2

/-- `((e))`, where `inner` is the text of the innermost pair, `(e)`. -/
def doubleParensMsg (inner : String) : Msg :=
  { code? := some Lint.doubleParens.code, headline := "parentheses directly around parentheses"
    label? := some "double parentheses"
    fixes := #[{ msg := "remove the outer parentheses", replacement := inner }] }

/-- Whether `double_neg` fires on a negation, whose operand, through
parentheses, is a negation if `negatedOperand` (`lint::double_neg`). -/
def doubleNeg (negatedOperand : Bool) : Bool := negatedOperand

def doubleNegMsg (replacement : String) : Msg :=
  { code? := some Lint.doubleNeg.code, headline := "negating twice is the operand itself", label? := some "a double negation"
    fixes := #[{ msg := s!"write `{replacement}`", replacement }] }

/-- An operand of a comparison, as `int_plus_one` sees it
(`lint::Offset`): `e + 1` or `1 + e`, `e - 1`, or neither. -/
inductive Offset where
  | zero
  | plusOne
  | minusOne
  deriving Inhabited, BEq, DecidableEq, Repr

/-- Whether `int_plus_one` fires on `l op r`, the strict comparison of its
fix, and whether the fix drops the offset of `l`, rather than of `r`
(`lint::int_plus_one`). -/
def intPlusOne (op : Comparison) (l r : Offset) : Bool × Comparison × Bool :=
  match op, l, r with
  | .ge, _, .plusOne => (true, .gt, false)
  | .ge, l, _ => (l matches .minusOne, .gt, true)
  | .le, .plusOne, _ => (true, .lt, true)
  | .le, _, r => (r matches .minusOne, .lt, false)
  | _, _, _ => (false, op, false)

def intPlusOneMsg (replacement : String) : Msg :=
  { code? := some Lint.intPlusOne.code, headline := "over integers, this is a strict comparison"
    label? := some "compares with an operand off by one"
    fixes := #[{ msg := s!"write `{replacement}`", replacement }] }

/-- Whether `neg_multiply` fires on `a * b`, where each says whether that
operand is `-1`, and whether the fix negates `a`, rather than `b`
(`lint::neg_multiply`). -/
def negMultiply (aMinusOne bMinusOne : Bool) : Bool × Bool := (aMinusOne || bMinusOne, bMinusOne)

def negMultiplyMsg (replacement : String) : Msg :=
  { code? := some Lint.negMultiply.code, headline := "multiplying by `-1` is negation", label? := some "a product with `-1`"
    fixes := #[{ msg := s!"write `{replacement}`", replacement }] }

/-- A report of `double_neg`, `int_plus_one` or `neg_multiply`: the lint,
where, and the fix, which replaces the range. -/
structure ShapeReport (α : Type) where
  lint : Lint
  ref : α
  range : Range
  msg : Msg
  deriving Inhabited

/-- `-t`, with a space if `t` starts with `-`, which would start a comment. -/
def negText (t : String) : String := if t.startsWith "-" then s!"- {t}" else s!"-{t}"

/-- The reports of `double_neg`, `int_plus_one` and `neg_multiply` in `n`,
which is in `slot` within `parent`, and in its operands, in order. An
atom's operands, such as an application's arguments, are where any
expression can be written. -/
partial def shapeReports (src : Array Char) (n : BNode α) (slot : Option Slot) (parent : Range) : Array (ShapeReport α) :=
  let .mk kind range ref kids := n
  let text (k : BNode α) : BText := match k with | .mk kk kr .. => { text := textOf src kr, prec := kk.prec }
  let isOne (k : BNode α) : Bool := match k with | .mk .atom kr _ _ => textOf src kr == "1" | _ => false
  let isMinusOne (k : BNode α) : Bool := match k with | .mk .neg _ _ #[o] => isOne o | _ => false
  -- The text of the replacement, parenthesized where the expression is.
  let place (t : BText) : String := if enclosed src parent range then t.text else t.inSlot slot
  let report (l : Lint) (msg : String → Msg) (t : BText) : Array (ShapeReport α) :=
    let replacement := place t
    #[{ lint := l, ref, range, msg := msg replacement }]
  let own := match kind, kids with
    | .neg, #[.mk .neg _ _ #[b]] =>
      if doubleNeg true then report .doubleNeg doubleNegMsg (text b) else #[]
    | .bin "*", #[a, b] =>
      match negMultiply (isMinusOne a) (isMinusOne b) with
      | (true, negA) =>
        let t := (text (if negA then a else b)).inSlot (some ⟨BKind.neg.prec, .right, true⟩)
        report .negMultiply negMultiplyMsg { text := negText t, prec := BKind.neg.prec }
      | _ => #[]
    | .bin op, #[a, b] =>
      -- An operand as `int_plus_one` sees it, and its text without the offset.
      let offset (k : BNode α) : Offset × BText := match k with
        | .mk (.bin "+") _ _ #[x, y] => if isOne y then (.plusOne, text x) else if isOne x then (.plusOne, text y) else (.zero, text k)
        | .mk (.bin "-") _ _ #[x, y] => if isOne y then (.minusOne, text x) else (.zero, text k)
        | _ => (.zero, text k)
      match Comparison.ofOp? op with
      | some c =>
        let ((oa, ta), (ob, tb)) := (offset a, offset b)
        match intPlusOne c oa ob with
        | (true, strict, dropLeft) =>
          let (l, r) := if dropLeft then (ta, text b) else (text a, tb)
          let slot (right : Bool) : Option Slot := some ⟨kind.prec, kind.assoc, right⟩
          report .intPlusOne intPlusOneMsg { text := s!"{l.inSlot (slot false)} {strict.op} {r.inSlot (slot true)}", prec := kind.prec }
        | _ => #[]
      | none => #[]
    | _, _ => #[]
  (kids.zipIdx.foldl (init := own) fun acc (k, i) => acc ++ shapeReports src k (kind.slots[i]?.join) range)

/-- The reports of `double_neg`, `int_plus_one` and `neg_multiply` in an
expression written in `src`, in the order they start, the outer of two
that start together first. -/
def arithReports (src : Array Char) (root : BNode α) : Array (ShapeReport α) :=
  let range := match root with | .mk _ r .. => r
  (shapeReports src root none range).qsort fun a b =>
    a.range.start < b.range.start || (a.range.start == b.range.start && a.range.stop > b.range.stop)

/-! ## Methods, patterns, types and matches -/

/-- The fix of a method without arguments called on the result of another
(`lint::method_chain`). -/
inductive ChainFix where
  /-- No shorter form. -/
  | keep
  /-- `e.inner.outer` is `e`. -/
  | receiver
  /-- `e.inner.outer` is `e.m`. -/
  | single (m : Method)
  deriving Inhabited, BEq, Repr

/-- The fix of `e.inner.outer` (`lint::method_chain`). -/
def methodChain : Method → Method → ChainFix
  | .rev, .rev | .inverse, .inverse => .receiver
  | .inverse, .domain => .single .range
  | .inverse, .range => .single .domain
  | .inverse, .card => .single .card
  | .rev, .len => .single .len
  | .closure, .closure => .single .closure
  | .closure, .domain => .single .domain
  | .closure, .range => .single .range
  | _, _ => .keep

/-- Calls `m` on a chain of methods in its shortest form, given innermost
last, and rewrites the result until it is shortest again. -/
def pushMethod : List Method → Method → List Method
  | inner :: rest, m =>
    match methodChain inner m with
    | .receiver => rest
    | .single m' => pushMethod rest m'
    | .keep => m :: inner :: rest
  | [], m => [m]

/-- The shortest form of a chain of methods without arguments, innermost
first: each pair that `methodChain` shortens is rewritten, until none is. -/
def shortestChain (ms : List Method) : List Method := (ms.foldl pushMethod []).reverse

/-- A chain of methods, whose shortest form is `fixed`. -/
def methodChainMsg (fixed : String) : Msg :=
  { code? := some "F0743", headline := "this chain of methods has a shorter form"
    label? := some "means the same as a shorter chain"
    fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

/-- What `trivial_pattern` writes instead of `s.matches?(p)`
(`lint::trivial_pattern`). -/
inductive PatternFix where
  | equality
  | startsWith
  | endsWith
  | contains
  deriving Inhabited, BEq, DecidableEq, Repr

/-- The string that the characters of a pattern match, if they are each a
character that is not special or `\` and a special one. -/
def literalPattern? : List Char → Option (List Char)
  | [] => some []
  | '\\' :: c :: rest => if reSpecials.contains c then (c :: ·) <$> literalPattern? rest else none
  | c :: rest => if reSpecials.contains c && c != '-' then none else (c :: ·) <$> literalPattern? rest

/-- If `trivial_pattern` fires on the pattern `p`, a string with `.*` at
its start, its end, both or neither, the fix and the string
(`lint::trivial_pattern`). -/
def trivialPattern? (p : String) : Option (PatternFix × String) := do
  let cs := p.toList
  let pre := cs.take 2 == ['.', '*']
  let cs := if pre then cs.drop 2 else cs
  let post := cs.length ≥ 2 && cs.drop (cs.length - 2) == ['.', '*']
  let lit ← literalPattern? (if post then cs.take (cs.length - 2) else cs)
  if lit.isEmpty then none
  let fix : PatternFix := match pre, post with
    | false, false => .equality
    | false, true => .startsWith
    | true, false => .endsWith
    | true, true => .contains
  return (fix, String.ofList lit)

/-- The fix of `s.matches?(p)`, from the text of `s` without parentheses
and as written, the fix and the string. -/
def trivialPatternText (recv : BText) (recvAtom : String) (fix : PatternFix) (lit : String) : BText :=
  let method (m : String) : BText := { text := s!"{recvAtom}.{m}({lit.quote})", prec := 9 }
  match fix with
  | .equality => { text := s!"{recv.inSlot (some ⟨5, .nonAssoc, false⟩)} = {lit.quote}", prec := 5 }
  | .startsWith => method "starts_with?"
  | .endsWith => method "ends_with?"
  | .contains => method "contains?"

def trivialPatternMsg (fix : PatternFix) (fixed : String) : Msg :=
  let label := match fix with
    | .equality => "matches one string"
    | .startsWith => "matches the strings that start with one"
    | .endsWith => "matches the strings that end with one"
    | .contains => "matches the strings that contain one"
  { code? := some "F0744", headline := "this pattern has no operator but `.*`", label? := some label
    fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

/-- Whether `redundant_bool_type` fires on a declaration of `n`, where
`isBool?` is whether its type, if written, is `Bool`
(`lint::redundant_bool_type`). -/
def redundantBoolType (n : Name) (isBool? : Option Bool) : Bool :=
  Fren.Str.endsWith (nameText n) "?" && isBool? == some true

def redundantBoolTypeMsg (n : Name) : Msg :=
  { code? := some "F0746", headline := s!"`{nameText n}` is a `Bool` by its name", label? := some "implied by the `?`"
    notes := #["note: a name that ends in `?` is a `Bool`, and only such a name is"]
    fixes := #[{ msg := "remove `: Bool`", replacement := "" }] }

/-- Whether `trivial_match` fires on a `match` of `nArms` arms, whose first
binds a name if `binds` (`lint::trivial_match`). -/
def trivialMatch (nArms : Nat) (binds : Bool) : Bool := nArms == 1 && !binds

/-- A `match` of one arm, whose body, as the fix writes it, is `fixed`. -/
def trivialMatchMsg (fixed : String) : Msg :=
  { code? := some "F0747", headline := "this `match` has one arm, which binds nothing"
    label? := some "always its only arm"
    notes := #["note: its value is the arm's body, whatever the scrutinee is"]
    fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

/-! ## Expectations -/

/-- A `set_option` to `expect`, with the level of
`unfulfilled_lint_expectations` there. -/
structure ExpectationRecord where
  /-- The lint expected, or the group, any of whose lints fulfils it. -/
  target : LintTarget
  level : LevelInEffect
  deriving Inhabited, Repr

/-- Whether an expectation is fulfilled (`lint::expectation`). -/
def expectationFulfilled (nFired : Nat) : Bool := nFired > 0

/-- Whether an unfulfilled expectation is reported (`lint::expectation`). -/
def expectationReported (nFired : Nat) (level : LintLevel) : Bool :=
  !expectationFulfilled nFired && level != .allow && level != .expect

def unfulfilledMsg (t : LintTarget) (fixable : Bool := false) : Msg :=
  let what := match t with
    | .lint l => s!"`{l.name}`"
    | .group g => s!"no lint of `{g.name}`"
  let expects := match t with
    | .lint l => s!"`{l.name}` to fire"
    | .group g => s!"some lint of `{g.name}` to fire"
  { code? := some Lint.unfulfilledExpectations.code, headline := "this lint expectation is unfulfilled"
    label? := some s!"{what} {if t matches .lint _ then "never fires" else "fires"} where this is in effect"
    notes := #[s!"note: `set_option {t.optionString} \"expect\"` expects {expects} where it is in effect",
      "help: remove this `set_option`"] ++ (if fixable then #[fixHelp] else #[]) }

/-- The messages for the expectations that nothing fulfilled, given the
indices of those fulfilled. -/
def expectationReports (exps : Array (ExpectationRecord × α)) (fulfilled : Array Nat) (fixable : Bool := false) :
    Array (LintReport α) :=
  (exps.mapIdx fun i (e, ref) => (i, e, ref)).filterMap fun (i, e, ref) =>
    if expectationReported (fulfilled.count i) e.level.effective then
      some { lint := .unfulfilledExpectations, level := e.level, ref, msg := unfulfilledMsg e.target fixable }
    else none

end Fren.Core
