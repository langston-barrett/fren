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
  | zeroSizedMapValues
  | manySingleCharNames
  | similarNames
  | tooManyLines
  | moduleInception
  | enumVariantNames
  | upperCaseAcronyms
  | justUnderscoresAndDigits
  | disallowedNames
  | needlessBoolAssign
  | needlessMatch
  | assertionsOnConstants
  | suspiciousUnaryOpFormatting
  | redundantSlicing
  | noEffectReplace
  | constIsEmpty
  | manualPatternCharComparison
  | almostCompleteRange
  | duplicateConstraint
  | invisibleCharacters
  | negativePosition
  | absurdExtremeComparisons
  | erasingOp
  | ifsSameCond
  | contradictoryComparisons
  | redundantComparisons
  | allowAttributes
  | wildcardEnumMatchArm
  | needlessRawStrings
  | nonAsciiLiteral
  | moduleNameRepetitions
  | minIdentChars
  | absolutePaths
  | precedence
  deriving Inhabited, BEq, DecidableEq, Repr

def Lint.all : Array Lint :=
  #[.unusedImports, .globImports, .nonSnakeCase, .nonCamelCaseTypes, .nonUpperCaseConstants, .unfulfilledExpectations,
    .unusedVariables, .deadCode, .nonminimalBool, .undecidable, .lengthZero, .cardZero,
    .singletonMembership, .membershipChain, .constantOutput, .definableOutput, .indexAfterUse, .unlessNot,
    .collapsibleWhen, .ifNotElse, .matchSameArms, .matchLikeMembership, .wildcardSingleVariant, .ifChainMatch,
    .caseSplitReqs, .redundantBindings, .eqOp, .sameBranches, .duplicateElements, .emptyArgument, .doubleComparison,
    .boolEquality, .manualMethod, .elseExtends, .identityOp, .doubleParens, .doubleNeg, .intPlusOne, .negMultiply,
    .redundantMethodChain, .trivialPattern, .redundantBoolType, .trivialMatch,
    .zeroSizedMapValues, .manySingleCharNames, .similarNames, .tooManyLines, .moduleInception, .enumVariantNames,
    .upperCaseAcronyms, .justUnderscoresAndDigits, .disallowedNames, .needlessBoolAssign, .needlessMatch,
    .assertionsOnConstants, .suspiciousUnaryOpFormatting, .redundantSlicing, .noEffectReplace, .constIsEmpty,
    .manualPatternCharComparison, .almostCompleteRange, .duplicateConstraint, .invisibleCharacters, .negativePosition,
    .absurdExtremeComparisons, .erasingOp, .ifsSameCond, .contradictoryComparisons, .redundantComparisons,
    .allowAttributes, .wildcardEnumMatchArm, .needlessRawStrings, .nonAsciiLiteral, .moduleNameRepetitions,
    .minIdentChars, .absolutePaths, .precedence]

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
  | .zeroSizedMapValues => "zero_sized_map_values"
  | .manySingleCharNames => "many_single_char_names"
  | .similarNames => "similar_names"
  | .tooManyLines => "too_many_lines"
  | .moduleInception => "module_inception"
  | .enumVariantNames => "enum_variant_names"
  | .upperCaseAcronyms => "upper_case_acronyms"
  | .justUnderscoresAndDigits => "just_underscores_and_digits"
  | .disallowedNames => "disallowed_names"
  | .needlessBoolAssign => "needless_bool_assign"
  | .needlessMatch => "needless_match"
  | .assertionsOnConstants => "assertions_on_constants"
  | .suspiciousUnaryOpFormatting => "suspicious_unary_op_formatting"
  | .redundantSlicing => "redundant_slicing"
  | .noEffectReplace => "no_effect_replace"
  | .constIsEmpty => "const_is_empty"
  | .manualPatternCharComparison => "manual_pattern_char_comparison"
  | .almostCompleteRange => "almost_complete_range"
  | .duplicateConstraint => "duplicate_constraint"
  | .invisibleCharacters => "invisible_characters"
  | .negativePosition => "negative_position"
  | .absurdExtremeComparisons => "absurd_extreme_comparisons"
  | .erasingOp => "erasing_op"
  | .ifsSameCond => "ifs_same_cond"
  | .contradictoryComparisons => "contradictory_comparisons"
  | .redundantComparisons => "redundant_comparisons"
  | .allowAttributes => "allow_attributes"
  | .wildcardEnumMatchArm => "wildcard_enum_match_arm"
  | .needlessRawStrings => "needless_raw_strings"
  | .nonAsciiLiteral => "non_ascii_literal"
  | .moduleNameRepetitions => "module_name_repetitions"
  | .minIdentChars => "min_ident_chars"
  | .absolutePaths => "absolute_paths"
  | .precedence => "precedence"

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
  | .zeroSizedMapValues => "F0789"
  | .manySingleCharNames => "F0795"
  | .similarNames => "F0796"
  | .tooManyLines => "F0797"
  | .moduleInception => "F0748"
  | .enumVariantNames => "F0749"
  | .upperCaseAcronyms => "F0750"
  | .justUnderscoresAndDigits => "F0751"
  | .disallowedNames => "F0752"
  | .needlessBoolAssign => "F0759"
  | .needlessMatch => "F0760"
  | .assertionsOnConstants => "F0761"
  | .suspiciousUnaryOpFormatting => "F0762"
  | .redundantSlicing => "F0753"
  | .noEffectReplace => "F0754"
  | .constIsEmpty => "F0755"
  | .manualPatternCharComparison => "F0756"
  | .almostCompleteRange => "F0757"
  | .duplicateConstraint => "F0768"
  | .invisibleCharacters => "F0769"
  | .negativePosition => "F0770"
  | .absurdExtremeComparisons => "F0763"
  | .erasingOp => "F0764"
  | .ifsSameCond => "F0765"
  | .contradictoryComparisons => "F0766"
  | .redundantComparisons => "F0767"
  | .allowAttributes => "F0780"
  | .wildcardEnumMatchArm => "F0781"
  | .needlessRawStrings => "F0782"
  | .nonAsciiLiteral => "F0783"
  | .moduleNameRepetitions => "F0784"
  | .minIdentChars => "F0785"
  | .absolutePaths => "F0786"
  | .precedence => "F0787"

/-- A group of lints (`lint::Group`). Each lint is in exactly one, whose
level it takes by default. -/
inductive Group where
  | unused
  | nonstandardStyle
  | style
  | complexity
  | suspicious
  | pedantic
  | restriction
  | decidability
  deriving Inhabited, BEq, DecidableEq, Repr

def Group.all : Array Group := #[.unused, .nonstandardStyle, .style, .complexity, .suspicious, .pedantic, .restriction,
  .decidability]

def Group.name : Group → String
  | .unused => "unused"
  | .nonstandardStyle => "nonstandard_style"
  | .style => "style"
  | .complexity => "complexity"
  | .suspicious => "suspicious"
  | .pedantic => "pedantic"
  | .restriction => "restriction"
  | .decidability => "decidability"

/-- The level of a group's lints by default (`lint::group_default`).
`undecidable`, alone in `decidability`, is denied, so that a spec opts out
of decidability explicitly (`Reqs/Lang/Decidability`); `pedantic` lints are
allowed, since they would fire on much that reads well as it is, and
`restriction` lints, since each is a rule that a project chooses. -/
def Group.default : Group → LintLevel
  | .pedantic | .restriction => .allow
  | .decidability => .deny
  | _ => .warn

def Group.ofName? (s : String) : Option Group := Group.all.find? (·.name == s)

def Lint.group : Lint → Group
  | .unusedImports | .unusedVariables | .deadCode | .unfulfilledExpectations => .unused
  | .nonSnakeCase | .nonCamelCaseTypes | .nonUpperCaseConstants => .nonstandardStyle
  | .globImports | .lengthZero | .cardZero | .unlessNot | .collapsibleWhen | .matchLikeMembership | .redundantBindings
  | .doubleNeg | .negMultiply | .trivialPattern | .redundantBoolType | .moduleInception | .enumVariantNames
  | .upperCaseAcronyms | .justUnderscoresAndDigits | .disallowedNames | .assertionsOnConstants
  | .manualPatternCharComparison => .style
  | .nonminimalBool | .singletonMembership | .constantOutput | .doubleComparison | .manualMethod | .elseExtends
  | .identityOp | .doubleParens | .intPlusOne | .redundantMethodChain | .trivialMatch | .needlessBoolAssign
  | .needlessMatch | .redundantSlicing | .redundantComparisons => .complexity
  | .indexAfterUse | .eqOp | .sameBranches | .duplicateElements | .emptyArgument
  | .suspiciousUnaryOpFormatting | .noEffectReplace | .constIsEmpty | .almostCompleteRange | .duplicateConstraint
  | .invisibleCharacters | .negativePosition | .absurdExtremeComparisons | .erasingOp | .ifsSameCond
  | .contradictoryComparisons => .suspicious
  | .membershipChain | .definableOutput | .ifNotElse | .matchSameArms | .wildcardSingleVariant | .ifChainMatch
  | .caseSplitReqs | .boolEquality | .zeroSizedMapValues | .manySingleCharNames | .similarNames
  | .tooManyLines => .pedantic
  | .allowAttributes | .wildcardEnumMatchArm | .needlessRawStrings | .nonAsciiLiteral | .moduleNameRepetitions
  | .minIdentChars | .absolutePaths | .precedence => .restriction
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
for each of its lints, in its place, and leaves a forbidden one as it is. -/
def Levels.ofFlags (flags : Array (LintTarget × LintLevel)) : Levels :=
  flags.foldl (init := Levels.defaults) fun ls (t, v) =>
    t.members.foldl (init := ls) fun ls l =>
      let (ok, level) := setLevel (ls.get l).level v
      if ok then ls.set l { level, isSet := true, group? := t.group? } else ls

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

/-- Whether `absurd_extreme_comparisons` fires on a comparison of a length
`n` with `bound`, `n OP bound` if `lengthLeft` and `bound OP n` otherwise,
and what it always is (`lint::absurd_extreme_comparisons`): `n` is never
negative, so it is above `bound`, or, for `0`, the same or above. -/
def absurdComparison (op : Comparison) (bound : Int) (lengthLeft : Bool) : Bool × Bool :=
  match if lengthLeft then op else op.mirror with
  | .lt => (bound ≤ 0, false)
  | .ge => (bound ≤ 0, true)
  | .eq | .le => (bound < 0, false)
  | .ne | .gt => (bound < 0, true)

/-- A comparison of a `len`, or a `card` if `card`, that is always `value`. -/
def absurdComparisonMsg (card value : Bool) : Msg :=
  { code? := some Lint.absurdExtremeComparisons.code, headline := s!"this comparison is always `{value}`"
    label? := some s!"`{if card then "card" else "len"}` is never negative"
    notes := #["note: the bound or the operator is probably not the one meant"] }

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

/-! ## Texts -/

def isWordChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '?'

/-- The characters `cs[start:stop]` without the comments outside their
string literals: line comments, and block comments, which nest. Each
comment becomes a space. With `limit? := some n`, it stops once it has `n`
characters from the first that is not whitespace, a prefix of the whole
result, which is all that a caller reading the first lexeme needs. -/
def withoutCommentsIn (cs : Array Char) (start stop : Nat) (limit? : Option Nat := none) : Array Char := Id.run do
  let stop := min stop cs.size
  let mut out : Array Char := #[]
  let mut i := start
  -- The first character of `out` that is not whitespace, once there is one,
  -- and how far `out` has been scanned for it.
  let mut first? : Option Nat := none
  let mut scanned := 0
  -- In a string literal: the number of `#` that end it, if raw.
  let mut str? : Option (Option Nat) := none
  while i < stop do
    if let some limit := limit? then
      while first?.isNone && scanned < out.size do
        if !out[scanned]!.isWhitespace then first? := some scanned
        scanned := scanned + 1
      if let some f := first? then
        if out.size - f ≥ limit then break
    let c := cs[i]!
    match str? with
    | some raw? =>
      out := out.push c
      match raw? with
      | none =>
        if c == '\\' && i + 1 < stop then out := out.push cs[i + 1]!; i := i + 1
        else if c == '"' then str? := none
      | some n =>
        if c == '"' && (List.range n).all (fun k => i + 1 + k < stop && cs[i + 1 + k]! == '#') then
          for _ in [0:n] do out := out.push '#'
          i := i + n
          str? := none
      i := i + 1
    | none =>
      if c == '-' && i + 1 < stop && cs[i + 1]! == '-' then
        while i < stop && cs[i]! != '\n' do i := i + 1
        out := out.push ' '
      else if c == '/' && i + 1 < stop && cs[i + 1]! == '-' then
        let mut depth := 1
        i := i + 2
        while i < stop && depth > 0 do
          if cs[i]! == '/' && i + 1 < stop && cs[i + 1]! == '-' then depth := depth + 1; i := i + 2
          else if cs[i]! == '-' && i + 1 < stop && cs[i + 1]! == '/' then depth := depth - 1; i := i + 2
          else i := i + 1
        out := out.push ' '
      else if c == '"' then
        -- A raw literal is `r`, some `#`, then `"`.
        let mut hashes := 0
        while hashes < i - start && cs[i - 1 - hashes]! == '#' do hashes := hashes + 1
        let raw := i - start ≥ hashes + 1 && cs[i - hashes - 1]! == 'r'
        str? := some (if raw then some hashes else none)
        out := out.push c
        i := i + 1
      else
        out := out.push c
        i := i + 1
  return out

/-- `s` without the comments outside its string literals (`withoutCommentsIn`). -/
def withoutComments (s : String) : String :=
  let cs := s.toList.toArray
  String.ofList (withoutCommentsIn cs 0 cs.size).toList

/-- The text `s` as the lints compare it, so that two texts are *written the
same* (`Reqs/Lint#written-the-same`) if these agree: without comments or
whitespace, but for one space between two characters of names, numbers or
keywords, and with string literals, raw ones too, as they are. -/
def writtenForm (s : String) : String := Id.run do
  let cs := (withoutComments s).toList.toArray
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
      -- A raw literal is `r`, some `#`, then `"`, and has no escapes.
      let mut hashes := 0
      while hashes + 1 < out.size && out[out.size - 2 - hashes]! == '#' do hashes := hashes + 1
      let raw := out.size ≥ hashes + 2 && out[out.size - hashes - 2]! == 'r'
      let closes (k : Nat) : Bool :=
        cs[k]! == '"' && (!raw || (List.range hashes).all fun h => cs[k + 1 + h]? == some '#')
      while i < cs.size && !closes i do
        if !raw && cs[i]! == '\\' && i + 1 < cs.size then
          out := out.push cs[i]!
          i := i + 1
        out := out.push cs[i]!
        i := i + 1
      let stop := min cs.size (i + 1 + (if raw then hashes else 0))
      out := out ++ cs.extract i stop
      i := stop
  return String.ofList out.toList

/-- Whether `cs` has, anywhere, the two characters that start a line
comment, or the two that start a block comment: without them,
`withoutComments` leaves a text as it is. -/
def mayHaveComments : List Char → Bool
  | '-' :: '-' :: _ | '/' :: '-' :: _ => true
  | _ :: rest => mayHaveComments rest
  | [] => false

/-- Whether `a` and `b` have the same characters other than whitespace. -/
def sameNonWhitespace : List Char → List Char → Bool
  | c :: a, b => if c.isWhitespace then sameNonWhitespace a b else
    match b.dropWhile Char.isWhitespace with
    | d :: b => c == d && sameNonWhitespace a b
    | [] => false
  | [], b => b.all Char.isWhitespace

/-- Whether `a` and `b` are written the same: whether their `writtenForm`s
agree. Most pairs that a lint compares differ, and are told apart without
computing those forms: `writtenForm` keeps every character of its text but
comments and whitespace, so two texts without comments that have different
characters other than whitespace have different forms. -/
def writtenSame (a b : String) : Bool :=
  let (as, bs) := (a.toList, b.toList)
  if !mayHaveComments as && !mayHaveComments bs && !sameNonWhitespace as bs then false
  else writtenForm a == writtenForm b

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
(`Reqs/Lint/Unused#unused-imports`). A local of `locals` that it hides instead
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

/-! ## Names -/

/-- Whether `module_inception` fires on a module named `name` whose parent
is named `parent`, `""` for a top-level module (`lint::module_inception`). -/
def moduleInception (name parent : String) : Bool := name == parent

/-- `module_inception` for the module at `path`, if its last segment repeats
its parent's. -/
def moduleInceptionMsg? (path : Name) : Option Msg :=
  match path.components.reverse with
  | n :: p :: _ =>
    if moduleInception (nameText n) (nameText p) then
      some { code? := some Lint.moduleInception.code
             headline := s!"module `{showPath path}` has the same name as its parent"
             label? := some s!"inside `{nameText p}`"
             notes := #["note: every path to it, or to an item in it, repeats the name",
               s!"help: rename it, or declare its items in `{showPath path.getPrefix}`"] }
    else none
  | _ => none

/-- Whether `enum_variant_names` fires on an enumeration of `nVariants`
variants, each of two or more words, all of which start, or end, with the
same word (`lint::enum_variant_names`). -/
def enumVariantNames (nVariants : Nat) (sharedFirst sharedLast : Bool) : Bool :=
  nVariants ≥ 2 && (sharedFirst || sharedLast)

/-- The word that each of the variants has first, or last, if each has two
or more words. -/
def sharedWord? (variants : Array Name) (last : Bool) : Option String :=
  let ws := variants.map (words ∘ nameText)
  let pick := fun (w : List String) => if last then w.getLast? else w.head?
  match ws[0]? with
  | some w0 => if ws.any (·.length < 2) then none else
    match pick w0 with
    | some w => if ws.all (pick · == some w) then some w else none
    | none => none
  | none => none

/-- `enum_variant_names` for the enumeration `n` of `variants`, if they share
a first or a last word. -/
def enumVariantNamesMsg? (n : Name) (variants : Array Name) : Option Msg :=
  let first? := sharedWord? variants false
  let last? := sharedWord? variants true
  if !enumVariantNames variants.size first?.isSome last?.isSome then none else
  let what := match first?, last? with
    | some f, some l => s!"starts with `{f}` and ends with `{l}`"
    | some f, none => s!"starts with `{f}`"
    | none, some l => s!"ends with `{l}`"
    | none, none => ""
  let ws := first?.toList ++ last?.toList
  some { code? := some Lint.enumVariantNames.code, headline := s!"every variant of `{nameText n}` {what}"
         label? := some "its variants share a word"
         notes := #[s!"help: remove {" and ".intercalate (ws.map (s!"`{·}`"))} from each variant's name, or put it in the enumeration's"] }

/-- Whether the words `sub` are consecutive words of `ws`. -/
def containsWords (ws sub : List String) : Bool :=
  (List.range (ws.length + 1)).any fun i => (ws.drop i).take sub.length == sub

/-- Whether `enum_variant_names` fires on a variant of `nWords` words, whose
words contain the `nEnumWords` words of its enumeration's name if
`contains` (`lint::variant_has_enum_name`). -/
def variantHasEnumName (nWords nEnumWords : Nat) (contains : Bool) : Bool := contains && nWords > nEnumWords

/-- `enum_variant_names` for the variant `v` of the enumeration `n`, if it
contains the enumeration's name. -/
def variantNameMsg? (n v : Name) : Option Msg :=
  let ws := words (nameText v)
  let es := words (nameText n)
  if !variantHasEnumName ws.length es.length (containsWords ws es) then none else
  some { code? := some Lint.enumVariantNames.code
         headline := s!"variant `{nameText v}` contains the name of its enumeration `{nameText n}`"
         label? := some s!"contains `{nameText n}`"
         notes := #[s!"note: a path to it names the enumeration already, as `{nameText n}::{nameText v}` does",
           s!"help: remove `{nameText n}` from its name"] }

/-- Whether the characters have a run of three or more uppercase letters. -/
def hasUpperRun (cs : List Char) : Bool :=
  (cs.foldl (fun (run, found) c => if isUpperAscii c then (run + 1, found || run + 1 ≥ 3) else (0, found))
    ((0 : Nat), false)).2

/-- Whether `upper_case_acronyms` fires on a name of `what`
(`lint::upper_case_acronyms`): it is in `CamelCase`, as its case requires,
with a run of three or more uppercase letters. -/
def upperCaseAcronyms (what : Named) (s : String) : Bool :=
  what.case == .camel && nameInCase s .camel && hasUpperRun s.toList

/-- `cs` with each run of three or more uppercase letters in lowercase but
for its first letter, and for its last if a lowercase letter follows it,
which starts the next word: `HTTPStatus` becomes `HttpStatus`. -/
def lowerUpperRuns (cs : List Char) : List Char :=
  let rec go : List Char → List Char → List Char
    | run, [] => flush run false
    | run, c :: rest =>
      if isUpperAscii c then go (run ++ [c]) rest
      else flush run (isLowerAscii c) ++ c :: go [] rest
  termination_by _ cs => cs.length
  go [] cs
where
  /-- A run of uppercase letters, followed by a lowercase letter if `lower`. -/
  flush (run : List Char) (lower : Bool) : List Char :=
    if run.length < 3 then run else
    match run with
    | [] => []
    | c :: rest =>
      if lower then c :: (rest.dropLast.map Char.toLower ++ rest.getLast?.toList)
      else c :: rest.map Char.toLower

def upperCaseAcronymsMsg (what : Named) (s : String) : Msg :=
  let fixed := String.ofList (lowerUpperRuns s.toList)
  { code? := some Lint.upperCaseAcronyms.code, headline := s!"{what.describe} `{s}` has an acronym in upper case"
    label? := some "three or more uppercase letters in a row"
    notes := #["note: in `CamelCase`, an acronym is a word, with only its first letter in upper case"]
    fixes := #[{ msg := s!"rename it to `{fixed}`", replacement := fixed }] }

/-- Whether `just_underscores_and_digits` fires on the name `s`
(`lint::just_underscores_and_digits`): without a final `?`, it is made of
`_` and digits, and is not the wildcard `_`. -/
def justUnderscoresAndDigits (s : String) : Bool :=
  let b := baseName s
  s != "_" && !b.isEmpty && b.all fun c => c == '_' || c.isDigit

def justUnderscoresAndDigitsMsg (what : Named) (s : String) : Msg :=
  { code? := some Lint.justUnderscoresAndDigits.code
    headline := s!"{what.describe} `{s}` is named only with `_` and digits"
    label? := some "says nothing of what it is"
    notes := #["help: give it a name that says what it is"] }

/-- The names that are placeholders (`lint::disallowed_names`), in lower
case. -/
def disallowedNames : List String := ["foo", "baz", "quux"]

/-- Whether `disallowed_names` fires on the name `s`
(`lint::disallowed_names`): without a final `?`, it is a placeholder, in
any case. -/
def disallowedName (s : String) : Bool := disallowedNames.contains (baseName s).toLower

def disallowedNameMsg (what : Named) (s : String) : Msg :=
  { code? := some Lint.disallowedNames.code, headline := s!"{what.describe} `{s}` has a placeholder name"
    label? := some "a placeholder"
    notes := #["help: give it a name that says what it is"] }

/-- Whether `min_ident_chars` fires on the name `s`
(`lint::min_ident_chars`): without a final `?`, it is one character, other
than `_`. -/
def minIdentChars (s : String) : Bool :=
  let b := baseName s
  b.length == 1 && b != "_"

def minIdentCharsMsg (what : Named) (s : String) : Msg :=
  { code? := some Lint.minIdentChars.code, headline := s!"{what.describe} `{s}` has a name of one character"
    label? := some "too short to say what it is"
    notes := #["help: give it a name that says what it is"] }

/-- The lints about a declared name alone: its case
(`lint::naming_case`), and the lints of the `style` and `restriction`
groups that look only at the name. -/
def nameMsgs (what : Named) (n : Name) : Array (Lint × Msg) :=
  let s := nameText n
  (namingMsg? what n).toArray
    ++ (if upperCaseAcronyms what s then #[(.upperCaseAcronyms, upperCaseAcronymsMsg what s)] else #[])
    ++ (if justUnderscoresAndDigits s then #[(.justUnderscoresAndDigits, justUnderscoresAndDigitsMsg what s)] else #[])
    ++ (if disallowedName s then #[(.disallowedNames, disallowedNameMsg what s)] else #[])
    ++ (if minIdentChars s then #[(.minIdentChars, minIdentCharsMsg what s)] else #[])

/-- Whether a declared name of `what` is an item's, which a path from
outside its module reaches through the module's name. -/
def Named.isItem : Named → Bool
  | .module | .component | .function | .global | .enumeration | .record | .abstractType | .constant => true
  | _ => false

/-- Whether `module_name_repetitions` fires on an item whose name has
`nWords` words, which contain the `nModuleWords` words of its module's last
segment if `contains` (`lint::module_name_repetitions`). -/
def moduleNameRepetitions (nWords nModuleWords : Nat) (contains : Bool) : Bool := contains && nWords > nModuleWords

/-- `module_name_repetitions` for the item `n` of `what`, declared in the
module `mod`, if its words contain those of the module's last segment, in
any case. -/
def moduleNameMsg? (what : Named) (mod n : Name) : Option Msg := do
  guard what.isItem
  let .str _ m := mod | none
  let ws := (words (nameText n)).map String.toLower
  let ms := (words m).map String.toLower
  guard (moduleNameRepetitions ws.length ms.length (containsWords ws ms))
  some { code? := some Lint.moduleNameRepetitions.code
         headline := s!"{what.describe} `{nameText n}` contains the name of its module `{showPath mod}`"
         label? := some s!"contains `{m}`"
         notes := #[s!"note: a path to it names the module already, as `{m}::{nameText n}` does",
           s!"help: remove `{m}` from its name"] }

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
such as a function's arguments, which no operator lint relates. A pattern
test, `e is P`, has its scrutinee as its operand, and binds as a
comparison. A chained comparison of `ops` operators binds as a comparison,
and its operands are each in a comparison's operand slot, but the rules do
not look inside it. -/
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
  | chain (ops : Nat)
  | atom
  deriving Inhabited, BEq, Repr

/-- The binary operators (`Reqs/Lang/Expressions#operators`). -/
def binaryOps : Array String :=
  #["iff", "or", "and", "=", "!=", "<", "<=", ">", ">=", "in", "subset", "+", "-", "++", "union", "minus", "*", "div",
    "mod", "inter", "join"]

/-- Whether the text of an expression ends in an *open-ended* form: a
conditional, a `when` or an `unless` that is not in parentheses, brackets
or braces, whose last operand extends as far right as possible
(`Reqs/Lint#fixing-lints`). Such a form starts at the first of these
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
      if depth == 0 && ["if", "when", "unless"].contains w then return true
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
  | .when _ | .ite => 0
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
  -- Its scrutinee, the left operand of a comparison.
  | k@.patternTest => #[some ⟨k.prec, k.assoc, false⟩]
  -- Each operand after the first is on the right of a comparison.
  | k@(.chain ops) => #[some ⟨k.prec, k.assoc, false⟩] ++ Array.replicate ops (some ⟨k.prec, k.assoc, true⟩)
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
    | .method _ | .patternTest | .chain _ | .atom => .atom 0

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
  -- Each body's form once, not once for each group it is compared with.
  let forms := arms.map (writtenForm ·.body.text)
  let mut groups : Array (Array Nat) := #[]
  for a in arms, i in [0:arms.size] do
    let fires (g : Array Nat) :=
      let b := arms[g[0]!]!
      sameArmsFires (forms[g[0]!]! == forms[i]!) (b.binds || a.binds)
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
is, for the body that replaces it, and `followed` whether an operator
follows it (`BText.inSlot`). -/
def sameArmsMsg (arms : Array ArmInfo) (g : Array Nat) (slot : Option Slot) (followed : Bool) : Nat × Msg :=
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
    | .replace => s!"help: replace the `match` with its body, `{first.body.inSlot slot followed}`"
  let notes := so ++ (if fix == .replace then #["note: every arm of the `match` has this body"] else #[]) ++ #[help]
  (removed[0]!, { code? := some Lint.matchSameArms.code, headline, label? := some "the same body", notes })

/-- The edits that fix `match_same_arms` in a `match` written at `range`,
where `slot` is and `followed` whether an operator follows it, given each
arm's range, its pattern's and its body's, with the parentheses around it. An arm that the fixes remove is removed
with the `,` between it and a kept arm. -/
def sameArmsEdits (range : Range) (arms : Array ArmInfo) (armRanges patRanges bodyRanges : Array Range)
    (slot : Option Slot) (followed : Bool) : Array (Range × String) := Id.run do
  let groups := sameArmGroups arms
  if let some g := groups.find? (groupFix arms · == .replace) then
    -- The body of the first arm, without what is around it.
    let b := arms[g[0]!]!.body
    let bare := b.inSlot slot followed == b.text
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

/-- The pattern of a variant whose path is `segs` and whose payload has `n`
values: `E::V`, or `E::V(_, _)` with one `_` for each. -/
def variantPattern (segs : Array Name) (n : Nat) : String :=
  "::".intercalate (segs.map toString).toList ++ (if n == 0 then "" else s!"({", ".intercalate (List.replicate n "_")})")

/-- A `_` arm that covers only the variant `v`, with the pattern that names
it, if one resolves. -/
def wildcardMsg (v : Name) (pattern? : Option String) : Msg :=
  { code? := some Lint.wildcardSingleVariant.code, headline := s!"`_` matches only `{showPath v}`"
    label? := some "matches one variant"
    notes := #[s!"note: named, a variant added later makes the `match` non-exhaustive, an error, rather than matched by `_`"]
    fixes := pattern?.toArray.map fun p => { msg := "name the variant", replacement := p } }

/-- Whether `wildcard_enum_match_arm` fires on an arm, if it is `_`, and
whether it has a fix, from the number of variants it matches that no
pattern names (`lint::wildcard_enum_match_arm`). -/
def wildcardEnumMatchArm (wildcard : Bool) (nUnnamed : Nat) : Bool × Bool := (wildcard, wildcard && nUnnamed == 0)

/-- A `_` arm that matches the variants `vs`, with the or-pattern that
names them, if each has a pattern that resolves. -/
def wildcardEnumMsg (vs : Array Name) (pattern? : Option String) : Msg :=
  { code? := some Lint.wildcardEnumMatchArm.code, headline := s!"`_` matches {proseList (vs.map showPath)}"
    label? := some "matches every variant that no other arm names"
    notes := #["note: a variant added later is matched by `_` too, without notice"]
    fixes := pattern?.toArray.map fun p =>
      { msg := if vs.size == 1 then "name the variant" else "name the variants", replacement := p } }

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

/-- The kind of a constraint or a global expectation (`lint::ConstraintKind`). -/
inductive ConstraintKind where
  | assume
  | req
  | expect
  deriving Inhabited, BEq, DecidableEq, Repr

def ConstraintKind.keyword : ConstraintKind → String
  | .assume => "assume"
  | .req => "req"
  | .expect => "expect"

/-- Whether `duplicate_constraint` fires on a constraint, from whether it is
written the same as an earlier one, and whether its fix removes it, from
their kinds (`lint::duplicate_constraint`). -/
def duplicateConstraint (earlier later : ConstraintKind) (same : Bool) : Bool × Bool :=
  (same, same && earlier == later)

/-- For each constraint written the same as an earlier one, from their
texts in order, its position and that of the first such
(`lint::duplicate_constraint`). -/
def repeatedConstraints (texts : Array String) : Array (Nat × Nat) :=
  let forms := texts.map writtenForm
  (Array.range forms.size).filterMap fun i => ((Array.range i).find? (forms[·]! == forms[i]!)).map (i, ·)

/-- A constraint of kind `later`, written the same as the earlier `name`, of
kind `earlier`. When the two are of one kind, the fix removes the later. -/
def duplicateConstraintMsg (earlier later : ConstraintKind) (name : String) : Msg :=
  let notes := if earlier == later then #["help: remove it"]
    else if later == .expect then
      #[s!"note: an `expect` that repeats a `{earlier.keyword}` tests nothing",
        "help: the expectation was probably meant to say something stronger"]
    else #["note: one of them is probably not the constraint meant"]
  { code? := some Lint.duplicateConstraint.code, headline := s!"this is written the same as `{name}`"
    label? := some s!"the same as `{name}`", notes }

/-! ## Invisible characters -/

/-- Whether `invisible_characters` reports the character whose code point is
`n`, in a comment if `comment`, or else in a string literal: a
bidirectional control or U+FEFF anywhere, and a zero-width or invisible
character in a literal (`lint::invisible_character`). -/
def invisibleCode (comment : Bool) (n : Nat) : Bool :=
  (0x202A ≤ n && n ≤ 0x202E) || (0x2066 ≤ n && n ≤ 0x2069) || n == 0xFEFF
    || (!comment && (n == 0x00AD || n == 0x200B || n == 0x2060))

/-- `U+XXXX`, the code point of `c`. -/
def codePoint (c : Char) : String :=
  let h := (String.ofList (Nat.toDigits 16 c.toNat)).toUpper
  "U+" ++ String.ofList (List.replicate (4 - min 4 h.length) '0') ++ h

/-- The name of a character that `invisible_characters` reports. -/
def invisibleName (c : Char) : String :=
  match c.toNat with
  | 0x00AD => "soft hyphen"
  | 0x200B => "zero width space"
  | 0x2060 => "word joiner"
  | 0x202A => "left-to-right embedding"
  | 0x202B => "right-to-left embedding"
  | 0x202C => "pop directional formatting"
  | 0x202D => "left-to-right override"
  | 0x202E => "right-to-left override"
  | 0x2066 => "left-to-right isolate"
  | 0x2067 => "right-to-left isolate"
  | 0x2068 => "first strong isolate"
  | 0x2069 => "pop directional isolate"
  | _ => "zero width no-break space"

/-- The escape of `c` in a string literal, `\uXXXX`. -/
def unicodeEscape (c : Char) : String := "\\u" ++ (codePoint c).drop 2

/-- The text between the quotes of the raw string literal written `t`,
`r"..."` or `r#"..."#`, or `none` if it is not raw. -/
def rawBody? (t : String) : Option String :=
  if t.startsWith "r" then
    -- The body is between the first `"` and the last.
    some ((t.drop 1).toString.dropWhile (· == '#') |>.toString.drop 1 |>.toString.dropEndWhile (· == '#')
      |>.toString.dropEnd 1 |>.toString)
  else none

/-- The string literal written `t`, with each character for which `esc`
holds written as an escape. A raw literal, which has no escapes, becomes an
ordinary one, with `\\` and `\"` for its `\` and `"`. -/
def escapedLiteral (esc : Char → Bool) (t : String) : String :=
  let escape (c : Char) := if esc c then unicodeEscape c else c.toString
  match rawBody? t with
  | some cs =>
    "\"" ++ String.join (cs.toList.map fun c => if c == '\\' then "\\\\" else if c == '"' then "\\\"" else escape c)
      ++ "\""
  | none => String.join (t.toList.map escape)

/-- `invisible_characters` on a comment, if `comment`, or a string literal,
written `t`: the characters it reports, and `t` with each removed from a
comment or written as an escape in a literal. A raw literal, which has no
escapes, becomes an ordinary one. `none` if it reports none. -/
def invisibleFix? (comment : Bool) (t : String) : Option (Array Char × String) := do
  let found := t.toList.toArray.filter (invisibleCode comment ·.toNat)
  guard !found.isEmpty
  if comment then return (found, String.ofList (t.toList.filter (!invisibleCode comment ·.toNat)))
  return (found, escapedLiteral (invisibleCode false ·.toNat) t)

/-- A comment, if `comment`, or a string literal, with the characters
`found`, whose fix is `fixed`. -/
def invisibleMsg (comment : Bool) (found : Array Char) (fixed : String) : Msg :=
  let distinct := found.foldl (init := #[]) fun acc c => if acc.contains c then acc else acc.push c
  let names := distinct.map fun c => s!"`{codePoint c}` ({invisibleName c})"
  let what := if comment then "comment" else "string literal"
  let headline := if distinct.size == 1 then s!"this {what} contains an invisible character, {names[0]!}"
    else s!"this {what} contains invisible characters: {", ".intercalate names.toList}"
  let control := distinct.any (invisibleCode true ·.toNat)
  let notes := if control then #["note: a bidirectional control can make the text read differently from what it means"]
    else #["note: it cannot be seen, so it is probably not meant"]
  let msg := if comment then (if found.size == 1 then "remove it" else "remove them")
    else if found.size == 1 then "write it as an escape" else "write them as escapes"
  { code? := some Lint.invisibleCharacters.code, headline, label? := some (if control then "may not read as it is written" else "contains what cannot be seen")
    notes, fixes := #[{ msg, replacement := fixed }] }

/-! ## Restricted literals -/

/-- Whether `needless_raw_strings` fires on a string literal, if it is
`raw`, from whether its contents have a `\` or a `"`
(`lint::needless_raw_strings`). -/
def needlessRawStrings (raw backslash quote : Bool) : Bool := raw && !backslash && !quote

/-- A raw string literal that needs no escapes, whose fix is `fixed`. -/
def needlessRawMsg (fixed : String) : Msg :=
  { code? := some Lint.needlessRawStrings.code, headline := "this raw string literal needs no escapes"
    label? := some "has no `\\` and no `\"`"
    notes := #["note: an ordinary literal of the same characters has the same value"]
    fixes := #[{ msg := "write it as an ordinary literal", replacement := fixed }] }

/-- Whether `non_ascii_literal` reports the character whose code point is
`n`, and whether an escape can write it (`lint::non_ascii_literal`). -/
def nonAscii (n : Nat) : Bool × Bool := (n ≥ 0x80, n ≤ 0xFFFF)

/-- A string literal with the non-ASCII characters `found`, whose fix, if
an escape can write each, is `fixed?`. -/
def nonAsciiMsg (found : Array Char) (fixed? : Option String) : Msg :=
  let distinct := found.foldl (init := #[]) fun acc c => if acc.contains c then acc else acc.push c
  let names := distinct.map fun c => s!"`{codePoint c}`"
  let headline := if distinct.size == 1 then s!"this string literal contains a non-ASCII character, {names[0]!}"
    else s!"this string literal contains non-ASCII characters: {", ".intercalate names.toList}"
  let beyond := distinct.filter fun c => !(nonAscii c.toNat).2
  let notes := if beyond.isEmpty then #[] else
    #[s!"note: {proseList (beyond.map codePoint)} {if beyond.size == 1 then "is" else "are"} beyond `U+FFFF`, which `\\uHHHH` cannot write, so this has no fix"]
  let msg := if found.size == 1 then "write it as an escape" else "write them as escapes"
  { code? := some Lint.nonAsciiLiteral.code, headline, label? := some "not ASCII", notes
    fixes := fixed?.toArray.map fun replacement => { msg, replacement } }

/-- The lints of the `restriction` group on the string literal written
`t`: `needless_raw_strings` and `non_ascii_literal`. -/
def literalMsgs (t : String) : Array (Lint × Msg) :=
  let raw := match rawBody? t with
    | some body =>
      if needlessRawStrings true (body.contains '\\') (body.contains '"') then
        #[(.needlessRawStrings, needlessRawMsg ("\"" ++ body ++ "\""))]
      else #[]
    | none => #[]
  let reported (c : Char) := (nonAscii c.toNat).1
  let found := t.toList.toArray.filter reported
  let fixed? := if found.all fun c => (nonAscii c.toNat).2 then some (escapedLiteral reported t) else none
  raw ++ if found.isEmpty then #[] else #[(.nonAsciiLiteral, nonAsciiMsg found fixed?)]

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

/-- Whether `x OP k` bounds `x` from below (`lint::disjoint`). -/
def Comparison.boundsBelow (c : Comparison) : Bool := c matches .eq | .gt | .ge

/-- Whether `x OP k` bounds `x` from above (`lint::disjoint`). -/
def Comparison.boundsAbove (c : Comparison) : Bool := c matches .eq | .lt | .le

/-- The least integer `x` with `x OP k`, if `OP` bounds it from below. -/
def Comparison.least (c : Comparison) (k : Int) : Int := if c matches .gt then k + 1 else k

/-- The greatest integer `x` with `x OP k`, if `OP` bounds it from above. -/
def Comparison.greatest (c : Comparison) (k : Int) : Int := if c matches .lt then k - 1 else k

/-- Whether no integer `x` has both `x OP₁ a` and `x OP₂ b`
(`lint::disjoint`). -/
def disjointBounds (c1 : Comparison) (a : Int) (c2 : Comparison) (b : Int) : Bool :=
  (c1.boundsBelow && c2.boundsAbove && c1.least a > c2.greatest b)
    || (c2.boundsBelow && c1.boundsAbove && c2.least b > c1.greatest a)
    || (a == b && ((c1, c2) matches (.eq, .ne) | (.ne, .eq)))

/-- Whether `contradictory_comparisons` fires on `x OP₁ a and x OP₂ b`, or
`or` if not `conj`, of integers (`lint::contradictory_comparisons`): under
`and`, no `x` has both; under `or`, none has neither. -/
def contradictoryComparisons (conj : Bool) (c1 : Comparison) (a : Int) (c2 : Comparison) (b : Int) : Bool :=
  if conj then disjointBounds c1 a c2 b else disjointBounds c1.complement a c2.complement b

/-- Whether `contradictory_comparisons` fires on `x OP₁ a and x OP₂ b`, or
`or` if not `conj`, where `a` and `b` are not integers, from whether they
are distinct (`lint::contradictory_equalities`). -/
def contradictoryEqualities (conj : Bool) (c1 c2 : Comparison) (distinct : Bool) : Bool :=
  distinct && if conj then (c1, c2) matches (.eq, .eq) else (c1, c2) matches (.ne, .ne)

/-- `x OP₁ a and x OP₂ b`, or `or` if not `conj`, that is always `false`,
or `true`. -/
def contradictoryMsg (conj : Bool) : Msg :=
  { code? := some Lint.contradictoryComparisons.code
    headline := if conj then "these two comparisons cannot both hold" else "one of these two comparisons always holds"
    label? := some s!"always `{!conj}`"
    notes := #["note: `and` and `or` may be swapped, or a value may not be the one meant"] }

/-- Whether `redundant_comparisons` fires on `x OP₁ a and x OP₂ b`, or `or`
if not `conj`, of integers, and whether the fix keeps the first comparison,
rather than the second (`lint::redundant_comparisons`): under `and` the one
that implies the other, under `or` the one that the other implies. -/
def redundantComparisons (conj : Bool) (c1 : Comparison) (a : Int) (c2 : Comparison) (b : Int) : Bool × Bool :=
  let firstImplies := disjointBounds c1 a c2.complement b
  let secondImplies := disjointBounds c2 b c1.complement a
  (firstImplies || secondImplies, if conj then firstImplies else secondImplies)

/-- `x OP₁ a and x OP₂ b`, or `or`, as the text of the comparison kept. -/
def redundantComparisonsMsg (fixed : String) : Msg :=
  { code? := some Lint.redundantComparisons.code, headline := s!"these two comparisons are `{fixed}`"
    label? := some "one comparison implies the other"
    fixes := #[{ msg := "remove the comparison that adds nothing", replacement := fixed }] }

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

/-- A search written with `index_of`, `slice` or `at`, as the text of the
call of `method` that it is. -/
def manualMethodMsg (method fixed label : String) : Msg :=
  { code? := some Lint.manualMethod.code, headline := s!"this is a call of `{method}`", label? := some label
    fixes := #[{ msg := s!"call `{method}`", replacement := fixed }] }

/-- `s.at(0) = ""`, or `!=`, as the text of the collection compared with
`empty`, `""` or `[]` (`lint::first_empty`). -/
def firstEmptyMsg (fixed empty : String) : Msg :=
  { code? := some Lint.lengthZero.code, headline := s!"say whether it is empty with `{empty}`, not `at`"
    label? := some s!"compares the first {if empty == "[]" then "element" else "character"} with `{empty}`"
    fixes := #[{ msg := s!"compare with `{empty}`", replacement := fixed }] }

/-- `s.slice(0, s.len)`, as the text of `s`. -/
def redundantSlicingMsg (fixed : String) : Msg :=
  { code? := some Lint.redundantSlicing.code, headline := "this slice is the whole of its receiver"
    label? := some "from the start, as long as the receiver"
    fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

/-- `s.replace(a, a)`, or `replace_all`, as the text of `s`. -/
def noEffectReplaceMsg (method fixed : String) : Msg :=
  { code? := some Lint.noEffectReplace.code, headline := s!"this `{method}` has no effect"
    label? := some "replaces with what it replaces"
    notes := #["note: the two arguments are written the same"]
    fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

/-- `a OP b` on integers. -/
def Comparison.compares : Comparison → Int → Int → Bool
  | .eq, a, b => a == b
  | .ne, a, b => a != b
  | .lt, a, b => a < b
  | .le, a, b => a ≤ b
  | .gt, a, b => a > b
  | .ge, a, b => a ≥ b

/-- Whether `const_is_empty` fires on a comparison of the length of a
literal of `n` characters or elements with `bound`, `n OP bound` if
`lengthLeft` and `bound OP n` otherwise, where `set` says that it is a set's
or relation's, whose `card` may be fewer; and what the comparison always is
(`lint::const_is_empty`). -/
def constIsEmpty (op : Comparison) (bound : Int) (lengthLeft set : Bool) (n : Nat) : Bool × Bool :=
  let (emptiness, empty) := lengthZero op bound lengthLeft
  (!set || emptiness,
    if set then empty == (n == 0) else if lengthLeft then op.compares n bound else op.compares bound n)

/-- Whether `const_is_empty` fires on `a = E` or `a != E`, where `E` is
empty and `a` a literal of `n` characters or elements, and what it always
is (`lint::const_empty_equation`). -/
def constEmptyEquation (equal : Bool) (n : Nat) : Bool × Bool := (n > 0, equal == (n == 0))

/-- A test of a literal that is always `value`. -/
def constIsEmptyMsg (value : Bool) : Msg :=
  { code? := some Lint.constIsEmpty.code, headline := s!"this test of a literal is always `{value}`"
    label? := some "the literal's length is fixed"
    notes := #["note: the literal is probably not the one meant"] }

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

/-- Whether `erasing_op` fires on `a OP b`, where `same` says that `a` and
`b` are written the same, which `eq_op` reports for `inter` and `minus`
(`lint::erasing_op`). -/
def erasingOp (op : InfixOp) (left right : IdentityOperand) (same : Bool) : Bool :=
  match op, same with
  | .inter, true | .minus, true => false
  | .mul, _ => (left matches .zero) || (right matches .zero)
  | .inter, _ | .join, _ => (left matches .empty) || (right matches .empty)
  | .minus, _ => (left matches .empty)
  | _, _ => false

/-- `a OP b`, which is always `0` if `zero`, and `{}` otherwise. -/
def erasingOpMsg (op : InfixOp) (zero : Bool) : Msg :=
  { code? := some Lint.erasingOp.code, headline := s!"this `{op.op}` is always `{if zero then "0" else "{}"}`"
    label? := some "ignores its other operand"
    notes := #["note: the literal is probably not the operand meant"] }

/-- Whether `ifs_same_cond` fires on a test of a chain of `else if`, from
whether an earlier test of the chain is written the same
(`lint::ifs_same_cond`). -/
def ifsSameCond (earlier : Bool) : Bool := earlier

/-- A test of a chain of `else if`, written the same as the earlier
`test`. -/
def ifsSameCondMsg (test : String) : Msg :=
  { code? := some Lint.ifsSameCond.code, headline := s!"`{test}` is already tested earlier in this chain"
    label? := some "the same as an earlier test"
    notes := #[s!"note: this branch is never taken: wherever `{test}` holds, the earlier branch is taken",
      "note: one of the tests is probably not the one meant"] }

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

/-- A comparison of a length with `bound`, where `recv` is the collection,
without the parentheses around it, and `empty` the text of an empty one,
such as `""`, `[]` or `{}`. The fix puts `recv` in parentheses where it
needs them, as the left operand of `=` or `!=`. -/
def lengthZeroMsg (card : Bool) (recv : BText) (empty : String) (isEmpty : Bool) (bound : Int) : Msg :=
  let m := if card then "card" else "len"
  let fixed := (binText (if isEmpty then "=" else "!=") recv { text := empty, prec := BKind.atom.prec }).text
  { code? := some (if card then "F0716" else "F0715"), headline := s!"say whether it is empty with `{empty}`, not `{m}`"
    label? := some s!"compares a length with {bound}"
    fixes := #[{ msg := s!"compare with `{empty}`", replacement := fixed }] }

/-- The text of `t`, which replaces `n`, in `slot` within `parent`: in
parentheses if it needs them there and `n` is not already in them. -/
def placed (src : Array Char) (n : BNode α) (slot : Option Slot) (parent : Range) (t : BText) : String :=
  if enclosed src parent n.range then t.text else t.inSlot slot (followedAt src n.range)

/-- The comparison `n` is, with its operands' texts as `writtenForm` gives them. -/
def comparisonOf? (src : Array Char) (n : BNode α) : Option (Comparison × String × String) := do
  let .bin op := n.kind | none
  let #[a, b] := n.kids | none
  let c ← Comparison.ofOp? op
  return (c, writtenForm (textOf src a.range), writtenForm (textOf src b.range))

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
      unless conj && writtenForm (textOf src c.range) == writtenForm (textOf src b.range)
        && writtenForm (textOf src d.range) == writtenForm (textOf src a.range) do none
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
  | .atom | .neg => (writtenForm (textOf src n.range)).toInt?
  | _ => none

/-- Whether `k` is written `e.len` or `(e).len`, where `o` is the text of
`e` without whitespace. -/
def isLenOf (src : Array Char) (o : String) (k : BNode α) : Bool :=
  let t := writtenForm (textOf src k.range)
  t == o ++ ".len" || t == s!"({o}).len"

/-- Whether `k` is a literal of one character, or a sequence literal of one
element. -/
def oneElement (src : Array Char) (k : BNode α) : Bool :=
  let t := textOf src k.range
  ((Lean.Syntax.decodeStrLit t).any (·.length == 1)) ||
    (k.kind == .atom && t.startsWith "[" && t.endsWith "]" && k.kids.size == 1)

/-- `manual_method` on `n`, a comparison in `slot` within `parent`
(`lint::index_test`, `lint::one_character`). -/
def manualMethodAt? (src : Array Char) (n : BNode α) (slot : Option Slot) (parent : Range) : Option (OpReport α) := do
  let .bin op := n.kind | none
  let c ← Comparison.ofOp? op
  let #[a, b] := n.kids | none
  -- The call, the other operand, and the comparison with the call on the left.
  let (call, other, c) := if a.kind matches .method _ then (a, b, c) else (b, a, c.mirror)
  let .method m := call.kind | none
  let recv ← call.kids[0]?
  let r := operandText src call.range recv
  let report (method fixed : String) (prec : Nat) (label : String) : OpReport α :=
    let fixed := placed src n slot parent { text := fixed, prec }
    { lint := .manualMethod, ref := n.ref, msg := manualMethodMsg method fixed label }
  -- `s.at(0) = t` and `s.at(s.len - 1) = t`, where `t` has one character.
  if m == "at" then
    let #[_, i] := call.kids | none
    unless (c == .eq || c == .ne) && oneElement src other do none
    let o := writtenForm (textOf src recv.range)
    let last := match i.kind, i.kids with
      | .bin "-", #[l, one] => writtenForm (textOf src one.range) == "1" && isLenOf src o l
      | _, _ => false
    let method ← if writtenForm (textOf src i.range) == "0" then some "starts_with?" else if last then some "ends_with?" else none
    let call := s!"{r}.{method}({textOf src other.range})"
    let label := if last then "compares the last element" else "compares the first element"
    return if c == .eq then report method call (BKind.method "").prec label
      else report method s!"not {call}" BKind.not.prec label
  let #[_, x, y] := call.kids | none
  if m == "index_of" then
    unless writtenForm (textOf src y.range) == "0" do none
    let t := textOf src x.range
    match indexTest c (← intLiteral? src other) with
    | .found => return report "contains?" s!"{r}.contains?({t})" (BKind.method "").prec "compares a position"
    | .absent => return report "contains?" s!"not {r}.contains?({t})" BKind.not.prec "compares a position"
    | .atStart => return report "starts_with?" s!"{r}.starts_with?({t})" (BKind.method "").prec "compares a position"
    | .other => none
  -- `s.slice(0, t.len) = t`.
  unless m == "slice" && c == .eq && writtenForm (textOf src x.range) == "0" do none
  unless isLenOf src (writtenForm (textOf src other.range)) y do none
  return report "starts_with?" s!"{r}.starts_with?({textOf src other.range})" (BKind.method "").prec "compares a prefix"

/-- `length_zero` on `n`, `s.at(0) = ""` or `q.at(0) = []`, or `!=`, in
`slot` within `parent` (`lint::first_empty`). -/
def firstEmptyAt? (src : Array Char) (n : BNode α) (slot : Option Slot) (parent : Range) : Option (OpReport α) := do
  let .bin op := n.kind | none
  unless op == "=" || op == "!=" do none
  let #[a, b] := n.kids | none
  let (call, other) := if a.kind matches .method _ then (a, b) else (b, a)
  let .method m := call.kind | none
  let #[recv, i] := call.kids | none
  let empty := writtenForm (textOf src other.range)
  unless m == "at" && writtenForm (textOf src i.range) == "0" && (empty == "\"\"" || empty == "[]") do none
  let fixed := placed src n slot parent (binText op (recv.text src) { text := empty, prec := BKind.atom.prec })
  return { lint := .lengthZero, ref := n.ref, msg := firstEmptyMsg fixed empty }

/-- Whether `redundant_slicing` fires on `s.slice(i, n)`, from whether it is
written `s.slice(0, s.len)`, the receivers written the same
(`lint::redundant_slicing`). -/
def redundantSlicing (whole : Bool) : Bool := whole

/-- Whether `no_effect_replace` fires on `s.replace(a, b)` or
`s.replace_all(a, b)`, from whether `a` and `b` are written the same
(`lint::no_effect_replace`). -/
def noEffectReplace (same : Bool) : Bool := same

/-- `manual_method` on `s.slice(i, 1)`, `redundant_slicing` on `s.slice(0,
s.len)`, and `no_effect_replace` on `s.replace(a, a)` and
`s.replace_all(a, a)`, where `n` is the call, in `slot` within `parent`
(`lint::one_character`, `lint::redundant_slicing`,
`lint::no_effect_replace`). -/
def methodCallAt? (src : Array Char) (n : BNode α) (slot : Option Slot) (parent : Range) : Option (OpReport α) := do
  let .method m := n.kind | none
  let recv ← n.kids[0]?
  let receiver := placed src n slot parent (recv.text src)
  match m, n.kids with
  | "slice", #[_, i, k] =>
    if writtenForm (textOf src k.range) == "1" then
      let fixed := s!"{operandText src n.range recv}.at({textOf src i.range})"
      return { lint := .manualMethod, ref := n.ref, msg := manualMethodMsg "at" fixed "a slice of length 1" }
    unless redundantSlicing (writtenForm (textOf src i.range) == "0" && isLenOf src (writtenForm (textOf src recv.range)) k) do none
    return { lint := .redundantSlicing, ref := n.ref, msg := redundantSlicingMsg receiver }
  | "replace", #[_, a, b] | "replace_all", #[_, a, b] =>
    unless noEffectReplace (writtenSame (textOf src a.range) (textOf src b.range)) do none
    return { lint := .noEffectReplace, ref := n.ref, msg := noEffectReplaceMsg m receiver }
  | _, _ => none

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
  match k.kind, writtenForm (textOf src k.range) with
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

/-- Whether `needless_bool_assign` fires on `if C then A else B`, and
whether its fix is `C != X`, rather than `C iff X`, where `elseNegates`
says that `B` is `not X`, for an `X` written the same as `A`, and
`thenNegates` that `A` is `not X`, for an `X` written the same as `B`
(`lint::needless_bool_assign`). -/
def needlessBoolAssign (elseNegates thenNegates : Bool) : Bool × Bool := (elseNegates || thenNegates, !elseNegates)

/-- `if C then X else not X`, or `if C then not X else X` if `unequal`,
where `x` is the text of `X`, as the text of its fix. -/
def needlessBoolAssignMsg (x fixed : String) (unequal : Bool) : Msg :=
  { code? := some Lint.needlessBoolAssign.code, headline := "this `if` gives a `Bool` or its negation"
    label? := some (if unequal then s!"the negation of `{x}` if the condition holds, and `{x}` otherwise"
      else s!"`{x}` if the condition holds, and its negation otherwise")
    fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

/-- `needless_bool_assign` on `n`, a conditional in `slot` within `parent`
(`lint::needless_bool_assign`). -/
def needlessBoolAssignAt? (src : Array Char) (n : BNode α) (slot : Option Slot) (parent : Range) :
    Option (OpReport α) := do
  let #[c, a, b] := n.kids | none
  -- Whether `k` is `not X`, for an `X` written the same as `x`.
  let negates (k x : BNode α) : Bool := match k.kind, k.kids with
    | .not, #[y] => writtenSame (textOf src y.range) (textOf src x.range)
    | _, _ => false
  let (fires, unequal) := needlessBoolAssign (negates b a) (negates a b)
  unless fires do none
  let x := if unequal then b else a
  let fixed := placed src n slot parent (binText (if unequal then "!=" else "iff") (c.text src) (x.text src))
  return { lint := .needlessBoolAssign, ref := n.ref, msg := needlessBoolAssignMsg (textOf src x.range) fixed unequal }

/-- The binary operators that are punctuators, but `-`, which
`suspicious_unary_op_formatting` looks at: `-` is never directly followed
by a `-`, which would start a comment, and `<` never is, since `<-` is
one punctuator. -/
def punctuatorOps : Array String := #["=", "!=", "<=", ">", ">=", "+", "++", "*"]

/-- Whether `suspicious_unary_op_formatting` fires on `a OP -b`, from
whether `OP` is a punctuator other than `-`, the `-` follows it directly,
and whitespace follows the `-` (`lint::suspicious_unary_op_formatting`). -/
def suspiciousUnaryOp (punctuator adjacent spaced : Bool) : Bool := punctuator && adjacent && spaced

def suspiciousUnaryOpMsg (op fixed : String) : Msg :=
  { code? := some Lint.suspiciousUnaryOpFormatting.code, headline := s!"`{op}-` looks like one operator"
    label? := some s!"`{op}`, then a negation"
    notes := #[s!"note: there is no operator `{op}-`: this is `{op}`, whose right operand is negated"]
    fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

/-- `suspicious_unary_op_formatting` on `n`, a binary operator
(`lint::suspicious_unary_op_formatting`). The fix moves the whitespace
after the `-` to before it, but keeps a space after it before a `-`,
which would start a comment. -/
def suspiciousUnaryAt? (src : Array Char) (n : BNode α) : Option (OpReport α) := do
  let .bin op := n.kind | none
  let #[_, b] := n.kids | none
  let .neg := b.kind | none
  let #[y] := b.kids | none
  let m := b.range.start
  let adjacent := m ≥ op.length && textOf src { start := m - op.length, stop := m } == op
  let spaced := src[m + 1]?.any Char.isWhitespace
  unless suspiciousUnaryOp (punctuatorOps.contains op) adjacent spaced do none
  let operand := textOf src { start := (withParensIn src b.range y.range).start, stop := n.range.stop }
  let neg := if operand.startsWith "-" then s!"- {operand}" else s!"-{operand}"
  let fixed := textOf src { start := n.range.start, stop := m } ++ " " ++ neg
  return { lint := .suspiciousUnaryOpFormatting, ref := n.ref, msg := suspiciousUnaryOpMsg op fixed }

/-- Whether `k`, the first operand of `n`, an atom, is its receiver: `n`
reads a field of it, or indexes it. -/
def isReceiverOf (src : Array Char) (n k : BNode α) : Bool := Id.run do
  let r := withParensIn src n.range k.range
  let mut i := r.stop
  while i < n.range.stop && src[i]!.isWhitespace do i := i + 1
  return r.start == n.range.start && (src[i]? == some '.' || src[i]? == some '[')

/-- A value that `contradictory_comparisons` compares with: an integer, a
string or a `Bool` literal, or a variant without a payload, by its path. -/
inductive ConstOperand where
  | int (k : Int)
  | str (s : String)
  | bool (b : Bool)
  | variant (v : String)
  deriving Inhabited, BEq

/-- Whether `a` and `b`, neither an integer, are distinct values: two string
literals written differently, without escape sequences, two `Bool`
literals, or two variants. -/
def ConstOperand.distinct : ConstOperand → ConstOperand → Bool
  | .str s, .str t => s != t && !s.contains '\\' && !t.contains '\\'
  | .bool b, .bool c => b != c
  | .variant v, .variant w => v != w
  | _, _ => false

/-- The value that `n` is written as, if it is a literal or, by `variant?`,
a variant without a payload. -/
def constOperand? (src : Array Char) (variant? : α → Option String) (n : BNode α) : Option ConstOperand :=
  let t := textOf src n.range
  match n.kind, intLiteral? src n with
  | .lit b, _ => some (.bool b)
  | _, some k => some (.int k)
  | .atom, none =>
    if t.length ≥ 2 && t.startsWith "\"" && t.endsWith "\"" && t.toList.count '"' == 2 then some (.str t)
    else (variant? n.ref).map .variant
  | _, none => none

/-- The comparison `n` is, if one operand is a value that `constOperand?`
sees, the right one if both are: the other operand's text, the comparison
with that operand on the left, and the value. -/
def constComparison? (src : Array Char) (variant? : α → Option String) (n : BNode α) :
    Option (String × Comparison × ConstOperand) := do
  let .bin op := n.kind | none
  let c ← Comparison.ofOp? op
  let #[a, b] := n.kids | none
  match constOperand? src variant? b with
  | some k => return (textOf src a.range, c, k)
  | none => return (textOf src b.range, c.mirror, ← constOperand? src variant? a)

/-- `contradictory_comparisons` on `n`, an `and` or an `or`
(`lint::contradictory_comparisons`, `lint::contradictory_equalities`). -/
def contradictoryAt? (src : Array Char) (variant? : α → Option String) (n : BNode α) (conj : Bool) :
    Option (OpReport α) := do
  let #[l, r] := n.kids | none
  let (x1, c1, k1) ← constComparison? src variant? l
  let (x2, c2, k2) ← constComparison? src variant? r
  unless writtenSame x1 x2 do none
  let fires := match k1, k2 with
    | .int a, .int b => contradictoryComparisons conj c1 a c2 b
    | .int _, _ | _, .int _ => false
    | _, _ => contradictoryEqualities conj c1 c2 (k1.distinct k2)
  unless fires do none
  return { lint := .contradictoryComparisons, ref := n.ref, msg := contradictoryMsg conj }

/-- `redundant_comparisons` on `n`, an `and` or an `or`, in `slot` within
`parent` (`lint::redundant_comparisons`). Two comparisons written the same
are left to `eq_op`. -/
def redundantAt? (src : Array Char) (n : BNode α) (slot : Option Slot) (parent : Range) (conj : Bool) :
    Option (OpReport α) := do
  let #[l, r] := n.kids | none
  let (x1, c1, .int a) ← constComparison? src (fun _ => none) l | none
  let (x2, c2, .int b) ← constComparison? src (fun _ => none) r | none
  unless writtenForm x1 == writtenForm x2 && !writtenSame (textOf src l.range) (textOf src r.range) do none
  let (true, keepFirst) := redundantComparisons conj c1 a c2 b | none
  let fixed := placed src n slot parent ((if keepFirst then l else r).text src)
  return { lint := .redundantComparisons, ref := n.ref, msg := redundantComparisonsMsg fixed }

/-- `erasing_op` on `n`, a binary operator (`lint::erasing_op`). -/
def erasingOpAt? (src : Array Char) (n : BNode α) : Option (OpReport α) := do
  let .bin op := n.kind | none
  let o ← InfixOp.ofOp? op
  let #[a, b] := n.kids | none
  let same := writtenSame (textOf src a.range) (textOf src b.range)
  unless erasingOp o (identityOperand src a) (identityOperand src b) same do none
  return { lint := .erasingOp, ref := n.ref, msg := erasingOpMsg o (o == .mul) }

/-- Whether `precedence` fires on an operand of `outer` whose outermost
operator is `inner`, if it is not `parenthesized` (`lint::precedence`). -/
def precedenceFires (outer inner : InfixOp) (parenthesized : Bool) : Bool :=
  !parenthesized && ((outer == .or && inner == .and)
    || ((outer == .union || outer == .minus) && (inner == .inter || inner == .join)))

/-- An operand `t` of `outer`, whose outermost operator is `inner`,
written without the parentheses that its precedence implies. -/
def precedenceMsg (outer inner t : String) : Msg :=
  { code? := some Lint.precedence.code, headline := s!"`{inner}` is an operand of `{outer}` without parentheses"
    label? := some s!"binds more tightly than `{outer}`"
    notes := #[s!"note: `{inner}` binds more tightly than `{outer}`, so this is `({t})` already"]
    fixes := #[{ msg := "add the parentheses, which keep the meaning", replacement := s!"({t})" }] }

/-- `precedence` on the operands of `n`. -/
def precedenceAt (src : Array Char) (n : BNode α) : Array (OpReport α) :=
  match n.kind with
  | .bin op => match InfixOp.ofOp? op with
    | some o => n.kids.filterMap fun k => do
      let .bin iop := k.kind | none
      let i ← InfixOp.ofOp? iop
      unless precedenceFires o i (enclosed src n.range k.range) do none
      return { lint := .precedence, ref := k.ref, msg := precedenceMsg op iop (textOf src k.range) }
    | none => #[]
  | _ => #[]

/-- The tests of the chain of `else if` that starts at `n`, in order. -/
partial def ifTests (n : BNode α) : Array (BNode α) :=
  match n.kind, n.kids with
  | .ite, #[c, _, e] => #[c] ++ ifTests e
  | _, _ => #[]

/-- `ifs_same_cond` on the chain of `else if` that starts at `n`
(`lint::ifs_same_cond`): at each test written the same as an earlier
one, naming the first. -/
def ifsSameCondAt (src : Array Char) (n : BNode α) : Array (OpReport α) :=
  let tests := ifTests n
  let texts := tests.map fun t => textOf src t.range
  tests.zipIdx.filterMap fun (t, i) => do
    let earlier := (texts.extract 0 i).find? (writtenSame · texts[i]!)
    unless ifsSameCond earlier.isSome do none
    return { lint := .ifsSameCond, ref := t.ref, msg := ifsSameCondMsg (earlier.getD "") }

/-- The messages of the operator and method lints in `n`, which is in
`slot` within `parent`, outermost first, where `inElse` says that `n` is
the `else` branch of a conditional. -/
partial def opReportsIn (src : Array Char) (boolEq : α → Bool) (variant? : α → Option String) (n : BNode α)
    (slot : Option Slot) (parent : Range) (inElse : Bool := false) : Array (OpReport α) :=
  let slots := n.kind.slots
  let own := match n.kind with
    | .bin op =>
      let operands := (n.kids.zip slots).filterMap fun (k, s) => s.bind (elseExtendsAt? src n k ·)
      (if op == "and" || op == "or" then
          (doubleComparisonAt? src n slot parent (op == "and")).toArray
            ++ (contradictoryAt? src variant? n (op == "and")).toArray
            ++ (redundantAt? src n slot parent (op == "and")).toArray
        else #[])
        ++ (boolEqualityAt? src boolEq n slot parent).toArray ++ (manualMethodAt? src n slot parent).toArray
        ++ (identityOpAt? src n slot parent).toArray ++ (suspiciousUnaryAt? src n).toArray
        ++ (erasingOpAt? src n).toArray ++ (firstEmptyAt? src n slot parent).toArray ++ operands
        ++ precedenceAt src n
    | .ite => (needlessBoolAssignAt? src n slot parent).toArray ++ (if inElse then #[] else ifsSameCondAt src n)
    | .method _ => (methodCallAt? src n slot parent).toArray
    | _ => #[]
  -- A receiver needs parentheses as an operand does.
  let slots := match n.kind, n.kids[0]? with
    | .method _, _ => #[some receiverSlot]
    | .atom, some k => if isReceiverOf src n k then #[some receiverSlot] else slots
    | _, _ => slots
  own ++ (n.kids.mapIdx fun i k =>
    opReportsIn src boolEq variant? k (slots[i]?.join) n.range (n.kind == .ite && i == 2)).flatten

/-- The messages of the operator and method lints in an expression written
in `src` (`Reqs/Lint/Complexity/Comparisons`), where `boolEq` says whether a
comparison compares `Bool`s, and `variant?` which variant without a payload a
path is, if it is one. -/
def opReports (src : Array Char) (boolEq : α → Bool) (variant? : α → Option String) (root : BNode α) :
    Array (OpReport α) :=
  opReportsIn (upTo src root.range) boolEq variant? root none root.range

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
  let place (t : BText) : String := if enclosed src parent range then t.text else t.inSlot slot (followedAt src range)
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
  (shapeReports (upTo src range) root none range).qsort fun a b =>
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

/-- A literal of the pattern `p` that replaces `orig`: raw, with the same
delimiters, if `orig` is raw and `p` has no `"`, and otherwise with the
escapes that a literal needs. -/
def patternLiteral (orig p : String) : String :=
  if orig.startsWith "r" && !p.toList.contains '"' then
    let pre := orig.toList.takeWhile (· != '"')
    String.ofList pre ++ "\"" ++ p ++ "\"" ++ String.ofList (pre.drop 1)
  else p.quote

/-- The character that `cs`, an alternative of a pattern, matches, if it is
one character that is not special, or `\` and a special one. -/
def patternChar? : List Char → Option Char
  | ['\\', c] => if reSpecials.contains c then some c else none
  | [c] => if reSpecials.contains c && c != '-' then none else some c
  | _ => none

/-- Whether `manual_pattern_char_comparison` fires on an alternation of `n`
alternatives, from whether each is one character
(`lint::manual_pattern_char_comparison`). -/
def manualPatternCharComparison (n : Nat) (single : Bool) : Bool := n ≥ 2 && single

/-- `c` as an item of a class: `\`, `]`, `^` and `-` escaped
(`lint::class_char`). -/
def classCharText (c : Char) : String := if ['\\', ']', '^', '-'].contains c then "\\" ++ c.toString else c.toString

/-- The position after the class whose `[` is at `i` in `cs`, a pattern
that parses. -/
partial def classEnd (cs : Array Char) (i : Nat) : Nat :=
  let rec go (j : Nat) : Nat :=
    match cs[j]? with
    | none => j
    | some ']' => j + 1
    | some '\\' => go (j + 2)
    | some _ => go (j + 1)
  go (if cs[i + 1]? == some '^' then i + 2 else i + 1)

mutual
/-- The alternative of `cs` from `i` up to `|`, `)` or the end, with each
alternation of single characters in it written as a class: its text, its
text as written, and the position after it. -/
partial def charClassSeq (cs : Array Char) (i : Nat) (out : String := "") (raw : List Char := []) :
    String × List Char × Nat :=
  match cs[i]? with
  | none | some '|' | some ')' => (out, raw, i)
  | some '\\' =>
    let t := (cs.extract i (i + 2)).toList
    charClassSeq cs (i + 2) (out ++ String.ofList t) (raw ++ t)
  | some '[' =>
    let j := classEnd cs i
    let t := (cs.extract i j).toList
    charClassSeq cs j (out ++ String.ofList t) (raw ++ t)
  | some '(' =>
    let (t, j, cls) := charClassAlt cs (i + 1)
    let t := if cls then t else "(" ++ t ++ ")"
    charClassSeq cs (j + 1) (out ++ t) (raw ++ (cs.extract i (j + 1)).toList)
  | some c => charClassSeq cs (i + 1) (out.push c) (raw ++ [c])

/-- The alternation of `cs` from `i` up to `)` or the end, rewritten: its
text, the position after it, and whether it is a class. -/
partial def charClassAlt (cs : Array Char) (i : Nat) (parts : Array (String × List Char) := #[]) :
    String × Nat × Bool :=
  let (t, raw, j) := charClassSeq cs i
  let parts := parts.push (t, raw)
  if cs[j]? == some '|' then charClassAlt cs (j + 1) parts else
  let chars := parts.filterMap (patternChar? ·.2)
  if manualPatternCharComparison parts.size (chars.size == parts.size) then
    ("[" ++ String.join (chars.toList.map classCharText) ++ "]", j, true)
  else ("|".intercalate (parts.toList.map (·.1)), j, false)
end

/-- The pattern `p`, which parses, with each alternation of single
characters written as a class, if it has one
(`lint::manual_pattern_char_comparison`). -/
def charClassPattern? (p : String) : Option String :=
  let (t, _, _) := charClassAlt p.toList.toArray 0
  if t == p then none else some t

def manualPatternCharComparisonMsg (fixed : String) : Msg :=
  { code? := some Lint.manualPatternCharComparison.code, headline := "this alternation of single characters is a class"
    label? := some "matches one of several characters"
    notes := #["note: a class, such as `[abc]`, matches one character of those in it"]
    fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

/-- Whether `almost_complete_range` fires on the range `low-high`, from the
code points of its ends, and the range of the fix
(`lint::almost_complete_range`). -/
def almostCompleteRange (low high : Int) : Bool × Int × Int :=
  let fires := ([97, 98, 65, 66].contains low && high == low + 24) || (low == 48 && high == 56)
  (fires, if fires && (low == 98 || low == 66) then low - 1 else low,
    if fires && (high == 121 || high == 89 || high == 56) then high + 1 else high)

/-- The character of a class at `i` in `cs`, which `\` may escape: the
character, its text, and the position after it. -/
def classCharAt (cs : Array Char) (i : Nat) : Char × String × Nat :=
  if cs[i]? == some '\\' then (cs[i + 1]?.getD ' ', String.ofList (cs.extract i (i + 2)).toList, i + 2)
  else (cs[i]?.getD ' ', (cs[i]?.getD ' ').toString, i + 1)

/-- The items of the class from `i` in `cs`, a pattern that parses, after
its `[` and `^`, with each range that `almost_complete_range` fires on
completed: their text, the ranges completed, and the position after the
class. -/
partial def completeClass (cs : Array Char) (i : Nat) (out : String) (found : Array (String × String)) :
    String × Array (String × String) × Nat :=
  match cs[i]? with
  | none => (out, found, i)
  | some ']' => (out.push ']', found, i + 1)
  | _ =>
    let (lo, loText, j) := classCharAt cs i
    if cs[j]? == some '-' && cs[j + 1]? != some ']' && (cs[j + 1]?).isSome then
      let (hi, hiText, k) := classCharAt cs (j + 1)
      let (fires, wlo, whi) := almostCompleteRange lo.toNat hi.toNat
      if fires then
        let whole := s!"{Char.ofNat wlo.toNat}-{Char.ofNat whi.toNat}"
        completeClass cs k (out ++ whole) (found.push (s!"{loText}-{hiText}", whole))
      else completeClass cs k (out ++ loText ++ "-" ++ hiText) found
    else completeClass cs j (out ++ loText) found

/-- The pattern `p` from `i`, with each range that `almost_complete_range`
fires on completed, and those ranges, as written and completed. -/
partial def completeRanges (cs : Array Char) (i : Nat) (out : String := "") (found : Array (String × String) := #[]) :
    String × Array (String × String) :=
  match cs[i]? with
  | none => (out, found)
  | some '\\' => completeRanges cs (i + 2) (out ++ String.ofList (cs.extract i (i + 2)).toList) found
  | some '[' =>
    let neg := cs[i + 1]? == some '^'
    let (t, found, j) := completeClass cs (if neg then i + 2 else i + 1) (if neg then "[^" else "[") found
    completeRanges cs j (out ++ t) found
  | some c => completeRanges cs (i + 1) (out.push c) found

/-- The pattern `p`, which parses, with each range that
`almost_complete_range` fires on completed, and those ranges, as written
and completed, if there is one. -/
def completeRangesPattern? (p : String) : Option (String × Array (String × String)) :=
  let (t, found) := completeRanges p.toList.toArray 0
  if found.isEmpty then none else some (t, found)

def almostCompleteRangeMsg (found : Array (String × String)) (fixed : String) : Msg :=
  let (r, whole) := found[0]!
  { code? := some Lint.almostCompleteRange.code
    headline := if found.size == 1 then s!"the range `{r}` is one character short of `{whole}`"
      else "these ranges are each one character short of a whole alphabet"
    label? := some (if found.size == 1 then s!"`{r}` leaves out one character" else "ranges that leave out one character")
    notes := #["note: a range is from its first character to its last, both included"]
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

/-! ## Names and sizes -/

/-- Whether `zero_sized_map_values` fires on `Rel(A, B)`, where `B` is an
enumeration of `nVariants` if `enum`, of which some has a payload if
`payload` (`lint::zero_sized_map_values`). -/
def zeroSizedMapValues (enum : Bool) (nVariants : Nat) (payload : Bool) : Bool :=
  enum && nVariants == 1 && !payload

/-- `Rel(a, b)`, where `v` is the one variant of `b`. -/
def zeroSizedMapValuesMsg (a b v : String) : Msg :=
  { code? := some "F0789", headline := s!"`Rel({a}, {b})` relates to `{b}`, which has one value"
    label? := some s!"`{b}` has only `{b}::{v}`"
    notes := #[s!"note: such a relation says only which `{a}`s it relates, as a set does",
      s!"help: write `Set({a})`"] }

/-- `a`, `b` and `c`. -/
def andList (xs : Array String) : String :=
  match xs.toList.reverse with
  | last :: rest@(_ :: _) => s!"{", ".intercalate rest.reverse} and {last}"
  | _ => ", ".intercalate xs.toList

/-- Whether a declared name has one character, not counting a final `?`. -/
def singleChar (n : Name) : Bool := (baseName (nameText n)).length == 1

/-- Whether `many_single_char_names` fires on an item that declares `n`
distinct single-character names (`lint::many_single_char_names`): more
than 4, as Clippy's threshold is. -/
def manySingleCharNames (n : Nat) : Bool := n ≥ 5

/-- The `what` named `n` declares the single-character `names`. -/
def manySingleCharNamesMsg (what : Named) (n : Name) (names : Array Name) : Msg :=
  { code? := some "F0795", headline := s!"{what.describe} `{nameText n}` declares {names.size} single-character names"
    label? := some "too many to tell apart"
    notes := #[s!"note: they are {andList (names.map (s!"`{nameText ·}`"))}",
      "help: name them for what they stand for"] }

/-- If one of `a` and `b` is the other with one character substituted,
inserted or deleted, the characters that differ, and whether one character
is substituted for another that are each a word of their names, between
`_`s or the name's ends. They differ in what is left of each once their
longest common prefix and then their longest common suffix are removed,
if neither has more than one character left, and they are not equal. -/
def oneEdit? (a b : List Char) : Option (List Char × Bool) :=
  let p := ((a.zip b).takeWhile fun (x, y) => x == y).length
  let (a', b') := (a.drop p, b.drop p)
  let s := ((a'.reverse.zip b'.reverse).takeWhile fun (x, y) => x == y).length
  let (ra, rb) := (a'.take (a'.length - s), b'.take (b'.length - s))
  let word := ra.length == 1 && rb.length == 1 && (p == 0 || a[p - 1]? == some '_')
    && (p + 1 == a.length || a[p + 1]? == some '_')
  if ra.length ≤ 1 && rb.length ≤ 1 && !(ra.isEmpty && rb.isEmpty) then some (ra ++ rb, word) else none

/-- Whether `similar_names` fires on two names of `lenA` and `lenB`
characters, without a final `?`, one of which is the other with one
character substituted, inserted or deleted if `oneEdit`, where the
characters that differ are digits if `digits`, and words of their own if
`word`, and the pair is one of `similarAllowed` if `allowed`
(`lint::similar_names`). -/
def similarNames (lenA lenB : Nat) (oneEdit digits word allowed : Bool) : Bool :=
  lenA ≥ 3 && lenB ≥ 3 && oneEdit && !digits && !word && !allowed

/-- The pairs of names that Clippy allows to be similar, of those that
apply to Fren. -/
def similarAllowed : List (String × String) := [
  -- keep-sorted start
  ("args", "arms"),
  ("lhs", "rhs"),
  ("lit", "lint"),
  ("set", "get"),
  -- keep-sorted end
]

/-- `similarNames` of two declared names. -/
def namesSimilar (a b : Name) : Bool :=
  let (a, b) := (baseName (nameText a), baseName (nameText b))
  let d? := oneEdit? a.toList b.toList
  let allowed := similarAllowed.any fun (x, y) => (a == x && b == y) || (a == y && b == x)
  similarNames a.length b.length d?.isSome (d?.any (·.1.all Char.isDigit)) (d?.any (·.2)) allowed

/-- `b`, declared after `a` in the `what` named `n`. -/
def similarNamesMsg (a b : Name) (what : Named) (n : Name) : Msg :=
  { code? := some "F0796", headline := s!"`{nameText b}` differs from `{nameText a}` by one character"
    label? := some "easily mistaken for the other"
    notes := #[s!"note: both are declared in {what.describe} `{nameText n}`",
      "help: rename one, so that they differ at a glance"] }

/-- The lines of `text` that have something other than whitespace and
comments: `--` to the end of the line, and `/-` to `-/`, which nest. A
`--` in a string literal starts no comment. -/
def codeLines (text : String) : Nat := Id.run do
  let cs := text.toList.toArray
  let mut n := 0
  let mut code := false
  let mut depth := 0
  let mut inString := false
  let mut i := 0
  while i < cs.size do
    let c := cs[i]!
    let next := cs[i + 1]?
    if c == '\n' then
      if code then n := n + 1
      code := false
      inString := false
      i := i + 1
    else if depth > 0 then
      if c == '-' && next == some '/' then depth := depth - 1; i := i + 2
      else if c == '/' && next == some '-' then depth := depth + 1; i := i + 2
      else i := i + 1
    else if inString then
      if c == '\\' then i := i + 2
      else
        if c == '"' then inString := false
        i := i + 1
    else if c == '-' && next == some '-' then
      while i < cs.size && cs[i]! != '\n' do i := i + 1
    else if c == '/' && next == some '-' then depth := 1; i := i + 2
    else
      if c == '"' then inString := true
      unless c.isWhitespace do code := true
      i := i + 1
  return if code then n + 1 else n

/-- Whether `too_many_lines` fires on an item of `n` lines of code
(`lint::too_many_lines`). -/
def tooManyLines (n : Nat) : Bool := n > 100

/-- The `what` named `n`, of `lines` lines of code. -/
def tooManyLinesMsg (what : Named) (n : Name) (lines : Nat) : Msg :=
  { code? := some "F0797", headline := s!"{what.describe} `{nameText n}` has {lines} lines"
    label? := some "longer than 100 lines"
    notes := #["note: blank lines and comments are not counted",
      if what == .function then "help: move parts of it into smaller functions, and apply them"
      else "help: move parts of it into smaller components, and make them its instances"] }

/-- Whether an arm that matches one variant gives it back, where
`sameVariant` says that its body builds that variant, `binders` are the
texts of the pattern's binders, `_` included, and `args` those of the
body's arguments: the binders, in order, none of them `_`
(`lint::needless_match`). -/
def givesBack (sameVariant : Bool) (binders args : Array String) : Bool :=
  sameVariant && binders.size == args.size && (binders.zip args).all fun (b, a) => b != "_" && writtenSame b a

/-- Whether `needless_match` fires on a `match`, from whether each arm but
`_` gives back the variant it matches, there is a `_` arm, its body is
written the same as the scrutinee, and `trivial_match` fires on it
(`lint::needless_match`). -/
def needlessMatch (givenBack wildcard scrutineeBack trivial : Bool) : Bool :=
  givenBack && (!wildcard || scrutineeBack) && !trivial

/-- A `match` that gives back its scrutinee, whose text, as the fix writes
it, is `fixed`. -/
def needlessMatchMsg (fixed : String) : Msg :=
  { code? := some Lint.needlessMatch.code, headline := "this `match` gives back its scrutinee"
    label? := some "each arm gives back the value it matches"
    fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

/-- Whether `assertions_on_constants` fires on a constraint, where
`mentions` is whether its expression mentions a variable or an
uninterpreted function (`lint::assertions_on_constants`). -/
def assertionOnConstant (mentions : Bool) : Bool := !mentions

/-- A constraint, an `assume`, `req` or `expect`, or a cover goal, that mentions no
variable, where `literal?` is its value if it is written `true` or
`false`. -/
def assertionOnConstantMsg (kind : String) (literal? : Option Bool) : Msg :=
  let what := match kind with
    | "assume" => "assumption"
    | "req" => "requirement"
    | "cover" => "cover goal"
    | _ => "expectation"
  let (label, note) := match literal?, kind with
    | some true, "assume" => ("always `true`", "it rules out no input")
    | some true, "req" => ("always `true`", "it constrains nothing")
    | some true, _ => ("always `true`", "it claims nothing")
    | some false, "assume" => ("always `false`", "no input meets it, so every requirement holds vacuously")
    | some false, "req" => ("always `false`", "no behaviour meets it, so the component is not realizable")
    | some false, _ => ("always `false`", "it always fails")
    | none, _ => ("the same in every behaviour",
      "it is either always true, and says nothing, or always false")
  { code? := some Lint.assertionsOnConstants.code, headline := s!"this {what} mentions no variable"
    label? := some label, notes := #[s!"note: {note}"] }

/-! ## Restricted settings and paths -/

/-- Whether `allow_attributes` fires on a `set_option` of a lint or group
to `requested`, and whether its fix applies, from whether the setting is
of `unfulfilled_lint_expectations` itself (`lint::allow_attributes`). -/
def allowAttributes (requested : LintLevel) (unfulfilled : Bool) : Bool × Bool :=
  (requested == .allow, requested == .allow && !unfulfilled)

/-- A `set_option` of `t` to `"allow"`, fixed to `"expect"` if `fixable`. -/
def allowAttributesMsg (t : LintTarget) (fixable : Bool) : Msg :=
  { code? := some Lint.allowAttributes.code, headline := s!"`{t.name}` is allowed rather than expected"
    label? := some "`allow`"
    notes := #[s!"note: `\"expect\"` silences {if t matches .group _ then "its lints" else "it"} too, and `unfulfilled_lint_expectations` reports the setting once nothing needs it"]
      ++ (if fixable then #[] else #["note: for `unfulfilled_lint_expectations`, `\"expect\"` means `\"allow\"`, so it is never fulfilled"])
    fixes := if fixable then #[{ msg := "expect it instead", replacement := "\"expect\"" }] else #[] }

/-- Whether `absolute_paths` fires on a path of `nSegments` segments, in an
expression, pattern or type, to an item or a variant
(`lint::absolute_paths`). -/
def absolutePath (nSegments : Nat) : Bool := nSegments ≥ 3

/-- `absolute_paths` for the path `segs` to `r`, if it is long. -/
def absolutePathMsg? (segs : Array Name) (r : Resolved) : Option Msg := do
  guard (absolutePath segs.size)
  let (target, rest) := match r with
    | .variant en idx => (en.path, s!"{en.path.getString!}::{nameText en.variants[idx]!}")
    | .item i => (i.path, i.path.getString!)
  some { code? := some Lint.absolutePaths.code
         headline := s!"`{"::".intercalate (segs.map nameText).toList}` is a path of {segs.size} segments"
         label? := some "a long path"
         notes := #[s!"help: import it with `use {showPath target}`, and write `{rest}`"] }

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
