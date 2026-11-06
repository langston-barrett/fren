-- keep-sorted start
import FrenCore.Ctors
import FrenCore.Diagnostic
-- keep-sorted end

/-!
# Lint names, groups and levels

Part of `FrenCore.Lint`, shared by both front ends.
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
  -- keep-sorted start
  | absolutePaths
  | absurdExtremeComparisons
  | allowAttributes
  | almostCompleteRange
  | arbitrarySourceItemOrdering
  | assertionsOnConstants
  | boolEquality
  | branchesSharingCode
  | cardZero
  | caseSplitGuarantees
  | chainableComparison
  | collapsibleMatch
  | collapsibleWhen
  | constIsEmpty
  | constantOutput
  | contractMentionsNothing
  | contradictoryComparisons
  | deadCode
  | definableOutput
  | disallowedNames
  | doubleComparison
  | doubleNeg
  | doubleParens
  | duplicateConstraint
  | duplicateElements
  | duplicateScrutinee
  | elseExtends
  | emptyArgument
  | enumVariantNames
  | eqOp
  | erasingOp
  | fnParamsExcessiveBools
  | globImports
  | identityOp
  | ifChainMatch
  | ifNotElse
  | ifsSameCond
  | inconsistentStructConstructor
  | indexAfterUse
  | intPlusOne
  | invalidUpcastComparisons
  | invisibleCharacters
  | irrefutableIs
  | isEquality
  | justUnderscoresAndDigits
  | lengthZero
  | letAndReturn
  | literalDotInPattern
  | manualAbs
  | manualAbsDiff
  | manualAtMostOne
  | manualClamp
  | manualForall
  | manualMethod
  | manualMinMax
  | manualNat
  | manualOrdering
  | manualPatternCharComparison
  | manualPatternTest
  | manualRangePatterns
  | manualRecordUpdate
  | manualRemEuclid
  | manualTable
  | manySingleCharNames
  | matchArmIfElse
  | matchBool
  | matchCouldBeTable
  | matchLikeMembership
  | matchOverlappingArm
  | matchSameArms
  | membershipChain
  | minIdentChars
  | minMax
  | moduleInception
  | moduleNameRepetitions
  | moduloOne
  | needlessBoolAssign
  | needlessHigherOrder
  | needlessMatch
  | needlessRawStringHashes
  | needlessRawStrings
  | needlessUpdate
  | negMultiply
  | negativePosition
  | noEffectReplace
  | nonAsciiLiteral
  | nonCamelCaseTypes
  | nonSnakeCase
  | nonUpperCaseConstants
  | nonminimalBool
  | overlyComplexBoolExpr
  | precedence
  | procWithoutOutputs
  | redundantBindings
  | redundantBoolType
  | redundantClosure
  | redundantComparisons
  | redundantGuards
  | redundantLocals
  | redundantMethodChain
  | redundantNewtypeRoundtrip
  | redundantSlicing
  | redundantTypeAnnotations
  | sameBranches
  | similarNames
  | singleCallFn
  | singleMatchElse
  | singletonMembership
  | structExcessiveBools
  | structFieldNames
  | suspiciousUnaryOpFormatting
  | tooManyLines
  | trivialCover
  | trivialGuard
  | trivialMatch
  | trivialPattern
  | trivialQuantifier
  | undecidable
  | unfulfilledExpectations
  | unicodeNotNfc
  | unlessNot
  | unnecessaryMinOrMax
  | unnecessaryStructInitialization
  | unnecessaryTrailingComma
  | unnestedOrPatterns
  | unrelatedBinders
  | unusedAssumption
  | unusedImports
  | unusedLintSetting
  | unusedVariables
  | upperCaseAcronyms
  | wildcardEnumMatchArm
  | wildcardInOrPatterns
  | wildcardSingleVariant
  | zeroPrefixedLiteral
  | zeroSizedMapValues
  -- keep-sorted end
  -- `BEq` from `DecidableEq`, which makes it lawful at once; a derived `BEq`
  -- would need a proof over every pair of lints.
  deriving Inhabited, DecidableEq, Repr

/-- Every lint, in the order of `Lint`'s constructors, which is by name. -/
def Lint.all : Array Lint := ctors% Lint

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

/-- A lint's name, code and group: one line for each lint, kept sorted, so
that lints added at once merge cleanly. (`F0713` was `shadowed_constants`,
which explicit shadowing replaced, `F0217`; it is not reused.) -/
def Lint.info : Lint → String × String × Group
  -- keep-sorted start
  | .absolutePaths => ("absolute_paths", "F0786", .restriction)
  | .absurdExtremeComparisons => ("absurd_extreme_comparisons", "F0763", .suspicious)
  | .allowAttributes => ("allow_attributes", "F0780", .restriction)
  | .almostCompleteRange => ("almost_complete_range", "F0757", .suspicious)
  | .arbitrarySourceItemOrdering => ("arbitrary_source_item_ordering", "F0779", .restriction)
  | .assertionsOnConstants => ("assertions_on_constants", "F0761", .style)
  | .boolEquality => ("bool_equality", "F0731", .pedantic)
  | .branchesSharingCode => ("branches_sharing_code", "F0778", .pedantic)
  | .cardZero => ("card_zero", "F0716", .style)
  | .caseSplitGuarantees => ("case_split_guarantees", "F0729", .pedantic)
  | .chainableComparison => ("chainable_comparison", "F0804", .style)
  | .collapsibleMatch => ("collapsible_match", "F0832", .style)
  | .collapsibleWhen => ("collapsible_when", "F0723", .style)
  | .constIsEmpty => ("const_is_empty", "F0755", .suspicious)
  | .constantOutput => ("constant_output", "F0719", .complexity)
  | .contractMentionsNothing => ("contract_mentions_nothing", "F0845", .suspicious)
  | .contradictoryComparisons => ("contradictory_comparisons", "F0766", .suspicious)
  | .deadCode => ("dead_code", "F0711", .unused)
  | .definableOutput => ("definable_output", "F0720", .pedantic)
  | .disallowedNames => ("disallowed_names", "F0752", .style)
  | .doubleComparison => ("double_comparison", "F0730", .complexity)
  | .doubleNeg => ("double_neg", "F0740", .style)
  | .doubleParens => ("double_parens", "F0739", .complexity)
  | .duplicateConstraint => ("duplicate_constraint", "F0768", .suspicious)
  | .duplicateElements => ("duplicate_elements", "F0738", .suspicious)
  | .duplicateScrutinee => ("duplicate_scrutinee", "F0849", .suspicious)
  | .elseExtends => ("else_extends", "F0733", .complexity)
  | .emptyArgument => ("empty_argument", "F0745", .suspicious)
  | .enumVariantNames => ("enum_variant_names", "F0749", .style)
  | .eqOp => ("eq_op", "F0736", .suspicious)
  | .erasingOp => ("erasing_op", "F0764", .suspicious)
  | .fnParamsExcessiveBools => ("fn_params_excessive_bools", "F0775", .pedantic)
  | .globImports => ("glob_imports", "F0702", .style)
  | .identityOp => ("identity_op", "F0734", .complexity)
  | .ifChainMatch => ("if_chain_match", "F0727", .pedantic)
  | .ifNotElse => ("if_not_else", "F0724", .pedantic)
  | .ifsSameCond => ("ifs_same_cond", "F0765", .suspicious)
  | .inconsistentStructConstructor => ("inconsistent_struct_constructor", "F0772", .pedantic)
  | .indexAfterUse => ("index_after_use", "F0721", .suspicious)
  | .intPlusOne => ("int_plus_one", "F0741", .complexity)
  | .invalidUpcastComparisons => ("invalid_upcast_comparisons", "F0798", .pedantic)
  | .invisibleCharacters => ("invisible_characters", "F0769", .suspicious)
  | .irrefutableIs => ("irrefutable_is", "F0803", .suspicious)
  | .isEquality => ("is_equality", "F0802", .style)
  | .justUnderscoresAndDigits => ("just_underscores_and_digits", "F0751", .style)
  | .lengthZero => ("length_zero", "F0715", .style)
  | .letAndReturn => ("let_and_return", "F0824", .style)
  | .literalDotInPattern => ("literal_dot_in_pattern", "F0794", .suspicious)
  | .manualAbs => ("manual_abs", "F0811", .complexity)
  | .manualAbsDiff => ("manual_abs_diff", "F0812", .complexity)
  | .manualAtMostOne => ("manual_at_most_one", "F0840", .complexity)
  | .manualClamp => ("manual_clamp", "F0814", .complexity)
  | .manualForall => ("manual_forall", "F0826", .style)
  | .manualMethod => ("manual_method", "F0732", .complexity)
  | .manualMinMax => ("manual_min_max", "F0813", .complexity)
  | .manualNat => ("manual_nat", "F0810", .style)
  | .manualOrdering => ("manual_ordering", "F0841", .pedantic)
  | .manualPatternCharComparison => ("manual_pattern_char_comparison", "F0756", .style)
  | .manualPatternTest => ("manual_pattern_test", "F0805", .style)
  | .manualRangePatterns => ("manual_range_patterns", "F0833", .complexity)
  | .manualRecordUpdate => ("manual_record_update", "F0818", .style)
  | .manualRemEuclid => ("manual_rem_euclid", "F0815", .complexity)
  | .manualTable => ("manual_table", "F0838", .pedantic)
  | .manySingleCharNames => ("many_single_char_names", "F0795", .pedantic)
  | .matchArmIfElse => ("match_arm_if_else", "F0808", .style)
  | .matchBool => ("match_bool", "F0837", .pedantic)
  | .matchCouldBeTable => ("match_could_be_table", "F0809", .pedantic)
  | .matchLikeMembership => ("match_like_membership", "F0726", .style)
  | .matchOverlappingArm => ("match_overlapping_arm", "F0835", .style)
  | .matchSameArms => ("match_same_arms", "F0725", .pedantic)
  | .membershipChain => ("membership_chain", "F0718", .pedantic)
  | .minIdentChars => ("min_ident_chars", "F0785", .restriction)
  | .minMax => ("min_max", "F0817", .suspicious)
  | .moduleInception => ("module_inception", "F0748", .style)
  | .moduleNameRepetitions => ("module_name_repetitions", "F0784", .restriction)
  | .moduloOne => ("modulo_one", "F0816", .suspicious)
  | .needlessBoolAssign => ("needless_bool_assign", "F0759", .complexity)
  | .needlessHigherOrder => ("needless_higher_order", "F0823", .pedantic)
  | .needlessMatch => ("needless_match", "F0760", .complexity)
  | .needlessRawStringHashes => ("needless_raw_string_hashes", "F0777", .pedantic)
  | .needlessRawStrings => ("needless_raw_strings", "F0782", .restriction)
  | .needlessUpdate => ("needless_update", "F0819", .complexity)
  | .negMultiply => ("neg_multiply", "F0742", .style)
  | .negativePosition => ("negative_position", "F0770", .suspicious)
  | .noEffectReplace => ("no_effect_replace", "F0754", .suspicious)
  | .nonAsciiLiteral => ("non_ascii_literal", "F0783", .restriction)
  | .nonCamelCaseTypes => ("non_camel_case_types", "F0704", .nonstandardStyle)
  | .nonSnakeCase => ("non_snake_case", "F0703", .nonstandardStyle)
  | .nonUpperCaseConstants => ("non_upper_case_constants", "F0705", .nonstandardStyle)
  | .nonminimalBool => ("nonminimal_bool", "F0712", .complexity)
  | .overlyComplexBoolExpr => ("overly_complex_bool_expr", "F0773", .pedantic)
  | .precedence => ("precedence", "F0787", .restriction)
  | .procWithoutOutputs => ("proc_without_outputs", "F0846", .pedantic)
  | .redundantBindings => ("redundant_bindings", "F0735", .style)
  | .redundantBoolType => ("redundant_bool_type", "F0746", .style)
  | .redundantClosure => ("redundant_closure", "F0821", .style)
  | .redundantComparisons => ("redundant_comparisons", "F0767", .complexity)
  | .redundantGuards => ("redundant_guards", "F0807", .complexity)
  | .redundantLocals => ("redundant_locals", "F0825", .suspicious)
  | .redundantMethodChain => ("redundant_method_chain", "F0743", .complexity)
  | .redundantNewtypeRoundtrip => ("redundant_newtype_roundtrip", "F0842", .complexity)
  | .redundantSlicing => ("redundant_slicing", "F0753", .complexity)
  | .redundantTypeAnnotations => ("redundant_type_annotations", "F0822", .restriction)
  | .sameBranches => ("same_branches", "F0737", .suspicious)
  | .similarNames => ("similar_names", "F0796", .pedantic)
  | .singleCallFn => ("single_call_fn", "F0788", .restriction)
  | .singleMatchElse => ("single_match_else", "F0771", .pedantic)
  | .singletonMembership => ("singleton_membership", "F0717", .complexity)
  | .structExcessiveBools => ("struct_excessive_bools", "F0776", .pedantic)
  | .structFieldNames => ("struct_field_names", "F0774", .pedantic)
  | .suspiciousUnaryOpFormatting => ("suspicious_unary_op_formatting", "F0762", .suspicious)
  | .tooManyLines => ("too_many_lines", "F0797", .pedantic)
  | .trivialCover => ("trivial_cover", "F0820", .suspicious)
  | .trivialGuard => ("trivial_guard", "F0806", .complexity)
  | .trivialMatch => ("trivial_match", "F0747", .complexity)
  | .trivialPattern => ("trivial_pattern", "F0744", .style)
  | .trivialQuantifier => ("trivial_quantifier", "F0827", .complexity)
  | .undecidable => ("undecidable", "F0714", .decidability)
  | .unfulfilledExpectations => ("unfulfilled_lint_expectations", "F0706", .unused)
  | .unicodeNotNfc => ("unicode_not_nfc", "F0799", .pedantic)
  | .unlessNot => ("unless_not", "F0722", .style)
  | .unnecessaryMinOrMax => ("unnecessary_min_or_max", "F0843", .complexity)
  | .unnecessaryStructInitialization => ("unnecessary_struct_initialization", "F0790", .complexity)
  | .unnecessaryTrailingComma => ("unnecessary_trailing_comma", "F0801", .pedantic)
  | .unnestedOrPatterns => ("unnested_or_patterns", "F0836", .pedantic)
  | .unrelatedBinders => ("unrelated_binders", "F0793", .suspicious)
  | .unusedAssumption => ("unused_assumption", "F0792", .unused)
  | .unusedImports => ("unused_imports", "F0701", .unused)
  | .unusedLintSetting => ("unused_lint_setting", "F0791", .unused)
  | .unusedVariables => ("unused_variables", "F0710", .unused)
  | .upperCaseAcronyms => ("upper_case_acronyms", "F0750", .style)
  | .wildcardEnumMatchArm => ("wildcard_enum_match_arm", "F0781", .restriction)
  | .wildcardInOrPatterns => ("wildcard_in_or_patterns", "F0834", .complexity)
  | .wildcardSingleVariant => ("wildcard_single_variant", "F0728", .pedantic)
  | .zeroPrefixedLiteral => ("zero_prefixed_literal", "F0758", .complexity)
  | .zeroSizedMapValues => ("zero_sized_map_values", "F0789", .pedantic)
  -- keep-sorted end

def Lint.name (l : Lint) : String := l.info.1

def Lint.code (l : Lint) : String := l.info.2.1

def Lint.group (l : Lint) : Group := l.info.2.2

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
is no order: `forbid` wins, from its default, its own option or its
group's, as `-F` does on the command line; otherwise the lint's own option
wins over its group's (`lint::outside_options`). -/
def outsideLevel (dflt : LintLevel) (own? group? : Option LintLevel) : LintLevel :=
  if dflt == .forbid || own? == some .forbid || group? == some .forbid then .forbid else
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
  /-- Set by a `set_option` in the file: its index among the file's lint
  settings (`unused_lint_setting`). -/
  setting? : Option Nat := none
  deriving Inhabited, Repr

def LevelInEffect.ofDefault (l : Lint) : LevelInEffect := { level := l.default }

/-- The level that decides what happens: `expect` without an expectation
is `allow`. -/
def LevelInEffect.effective (l : LevelInEffect) : LintLevel :=
  if l.level == .expect && l.expectation?.isNone then .allow else l.level

/-- The levels of every lint at some place. -/
abbrev Levels := Array (Lint × LevelInEffect)

def Levels.defaults : Levels := Lint.all.map fun l => (l, .ofDefault l)

/-- The level of `l` in `ls`. Every `Levels` is built from
`Levels.defaults`, which has one entry per lint, in the order of
`Lint.all`, by `Levels.set`, which keeps that so. `Lint.all` lists the
lints in the order of their constructors, so the entry of `l` is usually
at its constructor's index, where it is looked for first; the search is a
fallback. The answer is that of the search, since `l` has only one entry. -/
def Levels.get (ls : Levels) (l : Lint) : LevelInEffect :=
  match ls[l.ctorIdx]? with
  | some (l', v) => if l' == l then v else slow
  | none => slow
where slow := ((ls.find? (·.1 == l)).map (·.2)).getD (.ofDefault l)

/-- `ls` with `l` at level `v`. It keeps each entry in its place, and adds
one only for a lint that has none, so each lint still has one entry
(`Levels.get`). -/
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

end Fren.Core
