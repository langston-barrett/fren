-- keep-sorted start
import FrenCore.Lexical
import FrenCore.Mentions
import FrenCore.Names
import FrenCore.Nfc
import FrenCore.Patterns
import FrenCore.Regex
import FrenCore.Simplify
import FrenCore.Str
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
  | caseSplitGuarantees
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
  | unnecessaryStructInitialization
  | unusedLintSetting
  | unusedAssumption
  | unrelatedBinders
  | literalDotInPattern
  | invalidUpcastComparisons
  | unicodeNotNfc
  | unnecessaryTrailingComma
  | isEquality
  | irrefutableIs
  | chainableComparison
  | singleMatchElse
  | inconsistentStructConstructor
  | overlyComplexBoolExpr
  | structFieldNames
  | fnParamsExcessiveBools
  | structExcessiveBools
  | needlessRawStringHashes
  | branchesSharingCode
  | zeroPrefixedLiteral
  | arbitrarySourceItemOrdering
  | singleCallFn
  | manualAtMostOne
  | manualOrdering
  | redundantNewtypeRoundtrip
  | unnecessaryMinOrMax
  | manualNat
  | manualAbs
  | manualAbsDiff
  | manualMinMax
  | manualClamp
  | manualRemEuclid
  | moduloOne
  | minMax
  | manualRecordUpdate
  | needlessUpdate
  | trivialCover
  | manualPatternTest
  | collapsibleMatch
  | manualRangePatterns
  | wildcardInOrPatterns
  | matchOverlappingArm
  | unnestedOrPatterns
  | matchBool
  | manualTable
  | letAndReturn
  | redundantLocals
  | manualForall
  | trivialQuantifier
  | matchCouldBeTable
  -- `BEq` from `DecidableEq`, which makes it lawful at once; a derived `BEq`
  -- would need a proof over every pair of lints.
  deriving Inhabited, DecidableEq, Repr

def Lint.all : Array Lint :=
  #[.unusedImports, .globImports, .nonSnakeCase, .nonCamelCaseTypes, .nonUpperCaseConstants, .unfulfilledExpectations,
    .unusedVariables, .deadCode, .nonminimalBool, .undecidable, .lengthZero, .cardZero,
    .singletonMembership, .membershipChain, .constantOutput, .definableOutput, .indexAfterUse, .unlessNot,
    .collapsibleWhen, .ifNotElse, .matchSameArms, .matchLikeMembership, .wildcardSingleVariant, .ifChainMatch,
    .caseSplitGuarantees, .redundantBindings, .eqOp, .sameBranches, .duplicateElements, .emptyArgument, .doubleComparison,
    .boolEquality, .manualMethod, .elseExtends, .identityOp, .doubleParens, .doubleNeg, .intPlusOne, .negMultiply,
    .redundantMethodChain, .trivialPattern, .redundantBoolType, .trivialMatch,
    .zeroSizedMapValues, .manySingleCharNames, .similarNames, .tooManyLines, .moduleInception, .enumVariantNames,
    .upperCaseAcronyms, .justUnderscoresAndDigits, .disallowedNames, .needlessBoolAssign, .needlessMatch,
    .assertionsOnConstants, .suspiciousUnaryOpFormatting, .redundantSlicing, .noEffectReplace, .constIsEmpty,
    .manualPatternCharComparison, .almostCompleteRange, .duplicateConstraint, .invisibleCharacters, .negativePosition,
    .absurdExtremeComparisons, .erasingOp, .ifsSameCond, .contradictoryComparisons, .redundantComparisons,
    .allowAttributes, .wildcardEnumMatchArm, .needlessRawStrings, .nonAsciiLiteral, .moduleNameRepetitions,
    .minIdentChars, .absolutePaths, .precedence, .unnecessaryStructInitialization, .unusedLintSetting,
    .unusedAssumption, .unrelatedBinders, .literalDotInPattern, .invalidUpcastComparisons,
    .unicodeNotNfc, .unnecessaryTrailingComma,
    .isEquality, .irrefutableIs, .chainableComparison,
    .singleMatchElse, .inconsistentStructConstructor, .overlyComplexBoolExpr, .structFieldNames, .fnParamsExcessiveBools,
    .structExcessiveBools, .needlessRawStringHashes, .branchesSharingCode, .zeroPrefixedLiteral,
    .arbitrarySourceItemOrdering, .singleCallFn,
    .manualAtMostOne, .manualOrdering, .redundantNewtypeRoundtrip, .unnecessaryMinOrMax,
    .manualNat, .manualAbs, .manualAbsDiff, .manualMinMax, .manualClamp, .manualRemEuclid, .moduloOne, .minMax,
    .manualRecordUpdate, .needlessUpdate, .trivialCover, .manualPatternTest,
    .collapsibleMatch, .manualRangePatterns, .wildcardInOrPatterns, .matchOverlappingArm, .unnestedOrPatterns,
    .matchBool, .manualTable,
    .letAndReturn, .redundantLocals, .manualForall, .trivialQuantifier,
    .matchCouldBeTable]

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
  | .caseSplitGuarantees => "case_split_guarantees"
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
  | .unnecessaryStructInitialization => "unnecessary_struct_initialization"
  | .unusedLintSetting => "unused_lint_setting"
  | .unusedAssumption => "unused_assumption"
  | .unrelatedBinders => "unrelated_binders"
  | .literalDotInPattern => "literal_dot_in_pattern"
  | .invalidUpcastComparisons => "invalid_upcast_comparisons"
  | .unicodeNotNfc => "unicode_not_nfc"
  | .unnecessaryTrailingComma => "unnecessary_trailing_comma"
  | .isEquality => "is_equality"
  | .irrefutableIs => "irrefutable_is"
  | .chainableComparison => "chainable_comparison"
  | .singleMatchElse => "single_match_else"
  | .inconsistentStructConstructor => "inconsistent_struct_constructor"
  | .overlyComplexBoolExpr => "overly_complex_bool_expr"
  | .structFieldNames => "struct_field_names"
  | .fnParamsExcessiveBools => "fn_params_excessive_bools"
  | .structExcessiveBools => "struct_excessive_bools"
  | .needlessRawStringHashes => "needless_raw_string_hashes"
  | .branchesSharingCode => "branches_sharing_code"
  | .zeroPrefixedLiteral => "zero_prefixed_literal"
  | .arbitrarySourceItemOrdering => "arbitrary_source_item_ordering"
  | .singleCallFn => "single_call_fn"
  | .manualAtMostOne => "manual_at_most_one"
  | .manualOrdering => "manual_ordering"
  | .redundantNewtypeRoundtrip => "redundant_newtype_roundtrip"
  | .unnecessaryMinOrMax => "unnecessary_min_or_max"
  | .manualRecordUpdate => "manual_record_update"
  | .needlessUpdate => "needless_update"
  | .trivialCover => "trivial_cover"
  | .manualNat => "manual_nat"
  | .manualAbs => "manual_abs"
  | .manualAbsDiff => "manual_abs_diff"
  | .manualMinMax => "manual_min_max"
  | .manualClamp => "manual_clamp"
  | .manualRemEuclid => "manual_rem_euclid"
  | .moduloOne => "modulo_one"
  | .minMax => "min_max"
  | .manualPatternTest => "manual_pattern_test"
  | .collapsibleMatch => "collapsible_match"
  | .manualRangePatterns => "manual_range_patterns"
  | .wildcardInOrPatterns => "wildcard_in_or_patterns"
  | .matchOverlappingArm => "match_overlapping_arm"
  | .unnestedOrPatterns => "unnested_or_patterns"
  | .matchBool => "match_bool"
  | .manualTable => "manual_table"
  | .letAndReturn => "let_and_return"
  | .redundantLocals => "redundant_locals"
  | .manualForall => "manual_forall"
  | .trivialQuantifier => "trivial_quantifier"
  | .matchCouldBeTable => "match_could_be_table"

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
  | .caseSplitGuarantees => "F0729"
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
  | .unnecessaryStructInitialization => "F0790"
  | .unusedLintSetting => "F0791"
  | .unusedAssumption => "F0792"
  | .unrelatedBinders => "F0793"
  | .literalDotInPattern => "F0794"
  | .invalidUpcastComparisons => "F0798"
  | .unicodeNotNfc => "F0799"
  | .unnecessaryTrailingComma => "F0801"
  | .isEquality => "F0802"
  | .irrefutableIs => "F0803"
  | .chainableComparison => "F0804"
  | .singleMatchElse => "F0771"
  | .inconsistentStructConstructor => "F0772"
  | .overlyComplexBoolExpr => "F0773"
  | .structFieldNames => "F0774"
  | .fnParamsExcessiveBools => "F0775"
  | .structExcessiveBools => "F0776"
  | .needlessRawStringHashes => "F0777"
  | .branchesSharingCode => "F0778"
  | .zeroPrefixedLiteral => "F0758"
  | .arbitrarySourceItemOrdering => "F0779"
  | .singleCallFn => "F0788"
  | .manualAtMostOne => "F0840"
  | .manualOrdering => "F0841"
  | .redundantNewtypeRoundtrip => "F0842"
  | .unnecessaryMinOrMax => "F0843"
  | .manualRecordUpdate => "F0818"
  | .needlessUpdate => "F0819"
  | .trivialCover => "F0820"
  | .manualNat => "F0810"
  | .manualAbs => "F0811"
  | .manualAbsDiff => "F0812"
  | .manualMinMax => "F0813"
  | .manualClamp => "F0814"
  | .manualRemEuclid => "F0815"
  | .moduloOne => "F0816"
  | .minMax => "F0817"
  | .manualPatternTest => "F0805"
  | .collapsibleMatch => "F0832"
  | .manualRangePatterns => "F0833"
  | .wildcardInOrPatterns => "F0834"
  | .matchOverlappingArm => "F0835"
  | .unnestedOrPatterns => "F0836"
  | .matchBool => "F0837"
  | .manualTable => "F0838"
  | .letAndReturn => "F0824"
  | .redundantLocals => "F0825"
  | .manualForall => "F0826"
  | .trivialQuantifier => "F0827"
  | .matchCouldBeTable => "F0809"

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
  | .unusedImports | .unusedVariables | .deadCode | .unfulfilledExpectations | .unusedLintSetting
  | .unusedAssumption => .unused
  | .nonSnakeCase | .nonCamelCaseTypes | .nonUpperCaseConstants => .nonstandardStyle
  | .globImports | .lengthZero | .cardZero | .unlessNot | .collapsibleWhen | .matchLikeMembership | .redundantBindings
  | .doubleNeg | .negMultiply | .trivialPattern | .redundantBoolType | .moduleInception | .enumVariantNames
  | .upperCaseAcronyms | .justUnderscoresAndDigits | .disallowedNames | .assertionsOnConstants
  | .manualPatternCharComparison | .isEquality | .chainableComparison | .manualNat | .manualRecordUpdate
  | .manualPatternTest | .collapsibleMatch | .matchOverlappingArm | .letAndReturn | .manualForall => .style
  | .nonminimalBool | .singletonMembership | .constantOutput | .doubleComparison | .manualMethod | .elseExtends
  | .identityOp | .doubleParens | .intPlusOne | .redundantMethodChain | .trivialMatch | .needlessBoolAssign
  | .needlessMatch | .redundantSlicing | .redundantComparisons | .unnecessaryStructInitialization
  | .zeroPrefixedLiteral | .manualAtMostOne | .redundantNewtypeRoundtrip | .unnecessaryMinOrMax | .manualAbs
  | .manualAbsDiff | .manualMinMax | .manualClamp | .manualRemEuclid | .needlessUpdate
  | .manualRangePatterns | .wildcardInOrPatterns | .trivialQuantifier => .complexity
  | .indexAfterUse | .eqOp | .sameBranches | .duplicateElements | .emptyArgument
  | .suspiciousUnaryOpFormatting | .noEffectReplace | .constIsEmpty | .almostCompleteRange | .duplicateConstraint
  | .invisibleCharacters | .negativePosition | .absurdExtremeComparisons | .erasingOp | .ifsSameCond
  | .contradictoryComparisons | .unrelatedBinders | .literalDotInPattern | .irrefutableIs | .moduloOne | .minMax
  | .trivialCover
  | .redundantLocals => .suspicious
  | .membershipChain | .definableOutput | .ifNotElse | .matchSameArms | .wildcardSingleVariant | .ifChainMatch
  | .caseSplitGuarantees | .boolEquality | .zeroSizedMapValues | .manySingleCharNames | .similarNames
  | .tooManyLines | .invalidUpcastComparisons | .unicodeNotNfc | .unnecessaryTrailingComma => .pedantic
  | .allowAttributes | .wildcardEnumMatchArm | .needlessRawStrings | .nonAsciiLiteral | .moduleNameRepetitions
  | .minIdentChars | .absolutePaths | .precedence | .arbitrarySourceItemOrdering
  | .singleCallFn => .restriction
  | .singleMatchElse | .inconsistentStructConstructor | .overlyComplexBoolExpr
  | .structFieldNames | .fnParamsExcessiveBools | .structExcessiveBools | .needlessRawStringHashes
  | .branchesSharingCode | .manualOrdering | .unnestedOrPatterns | .matchBool | .manualTable
  | .matchCouldBeTable => .pedantic
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
indexes a sequence, and `patterns` that each right operand is a value that
a pattern writes (`patternValue`), which `manual_pattern_test` then
reports (`lint::membership_chain`). -/
def membershipChainFires (n : Nat) (sameLeft laterIndexes patterns : Bool) : Bool :=
  sameLeft && n ≥ 3 && !laterIndexes && !patterns

/-- `x = a or x = b or ...`, or `x != a and x != b and ...` if `negated`, as
the texts of `x` and the others. -/
def membershipChainMsg (x : String) (vals : Array String) (negated : Bool) : Msg :=
  let set := s!"\{{", ".intercalate vals.toList}}"
  { code? := some "F0718", headline := s!"this is `{x}` {if negated then "not " else ""}in a set of {vals.size}"
    label? := some s!"a chain of `{if negated then "and" else "or"}`"
    fixes := #[{ msg := "write it as a membership"
                 replacement := if negated then s!"not {x} in {set}" else s!"{x} in {set}" }] }

/-- Whether `constant_output` and `definable_output` fire on an output,
where `mentioned` is what its definition mentions, if it is defined
(`lint::output_lints`). -/
def outputLints (defined : Bool) (mentioned : List Mention) (nReqs : Nat) (equation : Bool) : Bool × Bool :=
  (defined && mentioned.isEmpty, !defined && nReqs == 1 && equation)

def constantOutputMsg (x : Name) : Msg :=
  { code? := some "F0719", headline := s!"defined output `{x}` is the same in every behaviour"
    label? := some "mentions no variable"
    notes := #["help: make it a `const`, which is shared by every procedure"] }

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

/-- Whether `s` has a comment outside its string literals. -/
def hasComment (s : String) : Bool := withoutComments s != s

/-- The text `s` as the lints compare it, so that two texts are *written the
same* (`Reqs/Lint#written-the-same`) if these agree: without comments or
whitespace, but for one space between two characters of names, numbers or
keywords, and with string literals, raw ones too, as they are. A text
without whitespace, string literals or the start of a comment is its own
form, and is returned as it is. -/
def writtenForm (s : String) : String := Id.run do
  let plain := (s.foldl (init := (true, ' ')) fun (ok, prev) c =>
    (ok && !c.isWhitespace && c != '"' && !(c == '-' && (prev == '-' || prev == '/')), c)).1
  if plain then return s
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

/-- Whether two expressions see the same binders of pattern tests, `sa` and
`sb`, as sets (`lint::Scoped`). -/
def sameScope (sa sb : List String) : Bool := sa.all (sb.contains ·) && sb.all (sa.contains ·)

/-- Whether two expressions are written the same in the same scope: their
texts `a` and `b` are written the same, and they see the same binders of
pattern tests, `sa` and `sb` (`lint::Scoped`). -/
def writtenSameIn (a b : String) (sa sb : List String) : Bool := writtenSame a b && sameScope sa sb

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

/-- The lints that Fren renamed, by their old names: `set_option` rejects
an old name, with its new one as the fix. -/
def renamedLints : List (String × String) :=
  [("case_split_reqs", "case_split_guarantees")]

def unknownLintMsg (n : String) : Msg :=
  match renamedLints.lookup n with
  | some new =>
    { code? := some "F0707", headline := s!"unknown lint `{n}`", label? := some "no such lint"
      notes := #[s!"note: `{n}` was renamed to `{new}`"]
      fixes := #[{ msg := s!"use the new name: `{new}`", replacement := s!"fren.lint.{new}" }] }
  | none =>
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
  /-- Its scope: the module, or the path of the procedure containing it. -/
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
of that import: a procedure's imports shadow its module's scope. -/
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
def Table.shadowedImport? (t : Table) (scope : Name) (locals : Locals) (n : Name) (bang : Bool) :
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
  | typeAlias
  | constant
  deriving Inhabited, BEq, DecidableEq, Repr

def Named.describe : Named → String
  | .module => "module"
  | .component => "procedure"
  | .variable => "variable"
  | .field => "field"
  | .binder => "binder"
  | .function => "function"
  | .instance => "call"
  | .constraint => "constraint"
  | .global => "global expectation"
  | .enumeration => "enum"
  | .variant => "variant"
  | .record => "record"
  | .abstractType => "abstract type"
  | .typeAlias => "type alias"
  | .constant => "constant"

/-- The case of a name (`lint::naming_case`). -/
def Named.case : Named → Case
  | .enumeration | .variant | .record | .abstractType | .typeAlias => .camel
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

/-- The words of a field's name, in lower case, without its `?`. -/
def fieldWords (n : Name) : List String := (words (baseName (nameText n))).map String.toLower

/-- `struct_field_names` for the record `n` of `fields`, if they share a
first or a last word (`lint::struct_field_names`, decided as for
`enum_variant_names`). -/
def structFieldNamesMsg? (n : Name) (fields : Array Name) : Option Msg :=
  let names := fields.map fun f => Name.mkSimple ("_".intercalate (fieldWords f))
  let first? := sharedWord? names false
  let last? := sharedWord? names true
  if !enumVariantNames fields.size first?.isSome last?.isSome then none else
  let what := match first?, last? with
    | some f, some l => s!"starts with `{f}` and ends with `{l}`"
    | some f, none => s!"starts with `{f}`"
    | none, some l => s!"ends with `{l}`"
    | none, none => ""
  let ws := first?.toList ++ last?.toList
  some { code? := some Lint.structFieldNames.code, headline := s!"every field of `{nameText n}` {what}"
         label? := some "its fields share a word"
         notes := #[s!"help: remove {" and ".intercalate (ws.map (s!"`{·}`"))} from each field's name, or put it in the record's"] }

/-- `struct_field_names` for the field `f` of the record `n`, if it
contains the record's name, its words compared in lower case
(`lint::field_has_record_name`, decided as for `enum_variant_names`). -/
def fieldNameMsg? (n f : Name) : Option Msg :=
  let ws := fieldWords f
  let rs := (words (nameText n)).map String.toLower
  if !variantHasEnumName ws.length rs.length (containsWords ws rs) then none else
  let recName := "_".intercalate rs
  some { code? := some Lint.structFieldNames.code
         headline := s!"field `{nameText f}` contains the name of its record `{nameText n}`"
         label? := some s!"contains `{recName}`"
         notes := #["note: a field is read from a value of its record, which says what the field is of",
           s!"help: remove `{recName}` from its name"] }

/-- Whether `fn_params_excessive_bools` fires on a function with `nBools`
`Bool` parameters (`lint::fn_params_excessive_bools`): more than 3, as in
Clippy. -/
def fnParamsExcessiveBools (nBools : Nat) : Bool := nBools > 3

/-- The function `f`, with `n` `Bool` parameters. -/
def fnParamsExcessiveBoolsMsg (f : Name) (n : Nat) : Msg :=
  { code? := some Lint.fnParamsExcessiveBools.code, headline := s!"function `{nameText f}` has {n} `Bool` parameters"
    label? := some "more than 3 `Bool` parameters"
    notes := #[s!"note: a call such as `{nameText f}({", ".intercalate (List.replicate n "true")})` does not say which is which",
      "help: replace some of them with an enumeration, or with a record of named `Bool` fields"] }

/-- Whether `struct_excessive_bools` fires on a record with `nBools`
`Bool` fields (`lint::struct_excessive_bools`): more than 3, as in Clippy. -/
def structExcessiveBools (nBools : Nat) : Bool := nBools > 3

/-- The record `r`, with `n` `Bool` fields. -/
def structExcessiveBoolsMsg (r : Name) (n : Nat) : Msg :=
  { code? := some Lint.structExcessiveBools.code, headline := s!"record `{nameText r}` has {n} `Bool` fields"
    label? := some "more than 3 `Bool` fields"
    notes := #["note: every combination of their values is allowed, though some are probably not meant",
      "help: replace some of them with an enumeration of the combinations that are meant"] }

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
  | .module | .component | .function | .global | .enumeration | .record | .abstractType | .typeAlias | .constant => true
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

/-- The message of `unused_variables` for a variable of a procedure, or
with `global`, of a global expectation, that nothing mentions. -/
def unusedVariableMsg (n : Name) (global : Bool) (output : Bool) : Msg :=
  { code? := some Lint.unusedVariables.code
    headline := s!"unused variable `{n}`", label? := some "never mentioned"
    notes := (if output then #["note: nothing constrains it, so it can take any value"]
        else #[s!"note: nothing in its {if global then "global expectation" else "procedure"} depends on it"])
      ++ #["help: remove it, or mention it in a constraint"] }

/-- A parameter of a defined function that its body never mentions. -/
def unusedParamMsg (n : Name) : Msg :=
  { code? := some Lint.unusedVariables.code
    headline := s!"unused parameter `{n}`", label? := some "never mentioned"
    notes := #["note: the function's value does not depend on it", "help: remove it, or mention it in the body"] }

/-- A name of a `let` or `where` clause that neither its body nor a later
definition of the clause mentions. -/
def unusedDefinitionMsg (n : Name) : Msg :=
  { code? := some Lint.unusedVariables.code
    headline := s!"unused definition `{n}`", label? := some "never mentioned"
    notes := #["note: a definition that nothing mentions has no effect",
      "help: remove it, or mention it in the body or a later definition"] }

/-- A bound name of a `forall` (`all`) or an `exists` that its body never
mentions. -/
def unusedBoundMsg (n : Name) (all : Bool) : Msg :=
  { code? := some Lint.unusedVariables.code
    headline := s!"unused bound name `{n}`", label? := some "never mentioned"
    notes := #[s!"note: the body does not depend on it, so the `{if all then "forall" else "exists"}` over it is its body",
      "help: remove it, or mention it in the body"] }

/-- The variables, or binders, of `declared` that `mentioned` does not
contain, in order. -/
def unmentioned (declared : Array (Name × α)) (mentioned : Array Name) : Array (Name × α) :=
  declared.filter fun (n, _) => !mentioned.contains n

/-! ## Dead code -/

/-- Whether an item is dead (`lint::dead_item`). -/
def deadItem (what : Named) (isPub : Bool) (nUses : Nat) : Bool :=
  match what with
  | .enumeration | .record | .abstractType | .typeAlias | .function | .constant => !isPub && nUses == 0
  | _ => false

/-- A private enumeration, record, abstract type, function or constant declared in
the file being elaborated, with the level of `dead_code` there. -/
structure ItemRecord where
  what : Named
  path : Name
  level : LevelInEffect
  /-- For a defined function, the level of `single_call_fn` there. -/
  singleCall? : Option LevelInEffect := none
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

/-- Whether `single_call_fn` fires on a function, `defined` if it has a
body, applied `nUses` times in its file (`lint::single_call_fn`). -/
def singleCallFn (defined isPub : Bool) (nUses : Nat) : Bool := defined && !isPub && nUses == 1

def singleCallFnMsg (n : Name) : Msg :=
  { code? := some Lint.singleCallFn.code, headline := s!"function `{n.getString!}` is applied only once"
    label? := some "applied once"
    notes := #["note: it is private, and only one path in this file applies it",
      "help: write its body in place of the application, with the arguments in place of the parameters"] }

/-- The `single_call_fn` messages of a file's defined functions, counting
uses as `deadCodeReports` does. -/
def singleCallReports (items : Array (ItemRecord × α)) (used : Array Name) : Array (LintReport α) :=
  items.filterMap fun (i, ref) => i.singleCall?.bind fun level =>
    if singleCallFn true false (used.count i.path) then
      some { lint := .singleCallFn, level, ref, msg := singleCallFnMsg i.path }
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

/-! ## Matches -/

/-- Where an operand that must be an atom is: the receiver of a field, a
method or an index, and a `match`'s scrutinee. -/
def receiverSlot : Slot := ⟨BKind.atom.prec, .left, false⟩

/-- The slot of a part of an atom other than a receiver: an argument of an
application or a method, a field of a record literal, an element of a
collection literal, an index, or a `match`'s scrutinee or arm's body.
These take any expression but an open-ended one, as a `when`'s condition
does (`Reqs/Lint#parentheses-in-fixes`). -/
def delimitedSlot : Slot := ⟨0, .nonAssoc, false⟩

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
  /-- Each alternative is a variant without a payload or a literal
  (`equatable`). -/
  equatable : Bool := false
  /-- Its pattern overlaps another only where one contains the other
  (`disjointPat`); so does `_`. -/
  disjoint : Bool := false
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

/-- Whether `match_like_membership` fires, whether its fix is negated, of
the alternatives whose arms are `false`, and whether it is a pattern test
rather than an equation: unless it lists one alternative, which `=` can
write (`lint::match_like_membership`). -/
def matchMembership (boolBodies binds disjoint trueFirst falseFirst equatableTrue equatableFalse wildcard
    wildcardTrue : Bool) (nTrue nFalse : Nat) : Bool × Bool × Bool :=
  let negated := if wildcard then wildcardTrue else if disjoint then nTrue > nFalse else falseFirst
  (boolBodies && !binds && (disjoint || if negated then falseFirst else trueFirst), negated,
    !(if negated then equatableFalse else equatableTrue) || (if negated then nFalse else nTrue) != 1)

/-- The fix of `match_like_membership`, if it fires, as the texts before
and after the scrutinee, which is `scrutinee` as written, with the
parentheses around it, and whether it is a pattern test; `slot` is where
the `match` is. -/
def membershipParts? (arms : Array ArmInfo) (scrutinee : BText) (slot : Option Slot) :
    Option (String × String × Bool) := do
  let lit (b : Bool) (a : ArmInfo) := a.body.text == toString b
  let boolBodies := arms.all (fun a => lit true a || lit false a) && arms.any (lit true) && arms.any (lit false)
  let wild? := arms.find? (·.wildcard)
  let named (b : Bool) := (arms.filter fun a => !a.wildcard && lit b a).flatMap (·.alts)
  -- Whether every arm whose body is `b` comes before every other arm but `_`.
  let first (b : Bool) := Id.run do
    let mut other := false
    for a in arms do
      if a.wildcard then continue
      if !lit b a then other := true
      else if other then return false
    return true
  let equatable (b : Bool) := arms.all fun a => a.wildcard || !lit b a || a.equatable
  let (fires, negated, test) := matchMembership boolBodies (arms.any (·.binds)) (arms.all (·.disjoint)) (first true)
    (first false) (equatable true) (equatable false) wild?.isSome (wild?.any (lit true)) (named true).size
    (named false).size
  guard fires
  let vs := named !negated
  let (op, prec) := if test then (s!" is {" | ".intercalate vs.toList}", if negated then 4 else 5)
    else (s!" {if negated then "!=" else "="} {vs[0]!}", 5)
  let bareScrutinee := bareOperand 5 scrutinee.prec .nonAssoc false
  let pre := (if negated && test then "not " else "") ++ (if bareScrutinee then "" else "(")
  let post := (if bareScrutinee then "" else ")") ++ op
  let bare := match slot with | some s => bareOperand s.outer prec s.assoc s.right | none => true
  return if bare then (pre, post, test) else ("(" ++ pre, post ++ ")", test)

/-- `match_like_membership`'s message, whose fix is `replacement`, a
pattern test if `test`. -/
def membershipMsg (replacement : String) (test : Bool) : Msg :=
  { code? := some Lint.matchLikeMembership.code, headline := "this `match` only tests which of its patterns its scrutinee matches"
    label? := some "each arm is `true` or `false`"
    fixes := #[{ msg := if test then "write it as a pattern test" else "write it as an equation", replacement }] }

/-! ## Pattern tests -/

/-- Whether the pattern `p` matches every value of `ty`: `_` is not useful
after it, as for an arm after it (`Reqs/Lang/Patterns`). -/
def matchesEvery (sigs : Sigs) (ty : PatTy) (p : Pat) : Bool := !useful sigs [ty] #[[p]] [.wild]

/-- Whether `irrefutable_is` fires on `e is P`, from whether `P` matches
every value of `e`'s type (`lint::irrefutable_is`). -/
def irrefutableIs (matchesEvery : Bool) : Bool := matchesEvery

/-- `e is P` that is always `true`, where `e` is a `ty`. -/
def irrefutableIsMsg (ty : String) (wildcard : Bool) : Msg :=
  { code? := some Lint.irrefutableIs.code, headline := "this pattern test is always `true`"
    label? := some (if wildcard then "`_` matches every value" else s!"matches every value of `{ty}`") }

/-- The alternatives of `p`'s own or-pattern, or `p` itself. -/
def Pat.top : Pat → Array Pat
  | .or alts => alts
  | p => #[p]

/-- Whether an alternative, written `text`, is one that `=` and `in` can
write: a variant without a payload, `true`, `false`, a string literal, or
an integer literal, not a range of one value. -/
def equatableAlt (p : Pat) (text : String) : Bool :=
  match p with
  | .ctor _ args => args.isEmpty
  | .bool _ | .str _ => true
  | .int (some a) (some b) => a == b && writtenForm text == toString a
  | _ => false

/-- Whether each alternative of `p`, written `texts`, is one that `=` and
`in` can write (`equatableAlt`). -/
def equatable (p : Pat) (texts : Array String) : Bool :=
  p.top.size == texts.size && (p.top.zip texts).all fun (a, t) => equatableAlt a t

/-- Whether `p`, written `texts`, overlaps another such pattern only where
one contains the other: each alternative is a literal, `true`, `false`, or
a variant whose payload's patterns are `_` (`lint::match_like_membership`). -/
def disjointPat (p : Pat) (texts : Array String) : Bool :=
  p.top.size == texts.size && (p.top.zip texts).all fun (a, t) =>
    equatableAlt a t || match a with | .ctor _ args => args.all (· matches .wild false) | _ => false

/-- Whether `is_equality` fires on `e is P`, from the number of
alternatives of `P`, whether each is a variant without a payload or a
literal, and whether `irrefutable_is` fires on it (`lint::is_equality`). -/
def isEquality (nAlts : Nat) (equatable irrefutable : Bool) : Bool := nAlts == 1 && equatable && !irrefutable

/-- `is_equality`'s message on `e is P`, from `e` as written, with the
parentheses around it, and the alternative that is `P`. -/
def isEqualityMsg (scrutinee : BText) (alt : String) : Msg :=
  let x := scrutinee.inSlot (some ⟨5, .nonAssoc, false⟩)
  let fixed := s!"{x} = {alt}"
  { code? := some Lint.isEquality.code, headline := "this pattern test is an equation"
    label? := some "names a variant without a payload, or a literal"
    fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

/-- Whether `single_match_else` fires on a `match` of `nArms` arms, from
whether its first arm's pattern is a test, a pattern other than `_` that
binds nothing, on a scrutinee that is not a `Bool`, whether the second is
`_`, and whether `match_like_membership`, `needless_match`,
`trivial_match` or `match_same_arms` fires on it
(`lint::single_match_else`). -/
def singleMatchElse (nArms : Nat) (test wildcard other : Bool) : Bool :=
  nArms == 2 && test && wildcard && !other

/-- The fix of `single_match_else`, if it fires, where `other` says that
another match lint fires on it, and `bool` that the scrutinee is a `Bool`:
`if x = V then a else b`, or with `x in {V, W}` for several variants
without a payload or literals, or `x is P` for another pattern, from the
scrutinee `x` as written, with the parentheses around it, in parentheses
where `slot` requires them, or where it is `followed` (`BText.inSlot`). -/
def singleMatchElseFix? (arms : Array ArmInfo) (scrutinee : BText) (slot : Option Slot) (other : Bool)
    (followed : Bool := false) (bool : Bool := false) : Option String := do
  let #[a, b] := arms | none
  let sameBodies := writtenSame a.body.text b.body.text
  guard (singleMatchElse arms.size (!a.wildcard && !a.binds && !bool) b.wildcard (other || sameBodies))
  let test := if a.equatable && a.alts.size == 1 then s!"{scrutinee.inSlot (BKind.bin "=").slots[0]!} = {a.alts[0]!}"
    else if a.equatable then s!"{scrutinee.inSlot (BKind.bin "in").slots[0]!} in \{{", ".intercalate a.alts.toList}}"
    else s!"{scrutinee.inSlot BKind.patternTest.slots[0]!} is {a.pattern}"
  let t : BText := { text := s!"if {test} then {a.body.text} else {b.body.text}", prec := BKind.ite.prec }
  return t.inSlot slot followed

/-- A match lint's message about a table over a scrutinee, which means a
`match` whose arms are disjoint, and which the lints look at as at that
`match`: it calls it a table (`Reqs/Lint/Pedantic/Matches#arms`). -/
def Msg.ofTable (m : Msg) : Msg :=
  let f (t : String) := t.replace "`match`" "table"
  { m with headline := f m.headline, label? := m.label?.map f, notes := m.notes.map f
           fixes := m.fixes.map fun x => { x with msg := f x.msg } }

/-- `single_match_else` on a `match` whose fix is `replacement`, which it
does not have where the `match` is `commented`: the fix would drop its
comments. -/
def singleMatchElseMsg (replacement : String) (commented : Bool := false) : Msg :=
  { code? := some Lint.singleMatchElse.code, headline := "this `match` tests for one pattern"
    label? := some "one pattern, then `_`"
    notes := if commented then #["note: the fix would drop the comments in the `match`, so it has none"] else #[]
    fixes := if commented then #[] else #[{ msg := "write it as an `if`", replacement }] }

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

/-! ## Patterns as written -/

/-- A pattern as written: what it resolves to, its text, where it is in a
front end's representation (`α`), and its parts, an or-pattern's
alternatives or a variant's payload's patterns. -/
inductive PatNode (α : Type) where
  | mk (pat : Pat) (text : String) (at_ : α) (kids : Array (PatNode α))

instance [Inhabited α] : Inhabited (PatNode α) := ⟨.mk default "" default #[]⟩

def PatNode.pat : PatNode α → Pat | .mk p .. => p
def PatNode.text : PatNode α → String | .mk _ t .. => t
def PatNode.at_ : PatNode α → α | .mk _ _ a _ => a
def PatNode.kids : PatNode α → Array (PatNode α) | .mk _ _ _ k => k

/-- The or-patterns of two or more alternatives within `n`, `n` too if it
is one, in preorder. -/
partial def PatNode.orPatterns (n : PatNode α) : Array (PatNode α) :=
  (if n.pat matches .or _ && n.kids.size ≥ 2 then #[n] else #[]) ++ n.kids.flatMap PatNode.orPatterns

/-- Whether `wildcard_in_or_patterns` fires on an or-pattern, from whether
one of its alternatives is `_` (`lint::wildcard_in_or_patterns`). -/
def wildcardInOr (wildcard : Bool) : Bool := wildcard

/-- An or-pattern with a `_` alternative. -/
def wildcardInOrMsg : Msg :=
  { code? := some Lint.wildcardInOrPatterns.code, headline := "this or-pattern has `_` as an alternative"
    label? := some "matches every value"
    notes := #["note: `_` matches every value, so the other alternatives add nothing"]
    fixes := #[{ msg := "write `_`", replacement := "_" }] }

/-- Whether a bound of a range, written `s`, after the `..` and any `=`,
is an integer literal, possibly negated, or absent, rather than a
constant. -/
def literalBound (s : String) : Bool :=
  match s.toList.dropWhile (fun c => c == '=' || c.isWhitespace) with
  | [] => true
  | c :: rest => c.isDigit || (c == '-' && (rest.dropWhile Char.isWhitespace).head?.any Char.isDigit)

/-- Whether the integer pattern written `text`, a literal or a range, has
only literal bounds. -/
def literalBounds (text : String) : Bool := (text.splitOn "..").all literalBound

/-- Whether the lower bound `lo` is at most the upper bound `hi`, where
`none` is unbounded. -/
def lowerAtMost : Option Int → Option Int → Bool
  | some l, some h => decide (l ≤ h)
  | _, _ => true

/-- The one interval that the intervals `ivs` make together, if they leave
no gap between them. -/
def unionInterval? (ivs : Array (Option Int × Option Int)) : Option (Option Int × Option Int) := do
  let sorted := ivs.qsort fun a b => match a.1, b.1 with
    | none, some _ => true
    | some x, some y => decide (x < y)
    | _, _ => false
  let (lo, hi₀) ← sorted[0]?
  let mut hi := hi₀
  for (l, h) in sorted.extract 1 sorted.size do
    let some h₀ := hi | continue
    unless lowerAtMost l (some (h₀ + 1)) do failure
    hi := h.map (max h₀)
  return (lo, hi)

/-- Whether `manual_range_patterns` fires on an or-pattern, from the number
of its alternatives, whether each is an integer literal or a range with
literal bounds, whether one is a range, and whether together they make
one interval, bounded on some side (`lint::manual_range_patterns`). -/
def manualRangePatterns (nAlts : Nat) (integers range interval : Bool) : Bool :=
  integers && interval && (nAlts ≥ 3 || (nAlts ≥ 2 && range))

/-- The range that matches the integers of the interval `iv`. -/
def rangeText : Option Int × Option Int → String
  | (some l, some h) => s!"{l}..={h}"
  | (some l, none) => s!"{l}.."
  | (none, some h) => s!"..={h}"
  | (none, none) => "_"

/-- The range that replaces an or-pattern whose alternatives are `alts`,
each resolved and written, if `manual_range_patterns` fires on it. -/
def manualRangeFix? (alts : Array (Pat × String)) : Option String :=
  let ivs := alts.filterMap fun (p, t) => match p with
    | .int lo hi => if literalBounds t then some (lo, hi) else none
    | _ => none
  let iv? := (unionInterval? ivs).filter fun iv => iv.1.isSome || iv.2.isSome
  let range := ivs.any fun (lo, hi) => lo.isNone || hi.isNone || lo != hi
  if manualRangePatterns alts.size (ivs.size == alts.size) range iv?.isSome then iv?.map rangeText else none

/-- An or-pattern that matches the integers of the range `fixed`. -/
def manualRangeMsg (fixed : String) : Msg :=
  { code? := some Lint.manualRangePatterns.code, headline := s!"this or-pattern matches the range `{fixed}`"
    label? := some "integers without a gap"
    fixes := #[{ msg := "write the range", replacement := fixed }] }

/-- Whether `unnested_or_patterns` fires on two alternatives of an
or-pattern next to each other, from whether they name the same variant,
and the number of values of its payload whose patterns are not written
the same (`lint::unnested_or_patterns`). -/
def unnestedOr (sameVariant : Bool) (nDiffer : Nat) : Bool := sameVariant && nDiffer == 1

/-- The value of the payload at which two alternatives differ, if
`unnested_or_patterns` fires on them. -/
def differAt? [Inhabited α] (a b : PatNode α) : Option Nat :=
  match a.pat, b.pat with
  | .ctor i _, .ctor j _ =>
    let n := a.kids.size
    let ds := (Array.range n).filter fun k => (writtenForm ·.text) <$> a.kids[k]? != (writtenForm ·.text) <$> b.kids[k]?
    if unnestedOr (i == j && b.kids.size == n) ds.size then ds[0]? else none
  | _, _ => none

/-- The alternatives `run`, of one variant, with the or-pattern of their
patterns of the value `k` of its payload nested there. -/
def nestedText [Inhabited α] (run : Array (PatNode α)) (k : Nat) : String :=
  let a := run[0]!
  let path := String.ofList (a.text.toList.takeWhile (· != '('))
  let args := (Array.range a.kids.size).map fun m =>
    if m == k then " | ".intercalate (run.map (·.kids[k]!.text)).toList else a.kids[m]!.text
  s!"{path}({", ".intercalate args.toList})"

/-- The runs of two or more alternatives of `alts`, next to each other,
that `unnested_or_patterns` fires on: each differs from the first of its
run at the same value of the payload. Each is its first and last index,
and the pattern that replaces it. -/
def unnestedRuns [Inhabited α] (alts : Array (PatNode α)) : Array (Nat × Nat × String) := Id.run do
  let mut out := #[]
  let mut i := 0
  while i + 1 < alts.size do
    match differAt? alts[i]! alts[i + 1]! with
    | none => i := i + 1
    | some k =>
      let mut j := i + 1
      while j + 1 < alts.size && differAt? alts[i]! alts[j + 1]! == some k do j := j + 1
      out := out.push (i, j, nestedText (alts.extract i (j + 1)) k)
      i := j + 1
  return out

/-- Alternatives of one variant that `fixed` writes as one. -/
def unnestedOrMsg (fixed : String) : Msg :=
  { code? := some Lint.unnestedOrPatterns.code, headline := "these alternatives differ only in one value of the payload"
    label? := some "one variant, written more than once"
    fixes := #[{ msg := "nest the or-pattern", replacement := fixed }] }

/-- Whether two intervals have an integer in common. -/
def intervalsMeet (a b : Option Int × Option Int) : Bool := lowerAtMost a.1 b.2 && lowerAtMost b.1 a.2

/-- Whether `match_overlapping_arm` fires on a range of an arm and one of
an earlier arm, from whether they have an integer in common, and whether
the later is within the earlier, or contains it
(`lint::match_overlapping_arm`). -/
def matchOverlappingArm (meet within contains : Bool) : Bool := meet && !within && !contains

/-- For the arms of a `match`, each its alternatives' intervals, `none`
for an alternative that is not an integer pattern: each alternative that
`match_overlapping_arm` fires on, by arm and alternative, with the first
alternative of an earlier arm that it overlaps, by arm and alternative. -/
def overlappingArms (arms : Array (Array (Option (Option Int × Option Int)))) : Array ((Nat × Nat) × (Nat × Nat)) :=
  (Array.range arms.size).flatMap fun j => (Array.range arms[j]!.size).filterMap fun b => do
    let J ← arms[j]![b]!
    let earlier := (Array.range j).flatMap fun i => (Array.range arms[i]!.size).map (i, ·)
    let hit ← earlier.find? fun (i, a) => match arms[i]![a]! with
      | some I => matchOverlappingArm (intervalsMeet I J) (intervalWithin J I) (intervalWithin I J)
      | none => false
    return ((j, b), hit)

/-- A range that overlaps `earlier`, an earlier arm's pattern, without
either containing the other. -/
def overlappingArmMsg (earlier : String) : Msg :=
  { code? := some Lint.matchOverlappingArm.code, headline := s!"this range overlaps `{earlier}`, an earlier arm's pattern"
    label? := some "overlaps an earlier arm"
    notes := #[s!"note: where they overlap, the earlier arm is taken, so this arm matches only part of its range"] }

/-! ## Matches on a binder -/

/-- Whether the text `s` mentions the name `x`: has an identifier, outside
comments and string literals, whose first segment is `x`, with or without
`!`. A path `E::x` names an item, not `x`. An over-approximation, which
keeps a lint that drops `x` from firing. -/
def mentionsName (s : String) (x : String) : Bool := Id.run do
  let cs := (withoutComments s).toList.toArray
  let mut i := 0
  while i < cs.size do
    let c := cs[i]!
    if c == '"' then
      i := i + 1
      while i < cs.size && cs[i]! != '"' do i := i + (if cs[i]! == '\\' then 2 else 1)
      i := i + 1
    else if isWordChar c then
      let start := i
      while i < cs.size && isWordChar cs[i]! do i := i + 1
      let w := String.ofList (cs.extract start i).toList
      let afterPath := start ≥ 2 && cs[start - 1]! == ':' && cs[start - 2]! == ':'
      let afterDot := start ≥ 1 && cs[start - 1]! == '.'
      if w == x && !afterPath && !afterDot then return true
    else i := i + 1
  return false

/-- Whether `collapsible_match` fires on an arm whose body is a `match`:
from whether its scrutinee is a binder of the arm's pattern, which is one
variant whose payload's patterns are `_` or binders; whether the inner
`match`'s last arm is `_`, and the first later arm of the outer `match`
that matches the variant is `_` with a body written the same; whether the
binder is mentioned elsewhere in the inner `match`, or the inner `_` arm's
body mentions a binder of the arm's pattern; whether an inner
pattern binds a name that the arm's pattern binds; and the number of
inner arms (`lint::collapsible_match`). -/
def collapsibleMatch (onBinder flat innerWildcard sameWildcard mentioned clash : Bool) (nInner : Nat) : Bool :=
  onBinder && flat && innerWildcard && sameWildcard && !mentioned && !clash && nInner ≥ 2

/-- The arms that replace an arm whose pattern is the variant written
`path` with the payload's patterns `args`, whose body is a `match` on the
binder at `k` with the arms `inner`, as their patterns and bodies, but for
its last, `_`. -/
def collapsedArms (path : String) (args : Array String) (k : Nat) (inner : Array (String × String)) : String :=
  ", ".intercalate (inner.toList.map fun (p, b) => s!"{path}({", ".intercalate (args.modify k fun _ => p).toList}) => {b}")

/-- A `match` on the binder `x` of its arm that the arm's pattern can
match instead, with the arms `fixed?` that replace the arm, unless the
arm has a comment. -/
def collapsibleMatchMsg (x : String) (fixed? : Option String) : Msg :=
  { code? := some Lint.collapsibleMatch.code, headline := s!"this `match` on `{x}` can be part of the arm's pattern"
    label? := some s!"a `match` on `{x}`"
    notes := #["note: its `_` arm has the body of the outer `match`'s `_` arm"] ++
      (if fixed?.isNone then #["note: the fix would drop the comments in the arm, so it has none"] else #[])
    fixes := fixed?.toArray.map fun r => { msg := "match the payload in the arm's pattern", replacement := r } }

/-! ## Matches on a `Bool` -/

/-- Whether `match_bool` fires on a `match` on a `Bool` of `nArms` arms,
from whether the first is `true` or `false` and the second the other or
`_`, and whether `match_like_membership`, `match_same_arms` or
`trivial_match` fires on it (`lint::match_bool`). -/
def matchBool (nArms : Nat) (literals other : Bool) : Bool := nArms == 2 && literals && !other

/-- The fix of `match_bool`, if it fires, where `other` says that another
match lint fires on it: `if x then a else b`, from the scrutinee `x` as
written, and the bodies of the arms, `a` that of the arm that `true`
takes, in parentheses where `slot` requires them, or where it is
`followed` (`BText.inSlot`). -/
def matchBoolFix? (pats : Array Pat) (arms : Array ArmInfo) (scrutinee : String) (slot : Option Slot) (other : Bool)
    (followed : Bool := false) : Option String := do
  let #[p, q] := pats | none
  let #[a, b] := arms | none
  let first? : Option Bool := match p with | .bool v => some v | _ => none
  let literals := first?.any fun v => match q with
    | .bool w => w != v
    | .wild false => true
    | _ => false
  guard (matchBool pats.size literals (other || writtenSame a.body.text b.body.text))
  let (t, f) := if first? == some true then (a, b) else (b, a)
  let ite : BText := { text := s!"if {scrutinee} then {t.body.text} else {f.body.text}", prec := BKind.ite.prec }
  return ite.inSlot slot followed

/-- `match_bool` on a `match` whose fix is `replacement`, which it does not
have where the `match` is `commented`. -/
def matchBoolMsg (replacement : String) (commented : Bool := false) : Msg :=
  { code? := some Lint.matchBool.code, headline := "this `match` on a `Bool` is an `if`"
    label? := some "a `match` on a `Bool`"
    notes := if commented then #["note: the fix would drop the comments in the `match`, so it has none"] else #[]
    fixes := if commented then #[] else #[{ msg := "write it as an `if`", replacement }] }

/-! ## Matches that could be tables -/

/-- Whether the static rules accept the arms of a `match` on a value of
`ty`, whose patterns are `pats`, of which those that have a guard are
`guarded`, as the arms of a table over a scrutinee
(`Reqs/Lang/Expressions#tables-over-a-scrutinee`): only the last arm is
`_` without a guard, and `checkTableArms` accepts them. -/
def acceptedAsTable (sigs : Sigs) (ty : PatTy) (pats : Array Pat) (guarded : Array Bool) : Bool :=
  (rowAfterWild? ((pats.zip guarded).map fun (p, g) => p matches .wild false && !g)).isNone &&
    (checkTableArms sigs ty pats guarded).toBool

/-- Whether `match_could_be_table` fires on a `match` of `nArms` arms, from
whether one has a guard, and whether the static rules accept its arms as
a table's (`acceptedAsTable`) (`lint::match_could_be_table`). -/
def matchCouldBeTable (nArms : Nat) (anyGuard tableAccepted : Bool) : Bool := nArms ≥ 2 && !anyGuard && tableAccepted

/-- `match_could_be_table`, whose fix writes `table` in place of `match`. -/
def matchCouldBeTableMsg : Msg :=
  { code? := some Lint.matchCouldBeTable.code, headline := "the arms of this `match` are disjoint, so it can be a table"
    label? := some "disjoint arms"
    notes := #["note: a table over a scrutinee states that its arms are disjoint, which is checked, so that their order does not matter"]
    fixes := #[{ msg := "write `table` in place of `match`", replacement := "table" }] }

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

/-- The kind of a constraint, a cover goal or a global expectation
(`lint::ConstraintKind`). -/
inductive ConstraintKind where
  | assume
  | ensure
  | expect
  | cover
  deriving Inhabited, BEq, DecidableEq, Repr

def ConstraintKind.keyword : ConstraintKind → String
  | .assume => "assume"
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
kind `earlier`. When the two are of one kind, the fix removes the later. -/
def duplicateConstraintMsg (earlier later : ConstraintKind) (name : String) : Msg :=
  let notes := if earlier == later then #["help: remove it"]
    else if later == .expect then
      #[s!"note: an `expect` that repeats an `{earlier.keyword}` tests nothing",
        "help: the expectation was probably meant to say something stronger"]
    else #["note: one of them is probably not the constraint meant"]
  { code? := some Lint.duplicateConstraint.code, headline := s!"this is written the same as `{name}`"
    label? := some s!"the same as `{name}`", notes }

/-! ## Raw string literals -/

/-- The `#`s around the raw string literal written `t`, `r#"..."#`, and its
body; `none` if `t` is not a raw literal. -/
def rawParts? (t : String) : Option (Nat × List Char) := do
  let 'r' :: cs := t.toList | none
  let hashes := (cs.takeWhile (· == '#')).length
  let '"' :: rest := cs.drop hashes | none
  guard (rest.length ≥ hashes + 1)
  return (hashes, rest.take (rest.length - hashes - 1))

/-- The longest run of `#` directly after a `"` in `body`, or `-1` if it has
no `"`. -/
def longestHashRun : List Char → Int
  | [] => -1
  | '"' :: rest => max (rest.takeWhile (· == '#')).length (longestHashRun rest)
  | _ :: rest => longestHashRun rest

/-- Whether `needless_raw_string_hashes` fires on a raw literal with
`hashes` `#`s, whose body's longest run of `#` after a `"` is `longest`,
and the fewest `#`s it needs: one more than that run, so that no `"` in
the body is followed by as many (`lint::needless_raw_string_hashes`). -/
def needlessRawHashes (hashes : Nat) (longest : Int) : Bool × Int := (hashes > longest + 1, longest + 1)

/-- The raw literal written `t`, with the fewest `#`s it needs, if
`needless_raw_string_hashes` fires on it. -/
def fewerHashes? (t : String) : Option String := do
  let (hashes, body) ← rawParts? t
  let (fires, fewest) := needlessRawHashes hashes (longestHashRun body)
  guard fires
  let hs := String.ofList (List.replicate fewest.toNat '#')
  return s!"r{hs}\"{String.ofList body}\"{hs}"

/-- A raw literal with more `#`s than it needs, as the text of its fix. -/
def needlessRawHashesMsg (fixed : String) : Msg :=
  { code? := some Lint.needlessRawStringHashes.code, headline := "this raw string literal has more `#`s than it needs"
    label? := some "fewer `#`s would do"
    notes := #["note: a raw literal needs one `#` more than the longest run of `#` after a `\"` in it, and none without a `\"`"]
    fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

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
  | div
  deriving Inhabited, BEq, DecidableEq, Repr

def IdentityOperator.ofOp? : String → Option IdentityOperator
  | "+" => some .add
  | "-" => some .sub
  | "*" => some .mul
  | "div" => some .div
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
  | .div => if right == .one then .keepLeft else .unchanged
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
  | .inter, true | .minus, true | .subset, true => false
  | .mul, _ => (left matches .zero) || (right matches .zero)
  | .inter, _ | .join, _ => (left matches .empty) || (right matches .empty)
  | .minus, _ | .subset, _ => (left matches .empty)
  | .in, _ => (right matches .empty)
  | _, _ => false

/-- Whether `erasing_op` fires on `a div k` or `a mod k`, from the value of
`a` if it is an integer literal, possibly negated (`lint::erasing_division`). -/
def erasingDivision (dividend : Option Int) : Bool := dividend == some 0

/-- `0 div k` or `0 mod k`, for `op`, `div` or `mod`. -/
def erasingDivisionMsg (op : String) : Msg :=
  { code? := some Lint.erasingOp.code, headline := s!"this `{op}` is always `0`", label? := some "divides `0`"
    notes := #["note: the dividend is probably not the one meant"] }

/-- The value that `a OP b` always has where `erasing_op` fires. -/
def erasingOpValue : InfixOp → String
  | .mul => "0"
  | .in => "false"
  | .subset => "true"
  | _ => "{}"

def erasingOpMsg (op : InfixOp) : Msg :=
  { code? := some Lint.erasingOp.code, headline := s!"this `{op.op}` is always `{erasingOpValue op}`"
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
text at `ref`, or from `ref` to `last?`, which ends it. -/
structure OpReport (α : Type) where
  lint : Lint
  ref : α
  msg : Msg
  last? : Option α := none
  /-- `fren fix` leaves this fix where it fixes this lint at this
  expression, whose fix overlaps it. -/
  unless? : Option (Lint × α) := none
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

/-- The words that start an expression or a path, which a bound name
cannot be, though they are not reserved. -/
def expressionWords : List String := ["when", "unless", "not", "true", "false", "self", "super"]

/-- Whether `n` is directly in parentheses of its own within `parent`:
the parentheses of an application, written right after its name, are not
around its argument alone. -/
def inOwnParens (src : Array Char) (n : BNode α) (parent : Range) : Bool :=
  let call (r : Range) : Bool := Id.run do
    let mut i := r.start
    while i > 0 && isWordChar src[i - 1]! do i := i - 1
    let w := textOf src { start := i, stop := r.start }
    return !w.isEmpty && !reservedWords.contains w && !expressionWords.contains w
  (parensAround? src parent n.range).any (!call ·)

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

/-- The least value of `n`, a call of a method whose values have a least
one, and the method (`Reqs/Lint/Pedantic#ranges-of-methods`): `index_of`,
which is never below `-1`, and `abs`, never below `0`, which `isAbs` says
`n` is, since `x.abs` is written as a field read is. -/
def leastValue? (isAbs : α → Bool) (n : BNode α) : Option (String × Int) :=
  match n.kind, n.kids.size with
  | .method "index_of", 3 => some ("index_of", -1)
  | .atom, _ | .method "abs", 1 => if isAbs n.ref then some ("abs", 0) else none
  | _, _ => none

/-- Whether `invalid_upcast_comparisons` fires on a comparison of a call
that is never below `least` with `bound`, `call OP bound` if `callLeft` and
`bound OP call` otherwise, and what it always is where it fires
(`lint::invalid_upcast_comparisons`): the call is above `bound`, or, for
`least`, the same or above. -/
def invalidUpcast (op : Comparison) (bound least : Int) (callLeft : Bool) : Bool × Bool :=
  match if callLeft then op else op.mirror with
  | .lt => (bound ≤ least, false)
  | .ge => (bound ≤ least, true)
  | .eq | .le => (bound < least, false)
  | .ne | .gt => (bound < least, true)

/-- A comparison of a call of `method`, never below `least`, that is always
`value`. -/
def invalidUpcastMsg (method : String) (least : Int) (value : Bool) : Msg :=
  { code? := some Lint.invalidUpcastComparisons.code, headline := s!"this comparison is always `{value}`"
    label? := some s!"`{method}` is never below {least}"
    notes := #["note: the bound or the operator is probably not the one meant"] }

/-- `invalid_upcast_comparisons` on `n`, a comparison, where `isAbs` says
which expressions are calls of `abs` (`lint::invalid_upcast_comparisons`). -/
def invalidUpcastAt? (src : Array Char) (isAbs : α → Bool) (n : BNode α) : Option (OpReport α) := do
  let .bin op := n.kind | none
  let c ← Comparison.ofOp? op
  let #[a, b] := n.kids | none
  let (call, other, left) := if (leastValue? isAbs a).isSome then (a, b, true) else (b, a, false)
  let (method, least) ← leastValue? isAbs call
  let (fires, value) := invalidUpcast c (← intLiteral? src other) least left
  unless fires do none
  return { lint := .invalidUpcastComparisons, ref := n.ref, msg := invalidUpcastMsg method least value }

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

/-- Whether the text of `src` in `r` (`textOf`) has more than two
characters other than whitespace, and no `-` or `/`. Then it has no
comment, so `writtenForm` keeps each of those characters, and its form is
longer than two characters. -/
def formLongerThanTwo (src : Array Char) (r : Range) : Bool :=
  go (min r.stop src.size) r.start 0
where
  go (stop i seen : Nat) : Bool :=
    if h : i < stop then
      let c := src[i]!
      if c == '-' || c == '/' then false
      else if c.isWhitespace then go stop (i + 1) seen
      else if seen == 2 then
        -- A third character; the rest of the text must still have no `-`
        -- or `/`, since a comment could start there.
        rest stop (i + 1)
      else go stop (i + 1) (seen + 1)
    else false
  termination_by stop - i
  rest (stop i : Nat) : Bool :=
    if h : i < stop then
      let c := src[i]!
      if c == '-' || c == '/' then false else rest stop (i + 1)
    else true
  termination_by stop - i

/-- How `identity_op` sees the operand `k`. -/
def identityOperand (src : Array Char) (k : BNode α) : IdentityOperand :=
  match k.kind with
  | .neg => .negation
  -- Only an atom's text is read, and not even that when it is surely
  -- longer than the forms below (`formLongerThanTwo`).
  | .atom => if formLongerThanTwo src k.range then .other else match writtenForm (textOf src k.range) with
    | "0" => .zero
    | "1" => .one
    | "\"\"" | "[]" | "{}" => .empty
    | _ => .other
  | _ => .other

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

/-- Whether `branches_sharing_code` fires on `if C then A op X else B op X`,
or `X op A` and `X op B`, from whether both branches apply the same binary
operator, whether their left, and their right, operands are written the
same, both being `same_branches`, and whether the fix would be `nonlinear`
(`branchesSharingNonlinear`) (`lint::branches_sharing_code`). -/
def branchesSharingCode (sameOp sharedLeft sharedRight nonlinear : Bool) : Bool :=
  sameOp && sharedLeft != sharedRight && !nonlinear

/-- Whether the fix of `branches_sharing_code` for the operator `op`, whose
shared operand is on the left if `left`, is outside the arithmetic that
Fren accepts: for `*`, the product of the `if` that the fix moves out,
which mentions `ifMentioned`, with the shared operand, which mentions
`sharedMentioned`, is not accepted (`lang::linear_product`); for `div` and
`mod`, the `if` would be the divisor, which must be a literal or a
constant (`lang::divisor`). -/
def branchesSharingNonlinear (op : String) (left : Bool) (ifMentioned sharedMentioned : List Mention) : Bool :=
  if op == "div" || op == "mod" then left else op == "*" && !productAccepted ifMentioned sharedMentioned

/-- `if C then A op X else B op X`, or the mirror form if `left`, whose
shared operand is written `x`, as the text of its fix. -/
def branchesSharingCodeMsg (op x fixed : String) (left : Bool) : Msg :=
  { code? := some Lint.branchesSharingCode.code
    headline := if left then s!"both branches of this `if` start with `{x} {op}`"
      else s!"both branches of this `if` end with `{op} {x}`"
    label? := some "the same operand in both branches"
    notes := #[s!"note: `{x}` is evaluated whichever branch is taken, and has the same value in both"]
    fixes := #[{ msg := "move it out of the `if`", replacement := fixed }] }

/-- `branches_sharing_code` on `n`, a conditional in `slot` within `parent`,
where `mentioned` is what an expression mentions, as far as the lint needs
it: what a condition or an operand of `*` mentions
(`lint::branches_sharing_code`). -/
def branchesSharingAt? (src : Array Char) (mentioned : α → List Mention) (n : BNode α) (slot : Option Slot) (parent : Range) :
    Option (OpReport α) := do
  let #[c, a, b] := n.kids | none
  let .bin op := a.kind | none
  let #[a1, a2] := a.kids | none
  let #[b1, b2] := b.kids | none
  let same (x y : BNode α) := writtenSame (textOf src x.range) (textOf src y.range)
  let left := same a1 b1
  -- The operands that the fix moves into an `if`, and the shared one.
  let (ka, kb, kx) := if left then (a2, b2, a1) else (a1, b1, a2)
  let nonlinear := branchesSharingNonlinear op left (mentioned c.ref ++ mentioned ka.ref ++ mentioned kb.ref) (mentioned kx.ref)
  unless branchesSharingCode (b.kind == .bin op) left (same a2 b2) nonlinear do none
  let k := BKind.bin op
  -- The branches without the shared operand, with the parentheses they are written with.
  let (x, ta, tb) := if left then (operandText src a.range a1, operandText src a.range a2, operandText src b.range b2)
    else (operandText src a.range a2, operandText src a.range a1, operandText src b.range b1)
  let ite : BText := { text := s!"if {textOf src c.range} then {ta} else {tb}", prec := BKind.ite.prec }
  let text := if left then s!"{x} {op} {ite.inSlot (k.slots[1]?.join)}" else s!"{ite.inSlot (k.slots[0]?.join)} {op} {x}"
  let fixed := placed src n slot parent { text, prec := k.prec }
  return { lint := .branchesSharingCode, ref := n.ref, msg := branchesSharingCodeMsg op x fixed left }

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

/-- Whether `contradictory_comparisons` fires on `a OP₁ x OP₂ b` within a
chained comparison, where `a` and `b` are integers: on `x OP₁' a and x OP₂
b`, with `OP₁'` the mirror of `OP₁` (`lint::contradictory_chain`). -/
def contradictoryChain (c1 : Comparison) (a : Int) (c2 : Comparison) (b : Int) : Bool :=
  contradictoryComparisons true c1.mirror a c2 b

/-- `contradictory_comparisons` on `n`, a chained comparison of `ops`: at
each operand between two integer literals (`lint::contradictory_chain`). -/
def contradictoryChainAt? (src : Array Char) (n : BNode α) (ops : Array String) : Option (OpReport α) := do
  guard (n.kids.size == ops.size + 1)
  let fires := (List.range (ops.size - 1)).any fun i => Id.run do
    let (some c1, some c2) := (Comparison.ofOp? ops[i]!, Comparison.ofOp? ops[i + 1]!) | return false
    let (some a, some b) := (n.kids[i]?.bind (intLiteral? src ·), n.kids[i + 2]?.bind (intLiteral? src ·))
      | return false
    return contradictoryChain c1 a c2 b
  guard fires
  let msg := contradictoryMsg true
  return { lint := .contradictoryComparisons, ref := n.ref
           msg := { msg with notes := #["note: a bound may not be the one meant, or the chain may order the wrong way"] } }

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

/-- Why `overly_complex_bool_expr` drops an operand (`lint::BoolRule`). -/
inductive BoolRule where
  /-- `a or (a and b)` is `a`, and `a and (a or b)` is `a`. -/
  | absorption
  /-- `a and not a` is `false`. -/
  | contradiction
  /-- `a or not a` is `true`. -/
  | excludedMiddle
  deriving Inhabited, BEq, DecidableEq, Repr

/-- Whether `overly_complex_bool_expr` fires on an `and`, if `conj`, or an
`or`, and by which rule, from whether an operand absorbs the other, whether
one is the other's negation, and whether `nonminimal_bool` rewrites that
negation (`lint::overly_complex_bool_expr`). -/
def overlyComplexBool (conj absorbs negates simplerNegation : Bool) : Bool × BoolRule :=
  (absorbs || (negates && !simplerNegation),
    if absorbs then .absorption else if conj then .contradiction else .excludedMiddle)

/-- `overly_complex_bool_expr` by `rule`, on an `and`, if `conj`, or an
`or`, whose fix is `fixed`. -/
def overlyComplexBoolMsg (conj : Bool) (rule : BoolRule) (fixed : String) (range? : Option Range := none) : Msg :=
  let op := if conj then "and" else "or"
  let (headline, label, note) := match rule with
    | .absorption => (s!"this `{op}` has an operand that does not change its value", "the other operand decides it",
      "note: `a or (a and b)` is `a`, and `a and (a or b)` is `a`")
    | .contradiction => ("this `and` is always `false`", "an operand and its negation",
      "note: one of the operands is probably not the one meant")
    | .excludedMiddle => ("this `or` is always `true`", "an operand and its negation",
      "note: one of the operands is probably not the one meant")
  { code? := some Lint.overlyComplexBoolExpr.code, headline, label? := some label, notes := #[note]
    fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed, range? }] }

/-- `overly_complex_bool_expr` on `n`, an `and` if `conj`, or an `or`, in
`slot` within `parent` (`lint::overly_complex_bool_expr`). -/
def overlyComplexAt? (src : Array Char) (n : BNode α) (slot : Option Slot) (parent : Range) (conj : Bool) :
    Option (OpReport α) := do
  let #[l, r] := n.kids | none
  let same (a b : BNode α) := writtenSame (textOf src a.range) (textOf src b.range)
  -- `k` is `p or q` in an `and`, or `p and q` in an `or`, where `p` or `q` is `o`.
  let absorbs (k o : BNode α) := k.kind == .bin (if conj then "or" else "and") && k.kids.any (same · o)
  let kept? := if absorbs r l then some l else if absorbs l r then some r else none
  let negates (k o : BNode α) := k.kind == .not && k.kids.any (same · o)
  let negation? := if negates r l then some r else if negates l r then some l else none
  let simpler := negation?.any fun k => ((k.toEx 3).simplerForm .nonminimalBool).isSome
  let (fires, rule) := overlyComplexBool conj kept?.isSome negation?.isSome simpler
  unless fires do none
  let t ← match rule, kept? with
    | .absorption, some k => some (k.text src)
    | .absorption, none => none
    | _, _ => some { text := toString (rule == .excludedMiddle), prec := BKind.atom.prec }
  -- An operand in parentheses: the fix replaces them too, and has the
  -- parentheses that its slot needs, rather than keeping those of `n`.
  match slot, parensAround? src parent n.range with
  | some _, some _ =>
    let outer := withParensIn src parent n.range
    let fixed := t.inSlot slot (followedAt src outer)
    return { lint := .overlyComplexBoolExpr, ref := n.ref, msg := overlyComplexBoolMsg conj rule fixed (some outer) }
  | _, _ =>
    let fixed := placed src n slot parent t
    return { lint := .overlyComplexBoolExpr, ref := n.ref, msg := overlyComplexBoolMsg conj rule fixed }

/-- `erasing_op` on `n`, a binary operator (`lint::erasing_op`). -/
def erasingOpAt? (src : Array Char) (n : BNode α) : Option (OpReport α) := do
  let .bin op := n.kind | none
  if op == "div" || op == "mod" then
    let #[a, _] := n.kids | none
    guard (erasingDivision (intLiteral? src a))
    return { lint := .erasingOp, ref := n.ref, msg := erasingDivisionMsg op }
  let o ← InfixOp.ofOp? op
  let #[a, b] := n.kids | none
  -- `erasingOp` reads `same` only for these operators.
  let same := (o matches .inter | .minus | .subset) && writtenSame (textOf src a.range) (textOf src b.range)
  unless erasingOp o (identityOperand src a) (identityOperand src b) same do none
  return { lint := .erasingOp, ref := n.ref, msg := erasingOpMsg o }

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

/-- Whether `chainable_comparison` joins the conjuncts `l and r`, and
whether its fix writes `l`, and `r`, the other way round
(`lint::chainable_comparison`): from whether each orders ascending, with
`<` and `<=`, whether each is one comparison, and which of their first and
last operands are written the same. -/
def chainableComparison (lAsc rAsc lSingle rSingle lastFirst firstLast firstFirst lastLast : Bool) :
    Bool × Bool × Bool :=
  let keep := lAsc == rAsc && lastFirst && !firstLast
  let flipLeft := lSingle && lAsc != rAsc && firstFirst && !lastLast
  let flipRight := rSingle && lAsc != rAsc && lastLast && !firstFirst
  let flipBoth := lSingle && rSingle && lAsc == rAsc && firstLast && !lastFirst
  (keep || flipLeft || flipRight || flipBoth, flipLeft || flipBoth, flipRight || flipBoth)

/-- `chainable_comparison`'s message, whose fix is `fixed`, or none but a
note if a comment between the comparisons would be lost (`commented`). -/
def chainableComparisonMsg (fixed : String) (commented : Bool) : Msg :=
  { code? := some Lint.chainableComparison.code, headline := "these comparisons can be chained"
    label? := some "comparisons that share an operand"
    notes := if commented then #[s!"help: write `{fixed}`",
      "note: `fren fix` leaves this, since the chain would lose the comment between the comparisons"] else #[]
    fixes := if commented then #[] else #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

/-- A conjunct that `chainable_comparison` can join: a comparison that
orders, or a chained comparison, as its operands and operators. -/
structure ChainPart (α : Type) where
  operands : Array (BNode α)
  ops : Array String

def ChainPart.ascending (p : ChainPart α) : Bool := p.ops.all (· matches "<" | "<=")

/-- The conjunct, written the other way round: `a < b` as `b > a`. -/
def ChainPart.flip (p : ChainPart α) : ChainPart α :=
  { operands := p.operands.reverse
    ops := p.ops.reverse.map fun op => ((Comparison.ofOp? op).map (·.mirror.op)).getD op }

/-- `n` as a conjunct that `chainable_comparison` can join, if it is one. -/
def chainPart? (n : BNode α) : Option (ChainPart α) :=
  match n.kind with
  | .bin op => if ["<", "<=", ">", ">="].contains op && n.kids.size == 2 then some ⟨n.kids, #[op]⟩ else none
  | .chain ops => if ops.size + 1 == n.kids.size then some ⟨n.kids, ops⟩ else none
  | _ => none

/-- The text of the chained comparison of `operands` and `ops`, each
operand in parentheses where it needs them, where `followed` says whether
an operator follows it. -/
def chainText (src : Array Char) (operands : Array (BNode α)) (ops : Array String) (followed : Bool) : BText :=
  let slots := (BKind.chain ops).slots
  let texts := operands.mapIdx fun i k => (k.text src).inSlot (slots[i]?.join) (i + 1 < operands.size || followed)
  let rest := (ops.zip (texts.extract 1)).foldl (fun acc (op, t) => s!"{acc} {op} {t}") (texts[0]?.getD "")
  { text := rest, prec := (BKind.chain ops).prec }

/-- The conjuncts of the run of `and` that `n` is the top of, in order:
through each left operand that is an `and` not in parentheses. -/
partial def conjuncts (src : Array Char) (n : BNode α) : Array (BNode α) :=
  match n.kind, n.kids with
  | .bin "and", #[l, r] =>
    (if l.kind == .bin "and" && !enclosed src n.range l.range then conjuncts src l else #[l]).push r
  | _, _ => #[n]

/-- `chainable_comparison` on `n`, an `and` in `slot` within `parent`, if
it is the top of a run of `and` (`lint::chainable_comparison`): one
report for each run of adjacent conjuncts that chain, from the first to
the last, which are not in parentheses. -/
def chainableAt [Inhabited α] (src : Array Char) (n : BNode α) (slot : Option Slot) (parent : Range) : Array (OpReport α) := Id.run do
  let inRun := slot.any (fun s => s.outer == (BKind.bin "and").prec && !s.right) && !enclosed src parent n.range
  if n.kind != .bin "and" || inRun then return #[]
  let cs := conjuncts src n
  let form (k : BNode α) := writtenForm (textOf src k.range)
  let bare (k : BNode α) := !enclosed src n.range k.range
  let mut out := #[]
  -- The run so far: its first conjunct, the chain, and how many it joins.
  let mut run : Option (Nat × ChainPart α × Nat) := none
  for i in [0:cs.size] do
    let k := cs[i]!
    let next? := if bare k then chainPart? k else none
    let joined? := do
      let (start, l, m) ← run
      let r ← next?
      let lSingle := m == 1 && l.ops.size == 1
      let (fires, fl, fr) := chainableComparison l.ascending r.ascending lSingle (r.ops.size == 1)
        (form l.operands.back! == form r.operands[0]!) (form l.operands[0]! == form r.operands.back!)
        (form l.operands[0]! == form r.operands[0]!) (form l.operands.back! == form r.operands.back!)
      guard fires
      let l := if fl then l.flip else l
      let r := if fr then r.flip else r
      pure (start, ({ operands := l.operands ++ r.operands.extract 1, ops := l.ops ++ r.ops } : ChainPart α), m + 1)
    match joined? with
    | some j => run := some j
    | none =>
      if let some (start, c, m) := run then if m ≥ 2 then out := out.push (start, i - 1, c)
      run := next?.map (i, ·, 1)
  if let some (start, c, m) := run then if m ≥ 2 then out := out.push (start, cs.size - 1, c)
  return out.map fun (a, b, c) =>
    let whole := a == 0 && b + 1 == cs.size
    let range : Range := { start := cs[a]!.range.start, stop := cs[b]!.range.stop }
    let t := chainText src c.operands c.ops (followedAt src range)
    let fixed := if whole then placed src n slot parent t else t.text
    let commented := (withoutComments (textOf src range)).length != (textOf src range).length
    { lint := .chainableComparison, ref := cs[a]!.ref, last? := some cs[b]!.ref, msg := chainableComparisonMsg fixed commented }

/-! ## Cardinality, ordered enumerations and newtypes -/

/-- What an elaborator knows of an expression that the lints of ordered
enumerations and newtypes read. -/
inductive NodeFact where
  /-- A variant of the ordered enumeration `enum`, the one at `pos`,
  from 0, of its `count`. -/
  | ordinal (enum : String) (pos count : Nat)
  /-- `Ms(e)`, which builds a value of the newtype `newtype`, where
  `synthesizes` says that `e` has a type of its own, rather than one taken
  from where it is written, as `[]` and `{}` do. -/
  | wraps (newtype : String) (synthesizes : Bool)
  /-- `x.0`, which reads the field of a value of the newtype `newtype`. -/
  | unwraps (newtype : String)
  /-- An `and` whose operands give a definedness obligation: an index, a
  table, or a name whose definition gives one (`Reqs/Lang/Expressions#sequences`). -/
  | obligations
  /-- An equation or a disequation whose operands are `Nat`s. -/
  | natOperands
  deriving Inhabited, BEq, Repr

/-- Whether the text at `i` in `src` starts with `s`. -/
def startsWithAt (src : Array Char) (i : Nat) (s : String) : Bool :=
  (s.foldl (init := (true, i)) fun (ok, k) c => (ok && src[k]? == some c, k + 1)).1

/-- Whether `n` applies a cardinality operator, `some true` for
`exactly_one?` and `some false` for `at_most_one?`: their names are
reserved, so an application written with one is theirs. -/
def cardinalityCall? (src : Array Char) (n : BNode α) : Option Bool :=
  if n.kind != .atom then none
  else if startsWithAt src n.range.start "exactly_one?(" then some true
  else if startsWithAt src n.range.start "at_most_one?(" then some false
  else none

def cardinalityName (exactly : Bool) : String := if exactly then "exactly_one?" else "at_most_one?"

/-- Whether `nonminimal_bool` fires on a cardinality operator of `n`
arguments, and whether its fix is the argument, rather than `true`
(`lint::nonminimal_cardinality`). -/
def nonminimalCardinality (exactly : Bool) (n : Nat) : Bool × Bool := (decide (n = 1), exactly)

/-- Whether `eq_op` fires on the argument `arg` of a cardinality operator,
as written, or `none` for a literal, from the arguments before it that are
not literals (`lint::eq_op_cardinality`). -/
def eqOpCardinality [DecidableEq β] (earlier : List β) (arg : Option β) : Bool :=
  match arg with
  | some x => earlier.contains x
  | none => false

/-- `eq_op` on the argument `arg` of a cardinality operator, written the
same as an earlier one. -/
def eqOpCardinalityMsg (exactly : Bool) (arg : String) : Msg :=
  { code? := some Lint.eqOp.code, headline := s!"`{arg}` is an argument of `{cardinalityName exactly}` more than once"
    label? := some "written the same as an earlier argument"
    notes := #[s!"note: the call holds only where `{arg}` is `false`, so one of the two is probably not the one meant"] }

/-- `nonminimal_bool` and `eq_op` on `n`, a cardinality operator, in
`slot` within `parent` (`lint::nonminimal_cardinality`,
`lint::eq_op_cardinality`). -/
def cardinalityAt? (src : Array Char) (n : BNode α) (slot : Option Slot) (parent : Range) : Option (OpReport α) := do
  let exactly ← cardinalityCall? src n
  let (single, operand) := nonminimalCardinality exactly n.kids.size
  if let (true, some a) := (single, n.kids[0]?) then
    let fixed := if operand then placed src n slot parent (a.text src) else "true"
    let label := if operand then s!"`{cardinalityName exactly}` of one argument is that argument"
      else s!"`{cardinalityName exactly}` of one argument always holds"
    return { lint := .nonminimalBool, ref := n.ref
             msg := { code? := some Lint.nonminimalBool.code, headline := "this `Bool` expression can be simpler"
                      label? := some label, fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed }] } }
  -- A literal is left to the lints of constants.
  let forms := n.kids.map fun k => if k.kind matches .lit _ then none else some (writtenForm (textOf src k.range))
  let j? := (List.range forms.size).find? fun j => eqOpCardinality ((forms.extract 0 j).toList.filterMap id) forms[j]!
  let k ← n.kids[← j?]?
  return { lint := .eqOp, ref := k.ref, msg := eqOpCardinalityMsg exactly (textOf src k.range) }

/-- The operands of the run of `op`, `and` or `or`, that `n` is the top
of, in order: through each left operand that is an `op` not in
parentheses, as `conjuncts` reads a run of `and`. -/
partial def runOperands (op : String) (src : Array Char) (n : BNode α) : Array (BNode α) :=
  match n.kind, n.kids with
  | .bin o, #[l, r] =>
    if o != op then #[n] else
    (if l.kind == .bin op && !enclosed src n.range l.range then runOperands op src l else #[l]).push r
  | _, _ => #[n]

/-- Whether `n`, an `op` in `slot` within `parent`, is the top of its run
of `op`: not the left operand of another, outside parentheses. -/
def runTop (op : String) (src : Array Char) (n : BNode α) (slot : Option Slot) (parent : Range) : Bool :=
  n.kind == .bin op && !(slot.any (fun s => s.outer == (BKind.bin op).prec && !s.right) && !enclosed src parent n.range)

/-- A conjunct `not (first and second)`, of operands `β`, where
`obligation` says that the `and` gives a definedness obligation
(`lint::PairNegation`). -/
structure PairNeg (β : Type) where
  first : β
  second : β
  obligation : Bool

/-- Whether `manual_at_most_one` fires on the conjuncts `ps`, and whether its
fix is `exactly_one?` rather than `at_most_one?`, where `disj` is the
disjunction beside them, if any (`lint::manual_at_most_one`), of conjuncts
`γ` read by `first`, `second` and `obligation`: they name three different
operands or more, none twice in one conjunct, and negate each pair of two
different ones, and no `and` gives an obligation; the fix is
`exactly_one?` if `disj` has exactly the operands they name. -/
def manualAtMostOne [DecidableEq β] (first second : γ → β) (obligation : γ → Bool) (ps : List γ) (disj : List β) :
    Bool × Bool :=
  let os := ps.flatMap fun p => [first p, second p]
  let negated (x y : β) := ps.any fun p => first p == x && second p == y
  (os.any (fun x => os.any fun y => os.any fun z => x != y && x != z && y != z)
      && ps.all (fun p => first p != second p)
      && os.all (fun x => os.all fun y => x == y || negated x y || negated y x)
      && !ps.any obligation,
    disj.any (fun _ => true) && disj.all (os.contains ·) && os.all (disj.contains ·))

/-- `manual_at_most_one`'s message, whose fix is `fixed`, at `range`, the
conjuncts with the parentheses around the disjunction, or none but a note
if a comment within them would be lost (`commented`). -/
def manualAtMostOneMsg (exactly : Bool) (n : Nat) (fixed : String) (range : Range) (commented : Bool) : Msg :=
  { code? := some Lint.manualAtMostOne.code, headline := s!"this is `{cardinalityName exactly}` of {n} operands"
    label? := some (if exactly then s!"says that one of {n} operands holds, and negates each pair" else s!"negates each pair of {n} operands")
    notes := if commented then #[s!"help: write `{fixed}`",
      "note: `fren fix` leaves this, since the call would lose the comment within the conjuncts"] else #[]
    fixes := if commented then #[] else #[{ msg := s!"write `{fixed}`", replacement := fixed, range? := some range }] }

/-- `manual_at_most_one` on `n`, an `and` in `slot` within `parent`, if it
is the top of a run of `and` (`lint::manual_at_most_one`): one report for
each longest run of adjacent conjuncts `not (a and b)`, not in
parentheses, with the disjunction of their operands just before or after
it, if there is one. The message is reported from the first conjunct it
replaces to the last. -/
def manualAtMostOneAt [Inhabited α] (src : Array Char) (fact? : α → Option NodeFact) (n : BNode α) (slot : Option Slot)
    (parent : Range) :
    Array (OpReport α) := Id.run do
  unless runTop "and" src n slot parent do return #[]
  let cs := runOperands "and" src n
  let bare (k : BNode α) := !enclosed src n.range k.range
  let form (k : BNode α) := writtenForm (textOf src k.range)
  let pair? (k : BNode α) : Option (BNode α × BNode α) := do
    guard (bare k)
    let (.not, #[i]) := (k.kind, k.kids) | none
    let (.bin "and", #[a, b]) := (i.kind, i.kids) | none
    pure (a, b)
  let mut out := #[]
  let mut i := 0
  while i < cs.size do
    if (pair? cs[i]!).isNone then
      i := i + 1
      continue
    let mut j := i
    while j + 1 < cs.size && (pair? cs[j + 1]!).isSome do j := j + 1
    let pairs := (cs.extract i (j + 1)).filterMap pair?
    -- Each conjunct, its operands as written, and whether its `and` gives
    -- an obligation, as the elaborator says.
    let model := (cs.extract i (j + 1)).toList.filterMap fun c => do
      let (a, b) ← pair? c
      pure ({ first := form a, second := form b
              obligation := c.kids.any fun k => fact? k.ref == some .obligations } : PairNeg String)
    -- The operands, each once, in the order they are first written.
    let dedup (ks : Array (BNode α)) := ks.foldl (init := (#[] : Array (BNode α))) fun acc k =>
      if acc.any (form · == form k) then acc else acc.push k
    let ops := dedup (pairs.flatMap fun (a, b) => #[a, b])
    -- The disjunction just before or after, in the parentheses that an
    -- operand of `and` needs, if the fix is `exactly_one?` with it.
    let disj? (k : Nat) : Option (Array (BNode α)) := do
      let c ← cs[k]?
      guard (c.kind == .bin "or")
      let ds := runOperands "or" src c
      guard (manualAtMostOne PairNeg.first PairNeg.second PairNeg.obligation model (ds.toList.map form)).2
      pure ds
    let (first, last, disjunction?) := match (if i > 0 then disj? (i - 1) else none), disj? (j + 1) with
      | some ds, _ => (i - 1, j, some ds)
      | none, some ds => (i, j + 1, some ds)
      | none, none => (i, j, none)
    let (fires, exactly) := manualAtMostOne PairNeg.first PairNeg.second PairNeg.obligation model ((disjunction?.getD #[]).toList.map form)
    if fires then
      let args := (dedup (disjunction?.getD ops)).map fun o => textOf src o.range
      let fixed := s!"{cardinalityName exactly}({", ".intercalate args.toList})"
      let range : Range := { start := (withParensIn src n.range cs[first]!.range).start
                             stop := (withParensIn src n.range cs[last]!.range).stop }
      let commented := hasComment (textOf src range)
      out := out.push { lint := .manualAtMostOne, ref := cs[first]!.ref, last? := some cs[last]!.ref
                        msg := manualAtMostOneMsg exactly ops.size fixed range commented }
    i := j + 1
  return out

/-- The variant of an ordered enumeration that `k` is, if it is one, as
its enumeration, its position and the number of variants. -/
def ordinalOf? (fact? : α → Option NodeFact) (k : BNode α) : Option (String × Nat × Nat) :=
  match fact? k.ref with
  | some (.ordinal e p c) => some (e, p, c)
  | _ => none

/-- The comparison and the position of the variant that `manual_ordering`'s
fix is, if it fires on a test that an operand is one of the variants at
`named` of an ordered enumeration of `count`, or, if `negated`, none of
them (`lint::manual_ordering`): where they are two or more, but not all,
and the first variants, the fix compares with the last of them, and where
they are the last, with the first of them. -/
def manualOrdering (count : Nat) (named : List Nat) (negated : Bool) : Option (Comparison × Nat) :=
  let has (v : Nat) := named.contains v
  let k := ((List.range count).filter has).length
  if k < 2 || k ≥ count then none
  else if (List.range count).all (fun v => has v == decide (v < k)) then some (if negated then .gt else .le, k - 1)
  else if (List.range count).all (fun v => has v == decide (count - k ≤ v)) then
    some (if negated then .lt else .ge, count - k)
  else none

/-- `manual_ordering`'s message, whose fix is `fixed`, from whether the
variants are the first of the enumeration, and whether the test is that
the operand is none of them. -/
def manualOrderingMsg (fixed : String) (first negated : Bool) (named : Nat) : Msg :=
  { code? := some Lint.manualOrdering.code, headline := s!"this is `{fixed}`"
    label? := some s!"{if negated then "excludes" else "names"} the {if first then "first" else "last"} {named} variants of an ordered enumeration"
    notes := #["note: they differ once a variant is added among those named: the comparison takes it in, and the test does not"]
    fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

/-- `manual_ordering` on `n`, in `slot` within `parent`, where `x` is the
operand and `vs` the variants it is tested against, and `negated` says
that the test is that it is none of them (`lint::manual_ordering`). -/
def manualOrderingOf? (src : Array Char) (fact? : α → Option NodeFact) (n x : BNode α) (vs : Array (BNode α))
    (negated : Bool) (slot : Option Slot) (parent : Range) : Option (OpReport α) := do
  let ords ← vs.mapM (ordinalOf? fact?)
  let (e, _, count) ← ords[0]?
  guard (ords.all fun (e', _, c) => e' == e && c == count)
  let ps := ords.map (·.2.1)
  let (c, target) ← manualOrdering count ps.toList negated
  let first := c matches .le | .gt
  let k ← (ps.findIdx? (· == target)).bind (vs[·]?)
  let fixed := placed src n slot parent (binText c.op (x.text src) (k.text src))
  let named := ((List.range count).filter (ps.contains ·)).length
  return { lint := .manualOrdering, ref := n.ref, msg := manualOrderingMsg fixed first negated named }

/-- `manual_ordering` on `n`, in `slot` within `parent`: `x in {...}`, or
at the top of a run of `or` of `x = V`, or of `and` of `x != V`
(`lint::manual_ordering`). -/
def manualOrderingAt? (src : Array Char) (fact? : α → Option NodeFact) (n : BNode α) (slot : Option Slot)
    (parent : Range) : Option (OpReport α) := do
  match n.kind, n.kids with
  | .bin "in", #[x, s] =>
    guard (s.kind == .atom && startsWithAt src s.range.start "{")
    manualOrderingOf? src fact? n x s.kids false slot parent
  | .bin op, _ =>
    let cmp ← if op == "or" then some "=" else if op == "and" then some "!=" else none
    guard (runTop op src n slot parent)
    let ds := runOperands op src n
    let eqs ← ds.mapM fun d => match d.kind, d.kids with
      | .bin c, #[l, r] => if c == cmp && !enclosed src n.range d.range then some (l, r) else none
      | _, _ => none
    let (x, _) ← eqs[0]?
    guard (eqs.all fun (l, _) => writtenForm (textOf src l.range) == writtenForm (textOf src x.range))
    manualOrderingOf? src fact? n x (eqs.map (·.2)) (op == "and") slot parent
  | _, _ => none

/-! ## Pattern tests written out -/

/-- An alternative of a pattern, as `manual_pattern_test` reads it
(`lint::Alt`): the integers from `lo` to `hi`, where `none` leaves that
side unbounded, so that a literal is a range of one integer; a string
literal, as written; or a variant, by its name, with or without a
payload. -/
inductive PatAlt where
  | ints (lo hi : Option Int)
  | str (s : String)
  | variant (name : String)
  deriving Inhabited, DecidableEq, Repr

/-- Whether the bound `hi` is below the bound `lo`, so that no integer is
at most `hi` and at least `lo`. -/
def boundBelow : Option Int → Option Int → Bool
  | some h, some l => h < l
  | _, _ => false

/-- Whether no value matches both `a` and `b`, as their text shows
(`lint::disjoint?`): two ranges of integers that do not meet, two string
literals written differently, without escape sequences, or two variants
of different names. A pattern's alternatives are of one type, so two
alternatives of different kinds are never both in a pattern that checks,
and are not disjoint here. -/
def PatAlt.disjoint : PatAlt → PatAlt → Bool
  | .ints l1 h1, .ints l2 h2 => boundBelow h1 l2 || boundBelow h2 l1
  | .str s, .str t => s != t && !Fren.Str.contains s "\\" && !Fren.Str.contains t "\\"
  | .variant v, .variant w => v != w
  | _, _ => false

/-- Whether each two alternatives of `as` are disjoint (`PatAlt.disjoint`). -/
def pairwiseDisjoint : List PatAlt → Bool
  | [] => true
  | a :: as => as.all (a.disjoint ·) && pairwiseDisjoint as

/-- Whether `manual_pattern_test` fires on a run of `nOperands` adjacent
operands of `or`, or of `and`, each an equation, or a disequation, of one
expression with a value that a pattern writes, or a pattern test of it,
or its negation, `nEquations` of them equations, whose alternatives are
`alts`, in order, where `chain` says that `membership_chain` reads the
chain they are in (`lint::manual_pattern_test`). -/
def manualPatternTest (alts : List PatAlt) (nOperands nEquations : Nat) (chain : Bool) : Bool :=
  nOperands ≥ 2 && nEquations ≥ 1 && !chain && pairwiseDisjoint alts

/-- The last segment of a path written `p`, with `::` or `.` between its
segments. -/
def lastSegment (p : String) : String :=
  let p := ((p.splitOn "::").getLast?.getD p)
  (p.splitOn ".").getLast?.getD p

/-- An integer literal written `t`, possibly negated, in decimal. -/
def decimalLiteral? (t : String) : Option Int :=
  let w := writtenForm t
  if w.isEmpty || !(w.toList.all fun c => c.isDigit || c == '-') then none else w.toInt?

/-- The value written `t` as a pattern's alternative, if a pattern writes it
as `t` is written: a decimal integer literal, possibly negated, a string
literal without `"` in it, or, where `variant?` gives its name, a variant
without a payload. `true` and `false` are left to `bool_equality`. -/
def valueAlt? (t : String) (variant? : Option String) : Option PatAlt :=
  let t := t.trimAscii.toString
  if let some k := decimalLiteral? t then some (.ints (some k) (some k))
  else if t.length ≥ 2 && t.startsWith "\"" && t.endsWith "\"" && t.toList.count '"' == 2 then some (.str t)
  else (variant?.map lastSegment).map .variant

/-- Whether `t`, written as a value, is one that a pattern writes, as
`membership_chain` asks of each value it puts in a set: as
`valueAlt?` reads it, or `true` or `false`, where `variant` says that it
is a variant without a payload. -/
def patternValue (t : String) (variant : Bool) : Bool :=
  let t := t.trimAscii.toString
  t == "true" || t == "false" || (valueAlt? t (if variant then some t else none)).isSome

/-- Splits `t` at each `|` outside parentheses and string literals. -/
def splitAlternatives (t : String) : Array String := Id.run do
  let mut out := #[]
  let mut cur := ""
  let mut depth : Nat := 0
  let mut inStr := false
  let mut esc := false
  for c in t.toList do
    if inStr then
      cur := cur.push c
      if esc then esc := false
      else if c == '\\' then esc := true
      else if c == '"' then inStr := false
    else if c == '"' then
      inStr := true
      cur := cur.push c
    else if c == '(' then
      depth := depth + 1
      cur := cur.push c
    else if c == ')' then
      depth := depth - 1
      cur := cur.push c
    else if c == '|' && depth == 0 then
      out := out.push cur.trimAscii.toString
      cur := ""
    else cur := cur.push c
  return out.push cur.trimAscii.toString

/-- Whether `t` is a path: identifiers joined by `::`. -/
def isPathText (t : String) : Bool :=
  !t.isEmpty && (t.splitOn "::").all fun s =>
    !s.isEmpty && (s.toList.all fun c => c.isAlphanum || c == '_') && !(s.toList.head?.any Char.isDigit)

/-- A bound of a range written `t`, if it is a decimal integer literal:
`some none` where it is left out. -/
def rangeBound? (t : String) : Option (Option Int) :=
  let t := t.trimAscii.toString
  if t.isEmpty then some none else (decimalLiteral? t).map some

/-- An alternative of a pattern test, written `t`, as `manual_pattern_test`
reads it (`PatAlt`), if it can: an integer literal, a range whose bounds
are integer literals, a string literal, or a variant, applied to patterns
or not. `_`, `true`, `false`, and a range with a constant as a bound are
not read. -/
def patternAlt? (t : String) : Option PatAlt :=
  let t := t.trimAscii.toString
  -- A variant, applied or not, before a range, which a payload may hold.
  let head := (t.splitOn "(").head!.trimAscii.toString
  if t == "_" || t == "true" || t == "false" then none
  else if let some k := decimalLiteral? t then some (.ints (some k) (some k))
  else if t.startsWith "\"" then
    if t.length ≥ 2 && t.endsWith "\"" && t.toList.count '"' == 2 then some (.str t) else none
  else if isPathText head && (head == t || t.endsWith ")") then some (.variant (lastSegment head))
  else if let [lo, hi] := t.splitOn "..=" then do
    let (l, h) := (← rangeBound? lo, ← rangeBound? hi)
    guard (h.isSome)
    some (.ints l h)
  else if let [lo, hi] := t.splitOn ".." then do
    let (l, h) := (← rangeBound? lo, ← rangeBound? hi)
    guard (l.isSome)
    some (.ints l (h.map (· - 1)))
  else none

/-- The alternatives of the pattern written `t`, if `patternAlt?` reads
each, with their texts. -/
def patternAlts? (t : String) : Option (Array (PatAlt × String)) := do
  guard (!hasComment t)
  let t := t.trimAscii.toString
  let t := if t.startsWith "|" then (t.drop 1).toString else t
  (splitAlternatives t).mapM fun a => return (← patternAlt? a, a)

/-- An operand of a run that `manual_pattern_test` reads: the expression it
tests, as written, its alternatives, with their texts, and whether it is
an equation, or a disequation, rather than a pattern test. -/
structure PatternOperand (α : Type) where
  scrutinee : BNode α
  alts : Array (PatAlt × String)
  equation : Bool

/-- `d`, an operand of a run of `or`, or of `and` if `conj`, within `outer`,
as `manual_pattern_test` reads it: `x = v` or `v = x`, `x != v` or `v !=
x` for `and`, where `v` is a value that `valueAlt?` reads, and `x` is
not, and `v` is not negative where `fact?` says that the operands are
`Nat`s, for which a negative alternative is an error; or `x is P`, `not x
is P` for `and`, where `patternAlts?` reads `P`. -/
def patternOperand? (src : Array Char) (variant? : α → Option String) (fact? : α → Option NodeFact) (conj : Bool)
    (d : BNode α) : Option (PatternOperand α) := do
  let nat := fact? d.ref == some .natOperands
  let value? (k : BNode α) : Option PatAlt := do
    let a ← match k.kind with
      | .atom | .neg => valueAlt? (textOf src k.range) (variant? k.ref)
      | _ => none
    if nat && a matches .ints (some (.negSucc _)) _ then none else some a
  match d.kind, d.kids with
  | .bin op, #[l, r] =>
    guard (op == if conj then "!=" else "=")
    match value? l, value? r with
    | none, some a => return { scrutinee := l, alts := #[(a, textOf src r.range)], equation := true }
    | some a, none => return { scrutinee := r, alts := #[(a, textOf src l.range)], equation := true }
    | _, _ => none
  | .not, #[t] =>
    guard conj
    test? t
  | _, _ => if conj then none else test? d
where
  test? (t : BNode α) : Option (PatternOperand α) := do
    let (.patternTest, #[x]) := (t.kind, t.kids) | none
    let rest := (textOf src { start := (withParensIn src t.range x.range).stop, stop := t.range.stop }).trimAscii.toString
    guard (rest.startsWith "is" && ((rest.drop 2).toString.toList.head?.any Char.isWhitespace))
    return { scrutinee := x, alts := ← patternAlts? (rest.drop 2).toString, equation := false }

/-- The operands of the chain of `op` that `n` is the top of, as
`membership_chain` reads it: through each operand that is an `op`, in
parentheses or not. -/
partial def chainOperandsOf (op : String) (n : BNode α) : Array (BNode α) :=
  match n.kind, n.kids with
  | .bin o, #[l, r] => if o == op then chainOperandsOf op l ++ chainOperandsOf op r else #[n]
  | _, _ => #[n]

/-- Whether `membership_chain` reads the chain of `or`, or of `and` if
`conj`, that `n` is the top of: three or more operands, each an equation,
or a disequation, with the same left operand, and some value that is not
one that a pattern writes (`patternValue`), whether or not a later value
indexes a sequence, which that lint also asks. -/
def membershipChainOf (src : Array Char) (variant? : α → Option String) (conj : Bool) (n : BNode α) : Bool := Id.run do
  let ds := chainOperandsOf (if conj then "and" else "or") n
  if ds.size < 3 then return false
  let eqs := ds.filterMap fun d => match d.kind, d.kids with
    | .bin op, #[l, r] => if op == (if conj then "!=" else "=") then some (l, r) else none
    | _, _ => none
  if eqs.size != ds.size then return false
  let some (l0, _) := eqs[0]? | return false
  let left := writtenForm (textOf src l0.range)
  return eqs.all (fun (l, _) => writtenForm (textOf src l.range) == left)
    && eqs.any fun (_, v) => !patternValue (textOf src v.range) (variant? v.ref).isSome

/-- `manual_pattern_test`'s message, on `x` if `conj` is not set, and
otherwise on its negation, whose fix is `fixed`, at `range`, the
operands with the parentheses around them, or none but a note if a
comment within them would be lost (`commented`). -/
def manualPatternTestMsg (x fixed : String) (conj : Bool) (range : Range) (commented : Bool) : Msg :=
  { code? := some Lint.manualPatternTest.code
    headline := if conj then s!"this says that `{x}` matches none of these patterns" else s!"this says that `{x}` matches one of these patterns"
    label? := some (if conj then "disequations of one expression with values that patterns write" else "equations of one expression with values that patterns write")
    notes := if commented then #[s!"help: write `{fixed}`",
      "note: `fren fix` leaves this, since the pattern test would lose the comment within the operands"] else #[]
    fixes := if commented then #[] else #[{ msg := s!"write `{fixed}`", replacement := fixed, range? := some range }] }

/-- `manual_pattern_test` on `n`, an `or`, or an `and` if `conj`, in `slot`
within `parent`, if it is the top of a run of them, where `chain` says
that `membershipChainOf` holds of the chain it is in
(`lint::manual_pattern_test`): one report for each longest run of
adjacent operands that `patternOperand?` reads, of an expression written
the same, from the first to the last. -/
def manualPatternTestAt [Inhabited α] (src : Array Char) (variant? : α → Option String) (fact? : α → Option NodeFact)
    (n : BNode α) (conj : Bool) (chain : Bool) (slot : Option Slot) (parent : Range) : Array (OpReport α) := Id.run do
  let op := if conj then "and" else "or"
  unless runTop op src n slot parent do return #[]
  let cs := runOperands op src n
  let ps := cs.map (patternOperand? src variant? fact? conj)
  let form (p : PatternOperand α) := writtenForm (textOf src p.scrutinee.range)
  let mut out := #[]
  let mut i := 0
  while i < cs.size do
    let some p := ps[i]! | i := i + 1; continue
    let mut j := i
    while j + 1 < cs.size && (ps[j + 1]!.any (form · == form p)) do j := j + 1
    let run := (ps.extract i (j + 1)).filterMap id
    let alts := run.flatMap (·.alts)
    if manualPatternTest (alts.toList.map (·.1)) run.size (run.filter (·.equation)).size chain then
      let x := (p.scrutinee.text src).inSlot (BKind.patternTest.slots[0]!)
      let test := s!"{x} is {" | ".intercalate (alts.toList.map (·.2))}"
      let t : BText := if conj then { text := s!"not {test}", prec := BKind.not.prec }
        else { text := test, prec := BKind.patternTest.prec }
      let whole := i == 0 && j + 1 == cs.size
      -- The whole run, in parentheses that the test does not need, is
      -- replaced with them.
      let outer := withParensIn src parent n.range
      let unwrapped := whole && outer != n.range && t.dropsParens slot (followedAt src outer)
      let range : Range := if unwrapped then outer
        else { start := (withParensIn src n.range cs[i]!.range).start, stop := (withParensIn src n.range cs[j]!.range).stop }
      let fixed := if unwrapped then t.text else if whole then placed src n slot parent t
        else t.inSlot (some ⟨(BKind.bin op).prec, .left, i > 0⟩) (j + 1 < cs.size)
      -- Where `manual_ordering` reports the run too, its fix is made,
      -- if `fren fix` makes it.
      let unless? := if whole && (manualOrderingAt? src fact? n slot parent).isSome then some (.manualOrdering, n.ref)
        else none
      out := out.push { lint := .manualPatternTest, ref := cs[i]!.ref, last? := some cs[j]!.ref, unless?
                        msg := manualPatternTestMsg (textOf src p.scrutinee.range) fixed conj range
                          (hasComment (textOf src range)) }
    i := j + 1
  return out

/-- The variant of an ordered enumeration that `k` is, or that the
newtype `k` builds holds, as its position and the number of variants. -/
def extremeOf? (fact? : α → Option NodeFact) (k : BNode α) : Option (Nat × Nat) :=
  let at_ (k : BNode α) := (ordinalOf? fact? k).map fun (_, p, c) => (p, c)
  match fact? k.ref, k.kids with
  | some (.wraps ..), #[v] => at_ v
  | _, _ => at_ k

/-- Whether `absurd_extreme_comparisons` fires on `x OP v`, or on `v OP x`
if not `right`, where `v` is the variant at `pos` of an ordered
enumeration of `count`, or a newtype of one, and what the comparison
always is (`lint::absurd_ordered`): only the first and the last variants
fix it. -/
def absurdOrdered (op : Comparison) (pos count : Nat) (right : Bool) : Bool × Bool :=
  let first := pos == 0
  let last := pos + 1 == count
  match if right then op else op.mirror with
  | .ge => (first, true)
  | .lt => (first, false)
  | .le => (last, true)
  | .gt => (last, false)
  | _ => (false, false)

/-- A comparison with `v`, the least value of its type if `least` and the
greatest otherwise, that is always `value`. -/
def absurdOrderedMsg (v : String) (least value : Bool) : Msg :=
  { code? := some Lint.absurdExtremeComparisons.code, headline := s!"this comparison is always `{value}`"
    label? := some s!"`{v}` is the {if least then "least" else "greatest"} value of its type"
    notes := #["note: the bound or the operator is probably not the one meant"] }

/-- `absurd_extreme_comparisons` on `n`, a comparison that orders, with
the first or last variant of an ordered enumeration
(`lint::absurd_ordered`). -/
def absurdOrderedAt? (src : Array Char) (fact? : α → Option NodeFact) (n : BNode α) : Option (OpReport α) := do
  let .bin op := n.kind | none
  let #[a, b] := n.kids | none
  let c ← Comparison.ofOp? op
  let try_ (v : BNode α) (right : Bool) : Option (OpReport α) := do
    let (pos, count) ← extremeOf? fact? v
    let (fires, value) := absurdOrdered c pos count right
    guard fires
    let least := if right then c matches .ge | .lt else c matches .le | .gt
    return { lint := .absurdExtremeComparisons, ref := n.ref, msg := absurdOrderedMsg (textOf src v.range) least value }
  try_ b true <|> try_ a false

/-- Whether `unnecessary_min_or_max` fires on `x.min(v)`, or `x.max(v)` if
`max`, where `v` is the variant at `pos` of an ordered enumeration of
`count`, and if it does, whether the call is always `v`, rather than `x`
(`lint::unnecessary_min_or_max`). -/
def unnecessaryMinOrMax (max : Bool) (pos count : Nat) : Option Bool :=
  if pos == 0 then some !max else if pos + 1 == count then some max else none

def unnecessaryMinOrMaxMsg (fixed v : String) (first : Bool) : Msg :=
  { code? := some Lint.unnecessaryMinOrMax.code, headline := s!"this is always `{fixed}`"
    label? := some s!"`{v}` is the {if first then "least" else "greatest"} value of its enumeration"
    fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

/-- `unnecessary_min_or_max` on `n`, a call of `min` or `max`, in `slot`
within `parent` (`lint::unnecessary_min_or_max`). -/
def minOrMaxAt? (src : Array Char) (fact? : α → Option NodeFact) (n : BNode α) (slot : Option Slot)
    (parent : Range) : Option (OpReport α) := do
  let .method m := n.kind | none
  guard (m == "min" || m == "max")
  let #[x, v] := n.kids | none
  let (_, p, count) ← ordinalOf? fact? v
  let first := p == 0
  let toV ← unnecessaryMinOrMax (m == "max") p count
  let fixed := placed src n slot parent ((if toV then v else x).text src)
  return { lint := .unnecessaryMinOrMax, ref := n.ref, msg := unnecessaryMinOrMaxMsg fixed (textOf src v.range) first }

/-- The value a newtype is built from, of newtypes `β`
(`lint::Inner`): the field of a value of a newtype, or another
expression, with a type of its own or not. -/
inductive RoundtripInner (β : Type) where
  | fieldOf (t : β)
  | typed
  | untyped

/-- `T(e)`, or `T(e).0` (`lint::Roundtrip`). -/
inductive Roundtrip (β : Type) where
  | built (t : β) (e : RoundtripInner β)
  | read (t : β) (e : RoundtripInner β)

/-- Whether `redundant_newtype_roundtrip` fires, and with a fix
(`lint::RoundtripFix`). -/
inductive RoundtripFix where
  | unchanged
  | reported
  | fixed
  deriving DecidableEq

/-- What `redundant_newtype_roundtrip` does on `r`
(`lint::redundant_newtype_roundtrip`): `T(x.0)` is `x` where `x` is a `T`,
and `T(e).0` is `e`, but for `T(x.0).0`, which is reported at `T(x.0)`,
and without a fix where `e` takes its type from the newtype. -/
def redundantNewtypeRoundtrip [DecidableEq β] : Roundtrip β → RoundtripFix
  | .built t (.fieldOf u) => if t = u then .fixed else .unchanged
  | .built _ _ => .unchanged
  | .read t (.fieldOf u) => if t = u then .unchanged else .fixed
  | .read _ .untyped => .reported
  | .read _ .typed => .fixed

/-- `Ms(x.0)`, or `Ms(n).0` if `read`, whose fix is `fixed`, or none but
a note if `n` takes its type from the newtype (`untyped`). -/
def roundtripMsg (newtype fixed : String) (read untyped : Bool) : Msg :=
  { code? := some Lint.redundantNewtypeRoundtrip.code
    headline := if read then "this reads the field of a newtype just built" else "this builds a newtype from the field of one of its own"
    label? := some s!"a round trip through `{newtype}`"
    notes := if untyped then #[s!"note: `fren fix` leaves this, since `{fixed}` takes its type from the newtype, and has none without it"]
      else #[]
    fixes := if untyped then #[] else #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

/-- `redundant_newtype_roundtrip` on `n`, in `slot` within `parent`
(`lint::redundant_newtype_roundtrip`). -/
def roundtripAt? (src : Array Char) (fact? : α → Option NodeFact) (n : BNode α) (slot : Option Slot)
    (parent : Range) : Option (OpReport α) := do
  let #[k] := n.kids | none
  let #[x] := k.kids | none
  let inner (synth : Bool) : RoundtripInner String := match fact? x.ref with
    | some (.unwraps u) => .fieldOf u
    | _ => if synth then .typed else .untyped
  let (t, shape) ← match fact? n.ref, fact? k.ref with
    | some (.wraps t _), some (.unwraps u) => some (t, Roundtrip.built t (.fieldOf u))
    | some (.unwraps _), some (.wraps t synth) => some (t, Roundtrip.read t (inner synth))
    | _, _ => none
  let fix := redundantNewtypeRoundtrip shape
  guard (fix != .unchanged)
  let read := shape matches .read ..
  let untyped := fix == .reported
  let fixed := placed src n slot parent (x.text src)
  let name := (t.splitOn ".").getLast?.getD t
  return { lint := .redundantNewtypeRoundtrip, ref := n.ref, msg := roundtripMsg name fixed read untyped }

/-! ## Integers -/

/-- Whether a comparison of `x` on its left says that `x` is below the
other operand, or above it: `<` and `<=`, or `>` and `>=`. -/
def Comparison.below : Comparison → Bool
  | .lt | .le => true
  | _ => false

def Comparison.above : Comparison → Bool
  | .gt | .ge => true
  | _ => false

/-- The type that an ordering compares, as the lints of integers see it
(`lint::Ordered`): `Int` or `Nat`, an ordered enumeration, or another,
such as `String` or a newtype. -/
inductive Ordered where
  | number
  | enumeration
  | other
  deriving Inhabited, DecidableEq, Repr

/-- Whether `manual_abs` fires on `if x OP 0 then a else b`, where `op` has
`x` on its left, mirrored where `x` is written on the right, and
`negatedThen` says that `a` is `-x` and `b` is `x`, rather than the reverse
(`lint::manual_abs`). -/
def manualAbs (compared : Ordered) (op : Comparison) (negatedThen : Bool) : Bool :=
  compared == .number && ((op.below && negatedThen) || (op.above && !negatedThen))

def manualAbsMsg (fixed : String) : Msg :=
  { code? := some Lint.manualAbs.code, headline := "this conditional is the absolute value"
    label? := some "negates a negative operand"
    fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

/-- Whether `manual_abs_diff` fires on `if a OP b then c else d`, where
`thenLeftFirst` says that `c` is `a - b` and `d` is `b - a`, rather than
the reverse (`lint::manual_abs_diff`). -/
def manualAbsDiff (op : Comparison) (thenLeftFirst : Bool) : Bool :=
  (op.above && thenLeftFirst) || (op.below && !thenLeftFirst)

/-- Whether `manual_abs_diff` fires on `if a OP b then c else d`, where
`compared` is the type that `OP` compares, `a` and `b` are the written
forms of its operands, and `c` and `d` those of the operands of the
branches, each a subtraction (`lint::manual_abs_diff`). -/
def manualAbsDiffRule (op : Comparison) (compared : Ordered) (a b : String) (c d : String × String) : Bool :=
  compared == .number && a != b
    && ((c == (a, b) && d == (b, a) && manualAbsDiff op true) || (c == (b, a) && d == (a, b) && manualAbsDiff op false))

def manualAbsDiffMsg (fixed : String) : Msg :=
  { code? := some Lint.manualAbsDiff.code, headline := "this conditional is the absolute value of a difference"
    label? := some "subtracts the lesser operand from the greater"
    fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

/-- `min` or `max` (`lint::MinMax`). -/
inductive MinMax where
  | min
  | max
  deriving Inhabited, BEq, DecidableEq, Repr

def MinMax.name : MinMax → String
  | .min => "min"
  | .max => "max"

def MinMax.ofName? : String → Option MinMax
  | "min" => some .min
  | "max" => some .max
  | _ => none

/-- The method that `if a OP b then c else d` is, where `thenLeft` says
that `c` is `a` and `d` is `b`, rather than the reverse, if
`manual_min_max` fires (`lint::manual_min_max`). -/
def manualMinMax (op : Comparison) (thenLeft : Bool) : Option MinMax :=
  if op.below then some (if thenLeft then .min else .max)
  else if op.above then some (if thenLeft then .max else .min)
  else none

/-- The method that `if a OP b then c else d` is, and whether the fix's
receiver is `a`, rather than `b`, if `manual_min_max` fires, where
`compared` is the type that `OP` compares, `a`, `b`, `c` and `d` are
written forms, and `aLit` and `bLit` say whether `a` and `b` have an
integer literal in them (`lint::manual_min_max`). -/
def manualMinMaxRule (op : Comparison) (compared : Ordered) (a b c d : String) (aLit bLit : Bool) :
    Option (MinMax × Bool) :=
  if compared != .other && a != b && !(aLit && bLit) && ((c == a && d == b) || (c == b && d == a)) then
    (manualMinMax op (c == a)).map (·, !aLit)
  else none

def manualMinMaxMsg (m : MinMax) (fixed : String) : Msg :=
  { code? := some Lint.manualMinMax.code, headline := s!"this conditional is `{m.name}`"
    label? := some s!"gives the {if m == .min then "lesser" else "greater"} operand"
    fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

/-- Whether `manual_clamp` fires on `if x OP₁ b₁ then b₁ else if x OP₂ b₂
then b₂ else x`, where each comparison has `x` on its left and the bounds
are integer literals (`lint::manual_clamp`). -/
def manualClamp (compared : Ordered) (firstOp secondOp : Comparison) (first second : Int) : Bool :=
  compared == .number && ((firstOp.below && secondOp.above && first ≤ second) || (firstOp.above && secondOp.below && second ≤ first))

def manualClampMsg (fixed : String) : Msg :=
  { code? := some Lint.manualClamp.code, headline := "this conditional keeps its operand between two bounds"
    label? := some "gives a bound where the operand is past it"
    fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

/-- An operand of the `+` in `(p + q) mod k`, as `manual_rem_euclid` sees
it (`lint::Summand`): its written form, and the written form of its
divisor if it is a `mod`. -/
structure Summand where
  text : String
  divisor? : Option String
  deriving Inhabited, BEq, Repr

/-- Whether `manual_rem_euclid` fires on `(p + q) mod k`, where `divisor`
is the written form of `k` (`lint::manual_rem_euclid`): the first of `p`
and `q` that is a `mod` is by `k`, and the other is written as `k`. -/
def manualRemEuclidRule (p q : Summand) (divisor : String) : Bool :=
  match p.divisor?, q.divisor? with
  | some d, _ => d == divisor && q.text == divisor
  | none, some d => d == divisor && p.text == divisor
  | none, none => false

def manualRemEuclidMsg (fixed : String) : Msg :=
  { code? := some Lint.manualRemEuclid.code, headline := "`mod` is never negative already"
    label? := some "adds the divisor to a remainder"
    notes := #["note: `mod` is Euclidean, so `a mod k` is at least 0 and below the size of `k`, even where `a` is negative"]
    fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

/-- Whether `modulo_one` fires on `x mod k`, where `k` is an integer
literal (`lint::modulo_one`). -/
def moduloOne (k : Int) : Bool := k == 1 || k == -1

def moduloOneMsg (k : String) : Msg :=
  { code? := some Lint.moduloOne.code, headline := s!"the remainder by `{k}` is always `0`", label? := some "always `0`"
    notes := #["note: the divisor is probably not the one meant"] }

/-- Whether `min_max` fires on `x.inner(a).outer(b)`, where `a` and `b`
are integer literals (`lint::min_max`). -/
def minMax (inner outer : MinMax) (a b : Int) : Bool :=
  match inner, outer with
  | .min, .max => a < b
  | .max, .min => a > b
  | _, _ => false

def minMaxMsg (inner outer : MinMax) (b : String) : Msg :=
  { code? := some Lint.minMax.code, headline := s!"this `{inner.name}` and `{outer.name}` always give `{b}`"
    label? := some s!"always `{b}`"
    notes := #["note: the bounds are probably swapped"] }

/-- Whether `eq_op` fires on a call of `min` or `max`, from whether its
receiver and argument are written the same (`lint::eq_op_method`). -/
def eqOpMethod (receiver argument : String) : Bool := receiver == argument

/-- `r.m(r)`, for `min` or `max`, where `r` is the text of the receiver
(`lint::eq_op_method`). -/
def eqOpMethodMsg (m : MinMax) (r : String) : Msg :=
  { code? := some Lint.eqOp.code, headline := s!"the receiver and the argument of `{m.name}` are written the same"
    label? := some s!"the same as `{r}`"
    notes := #["note: one of them is probably not the operand meant"] }

/-- Whether the text `t` has an integer literal in it: a digit that does
not continue a name. Such a literal is a `Nat` or an `Int` by where it is
(`Reqs/Lang/Expressions#natural-numbers`), so an operand with one can
change type when it moves. -/
def hasIntLiteral (t : String) : Bool := Id.run do
  let cs := (withoutComments t).toList.toArray
  for i in [0:cs.size] do
    if cs[i]!.isDigit && (i == 0 || !isWordChar cs[i - 1]!) then return true
  return false

/-- `k`'s text without the parentheses around it, as the receiver of a
method: in parentheses where `lang::operand` requires them. -/
def receiverText (src : Array Char) (k : BNode α) : String := (k.text src).inSlot (some receiverSlot)

/-- `msg` without its fix where the text of `n` has a comment, which the
fix would drop. -/
def keepComments (src : Array Char) (n : BNode α) (msg : Msg) : Msg :=
  if hasComment (textOf src n.range) then
    { msg with fixes := #[], notes := msg.notes.push "note: the fix would drop the comments in the conditional, so it has none" }
  else msg

/-- The method call `t`, which replaces `n`, in `slot` within `parent`. -/
def placedCall (src : Array Char) (n : BNode α) (slot : Option Slot) (parent : Range) (t : String) : String :=
  placed src n slot parent { text := t, prec := (BKind.method "").prec }

/-- `manual_abs` on `n`, a conditional in `slot` within `parent`
(`lint::manual_abs`). -/
def manualAbsAt? (src : Array Char) (ordered? : α → Option Ordered) (n : BNode α) (slot : Option Slot) (parent : Range) :
    Option (OpReport α) := do
  guard (n.kind == .ite)
  let #[c, t, e] := n.kids | none
  let .bin cop := c.kind | none
  let op ← Comparison.ofOp? cop
  let #[ca, cb] := c.kids | none
  let wf (k : BNode α) := writtenForm (textOf src k.range)
  -- `x`, and the comparison with `x` on its left.
  let (x, op) ← if wf cb == "0" then some (ca, op) else if wf ca == "0" then some (cb, op.mirror) else none
  guard (wf x).toInt?.isNone
  let negated (k : BNode α) : Bool := match k.kind, k.kids with
    | .neg, #[o] => wf o == wf x
    | _, _ => false
  let negatedThen ← if negated t && wf e == wf x then some true else if wf t == wf x && negated e then some false else none
  guard (manualAbs ((ordered? c.ref).getD .other) op negatedThen)
  let fixed := placedCall src n slot parent s!"{receiverText src x}.abs"
  return { lint := .manualAbs, ref := n.ref, msg := keepComments src n (manualAbsMsg fixed) }

/-- `manual_abs_diff` on `n`, a conditional in `slot` within `parent`
(`lint::manual_abs_diff`). -/
def manualAbsDiffAt? (src : Array Char) (ordered? : α → Option Ordered) (n : BNode α) (slot : Option Slot)
    (parent : Range) : Option (OpReport α) := do
  guard (n.kind == .ite)
  let #[c, t, e] := n.kids | none
  let (op, a, b) ← comparisonOf? src c
  let wf (k : BNode α) := writtenForm (textOf src k.range)
  let diff? (k : BNode α) : Option (String × String) := match k.kind, k.kids with
    | .bin "-", #[l, r] => some (wf l, wf r)
    | _, _ => none
  guard (manualAbsDiffRule op ((ordered? c.ref).getD .other) a b (← diff? t) (← diff? e))
  let fixed := placedCall src n slot parent s!"({textOf src t.range}).abs"
  return { lint := .manualAbsDiff, ref := n.ref, msg := keepComments src n (manualAbsDiffMsg fixed) }

/-- `manual_min_max` on `n`, a conditional in `slot` within `parent`, where
`ordered?` says what type an ordering compares (`lint::manual_min_max`).
The receiver of the fix is an operand without an integer literal, the left
one if both are. -/
def manualMinMaxAt? (src : Array Char) (ordered? : α → Option Ordered) (n : BNode α) (slot : Option Slot)
    (parent : Range) : Option (OpReport α) := do
  guard (n.kind == .ite)
  let #[c, t, e] := n.kids | none
  let (op, a, b) ← comparisonOf? src c
  let #[ca, cb] := c.kids | none
  let wf (k : BNode α) := writtenForm (textOf src k.range)
  let (m, left) ← manualMinMaxRule op ((ordered? c.ref).getD .other) a b (wf t) (wf e)
    (hasIntLiteral (textOf src ca.range)) (hasIntLiteral (textOf src cb.range))
  let (r, arg) := if left then (ca, cb) else (cb, ca)
  let fixed := placedCall src n slot parent s!"{receiverText src r}.{m.name}({textOf src arg.range})"
  return { lint := .manualMinMax, ref := n.ref, msg := keepComments src n (manualMinMaxMsg m fixed) }

/-- `manual_clamp` on `n`, a conditional in `slot` within `parent`
(`lint::manual_clamp`). -/
def manualClampAt? (src : Array Char) (ordered? : α → Option Ordered) (n : BNode α) (slot : Option Slot)
    (parent : Range) : Option (OpReport α) := do
  guard (n.kind == .ite)
  let #[c1, t1, e1] := n.kids | none
  guard (e1.kind == .ite)
  let #[c2, t2, e2] := e1.kids | none
  let wf (k : BNode α) := writtenForm (textOf src k.range)
  -- The test `x OP b then b`: `x`, the comparison with it on the left, and `b`.
  let test (c t : BNode α) : Option (BNode α × Comparison × BNode α × Int) := do
    let .bin cop := c.kind | none
    let op ← Comparison.ofOp? cop
    let #[ca, cb] := c.kids | none
    let (x, op, bound) ← if wf cb == wf t then some (ca, op, cb) else if wf ca == wf t then some (cb, op.mirror, ca) else none
    return (x, op, bound, ← intLiteral? src bound)
  let (x, op1, b1, v1) ← test c1 t1
  let (x', op2, b2, v2) ← test c2 t2
  guard (wf x == wf x' && wf e2 == wf x && !hasIntLiteral (textOf src x.range))
  guard (manualClamp ((ordered? c1.ref).getD .other) op1 op2 v1 v2)
  let (lo, hi) := if op1.below then (b1, b2) else (b2, b1)
  let fixed := placedCall src n slot parent
    s!"{receiverText src x}.max({textOf src lo.range}).min({textOf src hi.range})"
  return { lint := .manualClamp, ref := n.ref, msg := keepComments src n (manualClampMsg fixed) }

/-- `manual_rem_euclid` on `n`, a `mod` in `slot` within `parent`
(`lint::manual_rem_euclid`). -/
def manualRemEuclidAt? (src : Array Char) (n : BNode α) (slot : Option Slot) (parent : Range) : Option (OpReport α) := do
  guard (n.kind == .bin "mod")
  let #[s, k] := n.kids | none
  guard (s.kind == .bin "+")
  let #[p, q] := s.kids | none
  let wf (k : BNode α) := writtenForm (textOf src k.range)
  -- Each operand, with the divisor of a remainder.
  let summand (r : BNode α) : Summand := match r.kind, r.kids with
    | .bin "mod", #[_, d] => { text := wf r, divisor? := some (wf d) }
    | _, _ => { text := wf r, divisor? := none }
  guard (manualRemEuclidRule (summand p) (summand q) (wf k))
  let inner := if (summand p).divisor?.isSome then p else q
  let fixed := placed src n slot parent (inner.text src)
  return { lint := .manualRemEuclid, ref := n.ref, msg := manualRemEuclidMsg fixed }

/-- `modulo_one` on `n`, a `mod` (`lint::modulo_one`). -/
def moduloOneAt? (src : Array Char) (n : BNode α) : Option (OpReport α) := do
  guard (n.kind == .bin "mod")
  let #[_, k] := n.kids | none
  guard (moduloOne (← intLiteral? src k))
  return { lint := .moduloOne, ref := n.ref, msg := moduloOneMsg (writtenForm (textOf src k.range)) }

/-- `min_max` on `n`, a call of `min` or `max` (`lint::min_max`). -/
def minMaxAt? (src : Array Char) (n : BNode α) : Option (OpReport α) := do
  let .method om := n.kind | none
  let outer ← MinMax.ofName? om
  let #[r, b] := n.kids | none
  let .method im := r.kind | none
  let inner ← MinMax.ofName? im
  let #[_, a] := r.kids | none
  guard (minMax inner outer (← intLiteral? src a) (← intLiteral? src b))
  return { lint := .minMax, ref := n.ref, msg := minMaxMsg inner outer (writtenForm (textOf src b.range)) }

/-- `eq_op` on `n`, a call of `min` or `max` whose receiver and argument
are written the same (`lint::eq_op_method`). -/
def eqOpMethodAt? (src : Array Char) (n : BNode α) : Option (OpReport α) := do
  let .method name := n.kind | none
  let m ← MinMax.ofName? name
  let #[r, a] := n.kids | none
  let wf (k : BNode α) := writtenForm (textOf src k.range)
  guard (eqOpMethod (wf r) (wf a))
  return { lint := .eqOp, ref := n.ref, msg := eqOpMethodMsg m (textOf src r.range) }


/-! ## Local definitions and quantifiers -/

/-- Whether `let_and_return` fires on a `let` or `where` clause, from
whether its body is the name of its last definition, alone, and whether
that definition's type is written (`lint::let_and_return`). -/
def letAndReturn (bodyIsLast annotated : Bool) : Bool := bodyIsLast && !annotated

/-- The fix of `let_and_return`: the clause without its last definition,
whose expression `e` is its body, where `earlier?` is the text of the
definitions before it, from the first to the end of the one before it. -/
def letAndReturnFixed (isWhere : Bool) (earlier? : Option String) (e : String) : String :=
  match earlier? with
  | none => e
  | some ds => if isWhere then s!"{e} where {ds}" else s!"let {ds} in {e}"

/-- `let_and_return`'s message, at the body `n`, whose fix replaces the
clause at `range` with `fixed`, or none but a note if a comment in the
clause would be lost (`commented`). -/
def letAndReturnMsg (n : Name) (isWhere : Bool) (range : Range) (fixed : String) (commented : Bool) : Msg :=
  let help := s!"write the definition of `{n}` in place of `{n}`"
  { code? := some Lint.letAndReturn.code
    headline := s!"this {if isWhere then "`where` clause" else "`let`"} only gives back its last definition"
    label? := some s!"the body is `{n}`"
    notes := if commented then #[s!"help: {help}", "note: `fren fix` leaves this, since a comment in it would be lost"]
      else #[]
    fixes := if commented then #[] else #[{ msg := help, replacement := fixed, range? := some range }] }

/-- Whether `redundant_locals` fires on a definition, from whether its
name is written with `!`, whether its type is written, and whether its
expression is that name alone (`lint::redundant_locals`). -/
def redundantLocal (bang annotated ownName : Bool) : Bool := bang && !annotated && ownName

/-- `redundant_locals`' message on `x! := x`. It suggests removing the
definition, but `fren fix` does not apply that: the definition may be an
unfinished edit, such as of `x! := x + 1`, which removing it would hide. -/
def redundantLocalMsg (n : Name) : Msg :=
  { code? := some Lint.redundantLocals.code, headline := s!"redundant definition of `{n}`"
    label? := some s!"defines `{n}` as the `{n}` it hides"
    notes := #[s!"note: `{n}` means the same with the definition and without it",
      s!"help: write the expression meant for `{n}`, or remove the definition"] }

/-- Whether `trivial_quantifier` fires on a quantifier, from the number of
its bound names whose types have one value (`lint::trivial_quantifier`). -/
def trivialQuantifier (nOne : Nat) : Bool := nOne ≥ 1

/-- Whether `trivial_quantifier`'s fix is given, from the number of bound
names whose types have one value, the number of bound names, whether each
of those types is an enumeration with one variant without a payload, and
whether the quantifier is a global expectation's leading `forall`, and
whether its body declares one of its bound names again
(`lint::trivial_quantifier`). -/
def trivialQuantifierFixed (nOne nNames : Nat) (variants global redeclared : Bool) : Bool :=
  nOne ≥ 1 && nOne == nNames && variants && !global && !redeclared

/-- The body of a quantifier at `body`, with each of the mentions of its
bound names at `mentions`, which are within it, replaced by its value
`value`: the fix of `trivial_quantifier`. -/
def substituted (src : Array Char) (body : Range) (mentions : Array (Range × String)) : String := Id.run do
  let ms := mentions.qsort fun a b => a.1.start < b.1.start
  let mut out := ""
  let mut i := body.start
  for (r, v) in ms do
    if r.start < i || r.stop > body.stop then continue
    out := out ++ textOf src { start := i, stop := r.start } ++ v
    i := r.stop
  return out ++ textOf src { start := i, stop := body.stop }

/-- `trivial_quantifier`'s message on a `forall` (`all`) or an `exists`
whose bound name `n` has a type `ty` of one value, `value` if it is a
variant: fixed to `fixed?` if every bound name's type has one, which is a
variant, and no comment would be lost, in place of the quantifier at
`range`. -/
def trivialQuantifierMsg (all : Bool) (n : Name) (ty : String) (value? : Option String) (range : Range)
    (fixed? : Option String) : Msg :=
  let kw := if all then "forall" else "exists"
  let help := match value? with
    | some v => s!"write the body with `{v}` in place of `{n}`"
    | none => s!"write the body at the one value of `{ty}`"
  { code? := some Lint.trivialQuantifier.code, headline := s!"this `{kw}` ranges over one value"
    label? := some s!"`{ty}` has one value"
    notes := #[s!"note: {if all then "a" else "an"} `{kw}` over a type of one value is its body at that value"]
      ++ (if fixed?.isSome then #[] else #[s!"help: {help}"])
    fixes := match fixed? with
      | some f => #[{ msg := help, replacement := f, range? := some range }]
      | none => #[] }

/-- The lexemes of `src[r]` as `manual_forall` compares them, each with
its range: a name or a path, `a::b` or `a.b`, possibly with a final `!`,
is one, and so is a number or a string literal, raw ones too; comments
and whitespace are none, and every other character is one. -/
def pathLexemes (src : Array Char) (r : Range) : Array (Range × String) := Id.run do
  let stop := min r.stop src.size
  let mut out := #[]
  let mut i := r.start
  while i < stop do
    let c := src[i]!
    let start := i
    if c.isWhitespace then
      i := i + 1
    else if c == '-' && src[i + 1]? == some '-' then
      while i < stop && src[i]! != '\n' do i := i + 1
    else if c == '/' && src[i + 1]? == some '-' then
      let mut depth := 1
      i := i + 2
      while i < stop && depth > 0 do
        if src[i]! == '/' && src[i + 1]? == some '-' then depth := depth + 1; i := i + 2
        else if src[i]! == '-' && src[i + 1]? == some '/' then depth := depth - 1; i := i + 2
        else i := i + 1
    else
      -- A raw literal is `r`, some `#`, then `"`, and ends with `"` and as many `#`.
      let mut hashes := 0
      while c == 'r' && src[i + 1 + hashes]? == some '#' do hashes := hashes + 1
      let raw := c == 'r' && src[i + 1 + hashes]? == some '"'
      if raw || c == '"' then
        i := if raw then i + hashes + 2 else i + 1
        let closes (k : Nat) := src[k]! == '"' && (List.range (if raw then hashes else 0)).all (src[k + 1 + ·]? == some '#')
        while i < stop && !closes i do
          i := i + (if !raw && src[i]! == '\\' then 2 else 1)
        i := min stop (i + 1 + (if raw then hashes else 0))
      else if isWordChar c then
        while i < stop && isWordChar src[i]! do i := i + 1
        repeat
          if src[i]? == some ':' && src[i + 1]? == some ':' && (src[i + 2]?.any isWordChar) then i := i + 2
          else if src[i]? == some '.' && (src[i + 1]?.any isWordChar) then i := i + 1
          else break
          while i < stop && isWordChar src[i]! do i := i + 1
        if src[i]? == some '!' && src[i + 1]? != some '=' then i := i + 1
      else
        i := i + 1
      out := out.push ({ start, stop := i }, textOf src { start, stop := i })
  return out

/-- The first segment of a name or a path, without a `!`. -/
def pathRoot (s : String) : String :=
  (((s.splitOn "::").head!.splitOn ".").head!.dropEndWhile (· == '!')).toString

/-- Whether an expression written `s` has an index or a table, whose
guards a rewrite that reorders or regroups its parts might change. -/
def hasGuarded (s : String) : Bool :=
  let cs := s.toList.toArray
  (pathLexemes cs { start := 0, stop := cs.size }).any fun (_, t) => t == "[" || t == "table"

/-- What `manual_forall` needs to know of the constraint that an
expression is in, from its front end. -/
structure ForallCx where
  /-- The number of variants of the enumeration of a path, as `variant?`
  gives its variants, if none of them has a payload. -/
  variants? : String → Option Nat := fun _ => none
  /-- The names that the constraint declares: those of its `let`s and
  `where` clause, its bound names and its patterns' binders. -/
  declared : Array String := #[]
  /-- Whether a name declared there would hide something in scope. -/
  hides : String → Bool := fun _ => false
  /-- The constraint has no index and no table (`hasGuarded`), so that
  the guards are the same however its parts are ordered. -/
  unguarded : Bool := false
  deriving Inhabited

/-- Whether `manual_forall` fires on operands of a run of `and` or `or`,
from whether they are one expression at a variant written in the same
places in each, whether each variant of its enumeration is one operand's,
once, and the number of operands (`lint::manual_forall`). -/
def manualForall (instances covers : Bool) (n : Nat) : Bool := instances && covers && n ≥ 3

/-- The bound name that `manual_forall`'s fix writes for the enumeration
written `ty`, if it can: its last segment in snake case, which is not a
reserved word, written with `!` if it hides something; none if the
constraint declares it, or the operands mention it. -/
def forallName? (cx : ForallCx) (ty : String) (mentioned : Array String) : Option String := do
  let n := toCase .snake ((ty.splitOn "::").getLast!)
  guard (identifierAccepted n && !reservedWords.contains n && !expressionWords.contains n)
  guard (!cx.declared.contains n && !mentioned.contains n)
  return if cx.hides n then n ++ "!" else n

/-- `manual_forall`'s message on the operands of a run of `and` (`all`)
or `or`, which are one expression at each variant of `ty`, fixed to
`fixed?`, if a bound name can be written and no comment would be lost. -/
def manualForallMsg (all : Bool) (ty : String) (fixed? : Option String) : Msg :=
  let kw := if all then "forall" else "exists"
  { code? := some Lint.manualForall.code
    headline := s!"these {if all then "conjuncts" else "disjuncts"} are one expression at each variant of `{ty}`"
    label? := some "one for each variant"
    notes := #[s!"note: `{kw}` says this once, and says it of a variant added later too"]
      ++ (if fixed?.isSome then #[] else #[s!"help: write it with `{kw}`"])
    fixes := match fixed? with
      | some f => #[{ msg := s!"write it with `{kw}`", replacement := f }]
      | none => #[] }

/-- Where a run of operands is (`lint::RunPlace`): where any expression may
be written; a body of `when`, `let` or a quantifier; a `when`'s condition,
or a part of an atom, which take an operand alike (`delimitedSlot`); an
operand of an operator; or a receiver. -/
inductive RunPlace where
  | free
  | body
  | condition
  | operand
  | receiver
  deriving Inhabited, DecidableEq, Repr

/-- The place of an operand in `slot`. -/
def RunPlace.ofSlot : Option Slot → RunPlace
  | none => .free
  | some s =>
    if s.outer == 0 then (if s.right then .body else .condition)
    else if s.outer == BKind.atom.prec then .receiver else .operand

/-- Whether `manual_forall`'s quantifier is put in parentheses, from where
the run is, whether something follows it, whether the fix replaces the
whole run, and whether the run is already in parentheses of its own
(`lint::quantifier_parentheses`). A quantifier is open-ended, so this is
`BText.inSlot` for it. -/
def quantifierParenthesized (p : RunPlace) (followed whole enclosed : Bool) : Bool :=
  !enclosed && (!whole || followed || p matches .condition | .operand | .receiver)

/-- The paths in `n` that `variant?` says are variants without a payload,
each with its range and variant. -/
partial def variantPaths (variant? : α → Option String) (n : BNode α) : Array (Range × String) :=
  ((variant? n.ref).map (n.range, ·)).toArray ++ n.kids.flatMap (variantPaths variant?)

/-- The enumeration of a variant as `variant?` gives it: all but its last
component. -/
def variantEnum (v : String) : String := ".".intercalate (v.splitOn ".").dropLast

/-- Whether the operands `ops`, each as its lexemes and the variants in
it, are one expression at a variant: they have the same lexemes but at
some places, and at each of those, each operand has a path to one variant
of one enumeration, its own; if so, those places, each operand's variant,
and the type that the first operand's path names. -/
def instancesOf? (ops : Array (Array (Range × String) × Array (Range × String))) :
    Option (Array Nat × Array String × String) := do
  let (first, _) ← ops[0]?
  guard (ops.all (·.1.size == first.size))
  let places := (List.range first.size).toArray.filter fun p => ops.any (·.1[p]!.2 != first[p]!.2)
  guard (!places.isEmpty)
  let vs ← ops.mapM fun (lex, paths) => do
    let ws ← places.mapM fun p => (paths.find? (·.1 == lex[p]!.1)).map (·.2)
    let v ← ws[0]?
    guard (ws.all (· == v))
    pure v
  let e := variantEnum vs[0]!
  guard (vs.all (variantEnum · == e))
  let path := first[places[0]!]!.2
  guard ((path.splitOn "::").length ≥ 2)
  return (places, vs, "::".intercalate (path.splitOn "::").dropLast)

/-- `manual_forall` on `n`, an `and` or an `or` in `slot` within
`parent`, if it is the top of a run (`lint::manual_forall`): one report
for each run of adjacent operands, not in parentheses, that are one
expression at each variant of an enumeration, in a constraint that `cx`
says has no index and no table. -/
def manualForallAt [Inhabited α] (src : Array Char) (variant? : α → Option String) (cx : ForallCx) (n : BNode α)
    (slot : Option Slot) (parent : Range) : Array (OpReport α) := Id.run do
  let .bin op := n.kind | return #[]
  unless cx.unguarded && (op == "and" || op == "or") do return #[]
  if slot.any (fun s => s.outer == (BKind.bin op).prec && !s.right) && !enclosed src parent n.range then return #[]
  let cs := runOperands op src n
  let parts := cs.map fun k => (pathLexemes src k.range, variantPaths variant? k)
  let bare := cs.map fun k => !enclosed src n.range k.range
  let mut out := #[]
  let mut i := 0
  while i + 3 ≤ cs.size do
    let found? := (List.range (cs.size + 1 - i - 3)).findSome? fun d => do
      let j := i + 3 + d
      guard ((bare.extract i j).all id)
      let (places, vs, ty) ← instancesOf? (parts.extract i j)
      -- `x = E::A or x = E::B or ...` over every variant is always `true`,
      -- and is not a quantifier's instances but a test of `x`.
      let k := cs[i]!
      guard (!(k.kind matches .bin "=" | .bin "!=") ||
        !k.kids.any fun c => places.any (parts[i]!.1[·]!.1 == c.range))
      let covers := (cx.variants? (variantEnum vs[0]!)).any (· == j - i) && (vs.toList.eraseDups.length == j - i)
      guard (manualForall true covers (j - i))
      pure (j, places, ty)
    let some (j, places, ty) := found? | i := i + 1; continue
    let whole := i == 0 && j == cs.size
    let range : Range := { start := cs[i]!.range.start, stop := cs[j - 1]!.range.stop }
    let mentioned := ((parts.extract i j).flatMap (·.1)).map (pathRoot ·.2)
    let fixed? := do
      guard (!hasComment (textOf src range))
      let x ← forallName? cx ty mentioned
      let (lex, _) := parts[i]!
      let body := substituted src cs[i]!.range (places.map fun p => (lex[p]!.1, x.dropEndWhile (· == '!') |>.toString))
      let t : BText := { text := s!"{if op == "and" then "forall" else "exists"} ({x}: {ty}), {body}", prec := BKind.quant.prec }
      let paren := quantifierParenthesized (RunPlace.ofSlot slot) (followedAt src n.range) whole
        (whole && inOwnParens src n parent)
      pure (if paren then s!"({t.text})" else t.text)
    out := out.push { lint := .manualForall, ref := cs[i]!.ref, last? := some cs[j - 1]!.ref
                      msg := manualForallMsg (op == "and") ty fixed? }
    i := j
  return out

/-- The messages of the operator and method lints in `n`, which is in
`slot` within `parent`, outermost first, where `inElse` says that `n` is
the `else` branch of a conditional, `inClamp` that it is that of a clamp
(`manualClampAt?`), and `chain` that `membership_chain` reads the chain of
`or` or `and` that it is in, if it is one (`membershipChainOf`). -/
partial def opReportsIn [Inhabited α] (src : Array Char) (boolEq : α → Bool) (ordered? : α → Option Ordered)
    (variant? : α → Option String) (isAbs : α → Bool) (mentioned : α → List Mention) (fact? : α → Option NodeFact)
    (fcx : ForallCx) (n : BNode α) (slot : Option Slot) (parent : Range) (inElse inClamp : Bool := false) (chain : Bool := false)
    (delimited : Bool := false) : Array (OpReport α) :=
  let slots := n.kind.slots
  -- Whether `membership_chain` reads the chain of `or` or `and` that `n`
  -- is in: decided at its top, an operand of no operator of its kind.
  let chain := match n.kind with
    | .bin op => if op != "or" && op != "and" then false
      else if slot.any (·.outer == (BKind.bin op).prec) then chain
      else membershipChainOf src variant? (op == "and") n
    | _ => false
  let clamp := if n.kind == .ite then manualClampAt? src ordered? n slot parent else none
  let own := match n.kind with
    | .bin op =>
      let operands := (n.kids.zip slots).filterMap fun (k, s) => s.bind (elseExtendsAt? src n k ·)
      (if op == "and" || op == "or" then
          (doubleComparisonAt? src n slot parent (op == "and")).toArray
            ++ (contradictoryAt? src variant? n (op == "and")).toArray
            ++ (redundantAt? src n slot parent (op == "and")).toArray
            ++ (overlyComplexAt? src n slot parent (op == "and")).toArray
            ++ manualForallAt src variant? fcx n (if delimited then some delimitedSlot else slot) parent
        else #[])
        ++ (boolEqualityAt? src boolEq n slot parent).toArray ++ (manualMethodAt? src n slot parent).toArray
        ++ (identityOpAt? src n slot parent).toArray ++ (suspiciousUnaryAt? src n).toArray
        ++ (erasingOpAt? src n).toArray ++ (firstEmptyAt? src n slot parent).toArray
        ++ (invalidUpcastAt? src isAbs n).toArray ++ (absurdOrderedAt? src fact? n).toArray
        ++ (manualOrderingAt? src fact? n slot parent).toArray ++ (manualRemEuclidAt? src n slot parent).toArray
        ++ (moduloOneAt? src n).toArray ++ operands ++ precedenceAt src n
        ++ (if op == "and" then chainableAt src n slot parent ++ manualAtMostOneAt src fact? n slot parent else #[])
        ++ (if op == "and" || op == "or" then manualPatternTestAt src variant? fact? n (op == "and") chain slot parent
          else #[])
    | .ite =>
      (needlessBoolAssignAt? src n slot parent).toArray ++ (branchesSharingAt? src mentioned n slot parent).toArray
        ++ (if inElse then #[] else ifsSameCondAt src n)
        ++ clamp.toArray ++ (manualAbsAt? src ordered? n slot parent).toArray
        ++ (manualAbsDiffAt? src ordered? n slot parent).toArray
        -- The inner conditional of a clamp is the clamp's, not a `min` or `max` of its own.
        ++ (if inClamp then #[] else (manualMinMaxAt? src ordered? n slot parent).toArray)
    | .method _ => (methodCallAt? src n slot parent).toArray ++ (minOrMaxAt? src fact? n slot parent).toArray
        ++ (minMaxAt? src n).toArray ++ (eqOpMethodAt? src n).toArray
    | .chain ops => (contradictoryChainAt? src n ops).toArray
    | .atom => (cardinalityAt? src n slot parent).toArray ++ (roundtripAt? src fact? n slot parent).toArray
    | _ => #[]
  -- A receiver needs parentheses as an operand does.
  let receiver := match n.kind, n.kids[0]? with
    | .method _, _ => true
    | .atom, some k => isReceiverOf src n k
    | _, _ => false
  let slots := if receiver then #[some receiverSlot] else if n.kind matches .method _ | .atom then #[] else slots
  -- The other parts of an atom, its arguments, fields and elements, are
  -- delimited (`delimitedSlot`).
  let atomic := n.kind matches .method _ | .atom
  own ++ (n.kids.mapIdx fun i k =>
    opReportsIn src boolEq ordered? variant? isAbs mentioned fact? fcx k (slots[i]?.join) n.range (n.kind == .ite && i == 2)
      (clamp.isSome && i == 2) chain (atomic && !(receiver && i == 0))).flatten

/-- The messages of the operator and method lints in an expression written
in `src` (`Reqs/Lint/Complexity/Comparisons`), where `boolEq` says whether a
comparison compares `Bool`s, `ordered?` what type an ordering compares,
`variant?` which variant without a payload a path is, if it is one, `isAbs` whether an expression is a call of `abs`, `mentioned` what
an expression mentions, for the conditions and the operands of `*`, and
`fact?` what is known of an expression of an ordered enumeration or a
newtype; `fcx` is what `manual_forall` needs to know of the
constraint. -/
def opReports [Inhabited α] (src : Array Char) (boolEq : α → Bool) (ordered? : α → Option Ordered)
    (variant? : α → Option String) (isAbs : α → Bool) (mentioned : α → List Mention) (fact? : α → Option NodeFact)
    (fcx : ForallCx) (root : BNode α) : Array (OpReport α) :=
  opReportsIn (upTo src root.range) boolEq ordered? variant? isAbs mentioned fact? fcx root none root.range

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

/-- Whether `int_plus_one` fires on the comparison `i` of a chained
comparison of `n`, where its fix of that comparison alone drops the
offset of its left operand if `dropLeft`: only if that operand is at an
end of the chain, in no other comparison (`lint::int_plus_one_in_chain`). -/
def intPlusOneInChain (dropLeft : Bool) (i n : Nat) : Bool := if dropLeft then i == 0 else i + 1 == n

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

/-- Whether `unicode_not_nfc` fires on a string literal, and whether its
message suggests the literal in NFC (`lint::unicode_not_nfc`): if its value
is not in NFC, and this version of Unicode assigns each of its code points,
and a suggestion if it has no escape sequence. -/
def unicodeNotNfc (nfc assigned escapes : Bool) : Bool × Bool :=
  let fires := assigned && !nfc
  (fires, fires && !escapes)

/-- What `unicode_not_nfc` says of the string literal written `t`: `none`
if it does not fire, and else its value, the value in NFC, and the literal
it suggests, if any: `t` with its value in NFC. A raw literal, or one
without a `\`, has no escape sequence, so its value is the text between its
delimiters, and the suggestion keeps them. -/
def unicodeNotNfc? (t : String) : Option (String × String × Option String) := do
  let value ← Lean.Syntax.decodeStrLit t
  let raw := t.startsWith "r"
  let normal? := Nfc.nfc? value
  let (fires, suggested) := unicodeNotNfc (normal? == some value) normal?.isSome (!raw && t.contains '\\')
  guard fires
  let some normal := normal? | none
  -- `r#"`: the `r`, its `#`s and the `"`.
  let hashes := ((t.toList.drop 1).takeWhile (· == '#')).length
  let (pre, post) := if raw then ((t.take (hashes + 2)).toString, "\"" ++ String.ofList (List.replicate hashes '#'))
    else ("\"", "\"")
  return (value, normal, if suggested then some (pre ++ normal ++ post) else none)

/-- The code points `cs`, as `U+0065 U+0301`. -/
def codePoints (cs : List Char) : String :=
  " ".intercalate (cs.map fun c =>
    let h := (String.ofList (Nat.toDigits 16 c.toNat)).toUpper
    "U+" ++ String.ofList (List.replicate (4 - min 4 h.length) '0') ++ h)

/-- A string literal whose value, `value`, is not in NFC, where it is
`normal`, and the literal in NFC that it suggests, `suggested?`. The note
names the code points that differ, between the longest prefix and suffix
that the two share. There is no fix, which would change the value. -/
def unicodeNotNfcMsg (value normal : String) (suggested? : Option String) : Msg :=
  let (a, b) := (value.toList, normal.toList)
  let pre := ((a.zip b).takeWhile fun (x, y) => x == y).length
  let (a, b) := (a.drop pre, b.drop pre)
  let post := ((a.reverse.zip b.reverse).takeWhile fun (x, y) => x == y).length
  let (a, b) := (a.take (a.length - post), b.take (b.length - post))
  { code? := some Lint.unicodeNotNfc.code, headline := "this string literal is not in Unicode NFC"
    label? := some "not in NFC"
    notes := #[s!"note: {codePoints a} is {codePoints b} in NFC",
      "note: strings compare by code point, so it never equals text in NFC, which most text is in"]
      ++ #[match suggested? with
        | some t => s!"help: write it in NFC, `{t}`"
        | none => "help: write it so that its value is in NFC",
        "note: `fren fix` does not, since that changes the literal's value"] }

/-- Whether `zero_prefixed_literal` fires on the integer literal `s`: a
decimal one, a `0` and then another digit (`lint::zero_prefixed_literal`). -/
def zeroPrefixed (s : String) : Bool :=
  match s.toList with
  | '0' :: c :: _ => isDecimalDigit c
  | _ => false

/-- The message of `zero_prefixed_literal` on `s`. It names the octal
literal only where its digits are octal and it would mean something else,
from `8` on. -/
def zeroPrefixedMsg (s : String) : Msg :=
  let fixed := dropLeadingZeros s
  let value := (integerValue? s).getD 0
  let octal := s.toList.all (fun c => isOctalDigit c || c == '_') && value ≥ 8
  { code? := some Lint.zeroPrefixedLiteral.code
    headline := s!"`{s}` is {value}" ++ (if octal then s!"; for octal write `0o{fixed}`" else "")
    label? := some "leading zero"
    notes := #["note: a leading `0` does not make a literal octal"]
    fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

/-- `zero_prefixed_literal` on an integer literal written at `r` in `src`,
in an expression or a pattern, after a `-` if it is negated: the literal's
range, and the message. A literal needs no parentheses. -/
def zeroPrefixedReport? (src : Array Char) (r : Range) : Option (Range × Msg) := do
  let neg := if src[r.start]? == some '-' then 1 else 0
  let start := ((List.range' (r.start + neg) (r.stop - min r.stop (r.start + neg))).find?
    fun i => !(src[i]?.getD ' ').isWhitespace).getD r.stop
  let t := textOf src { start, stop := r.stop }
  guard (integerLiteral t && zeroPrefixed t)
  return ({ start, stop := r.stop }, zeroPrefixedMsg t)

/-- A report of `double_neg`, `int_plus_one`, `neg_multiply` or
`unicode_not_nfc`: the lint, where, and the fix, if any, which replaces the
range. -/
structure ShapeReport (α : Type) where
  lint : Lint
  ref : α
  range : Range
  msg : Msg
  deriving Inhabited

/-- `-t`, with a space if `t` starts with `-`, which would start a comment. -/
def negText (t : String) : String := if t.startsWith "-" then s!"- {t}" else s!"-{t}"

/-- The reports of `double_neg`, `int_plus_one`, `neg_multiply` and
`unicode_not_nfc` in `n`, which is in `slot` within `parent`, and in its
operands, in order. An
atom's operands, such as an application's arguments, are where any
expression can be written. -/
partial def shapeReports [Inhabited α] (src : Array Char) (n : BNode α) (slot : Option Slot) (parent : Range) : Array (ShapeReport α) :=
  let .mk kind range ref kids := n
  let text (k : BNode α) : BText := match k with | .mk kk kr .. => { text := textOf src kr, prec := kk.prec }
  let isOne (k : BNode α) : Bool := match k with | .mk .atom kr _ _ => textOf src kr == "1" | _ => false
  let isMinusOne (k : BNode α) : Bool := match k with | .mk .neg _ _ #[o] => isOne o | _ => false
  -- The text of the replacement, parenthesized where the expression is.
  let place (t : BText) : String := if enclosed src parent range then t.text else t.inSlot slot (followedAt src range)
  let report (l : Lint) (msg : String → Msg) (t : BText) : Array (ShapeReport α) :=
    let replacement := place t
    #[{ lint := l, ref, range, msg := msg replacement }]
  -- An operand as `int_plus_one` sees it, and its text without the offset.
  let offset (k : BNode α) : Offset × BText := match k with
    | .mk (.bin "+") _ _ #[x, y] => if isOne y then (.plusOne, text x) else if isOne x then (.plusOne, text y) else (.zero, text k)
    | .mk (.bin "-") _ _ #[x, y] => if isOne y then (.minusOne, text x) else (.zero, text k)
    | _ => (.zero, text k)
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
    -- A literal is an atom, which needs no parentheses.
    | .atom, #[] =>
      match unicodeNotNfc? (textOf src range) with
      | some (value, normal, suggested?) =>
        #[{ lint := .unicodeNotNfc, ref, range, msg := unicodeNotNfcMsg value normal suggested? }]
      | none => #[]
    | .chain ops, _ =>
      -- In a chained comparison, only an operand at either end, which is
      -- in one comparison: the first comparison's left, the last's right.
      let n := ops.size
      let at_ (i : Nat) : Array (ShapeReport α) := Id.run do
        let some c := Comparison.ofOp? ops[i]! | return #[]
        let ((oa, ta), (ob, tb)) := (offset kids[i]!, offset kids[i + 1]!)
        let (fires, strict, dropLeft) := intPlusOne c oa ob
        unless fires && intPlusOneInChain dropLeft i n do return #[]
        let texts := kids.mapIdx fun j k => if dropLeft && j == 0 then ta else if !dropLeft && j == n then tb else text k
        let slots := kind.slots
        let ops' := ops.set! i strict.op
        let ts := texts.mapIdx fun j t => t.inSlot (slots[j]?.join) (j < n)
        let body := (ops'.zip (ts.extract 1)).foldl (fun acc (op, t) => s!"{acc} {op} {t}") (ts[0]?.getD "")
        return report .intPlusOne intPlusOneMsg { text := body, prec := kind.prec }
      if kids.size == n + 1 && n ≥ 1 then at_ 0 ++ (if n ≥ 2 then at_ (n - 1) else #[]) else #[]
    | _, _ => #[]
  (kids.zipIdx.foldl (init := own) fun acc (k, i) => acc ++ shapeReports src k (kind.slots[i]?.join) range)

/-- The reports of `double_neg`, `int_plus_one`, `neg_multiply` and
`unicode_not_nfc` in an expression written in `src`, in the order they start, the outer of two
that start together first. -/
def arithReports [Inhabited α] (src : Array Char) (root : BNode α) : Array (ShapeReport α) :=
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

/-- Whether `literal_dot_in_pattern` fires on a `.` of a pattern, neither
escaped nor in a class, from whether a letter or digit is directly before
it, and one directly after it, neither escaped
(`lint::literal_dot_in_pattern`). -/
def literalDotInPattern (before after : Bool) : Bool := before && after

/-- The pattern `p` from `i`, which parses, with each `.` that
`literal_dot_in_pattern` fires on written `[.]`, and the text of each with
the characters around it, such as `1.2`; `lit` says that the character
before `i` is a letter or digit, not escaped. -/
partial def literalDots (cs : Array Char) (i : Nat) (lit : Bool := false) (out : String := "")
    (found : Array String := #[]) : String × Array String :=
  match cs[i]? with
  | none => (out, found)
  | some '\\' => literalDots cs (i + 2) false (out ++ String.ofList (cs.extract i (i + 2)).toList) found
  | some '[' =>
    let j := classEnd cs i
    literalDots cs j false (out ++ String.ofList (cs.extract i j).toList) found
  | some '.' =>
    let next := cs[i + 1]?.getD ' '
    if literalDotInPattern lit next.isAlphanum then
      literalDots cs (i + 1) false (out ++ "[.]") (found.push s!"{cs[i - 1]!}.{next}")
    else literalDots cs (i + 1) false (out.push '.') found
  | some c => literalDots cs (i + 1) c.isAlphanum (out.push c) found

/-- The pattern `p`, which parses, with each `.` that
`literal_dot_in_pattern` fires on written `[.]`, and the text around each,
if there is one. -/
def literalDotsPattern? (p : String) : Option (String × Array String) :=
  let (t, found) := literalDots p.toList.toArray 0
  if found.isEmpty then none else some (t, found)

def literalDotMsg (found : Array String) (fixed : String) : Msg :=
  let t := found[0]!
  { code? := some Lint.literalDotInPattern.code
    headline := if found.size == 1 then s!"the `.` in `{t}` matches any character, not only a dot"
      else "each of these `.` matches any character, not only a dot"
    label? := some (if found.size == 1 then "matches any character" else "`.` that match any character")
    notes := #[s!"note: `{t}` also matches `{t.replace "." "x"}`; `[.]` matches only a dot"]
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

/-- What a variable of a procedure is, as `manual_nat` sees it
(`lint::NatRole`). -/
inductive NatRole where
  | input
  | output
  | definedOutput
  deriving Inhabited, BEq, DecidableEq, Repr

/-- A variable of a procedure, as `manual_nat` sees it
(`lint::NatVariable`): its name, what it is, and whether it is declared an
`Int`. -/
structure NatVariable where
  name : String
  role : NatRole
  int : Bool
  deriving Inhabited, BEq, Repr

/-- The comparison of a conjunct, as `manual_nat` sees it
(`lint::BoundOp`): `>=`, `<=`, or another. -/
inductive BoundOp where
  | atLeast
  | atMost
  | otherOp
  deriving Inhabited, BEq, DecidableEq, Repr

def BoundOp.ofOp : String → BoundOp
  | ">=" => .atLeast
  | "<=" => .atMost
  | _ => .otherOp

/-- A conjunct of an assumption or a guarantee, as `manual_nat` sees it
(`lint::NatConjunct`): whether its constraint is an assumption, its
comparison, and the written forms of its operands. -/
structure NatConjunct where
  assumption : Bool
  op : BoundOp
  left : String
  right : String
  deriving Inhabited, BEq, Repr

/-- Whether the conjunct `c` is a bound of `v` that `manual_nat` reports
(`lint::bounds?`): `v` is declared an `Int`, `c` says that it is at least
`0`, and `c` is an assumption of an input or a guarantee of an output that
is not defined. -/
def natBounds (v : NatVariable) (c : NatConjunct) : Bool :=
  v.int
    && (match c.op with
      | .atLeast => c.left == v.name && c.right == "0"
      | .atMost => c.left == "0" && c.right == v.name
      | .otherOp => false)
    && (match v.role with
      | .input => c.assumption
      | .output => !c.assumption
      | .definedOutput => false)

/-- The position in `cs`, the conjuncts of a procedure's assumptions and
guarantees in order, of the bound of `v` that `manual_nat` reports, if it
fires, where `kept` says that a call, a refinement or an `impl` in
the file gives `v` an `Int` (`lint::manual_nat`). -/
def manualNatAt (v : NatVariable) (cs : List NatConjunct) (kept : Bool) : Option Nat :=
  if kept then none else cs.findIdx? (natBounds v)

/-- Where `manual_nat` fires in a procedure, given its own variables and
the conjuncts of each of its assumptions and guarantees, before the end of
the file shows which variables are kept `Int`s: for each variable it
fires on, its position, and the constraint and conjunct of its bound. -/
def manualNatBounds (vars : Array NatVariable) (props : Array (Array NatConjunct)) : Array (Nat × Nat × Nat) :=
  let flat := props.toList.zipIdx.flatMap fun (cs, p) => cs.toList.zipIdx.map fun (c, k) => (c, p, k)
  vars.zipIdx.filterMap fun (v, i) => do
    let j ← manualNatAt v (flat.map (·.1)) false
    let (_, p, k) ← flat[j]?
    return (i, p, k)

/-- A type that a file gives a variable of a procedure, by a call's,
a refinement's or an `impl`'s binding, or a refinement that reads it by
name (`lint::Given`). -/
inductive Given where
  | givenInt
  | givenNat
  deriving Inhabited, DecidableEq, Repr

/-- `manual_nat` on the variable `x`, whose bound `bound` is a conjunct of
the constraint `prop`. -/
def manualNatMsg (x : String) (input : Bool) (prop bound : String) : Msg :=
  let kind := if input then "assumption" else "guarantee"
  { code? := some Lint.manualNat.code, headline := s!"`{x}` is never negative, so it can be a `Nat`"
    label? := some s!"`{x}` is at least 0 by this {kind}"
    notes := #[s!"note: a `Nat` {if input then "parameter" else "output"} brings this {kind} with its type"]
      ++ (if input then #[s!"note: a call must then pass a `Nat` for `{x}`"] else #[])
      ++ #[s!"help: declare `{x}: Nat`, and remove `{bound}` from `{prop}`, where nothing binds `{x}` to an `Int`"] }

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

/-- Whether `zero_sized_map_values` fires on `Rel<A, B>`, where `B` is an
enumeration of `nVariants` if `enum`, of which some has a payload if
`payload` (`lint::zero_sized_map_values`). -/
def zeroSizedMapValues (enum : Bool) (nVariants : Nat) (payload : Bool) : Bool :=
  enum && nVariants == 1 && !payload

/-- `Rel<a, b>`, where `v` is the one variant of `b`. -/
def zeroSizedMapValuesMsg (a b v : String) : Msg :=
  { code? := some "F0789", headline := s!"`Rel<{a}, {b}>` relates to `{b}`, which has one value"
    label? := some s!"`{b}` has only `{b}::{v}`"
    notes := #[s!"note: such a relation says only which `{a}`s it relates, as a set does",
      s!"help: write `Set<{a}>`"] }

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

/-- The lines of the text of `cs` from `start` up to `stop`, read in place,
that have something other than whitespace and comments: `--` to the end
of the line, and `/-` to `-/`, which nest. A `--` in a string literal
starts no comment. -/
def codeLinesIn (cs : Array Char) (start stop : Nat) : Nat :=
  go (min stop cs.size) start 0 false 0 false
where
  /-- The index of the first line break at or after `i`, or `stop`. -/
  lineEnd (stop i : Nat) : Nat :=
    if h : i < stop then if cs[i]! == '\n' then i else lineEnd stop (i + 1) else i
  termination_by stop - i
  /-- From `i`, with `n` lines counted, `code` if the current line has
  code, in `depth` nested comments, and `inString` if in a string literal.
  A loop of its own, so that its state is not boxed at each character. -/
  go (stop i n : Nat) (code : Bool) (depth : Nat) (inString : Bool) : Nat :=
    if h : i < stop then
      let c := cs[i]!
      let next := if i + 1 < stop then cs[i + 1]? else none
      if c == '\n' then go stop (i + 1) (if code then n + 1 else n) false depth false
      else if depth > 0 then
        if c == '-' && next == some '/' then go stop (i + 2) n code (depth - 1) inString
        else if c == '/' && next == some '-' then go stop (i + 2) n code (depth + 1) inString
        else go stop (i + 1) n code depth inString
      else if inString then
        if c == '\\' then go stop (i + 2) n code depth inString
        else go stop (i + 1) n code depth (c != '"')
      -- `c` is no line break, so the line's end is past `i`.
      else if c == '-' && next == some '-' then go stop (max (lineEnd stop i) (i + 1)) n code depth inString
      else if c == '/' && next == some '-' then go stop (i + 2) n code 1 inString
      else go stop (i + 1) n (code || !c.isWhitespace) depth (c == '"')
    else if code then n + 1 else n
  termination_by stop - i

/-- `codeLinesIn` of all of `text`. -/
def codeLines (text : String) : Nat :=
  let cs := text.toList.toArray
  codeLinesIn cs 0 cs.size

/-- Whether `too_many_lines` fires on an item of `n` lines of code
(`lint::too_many_lines`). -/
def tooManyLines (n : Nat) : Bool := n > 100

/-- The `what` named `n`, of `lines` lines of code. -/
def tooManyLinesMsg (what : Named) (n : Name) (lines : Nat) : Msg :=
  { code? := some "F0797", headline := s!"{what.describe} `{nameText n}` has {lines} lines"
    label? := some "longer than 100 lines"
    notes := #["note: blank lines and comments are not counted",
      if what == .function then "help: move parts of it into smaller functions, and apply them"
      else "help: move parts of it into smaller procedures, and call them"] }

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
`mentioned` is what its expression mentions
(`lint::assertions_on_constants`). -/
def assertionOnConstant (mentioned : List Mention) : Bool := mentioned.isEmpty

/-- A constraint, an `assume`, `ensure` or `expect`, or a cover goal, that mentions no
variable, where `literal?` is its value if it is written `true` or
`false`. -/
def assertionOnConstantMsg (kind : String) (literal? : Option Bool) : Msg :=
  let what := match kind with
    | "assume" => "assumption"
    | "ensure" => "guarantee"
    | "cover" => "cover goal"
    | _ => "expectation"
  let (label, note) := match literal?, kind with
    | some true, "assume" => ("always `true`", "it rules out no input")
    | some true, "ensure" => ("always `true`", "it constrains nothing")
    | some true, _ => ("always `true`", "it claims nothing")
    | some false, "assume" => ("always `false`", "no input meets it, so every guarantee holds vacuously")
    | some false, "ensure" => ("always `false`", "no behaviour meets it, so the procedure is not realizable")
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

/-! ## Trailing commas -/

/-- Whether `unnecessary_trailing_comma` fires on a comma after the last
element of a list, from whether a line ends between it and the `}` or `]` that
closes the list (`lint::unnecessary_trailing_comma`). -/
def unnecessaryTrailingComma (lineBreak : Bool) : Bool := !lineBreak

/-- The commas among `toks` that `unnecessary_trailing_comma` reports, by
index: each followed by a `}` or `]`, which only a trailing comma is: a
list in parentheses has none.
Each token is its text, and whether a line ends before it. -/
def trailingCommas (toks : Array (String × Bool)) : Array Nat :=
  (Array.range toks.size).filter fun i =>
    toks[i]!.1 == "," && toks[i + 1]?.any fun (t, lineBreak) =>
      (t == "}" || t == "]" || t == ")") && unnecessaryTrailingComma lineBreak

/-- A trailing comma on the line of the `closer` of its list. -/
def unnecessaryTrailingCommaMsg (closer : String) : Msg :=
  { code? := some Lint.unnecessaryTrailingComma.code, headline := s!"unnecessary trailing comma before `{closer}`"
    label? := some "trailing comma"
    notes := #[s!"note: a list ends with a comma only where its `{closer}` starts a line, so that an element is added by adding a line"]
    fixes := #[{ msg := "remove the comma", replacement := "" }] }

/-! ## Record literals -/

/-- Whether `inconsistent_struct_constructor` fires on a record literal,
from whether its fields are written in the order its record declares them
(`lint::inconsistent_struct_constructor`). -/
def inconsistentStructConstructor (inOrder : Bool) : Bool := !inOrder

/-- The record literal written at `outer` in `src`, whose fields, named
`given`, are written at `fields`, with its fields in the order `declared`,
if `inconsistent_struct_constructor` fires on it: each field keeps its
text, and the text between fields stays where it is. The fix is `none`
where that text has a comment, which would no longer be by its field. -/
def reorderedFields? (src : Array Char) (outer : Range) (fields : Array Range) (given declared : Array Name) :
    Option (Option String) := do
  let order := declared.filterMap given.idxOf?
  guard (order.size == fields.size && fields.size > 0)
  guard (inconsistentStructConstructor (order == Array.range order.size))
  let before := textOf src { start := outer.start, stop := fields[0]!.start }
  let between := (Array.range fields.size).map fun k =>
    textOf src { start := fields[k]!.stop, stop := if k + 1 < fields.size then fields[k + 1]!.start else outer.stop }
  if hasComment before || between.any hasComment then return none
  let mut text := before
  for k in [0:fields.size] do
    text := text ++ textOf src fields[order[k]!]! ++ between[k]!
  return some text

/-- A record literal of the record `r`, whose fields are not in the order
`declared`, as the text of its fix, if it has one. -/
def inconsistentStructConstructorMsg (r : Name) (declared : Array Name) (fixed? : Option String) : Msg :=
  { code? := some Lint.inconsistentStructConstructor.code
    headline := s!"the fields of this literal are not in the order `{nameText r}` declares them"
    label? := some "fields out of order"
    notes := #[s!"note: `{nameText r}` declares {proseList (declared.map nameText)}, in this order"]
      ++ (if fixed?.isNone then #["note: a comment between the fields would not stay by its field, so this has no fix"] else #[])
    fixes := fixed?.toArray.map fun replacement => { msg := "write them in that order", replacement } }

/-! ## The order of members -/

/-- A member of a procedure's block, by its place in the order that
`arbitrary_source_item_ordering` asks for (`lint::MemberKind`). A
`set_option fren.evidence ... in` is part of the member after it. -/
inductive MemberKind where
  | use
  | assumption
  | «exists»
  | «let»
  /-- `out r := e`, the definition of a result, in the place of `let`. -/
  | define
  | call
  | guarantee
  | expectation
  | cover
  deriving Inhabited, BEq, DecidableEq, Repr

/-- Its place in the order (`lint::rank`). -/
def MemberKind.rank : MemberKind → Nat
  | .use => 0
  | .assumption => 1
  | .exists => 2
  | .let => 3
  | .define => 3
  | .call => 4
  | .guarantee => 5
  | .expectation => 6
  | .cover => 7

def MemberKind.describe : MemberKind → String
  | .use => "a `use`"
  | .assumption => "an assumption"
  | .exists => "an `exists`"
  | .let => "a `let`"
  | .define => "a result's definition"
  | .call => "a call"
  | .guarantee => "a guarantee"
  | .expectation => "an expectation"
  | .cover => "a cover goal"

/-- Whether `arbitrary_source_item_ordering` fires on a member of kind
`second` written right after one of kind `first`
(`lint::arbitrary_source_item_ordering`). -/
def outOfOrder (first second : MemberKind) : Bool := first.rank > second.rank

/-- The first member that `arbitrary_source_item_ordering` fires on, if
any: the members before it are in order, so the one just before it is of
the latest kind among them. -/
def firstOutOfOrder? (kinds : Array MemberKind) : Option Nat :=
  (List.range kinds.size).find? fun i => i > 0 && outOfOrder kinds[i - 1]! kinds[i]!

/-- Whether the order keeps a member's mention of another after the
other's declaration, where `earlier` says the other is written before it:
the kinds are put in order, and the members of one kind stay in the order
they are written in (`lint::arbitrary_source_item_ordering`). -/
def mentionKept (mentioner mentioned : MemberKind) (earlier : Bool) : Bool :=
  mentioned.rank < mentioner.rank || (mentioned.rank == mentioner.rank && earlier)

/-- Whether the order keeps each mention after what it mentions, where a
mention `(i, j)` is of the member at `j` by the definition or a binding of
the one at `i` (`lint::arbitrary_source_item_ordering`). -/
def keepsMentions (kinds : Array MemberKind) (mentions : List (Nat × Nat)) : Bool :=
  mentions.all fun (i, j) => i == j || match kinds[i]?, kinds[j]? with
    | some a, some b => mentionKept a b (j < i)
    | _, _ => false

/-- The members of a procedure in order, as indices: by kind, and as written
within a kind. -/
def canonicalOrder (kinds : Array MemberKind) : Array Nat :=
  let rank (i : Nat) := (kinds[i]?.map (·.rank)).getD 0
  ((List.range kinds.size).mergeSort fun i j => rank i < rank j || (rank i == rank j && i ≤ j)).toArray

/-- Just after the end of the line that `i` is on in `src`, if only
whitespace and a line comment follow `i` on it. -/
def lineRestEnd? (src : Array Char) (i : Nat) : Option Nat := do
  let nl ← (List.range' i (src.size - i)).find? (src[·]! == '\n')
  let rest := (textOf src { start := i, stop := nl }).trimAscii.toString
  if rest.isEmpty || rest.startsWith "--" then some (nl + 1) else none

/-- The whole lines that each member is written on, from the line after the
`{` of its procedure, or after the previous member's last line, to the end
of its own last line: the comments above it are its own. `none` unless
each member starts its line, and only a comment follows it on its last
one. `openStop` is just after the `{`. -/
def memberLines? (src : Array Char) (openStop : Nat) (members : Array Range) : Option (Array Range) := do
  let mut start ← lineRestEnd? src openStop
  let mut out := #[]
  for m in members do
    let before := (textOf src { start, stop := m.start }).splitOn "\n"
    unless (before.getLast?.getD "").all (fun c => c == ' ' || c == '\t') do failure
    let stop ← lineRestEnd? src m.stop
    out := out.push { start, stop }
    start := stop
  return out

/-- The blank lines that `text`, whole lines, starts with, and the rest. -/
def splitBlankLines (text : String) : String × String :=
  let lines := text.splitOn "\n"
  let blank := lines.takeWhile (·.all (·.isWhitespace))
  -- The last piece is what follows the last newline, which is empty.
  let n := min blank.length (lines.length - 1)
  ("".intercalate (lines.take n |>.map (· ++ "\n")), "\n".intercalate (lines.drop n))

/-- The fix of `arbitrary_source_item_ordering`: the lines of the members,
in order, in place of the lines they are written on. Each member moves with
the blank lines before it, but the first keeps none: the blank lines of the
member that comes first go to the member written first. `mentions[i]` are
the members that member `i`'s definition or bindings mention. `none` unless the order keeps each mention after its
declaration (`mentionKept`), and the members are a line apart
(`memberLines?`). -/
def memberOrderFix? (src : Array Char) (openStop : Nat) (members : Array Range) (kinds : Array MemberKind)
    (mentions : Array (Array Nat)) : Option (Range × String) := do
  guard <| keepsMentions kinds (mentions.zipIdx.toList.flatMap fun (ms, i) => ms.toList.map (i, ·))
  let lines ← memberLines? src openStop members
  let first ← lines[0]?
  let last ← lines.back?
  let parts := lines.map fun r => splitBlankLines (textOf src r)
  let order := canonicalOrder kinds
  let head := order[0]?.getD 0
  let blankOf (k : Nat) := (parts[if k == head then 0 else if k == 0 then head else k]!).1
  let text := String.join (order.toList.map fun k => blankOf k ++ parts[k]!.2)
  return ({ start := first.start, stop := last.stop }, text)

/-- A member of kind `member` written after one of kind `before`. -/
def memberOrderMsg (member before : MemberKind) : Msg :=
  { code? := some Lint.arbitrarySourceItemOrdering.code, headline := s!"{member.describe} after {before.describe}"
    label? := some "out of order"
    notes := #["note: the members of a procedure are written `use`, `assume`, `exists`, `let` and `out`, `call`, `ensure`, `expect`, then `cover`"] }

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

/-! ## Lint settings -/

/-- A `set_option` of a lint or group in the file: what it sets, to what,
the level of `unused_lint_setting` at it, and the last setting that
replaced it for one of its lints, if any. -/
structure SettingRecord where
  target : LintTarget
  requested : LintLevel
  level : LevelInEffect
  replacedBy? : Option (LintTarget × LintLevel) := none
  deriving Inhabited, Repr

/-- The lints whose level a later `set_option` reads at the setting: its
messages are about the setting itself. -/
def settingLints : Array Lint := #[.unfulfilledExpectations, .unusedLintSetting]

/-- Whether `unused_lint_setting` fires on a setting, from whether it is in
effect at an item, for some lint it sets, and whether it is to `expect`
(`lint::unused_lint_setting`). -/
def unusedLintSetting (seen expect : Bool) : Bool := !seen && !expect

/-- A setting that is in effect at no item: the setting that replaced it,
if it is not in effect at the end of the file. -/
def unusedSettingMsg (target : LintTarget) (requested : LintLevel) (replacedBy? : Option (LintTarget × LintLevel))
    (fixable : Bool) : Msg :=
  let help := #["help: remove this `set_option`"] ++ (if fixable then #[fixHelp] else #[])
  match replacedBy? with
  | none =>
    { code? := some Lint.unusedLintSetting.code, headline := "this lint setting is in effect at no item"
      label? := some "no item follows it", notes := help }
  | some (t, v) =>
    let by_ := s!"`set_option {t.optionString} \"{v.name}\"`"
    let undoes := if requested == .deny && v != .deny && v != .forbid then
        #[s!"note: {by_} undoes this `deny`: `{target.name}` is not an error at the items that follow"]
      else #[]
    { code? := some Lint.unusedLintSetting.code, headline := "this lint setting is replaced before any item"
      label? := some "replaced before any item"
      notes := #[s!"note: {by_} replaces it before any item"] ++ undoes ++ help }

/-- The messages of `unused_lint_setting` for the file's settings, given the
indices of those in effect at an item, and of those in effect at the end
of the file. -/
def unusedSettingReports (settings : Array (SettingRecord × α)) (seen atEnd : Array Nat) (fixable : Bool := false) :
    Array (LintReport α) :=
  (settings.mapIdx fun i (r, ref) => (i, r, ref)).filterMap fun (i, r, ref) =>
    if unusedLintSetting (seen.contains i) (r.requested == .expect) then
      let replacedBy? := if atEnd.contains i then none else r.replacedBy?
      some { lint := .unusedLintSetting, level := r.level, ref
             msg := unusedSettingMsg r.target r.requested replacedBy? fixable }
    else none

/-- `settings` after the setting of `target` to `requested`, given the
levels before it: each setting that it replaces for one of its lints
records it. -/
def SettingRecord.replace (settings : Array (SettingRecord × α)) (before : Lint → LevelInEffect)
    (target : LintTarget) (requested : LintLevel) : Array (SettingRecord × α) :=
  target.members.foldl (init := settings) fun ss l =>
    match (before l).setting? with
    | some i => ss.modify i fun (r, ref) => ({ r with replacedBy? := some (target, requested) }, ref)
    | none => ss

/-! ## Unused assumptions -/

/-- Whether `unused_assumption` fires on an assumption, from the number of
variables it mentions, whether all are inputs, whether one of them, or an
uninterpreted function it applies, is used in the procedure, and whether
one is read in the file (`lint::unused_assumption`). -/
def unusedAssumption (nMentioned : Nat) (allInputs mentioned read : Bool) : Bool :=
  nMentioned > 0 && allInputs && !mentioned && !read

/-- An uninterpreted function, as what links assumptions for
`unused_assumption`, beside variables: its path after a number, which no
variable's name has. -/
def fnLink (path : Name) : Name := Name.mkNum .anonymous 0 ++ path

/-- Which of the assumptions, given the variables each mentions and the
uninterpreted functions each applies (`fnLink`), are used: those that
mention one of `used`, or one that a used assumption mentions,
transitively, since they constrain the same values. -/
def usedAssumptions (mentions : Array (Array Name)) (used : Array Name) : Array Bool := Id.run do
  let mut used := used
  let mut out := mentions.map fun _ => false
  -- Each round marks one more assumption, or none.
  for _ in [0:mentions.size] do
    let some i := (List.range mentions.size).find? fun i => !out[i]! && mentions[i]!.any used.contains
      | break
    out := out.set! i true
    used := used ++ mentions[i]!
  return out

/-- An assumption that `unused_assumption` may fire on: its procedure, its
name, the inputs it mentions, those and the uninterpreted functions it
applies (`fnLink`), and the level of the lint at the procedure. It fires
unless the file reads one of its links, or one that a used assumption of
the procedure mentions. -/
structure AssumptionRecord where
  component : Name
  name : Name
  inputs : Array Name
  links : Array Name
  level : LevelInEffect
  deriving Inhabited, Repr

def unusedAssumptionMsg (name : Name) (inputs linked : Array Name) : Msg :=
  let show_ (ns : Array Name) := ", ".intercalate (ns.toList.map (s!"`{·}`"))
  let together := if linked.isEmpty then #[] else
    #[s!"note: it is linked to {show_ linked}, reported too, which may need it: remove them together"]
  { code? := some Lint.unusedAssumption.code
    headline := s!"the assumption `{name}` constrains only parameters that nothing uses"
    label? := some "constrains only unused parameters"
    notes := #[s!"note: no guarantee, expectation, definition, argument or binding mentions {show_ inputs}, \
        nor does another assumption tie them to a used variable"] ++ together ++
      #["help: remove the assumption and its parameters, or use them"] }

/-- The messages of `unused_assumption`, given what the file's global
expectations read through calls, or apply (`fnLink`), its calls
pass, and its refinements read of their abstractions: each read's
procedure and parameter or function. An assumption is read when it mentions a
read parameter, or one that a read assumption of its procedure mentions. Each
message names the other reported assumptions linked to it. -/
def unusedAssumptionReports (rs : Array (AssumptionRecord × α)) (reads : Array (Name × Name)) :
    Array (LintReport α) :=
  let reported := rs.filter fun (r, _) =>
    let same := (rs.filter (·.1.component == r.component)).map (·.1)
    let used := usedAssumptions (same.map (·.links)) ((reads.filter (·.1 == r.component)).map (·.2))
    let read := (same.findIdx? (·.name == r.name)).any (used[·]!)
    unusedAssumption r.inputs.size true false read
  reported.map fun (r, ref) =>
    let others := (reported.filter fun (o, _) => o.component == r.component && o.name != r.name).map (·.1)
    let linked := usedAssumptions (others.map (·.links)) r.links
    let names := (others.zip linked).filterMap fun (o, l) => if l then some o.name else none
    { lint := .unusedAssumption, level := r.level, ref, msg := unusedAssumptionMsg r.name r.inputs names }

/-! ## Unrelated binders -/

/-- The groups of `binders` that `atoms`, the names each atom mentions,
relate: two binders are in one group when an atom mentions both, or each
is in one group with a third. A binder that no atom mentions is in none. -/
def binderGroups (binders : Array Name) (atoms : Array (Array Name)) : Array (Array Name) := Id.run do
  let mut groups : Array (Array Name) := #[]
  for a in atoms do
    let bs := binders.filter a.contains
    if bs.isEmpty then continue
    let (joined, rest) := groups.partition fun g => g.any bs.contains
    let merged := joined.foldl (· ++ ·) bs
    groups := rest.push (binders.filter merged.contains)
  return groups

/-- The atoms of `n`, a `Bool` expression: its operands through `and`
(`lint::unrelated_binders`). -/
partial def BNode.atoms (n : BNode α) : Array (BNode α) :=
  match n.kind with
  | .bin "and" => n.kids.flatMap (·.atoms)
  | _ => #[n]

/-- Whether `unrelated_binders` fires on a global expectation, from the
number of groups of its binders (`lint::unrelated_binders`). -/
def unrelatedBinders (nGroups : Nat) : Bool := nGroups ≥ 2

def unrelatedBindersMsg (name : String) (groups : Array (Array Name)) : Msg :=
  let show_ (g : Array Name) := ", ".intercalate (g.toList.map (s!"`{·}`"))
  { code? := some Lint.unrelatedBinders.code
    headline := s!"the calls of `{name}` fall into {groups.size} groups that nothing relates"
    label? := some s!"{groups.size} claims in one"
    notes := #[s!"note: no atom, argument or parameter relates a call of {show_ groups[0]!} and one of {show_ groups[1]!}",
      "help: relate the calls, or write one global expectation for each group"] }

/-! ## Record literals -/

/-- Whether `unnecessary_struct_initialization` fires on a record literal
of `n` fields, from whether each field's value reads that field of some
`r`, `r` is written the same in each, is a value rather than a call,
and has the record's type (`lint::unnecessary_struct_initialization`). -/
def unnecessaryStructInit (n : Nat) (readsOwn same value sameType : Bool) : Bool :=
  n > 0 && readsOwn && same && value && sameType

def unnecessaryStructInitMsg (r : String) : Msg :=
  { code? := some Lint.unnecessaryStructInitialization.code, headline := s!"this record literal is `{r}`"
    label? := some s!"copies each field of `{r}`"
    fixes := #[{ msg := s!"write `{r}`", replacement := r }] }

end Fren.Core
