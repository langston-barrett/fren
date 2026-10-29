# Lints

A *lint* is a diagnostic about something that is allowed but probably not
intended, such as an import that nothing uses. Each lint has a
name and a *level*, which says whether it is reported and how. Each lint
has a default level, which can be changed on the command line, in Lean
options, and in the spec itself.

This chapter describes what all lints share, and the chapters after it
describe the lints of each [group](#groups).

```fren
pub mod lint

use view::Severity
```

## The lints

<!-- keep-sorted start skip_lines=2 -->
| Lint | Code | Group | Default | Reported at |
|---|---|---|---|---|
| `absolute_paths` | `F0786` | `restriction` | `allow` | a path of three or more segments in an expression, pattern or type, such as `climate::Mode::Heat` (see [Long paths](Lint/Restriction.md#long-paths)) |
| `absurd_extreme_comparisons` | `F0763` | `suspicious` | `warn` | a comparison of a `len` or `card` that is always the same, since a length is never negative, such as `s.len < 0`, or with the first or last variant of an ordered enumeration, such as `s >= Severity::Silent` (see [Comparisons](Lint/Suspicious/Comparisons.md)) |
| `allow_attributes` | `F0780` | `restriction` | `allow` | a `set_option` that sets a lint or a group to `allow` (see [Allowed lints](Lint/Restriction.md#allowed-lints)) |
| `almost_complete_range` | `F0757` | `suspicious` | `warn` | a range in a pattern one character short of an alphabet, such as `a-y` (see [Ranges of characters](Lint/Suspicious/Literals.md#ranges-of-characters)) |
| `arbitrary_source_item_ordering` | `F0779` | `restriction` | `allow` | a procedure whose members are out of order, such as an `exists` after an `ensure` (see [The order of members](Lint/Restriction.md#the-order-of-members)) |
| `assertions_on_constants` | `F0761` | `style` | `warn` | an `assume`, `ensure` or `expect` that mentions no variable, such as `ensure r: true` (see [Constant constraints](Lint/Style.md#constant-constraints)) |
| `bool_equality` | `F0731` | `pedantic` | `allow` | `a = b` on `Bool`s (see [Boolean equality](Lint/Pedantic.md#boolean-equality)) |
| `branches_sharing_code` | `F0778` | `pedantic` | `allow` | `if c then a op x else b op x`, whose branches share an operand (see [Branches sharing code](Lint/Pedantic/Conditionals.md#branches-sharing-code)) |
| `card_zero` | `F0716` | `style` | `warn` | a comparison of a set's or relation's `card` with `0` or `1` that says whether it is empty, such as `s.card = 0` (see [Empty collections](Lint/Style.md#empty-collections)) |
| `case_split_guarantees` | `F0729` | `pedantic` | `allow` | two or more guarantees `when T, y = e` of one output, whose tests are of which variant one scrutinee is (see [Variant tests](Lint/Pedantic/Matches.md#variant-tests)) |
| `chainable_comparison` | `F0804` | `style` | `warn` | two adjacent conjuncts of an `and` that one chained comparison writes, such as `lo <= x and x < hi` (see [Chained comparisons](Lint/Style/Comparisons.md#chained-comparisons)) |
| `collapsible_match` | `F0832` | `style` | `warn` | a `match` arm whose body is a `match` on one of its binders, which the arm's pattern can match instead (see [Collapsible matches](Lint/Style/Matches.md#collapsible-matches)) |
| `collapsible_when` | `F0723` | `style` | `warn` | a `when` whose body is a `when`, or an `unless` whose body is an `unless` (see [Conditionals](Lint/Style.md#conditionals)) |
| `const_is_empty` | `F0755` | `suspicious` | `warn` | a test of a literal whose value the literal fixes, such as `"ab".len = 0` (see [Tests of literals](Lint/Suspicious/Literals.md#tests-of-literals)) |
| `constant_output` | `F0719` | `complexity` | `warn` | a definition of a result or `let` variable that mentions no variable and no uninterpreted function (see [Constant outputs](Lint/Complexity.md#constant-outputs)) |
| `contradictory_comparisons` | `F0766` | `suspicious` | `warn` | two comparisons of one operand that cannot both hold, joined by `and`, or of which one always holds, joined by `or`, such as `x < 3 and x > 5`, or in a chained comparison, such as `5 < x < 3` (see [Comparisons](Lint/Suspicious/Comparisons.md)) |
| `dead_code` | `F0711` | `unused` | `warn` | a private enumeration, record, abstract type, function or constant that nothing in its file uses (see [Dead code](Lint/Unused.md#dead-code)) |
| `definable_output` | `F0720` | `pedantic` | `allow` | an output that one guarantee equates with an expression of other variables (see [Definable outputs](Lint/Pedantic.md#definable-outputs)) |
| `disallowed_names` | `F0752` | `style` | `warn` | a declared name that is a placeholder, such as `foo` (see [Names](Lint/Style.md#names)) |
| `double_comparison` | `F0730` | `complexity` | `warn` | two comparisons of the same operands that are one, such as `a < b or a = b` (see [Double comparisons](Lint/Complexity/Comparisons.md#double-comparisons)) |
| `double_neg` | `F0740` | `style` | `warn` | a negation of a negation, `- -x` (see [Negations](Lint/Style.md#negations)) |
| `double_parens` | `F0739` | `complexity` | `warn` | parentheses directly around parentheses, `((e))` (see [Parentheses](Lint/Complexity/Operators.md#parentheses)) |
| `duplicate_constraint` | `F0768` | `suspicious` | `warn` | a constraint or global expectation written the same as an earlier one, or a cover goal written the same as an earlier cover goal (see [Repeated constraints](Lint/Suspicious.md#repeated-constraints)) |
| `duplicate_elements` | `F0738` | `suspicious` | `warn` | a set or relation literal with an element written the same as an earlier one, such as `{a, b, a}` (see [Elements written the same](Lint/Suspicious/Expressions.md#elements-written-the-same)) |
| `else_extends` | `F0733` | `complexity` | `warn` | a conditional operand whose `else` branch extends past its operator, as in `2 * if c? then x else y + 1` (see [Conditional operands](Lint/Complexity/Operators.md#conditional-operands)) |
| `empty_argument` | `F0745` | `suspicious` | `warn` | a method applied to `""` or `[]`, or a `slice` of length `0`, such as `s.starts_with?("")` (see [Empty arguments](Lint/Suspicious/Methods.md#empty-arguments)) |
| `enum_variant_names` | `F0749` | `style` | `warn` | an enumeration whose variants all start, or all end, with the same word, or a variant that contains its enumeration's name (see [Names](Lint/Style.md#names)) |
| `eq_op` | `F0736` | `suspicious` | `warn` | an operator whose operands are written the same, such as `x = x`, `when C, C`, or `at_most_one?(a?, a?)` (see [Operands written the same](Lint/Suspicious/Expressions.md#operands-written-the-same)) |
| `erasing_op` | `F0764` | `suspicious` | `warn` | an operation whose value ignores an operand, such as `x * 0` or `x in {}` (see [Erasing operations](Lint/Suspicious/Expressions.md#erasing-operations)) |
| `fn_params_excessive_bools` | `F0775` | `pedantic` | `allow` | a function with more than 3 `Bool` parameters (see [Many `Bool`s](Lint/Pedantic/Records.md#many-bools)) |
| `glob_imports` | `F0702` | `style` | `warn` | a `use ...::*` (see [Glob imports](Lint/Style.md#glob-imports)) |
| `identity_op` | `F0734` | `complexity` | `warn` | an operation that leaves an operand as it is, such as `x + 0`, or the negation in `x + -y` (see [Identities](Lint/Complexity/Operators.md#identities)) |
| `if_chain_match` | `F0727` | `pedantic` | `allow` | a chain of `if` whose tests are of which variant one scrutinee is (see [Variant tests](Lint/Pedantic/Matches.md#variant-tests)) |
| `if_not_else` | `F0724` | `pedantic` | `allow` | an `if` whose condition is a negation, such as `if not c? then a else b` (see [Negated conditions](Lint/Pedantic.md#negated-conditions)) |
| `ifs_same_cond` | `F0765` | `suspicious` | `warn` | a test of a chain of `else if` written the same as an earlier one (see [Branches written the same](Lint/Suspicious/Expressions.md#branches-written-the-same)) |
| `inconsistent_struct_constructor` | `F0772` | `pedantic` | `allow` | a record literal whose fields are not in the order its record declares them (see [Record literals](Lint/Pedantic/Records.md#record-literals)) |
| `index_after_use` | `F0721` | `suspicious` | `warn` | an index on the left of an `and` whose right bounds the sequence (see [Indexes](Lint/Suspicious/Methods.md#indexes)) |
| `int_plus_one` | `F0741` | `complexity` | `warn` | a non-strict comparison of integers with an operand off by one, such as `x >= y + 1` (see [Off-by-one comparisons](Lint/Complexity/Comparisons.md#off-by-one-comparisons)) |
| `invalid_upcast_comparisons` | `F0798` | `pedantic` | `allow` | a comparison of a method's call that its least value fixes, such as `x.abs >= 0` or `s.index_of(t, i) < -1` (see [Ranges of methods](Lint/Pedantic.md#ranges-of-methods)) |
| `invisible_characters` | `F0769` | `suspicious` | `warn` | a string literal with an invisible character, or a string literal or comment with a bidirectional control (see [Invisible characters](Lint/Suspicious/Literals.md#invisible-characters)) |
| `irrefutable_is` | `F0803` | `suspicious` | `warn` | a pattern test whose pattern matches every value, such as `x is _` (see [Pattern tests](Lint/Suspicious.md#pattern-tests)) |
| `is_equality` | `F0802` | `style` | `warn` | a pattern test of one variant without a payload, or one literal, such as `x is E::A` (see [Pattern tests](Lint/Style/Comparisons.md#pattern-tests)) |
| `just_underscores_and_digits` | `F0751` | `style` | `warn` | a declared name made only of `_` and digits, such as `_1` (see [Names](Lint/Style.md#names)) |
| `length_zero` | `F0715` | `style` | `warn` | a comparison of a string's or sequence's `len` with `0` or `1`, or of its `at(0)` with `""` or `[]`, that says whether it is empty, such as `s.len = 0` (see [Empty collections](Lint/Style.md#empty-collections)) |
| `let_and_return` | `F0824` | `style` | `warn` | a `let` or `where` clause whose body is the name of its last definition, such as `let d := x + 1 in d` (see [Returned definitions](Lint/Style/Let.md#returned-definitions)) |
| `literal_dot_in_pattern` | `F0794` | `suspicious` | `warn` | a `.` between two letters or digits in a pattern, such as `r"v1.2"` (see [Dots in patterns](Lint/Suspicious/Literals.md#dots-in-patterns)) |
| `manual_abs` | `F0811` | `complexity` | `warn` | a conditional that is the absolute value, such as `if x < 0 then -x else x` (see [Absolute values](Lint/Complexity/Integers.md#absolute-values)) |
| `manual_abs_diff` | `F0812` | `complexity` | `warn` | a conditional that is the absolute value of a difference, such as `if a > b then a - b else b - a` (see [Absolute values](Lint/Complexity/Integers.md#absolute-values)) |
| `manual_at_most_one` | `F0840` | `complexity` | `warn` | a conjunction that negates each pair of three or more operands, such as `not (a? and b?) and not (a? and c?) and not (b? and c?)` (see [Cardinality](Lint/Complexity/Operators.md#cardinality)) |
| `manual_clamp` | `F0814` | `complexity` | `warn` | a conditional that keeps its operand between two literals, such as `if x < 0 then 0 else if x > 9 then 9 else x` (see [Lesser and greater](Lint/Complexity/Integers.md#lesser-and-greater)) |
| `manual_forall` | `F0826` | `style` | `warn` | three or more operands of a run of `and` or `or` that are one expression at each variant of an enumeration, such as `Mode::Heat in s and Mode::Cool in s and Mode::Off in s` (see [Operands at each variant](Lint/Style/Let.md#operands-at-each-variant)) |
| `manual_method` | `F0732` | `complexity` | `warn` | a search written with `index_of`, `slice` or `at`, such as `s.index_of(t, 0) >= 0` (see [Searches](Lint/Complexity/Methods.md#searches)) |
| `manual_min_max` | `F0813` | `complexity` | `warn` | a conditional that is `min` or `max`, such as `if a < b then a else b` (see [Lesser and greater](Lint/Complexity/Integers.md#lesser-and-greater)) |
| `manual_nat` | `F0810` | `style` | `warn` | an `Int` input or output that an assumption or a guarantee keeps at least 0, as in `assume counts: n >= 0` (see [Natural numbers](Lint/Style/Naturals.md#integers-kept-at-least-0)) |
| `manual_ordering` | `F0841` | `pedantic` | `allow` | a membership in the first or last variants of an ordered enumeration, such as `s in {Severity::Silent, Severity::Info}` (see [Orderings written out](Lint/Pedantic/Comparisons.md#orderings-written-out)) |
| `manual_pattern_char_comparison` | `F0756` | `style` | `warn` | an alternation of single characters in a pattern, such as `a\|b` (see [Classes of characters](Lint/Style.md#classes-of-characters)) |
| `manual_pattern_test` | `F0805` | `style` | `warn` | two or more equations of one expression with values that patterns write, such as `x = 429 or x = 503`, or the disequations of its dual (see [Pattern tests written out](Lint/Style/PatternTests.md)) |
| `manual_range_patterns` | `F0833` | `complexity` | `warn` | an or-pattern of integer literals and ranges that is one range, such as `1 \| 2 \| 3` (see [Ranges written as alternatives](Lint/Complexity/Patterns.md#ranges-written-as-alternatives)) |
| `manual_record_update` | `F0818` | `style` | `warn` | a record literal that copies more fields from one value than it gives, such as `Point { x := 1, y := p.y, z := p.z }` (see [Record literals](Lint/Style/Records.md#record-literals)) |
| `manual_rem_euclid` | `F0815` | `complexity` | `warn` | a remainder made non-negative by hand, `(a mod k + k) mod k` (see [Remainders](Lint/Complexity/Integers.md#remainders)) |
| `manual_table` | `F0838` | `pedantic` | `allow` | a chain of `if` of two or more tests that are not variant tests of one scrutinee, which a table writes (see [Chains of conditions](Lint/Pedantic/Matches.md#chains-of-conditions)) |
| `many_single_char_names` | `F0795` | `pedantic` | `allow` | a procedure, function or global expectation that declares more than four single-character names (see [Names](Lint/Pedantic.md#names)) |
| `match_bool` | `F0837` | `pedantic` | `allow` | a `match` on a `Bool` of `true` and `false`, or of one of them and `_` (see [Matches on a `Bool`](Lint/Pedantic/Matches.md#matches-on-a-bool)) |
| `match_like_membership` | `F0726` | `style` | `warn` | a `match` whose arms are all `true` or `false`, and bind no name (see [Matches that are memberships](Lint/Style.md#matches-that-are-memberships)) |
| `match_overlapping_arm` | `F0835` | `style` | `warn` | a range of a `match` arm that has an integer in common with an earlier arm's pattern, neither within the other, such as `5..=15` after `0..=10` (see [Overlapping arms](Lint/Style/Matches.md#overlapping-arms)) |
| `match_same_arms` | `F0725` | `pedantic` | `allow` | an arm of a `match` with the same body as another (see [Arms](Lint/Pedantic/Matches.md#arms)) |
| `membership_chain` | `F0718` | `pedantic` | `allow` | `x = a or x = b or x = c`, or `x != a and x != b and x != c`, three or more, where some value is not one that a pattern writes (see [Membership chains](Lint/Pedantic.md#membership-chains)) |
| `min_ident_chars` | `F0785` | `restriction` | `allow` | a declared name of one character, such as `x` (see [Names](Lint/Restriction.md#names)) |
| `min_max` | `F0817` | `suspicious` | `warn` | a `min` and a `max` whose literal bounds leave one value, such as `x.min(0).max(9)` (see [Integers](Lint/Suspicious/Integers.md#remainders-and-bounds)) |
| `module_inception` | `F0748` | `style` | `warn` | a module whose last segment repeats its parent's, as in `mod lint::lint` (see [Names](Lint/Style.md#names)) |
| `module_name_repetitions` | `F0784` | `restriction` | `allow` | an item whose name contains its module's, such as `climate::ClimateMode` (see [Names](Lint/Restriction.md#names)) |
| `modulo_one` | `F0816` | `suspicious` | `warn` | a remainder by `1` or `-1`, which is always `0` (see [Integers](Lint/Suspicious/Integers.md#remainders-and-bounds)) |
| `needless_bool_assign` | `F0759` | `complexity` | `warn` | `if C then X else not X`, or `if C then not X else X` (see [Conditionals of `Bool`s](Lint/Complexity.md#conditionals-of-bools)) |
| `needless_match` | `F0760` | `complexity` | `warn` | a `match` whose every arm gives back the value it matches, such as `match x { E::A => E::A, _ => x }` (see [Matches that give back the scrutinee](Lint/Complexity/Matches.md#matches-that-give-back-the-scrutinee)) |
| `needless_raw_string_hashes` | `F0777` | `pedantic` | `allow` | a raw string literal with more `#`s than it needs, such as `r#"a"#` (see [Raw string literals](Lint/Pedantic.md#raw-string-literals)) |
| `needless_raw_strings` | `F0782` | `restriction` | `allow` | a raw string literal with no `\` and no `"` (see [Literals](Lint/Restriction.md#literals)) |
| `needless_update` | `F0819` | `complexity` | `warn` | a record update that gives every field (see [Needless updates](Lint/Complexity/Updates.md#needless-updates)) |
| `neg_multiply` | `F0742` | `style` | `warn` | a product with `-1`, `x * -1` or `-1 * x` (see [Negations](Lint/Style.md#negations)) |
| `negative_position` | `F0770` | `suspicious` | `warn` | a negative integer literal as a position, such as `q[-1]` or `s.at(-1)` (see [Indexes](Lint/Suspicious/Methods.md#indexes)) |
| `no_effect_replace` | `F0754` | `suspicious` | `warn` | `s.replace(a, a)` or `s.replace_all(a, a)` (see [Replacements](Lint/Suspicious/Methods.md#replacements)) |
| `non_ascii_literal` | `F0783` | `restriction` | `allow` | a string literal with a character beyond ASCII (see [Literals](Lint/Restriction.md#literals)) |
| `non_camel_case_types` | `F0704` | `nonstandard_style` | `warn` | an enumeration, variant, record or abstract type not named in `CamelCase` (see [Naming conventions](Lint/NonstandardStyle.md#naming-conventions)) |
| `non_snake_case` | `F0703` | `nonstandard_style` | `warn` | a module, procedure, variable, function, call, constraint or global expectation not named in `snake_case` (see [Naming conventions](Lint/NonstandardStyle.md#naming-conventions)) |
| `non_upper_case_constants` | `F0705` | `nonstandard_style` | `warn` | a constant not named in `UPPER_CASE` (see [Naming conventions](Lint/NonstandardStyle.md#naming-conventions)) |
| `nonminimal_bool` | `F0712` | `complexity` | `warn` | a `Bool` expression with a simpler form, such as `a? = true` or `exactly_one?(a?)` (see [Simpler `Bool` expressions](Lint/Complexity.md#simpler-bool-expressions)) |
| `overly_complex_bool_expr` | `F0773` | `pedantic` | `allow` | an `and` or `or` with an operand that can be dropped, such as `a or (a and b)` or `a and not a` (see [Operands that can be dropped](Lint/Pedantic.md#operands-that-can-be-dropped)) |
| `precedence` | `F0787` | `restriction` | `allow` | an `and` in an `or`, or a `join` or `inter` in a `union` or `minus`, without parentheses, such as `a? or b? and c?` (see [Precedence](Lint/Restriction.md#precedence)) |
| `redundant_bindings` | `F0735` | `style` | `warn` | a field `x := x` of a record literal, or a field `x := r.x` of an update of `r` (see [Bindings](Lint/Style.md#bindings)) |
| `redundant_bool_type` | `F0746` | `style` | `warn` | a `: Bool` that a name ending in `?` implies, as in the parameter `ready?: Bool` (see [Boolean types](Lint/Style.md#boolean-types)) |
| `redundant_comparisons` | `F0767` | `complexity` | `warn` | two comparisons of one operand with integers, of which one implies the other, such as `x < 3 and x < 5` (see [Redundant comparisons](Lint/Complexity/Comparisons.md#redundant-comparisons)) |
| `redundant_locals` | `F0825` | `suspicious` | `warn` | a definition `x! := x` of a `let` or `where` clause (see [Redundant definitions](Lint/Suspicious.md#redundant-definitions)) |
| `redundant_method_chain` | `F0743` | `complexity` | `warn` | a chain of methods with a shorter form, such as `q.rev.rev` (see [Chains of methods](Lint/Complexity/Methods.md#chains-of-methods)) |
| `redundant_newtype_roundtrip` | `F0842` | `complexity` | `warn` | a newtype built from the field of one, `Ms(x.0)`, or the field of one just built, `Ms(n).0` (see [Newtypes](Lint/Complexity.md#newtypes)) |
| `redundant_slicing` | `F0753` | `complexity` | `warn` | `s.slice(0, s.len)` (see [Whole slices](Lint/Complexity/Methods.md#whole-slices)) |
| `same_branches` | `F0737` | `suspicious` | `warn` | `if c then a else a`, or a table whose rows' values are all written the same (see [Branches written the same](Lint/Suspicious/Expressions.md#branches-written-the-same)) |
| `similar_names` | `F0796` | `pedantic` | `allow` | a name declared in the same item as another that differs from it by one character, such as `level` and `levels` (see [Names](Lint/Pedantic.md#names)) |
| `single_call_fn` | `F0788` | `restriction` | `allow` | a private defined function that one path in its file applies (see [Functions applied once](Lint/Restriction.md#functions-applied-once)) |
| `single_match_else` | `F0771` | `pedantic` | `allow` | a `match` of one pattern that binds nothing and `_`, such as `match x { E::A => a, _ => b }` (see [One pattern and `_`](Lint/Pedantic/Matches.md#one-pattern-and-_)) |
| `singleton_membership` | `F0717` | `complexity` | `warn` | `x in {a}` (see [Singleton membership](Lint/Complexity.md#singleton-membership)) |
| `struct_excessive_bools` | `F0776` | `pedantic` | `allow` | a record with more than 3 `Bool` fields (see [Many `Bool`s](Lint/Pedantic/Records.md#many-bools)) |
| `struct_field_names` | `F0774` | `pedantic` | `allow` | a record whose fields all start, or all end, with the same word, or a field that contains its record's name (see [Field names](Lint/Pedantic/Records.md#field-names)) |
| `suspicious_unary_op_formatting` | `F0762` | `suspicious` | `warn` | a binary operator directly followed by a negation and then whitespace, such as `x >=- 1` (see [Negations after operators](Lint/Suspicious.md#negations-after-operators)) |
| `too_many_lines` | `F0797` | `pedantic` | `allow` | a procedure or defined function of more than 100 lines (see [Long items](Lint/Pedantic.md#long-items)) |
| `trivial_cover` | `F0820` | `suspicious` | `warn` | a cover goal that has a trigger, or is written the same as an assumption or a guarantee (see [Cover goals](Lint/Suspicious.md#cover-goals)) |
| `trivial_match` | `F0747` | `complexity` | `warn` | a `match` of one arm that binds nothing, such as `match x { _ => e }` (see [Trivial matches](Lint/Complexity/Matches.md#trivial-matches)) |
| `trivial_pattern` | `F0744` | `style` | `warn` | `s.matches?(p)`, where `p` is a string, with `.*` or not at either end (see [Trivial patterns](Lint/Style.md#trivial-patterns)) |
| `trivial_quantifier` | `F0827` | `complexity` | `warn` | a quantifier with a bound name whose type has one value (see [Trivial quantifiers](Lint/Complexity.md#trivial-quantifiers)) |
| `undecidable` | `F0714` | `decidability` | `deny` | a construct outside the decidable core (see [Undecidable constructs](Lint/Decidability.md#undecidable-constructs)) |
| `unfulfilled_lint_expectations` | `F0706` | `unused` | `warn` | a `set_option` that expects a lint that never fires (see [Expecting lints](#expecting-lints)) |
| `unicode_not_nfc` | `F0799` | `pedantic` | `allow` | a string literal whose value is not in Unicode NFC (see [Unicode normalization](Lint/Pedantic/Text.md#unicode-normalization)) |
| `unless_not` | `F0722` | `style` | `warn` | an `unless` whose condition is a negation, such as `unless not c?, d?` (see [Conditionals](Lint/Style.md#conditionals)) |
| `unnecessary_min_or_max` | `F0843` | `complexity` | `warn` | a `min` or `max` with the first or last variant of an ordered enumeration, such as `s.max(Severity::Silent)` (see [Bounds of orderings](Lint/Complexity/Methods.md#bounds-of-orderings)) |
| `unnecessary_struct_initialization` | `F0790` | `complexity` | `warn` | a record literal that copies each field of a value of its record, such as `Point { x := p.x, y := p.y }` (see [Copied records](Lint/Complexity.md#copied-records)) |
| `unnecessary_trailing_comma` | `F0801` | `pedantic` | `allow` | a trailing comma on the line of the `}` or `]` that closes its list, as in `{a, b,}` (see [Trailing commas](Lint/Pedantic/Text.md#trailing-commas)) |
| `unnested_or_patterns` | `F0836` | `pedantic` | `allow` | alternatives next to each other that name one variant and differ in one value of its payload, such as `E::V(1) \| E::V(2)` (see [Nested or-patterns](Lint/Pedantic/Matches.md#nested-or-patterns)) |
| `unrelated_binders` | `F0793` | `suspicious` | `warn` | a global expectation whose calls fall into two or more groups that nothing relates (see [Unrelated binders](Lint/Suspicious.md#unrelated-binders)) |
| `unused_assumption` | `F0792` | `unused` | `warn` | an assumption that mentions only inputs that nothing uses, even through other assumptions (see [Unused assumptions](Lint/Unused.md#unused-assumptions)) |
| `unused_imports` | `F0701` | `unused` | `warn` | a `use` that nothing in its file uses (see [Unused imports](Lint/Unused.md#unused-imports)) |
| `unused_lint_setting` | `F0791` | `unused` | `warn` | a lint setting that is in effect at no item (see [Unused lint settings](Lint/Unused.md#unused-lint-settings)) |
| `unused_variables` | `F0710` | `unused` | `warn` | a variable or binder that nothing mentions (see [Unused variables](Lint/Unused.md#unused-variables)) |
| `upper_case_acronyms` | `F0750` | `style` | `warn` | a name in `CamelCase` with three or more uppercase letters in a row, such as `HTTPStatus` (see [Names](Lint/Style.md#names)) |
| `wildcard_enum_match_arm` | `F0781` | `restriction` | `allow` | a `_` arm of a `match` (see [Wildcard arms](Lint/Restriction.md#wildcard-arms)) |
| `wildcard_in_or_patterns` | `F0834` | `complexity` | `warn` | an or-pattern with `_` among its alternatives, such as `E::A \| _` (see [Wildcards in or-patterns](Lint/Complexity/Patterns.md#wildcards-in-or-patterns)) |
| `wildcard_single_variant` | `F0728` | `pedantic` | `allow` | a `_` arm that matches only one variant (see [Arms](Lint/Pedantic/Matches.md#arms)) |
| `zero_prefixed_literal` | `F0758` | `complexity` | `warn` | a decimal integer literal with a leading `0`, such as `010` (see [Leading zeros](Lint/Complexity.md#leading-zeros)) |
| `zero_sized_map_values` | `F0789` | `pedantic` | `allow` | a relation type `Rel<A, B>` whose `B` has one value (see [Relations to one value](Lint/Pedantic.md#relations-to-one-value)) |
<!-- keep-sorted end -->

The lints' codes run from `F0701` to `F0843`, and each group's codes start
at `01`. Among them, `F0707`, `F0708` and `F0709` are errors in [setting
levels](#setting-levels), and `F0713` is the removed `shadowed_constants`'s.

Lints are found while elaborating, like [static
errors](View.md#static-errors), and never ask the solver anything: the
results of [checks](Check.md), such as a redundant constraint, are not
lints.

No lint is about shadowing. A declaration that hides a name in scope
without `!`, and one with `!` that hides nothing, are static errors,
`F0217` and `F0218` (see [Shadowing](Lang/Procedures.md#shadowing)). They
replace the lint `shadowed_constants`, which warned of a variable named
like a constant, and whose code `F0713` is not reused.

## Written the same

Many lints compare expressions by their text. Two expressions are *written
the same* if their texts agree but for whitespace and comments: a comment
counts as whitespace, and whitespace that does not separate two names,
numbers or keywords is ignored, except inside string literals, raw ones
too, which are compared as they are. So `x+1` and `x + 1` are written the
same, and so are `f(x)`, `f( x )` and `f(x /- c -/)`, but `"a b"` and
`"ab"` are not. The lints look only at the text, never at types or the
solver, so `x + 1` and `1 + x` are not written the same.

## Levels

| Level | Effect |
|---|---|
| `allow` | not reported |
| `expect` | not reported, but the lint must fire (see [Expecting lints](#expecting-lints)) |
| `warn` | a warning |
| `deny` | an error |
| `forbid` | an error, and the level can no longer be changed |

```fren
pub enum Level { Allow, Expect, Warn, Deny, Forbid }

use self::Level::{Allow, Deny, Expect, Forbid, Warn}
```

`lint::severity` gives the [severity](View.md#severity) of a lint's
message from its level:

```fren
pub proc severity(level: Level): (det result: Severity) {
    use view::Severity::{Error, Info, Silent, Warning}

    ensure rule: result = match level { Allow | Expect => Silent, Warn => Warning, Deny | Forbid => Error }

    expect never_info: result != Info
    expect silent_below_warn: result = Silent iff level in {Allow, Expect}
}
```

A denied lint is a static error, so no check runs, with either front end
(see [Static errors](View.md#static-errors)).

## Groups

Each lint is in exactly one *group*, and its default level is its group's:

<!-- keep-sorted start skip_lines=2 -->
| Group | Default | Lints that |
|---|---|---|
| [`complexity`](Lint/Complexity.md) | `warn` | find a simpler expression with the same meaning |
| [`decidability`](Lint/Decidability.md) | `deny` | find a construct outside the decidable core: `undecidable` alone |
| [`nonstandard_style`](Lint/NonstandardStyle.md) | `warn` | find a name in the wrong case |
| [`pedantic`](Lint/Pedantic.md) | `allow` | are matters of judgement, or would fire on much that reads well as it is |
| [`restriction`](Lint/Restriction.md) | `allow` | forbid what is fine in general, but a project may rule out |
| [`style`](Lint/Style.md) | `warn` | find a clearer way to write the same thing |
| [`suspicious`](Lint/Suspicious.md) | `warn` | find what is probably not what the writer meant |
| [`unused`](Lint/Unused.md) | `warn` | find what is declared but never used |
<!-- keep-sorted end -->

The groups follow those of rustc and Clippy, and a lint modelled on one of
theirs is in the group of the same name: a Clippy lint in `pedantic` or
`restriction` is allowed here too. These are the exceptions:

<!-- keep-sorted start -->
- `eq_op`: Clippy's is in `correctness`, which is denied by default. Fren
  has no `correctness` group, and an operator whose operands are written
  the same still has a meaning, which the spec's checks see, so it is in
  `suspicious`, and `warn`.
- `glob_imports` and `trivial_pattern`: their Clippy counterparts are in
  `pedantic` and `nursery`, but here both are in `style` (see [Trivial
  patterns](Lint/Style.md#trivial-patterns)), so both are `warn`.
- `precedence`: Clippy's is in `complexity`, but here it is in
  `restriction`, and allowed (see [Precedence](Lint/Restriction.md#precedence)).
- `is_equality`: its Clippy counterpart, `equatable_if_let`, is in
  `nursery`, which is about a lint's maturity rather than a judgement of
  style, so it is in `style` (see [Pattern
  tests](Lint/Style/Comparisons.md#pattern-tests)), and `warn`. Like
  `equatable_if_let`, it rewrites only a pattern of one alternative: a test
  of several values stays a pattern test, which
  [`manual_pattern_test`](Lint/Style/PatternTests.md)
  writes, as Clippy never pushes `matches!(x, A | B)` toward
  `[A, B].contains(&x)`.
- `redundant_locals`: Clippy's is in `correctness`. As for `eq_op`, Fren
  has no `correctness` group, and the definition changes no meaning, so it
  is in `suspicious`, and `warn` (see [Redundant
  definitions](Lint/Suspicious.md#redundant-definitions)).
- `redundant_bool_type`: its Clippy counterpart, `redundant_type_annotations`,
  is in `restriction`, which is allowed by default. The `?` of a name
  already gives its type, so the `: Bool` only repeats it: it is in
  `style`, and `warn`.
- `same_branches`: Clippy's `if_same_then_else` is in `style`. Two
  branches written the same are more likely a slip in one of them than a
  matter of style, so it is in `suspicious`. Both are `warn`.
<!-- keep-sorted end -->

```fren
pub enum Group { Unused, NonstandardStyle, Style, Complexity, Suspicious, Pedantic, Restriction, Decidability }

pub proc group_default(group: Group): (det level: Level) {
    ensure rule: level = match group {
        Group::Pedantic | Group::Restriction => Level::Allow,
        Group::Decidability => Level::Deny,
        _ => Level::Warn,
    }

    expect never_expect: not level is Level::Expect | Level::Forbid
}
```

A group's name is never a lint's, and wherever a lint's level is set, a
group's can be, which sets the level of each of its lints. Moving a lint to
another group changes its default level, so it is a breaking change.

## Setting levels

A lint's level is set:

- **On the command line.** `fren check` and `fren trace` take `-A LINT`
  (allow), `-W LINT` (warn), `-D LINT` (deny) and `-F LINT` (forbid), or
  the long forms `--allow`, `--warn`, `--deny` and `--forbid`. In Lean, the command line is the Lean options set outside the
  file, such as `leanOptions` in a Lake package. There is no `expect` on
  the command line: a Lean option set to `expect` outside the file means
  `allow`.
- **In the spec**, with the Lean command `set_option`, which the `fren`
  command also accepts in spec files:

  ```
  lint-setting := "set_option" lint-option STRING ["in" item]
  lint-option  := "fren.lint." IDENT
  ```

  `set_option fren.lint.glob_imports "allow"` sets the level of
  `glob_imports` for the rest of the file (in Lean, for the rest of the
  current `section` or `namespace`, if any). Followed by `in` and an item,
  it sets the level for that item only. The string is one of `allow`,
  `expect`, `warn`, `deny` and `forbid`.

A [group](#groups) is set like a lint, as in `-W pedantic` or `set_option
fren.lint.pedantic "warn"`, and its setting is a setting of each of its
lints, in its place. So `-W pedantic -A match_same_arms` warns of each
pedantic lint but `match_same_arms`.

Each file starts with the levels from the command line, or the defaults
for lints that the command line does not set. On the command line, the last
flag for a lint wins, except that `-F` always wins. In the spec, each
`set_option` replaces the level in effect before it, except that a
forbidden lint keeps its level, and trying to change it is an error at the
`set_option` (`F0709`). Setting `forbid` again is allowed. `lint::setting`
states one such setting:

```fren
pub proc setting(
    current: Level,      -- the level in effect before the setting
    requested: Level,    -- the level the setting asks for
): (det accepted?, det level: Level) {
    ensure forbidden: accepted? iff (current != Forbid or requested = Forbid)
    ensure applied: level = if accepted? then requested else current

    expect forbid_is_final: when current = Forbid, level = Forbid
    expect forbid_is_always_accepted: when requested = Forbid, accepted?
}
```

A group's setting is accepted when each of its lints would accept it, so
when none is forbidden, or when it sets `forbid`; otherwise it is an error
(`F0709`), and changes no level. That is for `set_option`: on the command
line, a group's flag is a flag for each of its lints, in its place, so it
leaves a forbidden lint as it is, and the others take its level. `lint::group_setting` states it, for one
lint of the group:

```fren
pub proc group_setting(
    current: Level,          -- the lint's level before the setting
    n_forbidden: Nat,        -- lints of the group at `forbid` before it
    requested: Level,
): (det accepted?, det level: Level) {
    ensure forbidden: accepted? iff (n_forbidden = 0 or requested = Level::Forbid)
    ensure applied: level = if accepted? then requested else current

    expect forbid_is_always_accepted: when requested = Level::Forbid, accepted? and level = Level::Forbid
    expect blocked_keeps_level: when n_forbidden > 0 and requested != Level::Forbid, level = current
}
```

In Lean, the options set outside the file have no order. There, as on the
command line, `forbid` wins, whether the lint's default, its own option or
its group's sets it, so `fren.lint.pedantic` at `forbid` and
`match_same_arms` at `warn` leave `match_same_arms` forbidden, as
`-F pedantic -W match_same_arms` does. Otherwise a lint's own option wins
over its group's, whichever is set. `lint::outside_options` states it:

```fren
pub proc outside_options(
    default_level: Level,
    own_set?,                -- the lint's own option is set
    own: Level,
    group_set?,              -- its group's option is set
    group: Level,
): (det level: Level) {
    ensure rule: level = if default_level = Level::Forbid or (own_set? and own = Level::Forbid)
        or (group_set? and group = Level::Forbid) then Level::Forbid
        else if own_set? then own else if group_set? then group else default_level

    expect forbid_wins: when group_set? and group = Level::Forbid, level = Level::Forbid
    expect own_wins: when own_set? and own != Level::Forbid and default_level != Level::Forbid
        and not (group_set? and group = Level::Forbid), level = own
}
```

`lint::history` states the rule for a whole file's settings of one lint,
in order: after the first `forbid`, only `forbid`. Naming each other level
says "every later setting" without a quantifier, over the settings after
the first `forbid`, `rest`, a `let` variable with a
[definition](Lang/Procedures.md#definitions). `in` on a sequence that is not
a literal, and `index_of`, are outside the [decidable
core](Lang/Decidability.md#sequences), so the rule opts out:

```fren
set_option fren.lint.undecidable "allow" in
pub proc history(
    settings: Seq<Level>,        -- the levels a file sets for one lint, in order
): (det accepted?) {
    -- The settings after the first `forbid`.
    let rest: Seq<Level> := settings.slice(settings.index_of([Forbid], 0) + 1, settings.len)

    ensure rule: accepted? iff not (Forbid in settings
        and (Allow in rest or Expect in rest or Warn in rest or Deny in rest))

    expect forbid_last: when settings = [Warn, Forbid], accepted?
    expect no_unforbid: when settings = [Forbid, Allow], not accepted?
}
```

If `forbid` is not among the settings, `rest` is what the definition gives,
but `rule` does not look at it then.

That a history is accepted exactly when every step that `lint::setting`
takes along it is accepted cannot be stated for every length without a
fold. For a fixed length it can, by a chain of `lint::setting`s, and
`lint::stepwise` does so for three settings. It starts them from `warn`,
though the level before the first setting may be any level: whatever it
is, `lint::setting` accepts every first setting, unless the level is
`forbid`. That happens only when the command line forbids the lint with
`-F`, where `history` and `fren` differ: `lint::effective` puts the
command line and the settings together. `history` refines it. `history` is outside the decidable
core, so the refinement is checked by testing:

```fren
pub proc stepwise(settings: Seq<Level>): (accepted?) {
    assume three: settings.len = 3

    call first := setting(Warn, settings[0])
    call second := setting(first.level, settings[1])
    call third := setting(second.level, settings[2])

    ensure rule: accepted? iff (first.accepted? and second.accepted? and third.accepted?)

    expect unforbid_last: when settings = [Warn, Forbid, Allow], not accepted?
}

set_option fren.evidence "tested" in
set_option fren.lint.undecidable "allow" in
expect history_is_stepwise(settings: Seq<lint::Level>) {
    use lint
    assume spec_three: (settings).len = 3
    call concrete := history(settings)
    refines concrete stepwise(settings)
}
```

`lint::effective` puts the sources together, for one lint at one place in
a file: its default, then the command line, then the last `set_option`
before that place that is in effect there. Each step is a `lint::setting`.

```fren
pub proc effective(
    default_level: Level,
    cli_set?,            -- the command line sets the lint
    cli: Level,          -- the level it sets
    src_set?,            -- a `set_option` in the file sets the lint here
    src: Level,          -- the level it sets
): (
    det after_cli: Level,         -- the level from the default and the command line
    det level: Level,
    det error?,          -- the `set_option` tries to change a forbidden lint
) {
    assume no_cli_expect: cli != Expect

    ensure cli_rule: after_cli = if cli_set? and (default_level != Forbid or cli = Forbid)
        then cli else default_level
    ensure level_rule: level = if src_set? and (after_cli != Forbid or src = Forbid)
        then src else after_cli
    ensure error_rule: error? iff (src_set? and after_cli = Forbid and src != Forbid)

    expect default_when_unset: when not cli_set? and not src_set?, level = default_level
    expect source_wins: when src_set? and not error?, level = src
    expect forbid_on_cli_is_final: when cli_set? and cli = Forbid, level = Forbid
}
```

The level that applies to a lint's message is the one in effect at the
item it is about: the `use` for the import lints; for the naming lints
and `unused_variables`, the item that declares the name, which for a
member is its procedure and for a variant its enumeration; for `dead_code`
and `single_call_fn`, the item it is about; for
`arbitrary_source_item_ordering`, the procedure; for
`unused_assumption`, its procedure; for `unused_lint_setting`, the setting, before it; for
`invisible_characters`, the item the literal or comment is in (see
[Invisible characters](Lint/Suspicious/Literals.md#invisible-characters)); for
`unnecessary_trailing_comma`, the item the comma is in; and
for `nonminimal_bool` and the other lints of expressions, the item the
expression is in. So
`set_option ... in` before an item sets the level for that item alone.

A `set_option` naming a lint that does not exist is an error (`F0707`),
and so is a level other than the five (`F0708`). In Lean, an option that
does not exist is Lean's own error, worded differently. The `fren` command
accepts no other `set_option` (see [Input files](Cli.md#input-files)).

A lint that was renamed is unknown by its old name, and the `fren` command's
error names the new one: `case_split_reqs` is now `case_split_guarantees`,
since a constraint once written `ensure` is now a guarantee, written `ensure`.

## Messages

A lint's message has the lint's code, and the severity that its level
gives. The first message of each lint in a file also says where its level
comes from. The messages of lints that [`fren fix`](#fixing-lints) can
fix say so:

```text
warning[F0701]: unused import `check::Verdict`
 --> spec.fren:3:5
  |
3 | use check::Verdict
  |     ^^^^^^^^^^^^^^ unused
  |
  = help: remove this `use`
  = help: `fren fix` can fix this
  = note: `unused_imports` is `warn` by default
  = help: to allow it, `set_option fren.lint.unused_imports "allow"`
```

When the level was set, the note says so instead, such as ``note:
`unused_imports` is set to `deny` ``, or, when its group's setting set it,
``note: `membership_chain` is set to `warn` by its group, `pedantic` ``, and
there is no help line.

## Expecting lints

`set_option fren.lint.LINT "expect"` says that the lint should fire where
the setting is in effect: the lint's messages
there are not reported, and if it does not fire at all there, the
`set_option` gets a message from the lint `unfulfilled_lint_expectations`,
at the end of the file. This documents a known lint where it is
deliberate, and points out the setting once it is no longer needed.

A lint *fires* where its condition holds and its level is not `allow`. A
lint that fires is reported with the severity of its level, or, at
`expect`, fulfils the expectation in effect there.

`set_option fren.lint.GROUP "expect"` is one expectation, for every lint
of the group, and any of them that fires there fulfils it.

Each `set_option` to `expect` is its own expectation: a lint that fires
fulfils only the expectation in effect where it fires, so the second of
two such settings in a row is fulfilled only by what follows it. The level
of `unfulfilled_lint_expectations` is the one in effect at the
`set_option`; for it, `expect` means `allow`. `lint::expectation` states
when an expectation is fulfilled:

```fren
pub proc expectation(
    n_fired: Nat,        -- times the lint fires where this expectation is in effect
    level: Level,        -- of `unfulfilled_lint_expectations`, at the `set_option`
): (det fulfilled?, det reported?) {
    ensure fulfilled: fulfilled? iff n_fired > 0
    ensure reported: reported? iff (not fulfilled? and not level in {Allow, Expect})

    expect fired_is_quiet: when n_fired > 0, not reported?
}
```

## Fixing lints

```
fren fix [--check] [--fmt] [--only LINT]... [--skip LINT]... [--ignore GLOB]... [-A|-W|-D|-F LINT]... FILE...
```

`fren fix` reads and elaborates the files as [`fren check`](Cli.md) does,
then rewrites them to fix the lints that fire, where a fix cannot change
what the spec means:

<!-- keep-sorted start skip_lines=2 -->
| Lint | Fix |
|---|---|
| `allow_attributes` | sets the lint to `expect` |
| `almost_complete_range` | replaces the pattern with one that completes each range |
| `arbitrary_source_item_ordering` | puts the members in order, unless a definition or an argument would then come before what it mentions |
| `bool_equality` | replaces `a = b` with `a iff b` |
| `branches_sharing_code` | moves the shared operand out of the `if`, `(if c then a else b) op x` |
| `card_zero` | compares the set with `{}`, as the message suggests |
| `chainable_comparison` | replaces the conjuncts with the chained comparison |
| `collapsible_match` | replaces the arm with one arm for each inner arm but `_`, with the inner pattern nested in the arm's |
| `collapsible_when` | collapses the two conditionals into one, as the message suggests |
| `double_comparison` | replaces the two comparisons with the one they are |
| `double_neg` | replaces `- -x` with `x` |
| `double_parens` | removes all but the innermost pair of parentheses |
| `duplicate_constraint` | removes the later constraint, or cover goal, where the two are of one kind |
| `duplicate_elements` | removes each repeated element, with the `,` before it |
| `else_extends` | puts the `else` branch in parentheses |
| `glob_imports` | imports by name the variants that the file uses through the glob: `use E::*` becomes `use E::{A, B}`, or `use E::A` for a single variant |
| `identity_op` | replaces the operation with the operand it leaves as it is, `x + -y` with `x - y`, and `x - -y` with `x + y` |
| `if_chain_match` | replaces the chain with a `match` |
| `if_not_else` | removes the negation and swaps the branches, as the message suggests |
| `inconsistent_struct_constructor` | writes the fields in the order their record declares them |
| `index_after_use` | swaps the operands of the `and` |
| `int_plus_one` | replaces the comparison with the strict one, without the offset, within its chained comparison if it is in one |
| `invisible_characters` | writes each character as an escape in a literal, and removes it from a comment |
| `is_equality` | replaces `x is E::A` with `x = E::A` |
| `length_zero` | compares the string with `""`, or the sequence with `[]`, as the message suggests |
| `let_and_return` | writes the last definition's expression in place of the body, and removes the definition, or the clause if it has no other |
| `literal_dot_in_pattern` | writes each `.` that it fires on as `[.]` |
| `manual_abs` | replaces the conditional with `x.abs` |
| `manual_abs_diff` | replaces the conditional with the `abs` of its `then` branch, `(a - b).abs` |
| `manual_at_most_one` | replaces the conjuncts with `at_most_one?`, or with `exactly_one?` where the disjunction of the operands is among them |
| `manual_clamp` | replaces the conditional with `x.max(lo).min(hi)` |
| `manual_forall` | replaces the operands with `forall (x: T), e`, or `exists` for `or`, as the message suggests |
| `manual_method` | replaces the comparison with a call of `contains?`, `starts_with?` or `ends_with?`, or `s.slice(i, 1)` with `s.at(i)`, as the message suggests |
| `manual_min_max` | replaces the conditional with `a.min(b)` or `a.max(b)`, as the message suggests |
| `manual_ordering` | replaces the test with a comparison with the last or first variant it names, as the message suggests |
| `manual_pattern_char_comparison` | replaces the pattern with one that writes each alternation of single characters as a class |
| `manual_pattern_test` | replaces the operands with a pattern test, `x is a \| b`, or `not x is a \| b` for the dual |
| `manual_range_patterns` | replaces the or-pattern with the range |
| `manual_record_update` | replaces the literal with an update of the value it copies from, as the message suggests |
| `manual_rem_euclid` | replaces `(a mod k + k) mod k` with `a mod k` |
| `match_bool` | replaces the `match` with `if c? then a else b` |
| `match_like_membership` | replaces the `match` with an equation, `x = E::A`, or a pattern test, `x is E::A \| E::B`, as the message suggests |
| `match_same_arms` | merges the arms into one with an or-pattern, removes those with the body of the `_` arm, or replaces the `match` with its body, as the message suggests |
| `membership_chain` | replaces the chain with a membership, `x in {a, b, c}`, or `not x in {a, b, c}` |
| `needless_bool_assign` | replaces the conditional with `C iff X`, or `C != X` |
| `needless_match` | replaces the `match` with its scrutinee |
| `needless_raw_string_hashes` | writes the fewest `#`s that the literal needs |
| `needless_raw_strings` | writes the literal as an ordinary one |
| `neg_multiply` | replaces `x * -1` or `-1 * x` with `-x` |
| `no_effect_replace` | replaces the call with its receiver |
| `non_ascii_literal` | writes each character beyond ASCII as an escape, where each is up to U+FFFF |
| `nonminimal_bool` | replaces the expression with its simpler form, as the message suggests |
| `overly_complex_bool_expr` | replaces the expression with the operand that stays, or with `false` or `true` |
| `precedence` | puts the operand in parentheses |
| `redundant_bindings` | replaces `x := x` with `x`, and removes a field `x := r.x` of an update of `r`, with a comma |
| `redundant_bool_type` | removes the `: Bool` |
| `redundant_comparisons` | replaces the two comparisons with the one that implies the other, under `and`, or the one that the other implies, under `or` |
| `redundant_method_chain` | replaces the chain with its shorter form |
| `redundant_newtype_roundtrip` | replaces `Ms(x.0)` with `x`, and `Ms(n).0` with `n` |
| `redundant_slicing` | replaces the slice with its receiver |
| `same_branches` | replaces the conditional with its `then` branch, or a table with a `_` row with its value |
| `single_match_else` | replaces the `match` with `if x = E::A then a else b`, or with `x in {...}` or `x is P` as the test, as the message suggests |
| `singleton_membership` | replaces `x in {a}` with `x = a` |
| `suspicious_unary_op_formatting` | moves the whitespace after the `-` to before it: `x >=- 1` becomes `x >= -1` |
| `trivial_match` | replaces the `match` with its arm's body |
| `trivial_pattern` | replaces `s.matches?(p)` with an equation or a call of `starts_with?`, `ends_with?` or `contains?` |
| `trivial_quantifier` | replaces the quantifier with its body, with the value of each bound name in place of its mentions |
| `unfulfilled_lint_expectations` | removes the `set_option`, or for `set_option ... in item`, removes `set_option ... in` and keeps the item |
| `unless_not` | removes the negation and writes `when`, as the message suggests |
| `unnecessary_min_or_max` | replaces the call with the operand it always is |
| `unnecessary_struct_initialization` | replaces the literal with the value it copies |
| `unnecessary_trailing_comma` | removes the comma |
| `unnested_or_patterns` | replaces the alternatives with one, with the or-pattern nested |
| `unused_imports` | removes the `use`, or the name from a grouped `use` |
| `unused_lint_setting` | removes the `set_option`, or for `set_option ... in item`, removes `set_option ... in` and keeps the item |
| `wildcard_enum_match_arm` | names the variants that `_` matches, `E::A \| E::B`, written as for `wildcard_single_variant` |
| `wildcard_in_or_patterns` | replaces the or-pattern with `_` |
| `wildcard_single_variant` | names the variant, `E::V`, or `E::V(_, _)` with one `_` per value of its payload |
| `zero_prefixed_literal` | drops the leading `0`s |
<!-- keep-sorted end -->

Each fix that rewrites an expression keeps what the expression means, for
every value of what it mentions. For `nonminimal_bool`, `length_zero`,
`card_zero`, `singleton_membership`, `membership_chain` and
`manual_pattern_test`, a procedure
in the lint's section states this as laws, which the solver checks: the
written form, which the lint fires on, is on the left of each `iff`, and
the fixed form on the right. Each procedure expects its lints, so it also
checks that each of them fires somewhere in it, though not that it fires
on every form. `index_after_use` is left out: its fix only swaps the
operands of `and`, which means the same either way round, and its written
form has an index that may be out of range, which the
[definedness](Check.md#definedness) check would report in the law itself. For `manual_abs`,
`manual_abs_diff`, `manual_min_max`, `manual_clamp` and
`manual_rem_euclid`, procedures as written and as fixed, and refinements
between them, in the lint's section, check it instead. To keep the meaning, a fix
puts parentheses where [Parentheses in fixes](#parentheses-in-fixes)
says.

The other lints have no fix. Renaming a declaration, as the naming lints
and `struct_field_names` would need, would also have to rename every use
of it, including uses in Lean code and in files that are not given, and so
would removing a dead item, or a function applied once, which
`single_call_fn` reports. Removing an unused variable, or the parameters of an
unused assumption, would change its procedure's interface, and merging the guarantees that `case_split_guarantees`
reports would change what traces, claims and `impl`s name, and so would
removing a constraint that `assertions_on_constants` reports. Writing a
string literal in NFC, as `unicode_not_nfc` suggests, would change its
value. Replacing `Bool`s with an enumeration, as
`struct_excessive_bools` and `fn_params_excessive_bools` suggest, would
change every use of the record or the function. A message of a lint that `fren fix` fixes says so, with the line
`` help: `fren fix` can fix this ``. In Lean, only the messages in a
[Markdown spec](Markdown.md) have this line, since `fren fix` does not read
Lean files.

- A lint is fixed where it fires at `warn`, `deny` or `forbid`, so `-A`
  and the other [level options](#setting-levels) choose what is fixed too.
  A lint at `expect` or `allow` is left as it is.
- `--only LINT` fixes only the lints given, and `--skip LINT` fixes all but
  those given. Both may be repeated, and a lint given to both is not fixed.
- `--ignore GLOB` leaves the matching files as they are. They are still
  read, since the other files may use their modules. Globs are as for
  [`fren fmt`](Fmt.md).
- With `--fmt`, `fren fix` then [formats](Fmt.md) each file that
  `--ignore` does not match, as `fren fmt` would.
- With `--check`, `fren fix` writes nothing, and instead prints what it
  would change, as a diff on standard output.

`lint::Lint` is the lints. `lint::fix_selected` gives whether a lint that
fires is fixed, from the sets given to `--only` and `--skip`, each empty
when the option is not given. A group given to either gives each of its
lints. A lint given twice is given once:

```fren
pub type Lint

pub proc fix_selected(
    lint: Lint,
    only: Set<Lint>,     -- the lints given to `--only`
    skip: Set<Lint>,     -- the lints given to `--skip`
): (det fixed?) {
    ensure rule: fixed? iff ((only = {} or lint in only) and not lint in skip)

    expect default_all: when only = {} and not lint in skip, fixed?
    expect only_excludes: unless only = {} or lint in only, not fixed?
    expect skip_wins: when lint in skip, not fixed?
}

-- Skipping more never fixes more.
expect skip_monotone(
    a_lint: Lint,
    a_only: Set<Lint>,
    a_skip: Set<Lint>,
    b_lint: Lint,
    b_only: Set<Lint>,
    b_skip: Set<Lint>,
) {
    call a := fix_selected(a_lint, a_only, a_skip)
    call b := fix_selected(b_lint, b_only, b_skip)
    expect skip_monotone: when a.lint = b.lint and a.only = b.only and a.skip subset b.skip and b.fixed?, a.fixed?
}
```

The lints that are not fixed are reported as `fren check` reports them. A
static error other than a denied lint stops `fren fix` before it writes
anything. The fixes are found from the files as given, and then again
from the files as fixed, until no fix is left: one fix can overlap
another, of which only the outer is made, or leave something that another
lint fixes. There
are at most 10 passes, in case two fixes undo each other, and a pass whose
fixes would make a static error is not kept. The lints reported are those left
in the files as fixed, or with `--check`, which writes nothing, those that
the first pass does not fix, in the files as given. The fixes do not change the layout of what they
leave behind, which may then need formatting, as `--fmt` does.

`lint::import_fix` gives the fix of one `use` that is not in a group,
from the lints that fire at it and whether each is fixed. For a glob that
is both unused and fixed by `unused_imports`, removing it wins. A glob that
is unused is not imported by name, since nothing would use those names.

```fren
pub enum ImportFix { Keep, Remove, ByName }

pub proc import_fix(
    unused?,             -- `unused_imports` fires at the `use`
    glob?,               -- `glob_imports` fires at it
    fix_unused?,         -- `unused_imports` is fixed: `--only` and `--skip` allow it
    fix_glob?,           -- `glob_imports` is fixed
    n_used: Nat,         -- distinct variants the file uses through it
): (det fix: ImportFix) {
    ensure rule: fix = if unused? and fix_unused? then ImportFix::Remove
        else if glob? and fix_glob? and not unused? and n_used > 0 then ImportFix::ByName
        else ImportFix::Keep

    expect quiet_kept: when not unused? and not glob?, fix = ImportFix::Keep
    expect by_name_is_glob: when fix = ImportFix::ByName, glob?
    expect skipped_kept: when not fix_unused? and not fix_glob?, fix = ImportFix::Keep
}
```

In a grouped `use`, each name is a `use` of its own, which is never a
glob: the names that `lint::import_fix` removes are removed from the group,
and if none is left, so is the `use`.

`lint::fix_exit` gives the exit status:

| Status | Meaning |
|---|---|
| 0 | the files were fixed, or, with `--check`, no file would change |
| 1 | with `--check`: some file would change |
| 2 | nothing was fixed: an unreadable file, bad arguments, or a static error other than a denied lint |

```fren
pub proc fix_exit(
    check?,              -- `--check` was given
    loaded?,             -- every file was read, and has no static error but denied lints
    unchanged?,          -- no file changes: no lint that is fixed fires, and with `--fmt`, every file is formatted
): (det code: Int) {
    ensure failed: unless loaded?, code = 2
    ensure pending: when loaded? and check? and not unchanged?, code = 1
    ensure fixed: when loaded? and (not check? or unchanged?), code = 0

    expect documented_codes: 0 <= code <= 2
}
```

`lint::fix_exit` follows the convention of every command,
[`cli::exit_status`](Cli.md#exit-status), with `fren fix` able to run
exactly when every file is loaded:

```fren
use cli::exit_status

expect fix_exit_status(check?, loaded?, unchanged?) {
    call concrete := fix_exit(check?, loaded?, unchanged?)
    refines concrete exit_status((loaded?))
}
```

### Parentheses in fixes

The lints that rewrite an expression look within the body of a
[`let` or `where`](Lang/Let.md), but not within its definitions. A fix
that rewrites an expression keeps the text of each operand it
writes, and puts an operand, or the fix itself, in parentheses where it is
not already in them and either:

- [`lang::operand`](Lang/Expressions.md#operators) requires them, where a
  conditional counts as binding more loosely than any operator; or
- it ends in an *open-ended* form, and something follows it.

The arguments of an application or a method call, the fields of a
record literal, the elements of a set, relation or sequence literal, an
index, and a `match`'s scrutinee and arms' bodies take an operand as a
`when`'s condition does: any expression but an open-ended one, defined
below, at its top. That is required for a
field or an arm's body, where a `when`, a `let` or a quantifier cannot be
written bare, and for the rest it keeps the reading plain.
An open-ended form is a conditional, a `when`, an `unless`, a
[`let`](Lang/Let.md) or a [quantifier](Lang/Quantifiers.md) that is not in
parentheses, brackets or braces: its last operand, or its body, extends as
far right as possible, so it would take in what follows. A `match` ends
with its `}`, so it is not one. A quantifier binds as loosely as `when`,
and its body is in the place of a `when`'s. A left operand is followed by its operator, and
the condition of a `when` or an `unless` by its `,`. A right operand is
followed by what follows the expression it is an operand of. What is
written in the file follows the fix where it is an infix operator, or the
`.` or `[` after a receiver, after any whitespace and comments. So `(p? or
if q? then r? else s?) = t?` becomes `(p? or if q? then r? else s?) iff
t?`, and `z = (x + if p? then 1 else 2) + 0 and q?` becomes `z = (x + if
p? then 1 else 2) and q?`, but `z = (x + if p? then 1 else 2) + 0` alone
becomes `z = x + if p? then 1 else 2`, as nothing follows it.
