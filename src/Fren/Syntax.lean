-- keep-sorted start
import FrenCore.Names
import Lean
-- keep-sorted end

/-!
# Fren syntax

Everything is `scoped` to `Fren.Lang`: Fren's keywords (`and`, `or`, `iff`,
`pub`, `mod`, ...) are reserved only where `Fren.Lang` is open, so other Lean
code (including Fren's own implementation, in `Fren`) can keep using them as
names. Spec files start with `open Fren.Lang`.

Precedence, lowest first: `when`/`unless`/`let` and the quantifiers, `iff`, `or`, `and`, `not`,
comparisons and `is`, `+ -`, `* div mod`, unary `-`; `if` is an atom whose
`else` branch extends as far right as possible.

A comparison's or `is`'s left operand may itself be a comparison or an
`is`, so that `a < b <= c` parses as `(a < b) <= c`: the elaborator reads
that as a chained comparison (`Reqs/Lang/Expressions#chained-comparisons`),
and rejects the chains that Fren does not have, such as `a = b = c` and
`a < b is P`, with the `fren` command's message.
-/

namespace Fren.Lang

declare_syntax_cat fren_expr (behavior := both)

open Lean Parser in
/-- One of Lean's tokens that are an identifier followed by `!`
(`Fren.Core.leanBangTokens`), read as that identifier, so that a
declaration of it reaches the elaborator, which rejects it as the `fren`
command does. -/
def bangTokenFn : ParserFn := fun c s =>
  let iniSz := s.stackSize
  let iniPos := s.pos
  let s := tokenFn [] c s
  if s.hasError then s.restore iniSz iniPos |>.mkErrorAt "identifier" iniPos
  else match s.stxStack.back with
    | .atom info val =>
      if Fren.Core.leanBangTokens.contains val then
        s.popSyntax.pushSyntax (.ident info val.toRawSubstring (.mkSimple val) [])
      else s.restore iniSz iniPos |>.mkErrorAt "identifier" iniPos
    | _ => s.restore iniSz iniPos |>.mkErrorAt "identifier" iniPos

open Lean Parser in
/-- An identifier of Fren: one of Lean's, or one of the tokens of
`bangTokenFn`. -/
def frenIdent : Parser :=
  withAntiquot (mkAntiquot "ident" identKind) (identNoAntiquot <|>
    { fn := bangTokenFn, info := { firstTokens := .tokens Fren.Core.leanBangTokens } })

open Lean PrettyPrinter in
@[combinator_formatter frenIdent] def frenIdent.formatter : Formatter := Formatter.identNoAntiquot.formatter

open Lean PrettyPrinter in
@[combinator_parenthesizer frenIdent] def frenIdent.parenthesizer : Parenthesizer :=
  Parenthesizer.identNoAntiquot.parenthesizer

/-- A `::`-separated path, e.g. `check::Verdict::Pass` or `self::Outcome`. -/
syntax fren_path := sepBy1(frenIdent, "::")

declare_syntax_cat fren_type (behavior := both)
/-- A type named by a path: `Bool`, `Int`, `String`, or an item. -/
syntax fren_path : fren_type
/-- `Set(T)`. -/
syntax (name := setType) &"Set" noWs "(" fren_type ")" : fren_type
/-- `Seq(T)`. -/
syntax (name := seqType) &"Seq" noWs "(" fren_type ")" : fren_type
/-- `Rel(A, B)`. -/
syntax (name := relType) &"Rel" noWs "(" fren_type ", " fren_type ")" : fren_type

open Lean Parser in
/-- The expression of a definition of a `let`: below `when`, which would
run on into the next definition, and ended by `in` outside brackets, so
that a membership there is written in parentheses (`Reqs/Lang/Let`). -/
def letValue : Parser := withForbidden "in" (categoryParser `fren_expr 20)

open Lean PrettyPrinter in
@[combinator_formatter letValue] def letValue.formatter : Formatter := Formatter.categoryParser.formatter `fren_expr

open Lean PrettyPrinter in
@[combinator_parenthesizer letValue] def letValue.parenthesizer : Parenthesizer :=
  Parenthesizer.categoryParser.parenthesizer `fren_expr 20

/-- `x := e` or `x: T := e`, a definition of a `let`. -/
syntax fren_let_def := frenIdent (" : " fren_type)? " := " letValue

/-- `x := e` or `x: T := e`, a definition of a `where` clause; like a
binding's, the expression cannot be a bare `when`, `unless` or `let`. -/
syntax fren_def := frenIdent (" : " fren_type)? " := " fren_expr:20

/-- `where x := e, ...`, after the whole expression of a constraint, a
definition, a function's body or a constant's value. -/
syntax fren_where := " where " sepBy1(fren_def, ", ")

/-- `let x := e, y := f in b`; like `when`, its body extends as far right
as possible. Its own `in` ends its definitions even within those of
another `let`, whose restriction its body keeps. -/
scoped syntax:10 (name := letExpr) "let " sepBy1(fren_let_def, ", ") withoutForbidden(" in ") fren_expr:10 : fren_expr

/-- `(x y: T)`: a binder of a quantifier, over the values of `T`, or of a
global expectation's leading `forall`, where it may name a component and
range over its behaviours (`Reqs/Lang/Quantifiers`). -/
syntax fren_binder := "(" frenIdent+ " : " fren_type ")"

/-- `forall (x: T), e` and `exists (x: T), e`, quantifiers over a finite
type, at the precedence of `when`. -/
scoped syntax:10 (name := quantExpr) ("forall " <|> "exists ") fren_binder+ ", " fren_expr:10 : fren_expr
scoped syntax:10 &"when " fren_expr:20 ", " fren_expr:10 : fren_expr
scoped syntax:10 &"unless " fren_expr:20 ", " fren_expr:10 : fren_expr
scoped syntax:20 fren_expr:21 " iff " fren_expr:21 : fren_expr
scoped syntax:30 fren_expr:30 " or " fren_expr:31 : fren_expr
scoped syntax:35 fren_expr:35 " and " fren_expr:36 : fren_expr
scoped syntax:40 &"not " fren_expr:40 : fren_expr
scoped syntax:50 fren_expr:50 " = " fren_expr:51 : fren_expr
scoped syntax:50 fren_expr:50 " != " fren_expr:51 : fren_expr
scoped syntax:50 fren_expr:50 " < " fren_expr:51 : fren_expr
scoped syntax:50 fren_expr:50 " <= " fren_expr:51 : fren_expr
scoped syntax:50 fren_expr:50 " > " fren_expr:51 : fren_expr
scoped syntax:50 fren_expr:50 " >= " fren_expr:51 : fren_expr
scoped syntax:65 fren_expr:65 " + " fren_expr:66 : fren_expr
scoped syntax:65 fren_expr:65 " - " fren_expr:66 : fren_expr
scoped syntax:65 fren_expr:65 " ++ " fren_expr:66 : fren_expr
/-! The set operators are reserved words where `Fren.Lang` is open: Lean
indexes an operator after an operand by its token, so it cannot be an
identifier. -/
scoped syntax:50 (name := subsetExpr) fren_expr:50 " subset " fren_expr:51 : fren_expr
scoped syntax:65 (name := unionExpr) fren_expr:65 " union " fren_expr:66 : fren_expr
scoped syntax:65 (name := minusExpr) fren_expr:65 " minus " fren_expr:66 : fren_expr
scoped syntax:70 (name := interExpr) fren_expr:70 " inter " fren_expr:71 : fren_expr
scoped syntax:70 (name := joinExpr) fren_expr:70 " join " fren_expr:71 : fren_expr

open Lean Parser in
/-- Succeeds if the next token is on the line where the syntax before it,
the left operand of a trailing parser, ends; `what` names that token, as
`the `in` of a membership`, for the error. -/
def sameLineAsLeft (what : String) : Parser where
  fn := fun c s =>
    match s.stxStack.back.getTailPos? with
    | some p =>
      if (c.fileMap.toPosition p).line == (c.fileMap.toPosition s.pos).line then s
      else s.mkError s!"{what} on the line of its left operand"
    | none => s

open Lean PrettyPrinter in
@[combinator_formatter sameLineAsLeft] def sameLineAsLeft.formatter (_ : String) : Formatter := pure ()

open Lean PrettyPrinter in
@[combinator_parenthesizer sameLineAsLeft] def sameLineAsLeft.parenthesizer (_ : String) : Parenthesizer := pure ()

open Lean Parser in
/-- `x in s`, membership. Its `in` must be on the line where `x` ends, so
that an `in` starting a line starts an input (`Reqs/Lang/Lexical`). -/
@[scoped fren_expr_parser] def memberExpr := trailing_parser:50:50 sameLineAsLeft "the `in` of a membership" >> " in " >> categoryParser `fren_expr 51

/-- `{a, b}`, a set literal; `{}` is the empty set. -/
scoped syntax:max (name := setExpr) "{" withoutForbidden(sepBy(fren_expr, ", ", ", ", allowTrailingSep)) "}" : fren_expr
scoped syntax:70 fren_expr:70 " * " fren_expr:71 : fren_expr
scoped syntax:70 (name := divExpr) fren_expr:70 " div " fren_expr:71 : fren_expr

open Lean Parser in
/-- `a mod k`, the remainder. Its `mod` must be on the line where `a` ends,
so that a `mod` starting a line starts a module (`Reqs/Lang/Lexical`). -/
@[scoped fren_expr_parser] def modExpr := trailing_parser:70:70 sameLineAsLeft "the `mod` of a remainder" >> " mod " >> categoryParser `fren_expr 71

scoped syntax:75 "-" fren_expr:75 : fren_expr
/-! Operators of other languages, parsed only to say what to write instead
(`Fren.Core.foreignOpMsg`). -/
scoped syntax:50 fren_expr:51 " == " fren_expr:51 : fren_expr
scoped syntax:35 fren_expr:35 " && " fren_expr:36 : fren_expr
scoped syntax:30 fren_expr:30 " || " fren_expr:31 : fren_expr
scoped syntax:30 fren_expr:30 " | " fren_expr:31 : fren_expr
scoped syntax:40 "!" fren_expr:40 : fren_expr
/-- `<-`, a Lean token, parsed only to say that it is not `< -`
(`Fren.Core.leftArrowMsg`). -/
scoped syntax:50 fren_expr:51 " <- " fren_expr:51 : fren_expr
/-- Like Lean's `if`, it can be an operand without parentheses, and the
`else` branch extends as far right as possible. Its condition and `then`
branch are delimited, so `in` is a membership there even in a definition
of a `let`, as in `match`'s scrutinee. -/
scoped syntax:max "if " withoutForbidden(fren_expr) " then " withoutForbidden(fren_expr) " else " fren_expr : fren_expr
scoped syntax:max num : fren_expr
/-- A string literal, raw or not. -/
scoped syntax:max str : fren_expr
scoped syntax:max &"true" : fren_expr
scoped syntax:max &"false" : fren_expr
scoped syntax:max fren_path : fren_expr
/-- `f(a, b)`, a function application. -/
scoped syntax:max (name := appExpr) fren_path noWs "(" withoutForbidden(sepBy1(fren_expr, ", ")) ")" : fren_expr
/-- `exactly_one?()` or `at_most_one?()`, a cardinality operator without
arguments, which parses so that the elaborator reports it, as the `fren`
command does. -/
scoped syntax:max (name := noArgsCardinalityExpr) (&"exactly_one?" <|> &"at_most_one?") noWs "(" ")" : fren_expr
scoped syntax:max "(" withoutForbidden(fren_expr) ")" : fren_expr
/-- `[a, b]`, a sequence literal; `[]` is the empty sequence. -/
scoped syntax:max (name := seqExpr) "[" withoutForbidden(sepBy(fren_expr, ", ", ", ", allowTrailingSep)) "]" : fren_expr
/-- `q[i]`, indexing, with no space before `[`. -/
scoped syntax:max (name := indexExpr) fren_expr:max noWs "[" withoutForbidden(fren_expr) "]" : fren_expr
/-- `(a, b)`, a pair: a member of a relation literal, or the left of `in`. -/
scoped syntax:max (name := pairExpr) "(" withoutForbidden(fren_expr) ", " withoutForbidden(fren_expr) ")" : fren_expr

/-- `x := e`, or `x` for `x := x`. The expression cannot be a bare
`when`/`unless`, which would swallow the following bindings. -/
syntax fren_binding := frenIdent (" := " fren_expr:20)?

/-- `R { x := e, y }`, a record literal. Its precedence is below `max`, so
that a `match`'s scrutinee, parsed at `max`, never tries it: `match s {`
starts the arms. -/
scoped syntax:arg (name := recordExpr) fren_path " { " withoutForbidden(sepBy1(fren_binding, ", ", ", ", allowTrailingSep)) " }" : fren_expr
/-- `{ r with x := e, y }`, a record update. Like a set literal, it starts
with `{`; `with` after the first expression makes it an update. `with` is
one of Lean's keywords, so it is never a name. -/
scoped syntax:max (name := updateExpr) "{ " withoutForbidden(fren_expr:20) " with " withoutForbidden(sepBy1(fren_binding, ", ", ", ", allowTrailingSep)) " }" :
  fren_expr
open Lean Parser in
/-- The decimal digits that name a field after `.`, as in `x.0`, read as
Lean reads a field index (`Lean.Parser.fieldIdxFn`), but from `0`: not as a
number, which in `x.0.0` would be the scientific literal `0.0`. -/
def fieldDigitsFn : ParserFn := fun c s =>
  let iniSz := s.stackSize
  let iniPos := s.pos
  if (c.get iniPos).isDigit then
    let s := takeWhileFn Char.isDigit c s
    mkNodeToken fieldIdxKind iniPos true c s
  else s.mkErrorAt "field" iniPos iniSz

open Lean Parser in
/-- `0` in `x.0`, the field of a newtype (`fieldDigitsFn`). -/
def fieldDigits : Parser :=
  withAntiquot (mkAntiquot "fieldIdx" `fieldIdx) { fn := fieldDigitsFn, info := mkAtomicInfo "fieldIdx" }

open Lean PrettyPrinter in
@[combinator_formatter fieldDigits] def fieldDigits.formatter : Formatter := Formatter.fieldIdx.formatter

open Lean PrettyPrinter in
@[combinator_parenthesizer fieldDigits] def fieldDigits.parenthesizer : Parenthesizer :=
  Parenthesizer.fieldIdx.parenthesizer

/-- `e.x`, reading a field of `e`, an atom that ends in `)` or `}`: after a
name, `.x` is part of the (dotted) identifier. `x.0`, the field of a
newtype, follows any atom, a name too, since digits never continue an
identifier. -/
scoped syntax:max (name := fieldExpr) fren_expr:arg noWs "." noWs (fieldDigits <|> frenIdent) : fren_expr
/-- `e.m(a, b)`, a method call on an atom that ends in `)` or `}`; on a name,
`x.m(a)` is parsed as an application of the dotted name. -/
scoped syntax:max (name := methodExpr) fren_expr:arg noWs "." noWs (frenIdent <|> "at") noWs "(" withoutForbidden(sepBy1(fren_expr, ", ")) ")" : fren_expr

/-! Patterns (`Reqs/Lang/Patterns`). -/

declare_syntax_cat fren_bound
/-- A bound of a range: an integer, possibly negated. -/
syntax (name := numBound) ("-")? num : fren_bound
/-- A bound of a range: a constant. -/
syntax (name := pathBound) fren_path : fren_bound

/-- An alternative of an or-pattern, or a pattern of a payload. -/
declare_syntax_cat fren_pattern
/-- `A | B`, an or-pattern, or one pattern. -/
syntax fren_or_pattern := sepBy1(fren_pattern, " | ")
/-- `_`, matching any value. -/
syntax (name := wildPattern) "_" : fren_pattern
/-- An integer literal, possibly negated. -/
syntax (name := numPattern) ("-")? num : fren_pattern
/-- A string literal, raw or not. -/
syntax (name := strPattern) str : fren_pattern
/-- `x`, `E::V` or `E::V(p, q)`: a path of one segment, not applied, is a
binder, `true`, `false` or a variant, once resolved (`lang::pattern_name`). -/
syntax (name := variantPattern) fren_path (noWs "(" sepBy1(fren_or_pattern, ", ") ")")? : fren_pattern
/-! The ranges are scoped, so that `..=` is a token only where `Fren.Lang`
is open, and are written without spaces around `..=` and `..`. -/
/-- `a..=b` -/
scoped syntax (name := rangePattern) fren_bound noWs "..=" noWs fren_bound : fren_pattern
/-- `a..b` and `a..` -/
scoped syntax (name := fromPattern) fren_bound noWs ".." (noWs fren_bound)? : fren_pattern
/-- `..=b` -/
scoped syntax (name := uptoPattern) "..=" noWs fren_bound : fren_pattern

/-- The pattern of a `match` arm or of `is`: an or-pattern, optionally
after a leading `|`. -/
syntax fren_top_pattern := ("| ")? sepBy1(fren_pattern, " | ")

/-- `pattern => e`; like a binding's, the expression cannot be a bare
`when`/`unless`. -/
syntax fren_arm := fren_top_pattern " => " fren_expr:20

/-- `match e { pattern => e, ... }`. -/
scoped syntax:max (name := matchExpr) "match " withoutForbidden(fren_expr:max) " { " withoutForbidden(sepBy(fren_arm, ", ", ", ", allowTrailingSep)) " }" : fren_expr

/-- A row of a table: `C => e`, or `_ => e`, optionally after `|`. Like a
`match` arm's body, neither the condition nor the value can be a bare
`when`/`unless`. -/
syntax fren_row := ("| ")? ("_" <|> fren_expr:20) " => " fren_expr:20

/-- `table { C => e, ... }`, a condition table. `table` is a reserved word
where `Fren.Lang` is open. -/
scoped syntax:max (name := tableExpr) "table " "{ " sepBy1(fren_row, ", ", ", ", allowTrailingSep) " }" : fren_expr

/-- `e is P`, a pattern test, at the precedence of the comparisons. `is`
is a reserved word where `Fren.Lang` is open, as the set operators are. -/
scoped syntax:50 (name := isExpr) fren_expr:50 " is " fren_top_pattern : fren_expr

declare_syntax_cat fren_member (behavior := both)

/-- `in x: T`; a definition, `:= e`, is parsed only to report that inputs
cannot have one. -/
scoped syntax (name := inMember) "in " frenIdent (" : " fren_type)? (" := " fren_expr)? : fren_member
/-- `[pub] [det] out x: T [:= e]`: `det` asks for the determinism check, and
`:= e` makes it a defined output. -/
scoped syntax (name := outMember) ("pub ")? (&"det ")? &"out " frenIdent (" : " fren_type)? (" := " fren_expr (fren_where)?)? : fren_member
scoped syntax (name := assumeMember) &"assume " frenIdent " : " fren_expr (fren_where)? : fren_member
scoped syntax (name := reqMember) &"req " frenIdent " : " fren_expr (fren_where)? : fren_member
scoped syntax (name := expectMember) &"expect " frenIdent " : " fren_expr (fren_where)? : fren_member
/-- `cover n: e`, a scenario that the component must allow (`Reqs/Lang/Components#cover-goals`). -/
scoped syntax (name := coverMember) &"cover " frenIdent " : " fren_expr (fren_where)? : fren_member

/-- `inst w: c { x := e, ... }`: an instance `w` of comp `c`. -/
scoped syntax (name := instMember) &"inst " frenIdent " : " fren_path " { " sepBy(fren_binding, ", ", ", ", allowTrailingSep) " }" : fren_member
/-- `use`, as a member: its names are in scope in the component only. -/
scoped syntax (name := useMember) "use " fren_path ("::*")? : fren_member
scoped syntax (name := useGroupMember) "use " fren_path "::{" sepBy1(fren_path, ", ", ", ", allowTrailingSep) "}" : fren_member
/-- `set_option fren.evidence "tested" in`, before a member whose checks it
sets (`Reqs/Check#checking-by-testing`). -/
scoped syntax (name := evidenceMember) "set_option " ident ppSpace str " in " fren_member : fren_member

/-- `mod a::b` makes `a::b` the current module for the rest of the file. -/
scoped syntax (name := modCmd) ("pub ")? "mod " fren_path : command

/-- `use a::b::c` imports an item; `use a::E::*` opens enum `E`. Lean lexes
`::*` as one token, so it is written without spaces. -/
scoped syntax (name := useCmd) "use " fren_path ("::*")? : command

/-- `use a::{b, c::d}` is `use a::b` and `use a::c::d`. Like `::*`, `::{` is
one token. -/
scoped syntax (name := useGroupCmd) "use " fren_path "::{" sepBy1(fren_path, ", ", ", ", allowTrailingSep) "}" : command

/-- `V` or `V(T, U)`, a variant with a payload. -/
syntax fren_variant := frenIdent (noWs "(" sepBy1(fren_type, ", ") ")")?

/-- `[pub] [ordered] enum E { A, B }`: `ordered` orders the variants as they
are declared (`Reqs/Lang/Items#enumerations`). -/
scoped syntax (name := enumCmd) ("pub ")? ("ordered ")? "enum " frenIdent " { " sepBy1(fren_variant, ", ", ", ", allowTrailingSep) " }" : command

/-- `x: T`, or `x?` for a `Bool`. -/
syntax fren_field := frenIdent (" : " fren_type)?

/-- `struct R { x: T, ... }`, a record. -/
scoped syntax (name := structCmd) ("pub ")? "struct " frenIdent " { " sepBy1(fren_field, ", ", ", ", allowTrailingSep) " }" : command

/-- `struct N(T)`, a newtype; its parentheses must hold one type
(`lang::newtype`), which the elaborator checks. -/
scoped syntax (name := newtypeCmd) ("pub ")? "struct " frenIdent "(" sepBy(fren_type, ", ") ")" : command

scoped syntax (name := compCmd) ("pub ")? "comp " frenIdent " { " fren_member* " }" : command

/-- `type T`, an abstract type. -/
scoped syntax (name := typeCmd) ("pub ")? "type " frenIdent : command

/-- A function's parameter: `T` of an uninterpreted function, `x: T` or
`x?` of a defined one. Which it is depends on whether the function has a
body (`lang::function_params`). -/
syntax fren_param := fren_type (" : " fren_type)?

/-- `fn f(T, U): R`, an uninterpreted function, or `fn f(x: T): R := e`, a
defined one. -/
scoped syntax (name := fnCmd) ("pub ")? "fn " frenIdent noWs "(" sepBy1(fren_param, ", ") ")" (" : " fren_type)?
  (" := " fren_expr (fren_where)?)? : command

/-- `const N: T := e`. -/
scoped syntax (name := constCmd) ("pub ")? "const " frenIdent " : " fren_type " := " fren_expr (fren_where)? : command


/-- `expect n: forall (a b: c), e`, a global expectation. -/
scoped syntax (name := globalCmd) "expect " frenIdent " : " ("forall " fren_binder+ ", ")? fren_expr (fren_where)? : command

/-- `refine r: c refines a [{ bindings }] [by tactics]`, a refinement
(`Reqs/Lang/Refinement`). -/
scoped syntax (name := refineCmd) "refine " frenIdent " : " fren_path ppSpace &"refines " fren_path
  (" { " sepBy(fren_binding, ", ", ", ", allowTrailingSep) " }")? (" by " Lean.Parser.Tactic.tacticSeq)? : command


end Fren.Lang
