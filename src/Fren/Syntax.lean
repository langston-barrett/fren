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
(`Fren.Core.leanBangTokens`), or one of Lean's keywords that have the shape
of an identifier (`Fren.Core.leanKeywords`), read as that identifier, so
that a declaration of it reaches the elaborator, which rejects it as the
`fren` command does. -/
def bangTokenFn : ParserFn := fun c s =>
  let iniSz := s.stackSize
  let iniPos := s.pos
  let s := tokenFn [] c s
  if s.hasError then s.restore iniSz iniPos |>.mkErrorAt "identifier" iniPos
  else match s.stxStack.back with
    | .atom info val =>
      if Fren.Core.leanBangTokens.contains val || Fren.Core.leanKeywords.contains val then
        s.popSyntax.pushSyntax (.ident info val.toRawSubstring (.mkSimple val) [])
      else s.restore iniSz iniPos |>.mkErrorAt "identifier" iniPos
    | _ => s.restore iniSz iniPos |>.mkErrorAt "identifier" iniPos

open Lean Parser in
/-- An identifier of Fren: one of Lean's, or one of the tokens of
`bangTokenFn`. -/
def frenIdent : Parser :=
  withAntiquot (mkAntiquot "ident" identKind) (identNoAntiquot <|>
    { fn := bangTokenFn, info := { firstTokens := .tokens (Fren.Core.leanBangTokens ++ Fren.Core.leanKeywords) } })

open Lean Parser in
/-- Fails if the next token is one of `Fren.Core.leanKeywords`, which
`frenIdent` would read as an identifier: where an optional path ends a
command, as in `#fren_check`, a keyword that follows starts the next
command. -/
def notLeanKeyword : Parser where
  fn := fun c s =>
    let iniSz := s.stackSize
    let iniPos := s.pos
    let t := tokenFn [] c s
    let keyword := !t.hasError && match t.stxStack.back with
      | .atom _ val => Fren.Core.leanKeywords.contains val
      | _ => false
    let s := t.restore iniSz iniPos
    if keyword then s.mkErrorAt "a path" iniPos else s

open Lean PrettyPrinter in
@[combinator_formatter notLeanKeyword] def notLeanKeyword.formatter : Formatter := pure ()

open Lean PrettyPrinter in
@[combinator_parenthesizer notLeanKeyword] def notLeanKeyword.parenthesizer : Parenthesizer := pure ()

open Lean PrettyPrinter in
@[combinator_formatter frenIdent] def frenIdent.formatter : Formatter := Formatter.identNoAntiquot.formatter

open Lean PrettyPrinter in
@[combinator_parenthesizer frenIdent] def frenIdent.parenthesizer : Parenthesizer :=
  Parenthesizer.identNoAntiquot.parenthesizer

/-- A `::`-separated path, e.g. `check::Verdict::Pass` or `self::Outcome`. -/
syntax fren_path := sepBy1(frenIdent, "::")

open Lean Parser in
/-- The `>` that closes type arguments or type parameters: one character,
so that in `Option<Set<Int>>` the `>>` that Lean lexes as one token closes
both (`Reqs/Lang/Generics#angle-brackets`). -/
def closeAngle : Parser where
  fn := fun c s =>
    if c.atEnd s.pos || c.get s.pos != '>' then s.mkErrorAt "'>'" s.pos
    else (rawCh '>' (trailingWs := true)).fn c s
  info := (rawCh '>' (trailingWs := true)).info

open Lean PrettyPrinter in
@[combinator_formatter closeAngle] def closeAngle.formatter : Formatter := Formatter.symbolNoAntiquot.formatter ">"

open Lean PrettyPrinter in
@[combinator_parenthesizer closeAngle] def closeAngle.parenthesizer : Parenthesizer :=
  Parenthesizer.symbolNoAntiquot.parenthesizer ">"

declare_syntax_cat fren_type (behavior := both)
/-- A type named by a path: `Bool`, `Int`, `String`, or an item. -/
syntax fren_path : fren_type
/-- `Set<T>`. -/
syntax (name := setType) &"Set" noWs "<" fren_type closeAngle : fren_type
/-- `Seq<T>`. -/
syntax (name := seqType) &"Seq" noWs "<" fren_type closeAngle : fren_type
/-- `Rel<A, B>`. -/
syntax (name := relType) &"Rel" noWs "<" fren_type ", " fren_type closeAngle : fren_type
/-- `G<A, B>`, an instance of a generic type (`Reqs/Lang/Generics`). Below
`Set<T>`, `Seq<T>` and `Rel<A, B>`, which it would also read. -/
syntax (name := instanceType) (priority := low) fren_path noWs "<" sepBy1(fren_type, ", ") closeAngle : fren_type
/-- `G(A, B)`, a type with its type arguments in parentheses, as they were
written before they were written in angle brackets: parsed only so that
the elaborator reports it, as the `fren` command does (`F0155`). -/
syntax (name := parenType) (priority := low) fren_path noWs "(" sepBy1(fren_type, ", ") ")" : fren_type

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
global expectation's leading `forall`, where it may name a procedure and
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

/-- `pattern => e`, or `pattern if C => e` with a guard; like a binding's,
neither the guard nor the expression can be a bare `when`/`unless`. -/
syntax fren_arm := fren_top_pattern (" if " fren_expr:20)? " => " fren_expr:20

/-- `match e { pattern => e, ... }`. -/
scoped syntax:max (name := matchExpr) "match " withoutForbidden(fren_expr:max) " { " withoutForbidden(sepBy(fren_arm, ", ", ", ", allowTrailingSep)) " }" : fren_expr

/-- A row of a table: `C => e`, or `_ => e`, optionally after `|`. Like a
`match` arm's body, neither the condition nor the value can be a bare
`when`/`unless`. -/
syntax fren_row := ("| ")? ("_" <|> fren_expr:20) " => " fren_expr:20

/-- `table { C => e, ... }`, a condition table. `table` is a reserved word
where `Fren.Lang` is open. -/
scoped syntax:max (name := tableExpr) "table " "{ " sepBy1(fren_row, ", ", ", ", allowTrailingSep) " }" : fren_expr

/-- `table e { pattern => e, ... }`, a table over a scrutinee: the `match`
whose arms are disjoint (`Reqs/Lang/Expressions#tables-over-a-scrutinee`).
Its parts are where a `match`'s are. `{` right after `table` starts the
rows of a table by conditions, so the scrutinee does not start with it. -/
scoped syntax:max (name := tableMatchExpr) "table " notFollowedBy("{") withoutForbidden(fren_expr:max) " { "
  withoutForbidden(sepBy1(fren_arm, ", ", ", ", allowTrailingSep)) " }" : fren_expr

/-- `e is P`, a pattern test, at the precedence of the comparisons. `is`
is a reserved word where `Fren.Lang` is open, as the set operators are. -/
scoped syntax:50 (name := isExpr) fren_expr:50 " is " fren_top_pattern : fren_expr

/-- `T is P`, a pattern type: the values of `T` that match `P`
(`Reqs/Lang/Types#pattern-types`). Its base type is never itself a pattern
type, so a second `is` does not parse. -/
scoped syntax:10 (name := patType) fren_type:11 " is " fren_top_pattern : fren_type

declare_syntax_cat fren_member (behavior := both)

/-- `in x: T`, an input as components declared them, parsed only so that
the elaborator reports it (`F0159`); a definition, `:= e`, is parsed only
to report that inputs cannot have one. -/
scoped syntax (name := inMember) "in " frenIdent (" : " fren_type)? (" := " fren_expr)? : fren_member
/-- `out r := e`, the definition of the result `r`; any other form, `[pub]
[det] out x: T [:= e]`, is an output as components declared them, which the
elaborator reports (`F0160`). -/
scoped syntax (name := outMember) ("pub ")? (&"det ")? &"out " frenIdent (" : " fren_type)? (" := " fren_expr (fren_where)?)? : fren_member
scoped syntax (name := assumeMember) &"assume " frenIdent " : " fren_expr (fren_where)? : fren_member
scoped syntax (name := ensureMember) &"ensure " frenIdent " : " fren_expr (fren_where)? : fren_member
scoped syntax (name := expectMember) &"expect " frenIdent " : " fren_expr (fren_where)? : fren_member
/-- `cover n: e`, a scenario that the procedure must allow (`Reqs/Lang/Procedures#cover-goals`). -/
scoped syntax (name := coverMember) &"cover " frenIdent " : " fren_expr (fren_where)? : fren_member

/-- `[det] exists x: T`: a private variable that the system chooses
(`Reqs/Lang/Procedures#members`). -/
scoped syntax (name := existsMember) (&"det ")? "exists " frenIdent (" : " fren_type)? : fren_member
/-- `[det] let x: T := e`: a private variable defined by `e`. -/
scoped syntax (name := letMember) (&"det ")? "let " frenIdent (" : " fren_type)? " := " fren_expr (fren_where)? : fren_member
/-- `call w := p(a, b)`: a call `w` of the procedure `p`, with an argument
for each of its parameters, in order. -/
scoped syntax (name := callMember) &"call " frenIdent " := " fren_path noWs "("
  withoutForbidden(sepBy(fren_expr, ", ", ", ", allowTrailingSep)) ")" : fren_member
/-- `inst w: c { x := e, ... }`: an instance, as calls were written before
they were calls, parsed only so that the elaborator reports it (`F0420`). -/
scoped syntax (name := instMember) &"inst " frenIdent " : " fren_path " { " sepBy(fren_binding, ", ", ", ", allowTrailingSep) " }" : fren_member
/-- `use`, as a member: its names are in scope in the procedure only. -/
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

/-- `<A, B>`, the type parameters of an enumeration, a record or a function
(`Reqs/Lang/Generics`). -/
syntax fren_type_params := "<" sepBy1(frenIdent, ", ") closeAngle

/-- `(A, B)`, type parameters in parentheses, as they were written before
they were written in angle brackets: parsed only so that the elaborator
reports them, as the `fren` command does (`F0156`). -/
syntax fren_paren_type_params := "(" sepBy1(frenIdent, ", ") ")"

/-- `[pub] [ordered] enum E { A, B }`: `ordered` orders the variants as they
are declared (`Reqs/Lang/Items#enumerations`); with type parameters,
`enum E<T> { ... }`. -/
scoped syntax (name := enumCmd) ("pub ")? ("ordered ")? "enum " frenIdent (noWs (fren_type_params <|> fren_paren_type_params))? " { " sepBy1(fren_variant, ", ", ", ", allowTrailingSep) " }" : command

/-- `x: T`, or `x?` for a `Bool`. -/
syntax fren_field := frenIdent (" : " fren_type)?

/-- `[pub] [ordered] struct R { x: T, ... }`, a record; `ordered` orders its
values by their fields (`Reqs/Lang/Items#ordered-declarations`). With type
parameters, `struct R<A, B> { ... }`, which the `{` tells apart from a
newtype. -/
scoped syntax (name := structCmd) ("pub ")? ("ordered ")? "struct " frenIdent (noWs (fren_type_params <|> fren_paren_type_params))? " { " sepBy1(fren_field, ", ", ", ", allowTrailingSep) " }" : command

/-- `[pub] [ordered] struct N(T)`, a newtype; its parentheses must hold one
type (`lang::newtype`), which the elaborator checks. -/
scoped syntax (name := newtypeCmd) ("pub ")? ("ordered ")? "struct " frenIdent noWs "(" sepBy(fren_type, ", ") ")" : command

/-- `comp c { members }`, a component, as procedures were written before
they were procedures, parsed only so that the elaborator reports it
(`F0158`). -/
scoped syntax (name := compCmd) ("pub ")? "comp " frenIdent " { " fren_member* " }" : command

/-- `x: T`, or `x?` for a `Bool`: a parameter of a procedure. A modifier,
`pub` or `det`, and a definition, `:= e`, are parsed only so that the
elaborator reports them (`F0110`, `F0114`). -/
syntax fren_proc_param := ("pub " <|> atomic(&"det " lookahead(frenIdent)))? frenIdent (" : " fren_type)? (" := " fren_expr)?

/-- `set_option fren.evidence "tested" in`, before a result, which sets the
evidence of its determinism check (`Reqs/Check#checking-by-testing`). -/
syntax fren_result_evidence := "set_option " ident ppSpace str " in "

/-- `[det] r: T`, a result of a procedure, after any evidence setting. -/
syntax fren_result := (fren_result_evidence)? (&"det ")? frenIdent (" : " fren_type)?

/-- `[pub] proc p(x: T, ...): (r: U, ...) { members }`, a procedure
(`Reqs/Lang/Procedures`): its inputs are its parameters, its public
outputs its named results, and its other members are in its block. -/
scoped syntax (name := procCmd) ("pub ")? "proc " frenIdent noWs "("
  sepBy(fren_proc_param, ", ", ", ", allowTrailingSep) ")"
  (" : " "(" sepBy1(fren_result, ", ", ", ", allowTrailingSep) ")")? " { " fren_member* " }" : command

/-- `type T`, an abstract type, or `type T := U`, a type alias. -/
scoped syntax (name := typeCmd) ("pub ")? "type " frenIdent (" := " fren_type)? : command

/-- A function's parameter: `T` of an uninterpreted function, `x: T` or
`x?` of a defined one. Which it is depends on whether the function has a
body (`lang::function_params`). -/
syntax fren_param := fren_type (" : " fren_type)?

/-- A clause of a function's contract: `assume n: e`, a precondition, or
`ensure n: e`, a postcondition (`Reqs/Lang/Items#contracts`). -/
syntax fren_clause := (&"assume " <|> &"ensure ") frenIdent " : " fren_expr (fren_where)?

/-- `fn f(T, U): R`, an uninterpreted function, or `fn f(x: T): R := e`, a
defined one, either followed by its contract's clauses. With type
parameters, `fn f<A, B>(x: A): B := e` (`Reqs/Lang/GenericFunctions`).
Type parameters in parentheses, `fn f(A, B)(x: A)`, as they were written
before they were written in angle brackets, are parsed so that the
elaborator reports them (`F0156`): a second `(` tells them apart from
the parameters. -/
scoped syntax (name := fnCmd) ("pub ")? "fn " frenIdent
  (noWs fren_type_params <|> atomic(noWs fren_paren_type_params noWs lookahead("(")))?
  noWs "(" sepBy1(fren_param, ", ") ")" (" : " fren_type)?
  (" := " fren_expr (fren_where)?)? fren_clause* : command

/-- `const N: T := e`. -/
scoped syntax (name := constCmd) ("pub ")? "const " frenIdent " : " fren_type " := " fren_expr (fren_where)? : command


/-- `expect n: e`, a global expectation in its short form, or `expect n:
forall (a b: c), e`, as global expectations were written before, which
the elaborator reports (`F0416`). -/
scoped syntax (name := globalCmd) "expect " frenIdent " : " ("forall " fren_binder+ ", ")? fren_expr (fren_where)? : command

/-- `expect n(x: T, ...) { members }`, a global expectation
(`Reqs/Lang/Global`): parameters and a block, as a procedure's. Results
are parsed only so that the elaborator reports them (`F0417`). -/
scoped syntax (name := globalBlockCmd) "expect " frenIdent noWs "("
  sepBy(fren_proc_param, ", ", ", ", allowTrailingSep) ")"
  (" : " "(" sepBy1(fren_result, ", ", ", ", allowTrailingSep) ")")? " { " fren_member* " }" : command

/-- `refine r: c refines a [{ bindings }] [by tactics]`, a refinement
(`Reqs/Lang/Refinement`). -/
scoped syntax (name := refineCmd) "refine " frenIdent " : " fren_path ppSpace &"refines " fren_path
  (" { " sepBy(fren_binding, ", ", ", ", allowTrailingSep) " }")? (" by " Lean.Parser.Tactic.tacticSeq)? : command


end Fren.Lang
