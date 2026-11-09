# Syntax

This chapter gives the concrete grammar of Fren: which sequences of tokens
form a program, and the tree that each one has. The tokens are those of
[Lexical structure](LexicalStructure.md). Syntax alone gives a program no
meaning: names are resolved, types checked and checks verified by later
rules, so `y + 1` is a syntactically valid body even where no `y` is in
scope, and `l + 1` is valid even where `l` is not an integer.

Each rule's `status:` line says how it is established, as in
[Lexical structure](LexicalStructure.md). A `tested` grammar rule is
compared with the actual parser by the chapter's wrapper, on the examples
that the rule names and on each example block of this chapter. A block
that the parser accepts as a file is marked `fren2`; one that it rejects is
marked `fren2 rejected`.

## Notation

**Syntax**

r[syntax.notation]
status: definition
A grammar rule `A ::= B` defines the nonterminal `A`, written in
`CamelCase`. A quoted string, such as `"fn"`, is a token with that
spelling: a keyword, a punctuator or a contextual word. `Identifier` and
`Numeral` are tokens of those lexical classes. `A | B` is either, `A B` is
`A` then `B`, `A?` is `A` or nothing, `A*` is zero or more and `A+` one or
more of `A`, and parentheses group. A `--` comment in a grammar is not
part of it. Trivia may come between any two tokens, except where a rule
says otherwise.

r[syntax.notation.trivia-sensitive]
status: tested Spec.Language.Syntax.productions_agree
Two terminals depend on the trivia before them. `TouchingOpen` is a `(`
with no trivia between it and the token before it: no space, tab, line
ending or comment. `SameLineMod` is the keyword `mod` with no line ending
in the trivia between it and the token before it.

## Programs

**Syntax**

r[syntax.file.syntax]
status: tested Spec.Language.Syntax.productions_agree
A file is a sequence of declarations, which may be empty.

```text
File            ::= Declaration*
Declaration     ::= ModuleDeclaration | EnumDeclaration | FunctionDeclaration
                  | ExpectationDeclaration
ExpressionEntry ::= Expression
```

r[syntax.file.entry]
status: tested Spec.Language.Syntax.productions_agree
A source text is read as a `File` or, where a single expression is
expected, such as in a library's tests, as an `ExpressionEntry`. Either
must cover the whole text, apart from trivia at its ends: text that
remains after the longest `File` or `Expression` is a syntax error, not the
start of something else. A text of trivia alone is an empty `File`, and no
`ExpressionEntry`.

## Names and paths

**Syntax**

r[syntax.path.syntax]
status: tested Spec.Language.Syntax.productions_agree
A path is one or more identifiers separated by `::`. A qualified path
has at least two.

```text
Path          ::= Identifier ("::" Identifier)*
QualifiedPath ::= Identifier ("::" Identifier)+
```

r[syntax.path.contextual]
status: tested Spec.Language.Syntax.productions_agree
The contextual words of `spec::lexical::CONTEXTUAL` are identifiers
everywhere the grammar reads an `Identifier`: a declared name, a
parameter, a member's label, a `let` binder, a variant, and any segment
of a path. The grammar gives them a meaning only at these positions:
`true` and `false` are literals, and `not` an operator, where they start
an expression; `assume` starts a member of an expectation; and `Bool` and
`Int`, as a whole type, are the built-in types. So no expression is a
name that starts with `true`, `false` or `not`: in `true::x` the `true`
is a literal, and `::x` does not continue it. `E::true` is a name.

## Types

**Syntax**

r[syntax.type.syntax]
status: tested Spec.Language.Syntax.productions_agree
A type is written as a path. A path that is the single identifier `Bool`
or `Int` denotes the built-in Boolean or integer type. Any other path,
including `Int::T` and `A::Int`, names a declared type, which name
resolution finds.

```text
Type ::= Path
```

## Declarations

### Modules

**Syntax**

r[syntax.module.syntax]
status: tested Spec.Language.Syntax.productions_agree
A module declaration is `mod` and the module's path, optionally `pub`.

```text
ModuleDeclaration ::= "pub"? "mod" Path
```

### Enumerations

**Syntax**

r[syntax.enumeration.syntax]
status: tested Spec.Language.Syntax.productions_agree
An enumeration declares its variants, in order, between braces: at least
one, separated by commas, with an optional trailing comma. A variant is a
single identifier and has no payload.

```text
EnumDeclaration ::= "pub"? "enum" Identifier "{" Identifier ("," Identifier)* ","? "}"
```

### Functions

**Syntax**

r[syntax.function.syntax]
status: tested Spec.Language.Syntax.productions_agree
A function declaration has a name, one or more parameters, a result type
and a body. Its parameter list starts with a `TouchingOpen`, has no
trailing comma, and is never empty.

```text
FunctionDeclaration ::= "pub"? "fn" Identifier TouchingOpen Parameter ("," Parameter)* ")"
                        ":" Type ":=" Expression
Parameter           ::= Identifier ":" Type | QuestionIdentifier
```

r[syntax.function.parameter]
status: tested Spec.Language.Syntax.productions_agree
A `QuestionIdentifier` is an identifier that ends in `?`. Such a parameter
may omit its type, which is then `Bool`, or write one: `b?` and `b?: Bool`
are both parameters, and so is `b?: Int`, whose inconsistency typing
reports. Any other parameter writes its type.

### Expectations

**Syntax**

r[syntax.expectation.syntax]
status: tested Spec.Language.Syntax.productions_agree
A global expectation has a name, a parameter list that starts with a
`TouchingOpen`, and a block of members. Its parameter list may be empty
and may have a trailing comma. Its block may have no members. A member is
an assumption or an expectation, with a label and a Boolean expression.
Members are not separated: each ends where its expression does. A global
expectation is never `pub`.

```text
ExpectationDeclaration ::= "expect" Identifier TouchingOpen (Parameter ("," Parameter)* ","?)? ")"
                           "{" Member* "}"
Member                 ::= ("assume" | "expect") Identifier ":" Expression
```

### Separated lists

**Syntax**

r[syntax.list.policy] spec::grammar::accepts?
status: tested Spec.Language.Syntax.lists_agree
The comma-separated lists of the grammar differ in whether they may be
empty and whether they may end in a comma. `accepts?` states, for each,
which numbers of items, with or without a trailing comma, it accepts. No
list has a comma without an item before it.

```fren
pub mod spec::grammar

use spec::lexical

pub enum Separated { FunctionParameters, ExpectationParameters, Arguments, Variants, Arms }

pub fn may_be_empty?(list: Separated) := list is Separated::ExpectationParameters | Separated::Arms

pub fn trailing_comma?(list: Separated) :=
    list is Separated::ExpectationParameters | Separated::Variants | Separated::Arms

-- Whether `list` may have `items` items, then a comma if `trailing?`.
pub fn accepts?(list: Separated, items: Int, trailing?) :=
    items >= 0 and (items > 0 or may_be_empty?(list) and not trailing?) and (trailing_comma?(list) or not trailing?)
```

## Expressions

**Syntax**

r[syntax.expression.syntax]
status: tested Spec.Language.Syntax.productions_agree
An expression is read at a *level*, a number from 0 to 9, written
`Expression[m]`; `Expression` is `Expression[0]`. A level bounds which
operators may start and continue it: an expression at level `m` is a
leading part, then any number of binary continuations whose operators
have precedence at least `m`, each with a right operand at a level one
more than its operator's precedence.

```text
Expression     ::= Expression[0]
Expression[m]  ::= Leading[m] Continuation[m]*
Leading[m]     ::= "-" Expression[8]                                  -- only if m <= 8
                 | "not" Expression[4]                                -- only if m <= 4
                 | "let" Identifier ":=" Expression[1] "in" Expression  -- only if m = 0
                 | Primary
Continuation[m] ::= BinaryOperator Expression[p + 1]
                   -- where p is the operator's precedence, and only if p >= m
BinaryOperator ::= "iff" | "or" | "and" | "=" | "!=" | "<" | "<=" | ">" | ">="
                 | "+" | "-" | "*" | "div" | SameLineMod
Primary        ::= "true" | "false" | Numeral | Name | Call | "(" Expression ")"
                 | "if" Expression "then" Expression "else" Expression
                 | "match" Expression[9] "{" (Arm ("," Arm)* ","?)? "}"
Name           ::= Path    -- whose first identifier is not "true", "false" or "not"
Call           ::= Name TouchingOpen Expression ("," Expression)* ")"
Arm            ::= QualifiedPath "=>" Expression[1]
```

r[syntax.expression.extent]
status: tested Spec.Language.Syntax.groupings_agree
Every `Expression[m]` extends as far to the right as the grammar allows:
a continuation, or a touching `(` after a name, that can belong to an
inner expression belongs to it, not to one that encloses it. This makes
each accepted token sequence have exactly one tree. In particular the
operand of a prefix operator, the right operand of a binary operator, the
body of a `let` and the `else` branch of an `if` take every continuation
they admit: `a + if b then c else d + e` is `a + (if b then c else (d + e))`.

### Operators

**Syntax**

r[syntax.operator.table] spec::grammar::{spelling, prefix?, precedence, non_associative?}
status: tested Spec.Language.Syntax.operators_agree
Each operator has a spelling, is prefix or binary, and has a precedence.
A larger precedence binds more tightly. `-` is both the prefix operator
`Negate` and the binary `Subtract`, and the position decides which.

| Precedence | Operators | Position | Associativity |
|---|---|---|---|
| 8 | `-` | prefix | |
| 7 | `*` `div` `mod` | binary | left |
| 6 | `+` `-` | binary | left |
| 5 | `=` `!=` `<` `<=` `>` `>=` | binary | none |
| 4 | `not` | prefix | |
| 3 | `and` | binary | left |
| 2 | `or` | binary | left |
| 1 | `iff` | binary | none |

r[syntax.operator.grouping] spec::grammar::{operand_level, admitted?, grouping}
status: tested Spec.Language.Syntax.groupings_agree
The operand to the right of an operator is read at `operand_level`: a
binary operator's at one more than its precedence, a prefix operator's at
its precedence. An operator is `admitted?` at a level at most its
precedence. So in `x a y b z` the binary `b` continues `a`'s right operand
exactly when it is admitted there, and otherwise follows `x a y`, as
`grouping` states. A prefix operator after another operator is accepted
exactly when it is admitted at the level of that operator's operand.

r[syntax.operator.non-associative] spec::grammar::grouping
status: tested Spec.Language.Syntax.groupings_agree
The comparisons and `iff` are non-associative. A binary continuation whose
operator is a comparison may not follow one whose operator is a
comparison, and likewise for `iff`. Such a sequence, such as `a < b <= c`
or `a iff b iff c`, is a syntax error, not a nested comparison; write
`(a < b) <= c`, or `(a iff b) iff c`, to mean the nesting.

```fren
pub enum Operator {
    Iff, Or, And, Not, Equal, NotEqual, Less, LessEqual, Greater, GreaterEqual,
    Add, Subtract, Multiply, Divide, Remainder, Negate,
}

pub fn spelling(op: Operator): String := match op {
    Operator::Iff => "iff",
    Operator::Or => "or",
    Operator::And => "and",
    Operator::Not => "not",
    Operator::Equal => "=",
    Operator::NotEqual => "!=",
    Operator::Less => "<",
    Operator::LessEqual => "<=",
    Operator::Greater => ">",
    Operator::GreaterEqual => ">=",
    Operator::Add => "+",
    Operator::Subtract => "-",
    Operator::Multiply => "*",
    Operator::Divide => "div",
    Operator::Remainder => "mod",
    Operator::Negate => "-",
}

pub fn prefix?(op: Operator) := op is Operator::Not | Operator::Negate

pub fn comparison?(op: Operator) :=
    op is Operator::Equal | Operator::NotEqual | Operator::Less | Operator::LessEqual | Operator::Greater | Operator::GreaterEqual

pub fn non_associative?(op: Operator) := op = Operator::Iff or comparison?(op)

pub fn precedence(op: Operator): Int := match op {
    Operator::Iff => 1,
    Operator::Or => 2,
    Operator::And => 3,
    Operator::Not => 4,
    Operator::Equal => 5,
    Operator::NotEqual => 5,
    Operator::Less => 5,
    Operator::LessEqual => 5,
    Operator::Greater => 5,
    Operator::GreaterEqual => 5,
    Operator::Add => 6,
    Operator::Subtract => 6,
    Operator::Multiply => 7,
    Operator::Divide => 7,
    Operator::Remainder => 7,
    Operator::Negate => 8,
}

-- The level of the operand to the right of `op`.
pub fn operand_level(op: Operator): Int :=
    if prefix?(op) then precedence(op) else precedence(op) + 1

-- Whether `op` may start (if prefix) or continue (if binary) an expression at `level`.
pub fn admitted?(op: Operator, level: Int) := level <= precedence(op)

pub enum Grouping { Left, Right, Rejected }

-- How `first y second z` groups, or `x first y second z` if `first` is
-- binary, for a binary `second`: `Right` if `second` continues the operand
-- of `first`, `Left` if it follows it, and `Rejected` if neither.
pub fn grouping(first: Operator, second: Operator): Grouping :=
    if admitted?(second, operand_level(first)) then Grouping::Right
    else if non_associative?(first) and non_associative?(second) and precedence(first) = precedence(second) then Grouping::Rejected
    else Grouping::Left
```

**Legality rules**

r[syntax.operator.properties] spec::grammar::operator_properties::{spellings, tokens, same_level, left, non_associative, negate_operand, not_operand, not_level}
status: smt
The table has these properties, which the checker proves. Two operators
of the same position have different spellings, so a token and its
position determine the operator. Every spelling is a punctuator, a keyword
of the grammar or a contextual word. Binary operators of the same
precedence are all left-associative or all non-associative. A
left-associative operator groups to the left with itself, and a
non-associative one rejects itself. Unary minus may follow any binary
operator, while `not` may follow only `and`, `or` and `iff`: `a + not b`
and `a = not b` need parentheses. `not` binds more loosely than every
comparison and more tightly than `and`, so `not a = b` is `not (a = b)`
and `not a and b` is `(not a) and b`.

```fren
expect operator_properties(a: Operator, b: Operator) {
    expect spellings: when a != b and prefix?(a) = prefix?(b), spelling(a) != spelling(b)
    expect tokens: spelling(a) in lexical::PUNCTUATORS
        or spelling(a) in lexical::GRAMMAR_KEYWORDS or spelling(a) in lexical::CONTEXTUAL
    expect same_level: when not prefix?(a) and not prefix?(b) and precedence(a) = precedence(b),
        non_associative?(a) = non_associative?(b)
    expect left: when not prefix?(a) and not non_associative?(a), grouping(a, a) = Grouping::Left
    expect non_associative: when non_associative?(a), grouping(a, a) = Grouping::Rejected
    expect negate_operand: when not prefix?(a), admitted?(Operator::Negate, operand_level(a))
    expect not_operand: when not prefix?(a), admitted?(Operator::Not, operand_level(a)) iff a is Operator::Iff | Operator::Or | Operator::And
    expect not_level: when comparison?(a) and b = Operator::And, precedence(b) < precedence(Operator::Not) < precedence(a)
}
```

**Examples**

```text
base + 5 * 2          -- base + (5 * 2)
base - 5 - 2          -- (base - 5) - 2
-x * 2                -- (-x) * 2
not x = y and true    -- (not (x = y)) and true
a or b and c iff d    -- (a or (b and c)) iff d
- - x                 -- -(-x)
```

```fren2 rejected
fn chained(a: Int, b: Int, c: Int): Bool := a < b <= c
```

```fren2 rejected
fn both(a?, b?, c?): Bool := a? iff b? iff c?
```

```fren2 rejected
fn negation(a?, b?): Bool := a? = not b?
```

### Places

**Syntax**

r[syntax.expression.places] spec::grammar::{place_level, let_admitted?}
status: tested Spec.Language.Syntax.places_agree
The grammar reads most expressions at level 0: a function body, a
member's expression, a `let` body, an argument, the parts of an `if` and
the inside of parentheses. A `let`'s definition and an arm's body are read
at level 1, so a bare `let` there needs parentheses, while every operator
is admitted. A `match`'s scrutinee is read at level 9, which admits no
operator and no `let`, so it is a `Primary`: a literal, a name, a call, a
parenthesized expression, an `if` or a `match`.

```fren
pub enum Place { Full, Definition, ArmBody, Scrutinee }

pub fn place_level(place: Place): Int := match place {
    Place::Full => 0,
    Place::Definition => 1,
    Place::ArmBody => 1,
    Place::Scrutinee => 9,
}

pub fn let_admitted?(level: Int) := level = 0
```

```fren2 rejected
fn nested(x: Int): Int := let y := let z := x in z in y
```

```fren2 rejected
fn scrutinee(x: Int): Int := match x + 1 { E::A => 1 }
```

### Literals and names

**Syntax**

r[syntax.literal.syntax]
status: tested Spec.Language.Syntax.productions_agree
`true` and `false` are the Boolean literals, and a numeral is an integer
literal, whose value [Lexical structure](LexicalStructure.md#numerals)
gives. There is no negative literal: `-1` applies unary minus to `1`. A
name is a path, possibly qualified, such as `x`, `Light::Red` or
`A::B::c`.

### Calls

**Syntax**

r[syntax.call.syntax]
status: tested Spec.Language.Syntax.productions_agree
A call applies a name to one or more arguments, separated by commas, with
no trailing comma. Its `(` touches the name's last identifier. Only a name
is called: `f(x)(y)`, `(f)(x)` and `1(x)` are syntax errors, and so is
`f (x)`, whose `(` does not touch `f`. A call is syntax whatever the name
resolves to: `unknown(x)` and `x(y)` are calls.

```fren2 rejected
fn spaced(x: Int): Int := f (x)
```

### Conditionals

**Syntax**

r[syntax.if.syntax]
status: tested Spec.Language.Syntax.productions_agree
An `if` has a condition, a `then` branch and an `else` branch, each an
expression at level 0. There is no `if` without `else`. The `else` branch
extends as far as it can (`syntax.expression.extent`).

### Local definitions

**Syntax**

r[syntax.let.syntax]
status: tested Spec.Language.Syntax.productions_agree
`let x := value in body` binds one identifier. The definition is read at
level 1 and the body at level 0, so the body extends as far as it can and
a `let` may follow `in` directly: `let x := 1 in let y := x in y`. A `let`
is admitted only at level 0, so it is never the bare operand of an
operator: `a and (let x := true in x)` needs its parentheses.

### Matches

**Syntax**

r[syntax.match.syntax]
status: tested Spec.Language.Syntax.productions_agree
A `match` has a scrutinee, a `Primary`, and arms between braces. Each arm
is a qualified path, `=>` and a body at level 1. Arms are separated by
commas, may end in a comma, and may be absent: `match l {}` is syntax,
and whether its arms cover every variant is checked later. An arm's path
has at least two identifiers, which resolution reads as an enumeration
and its variant.

### Remainders and modules at a line start

**Syntax**

r[syntax.remainder.line]
status: tested Spec.Language.Syntax.productions_agree
The binary `mod` is a `SameLineMod`: it must be on the line where its
left operand ends. A `mod` after a line ending, even with comments
between, does not continue the expression before it. In a file it starts
the next declaration, a module; in an `ExpressionEntry`, or inside a
delimiter that is not yet closed, it is a syntax error. The right operand
of a `mod` may start on the next line.

```text
fn half(x: Int): Int := x mod 2    -- a remainder
fn whole(x: Int): Int := x
mod second                         -- a module declaration
```

## Examples

**Examples**

These declarations use each form of the grammar.

```fren2
pub mod signals

pub enum Light { Red, Amber, Green }

pub fn next(l: Light): Light := match l {
    Light::Red => Light::Green,
    Light::Green => Light::Amber,
    Light::Amber => Light::Red,
}

pub fn wait(l: Light, base: Int): Int := match l {
    Light::Red => base + 30,
    Light::Amber => base + 5,
    Light::Green => base,
}

expect cycles(l: Light) { expect back: next(next(next(l))) = l }

expect waits(l: Light, base: Int) {
    assume bounded: base <= 100
    expect at_most: wait(l, base) <= 130
}

pub fn choose(b?, base: Int): Int := let delay := base + 5 in if b? then delay else base

expect division(x: Int) { expect euclidean: x = (x div 2) * 2 + x mod 2 }
```

These are syntax, though later rules reject them: `y` is not in scope,
`Light` has no `+`, and the claim is false.

```fren2
pub enum Light { Red, Green }

pub fn unbound(x: Int): Int := y + 1

pub fn sum(l: Light): Int := l + 1

expect never_red(l: Light) { expect claim: l != Light::Red }
```
