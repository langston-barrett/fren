# Syntax

This chapter gives the grammar of Fren: which sequences of tokens form a
program, and the abstract syntax tree of each. The tokens are those of
[Lexical structure](LexicalStructure.md). Syntax alone gives a program no
meaning: names are resolved, types checked and checks verified by later
rules. `y + 1` is a syntactically valid body even where no `y` is in
scope, and `l + 1` is valid even where `l` is not an integer.

The abstract syntax keeps a program's names as written paths. The
[Core](Types.md) is the resolved form, with items by identity and locals
by index; name resolution and the derived forms relate the two. The
lossless tree, which also keeps parentheses, trivia and every token, is
the subject of [AST and parsing](../Compiler/AstAndParsing.md).

Rule statuses are those of [Lexical structure](LexicalStructure.md). A
`tested` grammar rule is checked against the actual parser by the
chapter's wrapper, which reads the grammar blocks of this chapter as they
are written.

## Notation

The grammar is a parsing expression grammar over tokens.

**Syntax**

r[syntax.notation]
status: definition
A grammar rule `A ::= B` defines the nonterminal `A`, written in
`CamelCase`. A quoted string, such as `"fn"`, is a token with that
spelling: a keyword, a punctuator or the contextual word `assume`.
`Identifier` and `Numeral` are tokens of those lexical classes, and a
`QuestionIdentifier` is an identifier that ends in `?`. `A B` is `A` then
`B`, and parentheses group. The rules are read as a parsing expression
grammar: `A | B` matches what `A` matches if `A` matches, and otherwise
what `B` matches; `A?`, `A*` and `A+` match `A` as many times as it
matches, at most once, any number of times or at least once, and never
give a match back; and `!A` matches no token, where `A` does not match.
Trivia may come between any two tokens, except where a rule says
otherwise.

r[syntax.notation.trivia-sensitive]
status: tested Spec.Language.Syntax.grammar_agrees
One terminal depends on the trivia before it. `TouchingOpen` is a `(`
with no trivia between it and the token before it: no space, tab, line
ending or comment. Line endings are trivia like any other: an expression
may continue on the next line, as in `let r := a` and then `% b`.

## Programs

A program is a file of declarations.

**Syntax**

r[syntax.file.syntax]
status: tested Spec.Language.Syntax.grammar_agrees
A source text is read as a `File`, or, where a single expression is
expected, as an `ExpressionEntry`. Either is accepted only when it matches
all of the text's tokens. A text of trivia alone is an empty `File`, and
no `ExpressionEntry`.

```grammar
File            ::= Declaration*
ExpressionEntry ::= Expression
Declaration     ::= ModuleDeclaration | EnumDeclaration | FunctionDeclaration
                  | ExpectationDeclaration
```

## Names and types

Paths name items, and types are written as paths.

**Syntax**

r[syntax.path.syntax]
status: tested Spec.Language.Syntax.grammar_agrees
A path is one or more identifiers separated by `::`; a qualified path has
at least two. A type is written as a path. Its tree is the built-in
Boolean type for the path `Bool`, the built-in integer type for `Int`,
and otherwise the type that the path names, as for `Int::T` and `A::Int`,
which name resolution finds.

```grammar
Path          ::= Identifier ("::" Identifier)*
QualifiedPath ::= Identifier ("::" Identifier)+
Type          ::= Path
```

## Declarations

A file's declarations introduce modules, enumerations, functions and
global expectations.

**Syntax**

r[syntax.declaration.syntax]
status: tested Spec.Language.Syntax.grammar_agrees
A module declaration names a module by its path. An enumeration declares
its variants in order, each a single identifier with no payload. A
function declaration has a name, one or more parameters, a result type
and a body. A global expectation has a name, parameters and members, and
is never `pub`. A member is an assumption or an expectation, with a label
and an expression; members are not separated, and each ends where its
expression does. A parameter writes its type, unless its name ends in
`?`, when it may omit the type, which is then `Bool`: `b?`, `b?: Bool`
and `b?: Int` are all parameters, and typing reports the last.

```grammar
ModuleDeclaration      ::= "pub"? "mod" Path
EnumDeclaration        ::= "pub"? "enum" Identifier "{" Identifier ("," Identifier)* ","? "}"
FunctionDeclaration    ::= "pub"? "fn" Identifier TouchingOpen Parameter ("," Parameter)* ","? ")"
                           ":" Type ":=" Expression
ExpectationDeclaration ::= "expect" Identifier TouchingOpen (Parameter ("," Parameter)* ","?)? ")"
                           "{" Member* "}"
Parameter              ::= Identifier ":" Type | QuestionIdentifier
Member                 ::= ("assume" | "expect") Identifier ":" Expression
```

r[syntax.declaration.lists]
status: tested Spec.Language.Syntax.grammar_agrees
Every comma-separated list has one policy: its items are separated by
commas, and a comma may follow the last item, as in `f(1, 2,)`. A list may
be empty where that is meaningful: an expectation may have no parameters
and a match no arms. A function has at least one parameter, a call at
least one argument and an enumeration at least one variant. No list has a
comma without an item before it.

> **Rationale:** A trailing comma lets a list be written one item per line
> and grow without editing the line before, as in Rust. A function without
> parameters would be a constant, and a call without arguments its use,
> which the language does not have; an enumeration without variants would
> have no values.

## Expressions

An expression is built from literals, names, calls, operators, `if`,
`let` and `match`.

**Syntax**

r[syntax.expression.syntax]
status: tested Spec.Language.Syntax.grammar_agrees
The expression grammar gives each operator its precedence and grouping by
a nonterminal of its own, from the loosest, `Expression`, to the
tightest, `Primary`. Binary operators group to the left, but the
comparisons and `iff`, which do not associate: `a < b <= c` and
`a iff b iff c` are syntax errors, not nested operations, and parentheses
write the nesting. A `let` is admitted only where an `Expression` is, and
it is never the bare operand of an operator, a `let`'s definition or an
arm's body. A match's scrutinee is a `Primary`.

```grammar
Expression  ::= "let" Identifier ":=" Iff "in" Expression | Iff
Iff         ::= Or ("iff" Or)? !"iff"
Or          ::= And ("or" And)*
And         ::= Not ("and" Not)*
Not         ::= "not" Not | Comparison
Comparison  ::= Sum (CompareOp Sum)? !CompareOp
CompareOp   ::= "=" | "!=" | "<" | "<=" | ">" | ">="
Sum         ::= Product (("+" | "-") Product)*
Product     ::= Negation (("*" | "div" | "%") Negation)*
Negation    ::= "-" Negation | Primary
Primary     ::= "true" | "false" | Numeral | Call | Path | "(" Expression ")" | If | Match
Call        ::= Path TouchingOpen Expression ("," Expression)* ","? ")"
If          ::= "if" Expression "then" Expression "else" Expression
Match       ::= "match" Primary "{" (Arm ("," Arm)* ","?)? "}"
Arm         ::= QualifiedPath "=>" Iff
```

r[syntax.expression.extent]
status: tested Spec.Language.Syntax.grammar_agrees
The `else` branch of an `if` and the body of a `let` extend as far to the
right as they can: the grammar's repetitions never give a match back, and
`a + if b then c else d + e` is `a + (if b then c else (d + e))`.
Only a call's `(` that touches a path makes a call: in `f (x)` the path
`f` is complete, and `(x)` follows it, which no rule accepts.

r[syntax.expression.terminals] spec::surface::{CONTEXTUAL, GRAMMAR_KEYWORDS}
status: tested Spec.Language.Syntax.terminals_agree
The quoted terminals of the grammar are every punctuator, the keywords
`GRAMMAR_KEYWORDS`, and the contextual word `assume`, which the grammar
reads only at the start of a member and which is otherwise an identifier.
`Bool` and `Int` are identifiers, which only the tree of a type
interprets.

```fren
pub mod spec::surface

pub const GRAMMAR_KEYWORDS: Set<String> := {
    "mod",
    "pub",
    "enum",
    "fn",
    "expect",
    "iff",
    "and",
    "or",
    "not",
    "div",
    "in",
    "if",
    "then",
    "else",
    "match",
    "let",
    "true",
    "false",
}

pub const CONTEXTUAL: Set<String> := {"assume"}
```

> **Rationale:** The remainder is written `%`, and `mod` is only the
> keyword of a module declaration, so that no operator's meaning depends
> on where a line ends.

**Examples**

```fren2
fn half(x: Int): Int := x % 2  -- a remainder
fn spread(a: Int, b: Int): Int := let r := a
    % b in r
mod second
```

```fren2 rejected
fn chained(a: Int, b: Int, c: Int): Bool := a < b <= c  --~ error: expected parentheses around a comparison or `iff` that would chain
```

```fren2 rejected
fn both(a?, b?, c?): Bool := a? iff b? iff c?  --~ error: expected parentheses around a comparison or `iff` that would chain
```

```fren2 rejected
fn negation(a?, b?): Bool := a? = not b?  --~ error: expected parentheses around `not` in a tighter operand
```

```fren2 rejected
fn nested(x: Int): Int := let y := let z := x in z in y  --~ error: expected parentheses around `let` in an operator operand
```

```fren2 rejected
fn scrutinee(x: Int): Int := match x + 1 { E::A => 1 }  --~ error: expected `{`
```

```fren2 rejected
fn spaced(x: Int): Int := f (x)  --~ error: expected `(` adjacent to its called name
```

```fren2 rejected
fn unfinished(c?, x: Int): Int := if c? then x  --~ error: expected `else`
```

These lines group as their comments show, with the parentheses written
out.

```fren2 groups
base + 5 * 2 -- base + (5 * 2)
base - 5 - 2 -- (base - 5) - 2
-x * 2 -- (-x) * 2
not x = y and true -- (not (x = y)) and true
a or b and c iff d -- (a or (b and c)) iff d
- - x -- -(-x)
a + if b then c else d + e -- a + (if b then c else (d + e))
x % 2 * 3 -- (x % 2) * 3
f(x) + g(y, z) * 2 -- f(x) + (g(y, z) * 2)
```

## Abstract syntax

Each accepted text has one abstract syntax tree, which keeps what the
text means and drops how it is written.

**Syntax**

r[syntax.tree.types] spec::surface::{UnaryOp, BinaryOp, ExprF, Arm, TypeName, Parameter, Member, DeclarationF}
status: definition
An expression tree is a fixed point of `ExprF`: `ExprF<E>` is one node,
whose subexpressions are of type `E`. A file's tree is the sequence of
its declarations' trees, each a `DeclarationF` whose expressions are
expression trees. The trees keep names as written paths, and have no
parentheses. An expression tree is *well formed* when its paths are
nonempty, an arm's path has at least two identifiers, every call has at
least one argument, and every path segment, binder and name is an
identifier, not a keyword. The tree of every accepted expression is well
formed.

```fren
pub enum UnaryOp { Neg, Not }

pub enum BinaryOp { Add, Sub, Mul, Div, Mod, Eq, Ne, Lt, Le, Gt, Ge, And, Or, Iff }

-- A path, as its identifiers in order.
pub type Path := Seq<String>

-- A match arm: a variant's path and a body.
pub struct Arm<E> { variant: Path, body: E }

-- One expression node, with subexpressions of type `E`.
pub enum ExprF<E> {
    Boolean(Bool),
    Integer(Nat),
    Name(Path),
    Call(Path, Seq<E>),
    Unary(UnaryOp, E),
    Binary(BinaryOp, E, E),
    If(E, E, E),
    Let(String, E, E),
    Match(E, Seq<Arm<E>>),
}

pub enum TypeName { Boolean, Integer, Named(Path) }

pub struct Parameter { name: String, annotation: Option<TypeName> }

pub enum MemberKind { Assume, Expect }

pub struct Member<E> { kind: MemberKind, label: String, body: E }

-- One declaration; `public?` is whether it is written with `pub`.
pub enum DeclarationF<E> {
    Module(Bool, Path),
    Enumeration(Bool, String, Seq<String>),
    Function(Bool, String, Seq<Parameter>, TypeName, E),
    Expectation(String, Seq<Parameter>, Seq<Member<E>>),
}
```

r[syntax.tree.productions]
status: tested Spec.Language.Syntax.trees_agree
Each production gives its tree. `true` and `false` are `Boolean` nodes,
and a numeral an `Integer` node with its value. A `Path` is a `Name` node
of its identifiers, and a call a `Call` node of the path and the
arguments' trees, in order. `( e )` is the tree of `e`. A prefix operator
and its operand are a `Unary` node; a binary operator and its operands
are a `Binary` node, and a repetition such as `a - b - c` gives the nodes
`(a - b) - c`, from the left. `if`, `let` and `match` give `If`, `Let`
and `Match` nodes of their parts, a `let`'s binder as written. A type's
tree is as `syntax.path.syntax` says, a parameter's is its name and its
type if written, and each declaration's is the `DeclarationF` node of its
parts.

r[syntax.tree.operators] spec::surface::{unary_spelling, binary_spelling}
status: tested Spec.Language.Syntax.operators_agree
The operators are spelled as `unary_spelling` and `binary_spelling` say.
`-` is both `Neg` and `Sub`, and its position decides which.

```fren
pub fn unary_spelling(op: UnaryOp): String := match op {
    UnaryOp::Neg => "-",
    UnaryOp::Not => "not",
}

pub fn binary_spelling(op: BinaryOp): String := match op {
    BinaryOp::Add => "+",
    BinaryOp::Sub => "-",
    BinaryOp::Mul => "*",
    BinaryOp::Div => "div",
    BinaryOp::Mod => "%",
    BinaryOp::Eq => "=",
    BinaryOp::Ne => "!=",
    BinaryOp::Lt => "<",
    BinaryOp::Le => "<=",
    BinaryOp::Gt => ">",
    BinaryOp::Ge => ">=",
    BinaryOp::And => "and",
    BinaryOp::Or => "or",
    BinaryOp::Iff => "iff",
}
```

**Properties**

r[syntax.tree.spellings] spec::surface::spellings::{binary, unary}
status: smt
Two binary operators have different spellings, as do two unary
operators: a token and its position, binary or prefix, determine the
operator.

```fren
expect spellings(a: BinaryOp, b: BinaryOp, u: UnaryOp, v: UnaryOp) {
    expect binary: when a != b, binary_spelling(a) != binary_spelling(b)
    expect unary: when u != v, unary_spelling(u) != unary_spelling(v)
}
```

## Printing

A tree is printed with parentheses where its grouping needs them.

**Syntax**

r[syntax.print.roundtrip] spec::surface::{category, operand_category, fits?}
status: tested Spec.Language.Syntax.roundtrip_agrees
Printing an expression tree writes each node's tokens, and puts a subtree in
parentheses exactly where `fits?` says it does not fit its place. A
tree's `category` is the nonterminal that derives it without parentheses;
it fits a place whose nonterminal is no tighter than its category, unless
it is *open*, an `if` or `let`, or an operator node whose last subtree is
open, and something of the enclosing expression follows it. Parsing the
printed text of a well-formed expression tree gives the tree back. That
of an expression tree that is not well formed does not: the tree of an
accepted expression is well formed. Declarations are not printed by this
rule.

```fren
pub enum Category { Expression, Iff, Or, And, Not, Comparison, Sum, Product, Negation, Primary }

-- How tightly a category binds: each derives those of greater rank.
pub fn rank(c: Category): Int := match c {
    Category::Expression => 0,
    Category::Iff => 1,
    Category::Or => 2,
    Category::And => 3,
    Category::Not => 4,
    Category::Comparison => 5,
    Category::Sum => 6,
    Category::Product => 7,
    Category::Negation => 8,
    Category::Primary => 9,
}

-- The category of a unary or binary node with this operator.
pub fn category(unary?, u: UnaryOp, b: BinaryOp): Category :=
    if unary? then
    (if u = UnaryOp::Not then Category::Not else Category::Negation)
    else
    match b {
        BinaryOp::Iff => Category::Iff,
        BinaryOp::Or => Category::Or,
        BinaryOp::And => Category::And,
        BinaryOp::Add => Category::Sum,
        BinaryOp::Sub => Category::Sum,
        BinaryOp::Mul => Category::Product,
        BinaryOp::Div => Category::Product,
        BinaryOp::Mod => Category::Product,
        _ => Category::Comparison,
    }

-- The category of a binary node's left (`left?`) or right operand, or of a
-- unary node's operand: the same category for a left operand of a
-- left-associative operator and for a unary operand, else the next tighter.
pub fn operand_category(unary?, u: UnaryOp, b: BinaryOp, left?): Category :=
    if unary? then
    category(true, u, b)
    else if left? and not b is BinaryOp::Iff | BinaryOp::Eq | BinaryOp::Ne | BinaryOp::Lt | BinaryOp::Le
    | BinaryOp::Gt | BinaryOp::Ge then
    category(false, u, b)
    else
    match category(false, u, b) {
        Category::Iff => Category::Or,
        Category::Or => Category::And,
        Category::And => Category::Not,
        Category::Comparison => Category::Sum,
        Category::Sum => Category::Product,
        _ => Category::Negation,
    }

-- Whether a subtree of category `child`, open or not, may stand without
-- parentheses at a place of category `place`, followed or not by more of
-- the enclosing expression.
pub fn fits?(child: Category, open?, place: Category, followed?) :=
    rank(child) >= rank(place) and not (open? and followed?)
```

**Properties**

r[syntax.print.properties] spec::surface::printing::{categories, left_associative, non_associative, unary}
status: smt
Every operator's operands are of a tighter category, but the left operand
of a left-associative operator, which is of its own category, and a unary
operand, which is of the unary node's own category. For example,
`a - b - c` needs no parentheses, `a < (b < c)` and `(a < b) < c` both
do, and `not not a` and `- - a` need none.

```fren
expect printing(u: UnaryOp, b: BinaryOp) {
    expect categories: rank(operand_category(false, u, b, false)) > rank(category(false, u, b))
    expect left_associative: when b is BinaryOp::Add | BinaryOp::Mul | BinaryOp::And | BinaryOp::Or,
        operand_category(false, u, b, true) = category(false, u, b)
    expect non_associative: when b is BinaryOp::Eq | BinaryOp::Lt | BinaryOp::Iff,
        rank(operand_category(false, u, b, true)) > rank(category(false, u, b))
    expect unary: operand_category(true, u, b, false) = category(true, u, b)
}
```

## Precedence summary

> **Note:** This table summarizes the expression grammar and is not
> normative; `syntax.expression.syntax` decides.
>
> | Nonterminal | Operators | Grouping |
> |---|---|---|
> | `Negation` | prefix `-` | |
> | `Product` | `*` `div` `%` | left |
> | `Sum` | `+` `-` | left |
> | `Comparison` | `=` `!=` `<` `<=` `>` `>=` | none |
> | `Not` | prefix `not` | |
> | `And` | `and` | left |
> | `Or` | `or` | left |
> | `Iff` | `iff` | none |

## Examples

These declarations use the forms of the grammar: the wrapper checks that
every alternative of every grammar rule but `ExpressionEntry` matches
somewhere in the chapter's `fren2` blocks.

```fren2
pub mod signals

pub enum Light { Red, Amber, Green, }

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

expect waits(l: Light, base: Int,) {
    assume bounded: base <= 100
    expect at_most: wait(l, base) <= 130
}

pub fn choose(b?, base: Int): Int := let delay := base + 5 in if b? then delay else base

expect division(x: Int) { expect euclidean: x = (x div 2) * 2 + x % 2 }

expect operators() {
    expect all: not (true iff false) or -1 < 2 and 3 != 4 and 5 > 4 and 6 >= 6 and 7 - 1 = 6
}

fn none(l: Light): Int := match l {}

fn typed(b?: Bool, n: Int::T): Bool := b?
```

These are syntax, though later rules reject them: `y` is not in scope,
`Light` has no `+`, and the claim is false.

```fren2
pub enum Light { Red, Green }

pub fn unbound(x: Int): Int := y + 1

pub fn sum(l: Light): Int := l + 1

expect never_red(l: Light) { expect claim: l != Light::Red }
```
