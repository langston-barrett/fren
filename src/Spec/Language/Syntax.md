# Syntax

This chapter gives the grammar of Fren, which sequences of tokens form a
program, and the abstract syntax tree of each accepted program. The tokens
are those of [Lexical structure](LexicalStructure.md). Syntax alone gives a
program no meaning: names are resolved, types checked and checks verified
by later rules. `y + 1` is a syntactically valid body even where no `y` is
in scope, and `l + 1` is valid even where `l` is not an integer.

The abstract syntax keeps a program's names as written paths. The
[Core](Types.md) is the resolved form, with items by identity and locals by
index; name resolution and the derived forms relate the two. The lossless
tree, which also keeps parentheses, trivia and every token, is the subject
of [AST and parsing](../Compiler/AstAndParsing.md).

The chapter's wrapper reads the `grammar` blocks below as they are written
and runs them against the actual parser. Example blocks are checked too: a
`fren2` block is a file that the parser accepts, a `fren2 rejected` block
one that it rejects, a `fren2 groups` block lists expressions with the
grouping that parentheses would write, and a `fren2 trees` block lists
texts with their abstract syntax trees.

## Notation

The grammar is a parsing expression grammar over tokens.

r[syntax.notation]
A grammar rule `A ::= B` defines the nonterminal `A`, written in
`CamelCase`. A quoted string, such as `"fn"`, is a token with that spelling:
a keyword, a punctuator or the contextual word `assume`. `Identifier` and
`Numeral` are tokens of those lexical classes, and a `QuestionIdentifier`
is an identifier that ends in `?`. `A B` is `A` then `B`, and parentheses
group. The rules are read as a parsing expression grammar: `A | B` matches
what `A` matches if `A` matches, and otherwise what `B` matches; `A?`, `A*`
and `A+` match `A` at most once, any number of times or at least once, as
many times as it matches, and never give a match back; and `!A` matches no
token, where `A` does not match.
<!-- status: definition -->

r[syntax.notation.trivia-sensitive]
Trivia may come between any two tokens, and line endings are trivia like
any other: an expression may continue on the next line, as `let r := a`
and then `% b` does. One terminal depends on the trivia before it:
`TouchingOpen` is a `(` with no trivia between it and the token before it,
no space, tab, line ending or comment.
<!-- status: tested Spec.Language.Syntax.grammar_agrees -->

## Programs

A program is a file of declarations.

r[syntax.file.syntax]
A source text is read as a `File`, or, where a single expression is
expected, as an `ExpressionEntry`. Either is accepted only when it matches
all of the text's tokens. A text of trivia alone is an empty `File`, and no
`ExpressionEntry`.
<!-- status: tested Spec.Language.Syntax.grammar_agrees -->

```grammar
File            ::= Declaration*
ExpressionEntry ::= Expression
Declaration     ::= ModuleDeclaration | EnumDeclaration | FunctionDeclaration
                  | ExpectationDeclaration
```

## Names and types

Paths name items, and types are written as paths.

r[syntax.path.syntax]
A path is one or more identifiers separated by `::`; a qualified path has at
least two. A type is written as a path. Its tree is the built-in Boolean
type for the path `Bool`, the built-in integer type for `Int`, and otherwise
the type that the path names, as for `Int::T` and `A::Int`, which name
resolution finds.
<!-- status: tested Spec.Language.Syntax.trees_agree -->

```grammar
Path          ::= Identifier ("::" Identifier)*
QualifiedPath ::= Identifier ("::" Identifier)+
Type          ::= Path
```

> **Note:** A declaration may be named `Bool` or `Int`, and a type written
> as that single identifier still denotes the built-in type. Whether such
> a declaration is allowed belongs to [names and scope](NamesAndScope.md),
> and is recorded as design debt D2 in the
> [development coverage](../../../docs/fren2-specification-coverage.md#syntax-decisions-and-design-debt).

## Declarations

A file's declarations introduce modules, enumerations, functions and global
expectations.

r[syntax.declaration.syntax]
A module declaration names a module by its path. An enumeration declares its
variants in order, each a single identifier with no payload. A function
declaration has a name, one or more parameters, a result type and a body. A
global expectation has a name, parameters and members, and is never `pub`. A
member is an assumption or an expectation, with a label and an expression;
members are not separated, and each ends where its expression does. A
parameter writes its type, unless its name ends in `?`, when it may omit the
type, which is then `Bool`: `b?`, `b?: Bool` and `b?: Int` are all
parameters, and typing reports the last.
<!-- status: tested Spec.Language.Syntax.grammar_agrees -->

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
Every comma-separated list has one policy: its items are separated by
commas, and a comma may follow the last item, as in `f(1, 2,)`. A list may
be empty where that is meaningful: an expectation may have no parameters and
a match no arms. A function has at least one parameter, a call at least one
argument and an enumeration at least one variant. No list has a comma
without an item before it.
<!-- status: tested Spec.Language.Syntax.grammar_agrees -->

> **Rationale:** A trailing comma lets a list be written one item per line
> and grow without editing the line before, as in Rust. A function without
> parameters would be a constant, and a call without arguments its use,
> which the language does not have; an enumeration without variants would
> have no values. This is decision S1 in the
> [development coverage](../../../docs/fren2-specification-coverage.md#syntax-decisions-and-design-debt).

## Expressions

An expression is built from literals, names, calls, operators, `if`, `let`
and `match`.

r[syntax.expression.syntax]
The expression grammar gives each operator its precedence and grouping by a
nonterminal of its own, from the loosest, `Expression`, to the tightest,
`Primary`. Binary operators group to the left, but the comparisons and
`iff`, which do not associate: a comparison or `iff` is never followed by
another of its kind: `a < b <= c` and `a iff b iff c` are syntax errors,
not nested operations, and parentheses write the nesting. A `let` is
admitted only where an `Expression` is, and is never the bare operand of an
operator, a `let`'s definition or an arm's body. A match's scrutinee is a
`Primary`.
<!-- status: tested Spec.Language.Syntax.grammar_agrees -->

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
The `else` branch of an `if` and the body of a `let` extend as far to the
right as they can, because the grammar's repetitions never give a match
back: `a + if b then c else d + e` groups as `a + (if b then c else (d + e))`.
Only a `(` that touches a path makes a call: in `f (x)` the path `f` is
complete, and no rule accepts the `(x)` after it.
<!-- status: tested Spec.Language.Syntax.groups_agree -->

r[syntax.expression.terminals] spec::surface::{CONTEXTUAL, GRAMMAR_KEYWORDS}
The quoted terminals of the grammar are every punctuator, the keywords
`GRAMMAR_KEYWORDS`, and the contextual word `assume`, which the grammar
reads only at the start of a member and which is otherwise an identifier.
`Bool` and `Int` are identifiers, which only the tree of a type interprets.
<!-- status: tested Spec.Language.Syntax.terminals_agree -->

```fren
pub mod spec::surface

use spec::lexical

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

> **Rationale:** The remainder is written `%`, and `mod` is only the keyword
> of a module declaration, so that no operator's meaning depends on where a
> line ends. This is decision S2 in the
> [development coverage](../../../docs/fren2-specification-coverage.md#syntax-decisions-and-design-debt).

### Examples

```fren2
fn remainder(x: Int): Int := x % 2
fn spread(a: Int, b: Int): Int := let r := a
    % b in r
mod second
```

Each of these is rejected by the rule it names. Its annotation is the
parser's message, which is not normative.

`syntax.expression.syntax`: a comparison is never followed by another.

```fren2 rejected
fn chained(a: Int, b: Int, c: Int): Bool := a < b <= c  --~ error: expected parentheses around a comparison or `iff` that would chain
```

`syntax.expression.syntax`: `iff` is never followed by another `iff`.

```fren2 rejected
fn both(a?, b?, c?): Bool := a? iff b? iff c?  --~ error: expected parentheses around a comparison or `iff` that would chain
```

`syntax.expression.syntax`: the right operand of `=` is a `Sum`, which
cannot start with `not`.

```fren2 rejected
fn negation(a?, b?): Bool := a? = not b?  --~ error: expected parentheses around `not` in a tighter operand
```

`syntax.expression.syntax`: a `let`'s definition is an `Iff`, which cannot
start with `let`.

```fren2 rejected
fn nested(x: Int): Int := let y := let z := x in z in y  --~ error: expected parentheses around `let` in an operator operand
```

`syntax.expression.syntax`: a match's scrutinee is a `Primary`, so the `+`
after `x` cannot continue it, and a `{` must follow it.

```fren2 rejected
fn scrutinee(x: Int): Int := match x + 1 { E::A => 1 }  --~ error: expected `{`
```

`syntax.expression.extent`: a `(` after a space makes no call.

```fren2 rejected
fn spaced(x: Int): Int := f (x)  --~ error: expected `(` adjacent to its called name
```

`syntax.expression.syntax`: an `if` has an `else` branch.

```fren2 rejected
fn unfinished(c?, x: Int): Int := if c? then x  --~ error: expected `else`
```

`syntax.declaration.lists`: a comma follows an item.

```fren2 rejected
fn empty(x: Int,,): Int := x  --~ error: expected an identifier
```

These lines group as the text after `--` writes with parentheses.

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

Each accepted text has one abstract syntax tree, which keeps what the text
means and drops how it is written.

r[syntax.tree.types] spec::surface::{identifier?, Identifier, Path, UnaryOp, BinaryOp, ExprF, Arm, TypeName, Parameter, Member, DeclarationF}
An expression tree is a fixed point of `ExprF`: `ExprF<E>` is one node,
whose subexpressions are of type `E`. A file's tree is the sequence of its
declarations' trees, each a `DeclarationF` whose expressions are expression
trees. The trees keep names as written paths and have no parentheses. An
`Identifier` is a word that is not a keyword, as `identifier?` says.
<!-- status: definition -->

> **Note:** `ExprF` takes its subexpressions as a parameter, rather than
> being a recursive enumeration, because a call's arguments and a match's
> arms are sequences of subexpressions, and today's Fren has no recursive
> datatype whose recursion passes through a `Seq`. For the same reason of
> today's Fren, `Identifier` constrains only the names that no sequence
> holds: a constraint on the elements of a `Seq` quantifies over them,
> outside the decidable core, so the other conditions of
> `syntax.tree.well-formed` are stated, and tested, rather than typed. This is gap G1 in the
> [development coverage](../../../docs/fren2-specification-coverage.md#syntax-decisions-and-design-debt).

```fren
pub enum UnaryOp { Neg, Not }

pub enum BinaryOp { Add, Sub, Mul, Div, Mod, Eq, Ne, Lt, Le, Gt, Ge, And, Or, Iff }

-- Whether `word` is an identifier: a word that is not a keyword.
pub fn identifier?(word: String) :=
    lexical::in_class?(lexical::Class::Word, word) and not word in lexical::KEYWORDS

pub type Identifier = word: String where identifier: identifier?(word)

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
    Let(Identifier, E, E),
    Match(E, Seq<Arm<E>>),
}

pub enum TypeName { Boolean, Integer, Named(Path) }

pub struct Parameter { name: String, annotation: Option<TypeName> }

pub enum MemberKind { Assume, Expect }

pub struct Member<E> { kind: MemberKind, label: String, body: E }

pub struct ModuleDeclaration { public?, path: Path }

pub struct EnumDeclaration { public?, name: Identifier, variants: Seq<String> }

pub struct FunctionDeclaration<E> {
    public?,
    name: Identifier,
    parameters: Seq<Parameter>,
    result: TypeName,
    body: E,
}

pub struct ExpectationDeclaration<E> { name: Identifier, parameters: Seq<Parameter>, members: Seq<Member<E>> }

-- One declaration, with expressions of type `E`.
pub enum DeclarationF<E> {
    Module(ModuleDeclaration),
    Enumeration(EnumDeclaration),
    Function(FunctionDeclaration<E>),
    Expectation(ExpectationDeclaration<E>),
}
```

r[syntax.tree.productions]
Each production gives its tree. `true` and `false` are `Boolean` nodes, and
a numeral an `Integer` node with its value. A `Path` is a `Name` node of its
identifiers, and a call a `Call` node of the path and the arguments' trees,
in order. `( e )` is the tree of `e`. A prefix operator and its operand are a
`Unary` node; a binary operator and its operands are a `Binary` node, and a
repetition such as `a - b - c` gives the nodes `(a - b) - c`, from the left.
`if`, `let` and `match` give `If`, `Let` and `Match` nodes of their parts. A
type's tree is as `syntax.path.syntax` says, a parameter's is its name and
its type if written, and each declaration's is the `DeclarationF` node of
its parts, with `public?` true when it is written with `pub`.
<!-- status: tested Spec.Language.Syntax.trees_agree -->

r[syntax.tree.well-formed]
A tree is *well formed* when every identifier in it, a path's segment, a
binder, a label, a parameter's or a declaration's name, or a variant,
satisfies `identifier?`; every path has at least one segment and every
arm's path at least two; and every call has at least one argument. The tree
of every accepted text is well formed.
<!-- status: tested Spec.Language.Syntax.trees_agree -->

r[syntax.tree.operators] spec::surface::{unary_spelling, binary_spelling}
The operators are spelled as `unary_spelling` and `binary_spelling` say. `-`
is both `Neg` and `Sub`, and its position decides which.
<!-- status: tested Spec.Language.Syntax.operators_agree -->

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

### Examples

Each line gives a text and, after `--`, its tree, written with the names of
`ExprF` and `DeclarationF`; a path is written with its `::`.

```fren2 trees
-1 -- (Unary Neg (Integer 1))
not true -- (Unary Not (Boolean true))
007 -- (Integer 7)
A::B::c -- (Name A::B::c)
((x)) -- (Name x)
f(g(x), (y),) -- (Call f (Call g (Name x)) (Name y))
a - b - c -- (Binary Sub (Binary Sub (Name a) (Name b)) (Name c))
x % 2 -- (Binary Mod (Name x) (Integer 2))
if b then let x := 1 in x else 2 -- (If (Name b) (Let x (Integer 1) (Name x)) (Integer 2))
match f(l) { E::A => not a, E::B => 1, } -- (Match (Call f (Name l)) (Arm E::A (Unary Not (Name a))) (Arm E::B (Integer 1)))
match l {} -- (Match (Name l))
pub mod a::b -- (File (Module pub a::b))
enum E { A, B, } -- (File (Enumeration E A B))
fn f(a: Bool, b: Int, c: E, d: Int::T, q?,): Bool := (a) -- (File (Function f (Parameter a Boolean) (Parameter b Integer) (Parameter c (Named E)) (Parameter d (Named Int::T)) (Parameter q?) Boolean (Name a)))
expect e(x: Int,) { assume a: x > 0 expect b: let y := x in y >= 0 } -- (File (Expectation e (Parameter x Integer) (Member Assume a (Binary Gt (Name x) (Integer 0))) (Member Expect b (Let y (Name x) (Binary Ge (Name y) (Integer 0))))))
```

## Properties

These properties of the grammar and its trees are proved or tested.

r[syntax.property.spellings] spec::surface::spellings::{binary, unary, shared, tokens, grammar_keywords, contextual}
Two binary operators have different spellings, as do two unary operators,
and a unary and a binary operator share a spelling only for `Neg` and `Sub`:
a token and its position determine the operator. Every operator's spelling
is a punctuator or a keyword of the grammar. The grammar's keywords are
keywords, and its contextual word is not.
<!-- status: smt -->

```fren
expect spellings(a: BinaryOp, b: BinaryOp, u: UnaryOp, v: UnaryOp, word: String) {
    expect binary: when a != b, binary_spelling(a) != binary_spelling(b)
    expect unary: when u != v, unary_spelling(u) != unary_spelling(v)
    expect shared: unary_spelling(u) = binary_spelling(a) iff u = UnaryOp::Neg and a = BinaryOp::Sub
    expect tokens: (binary_spelling(a) in lexical::PUNCTUATORS or binary_spelling(a) in GRAMMAR_KEYWORDS)
        and (unary_spelling(u) in lexical::PUNCTUATORS or unary_spelling(u) in GRAMMAR_KEYWORDS)
    expect grammar_keywords: when word in GRAMMAR_KEYWORDS, word in lexical::KEYWORDS
    expect contextual: when word in CONTEXTUAL, not word in lexical::KEYWORDS
}
```

r[syntax.property.unambiguous] spec::surface::{binary_category, unary_category, left_category, right_category, fits?}
The grammar is unambiguous up to parentheses and complete for well-formed
expression trees. Every well-formed tree has a text whose tree it is: the
text that writes each node's tokens and puts a subtree in parentheses
exactly where `fits?` says that it does not fit its place. This
parenthesization is minimal: dropping any pair of its parentheses gives a
text that the parser rejects or that has another tree. A subtree fits a
place when the nonterminal that derives it without parentheses, its
*category*, is no looser than the place's, unless it is *open*, an `if` or
`let`, or an operator node whose last subtree is open and stands without
parentheses, and something of the enclosing expression follows it. Declarations are outside this property.
<!-- status: tested Spec.Language.Syntax.roundtrip_agrees -->

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

pub fn unary_category(op: UnaryOp): Category := match op {
    UnaryOp::Neg => Category::Negation,
    UnaryOp::Not => Category::Not,
}

pub fn binary_category(op: BinaryOp): Category := match op {
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

pub fn non_associative?(op: BinaryOp) := binary_category(op) is Category::Comparison | Category::Iff

-- The category of a binary operator's right operand: the next tighter one.
pub fn right_category(op: BinaryOp): Category := match binary_category(op) {
    Category::Iff => Category::Or,
    Category::Or => Category::And,
    Category::And => Category::Not,
    Category::Comparison => Category::Sum,
    Category::Sum => Category::Product,
    _ => Category::Negation,
}

-- The category of a binary operator's left operand: its own if it groups
-- to the left, and otherwise the next tighter one.
pub fn left_category(op: BinaryOp): Category :=
    if non_associative?(op) then right_category(op) else binary_category(op)

-- Whether a subtree of category `child`, open or not, may stand without
-- parentheses at a place of category `place`, followed or not by more of
-- the enclosing expression.
pub fn fits?(child: Category, open?, place: Category, followed?) :=
    rank(child) >= rank(place) and not (open? and followed?)
```

r[syntax.property.operands] spec::surface::operands::{right, left_associative, non_associative}
Every binary operator's right operand is of a tighter category than the
operator. Its left operand is of the operator's own category when the
operator groups to the left, and of a tighter one when it does not
associate. A unary operator's operand is of the operator's own category.
For example, `a - b - c` needs no parentheses, `a < (b < c)` and
`(a < b) < c` both do, and `not not a` and `- - a` need none.
<!-- status: smt -->

```fren
expect operands(b: BinaryOp) {
    expect right: rank(right_category(b)) > rank(binary_category(b))
    expect left_associative: when not non_associative?(b), left_category(b) = binary_category(b)
    expect non_associative: when non_associative?(b), rank(left_category(b)) > rank(binary_category(b))
}
```

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
each rule alternative, and each optional or repeated part of a rule, is
used somewhere in the chapter's `fren2` blocks.

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
    expect at_most: wait(l, base,) <= 130
}

pub fn choose(b?, base: Int): Int := let delay := base + 5 in if b? then delay else base

expect division(x: Int) { expect euclidean: x = (x div 2) * 2 + x % 2 }

expect operators() {
    expect all: not (true iff false) or -1 < 2 and 3 != 4 and 5 > 4 and 6 >= 6 and 7 - 1 = 6
}

fn none(l: Light): Int := match l {}

fn typed(b?: Bool, n: Int::T,): Bool := b?
```

These are syntax, though later rules reject them: `y` is not in scope,
`Light` has no `+`, and the claim is false.

```fren2
pub enum Light { Red, Green }

pub fn unbound(x: Int): Int := y + 1

pub fn sum(l: Light): Int := l + 1

expect never_red(l: Light) { expect claim: l != Light::Red }
```
