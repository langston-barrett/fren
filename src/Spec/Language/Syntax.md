# Syntax

This chapter gives the grammar of Fren, which sequences of tokens form a
program, and the abstract syntax tree of each accepted program. The tokens
are those of [Lexical structure](LexicalStructure.md). Syntax alone gives a
program no meaning: names are resolved, types checked and checks verified
by later rules. `y + 1` is a syntactically valid body even where no `y` is
in scope, and `l + 1` is valid even where `l` is not an integer.

The abstract syntax keeps a program's names as written paths.
[Resolution](NamesAndScope.md) takes this tree and gives the Core, the
resolved form with items by identity and locals by index, which
[Core typing](Types.md) types. The lossless tree, which also keeps
parentheses, trivia and every token, is the subject of
[AST and parsing](../Compiler/AstAndParsing.md).

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

r[syntax.notation.trivia-sensitive]
Trivia may come between any two tokens, and line endings are trivia like
any other: an expression may continue on the next line, as `let r := a`
and then `% b` does. One terminal depends on the trivia before it:
`TouchingOpen` is a `(` with no trivia between it and the token before it,
no space, tab, line ending or comment.

## Programs

A program is a file of declarations.

r[syntax.file.syntax]
A source text is read as a `File`, or, where a single expression is
expected, as an `ExpressionEntry`. Either is accepted only when it matches
all of the text's tokens. A text of trivia alone is an empty `File`, and no
`ExpressionEntry`.

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
the type that the path names, as for `E` and `a::T`, which name resolution
finds.

```grammar
Path          ::= Identifier ("::" Identifier)*
QualifiedPath ::= Identifier ("::" Identifier)+
Type          ::= Path
```

r[syntax.name.reserved]
`Bool` and `Int` are reserved names: no module, enumeration, variant,
function, global expectation, parameter or member label is named `Bool` or
`Int`, and no `let` binds either name. They are identifiers, so the
grammar accepts such a name, and resolution rejects it.
[`reserved?`](NamesAndScope.md#r-names.paths.reserved) defines the reserved
names. [Resolution](NamesAndScope.md) states where it rejects an
enumeration, variant, function, parameter or `let` binder of such a name:
in [collection](NamesAndScope.md#r-names.collection.reserved), for a
declaration's names and a function's parameters, and in the
[`let` layer](NamesAndScope.md#r-names.expression.layer), for a binder.
Its judgments do not yet state the rejection of a module, a global
expectation or a member label of such a name, which is
[open](NamesAndScope.md#r-names.paths.reserved).

> **Rationale:** A type written `Bool` or `Int` always denotes the built-in
> type, so a declaration of that name could never be referred to as a
> type. A label or a local of either name could be referred to, but a
> reader would take it for the type, so these names are reserved for every
> binder. This is decision D2 in the
> [development coverage](../../../docs/fren2-specification-coverage.md#syntax-decisions-and-design-debt).

### Examples

Each of these is rejected by name resolution, with the annotated message,
by the rule it names.

`syntax.name.reserved`: an enumeration is named `Int`.

```fren2 unresolved
mod shapes
enum Int { Small, Large }  --~ error: `Int` is a built-in type and cannot be redefined
```

`syntax.name.reserved`: a function's parameter is named `Bool`.

```fren2 unresolved
mod shapes
fn f(Bool: Int): Int := 1  --~ error: `Bool` is a built-in type and cannot be redefined
```

`syntax.name.reserved`: a member's label is `Int`.

```fren2 unresolved
mod shapes
expect e(x: Int) {
    expect Int: x = x  --~ error: `Int` is a built-in type and cannot be redefined
}
```

`syntax.name.reserved`: a `let` binds `Bool`.

```fren2 unresolved
mod shapes
fn g(x: Int): Int := let Bool := x in Bool  --~ error: `Bool` is a built-in type and cannot be redefined
```

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
type, which is then `Bool`.

> **Note:** `b?`, `b?: Bool` and `b?: Int` are all parameters of this
> grammar. Whether a name that ends in `?` may have a type other than
> `Bool` is a question of typing, which this chapter does not answer.

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

Only a `(` that touches a path makes a call: in `f (x)` the path `f` is
complete, and no rule accepts the `(x)` after it.

r[syntax.expression.terminals] spec::surface::{CONTEXTUAL, GRAMMAR_KEYWORDS}
The quoted terminals of the grammar are every punctuator, the keywords
`GRAMMAR_KEYWORDS`, and the contextual word `assume`, which the grammar
reads only at the start of a member and which is otherwise an identifier.
`Bool` and `Int` are identifiers, which only the tree of a type interprets.

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

`syntax.notation.trivia-sensitive`: a `(` after a space makes no call.

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

r[syntax.tree.types] spec::surface::{Snoc, Path, UnaryOp, BinaryOp, SurfaceF, SurfaceArm, TypeName, Parameter, MemberKind, Member, ModuleDeclaration, EnumDeclaration, FunctionDeclaration, ExpectationDeclaration, DeclarationF}
An expression tree is a fixed point of `SurfaceF`: `SurfaceF<E>` is one
node of the surface tree, whose subexpressions are of type `E`. A path is
a name, or a path and one more name: `a::b::c` is
`Member(Member(Name("a"), "b"), "c")`. A call's arguments and a match's
arms are *snoc sequences* in written order: a snoc sequence is empty, or
an earlier one extended by one last entry. This is the one definition of
the parsed tree: [Resolution](NamesAndScope.md) resolves these nodes and
gives the Core's, `CoreF`. A file's tree is the sequence of its
declarations' trees, each a `DeclarationF` whose expressions are expression
trees. The trees keep names as written paths and have no parentheses. The
types admit more than the trees of texts: `syntax.tree.well-formed` says
which of their values are well formed.

> **Note:** An `Integer` node carries an `Int`, though a numeral's value is
> never negative, because resolution holds nodes in snoc sequences, and
> today's Fren admits no constrained type, such as `Nat`, inside a
> recursive enumeration's argument. `syntax.tree.well-formed` states the
> bound.

> **Note:** `SurfaceF` takes its subexpressions as a parameter, rather
> than being a recursive enumeration, because a call's arguments and a
> match's arms are sequences of subexpressions, and today's Fren has no
> recursive datatype whose recursion passes through a sequence. A path, the
> arguments and the arms are recursive enumerations rather than `Seq`s
> because a Fren function recurs only over a recursive enumeration, and
> resolution walks all three. A declaration's variants, parameters and
> members, which this chapter only quantifies over, are `Seq`s. A name is
> a `String`,
> not a type of identifiers, because most names are in sequences, and a
> `Seq` whose element type has a constraint is outside Fren's decidable
> core. A quantifier over a sequence's elements is inside it, unless it
> passes an element that itself holds a sequence, such as a parameter,
> to a function. `syntax.tree.well-formed` states every condition on a
> declaration's names with such quantifiers, and the one over parameters
> is a definition outside the decidable core. This is decision G1 in the
> [development coverage](../../../docs/fren2-specification-coverage.md#syntax-decisions-and-design-debt).

```fren
pub enum UnaryOp { Neg, Not }

pub enum BinaryOp { Add, Sub, Mul, Div, Rem, Eq, Ne, Lt, Le, Gt, Ge, And, Or, Iff }

-- A snoc sequence: empty, or an earlier one and its last entry.
pub enum Snoc<T> { Empty, Extend(Snoc<T>, T) }

-- A path: its first identifier, or a path and its last identifier.
pub enum Path { Name(String), Member(Path, String) }

-- A match arm of the surface tree: a variant's path and a body.
pub struct SurfaceArm<E> { variant: Path, body: E }

-- One node of the surface tree, with subexpressions of type `E`.
pub enum SurfaceF<E> {
    Boolean(Bool),
    Integer(Int),
    Name(Path),
    Call(Path, Snoc<E>),
    Unary(UnaryOp, E),
    Binary(BinaryOp, E, E),
    If(E, E, E),
    Let(String, E, E),
    Match(E, Snoc<SurfaceArm<E>>),
}

pub enum TypeName { Boolean, Integer, Named(Path) }

pub struct Parameter { name: String, annotation: Option<TypeName> }

pub enum MemberKind { Assume, Expect }

pub struct Member<E> { kind: MemberKind, label: String, body: E }

pub struct ModuleDeclaration { public?, path: Path }

pub struct EnumDeclaration { public?, name: String, variants: Seq<String> }

pub struct FunctionDeclaration<E> {
    public?,
    name: String,
    parameters: Seq<Parameter>,
    result: TypeName,
    body: E,
}

pub struct ExpectationDeclaration<E> { name: String, parameters: Seq<Parameter>, members: Seq<Member<E>> }

-- One declaration, with expressions of type `E`.
pub enum DeclarationF<E> {
    Module(ModuleDeclaration),
    Enumeration(EnumDeclaration),
    Function(FunctionDeclaration<E>),
    Expectation(ExpectationDeclaration<E>),
}
```

r[syntax.tree.productions] spec::surface::type_name
Each production gives its tree. `true` and `false` are `Boolean` nodes, and
a numeral an `Integer` node with its value. A `Path` is a `Name` node of its
path, and a call a `Call` node of the path and the arguments' trees, in
order. `( e )` is the tree of `e`. A prefix operator and its operand are a
`Unary` node; a binary operator and its operands are a `Binary` node, and a
repetition such as `a - b - c` gives the nodes `(a - b) - c`, from the left.
`if`, `let` and `match` give `If`, `Let` and `Match` nodes of their parts. A
type's tree is the `type_name` of its path, a parameter's is its name and
its type if written, and each declaration's is the `DeclarationF` node of
its parts, with `public?` true when it is written with `pub`.

```fren
-- The tree of a type written as `path`.
pub fn type_name(path: Path): TypeName :=
    if path = Path::Name("Bool") then TypeName::Boolean
    else if path = Path::Name("Int") then TypeName::Integer
    else TypeName::Named(path)
```

r[syntax.tree.well-formed] spec::surface::{identifier?, path?, qualified?, Elided, arm_well_formed?, arms_well_formed?, node_well_formed?, type_well_formed?, parameter_well_formed?, parameters_well_formed?, declaration_well_formed?}
A tree is *well formed* when each of its nodes, types, parameters and
declarations is. An identifier is a word that is not a keyword, and a path
is a path when each of its names is an identifier. An expression node is
well formed when its integer is not negative, its path is a path, a call
has at least one argument, a `let` binds an identifier, and each arm's path
has at least two segments. A named type is well formed
when its path is a path other than `Bool` and `Int` alone, which
`type_name` never names. A parameter is well formed when its name is an
identifier and its type is well formed, and it has a type unless its name
ends in `?`. A declaration is well formed when its names, variants and
labels are identifiers, its module path is a path, its parameters and
result type are well formed, a function has at least one parameter and an
enumeration at least one variant. None of this looks at a node's
subexpressions, which the functions take as `Elided`.

```fren
-- Whether `word` is an identifier: a word that is not a keyword.
pub fn identifier?(word: String) :=
    lexical::in_class?(lexical::Class::Word, word) and not word in lexical::KEYWORDS

-- Whether each name of `path` is an identifier.
pub fn path?(path: Path) := match path {
    Path::Name(name) => identifier?(name),
    Path::Member(qualifier, name) => path?(qualifier) and identifier?(name),
}

-- Whether `path` has at least two segments.
pub fn qualified?(path: Path) := path is Path::Member(_, _)

-- A subexpression that is left out.
pub enum Elided { Elided }

pub fn arm_well_formed?(arm: SurfaceArm<Elided>) := path?(arm.variant) and qualified?(arm.variant)

pub fn arms_well_formed?(arms: Snoc<SurfaceArm<Elided>>) := match arms {
    Snoc::Empty => true,
    Snoc::Extend(earlier, arm) => arms_well_formed?(earlier) and arm_well_formed?(arm),
}

pub fn node_well_formed?(node: SurfaceF<Elided>) := match node {
    SurfaceF::Integer(value) => value >= 0,
    SurfaceF::Name(path) => path?(path),
    SurfaceF::Call(path, arguments) => path?(path) and arguments != Snoc::Empty,
    SurfaceF::Let(binder, _, _) => identifier?(binder),
    SurfaceF::Match(_, arms) => arms_well_formed?(arms),
    _ => true,
}

pub fn type_well_formed?(ty: TypeName) := match ty {
    TypeName::Named(path) => path?(path) and type_name(path) = ty,
    _ => true,
}

pub fn parameter_well_formed?(parameter: Parameter) :=
    identifier?(parameter.name)
    and match parameter.annotation {
        Option::Some(ty) => type_well_formed?(ty),
        Option::None => parameter.name.ends_with?("?"),
    }

set_option fren.lint.undecidable "allow" in  -- an element that holds a sequence is the argument of a function
pub fn parameters_well_formed?(parameters: Seq<Parameter>) :=
    forall (parameter: Parameter), when parameter in parameters, parameter_well_formed?(parameter)

pub fn declaration_well_formed?(declaration: DeclarationF<Elided>) := match declaration {
    DeclarationF::Module(d) => path?(d.path),
    DeclarationF::Enumeration(d) =>
        identifier?(d.name) and d.variants != []
        and (forall (variant: String), when variant in d.variants, identifier?(variant)),
    DeclarationF::Function(d) =>
        identifier?(d.name) and d.parameters != [] and parameters_well_formed?(d.parameters)
        and type_well_formed?(d.result),
    DeclarationF::Expectation(d) =>
        identifier?(d.name) and parameters_well_formed?(d.parameters)
        and (forall (member: Member<Elided>), when member in d.members, identifier?(member.label)),
}
```

r[syntax.tree.operators] spec::surface::{unary_spelling, binary_spelling}
The operators are spelled as `unary_spelling` and `binary_spelling` say. `-`
is both `Neg` and `Sub`, and its position decides which.

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
    BinaryOp::Rem => "%",
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
`SurfaceF` and `DeclarationF`; a path is written with its `::`, an arm,
which is a `SurfaceArm`, as `Arm` with its path and body, and the entries
of a snoc sequence one after another.

```fren2 trees
-1 -- (Unary Neg (Integer 1))
not true -- (Unary Not (Boolean true))
007 -- (Integer 7)
A::B::c -- (Name A::B::c)
((x)) -- (Name x)
f(g(x), (y),) -- (Call f (Call g (Name x)) (Name y))
a - b - c -- (Binary Sub (Binary Sub (Name a) (Name b)) (Name c))
x % 2 -- (Binary Rem (Name x) (Integer 2))
if b then let x := 1 in x else 2 -- (If (Name b) (Let x (Integer 1) (Name x)) (Integer 2))
match f(l) { E::A => not a, E::B => 1, } -- (Match (Call f (Name l)) (Arm E::A (Unary Not (Name a))) (Arm E::B (Integer 1)))
match l {} -- (Match (Name l))
pub mod a::b -- (File (Module pub a::b))
enum E { A, B, } -- (File (Enumeration E A B))
fn f(a: Bool, b: Int, c: E, d: a::T, q?,): Bool := (a) -- (File (Function f (Parameter a Boolean) (Parameter b Integer) (Parameter c (Named E)) (Parameter d (Named a::T)) (Parameter q?) Boolean (Name a)))
expect e(x: Int,) { assume a: x > 0 expect b: let y := x in y >= 0 } -- (File (Expectation e (Parameter x Integer) (Member Assume a (Binary Gt (Name x) (Integer 0))) (Member Expect b (Let y (Name x) (Binary Ge (Name y) (Integer 0))))))
```

## Properties

These properties of the grammar and its trees are proved or tested.

r[syntax.property.well-formed] spec::surface::accepted_trees_well_formed
The tree of every text that the grammar accepts is well formed.

```fren
pub proc accepted_trees_well_formed(): (holds?) { ensure output: holds? }

tested accepted_trees_well_formed: "src/FrenTest/SpecChapters/Syntax.lean"
```

r[syntax.property.terminals] spec::surface::grammar_terminals
The grammar's punctuators are exactly `PUNCTUATORS`, its keywords exactly
`GRAMMAR_KEYWORDS`, and its other quoted words exactly `CONTEXTUAL`.

```fren
pub proc grammar_terminals(): (holds?) { ensure output: holds? }

tested grammar_terminals: "src/FrenTest/SpecChapters/Syntax.lean"
```

r[syntax.property.spellings] spec::surface::spellings::{binary, unary, shared, tokens, grammar_keywords, contextual}
Two binary operators have different spellings, as do two unary operators,
and a unary and a binary operator share a spelling only for `Neg` and `Sub`:
a token and its position determine the operator. Every operator's spelling
is a punctuator or a keyword of the grammar. The grammar's keywords are
keywords, and its contextual word is not.

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

r[syntax.property.extent] spec::surface::extent
The `else` branch of an `if` and the body of a `let` extend as far to the
right as they can, because the grammar's repetitions never give a match
back: `a + if b then c else d + e` groups as `a + (if b then c else (d + e))`,
and every `fren2 groups` example groups as it says.

```fren
pub proc extent(): (holds?) { ensure output: holds? }

tested extent: "src/FrenTest/SpecChapters/Syntax.lean"
```

r[syntax.property.print-parse] spec::surface::{Category, rank, binary_category, unary_category, non_associative?, left_category, right_category, Shape, Place, fits?, placed, place, shaped, shape, print_parse}
Every well-formed expression tree has a *text*, and the tree of that text
is the tree. The text writes each node's tokens in the order of its
production: an operator as `syntax.tree.operators` spells it, a numeral in
decimal digits without a leading zero, and a list without a trailing
comma. One space separates each two consecutive tokens, except that a
call's `(` touches its path, so no two tokens join into another piece:
the text of a negated negation is `- - x`, not `--x`, which begins a
comment. A subtree stands in parentheses exactly where `fits?` says that
its `shape` does not fit its `place`. A binary operator's operands are at
`left_category` and `right_category`, a unary operator's operand at the
operator's own category, and every other subexpression at `Expression`,
but a `let`'s definition and an arm's body at `Iff`, as the grammar's
`let` and `Arm` take an `Iff` there, and a match's scrutinee at `Primary`.
A subtree fits a place when the nonterminal that derives it without
parentheses, its *category*, is no looser than the place's, unless it is
*open*, an `if` or `let`, or an operator node whose last subtree is open
and stands without parentheses, and it is the left operand of a binary
operator, which would follow it. Elsewhere a keyword or punctuator that no
expression continues with, such as `then`, `in`, `,` or `)`, ends an open
subtree.

This parenthesization is minimal: dropping any pair of the text's
parentheses gives a text that the parser rejects or that has another tree.
Conversely, the text of the tree of an accepted expression has that
expression's tokens, apart from pairs of parentheses, trailing commas and
the leading zeros of numerals. So the trees do not distinguish `f(1,)`
from `f(1)`, `(x)` from `x`, or `007` from `7`, and distinguish every
other two expressions that differ in a token. Declarations are outside
this property.

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
    BinaryOp::Rem => Category::Product,
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

-- A subtree as its place sees it: its category, and whether it is open.
pub struct Shape { category: Category, open? }

-- A place for a subtree: its category, and whether it is a binary
-- operator's left operand.
pub struct Place { category: Category, left_operand? }

-- Whether a subtree of shape `child` may stand at `place` without
-- parentheses.
pub fn fits?(child: Shape, place: Place) :=
    rank(child.category) >= rank(place.category) and not (child.open? and place.left_operand?)

pub fn placed(category: Category, left_operand?): Place := Place { category, left_operand? }

-- The place of the subexpression `k` of `node`, counting from 0 in the
-- order of `SurfaceF`: a call's arguments and a match's arms follow one
-- another.
pub fn place<E>(node: SurfaceF<E>, k: Int): Place := match node {
    SurfaceF::Unary(op, _) => placed(unary_category(op), false),
    SurfaceF::Binary(op, _, _) =>
        if k = 0 then placed(left_category(op), true) else placed(right_category(op), false),
    SurfaceF::Let(_, _, _) => placed(if k = 0 then Category::Iff else Category::Expression, false),
    SurfaceF::Match(_, _) => placed(if k = 0 then Category::Primary else Category::Iff, false),
    _ => placed(Category::Expression, false),
}

pub fn shaped(category: Category, open?): Shape := Shape { category, open? }

-- The shape of `node`, given the shapes of its subexpressions.
pub fn shape(node: SurfaceF<Shape>): Shape := match node {
    SurfaceF::Unary(op, operand) => shaped(
        unary_category(op),
        operand.open? and fits?(operand, place(node, 0))
    ),
    SurfaceF::Binary(op, _, right) => shaped(
        binary_category(op),
        right.open? and fits?(right, place(node, 1))
    ),
    SurfaceF::If(_, _, _) => shaped(Category::Primary, true),
    SurfaceF::Let(_, _, _) => shaped(Category::Expression, true),
    _ => shaped(Category::Primary, false),
}

pub proc print_parse(): (holds?) { ensure output: holds? }

tested print_parse: "src/FrenTest/SpecChapters/Syntax.lean"
```

r[syntax.property.operands] spec::surface::operands::{right, left_associative, non_associative}
Every binary operator's right operand is of a tighter category than the
operator. Its left operand is of the operator's own category when the
operator groups to the left, and of a tighter one when it does not
associate. For example, `a - b - c` needs no parentheses, and
`a < (b < c)` and `(a < b) < c` both do.

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

These declarations use the forms of the grammar.

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

fn typed(b?: Bool, n: a::T,): Bool := b?
```

These are syntax, though later rules reject them: `y` is not in scope,
`Light` has no `+`, and the claim is false.

```fren2
pub enum Light { Red, Green }

pub fn unbound(x: Int): Int := y + 1

pub fn sum(l: Light): Int := l + 1

expect never_red(l: Light) { expect claim: l != Light::Red }
```
