# Printing fixes

A [fix](../Lint.md#fixing-lints) that rewrites an expression builds what it
writes as a tree: operators applied to operands, down to the expressions
that it keeps as written. In Fren's Lean code, `fren_expr!{ ... }` builds
the tree from Fren's own syntax, read by the parser of the `fren` command,
with `$x` for a subtree, and one printer writes every tree. So no fix
decides parentheses for itself, and a spec of a fix can say which tree it
writes rather than which text.

```fren
pub mod lint
```

## What printing does

Printing a tree gives a text that reads back as the tree, and that has no
parentheses that the grammar does not need: without any pair of those that
the printer adds, the text would read as another expression, or as none.
There is one exception, which [Parentheses in
fixes](../Lint.md#parentheses-in-fixes) makes: an open-ended form as an
argument, an element, an index or a field is in parentheses, though the
grammar would read it without them, to keep the reading plain.

`lint::printing` states this over the expressions and texts of the
grammar, given by the expression that each text reads as, `reads`, and
the texts that need each pair of parentheses that the printer adds in
them, but for a pair around an open-ended form in a part of an atom:
without any one of those pairs, the text would read as another expression,
or as none. The grammar writes every expression with some such text:

```fren
-- An expression, as the grammar of expressions reads it, and a text.
pub type Expression
pub type Text

set_option fren.lint.undecidable "allow" in
pub proc printing(
    expression: Expression,
    reads: Rel<Text, Expression>,    -- each text, and the expression that the grammar reads it as
    needed: Set<Text>,               -- the texts that need each pair of parentheses that the printer adds
): (text: Text) {
    assume writable: exists (t: Text), (t, expression) in reads and t in needed

    ensure reads_back: (text, expression) in reads
    ensure all_needed: text in needed
}
```

No spec models the parser, so the printer's tests check this: they print
random trees and read them back with the parser of the `fren` command.

## Trees

`lint::print` states how the printer writes a tree, for the operators and
the forms that take an operand in a place of their own. The precedences
are those of [`lang::operand`](../Lang/Expressions.md#operators), lowest
first, where an open-ended form, which extends as far right as it can,
binds most loosely, and an atom most tightly:

```fren
pub enum Precedence { Open, Iff, Or, And, Negation, Comparison, Sum, Product, Minus, Atom }

pub fn rank_of(l: Precedence): Int := match l {
    Precedence::Open => 0,
    Precedence::Iff => 1,
    Precedence::Or => 2,
    Precedence::And => 3,
    Precedence::Negation => 4,
    Precedence::Comparison => 5,
    Precedence::Sum => 6,
    Precedence::Product => 7,
    Precedence::Minus => 8,
    Precedence::Atom => 9,
}
```

The binary operators, each with its precedence, its associativity and its
lexeme:

```fren
pub enum BinOp {
    Iff, Or, And, Eq, Ne, Lt, Le, Gt, Ge, In, Subset,
    Plus, Sub, Concat, Union, Without, Times, Div, Mod, Inter, Join,
}

pub fn op_precedence(o: BinOp): Precedence := match o {
    BinOp::Iff => Precedence::Iff,
    BinOp::Or => Precedence::Or,
    BinOp::And => Precedence::And,
    BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::In | BinOp::Subset => Precedence::Comparison,
    BinOp::Plus | BinOp::Sub | BinOp::Concat | BinOp::Union | BinOp::Without => Precedence::Sum,
    BinOp::Times | BinOp::Div | BinOp::Mod | BinOp::Inter | BinOp::Join => Precedence::Product,
}

pub fn op_assoc(o: BinOp): Assoc :=
    if op_precedence(o) is Precedence::Iff | Precedence::Comparison then Assoc::NonAssoc else Assoc::Left

pub fn lexeme(o: BinOp): String := match o {
    BinOp::Iff => "iff",
    BinOp::Or => "or",
    BinOp::And => "and",
    BinOp::Eq => "=",
    BinOp::Ne => "!=",
    BinOp::Lt => "<",
    BinOp::Le => "<=",
    BinOp::Gt => ">",
    BinOp::Ge => ">=",
    BinOp::In => "in",
    BinOp::Subset => "subset",
    BinOp::Plus => "+",
    BinOp::Sub => "-",
    BinOp::Concat => "++",
    BinOp::Union => "union",
    BinOp::Without => "minus",
    BinOp::Times => "*",
    BinOp::Div => "div",
    BinOp::Mod => "mod",
    BinOp::Inter => "inter",
    BinOp::Join => "join",
}
```

A tree is an expression as written, or an operator or a form applied to
trees. An expression as written comes with its text, its precedence,
whether it ends in an open-ended form, and whether it can be a receiver,
before the `.` of a field read or a method call, without parentheses: an
integer, `true`, `false`, a name that ends in `?` and a path of more than
one segment, as `E::A`, cannot. A name or a literal is an expression as
written, an atom. `Test(e, p)` is the pattern test `e is p`, with the
pattern as written, and `Field(e, x)` reads the field `x` of `e`:

```fren
pub enum FixTree {
    Written(String, Precedence, Bool, Bool),
    Bin(BinOp, FixTree, FixTree),
    Not(FixTree),
    Neg(FixTree),
    When(Bool, FixTree, FixTree),      -- `when c, d`, or `unless c, d` if negated
    If(FixTree, FixTree, FixTree),
    Test(FixTree, String),
    Field(FixTree, String),
}

pub fn precedence_of(t: FixTree): Precedence := match t {
    FixTree::Written(_, l, _, _) => l,
    FixTree::Bin(o, _, _) => op_precedence(o),
    FixTree::Not(_) => Precedence::Negation,
    FixTree::Neg(_) => Precedence::Minus,
    FixTree::When(_, _, _) | FixTree::If(_, _, _) => Precedence::Open,
    FixTree::Test(_, _) => Precedence::Comparison,
    FixTree::Field(_, _) => Precedence::Atom,
}

pub fn receivable?(t: FixTree) := match t {
    FixTree::Written(_, _, _, receivable?) => receivable?,
    _ => true,
}

pub fn atom(text: String): FixTree := FixTree::Written(text, Precedence::Atom, false, true)
```

`bare_operand?` is `lang::operand` over these precedences. A tree *ends open* where it
is an open-ended form, or its last operand is written without parentheses
and ends open. An operand is written without them where `lang::operand`
allows it, unless it ends open and something follows it, which it would
take in: a left operand is followed by its operator, a `when`'s condition
by its `,`, and a receiver by its `.`. A receiver is in parentheses also
where it cannot be one without them:

```fren
pub fn bare_operand?(outer: Precedence, inner: Precedence, assoc: Assoc, right?) :=
    rank_of(inner) > rank_of(outer)
    or (rank_of(inner) = rank_of(outer) and ((assoc = Assoc::Left and not right?) or (assoc = Assoc::Right and right?)))

pub fn ends_open?(t: FixTree) := match t {
    FixTree::Written(_, _, open?, _) => open?,
    FixTree::Bin(o, _, b) => bare_operand?(op_precedence(o), precedence_of(b), op_assoc(o), true) and ends_open?(b),
    FixTree::Not(a) => bare_operand?(Precedence::Negation, precedence_of(a), Assoc::Right, true) and ends_open?(a),
    FixTree::Neg(a) => bare_operand?(Precedence::Minus, precedence_of(a), Assoc::Right, true) and ends_open?(a),
    FixTree::When(_, _, _) | FixTree::If(_, _, _) => true,
    _ => false,
}

pub fn bare?(t: FixTree, outer: Precedence, assoc: Assoc, right?, followed?) :=
    bare_operand?(outer, precedence_of(t), assoc, right?) and not ((followed? or not right?) and ends_open?(t))
```

The text of a tree is its operands' texts, each in parentheses where it is
not bare, between its operator's lexemes. A negation of a text that starts
with `-` has a space after its `-`, which would otherwise start a comment.
The condition and the branches of `if` are between keywords, so any
expression can be written there:

```fren
set_option fren.lint.undecidable "allow" in
pub fn enclosed(text: String, plain?): String := if plain? then text else "(" ++ text ++ ")"

set_option fren.lint.undecidable "allow" in
pub fn negated(text: String): String := if text.starts_with?("-") then "- " ++ text else "-" ++ text

set_option fren.lint.undecidable "allow" in
pub fn printed(t: FixTree): String := match t {
    FixTree::Written(s, _, _, _) => s,
    FixTree::Bin(o, a, b) =>
        enclosed(printed(a), bare?(a, op_precedence(o), op_assoc(o), false, true)) ++ " " ++ lexeme(o) ++ " "
        ++ enclosed(printed(b), bare?(b, op_precedence(o), op_assoc(o), true, false)),
    FixTree::Not(a) => "not " ++ enclosed(printed(a), bare?(a, Precedence::Negation, Assoc::Right, true, false)),
    FixTree::Neg(a) => negated(enclosed(printed(a), bare?(a, Precedence::Minus, Assoc::Right, true, false))),
    FixTree::When(negated?, c, d) =>
        (if negated? then "unless " else "when ") ++ enclosed(printed(c), bare?(c, Precedence::Open, Assoc::NonAssoc, false, true))
        ++ ", " ++ enclosed(printed(d), bare?(d, Precedence::Open, Assoc::Right, true, false)),
    FixTree::If(c, a, b) => "if " ++ printed(c) ++ " then " ++ printed(a) ++ " else " ++ printed(b),
    FixTree::Test(e, p) => enclosed(printed(e), bare?(e, Precedence::Comparison, Assoc::NonAssoc, false, true)) ++ " is " ++ p,
    FixTree::Field(e, x) =>
        enclosed(printed(e), bare?(e, Precedence::Atom, Assoc::Left, false, true) and receivable?(e)) ++ "." ++ x,
}
```

`lint::print` gives a tree's text, its precedence, and whether it ends open, which
decide how a tree that has it as an operand writes it:

```fren
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "tested" in
pub proc print(tree: FixTree): (det text: String, det precedence: Precedence, det open?) {
    out text := printed(tree)
    out precedence := precedence_of(tree)
    out open? := ends_open?(tree)

    expect looser_right: when tree = FixTree::Bin(BinOp::And, atom("a"), FixTree::Bin(BinOp::Or, atom("b"), atom("c"))),
        text = "a and (b or c)"
    expect left_associative: when tree = FixTree::Bin(BinOp::Sub, FixTree::Bin(BinOp::Sub, atom("a"), atom("b")), atom("c")),
        text = "a - b - c"
    expect right_kept: when tree = FixTree::Bin(BinOp::Sub, atom("a"), FixTree::Bin(BinOp::Sub, atom("b"), atom("c"))),
        text = "a - (b - c)"
    expect non_associative: when tree = FixTree::Bin(BinOp::Eq, FixTree::Bin(BinOp::Eq, atom("a"), atom("b")), atom("c")),
        text = "(a = b) = c"
    expect open_last: when tree = FixTree::Bin(BinOp::And, atom("a"), FixTree::Written("x + if p? then 1 else 2", Precedence::Sum, true, true)),
        text = "a and x + if p? then 1 else 2" and open?
    expect open_followed: when tree = FixTree::Bin(BinOp::And, FixTree::Written("x + if p? then 1 else 2", Precedence::Sum, true, true), atom("a")),
        text = "(x + if p? then 1 else 2) and a" and not open?
    expect test_scrutinee: when tree = FixTree::Not(FixTree::Test(FixTree::Written("a or b", Precedence::Or, false, true), "E::A | E::B")),
        text = "not (a or b) is E::A | E::B"
    expect double_negation: when tree = FixTree::Neg(FixTree::Neg(atom("x"))), text = "- -x"
    expect receiver: when tree = FixTree::Field(FixTree::Written("a + b", Precedence::Sum, false, true), "abs"), text = "(a + b).abs"
    expect variant_receiver: when tree = FixTree::Field(FixTree::Written("E::A", Precedence::Atom, false, false), "min"),
        text = "(E::A).min"
}
```

`bare_operand?` is `lang::operand`, at the ranks of the precedences:

```fren
expect bare_operand_is_operand(outer: Precedence, inner: Precedence, assoc: Assoc, right?) {
    call o := operand(rank_of(outer), rank_of(inner), assoc, right?)
    expect same: o.bare? iff bare_operand?(outer, inner, assoc, right?)
}
```

The printer writes the other forms of its trees in the same way: the
operands of a chained comparison as a comparison's, and a receiver, an
argument, an element and an index as [Parentheses in
fixes](../Lint.md#parentheses-in-fixes) says. Its tests check them against
`lint::printing`.

```fren
#fren_check printing
#fren_check print
#fren_check bare_operand_is_operand
```
