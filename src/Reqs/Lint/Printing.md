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

## Trees

The precedences are those of
[`lang::operand`](../Lang/Expressions.md#operators), lowest first. `Open`
is that of an open-ended form, which extends as far right as it can:
`when`, `unless`, a quantifier and a conditional. `Not` is that of `not`,
and `Negative` that of `-` before an operand:

```fren
pub enum Precedence { Open, Iff, Or, And, Not, Comparison, Sum, Product, Negative, Atom }

pub fn rank_of(p: Precedence): Int := match p {
    Precedence::Open => 0,
    Precedence::Iff => 1,
    Precedence::Or => 2,
    Precedence::And => 3,
    Precedence::Not => 4,
    Precedence::Comparison => 5,
    Precedence::Sum => 6,
    Precedence::Product => 7,
    Precedence::Negative => 8,
    Precedence::Atom => 9,
}
```

The binary operators, each with its precedence, its associativity and its
lexeme. `Minus` is `-` between operands, and `Difference` the `minus` of
sets:

```fren
pub enum BinOp {
    Iff, Or, And, Eq, Ne, Lt, Le, Gt, Ge, In, Subset,
    Plus, Minus, Concat, Union, Difference, Times, Div, Mod, Inter, Join,
}

pub fn op_precedence(o: BinOp): Precedence := match o {
    BinOp::Iff => Precedence::Iff,
    BinOp::Or => Precedence::Or,
    BinOp::And => Precedence::And,
    BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::In | BinOp::Subset => Precedence::Comparison,
    BinOp::Plus | BinOp::Minus | BinOp::Concat | BinOp::Union | BinOp::Difference => Precedence::Sum,
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
    BinOp::Minus => "-",
    BinOp::Concat => "++",
    BinOp::Union => "union",
    BinOp::Difference => "minus",
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
one segment, as `E::A`, cannot, since `E::A.x` reads `A.x` as one
segment. `Test(e, p)` is the pattern test `e is p`, with the pattern as
written, and `Field(e, x)` reads the field `x` of `e`:

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
    FixTree::Written(_, p, _, _) => p,
    FixTree::Bin(o, _, _) => op_precedence(o),
    FixTree::Not(_) => Precedence::Not,
    FixTree::Neg(_) => Precedence::Negative,
    FixTree::When(_, _, _) | FixTree::If(_, _, _) => Precedence::Open,
    FixTree::Test(_, _) => Precedence::Comparison,
    FixTree::Field(_, _) => Precedence::Atom,
}

-- A field read can be a receiver unless its name ends in `?`, which no
-- identifier continues.
set_option fren.lint.undecidable "allow" in
pub fn receivable?(t: FixTree) := match t {
    FixTree::Written(_, _, _, receivable?) => receivable?,
    FixTree::Field(_, x) => not x.ends_with?("?"),
    _ => true,
}

pub fn atom(text: String): FixTree := FixTree::Written(text, Precedence::Atom, false, true)
```

An operand is in a *place*: an operand of an operator of a precedence and
an associativity, on its right or not, with something after it or not; a
receiver; a part of an atom between delimiters, as an argument, an element
or an index; or the condition or a branch of `if`, between keywords:

```fren
pub enum Place {
    Operand(Precedence, Assoc, Bool, Bool),    -- outer precedence, associativity, on the right, followed
    Receiver,
    Delimited,
    Branch,
}
```

A printed tree *ends open* where it is an open-ended form, or its last
operand is written without parentheses and ends open: then it would take
in what follows it.

```fren
pub fn bare_operand?(outer: Precedence, inner: Precedence, assoc: Assoc, right?) :=
    rank_of(inner) > rank_of(outer)
    or (rank_of(inner) = rank_of(outer) and ((assoc = Assoc::Left and not right?) or (assoc = Assoc::Right and right?)))

pub fn ends_open?(t: FixTree) := match t {
    FixTree::Written(_, _, open?, _) => open?,
    FixTree::Bin(o, _, b) => bare_operand?(op_precedence(o), precedence_of(b), op_assoc(o), true) and ends_open?(b),
    FixTree::Not(a) => bare_operand?(Precedence::Not, precedence_of(a), Assoc::Right, true) and ends_open?(a),
    FixTree::Neg(a) => bare_operand?(Precedence::Negative, precedence_of(a), Assoc::Right, true) and ends_open?(a),
    FixTree::When(_, _, _) | FixTree::If(_, _, _) => true,
    _ => false,
}
```

`bare_operand?` is `lang::operand` over these precedences:

```fren
expect bare_operand_is_operand(outer: Precedence, inner: Precedence, assoc: Assoc, right?) {
    call o := operand(rank_of(outer), rank_of(inner), assoc, right?)
    expect same: o.bare? iff bare_operand?(outer, inner, assoc, right?)
}
```

## What printing does

The printer writes each operand without parentheses where the grammar
reads it there as itself, and in parentheses where it does not, with two
exceptions, which [Parentheses in fixes](../Lint.md#parentheses-in-fixes)
makes to keep the reading plain: an open-ended form as an operand of an
operator is in parentheses, though the grammar reads a conditional
without them where nothing follows it; and so is an open-ended form
between delimiters, though the grammar reads it without them there.

The grammar reads an operand without parentheses as itself where
`lang::operand` allows it, counting a conditional as an atom, unless it
ends open and something follows it: a left operand is followed by its
operator, and a `when`'s condition by its `,`. A receiver must be an atom
that can be one and does not end open, and anything can be written
between delimiters or keywords:

```fren
pub fn grammar_precedence(t: FixTree): Precedence := if t is FixTree::If(_, _, _) then Precedence::Atom else precedence_of(t)

pub fn reads_bare?(t: FixTree, place: Place) := match place {
    Place::Operand(outer, assoc, right?, followed?) =>
        bare_operand?(outer, grammar_precedence(t), assoc, right?) and not ((followed? or not right?) and ends_open?(t)),
    Place::Receiver => grammar_precedence(t) = Precedence::Atom and receivable?(t) and not ends_open?(t),
    Place::Delimited | Place::Branch => true,
}

-- The two exceptions: an open-ended form as an operand, or between delimiters.
pub fn kept_for_reading?(t: FixTree, place: Place) := match place {
    Place::Operand(_, _, _, _) => precedence_of(t) = Precedence::Open,
    Place::Delimited => precedence_of(t) = Precedence::Open or ends_open?(t),
    _ => false,
}

-- Its own checks are by testing: the solver does not unfold the recursive
-- `ends_open?`. That the printer meets it is checked by the solver below.
set_option fren.evidence "random" in
pub proc parenthesization(operand: FixTree, place: Place): (parens?) {
    ensure reads_back: unless parens?, reads_bare?(operand, place)
    ensure all_needed: when parens?, not reads_bare?(operand, place) or kept_for_reading?(operand, place)
}
```

So the printed text reads back as the tree, and no pair of parentheses
that the printer adds can be removed without changing what it reads as,
but those of the two exceptions. `reads_bare?` is a model of the grammar,
not the parser itself, so the printer's tests check `lint::parenthesization`
against the parser of the `fren` command: they print random trees, read
each back, and remove each pair of parentheses in turn, which must change
the reading unless the pair is one of the exceptions.

## How the printer writes a tree

`lint::print` states how the printer writes a tree, for the operators and
the forms that take an operand in a place of their own. An operand is in
parentheses where `bare_in?` says it cannot do without them in its place:

```fren
pub fn bare?(t: FixTree, outer: Precedence, assoc: Assoc, right?, followed?) :=
    bare_operand?(outer, precedence_of(t), assoc, right?) and not ((followed? or not right?) and ends_open?(t))

pub fn bare_in?(t: FixTree, place: Place) := match place {
    Place::Operand(outer, assoc, right?, followed?) => bare?(t, outer, assoc, right?, followed?),
    Place::Receiver => bare?(t, Precedence::Atom, Assoc::Left, false, true) and receivable?(t),
    Place::Delimited => bare?(t, Precedence::Open, Assoc::NonAssoc, false, true),
    Place::Branch => true,
}

pub proc print_parens(operand: FixTree, place: Place): (det parens?) {
    out parens? := not bare_in?(operand, place)
}

set_option fren.lint.undecidable "allow" in
expect print_parens_refines(operand: FixTree, place: Place) {
    call concrete := print_parens(operand, place)
    refines concrete parenthesization(operand, place)
}
```

The text of a tree is its operands' texts, each in parentheses where it
is not bare in its place, as `bare_in?` says, between its operator's
lexemes. A negation of a text that
starts with `-` has a space after its `-`, which would otherwise start a
comment:

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
    FixTree::Not(a) => "not " ++ enclosed(printed(a), bare?(a, Precedence::Not, Assoc::Right, true, false)),
    FixTree::Neg(a) => negated(enclosed(printed(a), bare?(a, Precedence::Negative, Assoc::Right, true, false))),
    FixTree::When(negated?, c, d) =>
        (if negated? then "unless " else "when ")
        ++ enclosed(printed(c), bare?(c, Precedence::Open, Assoc::NonAssoc, false, true))
        ++ ", " ++ enclosed(printed(d), bare?(d, Precedence::Open, Assoc::Right, true, false)),
    FixTree::If(c, a, b) => "if " ++ printed(c) ++ " then " ++ printed(a) ++ " else " ++ printed(b),
    FixTree::Test(e, p) =>
        enclosed(printed(e), bare?(e, Precedence::Comparison, Assoc::NonAssoc, false, true)) ++ " is " ++ p,
    FixTree::Field(e, x) => enclosed(printed(e), bare?(e, Precedence::Atom, Assoc::Left, false, true) and receivable?(e)) ++ "." ++ x,
}
```

`lint::print` gives a tree's text, its precedence, whether it ends open,
and whether it can be a receiver, which decide how a tree that has it as an
operand writes it. Its expectations are checked by testing, `random`, as
the solver does not unfold a recursive function that builds a `String`:

```fren
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
pub proc print(tree: FixTree): (det text: String, det precedence: Precedence, det open?, det receiver?) {
    out text := printed(tree)
    out precedence := precedence_of(tree)
    out open? := ends_open?(tree)
    out receiver? := receivable?(tree)

    expect looser_right: when tree = FixTree::Bin(BinOp::And, atom("a"), FixTree::Bin(BinOp::Or, atom("b"), atom("c"))),
        text = "a and (b or c)"
    expect left_associative: when tree = FixTree::Bin(BinOp::Minus, FixTree::Bin(BinOp::Minus, atom("a"), atom("b")), atom("c")),
        text = "a - b - c"
    expect right_kept: when tree = FixTree::Bin(BinOp::Minus, atom("a"), FixTree::Bin(BinOp::Minus, atom("b"), atom("c"))),
        text = "a - (b - c)"
    expect non_associative: when tree = FixTree::Bin(BinOp::Eq, FixTree::Bin(BinOp::Eq, atom("a"), atom("b")), atom("c")),
        text = "(a = b) = c"
    expect open_last: when tree = FixTree::Bin(BinOp::And, atom("a"), FixTree::Written("x + if p? then 1 else 2", Precedence::Sum, true, true)),
        text = "a and x + if p? then 1 else 2" and open?
    expect open_followed: when tree = FixTree::Bin(BinOp::And, FixTree::Written("x + if p? then 1 else 2", Precedence::Sum, true, true), atom("a")),
        text = "(x + if p? then 1 else 2) and a" and not open?
    expect conditional_operand: when tree = FixTree::Bin(BinOp::And, atom("a"), FixTree::If(atom("p?"), atom("q?"), atom("r?"))),
        text = "a and (if p? then q? else r?)"
    expect test_scrutinee: when tree = FixTree::Not(FixTree::Test(FixTree::Written("a or b", Precedence::Or, false, true), "E::A | E::B")),
        text = "not (a or b) is E::A | E::B"
    expect double_negation: when tree = FixTree::Neg(FixTree::Neg(atom("x"))), text = "- -x"
    expect receiver: when tree = FixTree::Field(FixTree::Written("a + b", Precedence::Sum, false, true), "abs"), text = "(a + b).abs"
    expect variant_receiver: when tree = FixTree::Field(FixTree::Written("E::A", Precedence::Atom, false, false), "min"),
        text = "(E::A).min"
    expect predicate_receiver: when tree = FixTree::Field(FixTree::Field(atom("x"), "empty?"), "len"), text = "(x.empty?).len"
}
```

The printer writes the other forms of its trees in the same way: the
operands of a chained comparison as a comparison's, and a receiver, an
argument, an element and an index as [Parentheses in
fixes](../Lint.md#parentheses-in-fixes) says. Its tests check them against
`lint::parenthesization`.

```fren
#fren_check parenthesization
#fren_check print_parens
#fren_check print_parens_refines
#fren_check print
#fren_check bare_operand_is_operand
```
