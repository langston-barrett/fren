# Definedness and verification

Typing does not make an expression defined: `n div d` is well typed whatever
the value of `d`. Verification is the part of the static semantics that
proves every partial operation within its domain and every asserted fact
true, at the place where it is written. This chapter defines the
obligations that a typed Core expression gives rise to, the hypotheses under
which each must be proved, what it means for an obligation to be valid, and
what a solver's answer establishes. It builds on the typed Core of
[Core typing](Types.md), on the operator domains of the
[static semantics](StaticSemantics.md), on the values of the
[denotational semantics](DenotationalSemantics.md) and on the table
evaluator of the [dynamic semantics](DynamicSemantics.md). The static
semantics states, as judgments, the definedness and contracts that this
chapter states as obligations.

## Overview

Verification is declarative. An expression's obligations are determined by
its written form alone: no evaluation order is observable, and an obligation
exists whether or not some execution would reach its operation.

| Judgment | Meaning | Fren |
| --- | --- | --- |
| `l ⇝ C` | one layer l, its children's conditions given, has condition C | `generate` |
| `t ⇝ C` | the root of table t has condition C | `conditions`, `root_condition` |
| `Φ ⊢ C ∋ Φ' ⊢ g` | under hypotheses Φ, C requires goal g under Φ' | `collect` |
| `d ∋ Φ ⊢ g` | declaration d has the obligation, of its body or of a member | `declared_obligations` |
| `P; t; ρ ⊨ Φ ⊢ g` | in program P, the assignment ρ satisfies the obligation of table t | `satisfied?` |
| `P; t; ρ ⊨ C` | the assignment ρ satisfies the condition | `condition_holds?` |
| `Σ; P; t ⊨ Φ ⊢ g` | the obligation is valid: every assignment of its goal's context satisfies it | `valid?` |

r[verification.overview.laws]
In outline, verification is a function from a typed expression to a finite
sequence of obligations, and a semantic relation that says which
obligations are valid:

```text
  obligations : Table × Hyps → Obligation*
  satisfied?  : Program × Table × Assignment × Obligation → Bool
  valid?      : Symb × Program × Table × Obligation → Bool
  sound?      : Symb × Program × Table × Obligation × {Proved, Refuted(ρ), Unknown} → Bool

  valid?(Σ, P, t, o)               iff  satisfied?(P, t, ρ, o) for every assignment ρ of o
  sound?(Σ, P, t, o, Proved)       iff  valid?(Σ, P, t, o)
  sound?(Σ, P, t, o, Refuted(ρ))   iff  ρ is an assignment of o and not satisfied?(P, t, ρ, o)
  sound?(Σ, P, t, o, Unknown)      always
```

Generating obligations is decidable: it is a structural function of the
table, and reads neither contexts nor types
([context independence](#r-verification.generation.context-independent)).
A condition and its flattened obligations have the same meaning at every
assignment ([flattening](#r-verification.obligation.flattening)).
Satisfaction at one assignment is computed by the
[table evaluator](DynamicSemantics.md#the-table-evaluator). Validity quantifies over every
assignment to the locals in scope of a goal; a solver is a sound and
incomplete procedure for it
([the interface](#r-verification.validity.interface)), and its `Unknown`
establishes nothing ([verdicts](#r-verification.verdict.discharge)).
Soundness for the dynamic semantics is
[open](#r-verification.soundness).

## Goals, hypotheses and conditions

r[verification.object.goal] spec::verification::Goal
A *goal* is a fact to prove about the rows of a
[derivation table](Types.md#derivations). `NonZero(r)` states that row r,
a divisor, is not zero. `Defined(r)` states that the arguments of the call
at row r are within its callee's domain. `Asserted(r)` states that the
Boolean row r is true.

```fren
pub mod spec
pub mod spec::verification

use spec::denotation::{Value, value_type, value_valid?}

use spec::dynamics::{eval, typed, value_at, values}

use spec::statics::integer_domain?

use spec::names::{
    ArmF,
    CoreF,
    Ctx,
    Form,
    ItemId,
    ItemKind,
    LIGHT,
    LIGHT_GREEN,
    LIGHT_RED,
    Symb,
    Ty,
    entry,
    four,
    length,
    lookup,
    one,
    three,
    two,
}

use spec::surface::{BinaryOp, Snoc, UnaryOp}

use spec::types::{Arm, Decl, F, Row, SYMB, derivation?, rows_valid?, weaken}

use spec::surface::Snoc::{Empty, Extend}

pub enum Goal { NonZero(Int), Defined(Int), Asserted(Int) }
```

r[verification.object.fact] spec::verification::{Fact, Hyps}
A *hypothesis* is a fact that the written form supplies to the goals
beneath it. `Holds(r)` and `Fails(r)` state that the Boolean row r is true
and false. `Is(r, c)` states that row r is the constructor c. `Bound(r)`
states that the newest local in scope is the value of row r. Hypotheses
form a snoc sequence Φ, outermost first.

```fren
pub enum Fact { Holds(Int), Fails(Int), Is(Int, ItemId), Bound(Int) }

pub type Hyps := Snoc<Fact>
```

r[verification.object.condition] spec::verification::Condition
A *condition* is the structured requirement of an expression. `Trivial`
requires nothing and `Check(g)` requires g. `Both(C, D)` requires C and D in
the same hypotheses. `Branch(r, C, D)` requires C where row r holds and D
where it fails. `Case(r, c, C)` requires C where row r is the constructor c.
`Bind(r, C)` requires C in the scope of a local bound to row r.

```fren
pub enum Condition {
    Trivial,
    Check(Goal),
    Both(Condition, Condition),
    Branch(Int, Condition, Condition),
    Case(Int, ItemId, Condition),
    Bind(Int, Condition),
}
```

r[verification.object.obligation] spec::verification::Obligation
An *obligation* `Φ ⊢ g` is a goal with the hypotheses under which it must be
proved.

```fren
pub struct Obligation { hyps: Hyps, goal: Goal }
```

## Generating conditions

Each rule gives the condition of one layer from the conditions of its
children. No rule has a premise.

r[verification.generate.leaf]
A literal, a local and a constructor require nothing: `l ⇝ Trivial`.

r[verification.generate.unary]
A unary operator requires its operand's condition and nothing of its own:
`- e ⇝ Ce` and `not e ⇝ Ce`.

r[verification.generate.operator] spec::verification::{partial?, operator_condition}
An operator requires its operands' conditions, all in the incoming
hypotheses. This holds for `and`, `or` and `iff` as for every other
operator: no operand guards another. Division and remainder, the partial
operators, also require a nonzero divisor.

```text
  op total                          op ∈ {div, %}
  ----------------------------      --------------------------------------------
  l op r ⇝ Both(Cl, Cr)             l op r ⇝ Both(Both(Cl, Cr), Check(NonZero(r)))
```

```fren
pub fn partial?(op: BinaryOp) := op in {BinaryOp::Div, BinaryOp::Rem}

pub fn operator_condition(
    op: BinaryOp,
    left: Condition,
    right: Condition,
    divisor: Int
): Condition :=
    if partial?(op) then
    Condition::Both(
        Condition::Both(left, right),
        Condition::Check(Goal::NonZero(divisor))
    )
    else
    Condition::Both(left, right)
```

r[verification.generate.call] spec::verification::call_condition
A call at row r requires its arguments' conditions and that the arguments
are within the callee's domain: `f(es) ⇝ Both(Cs, Check(Defined(r)))`. The
callee's [domain](#r-verification.assignment.domain) is its `require`
members. A call requires nothing of the callee's body, whose obligations
belong to [its declaration](#r-verification.member.obligations).

```fren
pub fn call_condition(arguments: Condition, pos: Int): Condition :=
    Condition::Both(arguments, Condition::Check(Goal::Defined(pos)))
```

r[verification.generate.let] spec::verification::let_condition
A let requires its value's condition in the incoming hypotheses, whether or
not its body mentions the local, and its body's condition in the scope of
the binding: `let x := v in b ⇝ Both(Cv, Bind(v, Cb))`.

```fren
pub fn let_condition(value: Condition, bound: Int, body: Condition): Condition :=
    Condition::Both(value, Condition::Bind(bound, body))
```

r[verification.generate.if] spec::verification::if_condition
A conditional requires its condition's condition in the incoming
hypotheses, and each branch's under the guard that selects it:
`if c then t else e ⇝ Both(Cc, Branch(c, Ct, Ce))`.

```fren
pub fn if_condition(condition: Condition, guard: Int, yes: Condition, no: Condition): Condition :=
    Condition::Both(condition, Condition::Branch(guard, yes, no))
```

r[verification.generate.match] spec::verification::{arm_condition, match_condition}
A match requires its scrutinee's condition in the incoming hypotheses, and
each arm's body under the hypothesis that the scrutinee is that arm's
constructor: `match s { c ⇒ b, … } ⇝ Both(Cs, Both(…, Case(s, c, Cb)))`.

```fren
pub fn arm_condition(
    earlier: Condition,
    scrutinee: Int,
    constructor: ItemId,
    body: Condition
): Condition := Condition::Both(earlier, Condition::Case(scrutinee, constructor, body))

pub fn match_condition(scrutinee: Condition, arms: Condition): Condition :=
    Condition::Both(scrutinee, arms)
```

r[verification.generate.layer] spec::verification::{condition_at, arguments_condition, arms_condition, generate}
`generate` applies the rule of a layer's form. A layer's children are the
levels of earlier rows; their conditions are read from the conditions
already generated for those rows. A level that names no earlier row
contributes `Trivial`.

```fren
pub fn condition_at(prior: Snoc<Condition>, level: Int): Condition := match lookup(prior, level) {
    Some(condition) => condition,
    None => Condition::Trivial,
}

pub fn arguments_condition(prior: Snoc<Condition>, args: Snoc<Int>): Condition := match args {
    Empty => Condition::Trivial,
    Extend(earlier, arg) => Condition::Both(
        arguments_condition(prior, earlier),
        condition_at(prior, arg)
    ),
}

pub fn arms_condition(prior: Snoc<Condition>, scrutinee: Int, arms: Snoc<Arm>): Condition :=
    match arms {
        Empty => Condition::Trivial,
        Extend(earlier, arm) => arm_condition(
            arms_condition(prior, scrutinee, earlier),
            scrutinee,
            arm.constructor,
            condition_at(prior, arm.body)
        ),
    }

pub fn generate(prior: Snoc<Condition>, pos: Int, form: Form): Condition := match form {
    CoreF::Unary(_, operand) => condition_at(prior, operand),
    CoreF::Binary(op, left, right) => operator_condition(
        op,
        condition_at(prior, left),
        condition_at(prior, right),
        right
    ),
    CoreF::Call(_, args) => call_condition(arguments_condition(prior, args), pos),
    CoreF::Let(_, value, body) =>
        let_condition(condition_at(prior, value), value, condition_at(prior, body)),
    CoreF::If(condition, yes, no) => if_condition(
        condition_at(prior, condition),
        condition,
        condition_at(prior, yes),
        condition_at(prior, no)
    ),
    CoreF::Match(scrutinee, arms) => match_condition(
        condition_at(prior, scrutinee),
        arms_condition(prior, scrutinee, arms)
    ),
    _ => Condition::Trivial,
}
```

r[verification.generate.table] spec::verification::{conditions, root_condition}
The conditions of a table are generated row by row, oldest first; each
row's own level is the level its `Defined` goal names. The condition of
the expression that the table derives is its root's.

```fren
pub fn conditions(rows: Snoc<Row>): Snoc<Condition> := match rows {
    Empty => Empty,
    Extend(earlier, row) => Extend(
        conditions(earlier),
        generate(conditions(earlier), length(earlier), row.form)
    ),
}

pub fn root_condition(rows: Snoc<Row>): Condition := match conditions(rows) {
    Empty => Condition::Trivial,
    Extend(_, condition) => condition,
}
```

## Obligations

r[verification.obligation.collect] spec::verification::{collect, obligations, obligations_at}
The obligations of a condition under hypotheses Φ are its goals, each with
Φ extended by the hypotheses of the branches, cases and bindings that
enclose it, in written order. A conditional's condition and a let's value
are outside those scopes, so their goals keep the incoming hypotheses.

```text
  Φ ⊢ Check(g) ∋ Φ ⊢ g

  Φ ⊢ C ∋ o    or    Φ ⊢ D ∋ o           Φ, Holds(r) ⊢ C ∋ o    or    Φ, Fails(r) ⊢ D ∋ o
  ---------------------------           --------------------------------------------
  Φ ⊢ Both(C, D) ∋ o                    Φ ⊢ Branch(r, C, D) ∋ o

  Φ, Is(r, c) ⊢ C ∋ o                   Φ, Bound(r) ⊢ C ∋ o
  ---------------------                 --------------------
  Φ ⊢ Case(r, c, C) ∋ o                 Φ ⊢ Bind(r, C) ∋ o
```

```fren
pub fn collect(condition: Condition, hyps: Hyps, found: Snoc<Obligation>): Snoc<Obligation> :=
    match condition {
        Condition::Trivial => found,
        Condition::Check(goal) => Extend(found, Obligation { hyps, goal }),
        Condition::Both(first, second) => collect(second, hyps, collect(first, hyps, found)),
        Condition::Branch(guard, yes, no) => collect(
            no,
            Extend(hyps, Fact::Fails(guard)),
            collect(yes, Extend(hyps, Fact::Holds(guard)), found)
        ),
        Condition::Case(scrutinee, constructor, body) =>
            collect(body, Extend(hyps, Fact::Is(scrutinee, constructor)), found),
        Condition::Bind(value, body) => collect(body, Extend(hyps, Fact::Bound(value)), found),
    }

pub fn obligations(rows: Snoc<Row>, hyps: Hyps): Snoc<Obligation> :=
    collect(root_condition(rows), hyps, Empty)

pub fn obligations_at(
    rows: Snoc<Row>,
    root: Int,
    hyps: Hyps,
    found: Snoc<Obligation>
): Snoc<Obligation> := collect(condition_at(conditions(rows), root), hyps, found)
```

## Members and their keywords

r[verification.keyword.kinds] spec::verification::{Keyword, goal?, assumption?}
A member of a declaration states a Boolean expression under one of four
keywords. `require` states a condition of a function's domain: it is an
assumption where the function is declared, and the `Defined` goal of every
call. `assume` states an axiom. `assert` states a fact, which must be
proved. `expect` states a property to check. `assert` and `expect` members
are goals. These four are the only member keywords.

```fren
pub enum Keyword { Require, Assert, Assume, Expect }

pub fn goal?(keyword: Keyword) := keyword in {Keyword::Assert, Keyword::Expect}

pub fn assumption?(keyword: Keyword) := keyword in {Keyword::Require, Keyword::Assume}
```

r[verification.member.table] spec::verification::{Member, Declared, member_ok?, members_ok?, body_ok?, declared_ok?}
A declaration's members and its body, if it has one, are rows of one
derivation table, all in the context of the declaration's parameters. A
*member* is a keyword and the row of its expression, its *root*. The
table's rows are valid, every member's root is a Boolean row in the
parameter context, and the body's root is a row in that context. The
[declarations of Core typing](Types.md#declarations-and-programs) carry no
keyword; [the tables of a program](#r-verification.program.tables) relates
the two.

```fren
pub struct Member { keyword: Keyword, root: Int }

pub struct Declared {
    item: ItemId,
    params: Ctx,
    rows: Snoc<Row>,
    body: Option<Int>,
    members: Snoc<Member>,
}

pub fn member_ok?(rows: Snoc<Row>, params: Ctx, member: Member) := match lookup(rows, member.root) {
    Some(row) => row.ctx = params and row.ty = Ty::Boolean,
    None => false,
}

pub fn members_ok?(rows: Snoc<Row>, params: Ctx, members: Snoc<Member>) := match members {
    Empty => true,
    Extend(earlier, member) =>
        members_ok?(rows, params, earlier) and member_ok?(rows, params, member),
}

pub fn body_ok?(rows: Snoc<Row>, params: Ctx, body: Option<Int>) := match body {
    Some(root) => match lookup(rows, root) {
        Some(row) => row.ctx = params,
        None => false,
    },
    None => true,
}

pub fn declared_ok?(symb: Symb, decl: Declared) :=
    rows_valid?(symb, decl.rows)
    and members_ok?(decl.rows, decl.params, decl.members)
    and body_ok?(decl.rows, decl.params, decl.body)
```

r[verification.keyword.scope] spec::verification::{uses?, member_hyps, body_hyps}
The hypotheses of a member are members of the same declaration, selected
by keyword and never by position: a member written later applies as one
written earlier does. A goal's hypotheses are all of the declaration's
assumptions. An `expect` also has the declaration's `assert` facts. An
assumption has no hypotheses: its own partial operations must be defined
without the others. An `assert` is not a hypothesis of another `assert`.
No member of another declaration applies. A function body has the
hypotheses of an `assert`: the declaration's `require` and `assume`
members. Each selected member m contributes the hypothesis
`Holds(root of m)`.

```fren
pub fn uses?(member: Keyword, hypothesis: Keyword) :=
    (goal?(member) and assumption?(hypothesis))
    or (member = Keyword::Expect and hypothesis = Keyword::Assert)

pub fn member_hyps(members: Snoc<Member>, keyword: Keyword): Hyps := match members {
    Empty => Empty,
    Extend(earlier, member) =>
        if uses?(keyword, member.keyword) then
        Extend(member_hyps(earlier, keyword), Fact::Holds(member.root))
        else
        member_hyps(earlier, keyword),
}

pub fn body_hyps(members: Snoc<Member>): Hyps := member_hyps(members, Keyword::Assert)
```

r[verification.member.obligations] spec::verification::{stated, member_obligations, members_obligations, body_obligations, declared_obligations}
A member has the obligations of its expression, under the member's
hypotheses. A goal member also has the obligation `Asserted(r)` for its
root r, under the same hypotheses. A body has the obligations of its
expression under the body's hypotheses. A declaration's obligations are
its body's, then each member's, in written order.

```text
  d has body b    Φ = body_hyps(d)    Φ ⊢ Cb ∋ o          m ∈ d    Φ = member_hyps(d, keyword of m)    Φ ⊢ Cm ∋ o
  ----------------------------------------------          ------------------------------------------------------
  d ∋ o                                                   d ∋ o

  m ∈ d    m is an assert or expect with root r    Φ = member_hyps(d, keyword of m)
  ---------------------------------------------------------------------------------
  d ∋ Φ ⊢ Asserted(r)
```

```fren
pub fn stated(hyps: Hyps, member: Member, found: Snoc<Obligation>): Snoc<Obligation> :=
    if goal?(member.keyword) then
    Extend(
        found,
        Obligation {
            hyps,
            goal := Goal::Asserted(member.root),
        }
    )
    else
    found

pub fn member_obligations(
    rows: Snoc<Row>,
    all: Snoc<Member>,
    member: Member,
    found: Snoc<Obligation>
): Snoc<Obligation> := stated(
    member_hyps(all, member.keyword),
    member,
    obligations_at(rows, member.root, member_hyps(all, member.keyword), found)
)

pub fn members_obligations(
    rows: Snoc<Row>,
    all: Snoc<Member>,
    members: Snoc<Member>,
    found: Snoc<Obligation>
): Snoc<Obligation> := match members {
    Empty => found,
    Extend(earlier, member) => member_obligations(
        rows,
        all,
        member,
        members_obligations(rows, all, earlier, found)
    ),
}

pub fn body_obligations(decl: Declared): Snoc<Obligation> := match decl.body {
    Some(root) => obligations_at(decl.rows, root, body_hyps(decl.members), Empty),
    None => Empty,
}

pub fn declared_obligations(decl: Declared): Snoc<Obligation> := members_obligations(
    decl.rows,
    decl.members,
    decl.members,
    body_obligations(decl)
)
```

r[verification.keyword.evidence] spec::verification::implementation_discharges?
An `expect` may be discharged by a check that answers `Proved` or by the
proof of an implementation bound to its declaration. An `assert` is
discharged only by a check that answers `Proved`: no implementation
discharges it. An assumption is never discharged; it is taken as given.

```fren
pub fn implementation_discharges?(keyword: Keyword) := keyword = Keyword::Expect
```

## Satisfaction at an assignment

An *assignment* ρ gives a value to each local level in scope. A *program*
P is a sequence of declarations. Satisfaction reads the value of a row
from the
[table evaluator](DynamicSemantics.md#r-expressions.meaning.evaluation):
`eval(t, r, ρ)`.

r[verification.assignment.fact] spec::verification::{fact_refuted?, some_refuted?}
An assignment *refutes* a hypothesis when the evaluator gives the
hypothesis's row a value that contradicts it. `Holds(r)` is refuted where
row r is false, `Fails(r)` where it is true, and `Is(r, c)` where it is
the value of another constructor. `Bound(r)` is refuted where row r has a
value other than that of the local the let binds, whose level is the
length of row r's context. A hypothesis whose row has no value is not
refuted.

```fren
pub fn fact_refuted?(rows: Snoc<Row>, env: Snoc<Value>, fact: Fact) := match fact {
    Fact::Holds(pos) => eval(rows, pos, env) = Some(Value::Boolean(false)),
    Fact::Fails(pos) => eval(rows, pos, env) = Some(Value::Boolean(true)),
    Fact::Is(pos, constructor) => match eval(rows, pos, env) {
        Some(Value::Nominal(_, item)) => item != constructor,
        _ => false,
    },
    Fact::Bound(value) => match lookup(rows, value) {
        Some(row) => match eval(rows, value, env), lookup(env, length(row.ctx)) {
            Some(bound), Some(assigned) => bound != assigned,
            _, _ => false,
        },
        None => false,
    },
}

pub fn some_refuted?(rows: Snoc<Row>, env: Snoc<Value>, hyps: Hyps) := match hyps {
    Empty => false,
    Extend(earlier, fact) => some_refuted?(rows, env, earlier) or fact_refuted?(rows, env, fact),
}
```

r[verification.assignment.domain] spec::verification::{argument_values, requires_hold?, declaration_of, within_domain?}
A function's *domain* is the set of argument values at which every
`require` member of its declaration evaluates to true, in the assignment
that gives the parameters those values. A `require` member has no
hypotheses, so its value depends on the arguments alone. A callee that the
program does not declare has an empty domain.

```fren
pub fn argument_values(prior: Snoc<Option<Value>>, args: Snoc<Int>): Option<Snoc<Value>> :=
    match args {
        Empty => Some(Empty),
        Extend(earlier, arg) => match argument_values(prior, earlier), value_at(prior, arg) {
            Some(found), Some(value) => Some(Extend(found, value)),
            _, _ => None,
        },
    }

pub fn requires_hold?(rows: Snoc<Row>, members: Snoc<Member>, env: Snoc<Value>) := match members {
    Empty => true,
    Extend(earlier, member) =>
        requires_hold?(rows, earlier, env)
        and (
            member.keyword != Keyword::Require
            or eval(rows, member.root, env) = Some(Value::Boolean(true))
            ),
}

pub fn declaration_of(prog: Snoc<Declared>, item: ItemId): Option<Declared> := match prog {
    Empty => None,
    Extend(earlier, decl) => if decl.item = item then Some(decl) else declaration_of(earlier, item),
}

pub fn within_domain?(prog: Snoc<Declared>, callee: ItemId, arguments: Snoc<Value>) :=
    match declaration_of(prog, callee) {
        Some(decl) => requires_hold?(decl.rows, decl.members, arguments),
        None => false,
    }
```

r[verification.assignment.goal] spec::verification::goal_holds?
`NonZero(r)` holds in an assignment where row r is a nonzero integer, and
`Asserted(r)` where row r is true. `Defined(r)` holds where row r is a
call, every argument has a value, and those values are within the callee's
domain. `NonZero` and `Asserted` do not hold of a row that has no value.
`Defined` does not read the value of its own row, which a call never has:
it does not hold where an argument has no value, or where a `require`
root of the callee has none.

```fren
pub fn goal_holds?(prog: Snoc<Declared>, rows: Snoc<Row>, env: Snoc<Value>, goal: Goal) :=
    match goal {
        Goal::NonZero(pos) => match eval(rows, pos, env) {
            Some(Value::Integer(divisor)) => divisor != 0,
            _ => false,
        },
        Goal::Defined(pos) => match lookup(rows, pos) {
            Some(row) => match row.form {
                CoreF::Call(callee, args) => match argument_values(values(rows, env), args) {
                    Some(arguments) => within_domain?(prog, callee, arguments),
                    None => false,
                },
                _ => false,
            },
            None => false,
        },
        Goal::Asserted(pos) => eval(rows, pos, env) = Some(Value::Boolean(true)),
    }
```

r[verification.assignment.obligation] spec::verification::{satisfied?, all_satisfied?}
An assignment satisfies `Φ ⊢ g` when g holds in it or it refutes some
hypothesis of Φ.

```text
  ρ refutes some fact of Φ           g holds in P, t, ρ
  ------------------------           ------------------
  P; t; ρ ⊨ Φ ⊢ g                    P; t; ρ ⊨ Φ ⊢ g
```

```fren
pub fn satisfied?(
    prog: Snoc<Declared>,
    rows: Snoc<Row>,
    env: Snoc<Value>,
    obligation: Obligation
) :=
    some_refuted?(rows, env, obligation.hyps) or goal_holds?(prog, rows, env, obligation.goal)

pub fn all_satisfied?(
    prog: Snoc<Declared>,
    rows: Snoc<Row>,
    env: Snoc<Value>,
    found: Snoc<Obligation>
) := match found {
    Empty => true,
    Extend(earlier, obligation) =>
        all_satisfied?(prog, rows, env, earlier) and satisfied?(prog, rows, env, obligation),
}
```

r[verification.assignment.condition] spec::verification::condition_holds?
An assignment satisfies a condition by its structure: a branch, a case and
a binding require their bodies except where the assignment refutes their
hypothesis.

```fren
pub fn condition_holds?(
    prog: Snoc<Declared>,
    rows: Snoc<Row>,
    env: Snoc<Value>,
    condition: Condition
) := match condition {
    Condition::Trivial => true,
    Condition::Check(goal) => goal_holds?(prog, rows, env, goal),
    Condition::Both(first, second) =>
        condition_holds?(prog, rows, env, first) and condition_holds?(prog, rows, env, second),
    Condition::Branch(guard, yes, no) =>
        (fact_refuted?(rows, env, Fact::Holds(guard)) or condition_holds?(prog, rows, env, yes))
        and (fact_refuted?(rows, env, Fact::Fails(guard)) or condition_holds?(prog, rows, env, no)),
    Condition::Case(scrutinee, constructor, body) =>
        fact_refuted?(rows, env, Fact::Is(scrutinee, constructor))
        or condition_holds?(prog, rows, env, body),
    Condition::Bind(value, body) =>
        fact_refuted?(rows, env, Fact::Bound(value)) or condition_holds?(prog, rows, env, body),
}
```

## Validity and verdicts

r[verification.validity.assignment] spec::verification::{typed_values?, goal_row, assignment?}
An *assignment of an obligation* `Φ ⊢ g` gives one valid value of the
right type to each local of the context of g's row, and to no other. The
rows that Φ names have contexts that are initial parts of that context,
since a hypothesis comes from a layer that encloses the goal.

```fren
pub fn typed_values?(symb: Symb, ctx: Ctx, env: Snoc<Value>) := match ctx {
    Empty => env = Empty,
    Extend(types, ty) => match env {
        Empty => false,
        Extend(earlier, value) =>
            typed_values?(symb, types, earlier)
            and value_valid?(symb, value)
            and value_type(value) = ty,
    },
}

pub fn goal_row(goal: Goal): Int := match goal {
    Goal::NonZero(pos) => pos,
    Goal::Defined(pos) => pos,
    Goal::Asserted(pos) => pos,
}

pub fn assignment?(symb: Symb, rows: Snoc<Row>, obligation: Obligation, env: Snoc<Value>) :=
    match lookup(rows, goal_row(obligation.goal)) {
        Some(row) => typed_values?(symb, row.ctx, env),
        None => false,
    }
```

r[verification.validity.meaning]
An obligation is *valid* when every assignment of it satisfies it:

```text
  for every ρ:  assignment?(Σ, t, Φ ⊢ g, ρ)  implies  P; t; ρ ⊨ Φ ⊢ g
  -------------------------------------------------------------------
  Σ; P; t ⊨ Φ ⊢ g
```

Validity is the meaning of verification, and does not depend on any
solver. [The interface](#r-verification.validity.interface) states it in
Fren.

r[verification.validity.uncomputed]
A row that depends on a product, a quotient, a remainder or a call has no
value in any assignment, since the
[evaluator](DynamicSemantics.md#r-expressions.meaning.evaluation) computes
none. No `NonZero` or `Asserted` goal of such a row holds, and such a
row refutes no hypothesis. A `Defined` goal of a call row can hold, since
it reads the arguments and the callee's `require` roots; it does not hold
where one of those has no value. So
satisfaction never counts an undefined operation as defined; it also fails
to count a goal as holding, or a hypothesis as refuted, where that depends
on such a row.

r[verification.verdict.discharge] spec::verification::{Verdict, discharged?}
A check of an obligation answers `Proved`, `Refuted(ρ)` or `Unknown`. Only
`Proved` discharges the obligation. `Refuted(ρ)` carries an assignment
that does not satisfy the obligation. `Unknown`, which includes every
timeout and resource limit, proves neither the goal nor its negation: the
obligation stays undischarged, and the expression is not thereby undefined.

```fren
pub enum Verdict { Proved, Refuted(Snoc<Value>), Unknown }

pub fn discharged?(verdict: Verdict) := verdict = Verdict::Proved
```

## Defined programs and their expectations

r[verification.program.tables] spec::verification::{moved_arguments, moved_arms, moved_form, moved, ends_with?, upto, rooted?, has_member?, condition_tabled?, tabled?, all_tabled?, condition_typed?, members_typed?, tables_typed?, represents?}
The tables P *represent* the [declarations of a typed program](Types.md#declarations-and-programs)
when each has the other's bodies. Core typing gives each function body and
each condition a table of its own, and a declaration here has one table
for all of them, so a typed table is found inside a declaration's table
with its rows renumbered. A typed table of n rows is *at root r* of a
declaration's table when rows r + 1 - n to r of the declaration's table
are the typed table's rows in order, each with its references to rows
moved by r + 1 - n, the number of rows before them. Every typed
function has a table for its item, with the parameters of the function's
signature and with a body, at whose root the function's typed table is.
Every typed condition is at the root of a member of some declaration that
has the condition's parameters. Conversely, every declaration's table is
[well formed](#r-verification.member.table), and every member is a typed
condition. The correspondence does not count occurrences: one member may
stand for several equal typed conditions, and several equal members for
one. Core typing's conditions carry no keyword and no owner, so that a
member has the keyword and the declaration that the source gave it is not
stated; this part of the correspondence is open. That every typed program
has tables that represent it, such as its typed tables one after another,
is not stated as a law.

```fren
pub fn moved_arguments(args: Snoc<Int>, offset: Int): Snoc<Int> := match args {
    Empty => Empty,
    Extend(earlier, arg) => Extend(moved_arguments(earlier, offset), arg + offset),
}

pub fn moved_arms(arms: Snoc<Arm>, offset: Int): Snoc<Arm> := match arms {
    Empty => Empty,
    Extend(earlier, arm) => Extend(
        moved_arms(earlier, offset),
        ArmF {
            constructor := arm.constructor,
            body := arm.body + offset,
        }
    ),
}

pub fn moved_form(form: Form, offset: Int): Form := match form {
    CoreF::Unary(op, operand) => CoreF::Unary(op, operand + offset),
    CoreF::Binary(op, left, right) => CoreF::Binary(op, left + offset, right + offset),
    CoreF::Call(item, args) => CoreF::Call(item, moved_arguments(args, offset)),
    CoreF::Let(annotation, value, body) => CoreF::Let(annotation, value + offset, body + offset),
    CoreF::If(condition, then_branch, else_branch) => CoreF::If(
        condition + offset,
        then_branch + offset,
        else_branch + offset
    ),
    CoreF::Match(scrutinee, arms) => CoreF::Match(scrutinee + offset, moved_arms(arms, offset)),
    _ => form,
}

pub fn moved(rows: Snoc<Row>, offset: Int): Snoc<Row> := match rows {
    Empty => Empty,
    Extend(earlier, row) => Extend(
        moved(earlier, offset),
        { row with form := moved_form(row.form, offset) }
    ),
}

pub fn ends_with?(long: Snoc<Row>, short: Snoc<Row>) := match short {
    Empty => true,
    Extend(short_earlier, short_row) => match long {
        Empty => false,
        Extend(long_earlier, long_row) =>
            long_row = short_row and ends_with?(long_earlier, short_earlier),
    },
}

pub fn upto(rows: Snoc<Row>, count: Int): Snoc<Row> := match rows {
    Empty => Empty,
    Extend(earlier, _) => if length(rows) <= count then rows else upto(earlier, count),
}

pub fn rooted?(root: Int, body: Snoc<Row>, rows: Snoc<Row>) :=
    length(body) <= root + 1
    and root < length(rows)
    and ends_with?(upto(rows, root + 1), moved(body, root + 1 - length(body)))

pub fn has_member?(members: Snoc<Member>, body: Snoc<Row>, rows: Snoc<Row>) := match members {
    Empty => false,
    Extend(earlier, member) => has_member?(earlier, body, rows) or rooted?(member.root, body, rows),
}

pub fn condition_tabled?(prog: Snoc<Declared>, params: Ctx, body: Snoc<Row>) := match prog {
    Empty => false,
    Extend(earlier, found) =>
        condition_tabled?(earlier, params, body)
        or (found.params = params and has_member?(found.members, body, found.rows)),
}

pub fn tabled?(symb: Symb, prog: Snoc<Declared>, decl: Decl) := match decl {
    Decl::Function(item, body) => match declaration_of(prog, item) {
        Some(found) =>
            match found.body {
                Some(root) => rooted?(root, body, found.rows),
                None => false,
            }
            and match entry(symb, item) {
                Some(ItemKind::Function(sig)) => sig.params = found.params,
                _ => false,
            },
        None => false,
    },
    Decl::Condition(params, body) => condition_tabled?(prog, params, body),
}

pub fn all_tabled?(symb: Symb, prog: Snoc<Declared>, decls: Snoc<Decl>) := match decls {
    Empty => true,
    Extend(earlier, decl) => all_tabled?(symb, prog, earlier) and tabled?(symb, prog, decl),
}

pub fn condition_typed?(decls: Snoc<Decl>, params: Ctx, rows: Snoc<Row>, root: Int) := match decls {
    Empty => false,
    Extend(earlier, decl) =>
        condition_typed?(earlier, params, rows, root)
        or match decl {
            Decl::Condition(ctx, body) => ctx = params and rooted?(root, body, rows),
            Decl::Function(_, _) => false,
        },
}

pub fn members_typed?(decls: Snoc<Decl>, params: Ctx, rows: Snoc<Row>, members: Snoc<Member>) :=
    match members {
        Empty => true,
        Extend(earlier, member) =>
            members_typed?(decls, params, rows, earlier)
            and condition_typed?(decls, params, rows, member.root),
    }

pub fn tables_typed?(symb: Symb, decls: Snoc<Decl>, prog: Snoc<Declared>) := match prog {
    Empty => true,
    Extend(earlier, found) =>
        tables_typed?(symb, decls, earlier)
        and declared_ok?(symb, found)
        and members_typed?(decls, found.params, found.rows, found.members),
}

pub fn represents?(symb: Symb, decls: Snoc<Decl>, prog: Snoc<Declared>) :=
    all_tabled?(symb, prog, decls) and tables_typed?(symb, decls, prog)
```

r[verification.program.defined]
A program with tables P is *defined* when five conditions hold. It is
[well typed](Types.md#declarations-and-programs). P
[represents](#r-verification.program.tables) its declarations. Every match in it has
[distinct arms](StaticSemantics.md#r-statics.match.distinct) and covers
its scrutinee's constructors; both are conditions separate from typing
([Core typing](Types.md#r-types.judgment.coverage-separate)), and this
chapter does not yet state either in Fren. No function in it calls itself, directly or through others
([Core typing](Types.md#r-types.program.nonrecursive)). Every
[obligation of every declaration](#r-verification.member.obligations) is
valid, except the obligations of an `expect` member: its `Asserted`
obligation and every obligation of its expression, such as a divisor's
or a callee's `require`. An `expect` is
[outside the static semantics](StaticSemantics.md#r-statics.declaration.defined),
so neither its truth nor the definedness of its expression is a
condition of a defined program. The
keyword of each member is the one that P states, which nothing here ties
to the source. The conditions cover a function that nothing calls. Coverage and the absence
of recursion yield no obligations. The absence of recursion is not the
[termination check](StaticSemantics.md#r-statics.termination) of the
static semantics, and neither includes the other. It is narrower in that
the check admits structural recursion. It is wider in that it reads the
calls in bodies only: the
[call order](StaticSemantics.md#r-statics.call-order.relation) of the
static semantics also reads the functions that a `require`, `assume`
or `assert` member mentions, so a defined program may have a
recursive group there, which the
[correspondence](StaticSemantics.md#r-statics.property.tables) and
[soundness](#r-verification.soundness) exclude by a condition of their
own. This chapter's definition does not check that condition. The
[dynamic semantics](DynamicSemantics.md#r-dynamics.error.kinds) gives an
error to an operation outside its domain, and
[soundness](#r-verification.soundness) states where an evaluation in a
defined program reaches none.

r[verification.program.verified]
A defined program *meets its expectations* when every obligation of
every `expect` member is valid too: the `Asserted` obligation and the
obligations of the member's expression. Which programs are
*verified* is defined by the
[static semantics](StaticSemantics.md#r-statics.program.verified), and
neither the truth of an expectation nor the definedness of its
expression is part of it: an `expect` is a hypothesis of nothing.

What is known of an expectation is a report of tooling, read through the
[denotations](DenotationalSemantics.md#r-denotation.truth). A check
answers a
[verdict](#r-verification.verdict.discharge) for each obligation of the
`expect` member, and the member is reported in one of three ways. Where
its expression or one of its hypotheses mentions a function that
[has no denotation](DenotationalSemantics.md#r-denotation.domain), it is
*not established*, whatever the checks of its obligations answer: the
expectation has no truth value to report, and the report names the
function. A function has no denotation where its declaration, or that of
a function it depends on, is not verified, has opted out of the
termination check or has a false assumption. Where all those functions
have denotations, the member is *met* when every one of its obligations
is discharged. A `Refuted(ρ)` does not by itself make it refuted. The
verdict says that ρ does not
[satisfy](#r-verification.assignment.obligation) the obligation in this
chapter's sense, and the evaluator
[gives no value](#r-verification.validity.uncomputed) to a row that
depends on a product, a quotient, a remainder or a call. So a goal may
fail to hold at ρ because its row is uncomputed, and a hypothesis may be
unrefuted at ρ because its row is: where `g()` is verified with the body
`0`, the member `expect g() = 0` is true, its `Asserted` goal holds at no
assignment, and a sound check may answer `Refuted(ρ)`. The member is
*refuted* only when the refutation is computed: at ρ the evaluator gives
every hypothesis's row the value that the hypothesis states, and it
gives the goal a value that contradicts it, which is `false` for the
row of an `Asserted` goal, zero for the divisor of a `NonZero` goal, and
`false` for a `require` root that a `Defined` goal reads. A row that has
a value depends on no uncomputed operation, and that value is the row's
denotation at ρ, so ρ then makes the hypotheses true and the expectation
false or without a value. The report names the obligation, which tells
the two apart. A `Refuted(ρ)` that is not computed is a candidate
counterexample and no proof that the expectation is false: the member is
not established, and the report gives ρ and the rows that have no value.
With an obligation left `Unknown` and none refuted by a computed
refutation, the member is again
not established. None of the three reports makes a declaration
undefined or unverified, and none changes a verdict of another member.

r[verification.program.assumptions]
Both notions are relative to assumptions, each within its own
declaration: an `assume` member is a hypothesis of the obligations of the
declaration that states it, and of no other declaration's. A caller proves a
callee's `require` members and nothing else, so an `assume` member that is
false at some assignment makes the goals that use it hold vacuously there.
Assumptions that contradict each other are not an error: every goal that
uses them is valid.

## Properties

A procedure below states a law. The chapter's wrapper proves it in Lean by
an `impl`, or it is open and marked `trusted` with the reason; `fren trace`
reports which. Each procedure's own checks are set to random testing, and
that testing is not claimed as evidence.

r[verification.generation.function]
Generation is a function: a table has exactly one sequence of conditions,
one for each row, and a condition under given hypotheses has exactly one
sequence of obligations. `conditions` and `collect` are total and
structurally recursive, so generating obligations is decidable. Validity
is not decidable.

r[verification.generation.complete] spec::verification::{requires?, argument?, arm_body?, child?, complete::{divisor, call, inherited}}
Generation omits no partial operation. The condition of a row with a
partial operator requires that its divisor is not zero, the condition of a
call row requires that the call is defined, and a row's condition requires
every goal that an earlier child's condition requires. So the root's
condition requires a goal for every division, remainder and call that the
expression contains. That each goal occurs once for each written path to
it, with exactly the hypotheses of the enclosing branches, cases and
bindings, is stated by the [collecting rules](#r-verification.obligation.collect)
and is not a checked property.

```fren
pub fn requires?(condition: Condition, goal: Goal) := match condition {
    Condition::Trivial => false,
    Condition::Check(found) => found = goal,
    Condition::Both(first, second) => requires?(first, goal) or requires?(second, goal),
    Condition::Branch(_, yes, no) => requires?(yes, goal) or requires?(no, goal),
    Condition::Case(_, _, body) => requires?(body, goal),
    Condition::Bind(_, body) => requires?(body, goal),
}

pub fn argument?(args: Snoc<Int>, pos: Int) := match args {
    Empty => false,
    Extend(earlier, arg) => arg = pos or argument?(earlier, pos),
}

pub fn arm_body?(arms: Snoc<Arm>, pos: Int) := match arms {
    Empty => false,
    Extend(earlier, arm) => arm.body = pos or arm_body?(earlier, pos),
}

pub fn child?(form: Form, pos: Int) := match form {
    CoreF::Unary(_, operand) => operand = pos,
    CoreF::Binary(_, left, right) => left = pos or right = pos,
    CoreF::Call(_, args) => argument?(args, pos),
    CoreF::Let(_, value, body) => value = pos or body = pos,
    CoreF::If(condition, yes, no) => condition = pos or yes = pos or no = pos,
    CoreF::Match(scrutinee, arms) => scrutinee = pos or arm_body?(arms, pos),
    _ => false,
}

set_option fren.evidence "random" in
pub proc complete(
    rows: Snoc<Row>,
    pos: Int,
    row: Row,
    op: BinaryOp,
    left: Int,
    right: Int,
    callee: ItemId,
    args: Snoc<Int>,
    child: Int,
    goal: Goal,
): (holds?) {
    ensure output: holds?
    ensure divisor: when lookup(rows, pos) = Some(row)
        and row.form = CoreF::Binary(op, left, right)
        and partial?(op),
        requires?(condition_at(conditions(rows), pos), Goal::NonZero(right))
    ensure call: when lookup(rows, pos) = Some(row) and row.form = CoreF::Call(callee, args),
        requires?(condition_at(conditions(rows), pos), Goal::Defined(pos))
    ensure inherited: when lookup(rows, pos) = Some(row)
        and child?(row.form, child)
        and 0 <= child < pos
        and requires?(condition_at(conditions(rows), child), goal),
        requires?(condition_at(conditions(rows), pos), goal)
}

trusted complete: "open: needs that a row's condition in a table is generated from the conditions of the rows before it, which is not yet proved"
```

r[verification.generation.strict] spec::verification::strictness::{right_required, left_required, unused_value}
No operand guards another, and no value is exempt for being unused: an
assignment that satisfies the condition of `l op r` satisfies the
conditions of both operands, for every operator, and an assignment that
satisfies the condition of a let satisfies its value's.

```fren
set_option fren.evidence "random" in
pub proc strictness(
    prog: Snoc<Declared>,
    rows: Snoc<Row>,
    env: Snoc<Value>,
    op: BinaryOp,
    left: Condition,
    right: Condition,
    row: Int,
): (holds?) {
    ensure output: holds?
    ensure right_required: when condition_holds?(
        prog,
        rows,
        env,
        operator_condition(op, left, right, row)
    ),
        condition_holds?(prog, rows, env, right)
    ensure left_required: when condition_holds?(
        prog,
        rows,
        env,
        operator_condition(op, left, right, row)
    ),
        condition_holds?(prog, rows, env, left)
    ensure unused_value: when condition_holds?(prog, rows, env, let_condition(left, row, right)),
        condition_holds?(prog, rows, env, left)
}
```

r[verification.generation.guarded] spec::verification::guards::{untaken, taken, undetermined}
A branch's condition is required only under its guard. Where the guard is
false, a conditional's condition holds whatever the `then` branch
requires. Where it is true, the `then` branch's condition is required.
Where the guard has no value, both branches' conditions are required.

```fren
set_option fren.evidence "random" in
pub proc guards(
    prog: Snoc<Declared>,
    rows: Snoc<Row>,
    env: Snoc<Value>,
    condition: Condition,
    guard: Int,
    yes: Condition,
    no: Condition,
): (holds?) {
    ensure output: holds?
    ensure untaken: when fact_refuted?(rows, env, Fact::Holds(guard))
        and condition_holds?(prog, rows, env, condition)
        and condition_holds?(prog, rows, env, no),
        condition_holds?(prog, rows, env, if_condition(condition, guard, yes, no))
    ensure taken: when fact_refuted?(rows, env, Fact::Fails(guard))
        and condition_holds?(prog, rows, env, if_condition(condition, guard, yes, no)),
        condition_holds?(prog, rows, env, yes)
    ensure undetermined: when not fact_refuted?(rows, env, Fact::Holds(guard))
        and not fact_refuted?(rows, env, Fact::Fails(guard))
        and condition_holds?(prog, rows, env, if_condition(condition, guard, yes, no)),
        condition_holds?(prog, rows, env, yes) and condition_holds?(prog, rows, env, no)
}
```

r[verification.generation.divisor] spec::verification::divisor::{sound, complete}
The divisor goal is exactly the [operator's domain](StaticSemantics.md#r-expressions.domain.integer):
in an assignment where the divisor row is the integer d, `NonZero` holds
exactly when `integer_domain?` does for a partial operator.

```fren
set_option fren.evidence "random" in
pub proc divisor(
    prog: Snoc<Declared>,
    rows: Snoc<Row>,
    env: Snoc<Value>,
    op: BinaryOp,
    row: Int,
    d: Int,
): (holds?) {
    ensure output: holds?
    ensure sound: when eval(rows, row, env) = Some(Value::Integer(d))
        and goal_holds?(prog, rows, env, Goal::NonZero(row)),
        integer_domain?(op, d)
    ensure complete: when eval(rows, row, env) = Some(Value::Integer(d))
        and partial?(op)
        and integer_domain?(op, d),
        goal_holds?(prog, rows, env, Goal::NonZero(row))
}
```

r[verification.obligation.hypotheses] spec::verification::hypotheses::{weakening, strengthening, exclusive}
Satisfaction is monotone in the hypotheses. An assignment that satisfies
an obligation satisfies it with one more hypothesis (weakening), and a
hypothesis that the assignment does not refute can be removed
(strengthening). No assignment refutes both `Holds(r)` and `Fails(r)`.

```fren
set_option fren.evidence "random" in
pub proc hypotheses(
    prog: Snoc<Declared>,
    rows: Snoc<Row>,
    env: Snoc<Value>,
    hyps: Hyps,
    fact: Fact,
    goal: Goal,
    row: Int,
): (holds?) {
    ensure output: holds?
    ensure weakening: when satisfied?(prog, rows, env, Obligation { hyps, goal }),
        satisfied?(
            prog,
            rows,
            env,
            Obligation { hyps := Extend(hyps, fact), goal }
        )
    ensure strengthening: when not fact_refuted?(rows, env, fact)
        and satisfied?(
            prog,
            rows,
            env,
            Obligation { hyps := Extend(hyps, fact), goal }
        ),
        satisfied?(prog, rows, env, Obligation { hyps, goal })
    ensure exclusive: not fact_refuted?(rows, env, Fact::Holds(row))
        or not fact_refuted?(rows, env, Fact::Fails(row))
}
```

r[verification.obligation.cut] spec::verification::cut::asserted
A proved fact adds nothing as a hypothesis. An assignment that satisfies
`Φ ⊢ Asserted(r)` and `Φ, Holds(r) ⊢ g` satisfies `Φ ⊢ g`. So where a
declaration's `assert` members are valid, an `expect` that is valid with
their facts as hypotheses is valid without them, one fact at a time: the
rule that an `expect` uses `assert` facts changes what a check may assume,
not which programs meet their expectations.

```fren
set_option fren.evidence "random" in
pub proc cut(
    prog: Snoc<Declared>,
    rows: Snoc<Row>,
    env: Snoc<Value>,
    hyps: Hyps,
    root: Int,
    goal: Goal,
): (holds?) {
    ensure output: holds?
    ensure asserted: when satisfied?(
        prog,
        rows,
        env,
        Obligation { hyps, goal := Goal::Asserted(root) }
    )
        and satisfied?(
            prog,
            rows,
            env,
            Obligation {
                hyps := Extend(hyps, Fact::Holds(root)),
                goal,
            }
        ),
        satisfied?(prog, rows, env, Obligation { hyps, goal })
}
```

r[verification.program.represented] spec::verification::{has_body?, represented::{kept, none}}
Tables that represent a program omit no function body: a typed function
has a table with a body, and no tables at all represent no program that
has a function. So the obligations of a
[defined program](#r-verification.program.defined) include those of every
function body that Core typing typed.

```fren
pub fn has_body?(prog: Snoc<Declared>, item: ItemId) := match declaration_of(prog, item) {
    Some(found) => found.body != None,
    None => false,
}

set_option fren.evidence "random" in
pub proc represented(
    symb: Symb,
    decls: Snoc<Decl>,
    prog: Snoc<Declared>,
    item: ItemId,
    body: Snoc<Row>,
): (holds?) {
    ensure output: holds?
    ensure kept: when represents?(symb, Extend(decls, Decl::Function(item, body)), prog),
        has_body?(prog, item)
    ensure none: not represents?(symb, Extend(decls, Decl::Function(item, body)), Empty)
}
```

r[verification.member.scope] spec::verification::member_scope::{expect_unused, own, assumptions_independent, order}
An `expect` is a hypothesis of nothing: adding one changes no member's
hypotheses. No member is a hypothesis of itself, nor of a member with its
own keyword. An assumption has no hypotheses. Hypotheses do not depend on
the order in which members are written: exchanging the two members
written last does not change whether an assignment refutes one of the
hypotheses.

```fren
set_option fren.evidence "random" in
pub proc member_scope(
    rows: Snoc<Row>,
    env: Snoc<Value>,
    members: Snoc<Member>,
    member: Member,
    other: Member,
    keyword: Keyword,
): (holds?) {
    ensure output: holds?
    ensure expect_unused: when member.keyword = Keyword::Expect,
        member_hyps(Extend(members, member), keyword) = member_hyps(members, keyword)
    ensure own: when member.keyword = keyword,
        member_hyps(Extend(members, member), keyword) = member_hyps(members, keyword)
    ensure assumptions_independent: when assumption?(keyword), member_hyps(members, keyword) = Empty
    ensure order: some_refuted?(
        rows,
        env,
        member_hyps(Extend(Extend(members, member), other), keyword)
    ) iff some_refuted?(
        rows,
        env,
        member_hyps(Extend(Extend(members, other), member), keyword)
    )
}
```

r[verification.obligation.flattening] spec::verification::flattening::exact
Collecting preserves meaning. An assignment satisfies every obligation
collected from C under Φ exactly when it refutes some hypothesis of Φ or
satisfies C: the flat obligations, each with its own hypotheses, say what
the structured condition says.

```fren
set_option fren.evidence "random" in
pub proc flattening(
    prog: Snoc<Declared>,
    rows: Snoc<Row>,
    env: Snoc<Value>,
    condition: Condition,
    hyps: Hyps,
    found: Snoc<Obligation>,
): (holds?) {
    ensure output: holds?
    ensure exact: all_satisfied?(prog, rows, env, collect(condition, hyps, found)) iff (
        all_satisfied?(prog, rows, env, found)
        and (some_refuted?(rows, env, hyps) or condition_holds?(prog, rows, env, condition))
        )
}
```

r[verification.generation.context-independent] spec::verification::context_weakening::unchanged
Generation reads no context and no type. Inserting a type into every row's
context, as [weakening a table](Types.md#r-types.derivation.weakening)
does, leaves every condition unchanged.

```fren
set_option fren.evidence "random" in
pub proc context_weakening(rows: Snoc<Row>, cutoff: Int, extra: Ty): (holds?) {
    ensure output: holds?
    ensure unchanged: conditions(weaken(rows, cutoff, extra)) = conditions(rows)
}
```

r[verification.soundness]
Verification is sound for the denotational semantics, and through it
for the dynamic semantics, under conditions that
this chapter's definedness does not itself give. Let the program be
[defined](#r-verification.program.defined), let no function of it
reach itself in the
[call order](StaticSemantics.md#r-statics.call-order.relation) of the
static semantics, which reads conditions other than expectations as
well as bodies, let each of
its postconditions be `true`, and let none of its declarations have
[opted out](StaticSemantics.md#r-statics.termination.optional) of the
termination check. By the
[correspondence with the static semantics](StaticSemantics.md#r-statics.property.tables)
each of its declarations is then
[verified](StaticSemantics.md#r-statics.program.verified). Let d be one
of them, and let the
`assume` members of every function that d
[depends on](StaticSemantics.md#r-statics.call-order.relation) be
[true](DenotationalSemantics.md#r-denotation.truth), that is, true at
every argument tuple that meets their function's `require` members. Then
every function that d depends on
[has a denotation](DenotationalSemantics.md#r-denotation.domain), and the
body of d and the expression of each member of d other than an `expect`
denote a value at every assignment that makes their
hypotheses true. That is less than every assignment that
[satisfies](#r-verification.assignment.fact) them in this chapter's
sense, which asks only that none be refuted. The evaluation of the
expression there ends in that value by
[adequacy](DynamicSemantics.md#r-dynamics.theorem.adequacy), and a
function that d depends on is
[totally correct](DynamicSemantics.md#r-dynamics.theorem.total-correctness).
The statement is not of an `expect` member: the
obligations of one are no part of a defined program, and a function that
only an `expect` mentions is not one that d depends on. The expression
of an `expect` member denotes a value at the assignments that make its
hypotheses true under two
further premises: every obligation of the member is valid, and every
function that the member mentions has a denotation. The
`assume` members of d itself are among the hypotheses, and those of a
declaration that d does not depend on are not asked to be true. Without
the condition on opting out the statement fails as written: where `g()`
has the body `1` and has opted out and `f()` has the body `g()`, the
program is defined, no assumption is false, and g has no denotation, so
the body of f has none. Without the condition on the call order it fails
too: a defined program has no recursion through bodies, and where `f()`
has the body `0` and the member `assert g() = 0`, and `g()` has the body
`f()`, the two are one recursive group of the static semantics, neither
declaration is verified, and neither function has a denotation. The
[denotational semantics](DenotationalSemantics.md#r-expressions.value.denotation)
states the property. It is open: the evaluator gives no value to a product, a
quotient, a remainder or a call, so the statement cannot yet be written
for the whole Core. The laws above are its local parts: generation omits
no partial operation, the divisor goal is the operator's domain, strict
positions require their operands, guards are the hypotheses of their
branches, and flattening loses nothing.

## Examples

r[verification.examples.obligations] spec::verification::{INTEGERS, BOUND, integer, GUARDED_ROWS, CONJUNCTION_ROWS, UNUSED_ROWS, BOUND_ROWS, SHARED_ROWS, CALL_ROWS, NEGATION_ROWS, MATCH_ROWS, under, example?, worked_examples::{guarded, conjunction, unused, bound, shared, call, negation, matched}}
Each example is an expression, its table and its obligations under no
incoming hypotheses. The first two tables omit their contexts: every row
of the first has the context `·, Int, Int`, and every row of the second
the empty context.

`if d != 0 then n div d else 0`, with n at level 0 and d at level 1, has
the one obligation `Holds(row 2) ⊢ NonZero(row 4)`:

| Row | Layer | Condition |
| --- | --- | --- |
| 0 | `#1` | `Trivial` |
| 1 | `0` | `Trivial` |
| 2 | `row 0 != row 1` | `Both(Trivial, Trivial)` |
| 3 | `#0` | `Trivial` |
| 4 | `#1` | `Trivial` |
| 5 | `row 3 div row 4` | `Both(Both(Trivial, Trivial), Check(NonZero(4)))` |
| 6 | `0` | `Trivial` |
| 7 | `if row 2 then row 5 else row 6` | `Both(C2, Branch(2, C5, C6))` |

In an assignment where d is 0, row 2 is false, `Holds(row 2)` is refuted,
and the obligation is satisfied. Where d is not 0, the goal holds.

`false and (1 div 0 = 0)` has the one obligation `· ⊢ NonZero(row 2)`: the
conjunction supplies no hypothesis. The empty assignment does not satisfy
it, so the expression is rejected although an execution could skip its
right operand.

| Row | Layer | Condition |
| --- | --- | --- |
| 0 | `false` | `Trivial` |
| 1 | `1` | `Trivial` |
| 2 | `0` | `Trivial` |
| 3 | `row 1 div row 2` | `Both(Both(Trivial, Trivial), Check(NonZero(2)))` |
| 4 | `0` | `Trivial` |
| 5 | `row 3 = row 4` | `Both(C3, Trivial)` |
| 6 | `row 0 and row 5` | `Both(Trivial, C5)` |

`let x := 1 div 0 in 0` has the one obligation `· ⊢ NonZero(row 1)`, though
its body ignores x:

| Row | Layer | Context | Condition |
| --- | --- | --- | --- |
| 0 | `1` | `·` | `Trivial` |
| 1 | `0` | `·` | `Trivial` |
| 2 | `row 0 div row 1` | `·` | `Both(Both(Trivial, Trivial), Check(NonZero(1)))` |
| 3 | `0` | `·, Int` | `Trivial` |
| 4 | `let x := row 2 in row 3` | `·` | `Both(C2, Bind(2, Trivial))` |

`let d := 2 in 10 div d` has the one obligation
`Bound(row 0) ⊢ NonZero(row 2)`, where row 2 is the local d, at level 0:

| Row | Layer | Context | Condition |
| --- | --- | --- | --- |
| 0 | `2` | `·` | `Trivial` |
| 1 | `10` | `·, Int` | `Trivial` |
| 2 | `#0` | `·, Int` | `Trivial` |
| 3 | `row 1 div row 2` | `·, Int` | `Both(Both(Trivial, Trivial), Check(NonZero(2)))` |
| 4 | `let d := row 0 in row 3` | `·` | `Both(Trivial, Bind(0, C3))` |

`(let x := 0 in 10 div x) + (let x := 1 in 10 div x)` can share the rows of
its two bodies. It then has two obligations with the same goal,
`Bound(row 0) ⊢ NonZero(row 3)` and `Bound(row 1) ⊢ NonZero(row 3)`:

| Row | Layer | Context | Condition |
| --- | --- | --- | --- |
| 0 | `0` | `·` | `Trivial` |
| 1 | `1` | `·` | `Trivial` |
| 2 | `10` | `·, Int` | `Trivial` |
| 3 | `#0` | `·, Int` | `Trivial` |
| 4 | `row 2 div row 3` | `·, Int` | `Both(Both(Trivial, Trivial), Check(NonZero(3)))` |
| 5 | `let x := row 0 in row 4` | `·` | `Both(Trivial, Bind(0, C4))` |
| 6 | `let x := row 1 in row 4` | `·` | `Both(Trivial, Bind(1, C4))` |
| 7 | `row 5 + row 6` | `·` | `Both(C5, C6)` |

The call `M::f(1)`, at row 1, has the one obligation `· ⊢ Defined(row 1)`.

`-(1 div 0)` has the one obligation `· ⊢ NonZero(row 1)`, which is its
operand's:

| Row | Layer | Condition |
| --- | --- | --- |
| 0 | `1` | `Trivial` |
| 1 | `0` | `Trivial` |
| 2 | `row 0 div row 1` | `Both(Both(Trivial, Trivial), Check(NonZero(1)))` |
| 3 | `- row 2` | `C2` |

`match s { Red ⇒ 1, Green ⇒ 1 div 0 }`, with s of type `M::Light` at level
0, has the one obligation `Is(row 0, Green) ⊢ NonZero(row 2)`. Every row
has the context `·, M::Light`:

| Row | Layer | Condition |
| --- | --- | --- |
| 0 | `#0` | `Trivial` |
| 1 | `1` | `Trivial` |
| 2 | `0` | `Trivial` |
| 3 | `row 1 div row 2` | `Both(Both(Trivial, Trivial), Check(NonZero(2)))` |
| 4 | `match row 0 { Red ⇒ row 1, Green ⇒ row 3 }` | `Both(Trivial, Both(Both(Trivial, Case(0, Red, Trivial)), Case(0, Green, C3)))` |

The procedure `worked_examples` states that each table is a valid
derivation of Core typing, in the program of that chapter's examples, and
has exactly the obligations given.

```fren
pub const INTEGERS: Ctx := two(Ty::Integer, Ty::Integer)
pub const BOUND: Ctx := one(Ty::Integer)

pub fn integer(form: Form): Row := typed(form, INTEGERS, Ty::Integer)

pub const GUARDED_ROWS: Snoc<Row> := Extend(
    Extend(
        Extend(
            Extend(
                four(
                    integer(CoreF::Local(1)),
                    integer(CoreF::IntegerLiteral(0)),
                    typed(CoreF::Binary(BinaryOp::Ne, 0, 1), INTEGERS, Ty::Boolean),
                    integer(CoreF::Local(0))
                ),
                integer(CoreF::Local(1))
            ),
            integer(CoreF::Binary(BinaryOp::Div, 3, 4))
        ),
        integer(CoreF::IntegerLiteral(0))
    ),
    integer(CoreF::If(2, 5, 6))
)

pub const CONJUNCTION_ROWS: Snoc<Row> := Extend(
    Extend(
        Extend(
            four(
                typed(CoreF::BooleanLiteral(false), Empty, Ty::Boolean),
                typed(CoreF::IntegerLiteral(1), Empty, Ty::Integer),
                typed(CoreF::IntegerLiteral(0), Empty, Ty::Integer),
                typed(CoreF::Binary(BinaryOp::Div, 1, 2), Empty, Ty::Integer)
            ),
            typed(CoreF::IntegerLiteral(0), Empty, Ty::Integer)
        ),
        typed(CoreF::Binary(BinaryOp::Eq, 3, 4), Empty, Ty::Boolean)
    ),
    typed(CoreF::Binary(BinaryOp::And, 0, 5), Empty, Ty::Boolean)
)

pub const UNUSED_ROWS: Snoc<Row> := Extend(
    four(
        typed(CoreF::IntegerLiteral(1), Empty, Ty::Integer),
        typed(CoreF::IntegerLiteral(0), Empty, Ty::Integer),
        typed(CoreF::Binary(BinaryOp::Div, 0, 1), Empty, Ty::Integer),
        typed(CoreF::IntegerLiteral(0), BOUND, Ty::Integer)
    ),
    typed(CoreF::Let(None, 2, 3), Empty, Ty::Integer)
)

pub const BOUND_ROWS: Snoc<Row> := Extend(
    four(
        typed(CoreF::IntegerLiteral(2), Empty, Ty::Integer),
        typed(CoreF::IntegerLiteral(10), BOUND, Ty::Integer),
        typed(CoreF::Local(0), BOUND, Ty::Integer),
        typed(CoreF::Binary(BinaryOp::Div, 1, 2), BOUND, Ty::Integer)
    ),
    typed(CoreF::Let(None, 0, 3), Empty, Ty::Integer)
)

pub const SHARED_ROWS: Snoc<Row> := Extend(
    Extend(
        Extend(
            Extend(
                four(
                    typed(CoreF::IntegerLiteral(0), Empty, Ty::Integer),
                    typed(CoreF::IntegerLiteral(1), Empty, Ty::Integer),
                    typed(CoreF::IntegerLiteral(10), BOUND, Ty::Integer),
                    typed(CoreF::Local(0), BOUND, Ty::Integer)
                ),
                typed(CoreF::Binary(BinaryOp::Div, 2, 3), BOUND, Ty::Integer)
            ),
            typed(CoreF::Let(None, 0, 4), Empty, Ty::Integer)
        ),
        typed(CoreF::Let(None, 1, 4), Empty, Ty::Integer)
    ),
    typed(CoreF::Binary(BinaryOp::Add, 5, 6), Empty, Ty::Integer)
)

pub const CALL_ROWS: Snoc<Row> := two(
    typed(CoreF::IntegerLiteral(1), Empty, Ty::Integer),
    typed(CoreF::Call(F, one(0)), Empty, Ty::Integer)
)

pub const NEGATION_ROWS: Snoc<Row> := four(
    typed(CoreF::IntegerLiteral(1), Empty, Ty::Integer),
    typed(CoreF::IntegerLiteral(0), Empty, Ty::Integer),
    typed(CoreF::Binary(BinaryOp::Div, 0, 1), Empty, Ty::Integer),
    typed(CoreF::Unary(UnaryOp::Neg, 2), Empty, Ty::Integer)
)

pub const MATCH_ROWS: Snoc<Row> := Extend(
    four(
        typed(CoreF::Local(0), one(Ty::Nominal(LIGHT)), Ty::Nominal(LIGHT)),
        typed(
            CoreF::IntegerLiteral(1),
            one(Ty::Nominal(LIGHT)),
            Ty::Integer
        ),
        typed(
            CoreF::IntegerLiteral(0),
            one(Ty::Nominal(LIGHT)),
            Ty::Integer
        ),
        typed(
            CoreF::Binary(BinaryOp::Div, 1, 2),
            one(Ty::Nominal(LIGHT)),
            Ty::Integer
        )
    ),
    typed(
        CoreF::Match(
            0,
            two(
                ArmF { constructor := LIGHT_RED, body := 1 },
                ArmF { constructor := LIGHT_GREEN, body := 3 }
            )
        ),
        one(Ty::Nominal(LIGHT)),
        Ty::Integer
    )
)

pub fn under(fact: Fact, goal: Goal): Obligation := Obligation { hyps := one(fact), goal }

pub fn example?(rows: Snoc<Row>, ctx: Ctx, ty: Ty, expected: Snoc<Obligation>) :=
    derivation?(SYMB, rows, ctx, ty) and obligations(rows, Empty) = expected

-- The examples are constant judgments, which the wrapper evaluates.
set_option fren.lint.assertions_on_constants "allow" in
set_option fren.evidence "random" in
pub proc worked_examples(): (holds?) {
    ensure output: holds?
    ensure guarded: example?(
        GUARDED_ROWS,
        INTEGERS,
        Ty::Integer,
        one(under(Fact::Holds(2), Goal::NonZero(4)))
    )
    ensure conjunction: example?(
        CONJUNCTION_ROWS,
        Empty,
        Ty::Boolean,
        one(Obligation { hyps := Empty, goal := Goal::NonZero(2) })
    )
    ensure unused: example?(
        UNUSED_ROWS,
        Empty,
        Ty::Integer,
        one(Obligation { hyps := Empty, goal := Goal::NonZero(1) })
    )
    ensure bound: example?(
        BOUND_ROWS,
        Empty,
        Ty::Integer,
        one(under(Fact::Bound(0), Goal::NonZero(2)))
    )
    ensure shared: example?(
        SHARED_ROWS,
        Empty,
        Ty::Integer,
        two(
            under(Fact::Bound(0), Goal::NonZero(3)),
            under(Fact::Bound(1), Goal::NonZero(3))
        )
    )
    ensure call: example?(
        CALL_ROWS,
        Empty,
        Ty::Integer,
        one(Obligation { hyps := Empty, goal := Goal::Defined(1) })
    )
    ensure negation: example?(
        NEGATION_ROWS,
        Empty,
        Ty::Integer,
        one(Obligation { hyps := Empty, goal := Goal::NonZero(1) })
    )
    ensure matched: example?(
        MATCH_ROWS,
        one(Ty::Nominal(LIGHT)),
        Ty::Integer,
        one(under(Fact::Is(0, LIGHT_GREEN), Goal::NonZero(2)))
    )
}
```

r[verification.examples.assignments] spec::verification::at_assignments::{guarded, unguarded, bound, first, second, arm}
In the assignment of the first example where n is 7 and d is 0, the
guarded obligation is satisfied; the same goal without its hypothesis is
not.

A binding's hypothesis ties its local to its value. The obligation of the
bound example is satisfied where the local is 2, since the divisor is not
zero, and where the local is 0, since the assignment refutes
`Bound(row 0)`. In the shared example the one row of the local serves both
lets. Where the local is 0, the first let's obligation is not satisfied,
so it is not valid. The second let's obligation is satisfied there, since
that assignment refutes `Bound(row 1)`, and where the local is 1: the
first let's zero does not count against it.

The match example's obligation is satisfied where s is `Red`, which
refutes its hypothesis, and not where s is `Green`.

```fren
-- The examples are constant judgments, which the wrapper evaluates.
set_option fren.lint.assertions_on_constants "allow" in
set_option fren.evidence "random" in
pub proc at_assignments(): (holds?) {
    ensure output: holds?
    ensure guarded: satisfied?(
        Empty,
        GUARDED_ROWS,
        two(Value::Integer(7), Value::Integer(0)),
        under(Fact::Holds(2), Goal::NonZero(4))
    )
    ensure unguarded: not satisfied?(
        Empty,
        GUARDED_ROWS,
        two(Value::Integer(7), Value::Integer(0)),
        Obligation { hyps := Empty, goal := Goal::NonZero(4) }
    )
    ensure bound: satisfied?(
        Empty,
        BOUND_ROWS,
        one(Value::Integer(2)),
        under(Fact::Bound(0), Goal::NonZero(2))
    )
        and satisfied?(
            Empty,
            BOUND_ROWS,
            one(Value::Integer(0)),
            under(Fact::Bound(0), Goal::NonZero(2))
        )
    ensure first: not satisfied?(
        Empty,
        SHARED_ROWS,
        one(Value::Integer(0)),
        under(Fact::Bound(0), Goal::NonZero(3))
    )
    ensure second: satisfied?(
        Empty,
        SHARED_ROWS,
        one(Value::Integer(0)),
        under(Fact::Bound(1), Goal::NonZero(3))
    )
        and satisfied?(
            Empty,
            SHARED_ROWS,
            one(Value::Integer(1)),
            under(Fact::Bound(1), Goal::NonZero(3))
        )
    ensure arm: satisfied?(
        Empty,
        MATCH_ROWS,
        one(Value::Nominal(LIGHT, LIGHT_RED)),
        under(Fact::Is(0, LIGHT_GREEN), Goal::NonZero(2))
    )
        and not satisfied?(
            Empty,
            MATCH_ROWS,
            one(Value::Nominal(LIGHT, LIGHT_GREEN)),
            under(Fact::Is(0, LIGHT_GREEN), Goal::NonZero(2))
        )
}
```

r[verification.examples.scopes] spec::verification::{SIBLING_ROWS, scopes::{derived, first, second, refuted}}
A let's row has the value of the let, whatever value its body's row has in
the same assignment. `1 div ((let x := 2 in x) - (let x := 1 in x) - 1)`
shares the row of x between its two lets, and divides by zero:

| Row | Layer | Context | Value in the empty assignment |
| --- | --- | --- | --- |
| 0 | `1` | `·` | 1 |
| 1 | `2` | `·` | 2 |
| 2 | `#0` | `·, Int` | none |
| 3 | `let x := row 1 in row 2` | `·` | 2 |
| 4 | `let x := row 0 in row 2` | `·` | 1 |
| 5 | `row 3 - row 4` | `·` | 1 |
| 6 | `row 5 - row 0` | `·` | 0 |
| 7 | `row 0 div row 6` | `·` | none |

Its one obligation is `· ⊢ NonZero(row 6)`, in the empty context. The two
lets have different values, though they share a body, and the empty
assignment does not satisfy the obligation, so the obligation is not
valid.

```fren
pub const SIBLING_ROWS: Snoc<Row> := Extend(
    Extend(
        Extend(
            Extend(
                four(
                    typed(CoreF::IntegerLiteral(1), Empty, Ty::Integer),
                    typed(CoreF::IntegerLiteral(2), Empty, Ty::Integer),
                    typed(CoreF::Local(0), BOUND, Ty::Integer),
                    typed(CoreF::Let(None, 1, 2), Empty, Ty::Integer)
                ),
                typed(CoreF::Let(None, 0, 2), Empty, Ty::Integer)
            ),
            typed(CoreF::Binary(BinaryOp::Sub, 3, 4), Empty, Ty::Integer)
        ),
        typed(CoreF::Binary(BinaryOp::Sub, 5, 0), Empty, Ty::Integer)
    ),
    typed(CoreF::Binary(BinaryOp::Div, 0, 6), Empty, Ty::Integer)
)

-- The example is a constant judgment, which the wrapper evaluates.
set_option fren.lint.assertions_on_constants "allow" in
set_option fren.evidence "random" in
pub proc scopes(): (holds?) {
    ensure output: holds?
    ensure derived: example?(
        SIBLING_ROWS,
        Empty,
        Ty::Integer,
        one(Obligation { hyps := Empty, goal := Goal::NonZero(6) })
    )
    ensure first: eval(SIBLING_ROWS, 3, Empty) = Some(Value::Integer(2))
    ensure second: eval(SIBLING_ROWS, 4, Empty) = Some(Value::Integer(1))
    ensure refuted: not satisfied?(
        Empty,
        SIBLING_ROWS,
        Empty,
        Obligation { hyps := Empty, goal := Goal::NonZero(6) }
    )
}
```

r[verification.examples.members] spec::verification::{G, DOMAIN_ROWS, declared, REJECTED, ACCEPTED, member_examples::{rejected, refuted, accepted, satisfied}}
A function `g(n, d)` with body `n div d` may not state its domain as
`require d != 0 and n div d > 0`: a conjunction supplies no hypothesis, so
the member has the obligation `· ⊢ NonZero(d)`. Nor may it state the two
members `require d != 0` and `require n div d > 0`, since an assumption
has no hypotheses. The accepted form guards the quotient with a
conditional: `require d != 0` and
`require if d != 0 then n div d > 0 else false`. One table holds the body
and every member's expression; each row has the context `·, Int, Int`,
with n at level 0 and d at level 1:

| Row | Layer |
| --- | --- |
| 0 | `#1` |
| 1 | `0` |
| 2 | `row 0 != row 1` |
| 3 | `#0` |
| 4 | `#1` |
| 5 | `row 3 div row 4` |
| 6 | `row 5 > row 1` |
| 7 | `false` |
| 8 | `if row 2 then row 6 else row 7` |

The rejected declaration has the body row 5 and the members
`require row 2` and `require row 6`. Its obligations are the body's,
`Holds(row 2), Holds(row 6) ⊢ NonZero(row 4)`, and the second member's,
`· ⊢ NonZero(row 4)`, which the assignment of 7 to n and 0 to d does not
satisfy.

The accepted declaration has the body row 5 and the members
`require row 2`, `require row 8` and `assert row 2`. Its obligations are
the body's, `Holds(row 2), Holds(row 8) ⊢ NonZero(row 4)`; the second
member's, `Holds(row 2) ⊢ NonZero(row 4)`, whose hypothesis is the
conditional's guard; and the assert's,
`Holds(row 2), Holds(row 8) ⊢ Asserted(row 2)`. The assignments of 7 and 0
and of 7 and 2 satisfy all three. An `assert` uses no other `assert`, so a
second `assert` here could not use the first as a lemma.

```fren
pub const G: ItemId := ["M", "g"]

pub const DOMAIN_ROWS: Snoc<Row> := Extend(
    Extend(
        Extend(
            Extend(
                Extend(
                    four(
                        integer(CoreF::Local(1)),
                        integer(CoreF::IntegerLiteral(0)),
                        typed(CoreF::Binary(BinaryOp::Ne, 0, 1), INTEGERS, Ty::Boolean),
                        integer(CoreF::Local(0))
                    ),
                    integer(CoreF::Local(1))
                ),
                integer(CoreF::Binary(BinaryOp::Div, 3, 4))
            ),
            typed(CoreF::Binary(BinaryOp::Gt, 5, 1), INTEGERS, Ty::Boolean)
        ),
        typed(CoreF::BooleanLiteral(false), INTEGERS, Ty::Boolean)
    ),
    typed(CoreF::If(2, 6, 7), INTEGERS, Ty::Boolean)
)

pub fn declared(members: Snoc<Member>): Declared := Declared {
    item := G,
    params := INTEGERS,
    rows := DOMAIN_ROWS,
    body := Some(5),
    members,
}

pub const REJECTED: Declared := declared(
    two(
        Member { keyword := Keyword::Require, root := 2 },
        Member { keyword := Keyword::Require, root := 6 }
    )
)

pub const ACCEPTED: Declared := declared(
    three(
        Member { keyword := Keyword::Require, root := 2 },
        Member { keyword := Keyword::Require, root := 8 },
        Member { keyword := Keyword::Assert, root := 2 }
    )
)

-- The examples are constant judgments, which the wrapper evaluates.
set_option fren.lint.assertions_on_constants "allow" in
set_option fren.evidence "random" in
pub proc member_examples(): (holds?) {
    ensure output: holds?
    ensure rejected: declared_ok?(SYMB, REJECTED)
        and declared_obligations(REJECTED) = two(
            Obligation {
                hyps := two(Fact::Holds(2), Fact::Holds(6)),
                goal := Goal::NonZero(4),
            },
            Obligation { hyps := Empty, goal := Goal::NonZero(4) }
        )
    ensure refuted: not satisfied?(
        Empty,
        DOMAIN_ROWS,
        two(Value::Integer(7), Value::Integer(0)),
        Obligation { hyps := Empty, goal := Goal::NonZero(4) }
    )
    ensure accepted: declared_ok?(SYMB, ACCEPTED)
        and declared_obligations(ACCEPTED) = three(
            Obligation {
                hyps := two(Fact::Holds(2), Fact::Holds(8)),
                goal := Goal::NonZero(4),
            },
            under(Fact::Holds(2), Goal::NonZero(4)),
            Obligation {
                hyps := two(Fact::Holds(2), Fact::Holds(8)),
                goal := Goal::Asserted(2),
            }
        )
    ensure satisfied: all_satisfied?(
        Empty,
        DOMAIN_ROWS,
        two(Value::Integer(7), Value::Integer(0)),
        declared_obligations(ACCEPTED)
    )
        and all_satisfied?(
            Empty,
            DOMAIN_ROWS,
            two(Value::Integer(7), Value::Integer(2)),
            declared_obligations(ACCEPTED)
        )
}
```

r[verification.examples.domain] spec::verification::{NONZERO, ZERO_CALL_ROWS, domains::{within, outside, undeclared}}
Let `M::f(x)` have the one member `require x != 0`, whose table has the
rows `#0`, `0` and `row 0 != row 1`. The goal `Defined(row 1)` of the call
`M::f(1)` holds: the argument's value 1 makes the member true. The same
goal of `M::f(0)` does not hold. In a program that does not declare
`M::f`, neither holds.

```fren
pub const NONZERO: Declared := Declared {
    item := F,
    params := BOUND,
    rows := three(
        typed(CoreF::Local(0), BOUND, Ty::Integer),
        typed(CoreF::IntegerLiteral(0), BOUND, Ty::Integer),
        typed(CoreF::Binary(BinaryOp::Ne, 0, 1), BOUND, Ty::Boolean)
    ),
    body := None,
    members := one(Member { keyword := Keyword::Require, root := 2 }),
}

pub const ZERO_CALL_ROWS: Snoc<Row> := two(
    typed(CoreF::IntegerLiteral(0), Empty, Ty::Integer),
    typed(CoreF::Call(F, one(0)), Empty, Ty::Integer)
)

-- The examples are constant judgments, which the wrapper evaluates.
set_option fren.lint.assertions_on_constants "allow" in
set_option fren.evidence "random" in
pub proc domains(): (holds?) {
    ensure output: holds?
    ensure within: declared_ok?(SYMB, NONZERO)
        and goal_holds?(one(NONZERO), CALL_ROWS, Empty, Goal::Defined(1))
    ensure outside: not goal_holds?(one(NONZERO), ZERO_CALL_ROWS, Empty, Goal::Defined(1))
    ensure undeclared: not goal_holds?(Empty, CALL_ROWS, Empty, Goal::Defined(1))
}
```

r[verification.examples.tables] spec::verification::{F_DECLS, NONZERO_BODY, ONE_DECLS, SEPARATE, UNMOVED, tables::{omitted, present, extra, separate, unmoved}}
Let the typed program declare `M::f(x)` with the body `x` and the
condition `x != 0`. The table above, which has no body, does not
[represent](#r-verification.program.tables) it, and so no program with
that table is defined, whatever its obligations. The same table with the
body at row 0 represents it. That table does not represent the program
without the condition: its member is no typed condition of that program.

Let the body be `1` instead. Its typed table is the one row `1`, and the
condition's typed table begins with the row `#0`, so neither is the
beginning of the other. The table with the rows `1`, `#0`, `0` and
`row 1 != row 2` represents the program: the body is at root 0, and the
condition is at root 3 with its references moved by one. The same table
with the last row `row 0 != row 1` is well formed, but its member is the
condition `1 != x`, and it does not represent the program.

```fren
pub const F_DECLS: Snoc<Decl> := two(
    Decl::Function(F, one(typed(CoreF::Local(0), BOUND, Ty::Integer))),
    Decl::Condition(BOUND, NONZERO.rows)
)

pub const ONE_DECLS: Snoc<Decl> := two(
    Decl::Function(F, one(typed(CoreF::IntegerLiteral(1), BOUND, Ty::Integer))),
    Decl::Condition(BOUND, NONZERO.rows)
)

pub const SEPARATE: Declared := Declared {
    item := F,
    params := BOUND,
    rows := four(
        typed(CoreF::IntegerLiteral(1), BOUND, Ty::Integer),
        typed(CoreF::Local(0), BOUND, Ty::Integer),
        typed(CoreF::IntegerLiteral(0), BOUND, Ty::Integer),
        typed(CoreF::Binary(BinaryOp::Ne, 1, 2), BOUND, Ty::Boolean)
    ),
    body := Some(0),
    members := one(Member { keyword := Keyword::Require, root := 3 }),
}

pub const UNMOVED: Declared := Declared {
    item := F,
    params := BOUND,
    rows := four(
        typed(CoreF::IntegerLiteral(1), BOUND, Ty::Integer),
        typed(CoreF::Local(0), BOUND, Ty::Integer),
        typed(CoreF::IntegerLiteral(0), BOUND, Ty::Integer),
        typed(CoreF::Binary(BinaryOp::Ne, 0, 1), BOUND, Ty::Boolean)
    ),
    body := Some(0),
    members := one(Member { keyword := Keyword::Require, root := 3 }),
}

pub const NONZERO_BODY: Declared := Declared {
    item := F,
    params := BOUND,
    rows := NONZERO.rows,
    body := Some(0),
    members := NONZERO.members,
}

-- The examples are constant judgments, which the wrapper evaluates.
set_option fren.lint.assertions_on_constants "allow" in
set_option fren.evidence "random" in
pub proc tables(): (holds?) {
    ensure output: holds?
    ensure omitted: not represents?(SYMB, F_DECLS, one(NONZERO))
    ensure present: represents?(SYMB, F_DECLS, one(NONZERO_BODY))
    ensure extra: not represents?(
        SYMB,
        one(
            Decl::Function(F, one(typed(CoreF::Local(0), BOUND, Ty::Integer)))
        ),
        one(NONZERO_BODY)
    )
    ensure separate: represents?(SYMB, ONE_DECLS, one(SEPARATE))
    ensure unmoved: declared_ok?(SYMB, UNMOVED) and not represents?(SYMB, ONE_DECLS, one(UNMOVED))
}
```

## Interface

r[verification.validity.interface] spec::validity::{valid?, sound?}
`valid?` is the [validity](#r-verification.validity.meaning) of an
obligation of a table, defined outright: an obligation is valid when every
assignment of it satisfies it. The definition quantifies over all
assignments, so it is not computable. `sound?` says when a verdict is a
sound answer for an obligation: `Proved` only when the obligation is
valid, `Refuted(ρ)` only when ρ is an assignment of the obligation that
does not satisfy it, and `Unknown` always, since it establishes nothing. A
check is any function from obligations to verdicts all of whose answers
are sound, and a solver implements one. The function that always answers
`Unknown` is a check, so the definition does not ask for a decision
procedure.

```fren
pub mod spec::validity

use spec::denotation::Value
use spec::names::Symb
use spec::surface::Snoc
use spec::types::Row
use spec::verification::{Declared, Obligation, Verdict, assignment?, satisfied?}

-- Every assignment of the obligation satisfies it.
set_option fren.lint.undecidable "allow" in
pub fn valid?(symb: Symb, prog: Snoc<Declared>, rows: Snoc<Row>, obligation: Obligation) :=
    forall (env: Snoc<Value>), when assignment?(symb, rows, obligation, env), satisfied?(prog, rows, env, obligation)

-- The verdict is a sound answer for the obligation.
pub fn sound?(
    symb: Symb,
    prog: Snoc<Declared>,
    rows: Snoc<Row>,
    obligation: Obligation,
    verdict: Verdict
) := match verdict {
    Verdict::Proved => valid?(symb, prog, rows, obligation),
    Verdict::Refuted(found) =>
        assignment?(symb, rows, obligation, found) and not satisfied?(prog, rows, found, obligation),
    Verdict::Unknown => true,
}
```
