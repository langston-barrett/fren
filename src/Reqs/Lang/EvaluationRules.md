# Rules of evaluation

This chapter states the rule of each form of expression of the [dynamic
semantics](Semantics.md) as laws of `lang::eval`, over the outcomes of the
form's immediate subexpressions, in the order of the Rust Reference's
chapters on expressions. Each law is about one form, so the solver decides
it from one step of `eval`'s equations (see [Solver
encoding](Recursion.md#solver-encoding)). Then come the free variables of
an expression, with the coincidence lemma, and the guards of the
[definedness check](../Check.md#definedness).

```fren
pub mod lang
```

## Literal expressions

A literal evaluates to its value, and is always WD.

## Path expressions

A variable evaluates to the outcome that the environment binds it to. A
constant is an `Apply` of its definition, and a variant without a payload
a `Construct` (see [Derived forms](Semantics.md#derived-forms)).

```fren
expect leaf_rules(i: Interp, env: Env, v: Value, x: Id) {
    expect literal: eval(i, env, Expr::Literal(v)) = Outcome::Defined(v)
    expect read: eval(i, env, Expr::Var(x)) = lookup(env, x)
}
```

## Let expressions

`Let(x, d, b)` evaluates `b` with `x` bound to the outcome of `d`. Since
`x` is bound to an outcome, not a value, `d` counts only where `b` reads
`x`: a definition that is not WD makes the `let` undefined only where its
name is evaluated, as if it were written there. This is the rule of
[Local definitions](Let.md#meaning), and the reason that the
[definedness check](../Check.md#definedness) guards a definition where
its name is mentioned.

```fren
expect let_rules(i: Interp, env: Env, x: Id, d: Expr, b: Expr, v: Value) {
    expect body: eval(i, env, Expr::Let(x, d, b)) = eval(i, Env::Bind(x, eval(i, env, d), env), b)
    -- A definition that is not WD does not count where the body is WD without it.
    expect lazy: when eval(i, env, d) = Outcome::Undefined and eval(i, Env::Bind(x, Outcome::Undefined, env), b) = Outcome::Defined(v),
        eval(i, env, Expr::Let(x, d, b)) = Outcome::Defined(v)
}
```

## Operator expressions

`Unary(op, a)` and `Binary(op, a, b)` evaluate every operand, and are WD
exactly where the operands are and the operator applies to their values:
`not` to a `Bool`, `-` and the arithmetic operators to integers, `div`
and `mod` to a divisor other than `0`, `++` to two strings or two lists,
`in` to a list, and `=` to any two values. `<` and `<=` compare integers
here; the orders of the other [ordered types](Types.md#ordered-types) are
not yet in the model. `Count(c, args)` evaluates every argument, as a
function does, and so is WD where each is.

```fren
expect operator_rules(i: Interp, env: Env, op: BinaryOp, a: Expr, b: Expr, m: Int, n: Int) {
    -- Strictness: an operand that is not WD makes the operation undefined.
    expect strict_left: when eval(i, env, a) = Outcome::Undefined, eval(i, env, Expr::Binary(op, a, b)) = Outcome::Undefined
    expect strict_right: when eval(i, env, b) = Outcome::Undefined, eval(i, env, Expr::Binary(op, a, b)) = Outcome::Undefined
    expect strict_unary: when eval(i, env, a) = Outcome::Undefined, eval(i, env, Expr::Unary(UnaryOp::Not, a)) = Outcome::Undefined
        and eval(i, env, Expr::Unary(UnaryOp::Neg, a)) = Outcome::Undefined
    expect negation: when eval(i, env, a) = Outcome::Defined(Value::Integer(m)),
        eval(i, env, Expr::Unary(UnaryOp::Neg, a)) = Outcome::Defined(Value::Integer(-m))
    -- `=` is WD wherever its operands are.
    expect equality: when eval(i, env, a) is Outcome::Defined(_) and eval(i, env, b) is Outcome::Defined(_),
        eval(i, env, Expr::Binary(BinaryOp::Eq, a, b)) is Outcome::Defined(Value::True | Value::False)
    -- The linear operations are Fren's own.
    expect sum: when eval(i, env, a) = Outcome::Defined(Value::Integer(m)) and eval(i, env, b) = Outcome::Defined(Value::Integer(n)),
        eval(i, env, Expr::Binary(BinaryOp::Add, a, b)) = Outcome::Defined(Value::Integer(m + n))
    expect zero_divisor: when eval(i, env, b) = Outcome::Defined(Value::Integer(0)),
        eval(i, env, Expr::Binary(BinaryOp::Div, a, b)) = Outcome::Undefined
}
```

## Lazy Boolean expressions

`And(a, b)` evaluates `a`. If `a` is `false`, the result is `false`, and
`b` is not evaluated; if `a` is `true`, the result is that of `b`. `Or(a,
b)` is its dual. Either is undefined where `a` is not a WD `Bool`. So `a
and b` and `b and a` have the same value wherever both are WD, but not the
same well-definedness: `q != [] and q[0] = x` is WD, and `q[0] = x and q
!= []` is not where `q` is empty.

```fren
expect lazy_rules(i: Interp, env: Env, a: Expr, b: Expr, b2: Expr) {
    expect and_false: when eval(i, env, a) = Outcome::Defined(Value::False),
        eval(i, env, Expr::And(a, b)) = Outcome::Defined(Value::False)
    expect and_true: when eval(i, env, a) = Outcome::Defined(Value::True),
        eval(i, env, Expr::And(a, b)) = eval(i, env, b)
    expect or_true: when eval(i, env, a) = Outcome::Defined(Value::True),
        eval(i, env, Expr::Or(a, b)) = Outcome::Defined(Value::True)
    -- The right operand is not evaluated where the left decides.
    expect and_unevaluated: when eval(i, env, a) = Outcome::Defined(Value::False),
        eval(i, env, Expr::And(a, b)) = eval(i, env, Expr::And(a, b2))
    expect or_unevaluated: when eval(i, env, a) = Outcome::Defined(Value::True),
        eval(i, env, Expr::Or(a, b)) = eval(i, env, Expr::Or(a, b2))
}
```

## If expressions

`If(c, t, f)` evaluates `c`, and then `t` where it is `true` and `f` where
it is `false`; exactly one branch is evaluated. It is undefined where `c`
is not a WD `Bool`.

```fren
expect if_rules(i: Interp, env: Env, c: Expr, t: Expr, f: Expr, t2: Expr, f2: Expr) {
    expect then_branch: when eval(i, env, c) = Outcome::Defined(Value::True),
        eval(i, env, Expr::If(c, t, f)) = eval(i, env, t) and eval(i, env, Expr::If(c, t, f)) = eval(i, env, Expr::If(c, t, f2))
    expect else_branch: when eval(i, env, c) = Outcome::Defined(Value::False),
        eval(i, env, Expr::If(c, t, f)) = eval(i, env, f) and eval(i, env, Expr::If(c, t, f)) = eval(i, env, Expr::If(c, t2, f))
    expect condition: when eval(i, env, c) = Outcome::Undefined, eval(i, env, Expr::If(c, t, f)) = Outcome::Undefined
}
```

## Match expressions

`Match(s, p, g, b, rest)` is a `match`'s first arm and the arms after
it, `rest`. It evaluates the scrutinee `s`. Where `p` matches its value,
it evaluates the guard `g` with `p`'s binders bound: where `g` is
`true`, the arm is *taken*, and the result is the body `b`'s, with the
binders bound; where `g` is `false`, the result is `rest`'s. Where `p`
does not match, the result is `rest`'s, and neither `g` nor `b` is
evaluated. `NoMatch`, after the last arm, is undefined: a `match` where no
arm is taken is not WD, which the [completeness
check](../Check.md#completeness) rules out. So the arms are tried in
order, and the first that is taken gives the value, as
[`lang::guarded_match`](Expressions.md#matches) states with `Taken`.
`Is(s, p)` says whether `p` matches `s`'s value, and is WD where `s` is.

```fren
expect match_rules(i: Interp, env: Env, s: Expr, p: Pattern, g: Expr, b: Expr, rest: Expr, g2: Expr, b2: Expr, rest2: Expr, v: Value) {
    assume scrutinee: eval(i, env, s) = Outcome::Defined(v)

    -- An arm whose pattern does not match is skipped, unevaluated.
    expect skipped: when not matches_value?(p, v),
        eval(i, env, Expr::Match(s, p, g, b, rest)) = eval(i, env, rest)
        and eval(i, env, Expr::Match(s, p, g, b, rest)) = eval(i, env, Expr::Match(s, p, g2, b2, rest))
    -- An arm whose guard fails falls through, without its body.
    expect falls_through: when matches_value?(p, v) and eval(i, bind(p, v, env), g) = Outcome::Defined(Value::False),
        eval(i, env, Expr::Match(s, p, g, b, rest)) = eval(i, env, rest)
        and eval(i, env, Expr::Match(s, p, g, b, rest)) = eval(i, env, Expr::Match(s, p, g, b2, rest))
    -- A taken arm gives the value, and the later arms are not evaluated.
    expect taken: when matches_value?(p, v) and eval(i, bind(p, v, env), g) = Outcome::Defined(Value::True),
        eval(i, env, Expr::Match(s, p, g, b, rest)) = eval(i, bind(p, v, env), b)
        and eval(i, env, Expr::Match(s, p, g, b, rest)) = eval(i, env, Expr::Match(s, p, g, b, rest2))
    expect test: eval(i, env, Expr::Is(s, p)) = Outcome::Defined(truth(matches_value?(p, v)))
    expect no_arm: eval(i, env, Expr::NoMatch) = Outcome::Undefined
}
```

## List expressions

`Nil` and `Cons(a, rest)` evaluate to lists, and are WD where every
element is. `Construct(c, args)` evaluates to the value `c` built from the
list of its arguments' values. `Project(a, c, k)` is the value at
position `k` of the list of `a`'s value, where that value is built by `c`,
and is undefined otherwise: a field of a record, or a payload's value
where a pattern test has shown its variant. `Index(q, k)` is the element
of the list `q` at the position `k`, from 0, and is undefined out of range
(see [Sequences](Expressions.md#sequences)).

```fren
expect list_rules(i: Interp, env: Env, a: Expr, rest: Expr, q: Expr, k: Expr, c: Id, v: Value, w: Value) {
    expect element: when eval(i, env, a) = Outcome::Defined(v) and eval(i, env, rest) = Outcome::Defined(w),
        eval(i, env, Expr::Cons(a, rest)) = Outcome::Defined(Value::Cons(v, w))
    expect strict_element: when eval(i, env, a) = Outcome::Undefined, eval(i, env, Expr::Cons(a, rest)) = Outcome::Undefined
    expect constructed: when eval(i, env, a) = Outcome::Defined(Value::Cons(v, Value::Nil)),
        eval(i, env, Expr::Construct(c, a)) = Outcome::Defined(Value::Constructed(c, Value::Cons(v, Value::Nil)))
    expect first_field: when eval(i, env, a) = Outcome::Defined(Value::Constructed(c, Value::Cons(v, w))),
        eval(i, env, Expr::Project(a, c, 0)) = Outcome::Defined(v)
    expect first_index: when eval(i, env, q) = Outcome::Defined(Value::Cons(v, w)) and eval(i, env, k) = Outcome::Defined(Value::Integer(0)),
        eval(i, env, Expr::Index(q, k)) = Outcome::Defined(v)
    expect empty_index: when eval(i, env, q) = Outcome::Defined(Value::Nil), eval(i, env, Expr::Index(q, k)) = Outcome::Undefined
}
```

## Method call expressions

`Method(m, r, args)` evaluates the receiver and the arguments, and
applies the [method](Expressions.md#methods): `abs`, `min` and `max` of
integers, and `len` of a string or a list. The methods of strings other
than `len`, and `min` and `max` of the other ordered types, are not yet in
the model.

```fren
expect method_rules(i: Interp, env: Env, r: Expr, args: Expr, m: Int, n: Int, s: String) {
    expect strict: when eval(i, env, r) = Outcome::Undefined, eval(i, env, Expr::Method(MethodName::Abs, r, args)) = Outcome::Undefined
    expect abs: when eval(i, env, r) = Outcome::Defined(Value::Integer(m)) and eval(i, env, args) = Outcome::Defined(Value::Nil),
        eval(i, env, Expr::Method(MethodName::Abs, r, args)) = Outcome::Defined(Value::Integer(m.abs))
    expect min: when eval(i, env, r) = Outcome::Defined(Value::Integer(m))
        and eval(i, env, args) = Outcome::Defined(Value::Cons(Value::Integer(n), Value::Nil)),
        eval(i, env, Expr::Method(MethodName::Min, r, args)) = Outcome::Defined(Value::Integer(m.min(n)))
    expect text_len: when eval(i, env, r) = Outcome::Defined(Value::Text(s)) and eval(i, env, args) = Outcome::Defined(Value::Nil),
        eval(i, env, Expr::Method(MethodName::Len, r, args)) = Outcome::Defined(Value::Integer(s.len))
}
```

## Call expressions

`Apply(f, args, ps, body)` is an application of a defined function that is
not recursive, or a constant: it evaluates the arguments, and then the
body, in an environment that binds only the parameters `ps` to their
values, so the body reads nothing of the caller's. This is the rule of
[Defined functions](Items.md#defined-functions): the value of an
application is that of the body with the parameters substituted by the
arguments' values (*substitution*). `Call(f, args)` is an application of
an uninterpreted function, whose value is the interpretation's
`functions`, which differ between behaviours. An instance of a [generic
uninterpreted function](GenericFunctions.md#uninterpreted-generic-functions)
is named with its type arguments, as `pick<Int>`, so that each instance is
a function of its own. `Recur(f, args)` is an application of a structural
recursion, whose value is the interpretation's `recursions`, the same in
every behaviour. All three evaluate every argument.

```fren
expect call_rules(i: Interp, env: Env, f: Id, args: Expr, ps: Params, body: Expr, l: Value) {
    assume arguments: eval(i, env, args) = Outcome::Defined(l)

    expect substitution: eval(i, env, Expr::Apply(f, args, ps, body)) = eval(i, bind_params(ps, l), body)
    expect interpreted: eval(i, env, Expr::Call(f, args)) = apply(i.functions, f, l)
    expect recursive: eval(i, env, Expr::Recur(f, args)) = apply(i.recursions, f, l)
}
```

A structural recursion `f` with the parameters `ps` and the body `e`
denotes the least fixed point of its equations (see
[Meaning](Recursion.md#meaning)). An interpretation *respects* it at the
arguments `l` where its point in `recursions` there is the body's
outcome, evaluated with `f`'s applications read from the same
interpretation, or where it has no point; the language's interpretation
respects every structural recursion everywhere. Where it does, an
application of `f` unfolds to its body, as [Defined
functions](Items.md#defined-functions) states:

```fren
pub fn respects?(i: Interp, f: Id, ps: Params, e: Expr, l: Value) :=
    apply(i.recursions, f, l) = Outcome::Undefined or apply(i.recursions, f, l) = eval(i, bind_params(ps, l), e)

expect recursion_unfolds(i: Interp, env: Env, f: Id, args: Expr, ps: Params, body: Expr, l: Value, r: Outcome) {
    assume arguments: eval(i, env, args) = Outcome::Defined(l)
    -- The body's outcome at `l`, which is the interpretation's point for `f` there.
    assume body_outcome: eval(i, bind_params(ps, l), body) = r
    assume point: apply(i.recursions, f, l) = r and r is Outcome::Defined(_)
    expect unfolds: eval(i, env, Expr::Recur(f, args)) = r
    expect respected: respects?(i, f, ps, body, l)
}
```

## Free variables

`free_vars(e)` is the set of the variables and functions that `e`'s
outcome may depend on, as `lang::Mention`s, named apart so that a
variable and a function of one name are two: a variable mentions itself;
a `Call` its function, and what its arguments mention; a `Let(x, d, b)`
what `b` mentions but `x`, and what `d` mentions where `b` mentions `x`;
a `Match` what its scrutinee and later arms mention, and what its guard
and body mention but its pattern's binders; an `Apply` what its arguments
mention, and what its body mentions but its parameters, which is nothing
for an elaborated one, whose body reads only its parameters and applies no
uninterpreted function; a `Recur` what its arguments mention, since the
values of structural recursions are the same in every behaviour; and
every other form what its immediate subexpressions mention. Where a
definition is not read, it counts for nothing, as for the
[mentions](Expressions.md#mentions) of the front ends.

```fren
pub enum Mention { Var(Id), Fn(Id) }

-- The names that a pattern binds.
pub fn binders(p: Pattern): Set<Mention> := match p {
    Pattern::Binder(x) => {Mention::Var(x)},
    Pattern::Variant(_, ps) => binders(ps),
    Pattern::Cons(first, rest) => binders(first) union binders(rest),
    _ => {},
}

-- The names of a function's parameters.
pub fn param_names(ps: Params): Set<Mention> := match ps {
    Params::Cons(x, rest) => {Mention::Var(x)} union param_names(rest),
    Params::Nil => {},
}

pub fn free_vars(e: Expr): Set<Mention> := match e {
    Expr::Var(x) => {Mention::Var(x)},
    Expr::Let(x, d, b) => (free_vars(b) minus {Mention::Var(x)})
        union (if Mention::Var(x) in free_vars(b) then free_vars(d) else {}),
    Expr::Unary(_, a) => free_vars(a),
    Expr::Binary(_, a, b) => free_vars(a) union free_vars(b),
    Expr::And(a, b) => free_vars(a) union free_vars(b),
    Expr::Or(a, b) => free_vars(a) union free_vars(b),
    Expr::If(c, t, f) => free_vars(c) union free_vars(t) union free_vars(f),
    Expr::Is(s, _) => free_vars(s),
    Expr::Match(s, p, g, b, rest) => free_vars(s) union ((free_vars(g) union free_vars(b)) minus binders(p))
        union free_vars(rest),
    Expr::Cons(a, rest) => free_vars(a) union free_vars(rest),
    Expr::Construct(_, args) => free_vars(args),
    Expr::Project(a, _, _) => free_vars(a),
    Expr::Index(q, k) => free_vars(q) union free_vars(k),
    Expr::Method(_, r, args) => free_vars(r) union free_vars(args),
    Expr::Count(_, args) => free_vars(args),
    Expr::Apply(_, args, ps, body) => free_vars(args) union (free_vars(body) minus param_names(ps)),
    Expr::Call(f, args) => {Mention::Fn(f)} union free_vars(args),
    Expr::Recur(_, args) => free_vars(args),
    _ => {},
}
```

Two interpretations and environments *agree* on a set of mentions where
they bind each of its variables to the same outcome, give each of its
functions the same points, and have the same structural recursions and
primitive operations, which are the same in every behaviour.
`points(g, f)` are the points of `g` for `f`:

```fren
pub fn points(g: Graph, f: Id): Graph := match g {
    Graph::Point(h, a, r, rest) => if h = f then Graph::Point(h, a, r, points(rest, f)) else points(rest, f),
    Graph::Empty => Graph::Empty,
}

-- A quantifier over a set's members is outside the decidable core; the
-- laws that use it are tested, or decided where the set is empty.
set_option fren.lint.undecidable "allow" in
pub fn agree?(i: Interp, p: Env, j: Interp, q: Env, ms: Set<Mention>) := i.recursions = j.recursions
    and i.primitives = j.primitives
    and (forall (m: Mention), when m in ms, match m {
    Mention::Var(x) => lookup(p, x) = lookup(q, x),
    Mention::Fn(f) => points(i.functions, f) = points(j.functions, f),
})
```

The *coincidence lemma*: an expression has the same outcome under two
interpretations and environments that agree on its free variables. So an
expression that mentions nothing has the same outcome in every behaviour,
which is why a product may have it as a factor (see [Linear
arithmetic](Expressions.md#linear-arithmetic)) and why a constraint that
mentions nothing is constant (see [Expressions that mention
nothing](../Lint/Meaning.md#expressions-that-mention-nothing)).
`lang::coincidence` states it. It is a procedure rather than an
expectation, so that the other chapters can call it, and its guarantee is
the lemma. It holds by structural induction on `e`, which the solver does
not do, since [recursive functions are
opaque](Recursion.md#counterexamples-and-completeness) beyond one step:
`fren check` tests it, and `src/Impls/Semantics.lean` proves it in Lean,
by induction on `lang::Expr`, for every interpretation, environment and
expression.

```fren
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "tested" in
pub proc coincidence(i: Interp, p: Env, j: Interp, q: Env, e: Expr) {
    ensure same: when agree?(i, p, j, q, free_vars(e)), eval(i, p, e) = eval(j, q, e)
}
```

Its case for an expression that mentions nothing, `lang::closed`, needs no
quantifier, and is the one that the other chapters call: such an
expression has one outcome in every interpretation and environment, given
the structural recursions and the primitive operations. `fren check`
tests it, and `src/Impls/Semantics.lean` proves it in Lean, from the
coincidence lemma:

```fren
set_option fren.evidence "tested" in
pub proc closed(i: Interp, p: Env, j: Interp, q: Env, e: Expr) {
    ensure same: when free_vars(e) = {} and i.recursions = j.recursions and i.primitives = j.primitives,
        eval(i, p, e) = eval(j, q, e)
}
```

## Guards

The [definedness check](../Check.md#definedness) asks whether an
expression is WD where it is evaluated, its *guard*.
`lang::guard` states which operands are evaluated only under a condition,
and when, from the operand and the condition's value: the body of `when C`
and `unless C`, the branches of a conditional, the right operand of `and`
and `or`, and a `match` arm's guard and body, whose condition is that the
arm's pattern matches and no earlier arm is taken, and that the arm is
the first taken. An operand is evaluated exactly when its guard holds, and
an operand that is not one of these whenever the expression it is in is.
Guards nest by conjunction.

```fren
-- The operands evaluated only under a condition.
pub enum GuardedOperand { WhenBody, UnlessBody, ThenBranch, ElseBranch, AndRight, OrRight, ArmGuard, ArmBody }

pub proc guard(
    operand: GuardedOperand,
    condition: Value,          -- the condition's value
): (
    det holds?,
    det evaluated?,          -- it is evaluated: its guard holds
) {
    use self::GuardedOperand::{
        AndRight,
        ArmBody,
        ArmGuard,
        ElseBranch,
        OrRight,
        ThenBranch,
        UnlessBody,
        WhenBody,
    }

    out holds? := condition = Value::True

    ensure rule: evaluated? iff match operand {
        WhenBody | ThenBranch | AndRight | ArmGuard | ArmBody => holds?,
        UnlessBody | ElseBranch | OrRight => not holds?,
    }

    -- `a and b` is false without `b` once `a` is, and `a or b` true once `a` is.
    expect and_short_circuits: when operand = AndRight and not holds?, not evaluated?
    expect or_short_circuits: when operand = OrRight and holds?, not evaluated?
    -- The bodies of `when C` and `unless C` are evaluated under opposite conditions.
    expect opposite: when operand is WhenBody | UnlessBody, evaluated? iff (holds? iff operand = WhenBody)
}
```

The guards are those of evaluation: where `guard` says that an operand is
not evaluated, replacing it changes no outcome. `guards_evaluation` states
this for the operands of `and`, `or`, the conditional, and `when` and
`unless` through their [translations](Semantics.md#derived-forms), whose
conditions are WD `Bool`s:

```fren
expect guards_evaluation(i: Interp, env: Env, a: Expr, b: Expr, c: Expr, b2: Expr, c2: Expr, cond?) {
    assume condition: eval(i, env, a) = Outcome::Defined(truth(cond?))
    call conjunct := guard(GuardedOperand::AndRight, truth(cond?))
    call disjunct := guard(GuardedOperand::OrRight, truth(cond?))
    call then_guard := guard(GuardedOperand::ThenBranch, truth(cond?))
    call else_guard := guard(GuardedOperand::ElseBranch, truth(cond?))
    call when_guard := guard(GuardedOperand::WhenBody, truth(cond?))
    call unless_guard := guard(GuardedOperand::UnlessBody, truth(cond?))

    expect and_right: unless conjunct.evaluated?, eval(i, env, Expr::And(a, b)) = eval(i, env, Expr::And(a, b2))
    expect or_right: unless disjunct.evaluated?, eval(i, env, Expr::Or(a, b)) = eval(i, env, Expr::Or(a, b2))
    expect then_unevaluated: unless then_guard.evaluated?, eval(i, env, Expr::If(a, b, c)) = eval(i, env, Expr::If(a, b2, c))
    expect else_unevaluated: unless else_guard.evaluated?, eval(i, env, Expr::If(a, b, c)) = eval(i, env, Expr::If(a, b, c2))
    -- `when a, b` is `if a then b else true`, and `unless a, b` is `if a then true else b`.
    expect when_body: unless when_guard.evaluated?, eval(i, env, Expr::If(a, b, Expr::Literal(Value::True)))
        = eval(i, env, Expr::If(a, b2, Expr::Literal(Value::True)))
    expect unless_body: unless unless_guard.evaluated?, eval(i, env, Expr::If(a, Expr::Literal(Value::True), b))
        = eval(i, env, Expr::If(a, Expr::Literal(Value::True), b2))
    -- Exactly one branch of a conditional is evaluated.
    expect one_branch: then_guard.evaluated? != else_guard.evaluated?
}
```

For an arm of a `match`, the condition of its guard is that its pattern
matches and no earlier arm is taken, and that of its body that the arm is
the one taken, as [`guard`](#guards) states for `ArmGuard` and `ArmBody`.
`arm_guards_evaluation` states this of the first arm of a chain, whose
earlier arms are none, and of a later arm, through the `rest` of the
first, which is evaluated exactly where the first is not taken:

```fren
expect arm_guards_evaluation(
    i: Interp,
    env: Env,
    s: Expr,
    p: Pattern,
    g: Expr,
    b: Expr,
    rest: Expr,
    g2: Expr,
    b2: Expr,
    rest2: Expr,
    v: Value,
    taken?,
) {
    assume scrutinee: eval(i, env, s) = Outcome::Defined(v)
    -- The guard is a WD `Bool` where the pattern matches.
    assume guard_value: when matches_value?(p, v), eval(i, bind(p, v, env), g) = Outcome::Defined(truth(taken?))

    call arm_guard := guard(GuardedOperand::ArmGuard, truth(matches_value?(p, v)))
    call arm_body := guard(GuardedOperand::ArmBody, truth(matches_value?(p, v) and taken?))
    -- The later arms are evaluated where this one is not taken.
    call later := guard(GuardedOperand::ArmGuard, truth(not (matches_value?(p, v) and taken?)))

    expect guard_unevaluated: unless arm_guard.evaluated?,
        eval(i, env, Expr::Match(s, p, g, b, rest)) = eval(i, env, Expr::Match(s, p, g2, b, rest))
    expect body_unevaluated: unless arm_body.evaluated?,
        eval(i, env, Expr::Match(s, p, g, b, rest)) = eval(i, env, Expr::Match(s, p, g, b2, rest))
    expect later_unevaluated: unless later.evaluated?,
        eval(i, env, Expr::Match(s, p, g, b, rest)) = eval(i, env, Expr::Match(s, p, g, b, rest2))
}
```
