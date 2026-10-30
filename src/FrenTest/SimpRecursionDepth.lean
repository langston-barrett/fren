-- keep-sorted start
import Fren.View
-- keep-sorted end
open Fren.Lang

/-!
# A hosted front-end failure: `simp` reaches its maximum recursion depth

The code of `Reqs/Lang/Semantics.md` and `Reqs/Lang/EvaluationRules.md`,
copied as of the semantics rewrite (#391), with two changes:
`bind_params` has the contract that #391 dropped, `no_parameters`, and
`recursion_unfolds` has the assumption `unfolded`. With both, the
Lean-hosted front end fails the whole check of `recursion_unfolds`: `simp`
reaches its maximum recursion depth. #417 reports that the `fren` command
passes the same check. A smaller copy, with only the forms that
`recursion_unfolds` reads, passes in the hosted front end, so the
failure needs more of the model. The copy is frozen on purpose: it need
not follow later changes to the chapters, only keep the failure. If its
check grows slow, shrink it to the smallest copy that still fails.

This is a disagreement between the front ends, which #391 avoided by
dropping the contract. `#expect_max_rec_depth` below records today's
failure, and fails once the check stops reaching the maximum recursion
depth, so that a fix of the hosted front end shows up here (#417, #420).
-/

mod simp_depth

pub type Id := String

pub enum Value {
    True,
    False,
    Integer(Int),
    Text(String),
    Nil,
    Cons(Value, Value),
    Constructed(Id, Value),
}

-- The value of a `Bool`.
pub fn truth(b?): Value := if b? then Value::True else Value::False

pub enum Outcome { Defined(Value), Undefined }

pub enum Pattern {
    Wildcard,
    Binder(Id),
    Literal(Value),
    AtLeast(Int),
    AtMost(Int),
    Between(Int, Int),
    Variant(Id, Pattern),
    Nil,
    Cons(Pattern, Pattern),
    Or(Pattern, Pattern),
}

pub enum UnaryOp { Not, Neg }

pub enum BinaryOp { Eq, Lt, Le, Add, Sub, Mul, Div, Mod, Concat, In }

pub enum MethodName { Abs, Min, Max, Len }

-- The cardinality operators: `exactly_one?` and `at_most_one?`.
pub enum Cardinality { Exactly, AtMost }

-- A function's parameters, in order.
pub enum Params { Nil, Cons(Id, Params) }

pub enum Expr {
    Literal(Value),
    Var(Id),
    Let(Id, Expr, Expr),
    Unary(UnaryOp, Expr),
    Binary(BinaryOp, Expr, Expr),
    And(Expr, Expr),
    Or(Expr, Expr),
    If(Expr, Expr, Expr),
    Is(Expr, Pattern),
    Match(Expr, Pattern, Expr, Expr, Expr),
    NoMatch,
    Nil,
    Cons(Expr, Expr),
    Construct(Id, Expr),
    Project(Expr, Id, Int),
    Index(Expr, Expr),
    Method(MethodName, Expr, Expr),
    Count(Cardinality, Expr),
    Apply(Id, Expr, Params, Expr),
    Call(Id, Expr),
    Recur(Id, Expr),
}

pub enum Env { Empty, Bind(Id, Outcome, Env) }

pub enum Graph { Empty, Point(Id, Value, Value, Graph) }

pub struct Interp { functions: Graph, recursions: Graph, primitives: Graph }

pub fn lookup(env: Env, x: Id): (r: Outcome) {
    out r := match env {
        Env::Empty => Outcome::Undefined,
        Env::Bind(y, bound, rest) => if y = x then bound else lookup(rest, x),
    }

    ensure innermost: match env {
        Env::Bind(y, bound, _) => (when y = x, r = bound),
        Env::Empty => r = Outcome::Undefined,
    }
}

-- `f`'s value at `args`, and undefined where the graph has no point for them.
pub fn apply(g: Graph, f: Id, args: Value): Outcome := match g {
    Graph::Empty => Outcome::Undefined,
    Graph::Point(h, a, r, rest) => if h = f and a = args then Outcome::Defined(r) else apply(rest, f, args),
}

expect lookup_binding(env: Env, x: Id, y: Id, r: Outcome) {
    expect innermost: lookup(Env::Bind(x, r, env), x) = r
    expect others: when y != x, lookup(Env::Bind(y, r, env), x) = lookup(env, x)
}

-- The element at position `k`, from 0, and undefined out of range.
pub fn nth(list: Value, k: Int): (r: Outcome) {
    out r := match list {
        Value::Cons(v, rest) => if k = 0 then Outcome::Defined(v) else if k < 0 then Outcome::Undefined else nth(rest, k - 1),
        _ => Outcome::Undefined,
    }

    ensure first: match list {
        Value::Cons(v, _) => (when k = 0, r = Outcome::Defined(v)),
        _ => r = Outcome::Undefined,
    }
    ensure negative: when k < 0, r = Outcome::Undefined
}

pub fn length(list: Value): Int := match list {
    Value::Cons(_, rest) => 1 + length(rest),
    _ => 0,
}

pub fn append(a: Value, b: Value): Value := match a {
    Value::Cons(v, rest) => Value::Cons(v, append(rest, b)),
    _ => b,
}

pub fn element?(v: Value, list: Value) := match list {
    Value::Cons(w, rest) => w = v or element?(v, rest),
    _ => false,
}

pub fn list?(v: Value) := v is Value::Nil | Value::Cons(_, _)

-- How many of the elements are `true`, and whether all are `Bool`s.
pub fn trues(list: Value): Int := match list {
    Value::Cons(w, rest) => (if w = Value::True then 1 else 0) + trues(rest),
    _ => 0,
}

pub fn booleans?(list: Value) := match list {
    Value::Cons(w, rest) => w is Value::True | Value::False and booleans?(rest),
    Value::Nil => true,
    _ => false,
}

pub fn matches_value?(p: Pattern, v: Value) := match p {
    Pattern::Wildcard => true,
    Pattern::Binder(_) => true,
    Pattern::Literal(w) => v = w,
    Pattern::AtLeast(lo) => v is Value::Integer(n) and n >= lo,
    Pattern::AtMost(hi) => v is Value::Integer(n) and n <= hi,
    Pattern::Between(lo, hi) => v is Value::Integer(n) and lo <= n <= hi,
    Pattern::Variant(c, ps) => match v {
        Value::Constructed(d, payload) => c = d and matches_value?(ps, payload),
        _ => false,
    },
    Pattern::Nil => v = Value::Nil,
    Pattern::Cons(first, rest) => match v {
        Value::Cons(w, more) => matches_value?(first, w) and matches_value?(rest, more),
        _ => false,
    },
    Pattern::Or(a, b) => matches_value?(a, v) or matches_value?(b, v),
}

pub fn bind(p: Pattern, v: Value, env: Env): Env := match p {
    Pattern::Binder(x) => Env::Bind(x, Outcome::Defined(v), env),
    Pattern::Variant(_, ps) => match v {
        Value::Constructed(_, payload) => bind(ps, payload, env),
        _ => env,
    },
    Pattern::Cons(first, rest) => match v {
        Value::Cons(w, more) => bind(rest, more, bind(first, w, env)),
        _ => env,
    },
    _ => env,
}

-- The environment of a function's body: its parameters bound to the arguments.
pub fn bind_params(ps: Params, args: Value): (r: Env) {
    out r := match ps {
        Params::Cons(x, rest) => match args {
            Value::Cons(v, more) => Env::Bind(x, Outcome::Defined(v), bind_params(rest, more)),
            _ => Env::Empty,
        },
        Params::Nil => Env::Empty,
    }

    ensure no_parameters: when ps = Params::Nil, r = Env::Empty
}

pub fn unary_value(op: UnaryOp, a: Outcome): Outcome := match op, a {
    UnaryOp::Not, Outcome::Defined(Value::True) => Outcome::Defined(Value::False),
    UnaryOp::Not, Outcome::Defined(Value::False) => Outcome::Defined(Value::True),
    UnaryOp::Neg, Outcome::Defined(Value::Integer(n)) => Outcome::Defined(Value::Integer(-n)),
    _, _ => Outcome::Undefined,
}

-- A primitive operation at two arguments.
pub fn primitive(i: Interp, f: Id, v: Value, w: Value): Outcome :=
    apply(i.primitives, f, Value::Cons(v, Value::Cons(w, Value::Nil)))

pub fn binary_value(i: Interp, op: BinaryOp, a: Outcome, b: Outcome): Outcome := match a, b {
    Outcome::Defined(v), Outcome::Defined(w) => match op, v, w {
        BinaryOp::Eq, _, _ => Outcome::Defined(truth(v = w)),
        BinaryOp::Lt, Value::Integer(m), Value::Integer(n) => Outcome::Defined(truth(m < n)),
        BinaryOp::Le, Value::Integer(m), Value::Integer(n) => Outcome::Defined(truth(m <= n)),
        BinaryOp::Add, Value::Integer(m), Value::Integer(n) => Outcome::Defined(Value::Integer(m + n)),
        BinaryOp::Sub, Value::Integer(m), Value::Integer(n) => Outcome::Defined(Value::Integer(m - n)),
        BinaryOp::Mul, Value::Integer(_), Value::Integer(_) => primitive(i, "*", v, w),
        BinaryOp::Div, Value::Integer(_), Value::Integer(n) => if n = 0 then Outcome::Undefined else primitive(i, "div", v, w),
        BinaryOp::Mod, Value::Integer(_), Value::Integer(n) => if n = 0 then Outcome::Undefined else primitive(i, "mod", v, w),
        BinaryOp::Concat, Value::Text(_), Value::Text(_) => primitive(i, "++", v, w),
        BinaryOp::Concat, Value::Nil | Value::Cons(_, _), Value::Nil | Value::Cons(_, _) => Outcome::Defined(append(v, w)),
        BinaryOp::In, _, Value::Nil | Value::Cons(_, _) => Outcome::Defined(truth(element?(v, w))),
        _, _, _ => Outcome::Undefined,
    },
    _, _ => Outcome::Undefined,
}

pub fn method_value(m: MethodName, receiver: Outcome, args: Outcome): Outcome := match receiver, args {
    Outcome::Defined(v), Outcome::Defined(l) => match m, v, l {
        MethodName::Abs, Value::Integer(n), Value::Nil => Outcome::Defined(Value::Integer(n.abs)),
        MethodName::Min, Value::Integer(n), Value::Cons(Value::Integer(k), Value::Nil) => Outcome::Defined(Value::Integer(n.min(k))),
        MethodName::Max, Value::Integer(n), Value::Cons(Value::Integer(k), Value::Nil) => Outcome::Defined(Value::Integer(n.max(k))),
        MethodName::Len, Value::Text(s), Value::Nil => Outcome::Defined(Value::Integer(s.len)),
        MethodName::Len, Value::Nil | Value::Cons(_, _), Value::Nil => Outcome::Defined(Value::Integer(length(v))),
        _, _, _ => Outcome::Undefined,
    },
    _, _ => Outcome::Undefined,
}

pub fn count_value(c: Cardinality, args: Outcome): Outcome := match args {
    Outcome::Defined(l) => if booleans?(l) then Outcome::Defined(truth(match c {
        Cardinality::AtMost => trues(l) <= 1,
        Cardinality::Exactly => trues(l) = 1,
    })) else Outcome::Undefined,
    Outcome::Undefined => Outcome::Undefined,
}

pub fn eval(i: Interp, env: Env, e: Expr): (r: Outcome) {
    out r := match e {
        Expr::Literal(v) => Outcome::Defined(v),
        Expr::Var(x) => lookup(env, x),
        Expr::Let(x, d, b) => eval(i, Env::Bind(x, eval(i, env, d), env), b),
        Expr::Unary(op, a) => unary_value(op, eval(i, env, a)),
        Expr::Binary(op, a, b) => binary_value(i, op, eval(i, env, a), eval(i, env, b)),
        Expr::And(a, b) => match eval(i, env, a) {
            Outcome::Defined(Value::True) => eval(i, env, b),
            Outcome::Defined(Value::False) => Outcome::Defined(Value::False),
            _ => Outcome::Undefined,
        },
        Expr::Or(a, b) => match eval(i, env, a) {
            Outcome::Defined(Value::True) => Outcome::Defined(Value::True),
            Outcome::Defined(Value::False) => eval(i, env, b),
            _ => Outcome::Undefined,
        },
        Expr::If(c, t, f) => match eval(i, env, c) {
            Outcome::Defined(Value::True) => eval(i, env, t),
            Outcome::Defined(Value::False) => eval(i, env, f),
            _ => Outcome::Undefined,
        },
        Expr::Is(s, p) => match eval(i, env, s) {
            Outcome::Defined(v) => Outcome::Defined(truth(matches_value?(p, v))),
            Outcome::Undefined => Outcome::Undefined,
        },
        Expr::Match(s, p, g, b, rest) => match eval(i, env, s) {
            Outcome::Defined(v) => if matches_value?(p, v) then (match eval(i, bind(p, v, env), g) {
                Outcome::Defined(Value::True) => eval(i, bind(p, v, env), b),
                Outcome::Defined(Value::False) => eval(i, env, rest),
                _ => Outcome::Undefined,
            }) else eval(i, env, rest),
            Outcome::Undefined => Outcome::Undefined,
        },
        Expr::NoMatch => Outcome::Undefined,
        Expr::Nil => Outcome::Defined(Value::Nil),
        Expr::Cons(a, rest) => match eval(i, env, a), eval(i, env, rest) {
            Outcome::Defined(v), Outcome::Defined(l) => Outcome::Defined(Value::Cons(v, l)),
            _, _ => Outcome::Undefined,
        },
        Expr::Construct(c, args) => match eval(i, env, args) {
            Outcome::Defined(l) => Outcome::Defined(Value::Constructed(c, l)),
            Outcome::Undefined => Outcome::Undefined,
        },
        Expr::Project(a, c, k) => match eval(i, env, a) {
            Outcome::Defined(Value::Constructed(d, l)) => if c = d then nth(l, k) else Outcome::Undefined,
            _ => Outcome::Undefined,
        },
        Expr::Index(q, k) => match eval(i, env, q), eval(i, env, k) {
            Outcome::Defined(l), Outcome::Defined(Value::Integer(n)) => if list?(l) then nth(l, n) else Outcome::Undefined,
            _, _ => Outcome::Undefined,
        },
        Expr::Method(m, receiver, args) => method_value(m, eval(i, env, receiver), eval(i, env, args)),
        Expr::Count(c, args) => count_value(c, eval(i, env, args)),
        Expr::Apply(_, args, ps, body) => match eval(i, env, args) {
            Outcome::Defined(l) => eval(i, bind_params(ps, l), body),
            Outcome::Undefined => Outcome::Undefined,
        },
        Expr::Call(f, args) => match eval(i, env, args) {
            Outcome::Defined(l) => apply(i.functions, f, l),
            Outcome::Undefined => Outcome::Undefined,
        },
        Expr::Recur(f, args) => match eval(i, env, args) {
            Outcome::Defined(l) => apply(i.recursions, f, l),
            Outcome::Undefined => Outcome::Undefined,
        },
    }
}

expect determinism(i: Interp, env: Env, e: Expr, e2: Expr) {
    expect same: when e2 = e, eval(i, env, e2) = eval(i, env, e)
}

expect leaf_rules(i: Interp, env: Env, v: Value, x: Id) {
    expect literal: eval(i, env, Expr::Literal(v)) = Outcome::Defined(v)
    expect read: eval(i, env, Expr::Var(x)) = lookup(env, x)
}

expect let_rules(i: Interp, env: Env, x: Id, d: Expr, b: Expr, v: Value) {
    expect body: eval(i, env, Expr::Let(x, d, b)) = eval(i, Env::Bind(x, eval(i, env, d), env), b)
    -- A definition that is not WD does not count where the body is WD without it.
    expect lazy: when eval(i, env, d) = Outcome::Undefined and eval(i, Env::Bind(x, Outcome::Undefined, env), b) = Outcome::Defined(v),
        eval(i, env, Expr::Let(x, d, b)) = Outcome::Defined(v)
}

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

expect if_rules(i: Interp, env: Env, c: Expr, t: Expr, f: Expr, t2: Expr, f2: Expr) {
    expect then_branch: when eval(i, env, c) = Outcome::Defined(Value::True),
        eval(i, env, Expr::If(c, t, f)) = eval(i, env, t) and eval(i, env, Expr::If(c, t, f)) = eval(i, env, Expr::If(c, t, f2))
    expect else_branch: when eval(i, env, c) = Outcome::Defined(Value::False),
        eval(i, env, Expr::If(c, t, f)) = eval(i, env, f) and eval(i, env, Expr::If(c, t, f)) = eval(i, env, Expr::If(c, t2, f))
    expect condition: when eval(i, env, c) = Outcome::Undefined, eval(i, env, Expr::If(c, t, f)) = Outcome::Undefined
}

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

expect call_rules(i: Interp, env: Env, f: Id, args: Expr, ps: Params, body: Expr, l: Value) {
    assume arguments: eval(i, env, args) = Outcome::Defined(l)

    expect substitution: eval(i, env, Expr::Apply(f, args, ps, body)) = eval(i, bind_params(ps, l), body)
    expect interpreted: eval(i, env, Expr::Call(f, args)) = apply(i.functions, f, l)
    expect recursive: eval(i, env, Expr::Recur(f, args)) = apply(i.recursions, f, l)
}

pub fn respects?(i: Interp, f: Id, ps: Params, e: Expr, l: Value) :=
    apply(i.recursions, f, l) = Outcome::Undefined or apply(i.recursions, f, l) = eval(i, bind_params(ps, l), e)

expect recursion_unfolds(i: Interp, env: Env, f: Id, args: Expr, ps: Params, body: Expr, l: Value, r: Outcome) {
    assume arguments: eval(i, env, args) = Outcome::Defined(l)
    -- The body's outcome at `l`, which is the interpretation's point for `f` there.
    assume body_outcome: eval(i, bind_params(ps, l), body) = r
    assume point: apply(i.recursions, f, l) = r and r is Outcome::Defined(_)
    assume unfolded: apply(i.recursions, f, l) = eval(i, bind_params(ps, l), body)
    expect unfolds: eval(i, env, Expr::Recur(f, args)) = r
    expect respected: respects?(i, f, ps, body, l)
}

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

set_option fren.lint.undecidable "allow" in
set_option fren.evidence "random" in
pub proc coincidence(i: Interp, p: Env, j: Interp, q: Env, e: Expr) {
    ensure same: when agree?(i, p, j, q, free_vars(e)), eval(i, p, e) = eval(j, q, e)
}

set_option fren.evidence "random" in
pub proc closed(i: Interp, p: Env, j: Interp, q: Env, e: Expr) {
    ensure same: when free_vars(e) = {} and i.recursions = j.recursions and i.primitives = j.primitives,
        eval(i, p, e) = eval(j, q, e)
}

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

open Lean Elab Command in
/-- Elaborates `cmd`, and fails unless it logs Lean's maximum recursion
depth error, which it removes from the log. `#guard_msgs` did not record
that error, with or without `Elab.async`, though it is in the log. -/
elab "#expect_max_rec_depth " cmd:command : command => do
  let before := (← get).messages
  modify fun s => { s with messages := {} }
  elabCommand cmd
  let logged := (← get).messages
  let isDepth (m : Message) : BaseIO Bool := do
    return m.severity == .error && ((← m.data.toString).splitOn "maximum recursion depth").length > 1
  let mut depth := 0
  let mut kept : MessageLog := {}
  for m in logged.toList do
    if ← isDepth m then depth := depth + 1 else kept := kept.add m
  modify fun s => { s with messages := before ++ kept }
  if depth = 0 then
    throwError m!"expected the maximum recursion depth error among the {logged.toList.length} messages logged"

#expect_max_rec_depth #fren_check recursion_unfolds
