-- keep-sorted start
import Fren.View
-- keep-sorted end
open Fren.Lang

/-!
# A hosted front-end failure: `simp` reaches its maximum recursion depth

A model of the semantics (`Reqs/Lang/Semantics.md`) with five forms of
expression, and `recursion_unfolds` of `Reqs/Lang/EvaluationRules.md`, in
which `bind_params` has the contract that the semantics rewrite (#391)
dropped, `no_parameters`. With it, the Lean-hosted front end fails the whole
check of `recursion_unfolds`: `simp` reaches its maximum recursion depth.
#417 reports that the `fren` command passes the same check. Without the
contract, the check passes.

The depth that `simp` reaches grows with the number of forms that `eval`
has. With the default `maxRecDepth`, the semantics' 21 forms fail, and so
do 14 of them: all but `Let`, `If`, `And`, `Or`, `Is`, `Match` and
`NoMatch`. Without `Unary`, `Binary`, `Method` and `Count`, those 14 pass,
and with `Binary` alone, or with only the other three, they pass too. So the check runs at a `maxRecDepth` of
128, where these five forms fail, and quickly, with the contract, and pass
without it. #417's own reproduction also assumes `unfolded`; at this depth,
the contract alone is enough.

This is a disagreement between the front ends, which #391 avoided by
dropping the contract. `#expect_max_rec_depth` below records today's
failure, and fails once the check stops reaching the maximum recursion
depth, so that a fix of the hosted front end shows up here (#417, #420).
The model need not follow later changes to the chapters, only keep the
failure.
-/

mod simp_depth

pub type Id := String

pub enum Value { Nil, Cons(Value, Value), Integer(Int) }

pub enum Outcome { Defined(Value), Undefined }

pub enum Params { Nil, Cons(Id, Params) }

pub enum Expr { Var(Id), Nil, Cons(Expr, Expr), Apply(Id, Expr, Params, Expr), Recur(Id, Expr) }

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

pub fn apply(g: Graph, f: Id, args: Value): Outcome := match g {
    Graph::Empty => Outcome::Undefined,
    Graph::Point(h, a, r, rest) => if h = f and a = args then Outcome::Defined(r) else apply(rest, f, args),
}

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

pub fn eval(i: Interp, env: Env, e: Expr): (r: Outcome) {
    out r := match e {
        Expr::Var(x) => lookup(env, x),
        Expr::Nil => Outcome::Defined(Value::Nil),
        Expr::Cons(a, rest) => match eval(i, env, a), eval(i, env, rest) {
            Outcome::Defined(v), Outcome::Defined(l) => Outcome::Defined(Value::Cons(v, l)),
            _, _ => Outcome::Undefined,
        },
        Expr::Apply(_, args, ps, body) => match eval(i, env, args) {
            Outcome::Defined(l) => eval(i, bind_params(ps, l), body),
            Outcome::Undefined => Outcome::Undefined,
        },
        Expr::Recur(f, args) => match eval(i, env, args) {
            Outcome::Defined(l) => apply(i.recursions, f, l),
            Outcome::Undefined => Outcome::Undefined,
        },
    }
}

pub fn respects?(i: Interp, f: Id, ps: Params, e: Expr, l: Value) :=
    apply(i.recursions, f, l) = Outcome::Undefined or apply(i.recursions, f, l) = eval(i, bind_params(ps, l), e)

expect recursion_unfolds(i: Interp, env: Env, f: Id, args: Expr, ps: Params, body: Expr, l: Value, r: Outcome) {
    assume arguments: eval(i, env, args) = Outcome::Defined(l)
    assume body_outcome: eval(i, bind_params(ps, l), body) = r
    assume point: apply(i.recursions, f, l) = r and r is Outcome::Defined(_)
    assume unfolded: apply(i.recursions, f, l) = eval(i, bind_params(ps, l), body)
    expect unfolds: eval(i, env, Expr::Recur(f, args)) = r
    expect respected: respects?(i, f, ps, body, l)
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

#expect_max_rec_depth set_option maxRecDepth 128 in #fren_check recursion_unfolds
