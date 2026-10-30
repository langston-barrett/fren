-- keep-sorted start
import Fren.View
-- keep-sorted end
open Fren.Lang

/-!
# A hosted front-end failure: `simp` reaches its maximum recursion depth

A small model of the semantics (`Reqs/Lang/Semantics.md`), with the law
`recursion_unfolds` of `Reqs/Lang/EvaluationRules.md`, in which
`bind_params` has the contract that the semantics rewrite (#391) dropped,
`no_parameters`. With it, the Lean-hosted front end fails the whole check:
`simp` reaches its maximum recursion depth. #417 reports that the `fren`
command passes the same check. Without that one contract, the check passes
here too, so the failure is pinned to it.

The depth that `simp` reaches grows with the model, so this check runs at a
`maxRecDepth` of 128, where the failure comes quickly. What the failure
needs, as far as bisecting found:

- The whole semantics, 21 forms of expression, fails at the default
  `maxRecDepth`, and so does a model of 14 forms; a model of 12, without
  the operators and methods, passes, and so do models with only some of
  `Unary`, `Binary`, `Method` and `Count` added back.
- At a `maxRecDepth` of 128, these five forms fail, and three (without
  `Nil` and `Cons`) pass. At 64, three forms fail with the contract and
  without it, so that limit pins nothing.
- `lookup`'s contract is needed: without it this model passes. So are the
  assumption `unfolded` and `respects?`, which #417's reproduction has.

`#expect_max_rec_depth` records today's failure, and fails once the check
stops reaching the maximum recursion depth, so a fix of the hosted front
end shows up here (#417, #420, #476).
-/

mod simp_depth

pub type Id := String

pub enum Value { Nil, Cons(Value, Value) }

pub enum Outcome { Defined(Value), Undefined }

pub enum Params { Nil, Cons(Id, Params) }

pub enum Expr { Var(Id), Nil, Cons(Expr, Expr), Apply(Id, Expr, Params, Expr), Recur(Id, Expr) }

pub enum Env { Empty, Bind(Id, Outcome, Env) }

pub enum Graph { Empty, Point(Id, Value, Value, Graph) }

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

pub fn eval(g: Graph, env: Env, e: Expr): Outcome := match e {
    Expr::Var(x) => lookup(env, x),
    Expr::Nil => Outcome::Defined(Value::Nil),
    Expr::Cons(a, rest) => match eval(g, env, a), eval(g, env, rest) {
        Outcome::Defined(v), Outcome::Defined(l) => Outcome::Defined(Value::Cons(v, l)),
        _, _ => Outcome::Undefined,
    },
    Expr::Apply(_, args, ps, body) => match eval(g, env, args) {
        Outcome::Defined(l) => eval(g, bind_params(ps, l), body),
        Outcome::Undefined => Outcome::Undefined,
    },
    Expr::Recur(f, args) => match eval(g, env, args) {
        Outcome::Defined(l) => apply(g, f, l),
        Outcome::Undefined => Outcome::Undefined,
    },
}

pub fn respects?(g: Graph, f: Id, ps: Params, e: Expr, l: Value) :=
    apply(g, f, l) = Outcome::Undefined or apply(g, f, l) = eval(g, bind_params(ps, l), e)

expect recursion_unfolds(g: Graph, env: Env, f: Id, args: Expr, ps: Params, body: Expr, l: Value, r: Outcome) {
    assume arguments: eval(g, env, args) = Outcome::Defined(l)
    assume body_outcome: eval(g, bind_params(ps, l), body) = r
    assume point: apply(g, f, l) = r and r is Outcome::Defined(_)
    assume unfolded: apply(g, f, l) = eval(g, bind_params(ps, l), body)
    expect unfolds: eval(g, env, Expr::Recur(f, args)) = r
    expect respected: respects?(g, f, ps, body, l)
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
