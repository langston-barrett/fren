-- keep-sorted start
import FrenTest.FuzzFrontends.Expressions
-- keep-sorted end

open Lean FrenCli FrenCli.Eval

namespace FrenTest.FuzzFrontends.Wide

/-- A recursive defined function with a postcondition, applied on several
paths of one expectation, each with its own guards, whose facts a query
asserts once, under its weakest paths (`lang::merged_facts`): on a path
whose guards include another's, on two neither of whose guards are among
the other's, or on one without guards first; and at a larger argument,
whose one-step equation applies it again. Each expectation holds, by the
postcondition or by one unfolding, so no result depends on a model. It is
written from a grammar of its own, as `factChain` is. -/
def guardPaths : R String := do
  let k ← below 3
  let shape ← below 3
  let (params, goal) := match shape with
    | 0 => ("a?", "(not a? or gpsum(l) >= 0) and (not a? or gpsum(l) > -1)")
    | 1 => ("a?, b?", s!"(not a? or gpsum(l) >= 0) and (not b? or gpsum(GuardList::Cons({k}, l)) >= {k})")
    | _ => ("a?", s!"gpsum(l) > -1 and (not a? or gpsum(GuardList::Cons({k}, l)) >= {k})")
  return "pub enum GuardList { Nil, Cons(Int, GuardList) }\n" ++
    "pub fn gpsum(l: GuardList): (r: Int) {\n    out r := match l { GuardList::Nil => 0, GuardList::Cons(m, rest) => m.abs + gpsum(rest) }\n" ++
    "    ensure e: r >= 0\n}\n" ++
    s!"\nproc gp_paths(l: GuardList, {params}) \{\n    expect c: {goal}\n}\n"

/-- Generic structural recursions (`Reqs/Lang/Recursion#generic-recursion`):
over a generic list and a tree with two type parameters, with an `Int`, a
`Nat`, a `Bool` and a `Set<T>` result, with a contract that holds by
induction or fails, nested (one applying another at its own type parameter
and at a list of it), applied in a closure given to a generic higher-order
function and in a generic function that is not recursive, and a procedure
that applies them at two instances, of `Int`, `Bool`, `String`, `E` if the
spec has it, or `Option<Int>`, at constant arguments too. Now and then, at
`Bool` or `E`, the procedure is enumerated, with one list of that type as
its only input. A check may fail or be inconclusive, but nothing here is a
static error. -/
def genericRecursion (sc : WScope) : R String := do
  let post ← pick #["r >= 0", "r >= 1", "r = gr_len(l)", "r <= gr_len(l)"]
  let mut out := "pub enum Gl<T> { Nil, Cons(T, Gl<T>) }\n" ++
    "pub enum Gt<A, B> { Leaf(A), Node(B, Gt<A, B>, Gt<A, B>) }\n" ++
    "pub fn gr_len<T>(l: Gl<T>): Int := match l { Gl::Nil => 0, Gl::Cons(_, r) => 1 + gr_len(r) }\n" ++
    "pub fn gr_nlen<T>(l: Gl<T>): Nat := match l { Gl::Nil => 0, Gl::Cons(_, r) => 1 + gr_nlen(r) }\n" ++
    "pub fn gr_has?<T>(l: Gl<T>, x: T) := match l { Gl::Nil => false, Gl::Cons(y, r) => y = x or gr_has?(r, x) }\n" ++
    "pub fn gr_elems<T>(l: Gl<T>): Set<T> := match l { Gl::Nil => {}, Gl::Cons(y, r) => {y} union gr_elems(r) }\n" ++
    "pub fn gr_count<T>(l: Gl<T>): (r: Int) {\n    out r := match l { Gl::Nil => 0, Gl::Cons(_, t) => 1 + gr_count(t) }\n" ++
    s!"    ensure e: {post}\n}\n" ++
    "pub fn gr_total<T>(ls: Gl<Gl<T>>): Int := match ls { Gl::Nil => 0, Gl::Cons(l, r) => gr_len(l) + gr_total(r) }\n" ++
    "pub fn gr_size<A, B>(t: Gt<A, B>): (r: Int) {\n" ++
    "    out r := match t { Gt::Leaf(_) => 1, Gt::Node(_, a, b) => 1 + gr_size(a) + gr_size(b) }\n    ensure pos: r >= 1\n}\n" ++
    "pub fn gr_leaves<A, B>(t: Gt<A, B>): Set<A> := match t {\n" ++
    "    Gt::Leaf(x) => {x},\n    Gt::Node(_, a, b) => gr_leaves(a) union gr_leaves(b),\n}\n" ++
    "pub fn gr_holds?<T>(l: Gl<T>, p: fn(Gl<T>) -> Bool) := p(l)\n" ++
    "pub fn gr_nonempty?<T>(l: Gl<T>) := gr_len(l) > 0\n"
  let tys := #[("Int", "1", "2"), ("Bool", "true", "false"), ("String", "\"a\"", "\"b\""),
    ("Option<Int>", "Option::Some(1)", "Option::Some(0)")] ++
    (if sc.nVariants > 0 then #[("E", "E::V0", "E::V1")] else #[])
  let (ty, a, b) ← pick tys
  let (ty2, _, _) ← pick tys
  let enumerated := (ty == "Bool" || ty == "E") && (← chance 40)
  let cons (v : String) (l : String) := s!"Gl::Cons({v}, {l})"
  let lst : R String := do
    if enumerated then pick #["l", cons a "l", cons a "Gl::Nil"]
    else pick #["l", "m", cons a "l", cons b (cons a "Gl::Nil"), cons b "Gl::Nil"]
  let mut body := ""
  for k in [0:(← below 4) + 2] do
    let e ← match ← below 14 with
      | 0 => pure s!"gr_len({← lst}) >= 0"
      | 1 => pure s!"when l is Gl::Cons(_, r), gr_len(l) = 1 + gr_len(r)"
      | 2 => pure s!"gr_nlen({← lst}) {← pick #[">=", "<", "="]} {← below 3}"
      | 3 => pure s!"gr_has?({cons a "l"}, {a})"
      | 4 => pure s!"gr_has?({← lst}, {b}) {← pick #["iff", "or"]} {b} in gr_elems({← lst})"
      | 5 => pure s!"gr_count({← lst}) {← pick #[">=", ">", "="]} {← pick #["0", "gr_len(l)"]}"
      -- The same list on both sides: a check that holds, whatever model
      -- the solver gives where it needs more than one step (#634).
      | 6 =>
        let x ← lst
        pure s!"gr_total({cons x "Gl::Nil"}) = gr_len({x})"
      | 7 => pure s!"gr_holds?({← lst}, |z| gr_len(z) >= {← below 2})"
      | 8 => pure s!"when l is Gl::Cons(_, _), gr_nonempty?(l)"
      | 9 => pure s!"gr_len({cons a "Gl::Nil"}) = 1 or l = Gl::Nil"
      | 10 =>
        if enumerated then pure s!"gr_elems(l) subset gr_elems({cons a "l"})"
        else pure s!"gr_size(t) >= {← pick #["1", "2"]}"
      | 11 =>
        if enumerated then pure s!"gr_len(l) = gr_count(l)"
        else
          let x := if ty == "Bool" then "x?" else "x"
          pure s!"when t is Gt::Leaf({x}), gr_leaves(t) = \{{x}}"
      | 12 =>
        if enumerated then pure s!"not gr_has?(Gl::Nil, {a})"
        else pure s!"gr_len(w) >= 0 and gr_count(w) {← pick #[">=", "<"]} 0"
      | _ => pure s!"gr_elems({← lst}) = gr_elems({← lst})"
    body := body ++ s!"    expect gr{k}: {e}\n"
  -- Every input mentioned, so that none is unused.
  body := body ++ (if enumerated then "    expect grm: gr_len(l) >= 0\n"
    else "    expect grm: gr_len(l) + gr_len(m) + gr_len(w) >= 0 and gr_size(t) >= 1\n")
  if enumerated then
    return out ++ "set_option fren.enumeration.size 3 in\nset_option fren.evidence \"enumerated\" in\n" ++
      s!"pub proc gr_apps(l: Gl<{ty}>) \{\n{body}}\n"
  return out ++ s!"pub proc gr_apps(l: Gl<{ty}>, m: Gl<{ty}>, t: Gt<{ty}, {ty2}>, w: Gl<{ty2}>) \{\n{body}}\n"

/-- Structural recursions whose results have subset types (#693): of
`Int` or `Nat`, named or through an alias, over a list and a tree, with
each recursive application direct, under an `if`'s guard, under a `match`
on a payload, within arithmetic, or several of them, with a postcondition
or without, one generic at a result type that is not its type parameter,
and a procedure whose expectations apply each. Each application's result
type is a fact, in the function's own body too, beside its postconditions
(`lang::recursive_facts`), and a model that evaluation refutes is
Inconclusive (`lang::counterexample_confirmed`). A check may fail or be
inconclusive, but nothing here is a static error. -/
def recursiveSubsets : R String := do
  -- The subset type's base and its invariant, of a value.
  let (base, inv) ← pick #[("Int", fun (e : String) => s!"{e} >= 1"), ("Int", fun e => s!"{e} != 0"),
    ("Nat", fun e => s!"{e} >= 2"), ("Int", fun e => s!"{e} >= 1 and {e} <= 100")]
  let alias ← chance 50
  let ty := if alias then "Rsq" else "Rsp"
  let mut out := "pub enum Rsl { Nil, Cons(Int, Rsl) }\npub enum Rst { Leaf, Node(Rst, Rst) }\n" ++
    s!"pub type Rsp = n: {base} where inv: {inv "n"}\n" ++ (if alias then "pub type Rsq := Rsp\n" else "")
  -- The arm of a `Cons`, with the recursive application `f(p, ·)`, and
  -- whether it reads the element `x`.
  let arm (f : String) : R (String × String) := do
    match ← below 6 with
    | 0 => pure ("_", s!"{f}(p, r)")
    | 1 => pure ("x", s!"if x > 0 then {f}(p, r) else p")
    | 2 => pure ("_", s!"match r \{ Rsl::Nil => p, Rsl::Cons(_, s) => {f}(p, s) }")
    | 3 => pure ("_", s!"if {f}(p, r) = p then p else {f}(p, r)")
    -- Each arm meets the result type where the recursive applications
    -- do, so that a caller's check, which assumes it, holds in fact and
    -- the methods agree (`methodsAgree fuzz`).
    | 4 => pure ("_", s!"{f}(p, r) + 0")
    | _ => pure ("x", s!"if x = 0 then p else {f}(p, r)")
  let fns := #["rs_keep", "rs_post"]
  let (x, a) ← arm "rs_keep"
  out := out ++ s!"pub fn rs_keep(p: {ty}, l: Rsl): {ty} := match l \{\n" ++
    s!"    Rsl::Nil => p,\n    Rsl::Cons({x}, r) => {a},\n}\n"
  -- With a postcondition, which holds or fails by induction.
  let post ← pick #["o >= p", "o = p", "o > p", "o >= 1"]
  let (x, a) ← arm "rs_post"
  out := out ++ s!"pub fn rs_post(p: {ty}, l: Rsl): (o: {ty}) \{\n    out o := match l \{\n" ++
    s!"        Rsl::Nil => p,\n        Rsl::Cons({x}, r) => {a},\n    }\n    ensure e: {post}\n}\n"
  -- Two applications, over a tree.
  let (pat, a) ← pick #[("Rst::Node(a, b)", "if rs_tree(p, a) > rs_tree(p, b) then rs_tree(p, a) else rs_tree(p, b)"),
    ("Rst::Node(a, _)", "rs_tree(p, a)"), ("Rst::Node(a, b)", "if a = b then rs_tree(p, b) else p")]
  out := out ++ s!"pub fn rs_tree(p: {ty}, t: Rst): {ty} := match t \{\n    Rst::Leaf => p,\n    {pat} => {a},\n}\n"
  let generic ← chance 50
  if generic then
    out := out ++ s!"pub fn rs_gen<T>(p: {ty}, y: T, l: Rsl): {ty} := match l \{\n" ++
      s!"    Rsl::Nil => p,\n    Rsl::Cons(_, r) => rs_gen(p, y, r),\n}\n"
  -- Every input mentioned, so that none is unused: `l` first, `t` second.
  let mut body := ""
  for k in [0:(← below 3) + 2] do
    let app ← match k, ← below (if generic then 5 else 4) with
      | 0, _ => pure s!"{← pick fns}(p, l)"
      | 1, _ | _, 2 => pure "rs_tree(p, t)"
      | _, 0 => pure s!"{← pick fns}(p, l)"
      | _, 1 => pure s!"{← pick fns}(p, Rsl::Cons({← pick #["0", "1", "-1"]}, l))"
      | _, 3 => pure s!"{← pick fns}(p, Rsl::Nil)"
      | _, _ => pure s!"rs_gen(p, {← pick #["true", "1", "l"]}, l)"
    body := body ++ s!"    expect rs{k}: {← pick #[inv app, s!"{app} = p or ({inv app})"]}\n"
  out := out ++ s!"pub proc rs_apps(p: {ty}, l: Rsl, t: Rst) \{\n{body}}\n"
  -- A generic one whose result is its type parameter, at an enumeration
  -- whose payload has the subset type: its instance's result brings no
  -- fact, in both front ends.
  if ← chance 50 then
    out := out ++ s!"pub enum Rsb \{ B({ty}) }\n" ++
      "pub fn rs_rep<T>(x: T, l: Rsl): T := match l {\n    Rsl::Nil => x,\n    Rsl::Cons(_, r) => rs_rep(x, r),\n}\n" ++
      s!"pub proc rs_reps(b: Rsb, l: Rsl) \{\n    expect rr: match rs_rep(b, l) \{\n        Rsb::B(n) => {inv "n"},\n    }\n}\n"
  -- Result types that bring the subset type's constraint through data,
  -- each now and then: a record's field, a newtype's, an enumeration's
  -- payload, an option's, and every element of a set or a sequence, which
  -- quantifies over them. Each body meets its type, and a caller reads the
  -- constraint.
  let forms : Array (String × String × String × String) := #[
    ("rs_rec", "Rsr", s!"pub struct Rsr \{ v: {ty}, k: Int }\n", inv "rs_rec(v, l).v"),
    ("rs_nt", "Rsn", s!"pub struct Rsn({ty})\n", inv "rs_nt(v, l).0"),
    ("rs_ch", "Rse", s!"pub enum Rse \{ A({ty}), Z }\n",
      s!"match rs_ch(v, l) \{ Rse::A(n) => {inv "n"}, Rse::Z => true }"),
    ("rs_opt", s!"Option<{ty}>", "",
      s!"match rs_opt(v, l) \{ Option::Some(n) => {inv "n"}, Option::None => true }"),
    ("rs_set", s!"Set<{ty}>", "", s!"forall (n: {base}), when n in rs_set(v, l), {inv "n"}"),
    ("rs_seq", s!"Seq<{ty}>", "", s!"forall (n: {base}), when n in rs_seq(v, l), {inv "n"}")]
  for (f, rt, decl, read) in forms do
    unless ← chance 30 do continue
    -- A `Nat`, or a subset type of one, is no type argument or element type.
    if base == "Nat" && rt.contains '<' then continue
    -- A collection's constraint quantifies over its elements.
    let opt := if rt.startsWith "Set" || rt.startsWith "Seq" then "set_option fren.lint.undecidable \"allow\" in\n" else ""
    let (x, a) ← pick #[("_", s!"{f}(v, r)"), ("x", s!"if x > 0 then {f}(v, r) else v")]
    out := out ++ decl ++ opt ++ s!"pub fn {f}(v: {rt}, l: Rsl): {rt} := match l \{\n" ++
      s!"    Rsl::Nil => v,\n    Rsl::Cons({x}, r) => {a},\n}\n" ++
      opt ++ s!"pub proc {f}_apps(v: {rt}, l: Rsl) \{\n    expect c: {read}\n}\n"
  -- A body wrong only at its induction step, which no caller applies: its
  -- obligation's model, at a recursive application, is never confirmed,
  -- so it is Inconclusive in both front ends, never `F0661`.
  if base != "Nat" && (← chance 30) then
    out := out ++ s!"pub fn rs_bad(p: {ty}, l: Rsl): {ty} := match l \{\n" ++
      "    Rsl::Nil => p,\n    Rsl::Cons(x, r) => if x > 0 then rs_bad(p, r) - 1 else p,\n}\n"
  return out

end FrenTest.FuzzFrontends.Wide
