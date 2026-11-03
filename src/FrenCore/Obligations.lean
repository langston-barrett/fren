-- keep-sorted start
import FrenCore.Check
import FrenCore.Evidence
-- keep-sorted end

/-!
# Obligations

What each check asks (`Reqs/Cli#obligations`): its context, the signature
and the sentences that its query may use, and its goal, after each front
end's instantiation and desugaring, with its evidence. `fren check
--dump=obligations` prints them, and so does the Lean-hosted front end with
`set_option fren.dump "obligations"`.

Both front ends take each check's question from `questionsOf`, give its
query's script as they would ask it, without asking it, and print them all
with `dump`, which makes every decision about their canonical form: which
commands are kept, how definitions are unfolded, and the order of
everything. So for the same spec, two front ends that build the same
queries print the same dump, and a difference between their dumps is a
difference between their queries.
-/

open Lean

namespace Fren.Core

/-! ## Questions -/

/-- A check's question: the hypotheses and goal of the query that it asks
first, of a kind `kind`, about `prop?`, with `part` telling apart the
questions of one check, such as an index's position. A `consistency`
question asks whether its hypotheses can hold together: its goal is the
backend's `falseF`. -/
structure Question (F : Type) where
  kind : CheckKind
  prop? : Option Name := none
  part : String := ""
  hyps : Array (Name × F)
  goal : F
  consistency : Bool := false

/-- Whether two questions are of the same check, and the same part of it. -/
def Question.same {F G : Type} (a : Question F) (b : Question G) : Bool :=
  a.kind == b.kind && a.prop? == b.prop? && a.part == b.part

variable {m : Type → Type} [Monad m] {F V : Type}

/-- The questions of the checks of `c` of the kinds `kinds`, in the order in
which `checkCompLawful` runs them, each with the hypotheses and goal of the
query that the check asks: the same as the check functions' own
(`checkRealizable`, `checkInst`, ...), which `FrenTest.Obligations` checks
against the queries that they ask. A question that a check asks only after
an answer, such as redundancy's after its consistency, is among them all
the same: the questions are what the checks ask, not what one run asked.
-/
def questionsOf (bk : CheckKind → Backend m F V) (c : Comp F) (kinds : Array CheckKind := CheckKind.all)
    (interprets : F → Bool := fun _ => false) : m (Array (Question F)) := do
  let mut out : Array (Question F) := #[]
  if kinds.contains .realizable then
    let b := bk .realizable
    let c := c.forKind .realizable
    if c.fixedInhabitation interprets then
      out := out.push { kind := .realizable, part := "inhabitation", hyps := c.defEqs .realizable ++ c.hyps b ++ c.reqs
                        goal := b.falseF, consistency := true }
    else
      let sub := c.substHyps b
      out := out.push { kind := .realizable, part := "assumptions", hyps := sub c.assumes, goal := b.falseF, consistency := true }
      out := out.push { kind := .realizable, part := "outputs", hyps := sub (c.hyps b)
                        goal := ← b.existsOutputs (c.subst b .realizable (b.conj (c.reqs.map (·.2)))) }
  if kinds.contains .inst then
    let b := bk .inst
    for (i, k) in c.insts.zipIdx do
      for a in i.assumes do
        out := out.push { kind := .inst, prop? := some i.name, part := s!"assumption {a.1}"
                          hyps := c.defEqs .inst ++ (c.hyps b k).push (i.name, i.bindings), goal := a.2 }
  if kinds.contains .expect then
    let b := bk .expect
    for e in c.expects do
      out := out.push { kind := .expect, prop? := some e.1, hyps := c.defEqs .expect ++ (c.hyps b ++ c.reqs), goal := e.2 }
  if kinds.contains .cover then
    let b := bk .cover
    for g in c.covers do
      out := out.push { kind := .cover, prop? := some g.1, hyps := c.defEqs .cover ++ (c.hyps b ++ c.reqs), goal := b.notF g.2 }
  if kinds.contains .vacuity then
    let b := bk .vacuity
    for t in c.triggers do
      out := out.push { kind := .vacuity, prop? := some t.1, hyps := c.defEqs .vacuity ++ (c.hyps b ++ c.reqs)
                        goal := b.notF t.2 }
  if kinds.contains .redundancy then
    let b := bk .redundancy
    let base := c.defEqs .redundancy
    if !(base ++ c.assumes).isEmpty then
      out := out.push { kind := .redundancy, part := "assumptions", hyps := base ++ c.assumes, goal := b.falseF
                        consistency := true }
    for a in c.assumes do
      out := out.push { kind := .redundancy, prop? := some a.1, hyps := base ++ c.assumes.filter (·.1 != a.1), goal := a.2 }
    if !c.reqs.isEmpty then
      out := out.push { kind := .redundancy, part := "constraints", hyps := base ++ (c.hyps b ++ c.reqs), goal := b.falseF
                        consistency := true }
    for r in c.reqs do
      out := out.push { kind := .redundancy, prop? := some r.1, hyps := base ++ (c.hyps b ++ c.reqs.filter (·.1 != r.1))
                        goal := r.2 }
  if kinds.contains .determinism then
    let b := bk .determinism
    for v in c.vars do
      if v.isDet then
        let once := c.defEqs .determinism ++ (c.hyps b ++ c.reqs)
        out := out.push { kind := .determinism, prop? := some v.name, hyps := once ++ once.map fun (n, f) => (primed n, b.prime f)
                          goal := b.samePrimed v.name }
  if kinds.contains .definedness then
    let b := bk .definedness
    for s in c.indexes do
      out := out.push { kind := .definedness, prop? := some s.prop, part := s!"index {s.k}"
                        hyps := c.defEqs .definedness ++ c.siteHyps b s, goal := s.goal }
  for k in [CheckKind.completeness, .disjointness, .precondition] do
    if kinds.contains k then
      let b := bk k
      for t in c.tablesOf k do
        out := out.push { kind := k, prop? := some t.site.prop, part := s!"site {t.site.k}", hyps := c.tableHyps b t
                          goal := t.site.goal }
  if kinds.contains .postcondition then
    for p in c.posts do
      out := out.push { kind := .postcondition, prop? := some p.1, hyps := c.assumes, goal := p.2 }
  if kinds.contains .reachability then
    let b := bk .reachability
    for t in c.tablesOf .reachability do
      out := out.push { kind := .reachability, prop? := some t.site.prop, part := s!"site {t.site.k}"
                        hyps := c.reachHyps b t.site, goal := t.site.goal }
  -- The vacuity under a trait's laws, where `checkCompLawful` asks it.
  if !(c.laws.isEmpty || (c.assumes.isEmpty && c.insts.isEmpty) || !kinds.contains .vacuity) then
    let b := bk .vacuity
    let parts := hypParts .vacuity true
    let call (i : Inst F) : Name × F :=
      if parts.callAssumptions then (i.name, b.conj #[i.bindings, i.behaviour])
      else (i.name, b.conj #[i.bindings, b.notF (b.conj #[b.conj (i.assumes.map (·.2)), b.notF i.behaviour])])
    let hyps := (if parts.laws then c.laws else #[]) ++ c.assumes ++ c.insts.map call
    out := out.push { kind := .vacuity, part := "laws", hyps := c.defEqs .vacuity ++ hyps, goal := b.falseF, consistency := true }
  return out

/-! ## S-expressions -/

/-- An SMT-LIB term or command, as the dump reads a query's script: an atom,
with any `|` quotes removed, or a list. -/
inductive Sx where
  | atom (s : String)
  | list (xs : Array Sx)
  deriving Inhabited, BEq, Hashable

partial def Sx.toString : Sx → String
  | .atom s => s
  | .list xs => "(" ++ " ".intercalate (xs.toList.map Sx.toString) ++ ")"

instance : ToString Sx := ⟨Sx.toString⟩

/-- The S-expressions of `cs` from `i`, up to an unmatched `)`, and where
they end, skipping comments, from `;` to the end of the line. -/
partial def Sx.parseAt (cs : Array Char) (i : Nat) : Array Sx × Nat := Id.run do
  let mut i := i
  let mut out := #[]
  while h : i < cs.size do
    let c := cs[i]
    if c.isWhitespace then i := i + 1
    else if c == ';' then
      while i < cs.size && cs[i]! != '\n' do i := i + 1
    else if c == ')' then return (out, i + 1)
    else if c == '(' then
      let (xs, j) := Sx.parseAt cs (i + 1)
      out := out.push (.list xs)
      i := j
    else if c == '"' then
      -- A string literal, in which `""` is a `"`.
      let mut j := i + 1
      while j < cs.size && !(cs[j]! == '"' && cs[j + 1]? != some '"') do
        j := if cs[j]! == '"' then j + 2 else j + 1
      out := out.push (.atom (String.ofList (cs.extract i (j + 1)).toList))
      i := j + 1
    else if c == '|' then
      let mut j := i + 1
      while j < cs.size && cs[j]! != '|' do j := j + 1
      out := out.push (.atom (String.ofList (cs.extract (i + 1) j).toList))
      i := j + 1
    else
      let mut j := i
      while j < cs.size && !(cs[j]!.isWhitespace || cs[j]! == '(' || cs[j]! == ')' || cs[j]! == ';') do j := j + 1
      out := out.push (.atom (String.ofList (cs.extract i j).toList))
      i := j
  return (out, i)

/-- `a` without Lean's `«»`, if they quote all of it, as lean-smt writes a
symbol that Lean's names quote, such as `«i#0»`. -/
def unguillemet (a : String) : String :=
  if a.startsWith "«" && a.endsWith "»" && a.length ≥ 2 && !((a.drop 1).dropEnd 1).contains '«' then
    ((a.drop 1).dropEnd 1).toString
  else a

/-- `a` without the `✝` that Lean's names of inaccessible locals end in, as
lean-smt names the locals that its preprocessing introduces, with any
superscript digits after it. -/
def withoutDagger (a : String) : String :=
  let t := (a.toList.reverse.dropWhile fun c => "⁰¹²³⁴⁵⁶⁷⁸⁹".toList.contains c).reverse
  match t.reverse with
  | '✝' :: rest@(_ :: _) => String.ofList rest.reverse
  | _ => a

/-- The S-expressions of `s`. -/
def Sx.parseAll (s : String) : Array Sx := (Sx.parseAt s.toList.toArray 0).1

/-- One of SMT-LIB's binding constructs, as a dump's scripts can contain
them, which every function below that knows of binding reads
(`Sx.binder?`): its `names`, its parts, each a term with the names bound
in it, and how to build it again with its names renamed and its parts
replaced. The constructs are:

- `forall`, `exists` and `lambda`, whose sorted variables are bound in
  their body, and whose sorts are parts in which nothing is bound;
- `let`, whose names are bound in its body, but not in its definitions;
- `match`, each of whose cases binds its pattern's variables, `x` in
  `((C x y) body)`, in its body; a pattern that is a symbol alone is
  taken for a constructor, which binds nothing.

The others bind only in declarations: a parametric datatype's `par` its
sort parameters, and a recursive definition, `define-fun-rec` or
`define-funs-rec`, its parameters, which `unfoldDecl` binds. -/
structure Binder where
  names : Array String
  parts : Array (Array String × Sx)
  rebuild : (String → String) → Array Sx → Sx

/-- The names of a pattern of a `match` case: its variables. -/
def patternVars : Sx → Array String
  | .list xs => (xs.extract 1).filterMap fun | .atom x => some x | _ => none
  | _ => #[]

/-- `e` as a binding construct (`Binder`), if it is one. -/
def Sx.binder? : Sx → Option Binder
  -- First, since a `match` on a list has the shape of the others.
  | .list #[q@(.atom "match"), t, .list cs] =>
    let cases := cs.filterMap fun | .list #[pat, b] => some (pat, b) | _ => none
    if cases.size != cs.size then none else
    let names := cases.foldl (init := #[]) fun acc (pat, _) =>
      (patternVars pat).foldl (fun acc x => if acc.contains x then acc else acc.push x) acc
    some { names, parts := #[(#[], t)] ++ cases.map fun (pat, b) => (patternVars pat, b)
           rebuild := fun f ps =>
             let renamePat : Sx → Sx := fun
               | .list xs => .list (xs.mapIdx fun i x => if i == 0 then x else match x with | .atom v => .atom (f v) | x => x)
               | pat => pat
             .list #[q, ps[0]?.getD t, .list (cases.zipWith (fun c b => Sx.list #[renamePat c.1, b]) (ps.extract 1))] }
  | .list #[q@(.atom k), .list bs, body] =>
    if k == "forall" || k == "exists" || k == "lambda" then
      let vs := bs.filterMap fun | .list #[.atom x, t] => some (x, t) | _ => none
      if vs.size != bs.size then none else
      let names := vs.map (·.1)
      some { names, parts := vs.map (fun v => (#[], v.2)) |>.push (names, body)
             rebuild := fun f ps => .list #[q, .list (vs.zipWith (fun v t => Sx.list #[.atom (f v.1), t]) ps), ps.back?.getD body] }
    else if k == "let" then
      let ds := bs.filterMap fun | .list #[.atom x, v] => some (x, v) | _ => none
      if ds.size != bs.size then none else
      let names := ds.map (·.1)
      some { names, parts := ds.map (fun d => (#[], d.2)) |>.push (names, body)
             rebuild := fun f ps => .list #[q, .list (ds.zipWith (fun d v => Sx.list #[.atom (f d.1), v]) ps), ps.back?.getD body] }
    else none
  | _ => none

/-- The names that `e` binds, if it is a binding construct (`Sx.binder?`). -/
def Sx.binds (e : Sx) : Array String := ((e.binder?).map (·.names)).getD #[]

/-- The atoms of `e` that no binder within it binds (`Sx.binder?`). -/
partial def Sx.freeAtoms (e : Sx) (bound : Array String := #[]) (acc : Std.HashSet String := {}) : Std.HashSet String :=
  match e with
  | .atom a => if bound.contains a then acc else acc.insert a
  | .list xs => match e.binder? with
    | some b => b.parts.foldl (init := acc) fun acc (ns, p) => p.freeAtoms (bound ++ ns) acc
    | none => xs.foldl (init := acc) fun acc x => x.freeAtoms bound acc

/-- The first of `x#s0`, `x#s1`, … that `avoid` does not have: a bound
name renamed apart. No Fren name has `#`, and no front end writes `#s`. -/
def freshName (x : String) (avoid : Std.HashSet String) : String := Id.run do
  for k in [0:avoid.size + 1] do
    let c := s!"{x}#s{k}"
    unless avoid.contains c do return c
  return s!"{x}#s{avoid.size + 1}"

/-- `b`'s names renamed apart where they are in `captured`, avoiding
`avoid`: the renaming, as a function and as a substitution. -/
def Binder.apart (b : Binder) (captured avoid : Std.HashSet String) : (String → String) × Array (String × Sx) := Id.run do
  let mut avoid := b.names.foldl (·.insert ·) avoid
  let mut ren : Array (String × String) := #[]
  for x in b.names do
    if captured.contains x then
      let x' := freshName x avoid
      avoid := avoid.insert x'
      ren := ren.push (x, x')
  let f := fun x => ((ren.find? (·.1 == x)).map (·.2)).getD x
  return (f, ren.map fun (x, x') => (x, .atom x'))

/-- `e` with each free atom of `σ` replaced by its value, without capture:
a binder (`Sx.binder?`) that would capture a free name of a value that a
part of it uses has its bound name renamed apart (`freshName`). -/
partial def Sx.subst (σ : Array (String × Sx)) (e : Sx) : Sx :=
  if σ.isEmpty then e else
  match e with
  | .atom a => ((σ.find? (·.1 == a)).map (·.2)).getD e
  | .list xs => match e.binder? with
    | none => .list (xs.map (·.subst σ))
    | some b =>
      -- The values that a part uses, where its names do not hide them, and
      -- the bound names of that part that they have free.
      let captured := b.parts.foldl (init := ({} : Std.HashSet String)) fun acc (ns, p) =>
        let free := p.freeAtoms
        (σ.filter fun (x, _) => !ns.contains x && free.contains x).foldl (init := acc) fun acc (_, v) =>
          (v.freeAtoms #[]).fold (fun acc y => if ns.contains y then acc.insert y else acc) acc
      let avoid := b.parts.foldl (init := σ.foldl (init := {}) fun acc (_, v) => v.freeAtoms #[] acc)
        fun acc (_, p) => p.freeAtoms #[] acc
      let (f, ren) := b.apart captured avoid
      b.rebuild f (b.parts.map fun (ns, p) =>
        (p.subst (ren.filter fun (x, _) => ns.contains x)).subst (σ.filter fun (x, _) => !ns.contains x))

/-- The integer that `e` is, if it is a literal: a numeral or its negation. -/
def Sx.int? : Sx → Option Int
  | .atom a => a.toNat?.map Int.ofNat
  | .list #[.atom "-", .atom a] => a.toNat?.map fun n => -Int.ofNat n
  | _ => none

/-- The atoms of `e`, bound or free, added to `acc`. -/
partial def Sx.atomsInto (e : Sx) (acc : Std.HashSet String) : Std.HashSet String :=
  match e with
  | .atom a => acc.insert a
  | .list xs => xs.foldl (fun acc x => x.atomsInto acc) acc

/-- `e` with each atom renamed by `symbols`. -/
partial def Sx.rename (symbols : Std.HashMap String String) : Sx → Sx
  | .atom a => .atom (symbols.getD a a)
  | .list xs => .list (xs.map (Sx.rename symbols))

/-- The conjuncts of `e`, with those of each conjunction in it. -/
partial def Sx.conjuncts : Sx → Array Sx
  | .list xs => if xs[0]? == some (.atom "and") then (xs.extract 1).flatMap Sx.conjuncts else #[.list xs]
  | e => #[e]

/-- The canonical name of a newtype's constructor and of its field, which
`fren check` erases (`Reqs/Lang/Items#newtypes`): `Sx.normalize` writes
an application of either as its argument, and `canonical` leaves out a
datatype's declaration that mentions it, the newtype's. A front end that does not erase newtypes
maps them to it, and the newtype itself to its underlying type's sort. -/
def erasedSymbol : String := "#erased"

/-- The operators whose nested applications `Sx.normalize` flattens. -/
def associative : List String := ["and", "or", "+", "*", "seq.++", "str.++"]

/-- `e` written as both front ends could: with each atom renamed by
`symbols` (which `canonical` gives without `«»` (`unguillemet`) and `✝`
(`withoutDagger`), where no two names would then be one);
each `declare-datatype` as the `declare-datatypes` of one datatype, as
lean-smt declares them; each conjunction of conjunctions as one; each
implication whose conclusion is an implication, `(=> a (=> b c))`, as
`(=> (and a b) c)`; each `let`'s definitions
substituted into its body, as Lean's `zetaReduce` substitutes them; and
each quantifier directly over another of its kind as one over both's
bound names, where they are distinct; each application of an associative operator to an
application of itself as one application; a binary `distinct` as the
negation of `=`, and a double negation as what it negates; an equation
with `true` or `false` as the other side or its negation; and `<=` and
`<` as `>=` and `>`, with their sides swapped; and a comparison of two
integer literals, a negation, a conjunction or disjunction with `true` or
`false`, and a conditional on `true` or `false`, as what it is, as
lean-smt's preprocessing simplifies them. None of these changes what the
formula means. -/
partial def Sx.normalize (symbols : Std.HashMap String String) : Sx → Sx
  | .atom a => .atom (symbols.getD a a)
  | .list xs =>
    let xs := xs.map (Sx.normalize symbols)
    if xs.size == 2 && xs[0]? == some (.atom erasedSymbol) then xs[1]! else
    match xs with
    | #[.atom "declare-datatype", n, body] =>
      let arity : Nat := match body with
        | Sx.list #[Sx.atom "par", Sx.list ps, _] => ps.size
        | _ => 0
      .list #[.atom "declare-datatypes", .list #[.list #[n, .atom s!"{arity}"]], .list #[body]]
    | #[.atom "=>", a, .list #[.atom "=>", b, c]] =>
      .list #[.atom "=>", .list (#[.atom "and"] ++ a.conjuncts ++ b.conjuncts), c]
    | #[.atom "let", .list bs, body] =>
      let σ := bs.filterMap fun | .list #[.atom x, v] => some (x, v) | _ => none
      if σ.size == bs.size then body.subst σ else .list xs
    | #[q@(.atom "forall"), .list bs, inner@(.list #[.atom q', .list bs', body])]
    | #[q@(.atom "exists"), .list bs, inner@(.list #[.atom q', .list bs', body])] =>
      -- Only where no name is bound twice, which would be no binder list.
      let outer := (Sx.list #[q, .list bs, .atom "true"]).binds
      if q == .atom q' && !inner.binds.any outer.contains then .list #[q, .list (bs ++ bs'), body] else .list xs
    | #[.atom "distinct", a, b] => (Sx.list #[.atom "not", .list #[.atom "=", a, b]]).normalize {}
    | #[.atom "not", .list #[.atom "not", a]] => a
    | #[.atom "=", a, .atom "true"] | #[.atom "=", .atom "true", a] => a
    | #[.atom "=", a, .atom "false"] | #[.atom "=", .atom "false", a] => .list #[.atom "not", a]
    | #[.atom "<=", a, b] => (Sx.list #[.atom ">=", b, a]).normalize {}
    | #[.atom "<", a, b] => (Sx.list #[.atom ">", b, a]).normalize {}
    | #[.atom ">=", a, b] => match a.int?, b.int? with
      | some i, some j => .atom (if i ≥ j then "true" else "false")
      | _, _ => .list xs
    | #[.atom ">", a, b] => match a.int?, b.int? with
      | some i, some j => .atom (if i > j then "true" else "false")
      | _, _ => .list xs
    | #[.atom "not", .atom "true"] => .atom "false"
    | #[.atom "not", .atom "false"] => .atom "true"
    | #[.atom "ite", .atom "true", a, _] => a
    | #[.atom "ite", .atom "false", _, b] => b
    | xs => match xs[0]? with
      | some (Sx.atom op) =>
        -- An associative operator applied to an application of itself, as
        -- one application.
        if associative.contains op then
          let args := (xs.extract 1).flatMap fun
            | .list ys => if ys[0]? == some (.atom op) then ys.extract 1 else #[.list ys]
            | y => #[y]
          -- A conjunction or disjunction with a literal `true` or `false`.
          if op == "and" || op == "or" then
            let (unit, zero) := if op == "and" then ("true", "false") else ("false", "true")
            if args.contains (.atom zero) then .atom zero else
            match args.filter (· != .atom unit) with
            | #[] => .atom unit
            | #[a] => a
            | args => .list (#[.atom op] ++ args)
          else .list (#[.atom op] ++ args)
        else .list xs
      | _ => .list xs

/-- `e` with each application of a definition of `defs`, by its name, to as
many arguments as it has parameters, and each mention of one without
parameters, replaced by its body, without capture: a name that `bound`
or a binder within `e` binds is not a definition's, and a binder that
would capture a free name of a body it holds has its bound name renamed
apart (`freshName`). The bodies are unfolded already. -/
partial def Sx.unfold (defs : Std.HashMap String (Array String × Sx)) (e : Sx) (bound : Array String := #[]) : Sx :=
  if defs.isEmpty then e else
  match e with
  | .atom a => if bound.contains a then e else match defs[a]? with
    | some (#[], body) => body
    | _ => e
  | .list xs =>
    if let some b := e.binder? then
      -- The definitions that a part uses, and the free names of their
      -- bodies, which a name bound in that part would capture.
      let captured := b.parts.foldl (init := ({} : Std.HashSet String)) fun acc (ns, p) =>
        (p.freeAtoms (bound ++ ns)).fold (init := acc) fun acc a => match defs[a]? with
          | some (ps, body) => (body.freeAtoms ps).fold (fun acc y => if ns.contains y then acc.insert y else acc) acc
          | none => acc
      let avoid := b.parts.foldl (init := bound.foldl (·.insert ·) {}) fun acc (_, p) => p.freeAtoms #[] acc
      let avoid := defs.fold (init := avoid) fun acc _ (ps, body) => body.freeAtoms ps acc
      let (f, ren) := b.apart captured avoid
      b.rebuild f (b.parts.map fun (ns, p) =>
        (p.subst (ren.filter fun (x, _) => ns.contains x)).unfold defs (bound ++ ns.map f))
    else
    let xs := xs.map (·.unfold defs bound)
    match xs[0]? with
    | some (Sx.atom f) => if bound.contains f then .list xs else match defs[f]? with
      | some (ps, body) =>
        if ps.size + 1 == xs.size && !ps.isEmpty then body.subst (ps.zip (xs.extract 1)) else .list xs
      | none => .list xs
    | _ => .list xs

/-! ## Canonical names -/

/-- What a symbol of a query that is not a variable stands for: a spec's
type, constructor, selector, function or abstract type. -/
inductive ItemSymbol where
  /-- An enumeration or a record. -/
  | datatype (path : Name)
  /-- A variant of an enumeration. -/
  | variant (path : Name) (v : Name)
  /-- The `k`th value of a variant's payload. -/
  | payload (path : Name) (v : Name) (k : Nat)
  /-- A record's constructor. -/
  | record (path : Name)
  | field (path : Name) (f : Name)
  /-- A function, or an abstract type. -/
  | item (path : Name)

/-- The canonical name of a symbol, which the dump prints for it
(`Reqs/Cli#obligations`): the one that `fren check` gives the solver
(`FrenCli.ctorSym` and the others), without its `|`s, which
`FrenTest.Obligations` checks. -/
def ItemSymbol.text : ItemSymbol → String
  | .datatype p => ((userSortSym (showPath p)).drop 1 |>.dropEnd 1).toString
  | .variant p v => s!"{showPath p}::{v}"
  | .payload p v k => s!"{showPath p}::{v}::{k}"
  | .record p => s!"{showPath p}\{}"
  | .field p f => s!"{showPath p}::{f}"
  | .item p => s!"::{showPath p}"

/-! ## Canonical obligations -/

/-- A query's context and goal, as the dump prints them (`canonical`). -/
structure QueryContext where
  /-- Its declarations: of sorts, datatypes, constants, functions and
  recursive definitions, each once, in order of their text. -/
  signature : Array String
  /-- Its sentences, each once, in order of their text. -/
  sentences : Array String
  goal : String
  deriving Inhabited, BEq

/-- `l` with each run of equal neighbours as one. -/
def dedupAdjacent {α : Type} [BEq α] : List α → List α
  | a :: b :: rest => if a == b then dedupAdjacent (b :: rest) else a :: dedupAdjacent (b :: rest)
  | l => l

/-- Each of `xs` once, in the order `le` (`cli::canonical_sentences`): how
the dump prints a context's declarations and sentences, which neither
their order nor a repeated one changes. -/
def sortedOnce {α : Type} [BEq α] (le : α → α → Bool) (xs : Array α) : Array α :=
  (dedupAdjacent (xs.toList.mergeSort le)).toArray

/-- Texts in order: by their characters. -/
def textLe (a b : String) : Bool := !(b < a)

/-- The names of a list of sorted variables, `((x Int) (y Bool))`. -/
def sortedVars : Sx → Array String
  | .list vs => vs.filterMap fun | .list #[.atom x, _] => some x | _ => none
  | _ => #[]

/-- The declaration `cmd` with the definitions of `defs` unfolded in it
(`Sx.unfold`), with the names that it binds itself bound: a recursive
definition's parameters, whose names stay and whose sorts are unfolded,
in its body, and a parametric datatype's sort parameters. The other names that a declaration has are its own, which no
definition of the same script has. -/
def unfoldDecl (defs : Std.HashMap String (Array String × Sx)) (cmd : Sx) : Sx :=
  match cmd with
  | .list #[h@(.atom "define-fun-rec"), f, ps, s, body] =>
    let bound := sortedVars ps
    .list #[h, f, unfoldSorts ps, s.unfold defs, body.unfold defs bound]
  | .list #[h@(.atom "define-funs-rec"), .list decls, .list bodies] =>
    let bodies := bodies.zipWith (fun (b : Sx) (d : Sx) => match d with
      | .list #[_, ps, _] => b.unfold defs (sortedVars ps)
      | _ => b.unfold defs) decls
    .list #[h, .list (decls.map fun
      | .list #[f, ps, r] => Sx.list #[f, unfoldSorts ps, r.unfold defs]
      | d => d), .list bodies]
  | .list #[h@(.atom "declare-datatypes"), sorts, .list dts] =>
    .list #[h, sorts, .list (dts.map fun
      | .list #[p@(.atom "par"), .list ps, body] =>
        Sx.list #[p, .list ps, body.unfold defs (ps.filterMap fun | .atom x => some x | _ => none)]
      | dt => dt.unfold defs)]
  | .list #[h@(.atom "declare-datatype"), n, .list #[p@(.atom "par"), .list ps, body]] =>
    .list #[h, n, .list #[p, .list ps, body.unfold defs (ps.filterMap fun | .atom x => some x | _ => none)]]
  | cmd => cmd.unfold defs
where
  /-- A list of sorted variables with only their sorts unfolded. -/
  unfoldSorts : Sx → Sx
    | .list vs => .list (vs.map fun
      | .list #[x, t] => Sx.list #[x, t.unfold defs]
      | v => v)
    | e => e

/-- The commands of a script that say nothing of what a query asks: its
logic, options and the solver's commands. -/
def solverCommands : List String :=
  ["set-logic", "set-option", "set-info", "check-sat", "reset", "get-model", "get-value", "exit", "push", "pop"]

/-- What the script `script` of a query asks, canonically: without its
logic, options and solver commands; with each non-recursive definition
(`define-fun`) unfolded where it is used, and dropped, since one front end
gives the solver a function's definition and the other its body; with its
declarations and its sentences each once and sorted, since neither their
order nor a repeated one changes the query; and with its goal apart. The
goal of a question that is not one of `consistency` is the negation of its
last assertion, which is the goal's negation, `(not G)`; a question of
`consistency` has the goal `false`, which a front end may leave out, as it
leaves out every sentence `true` or `(not false)`. Texts are in `String`'s
order (`textLe`), which is total. -/
def canonical (script : String) (consistency : Bool) (symbols : Std.HashMap String String := {}) : QueryContext := Id.run do
  let mut defs : Std.HashMap String (Array String × Sx) := {}
  let mut sig : Array Sx := #[]
  let mut asserts : Array Sx := #[]
  -- Lean's `«»` and `✝` go from each name, but where two names would be
  -- one without them, which would merge two constants or bound names.
  let renamed := (Sx.parseAll script).map (·.rename symbols)
  let atoms := renamed.foldl (init := ({} : Std.HashSet String)) fun acc c => c.atomsInto acc
  let plain (a : String) := withoutDagger (unguillemet a)
  let count := atoms.fold (init := ({} : Std.HashMap String Nat)) fun m a => m.insert (plain a) (m.getD (plain a) 0 + 1)
  let strips := atoms.fold (init := ({} : Std.HashMap String String)) fun m a =>
    if plain a != a && count.getD (plain a) 0 == 1 then m.insert a (plain a) else m
  for raw in Sx.parseAll script do
    -- A newtype's declaration, which `fren check` erases, goes, as its
    -- renamed symbols show (`erasedSymbol`).
    let declares := match raw with
      | .list xs => xs[0]? == some (.atom "declare-datatypes") || xs[0]? == some (.atom "declare-datatype")
      | _ => false
    if declares && (raw.rename symbols).freeAtoms.contains erasedSymbol then continue
    let cmd := (raw.rename symbols).normalize strips
    let .list xs := cmd | continue
    let some (Sx.atom head) := xs[0]? | continue
    if solverCommands.contains head then continue
    match head, xs.toList with
    -- A sort's definition, as a definition without parameters.
    | "define-sort", [_, .atom f, .list #[], body] => defs := defs.insert f (#[], body)
    | "define-fun", [_, .atom f, .list ps, _, body] =>
      let ps := ps.filterMap fun | .list #[.atom x, _] => some x | _ => none
      -- Its parameters are bound in its body, so no definition is theirs.
      defs := defs.insert f (ps, (body.unfold defs ps).normalize {})
    -- Written again as both front ends could, once unfolded: an argument
    -- may make a new instance of a rule of `Sx.normalize`.
    | "assert", [_, t] => asserts := asserts.push ((t.unfold defs).normalize {})
    | _, _ => sig := sig.push ((unfoldDecl defs cmd).normalize {})
  let trivial (t : Sx) := t == .atom "true" || t == .list #[.atom "not", .atom "false"]
  -- The last assertion is the goal's negation, which `Sx.normalize` may
  -- have rewritten, as `(not (not g))` to `g`: the goal is its negation,
  -- written as both front ends could.
  let (goal, sentences) := if consistency then (Sx.atom "false", asserts) else
    match asserts.back? with
    | some t => ((Sx.list #[.atom "not", t]).normalize {}, asserts.pop)
    | none => (.atom "false", asserts)
  -- A conjunction is as many sentences, as lean-smt splits a hypothesis.
  let sentences := (sentences.flatMap Sx.conjuncts).filter (!trivial ·)
  -- A constant or function that nothing else mentions cannot change the
  -- query, and one front end declares some of those that the other does
  -- not, such as an output that only a binder names.
  let used := sentences.foldl (init := goal.freeAtoms) fun acc t => t.freeAtoms #[] acc
  let used := sig.foldl (init := used) fun acc d => match d with
    | .list xs => if xs[0]? == some (.atom "declare-const") || xs[0]? == some (.atom "declare-fun") then acc
      else d.freeAtoms #[] acc
    | _ => acc
  let declared := sig.filter fun d => match d with
    | .list xs => !(xs[0]? == some (.atom "declare-const") || xs[0]? == some (.atom "declare-fun"))
      || (match xs[1]? with | some (Sx.atom f) => used.contains f | _ => true)
    | _ => true
  return { signature := sortedOnce textLe (declared.map toString), sentences := sortedOnce textLe (sentences.map toString)
           goal := toString goal }

/-- An obligation, as a front end gives it to `dump`: a question of the item
`comp`, the script of its query as the front end would ask it, its
evidence, as `set_option fren.evidence` writes it, and where it is
written, as metadata. -/
structure Obligation where
  comp : Name
  kind : CheckKind
  prop? : Option Name := none
  part : String := ""
  consistency : Bool := false
  evidence : String := "solver"
  script : String
  /-- Where its constraint, or its item, is written, as `line:column`:
  metadata, which `withoutMetadata` drops. -/
  span? : Option String := none
  /-- The canonical name (`ItemSymbol.text`) of each symbol of the script
  that the front end names otherwise. -/
  symbols : Std.HashMap String String := {}
  deriving Inhabited

/-- The obligation of the question `q` of `comp`, with the script of its
query. -/
def Question.obligation (q : Question F) (comp : Name) (script : String) (evidence := "solver") (span? : Option String := none)
    (symbols : Std.HashMap String String := {}) : Obligation :=
  { comp, kind := q.kind, prop? := q.prop?, part := q.part, consistency := q.consistency, evidence, script, span?, symbols }

/-- The evidence of a check, as `set_option fren.evidence` writes it: the
solver's, if `solver` (its question is among those that the solver is
asked, once its checks set to testing and enumeration are taken out,
`Comp.untested`), and otherwise by whether `tested` and `enumerated` cover
it. -/
def evidenceName (solver tested enumerated : Bool) : String :=
  if solver then "solver"
  else if tested && enumerated then "enumerated+random"
  else if enumerated then "enumerated"
  else if tested then "random"
  else "solver"

/-- The item that the dump names `c`'s obligations after: a function's body
or contract, which is checked as an item whose path is its module's, after
the function, by its path (`fn?`, which is within the module); any other
item by its own path. -/
def itemName (c : Comp F) : Name :=
  match c.fn? with
  | some f => if c.path.isPrefixOf f then f else c.path ++ f
  | none => c.path

/-- The obligations of `c`, with the checks `kinds`, of which those set to
testing or enumeration, `tested` and `enumerated`, have their evidence:
`questionsOf` of `c`, with their scripts, as `script` gives them for each
kind. A question that the solver is asked has the hypotheses and goal that
it is asked them with, those of `c.untested`, which can differ from `c`'s:
`Comp.untested` clears the assumptions of a call set to testing or
enumeration, which a vacuity question reads. `spanOf` gives where a
constraint, or the item itself, is written, and `symbols` the canonical
name of each of the front end's symbols that `ItemSymbol.text` names
otherwise. -/
def obligationsOf (bk : CheckKind → Backend m F V) (script : CheckKind → Array (Name × F) → F → m String)
    (c : Comp F) (kinds : Array CheckKind) (tested enumerated : Tested) (interprets : F → Bool := fun _ => false)
    (spanOf : Option Name → Option String := fun _ => none) (symbols : Std.HashMap String String := {}) :
    m (Array Obligation) := do
  let all ← questionsOf bk c kinds interprets
  let (solved, solverKinds) := c.untested (tested.union enumerated) kinds
  let bySolver ← questionsOf bk solved solverKinds interprets
  all.mapM fun q => do
    let r : CheckResult := { kind := q.kind, comp := c.path, prop? := q.prop?, verdict := .pass }
    let asked? := bySolver.find? (·.same q)
    let evidence := evidenceName asked?.isSome (tested.covers r) (enumerated.covers r)
    let q := asked?.getD q
    let item := itemName c
    return q.obligation item (← script q.kind q.hyps q.goal) evidence (spanOf q.prop?) symbols

/-- The check that an obligation is of, as the dump names it:
`(check KIND [PROP] [PART])`. -/
def Obligation.checkText (o : Obligation) : String :=
  let prop := (o.prop?.map fun n => s!" {n.toString (escape := false)}").getD ""
  let part := if o.part.isEmpty then "" else s!" ({o.part})"
  s!"(check {kindName o.kind}{prop}{part})"

/-- An obligation as the dump prints it: its item, its check, its evidence,
then its context and goal (`canonical`), with where it is written as a
comment. -/
def Obligation.render (o : Obligation) : String :=
  let cx := canonical o.script o.consistency o.symbols
  let block (name : String) (xs : Array String) : String :=
    if xs.isEmpty then s!"  ({name})\n" else s!"  ({name}\n" ++ String.join (xs.toList.map (s!"    {·}\n")) ++ "  )\n"
  s!"(obligation\n" ++ ((o.span?.map (s!"  ; at {·}\n")).getD "")
    ++ s!"  (item {showComp o.comp})\n  {o.checkText}\n  (evidence {o.evidence})\n"
    ++ block "signature" cx.signature ++ block "context" cx.sentences ++ s!"  (goal {cx.goal})\n)\n"

/-- The script of a query that a front end could not build, with why: an
`(error ...)` command, which the dump shows among the declarations. -/
def errorScript (why : String) : String := s!"(error \"{why.replace "\"" "\"\""}\")"

/-- The first line of a dump of obligations, and its last, by which a
dump is found in a front end's output. -/
def dumpStart : String := "; obligations"
def dumpEnd : String := "; end of obligations"

/-- `text`, a dump, without its metadata: its comments, but its first and
last lines. Two front ends' dumps of a spec are compared so. -/
def withoutMetadata (text : String) : String :=
  "\n".intercalate ((text.splitOn "\n").filter fun l => !l.trimAscii.toString.startsWith "; at ")

/-- The obligations dump of a spec, from each front end's obligations of
its items: each obligation rendered (`Obligation.render`), in order of its
item's path, then of its place among its item's, which `questionsOf`
gives; an item checked twice, as a function's body and its contract are,
in order of their checks, then of their text without its metadata
(`withoutMetadata`), so that where they are written does not order them. -/
def dump (items : Array (Array Obligation)) : String :=
  let keyed := items.filterMap fun os => os[0]?.map fun o =>
    let text := String.join (os.toList.map (·.render))
    (showComp o.comp, String.join (os.toList.map (·.checkText)), withoutMetadata text, text)
  let sorted := keyed.qsort fun (p, k, a, _) (q, l, b, _) => p < q || (p == q && (k < l || (k == l && a < b)))
  s!"{dumpStart}\n" ++ String.join (sorted.toList.map (·.2.2.2 ++ "\n")) ++ s!"{dumpEnd}\n"

end Fren.Core
