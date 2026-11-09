module

public import FrenModule.Core

/-! A generator of THIR modules that are well typed by construction (each node
is generated at the type it must have), whose erasure is the HIR input of
`FrenHirToThir`; and of ill-typed variants with exactly one injected fault,
together with the error the type checker must report for it.

The generator is written over any monad with a source of choices, so the same
code runs under Plausible's `Gen` and under a seeded `StdGen` for censuses.

Programs are generated so that they also print as Fren source whose parse is
the same tree: an operand or scrutinee that is not atomic is wrapped in a
parenthesis node, and a `let` in a `let` value or `match` arm is too. Locals
are named by depth (`p<i>` for parameters, `x<depth>` for `let`s), so every
name is unique along its scope chain. -/

public section
namespace FrenGen.Thir

open FrenExpr FrenModule.Core
open FrenAst (UnaryOp BinaryOp)

/-- The faults a generated program can carry, one at most. -/
inductive Fault where
  /-- A literal of another type where the context fixes the type. -/
  | swap
  /-- A call with one argument too few or too many. -/
  | arity
  /-- A constructor as a callee. -/
  | ctorCallee
  /-- A function name in value position. -/
  | fnValue
  /-- A local index past every enclosing binder (not printable as source). -/
  | dangling
  /-- A pattern from another enum. -/
  | wrongPattern
  | emptyMatch
  /-- A `?`-suffixed `let` whose value is not `Bool`. -/
  | letSuffix
  /-- A `?`-suffixed parameter whose written type is not `Bool`. -/
  | paramSuffix
  deriving Repr, BEq, DecidableEq, Inhabited

def Fault.all : List Fault :=
  [.swap, .arity, .ctorCallee, .fnValue, .dangling, .wrongPattern, .emptyMatch, .letSuffix, .paramSuffix]

/-- Faults whose program prints as source that parses and resolves. -/
def Fault.printable : Fault → Bool
  | .dangling => false
  | _ => true

/-- The error a faulty program must be rejected with. -/
inductive Outcome where
  | mismatch (expected found : Ty)
  | notValue (id : FrenBase.ItemId)
  | notCallable (id : FrenBase.ItemId)
  | arity (expected found : Nat)
  | dangling (index : Nat)
  | matchNotEnum (found : Ty)
  | emptyMatch
  deriving Repr, BEq, DecidableEq

structure Expected where
  fault : Fault
  item : FrenBase.ItemId
  origin : OriginId
  outcome : Outcome
  deriving Repr, BEq

/-- What a generated case is: the THIR module (the type checker's expected
output when there is no fault) and the fault's expected error. -/
structure Case where
  thir : Thir
  expected : Option Expected

/-- The module the HIR input comes from. -/
@[expose] def Case.hir (c : Case) : Hir := c.thir.eraseTypes

structure Shape where
  module : FrenBase.ItemId
  enums : Array Enum
  /-- Function id, parameter types and result type. -/
  functions : Array (FrenBase.ItemId × Array Ty × Ty)

structure St where
  origins : Array Origin := #[]
  item : FrenBase.ItemId := FrenBase.ItemId.root
  /-- The fault still to inject, and how many eligible sites to pass first. -/
  pending : Option Fault := none
  countdown : Nat := 0
  injected : Option Expected := none
  /-- How many nodes of each form were generated (for censuses). -/
  forms : Array Nat := Array.replicate 16 0

variable {m : Type → Type} [Monad m]

abbrev G (m : Type → Type) := StateT St m

section
variable (pick : Nat → m Nat)

def below (n : Nat) : G m Nat := do
  if n ≤ 1 then return 0
  let k ← (pick n : m Nat)
  return k % n

def coin : G m Bool := return (← below pick 2) == 0

def oneOf (xs : Array α) (default : α) : G m α := do
  return xs[← below pick xs.size]?.getD default

def fresh (name : Option String := none) : G m OriginId :=
  modifyGet fun s => (s.origins.size, {s with origins := s.origins.push {name}})

def count (form : Nat) : G m Unit :=
  modify fun s => {s with forms := s.forms.modify form (· + 1)}

/-- Whether the pending fault is `f` and this eligible site is the one. -/
def takeFault (f : Fault) : G m Bool := do
  let s ← get
  if s.pending != some f then return false
  if s.countdown > 0 then
    set {s with countdown := s.countdown - 1}
    return false
  set {s with pending := none}
  return true

def record (f : Fault) (origin : OriginId) (outcome : Outcome) : G m Unit :=
  modify fun s => {s with injected := some ⟨f, s.item, origin, outcome⟩}

end

private theorem thirTyped : Phase.Typed .thir := by decide
private theorem thirSurface : Phase.Surface .thir := Or.inr rfl

def mk (o : OriginId) (ty : Ty) (n : ExprF .thir (Expr .thir)) : Expr .thir := ⟨o, ty, n⟩

def atomic (e : Expr .thir) : Bool :=
  match e.node with
  | .bool _ | .int _ | .var _ | .ctor _ _ | .call _ _ _ | .paren _ _ | .item _ _ | .apply _ _ _ => true
  | _ => false

def isLet (e : Expr .thir) : Bool := match e.node with | .letE _ _ _ => true | _ => false

/-- Form indices for the census. -/
def formNames : Array String :=
  #["bool", "int", "var", "ctor", "call", "unary", "binary", "if", "let", "match", "paren",
    "eq-enum", "suffix-let", "nested-let-ref", "multi-arm", "fault"]

section
variable (pick : Nat → m Nat) (shape : Shape)

def wrapIf (cond : Bool) (e : Expr .thir) : G m (Expr .thir) := do
  if !cond then return e
  count 10
  return mk (← fresh) e.ann (.paren thirSurface e)

def literal (t : Ty) : G m (Expr .thir) := do
  match t with
  | .bool => count 0; return mk (← fresh) .bool (.bool (← coin pick))
  | .int => count 1; return mk (← fresh) .int (.int (← below pick 20))
  | .enum id =>
    count 3
    let ctors := ((shape.enums.find? (·.id == id)).map (·.ctors)).getD #[]
    return mk (← fresh) t (.ctor thirTyped (← oneOf pick ctors FrenBase.ItemId.root))

/-- A literal of a type other than `t`. -/
def otherLiteral (t : Ty) : G m (Expr .thir) :=
  literal pick shape (if t == .bool then .int else .bool)

/-- A leaf of type `t`: a literal or a local of that type; or a fault. -/
def leaf (ctx : List Ty) (t : Ty) : G m (Expr .thir) := do
  if ← takeFault .fnValue then
    let some (fn, _, _) := shape.functions[0]? | return ← literal pick shape t
    let o ← fresh
    record .fnValue o (.notValue fn)
    count 15
    return mk o t (.ctor thirTyped fn)
  if ← takeFault .dangling then
    let o ← fresh
    let i := ctx.length + (← below pick 3)
    record .dangling o (.dangling i)
    count 15
    return mk o t (.var i)
  let locals := (ctx.zipIdx.filter (·.1 == t)).map (·.2)
  if !locals.isEmpty && (← coin pick) then
    count 2
    let i ← oneOf pick locals.toArray 0
    if i > 0 then count 13
    return mk (← fresh) t (.var i)
  literal pick shape t

def randomType : G m Ty := do
  let k ← below pick (2 + shape.enums.size)
  return match k with
    | 0 => .bool
    | 1 => .int
    | k => .enum ((shape.enums[k - 2]?.map (·.id)).getD FrenBase.ItemId.root)

mutual

/-- A child at a position whose type the parent fixes: where the swap fault
applies. `wrap` asks for parentheses around a non-atomic child. -/
def fixed (ctx : List Ty) (t : Ty) (d : Nat) (wrap : Bool) : G m (Expr .thir) := do
  if ← takeFault .swap then
    let e ← otherLiteral pick shape t
    record .swap e.origin (.mismatch t e.ann)
    count 15
    return e
  let e ← expr ctx t d
  wrapIf (wrap && !atomic e) e
termination_by 2 * d + 1

/-- An expression of type `t` with depth at most `d`. -/
def expr (ctx : List Ty) (t : Ty) (depth : Nat) : G m (Expr .thir) :=
  match depth with
  | 0 => leaf pick shape ctx t
  | d + 1 => do
    let calls := shape.functions.filter (·.2.2 == t)
    let k ← below pick 9
    match k with
    | 0 => leaf pick shape ctx t
    | 1 => do
      count 10
      let e ← expr ctx t d
      return mk (← fresh) t (.paren thirSurface e)
    | 2 => do
      count 7
      let c ← fixed ctx .bool d false
      let y ← expr ctx t d
      let n ← fixed ctx t d false
      return mk (← fresh) t (.ite c y n)
    | 3 => do
      count 8
      let vt ← randomType pick shape
      let v ← expr ctx vt d
      let v ← wrapIf (isLet v) v
      let faulty ← if vt != .bool then takeFault .letSuffix else pure false
      let suffix := faulty || (vt == .bool && (← coin pick))
      if suffix then count 12
      let depth := ctx.length
      let b ← fresh (some s!"x{depth}{if suffix then "?" else ""}")
      if faulty then
        record .letSuffix b (.mismatch .bool vt)
        count 15
      let body ← expr (vt :: ctx) t d
      return mk (← fresh) t (.letE ⟨b, suffix⟩ v body)
    | 4 => do
      let some e := shape.enums[← below pick shape.enums.size]? | leaf pick shape ctx t
      count 9
      let s ← fixedScrutinee ctx (.enum e.id) d
      if ← takeFault .emptyMatch then
        let o ← fresh
        record .emptyMatch o .emptyMatch
        count 15
        return mk o t (.matchE s #[])
      let n := 1 + (← below pick 3)
      if n > 1 then count 14
      let mut arms := #[]
      for _ in [:n] do
        let wrong := shape.enums.find? (·.id != e.id)
        let faulty ← if wrong.isSome then takeFault .wrongPattern else pure false
        let po ← fresh
        let ctor ← if faulty then do
            let w := wrong.getD e
            let c ← oneOf pick w.ctors FrenBase.ItemId.root
            record .wrongPattern po (.mismatch (.enum e.id) (.enum w.id))
            count 15
            pure c
          else oneOf pick e.ctors FrenBase.ItemId.root
        let body ← expr ctx t d
        arms := arms.push ((⟨po, ctor⟩ : Pattern), ← wrapIf (isLet body) body)
      return mk (← fresh) t (.matchE s arms)
    | 5 => do
      let some (fn, params, _) := calls[← below pick calls.size]? | leaf pick shape ctx t
      count 4
      let o ← fresh
      let ctorCallee ← takeFault .ctorCallee
      let arity ← if ctorCallee then pure false else takeFault .arity
      let mut args := #[]
      for p in params do args := args.push (← fixed ctx p d false)
      if ctorCallee then
        let ctor := ((shape.enums[0]?).bind (·.ctors[0]?)).getD FrenBase.ItemId.root
        record .ctorCallee o (.notCallable ctor)
        count 15
        return mk o t (.call thirTyped ctor args)
      if arity then
        let drop ← coin pick
        if args.size > 1 && drop then args := args.pop
        else args := args.push (← literal pick shape .int)
        record .arity o (.arity params.size args.size)
        count 15
      return mk o t (.call thirTyped fn args)
    | 6 => do
      match t with
      | .int =>
        count 5
        let e ← fixed ctx .int d true
        return mk (← fresh) .int (.unary .neg e)
      | .bool =>
        count 5
        let e ← fixed ctx .bool d true
        return mk (← fresh) .bool (.unary .not e)
      | _ => leaf pick shape ctx t
    | _ => do
      match t with
      | .int =>
        count 6
        let op ← oneOf pick #[BinaryOp.add, .sub, .mul, .div, .mod] .add
        let l ← fixed ctx .int d true
        let r ← fixed ctx .int d true
        return mk (← fresh) .int (.binary op l r)
      | .bool =>
        count 6
        let k ← below pick 3
        if k == 0 then
          let op ← oneOf pick #[BinaryOp.and, .or, .iff] .and
          let l ← fixed ctx .bool d true
          let r ← fixed ctx .bool d true
          return mk (← fresh) .bool (.binary op l r)
        if k == 1 then
          let op ← oneOf pick #[BinaryOp.lt, .le, .gt, .ge] .lt
          let l ← fixed ctx .int d true
          let r ← fixed ctx .int d true
          return mk (← fresh) .bool (.binary op l r)
        let op ← oneOf pick #[BinaryOp.eq, .ne] .eq
        let lt ← randomType pick shape
        if let .enum _ := lt then count 11
        let l ← expr ctx lt d
        let l ← wrapIf (!atomic l) l
        let r ← fixed ctx lt d true
        return mk (← fresh) .bool (.binary op l r)
      | _ => leaf pick shape ctx t
termination_by 2 * depth

/-- A scrutinee: a non-enum literal under the swap fault. -/
def fixedScrutinee (ctx : List Ty) (t : Ty) (d : Nat) : G m (Expr .thir) := do
  if ← takeFault .swap then
    let e ← literal pick shape .int
    record .swap e.origin (.matchNotEnum .int)
    count 15
    return e
  let e ← expr ctx t d
  wrapIf (!atomic e) e
termination_by 2 * d + 1

end

end

/-- Generate a case: module shape, then each item, injecting `fault` (if any)
at a randomly chosen eligible site. `size` bounds the expression depth. -/
def genCase (pick : Nat → m Nat) (size : Nat) (fault : Option Fault) : m (Case × Array Nat) := do
  let run : G m Case := do
    let module := FrenBase.ItemId.root.named "m"
    let depth := 1 + size % 4
    let countdown ← below pick 3
    modify fun s => {s with pending := fault, countdown}
    -- Enums.
    let nEnums := 1 + (← below pick 3)
    let enums : Array Enum := (Array.range nEnums).map fun i =>
      let id := module.named s!"E{i}"
      ⟨id, 0, #[]⟩
    let mut enums2 := #[]
    for e in enums do
      let n := 1 + (← below pick 3)
      enums2 := enums2.push {e with ctors := (Array.range n).map fun j => e.id.named s!"C{j}"}
    let enums := enums2
    let shape0 : Shape := ⟨module, enums, #[]⟩
    -- Signatures.
    let nFns := 1 + (← below pick 3)
    let mut sigs := #[]
    for i in [:nFns] do
      let np := 1 + (← below pick 3)
      let mut ps := #[]
      for _ in [:np] do ps := ps.push (← randomType pick shape0)
      sigs := sigs.push (module.named s!"f{i}", ps, ← randomType pick shape0)
    let shape : Shape := ⟨module, enums, sigs⟩
    let nChecks ← below pick 3
    let params (item : FrenBase.ItemId) (types : Array Ty) : G m (Array Param) := do
      let mut out := #[]
      for h : i in [:types.size] do
        let t := types[i]
        let faulty ← if t != .bool then takeFault .paramSuffix else pure false
        let suffix := faulty || (t == .bool && (← coin pick))
        let annotated := !suffix || faulty || (← coin pick)
        let o ← fresh (some s!"p{i}{if suffix then "?" else ""}")
        if faulty then
          modify fun s => {s with injected := some ⟨.paramSuffix, item, o, .mismatch .bool t⟩}
          count 15
        out := out.push ⟨o, t, suffix, annotated⟩
      return out
    let mut items : Array (Item (Expr .thir)) := #[]
    for e in enums do
      items := items.push (.enum e #[{name := some (e.id.components.getLast?.map (fun
        | .named n => n | .generated k _ => k) |>.getD "")}])
    -- Parameter suffix faults are signature errors, reported before any body:
    -- give them their sites first so one cannot follow a body fault.
    let mut fnItems := #[]
    for (id, types, result) in sigs do
      modify fun s => {s with origins := #[{name := some "f"}], item := id}
      let ps ← params id types
      fnItems := fnItems.push (id, ps, result, (← get).origins)
    let mut checkItems := #[]
    for i in [:nChecks] do
      let id := module.named s!"k{i}"
      modify fun s => {s with origins := #[{name := some "k"}], item := id}
      let np ← below pick 3
      let mut types := #[]
      for _ in [:np] do types := types.push (← randomType pick shape)
      let ps ← params id types
      checkItems := checkItems.push (id, ps, (← get).origins)
    -- A parameter fault no site took is not injected.
    if (← get).pending == some .paramSuffix then modify fun s => {s with pending := none}
    for (id, ps, result, os) in fnItems do
      modify fun s => {s with origins := os, item := id}
      let ctx := ps.toList.reverse.map (·.type)
      let body ← fixed pick shape ctx result depth false
      items := items.push (.function ⟨id, 0, ps, result, body⟩ (← get).origins)
    for (id, ps, os) in checkItems do
      modify fun s => {s with origins := os, item := id}
      let ctx := ps.toList.reverse.map (·.type)
      let n := 1 + (← below pick 3)
      let mut members := #[]
      for j in [:n] do
        let o ← fresh (some s!"l{j}")
        let kind ← oneOf pick #[FrenAst.MemberKind.assume, .expect] .expect
        members := members.push ⟨kind, s!"l{j}", o, ← fixed pick shape ctx .bool depth false⟩
      items := items.push (.check ⟨id, 0, ps, members⟩ (← get).origins)
    -- Declaration order is free: rotate the items.
    let r ← below pick (items.size + 1)
    let ordered := items.extract r items.size ++ items.extract 0 r
    let s ← get
    return ⟨⟨module, ordered⟩, s.injected⟩
  let (c, s) ← run.run {}
  return (c, s.forms)

/-- Like `genCase`, but when a fault is asked for and no eligible site took
it, generate again (at most `tries` times in all), so most faulty cases carry
their fault. Forms are counted over the attempt that is returned. -/
def genCaseRetry (pick : Nat → m Nat) (size : Nat) (fault : Option Fault) :
    Nat → m (Case × Array Nat)
  | 0 => genCase pick size fault
  | tries + 1 => do
    let (c, forms) ← genCase pick size fault
    if fault.isNone || c.expected.isSome then return (c, forms)
    genCaseRetry pick size fault tries

/-- A seeded instance, for censuses outside Plausible. -/
def seeded (seed size : Nat) (fault : Option Fault) : Case × Array Nat :=
  let pick (n : Nat) : StateM StdGen Nat := modifyGet fun g => randNat g 0 (n - 1)
  (genCaseRetry pick size fault 8 |>.run (mkStdGen seed)).1

end FrenGen.Thir
