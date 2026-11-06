-- keep-sorted start
import FrenCli.Elab.Expr
-- keep-sorted end

/-!
# Item elaboration helpers for `.fren` files

Resolves item type parameters, variables and calls, tracks evidence and
uses, and reports member-order lints. Shared by procedures and other items.
-/

open Lean

namespace FrenCli

open Fren.Core (Ty Table Resolved Role Place showPath Msg Severity Lint LintLevel Levels LevelInEffect Named)

/-- Whether the type `segs` is the item `name`, and whether it has it as a
set's element type (`Fren.Core.ownIn`). -/
def ownIn (segs : Array Ident) (name : Ident) : Bool × Bool := Fren.Core.ownIn (segs.map (·.name)) name.name

/-- Whether the type `segs` is the item `name` being declared, whether with
its own type parameters `params`, and whether `name` is within its
arguments (`Fren.Core.ownArgs`). -/
def ownArgs (segs : Array Ident) (name : Ident) (params : Array Name) : Bool × Bool × Bool :=
  Fren.Core.ownArgs (segs.map (·.name)) name.name (params.map toString)

/-- The type parameters `params` of the enumeration or record being
declared, checked: distinct (`lang::distinct_names`), without `!`, and
without the name of a type or of an item in scope (`Reqs/Lang/Generics`). -/
def elabTypeParams (params : Array Ident) : M (Array Name) := do
  let ns := params.map (Name.mkSimple ·.name)
  if let some k := (Fren.Core.repeatsAt ns)[0]? then err params[k]!.span (Fren.Core.dupTypeParamMsg ns[k]!)
  for p in params, n in ns do
    liftMsg p.span (Fren.Core.checkNoBang n)
    if #["Bool", "Int", "Nat", "String", "Set", "Seq", "Rel"].contains p.name then
      err p.span (Fren.Core.typeParamNameMsg n s!"the built-in type `{p.name}`")
    let st ← get
    if let .ok r := st.table.resolvePath st.scope #[n] #[] then
      err p.span (Fren.Core.typeParamNameMsg n r.describe)
  return ns

/-- The span of the annotation `: T` of the type at `span`, from the end of
what precedes it. -/
def annotationSpan (span : Span) : M Span := do
  let src := (← get).src
  let mut i := span.start
  while i > 0 && src[i - 1]!.isWhitespace do i := i - 1
  if i > 0 && src[i - 1]! == ':' then i := i - 1
  while i > 0 && src[i - 1]!.isWhitespace do i := i - 1
  return { span with start := i }

/-- The declared type of the variable, field or function `name`, written
`ty?`, which is `Bool` if it is not written, with its patterns. -/
def varPTy (ty? : Option (Array Ident)) (name : Ident) : M Fren.Core.PTy := do
  let pt ← ty?.mapM elabPTy
  let t := pt.map (·.ty)
  let n := Name.mkSimple name.name
  unless Fren.Core.generatedName name.name do liftMsg name.span (Fren.Core.checkVarName n (t.map (· == .bool)))
  -- `redundant_bool_type` (`lint::redundant_bool_type`), but not of a
  -- subset type, whose invariants the annotation holds.
  if let (some segs, true, false) := (ty?, !Fren.Core.generatedName name.name && Fren.Core.redundantBoolType n (t.map (· == .bool)), pt.any (fun t => t.pat?.isSome || !t.invariants.isEmpty)) then
    let span ← annotationSpan (segs[0]!.span.to segs.back!.span)
    lintFix .redundantBoolType span (Fren.Core.redundantBoolTypeMsg n)
  let result := pt.getD (.plain .bool)
  noteResolved "type" name.span fun _ => result.ty.showQualified
  return result

def varTy (ty? : Option (Array Ident)) (name : Ident) : M Ty := return (← varPTy ty? name).ty

/-- Records what a call of `c`, written at `span`, brings to the current
procedure's mix of relational operators and counting. -/
def noteCounts (c : CComp) (span : Span) : M Unit :=
  modify fun s => { s with relationalUsed := s.relationalUsed || c.relational, guardedUsed := s.guardedUsed || c.guarded
                           countSpans := if c.counts then s.countSpans.push span else s.countSpans }

/-- A call whose procedure has been resolved, before its bindings are
elaborated. -/
structure PendingInst where
  name : Ident
  comp : CComp
  bindings : Array (Ident × Option Expr)
  /-- A call's arguments, rather than bindings written by name. -/
  positional : Bool := true

/-- Resolves the call `call x := p(args)`: the called procedure and the
call's variables, with each argument bound to the parameter in its
position (`F0408`, `F0409`). -/
def resolveInst (x : Ident) (p : Array Ident) (bs : Array (Ident × Option Expr)) : M (PendingInst × Array CVar) := do
  let w := Name.mkSimple x.name
  let path ← match ← resolve p with
    | .item { kind := .compItem, path, .. } => pure path
    | r => err (p[0]!.span.to p.back!.span) (Fren.Core.notACompMsg r)
  let st ← get
  let some c := st.comps.find? (·.path == path) | internal x.span s!"unknown comp `{path}`"
  unless c.decidable do
    modify fun s => { s with outsideCore := true }
    lint .undecidable (p[0]!.span.to p.back!.span) (Fren.Core.undecidableInstMsg path)
  noteCounts c (p[0]!.span.to p.back!.span)
  let params := c.vars.filter (fun v => v.role == .input && v.name.isAtomic) |>.map (·.name)
  let callee := showPath path
  let some bound := Fren.Core.callBindings (params.map Fren.Core.nameText) bs
    | let at_ := if bs.size > params.size then bs[params.size]!.1.span.to bs.back!.1.span else p[0]!.span.to p.back!.span
      err at_ (Fren.Core.callArityMsg callee (params.map Fren.Core.nameText) bs.size)
  let bs := bound.map fun (n, (a, e?)) => ({ a with name := n }, e?)
  let vars := c.vars.map fun v =>
    let role := Role.ofInst v.role v.isPub
    -- An input's constraint is the call's obligation, which the
    -- call check asks, rather than a fact (`Reqs/Check#call-assumptions`).
    { name := w ++ v.name, role, isPub := role == .instOutput, ty := v.ty, span := x.span, ptype := v.ptype
      fact? := if v.role == .input then none else v.fact?.map (rename w c.vars) }
  return ({ name := x, comp := c, bindings := bs }, vars)

/-- Elaborates the bindings of a call. -/
def elabInst (cx : ExprCtx) (pi : PendingInst) : M CInst := do
  let w := Name.mkSimple pi.name.name
  let mut eqs := #[]
  let c := pi.comp
  for (b, e?) in pi.bindings do
    if let some e := e? then if !pi.positional then lintRedundant b e false
    let e := e?.getD (.path b.span #[b])
    let some v := cx.vars.find? (·.name == w ++ Name.mkSimple b.name)
      | internal b.span s!"no variable for `{b.name}`"
    let (smt, t) ← elabExpr { cx with expected? := Fren.Core.ExprSite.binding.expected (some v.ty) none } e
    liftMsg e.span (Fren.Core.checkType v.ty t (some s!"note: `{b.name}` of `{showPath c.path}` has type `{v.ty.show}`"))
    -- An `Int` bound to an `Int` keeps it one (`lint::manual_nat`).
    if v.ty == .int && t == .int then modify fun s => { s with natKept := s.natKept.push (c.path, b.name) }
    lintBools e (← hidesIn cx) (pi.positional && pi.bindings.size == 1)
    eqs := eqs.push s!"(= {quote v.name.toString} {smt})"
  modify fun s => { s with natApps := s.natApps ++ c.natApps.map (rename w c.vars) }
  -- Each input whose type has an obligation assumes it, before the
  -- procedure's own assumptions (`Reqs/Check#call-assumptions`).
  let st ← get
  let typed := c.vars.filter (·.role == .input) |>.flatMap fun v =>
    (v.ptype.obligation st.shapeOf).toArray.flatMap fun obligation =>
      obligation.namedParts.mapIdx fun k (label, part) =>
        let text := if label.isAnonymous then v.ptype.text else "@invariant:" ++ Fren.Core.showPath label
        (Name.num v.name k, text, rename w c.vars (consSmt st.dataOf? part (quote v.name.toString)))
  -- Preconditions may read local definitions. They must be substituted
  -- before becoming obligations: the call's own behaviour is deliberately
  -- not a hypothesis of its call check.
  let unfold (smt : String) := c.defs.foldr (fun (n, value) body =>
    substQuoted (fun p => if p == n.toString then value else quote p) body) smt
  return {
    name := w, comp := c.path, span := pi.name.span, bindings := conj eqs
    behaviour := rename w c.vars c.meaning
    assumes := typed.map (fun (n, _, f) => (n, f)) ++ (c.props.filter (·.kind == .assume) |>.map fun a => (a.name, rename w c.vars (unfold a.smt)))
    typed := typed.map fun (n, t, _) => (n, t)
    bounded := c.vars.any fun v => v.role == .input && (v.ptype.obligation st.shapeOf).any (·.quantifies) }

/-- Imports the path `segs`, written at `loc`, into the current module, or,
with `scope`, into the procedure of that path. -/
def declareUse (segs : Array Ident) (glob : Bool) (loc : UseLoc) (scope : Option Name := none) : M Unit := do
  let st ← get
  let u ← liftResolve segs (st.table.declareUse st.module (segNames segs) glob (scope.getD st.module))
  noteResolved "name" loc.path fun _ => resolvedPath u.target
  let record : Fren.Core.UseRecord := {
    module := u.scope, target := u.target, glob := u.glob
    unusedLevel := st.levels.get .unusedImports, globLevel := st.levels.get .globImports }
  modify fun s => { s with table := s.table.addUse u, useRecords := s.useRecords.push (record, loc.path),
                           useLocs := s.useLocs.push loc }

/-- Declares a procedure's `use`s, in the scope `path`, and makes it the
scope that paths resolve in if there are any. -/
def declareMemberUses (path : Name) (members : Array Member) : M Unit := do
  for m in members do
    match m with
    | .use span segs glob =>
      declareUse segs glob { item := span, removal := span, path := segs[0]!.span.to segs.back!.span } (some path)
      modify fun s => { s with scope := path }
    | .useGroup span pre paths =>
      for p in paths do
        declareUse (pre ++ p) false
          { item := span, removal := span, path := p[0]!.span.to p.back!.span, pre? := some (pre[0]!.span.to pre.back!.span) }
          (some path)
      modify fun s => { s with scope := path }
    | _ => pure ()

/-- The evidence that the `set_option fren.evidence` in effect sets
(`Reqs/Check#checking-by-enumeration`); an invalid value sets nothing. -/
def evidenceOfEffect : M Fren.Core.Evidence := do
  let st ← get
  return Fren.Core.evidenceInEffect st.evidenceOverride? (st.evidence?.bind fun (value, _) => Fren.Core.evidenceOf? value)

/-- Whether the `set_option fren.evidence` in effect sets checks to testing.
An invalid value, reported once where it is set (`F0214`), sets nothing. -/
def evidenceInEffect : M Bool := return (← evidenceOfEffect).tested

/-- The conjuncts of `e`, a constraint: the operands of its `and`s, not
through parentheses but its own (`lint::manual_nat`). -/
partial def constraintConjuncts (src : Array Char) (e : Expr) : Array Expr :=
  let rec go (top : Bool) (e : Expr) : Array Expr :=
    let bare := top || Fren.Core.withParens src (toRange e.span) == toRange e.span
    match e with
    | .bin _ "and" a b => if bare then go false a ++ go false b else #[e]
    | _ => #[e]
  go true e

/-- Records `manual_nat` in the procedure `comp` of `members`
(`lint::manual_nat`): for each variable it fires on, at its first bound,
reported at the end of the file (`finishNat`). -/
def lintManualNat (comp : Name) (members : Array Member) : M Unit := do
  let src := (← get).src
  let vars := members.filterMap fun
    | .var isIn _ _ x ty? defn? => some ((declaredIdent x).1, ty?, isIn, defn?.isSome)
    | _ => none
  -- Only assumptions and guarantees constrain; an expectation or a cover goal has no bound.
  let props := members.filterMap fun
    | .prop kind x e => some (kind, x, e, if kind == .assume || kind == .ensure then constraintConjuncts src e else #[])
    | _ => none
  let wf (e : Expr) : String := Fren.Core.writtenForm (Fren.Core.textOf src (toRange e.span))
  let conjunct (assumption : Bool) (e : Expr) : Fren.Core.NatConjunct := match e with
    | .bin _ op l r => { assumption, op := .ofOp op, left := wf l, right := wf r }
    | _ => { assumption, op := .otherOp, left := "", right := "" }
  let isInt (ty? : Option (Array Ident)) : Bool := match ty? with | some #[t] => t.name == "Int" | _ => false
  let bounds := Fren.Core.manualNatBounds
    (vars.map fun (x, ty?, isIn, defined) =>
      { name := x.name, role := if isIn then .input else if defined then .definedOutput else .output, int := isInt ty? })
    (props.map fun (kind, _, _, cs) => cs.map (conjunct (kind == .assume)))
  for (i, p, k) in bounds do
    let (x, _, isIn, _) := vars[i]!
    let (_, name, _, cs) := props[p]!
    let msg := Fren.Core.manualNatMsg x.name isIn name.name (Fren.Core.textOf src (toRange cs[k]!.span))
    let report := { lint := .manualNat, level := (← get).levels.get .manualNat, ref := cs[k]!.span, msg }
    modify fun s => { s with natReports := s.natReports.push { comp, var := x.name, report } }

/-- The checks of a procedure with `members` that are tested
(`Reqs/Check#checking-by-testing`): `all` if the procedure is set to testing,
then each member's own setting. -/
def testedOf (all : Fren.Core.Evidence) (members : Array Member) : M (Fren.Core.Tested × Fren.Core.Tested) := do
  let reserved := members.filterMap fun | .prop _ x _ => some (Name.mkSimple x.name) | _ => none
  let mut refinesIndex := 0
  let mut pending : Option (Fren.Core.Evidence × Span) := none
  let mut expects := #[]
  let mut insts := #[]
  let mut dets := #[]
  let mut constraints := #[]
  for m in members do
    if let .evidence span value valueSpan := m then
      let some b := Fren.Core.evidenceOf? value | err valueSpan (Fren.Core.invalidEvidenceMsg value)
      pending := some (b, span)
      continue
    -- `--evidence` sets every check, the members' too (`cli::evidence_in_effect`).
    let override? := (← get).evidenceOverride?
    let set? := pending.map fun (b, _) => Fren.Core.evidenceInEffect override? (some b)
    match m, pending with
    | .refines .., _ =>
      refinesIndex := refinesIndex + 1
      while reserved.contains (Name.mkSimple s!"refines_{refinesIndex}") do refinesIndex := refinesIndex + 1
      expects := expects.push (Name.mkSimple s!"refines_{refinesIndex}", set?)
    | .prop .expect x _, _ | .prop .cover x _, _ => expects := expects.push (Name.mkSimple x.name, set?)
    -- By the names they declare, without the `!` of shadowing.
    | .inst x .., _ => insts := insts.push (Name.mkSimple (declaredIdent x).1.name, set?)
    | .var false _ true x _ _, _ => dets := dets.push (Name.mkSimple (declaredIdent x).1.name, set?)
    | _, some (_, span) =>
      let what := match m with
        | .prop .assume .. => "an assumption" | .prop .ensure .. => "a guarantee"
        | .var true .. => "a parameter" | .var .. => "a variable that is not `det`" | .define .. => "a result's definition"
        | _ => "a `use`"
      err span (Fren.Core.misplacedEvidenceMsg what)
    | _, none => pure ()
    match m with
    | .prop .assume x _ | .prop .ensure x _ => constraints := constraints.push (Name.mkSimple x.name)
    | .var false _ _ x _ (some _) => constraints := constraints.push (Name.mkSimple (declaredIdent x).1.name)
    | _ => pure ()
    pending := none
  if let some (_, span) := pending then err span (Fren.Core.misplacedEvidenceMsg "the end of the procedure")
  let by_ (f : Fren.Core.Evidence → Bool) :=
    let pick (xs : Array (Name × Option Fren.Core.Evidence)) := xs.map fun (n, e?) => (n, e?.map f)
    Fren.Core.Tested.ofSettings (f all) constraints (pick expects) (pick insts) (pick dets)
  return (by_ (·.tested), by_ (·.enumerated))

/-- Reports `arbitrary_source_item_ordering` on a procedure whose members,
written at `spans`, are `members`, and whose `{` ends at `openStop`
(`lint::arbitrary_source_item_ordering`). An evidence setting is part of
the member after it. -/
def lintMemberOrder (members : Array Member) (spans : Array Span) (openStop : Nat) (global := false) : M Unit := do
  let mut kinds := #[]
  let mut ranges : Array Fren.Core.Range := #[]
  let mut names := #[]
  let mut mentioned := #[]
  let mut start? : Option Nat := none
  for m in members, sp in spans do
    let (kind, name?, ms) : Fren.Core.MemberKind × Option Ident × Array Name := match m with
      | .refines w _ args _ => (.expectation, none, #[Name.mkSimple w.name] ++ args.flatMap (fun e => (mentions e).map (·.getRoot)))
      | .evidence .. => (.use, none, #[])
      | .use .. | .useGroup .. => (.use, none, #[])
      | .var _ _ _ x _ none => (.exists, some x, #[])
      | .var _ _ _ x _ (some d) => (.let, some x, (mentions d).map (·.getRoot))
      | .define _ d => (.define, none, (mentions d).map (·.getRoot))
      | .inst x _ bs .. => (.call, some x, bs.foldl (init := #[]) fun acc (b, e?) =>
          acc ++ ((e?.map mentions).getD #[Name.mkSimple (declaredIdent b).1.name]).map (·.getRoot))
      | .prop .assume x _ => (.assumption, some x, #[])
      | .prop .ensure x _ => (.guarantee, some x, #[])
      | .prop .expect x _ => (.expectation, some x, #[])
      | .prop .cover x _ => (.cover, some x, #[])
    if m matches .evidence .. then
      start? := start?.orElse fun _ => some sp.start
      continue
    kinds := kinds.push kind
    ranges := ranges.push { start := start?.getD sp.start, stop := sp.stop }
    start? := none
    names := names.push (name?.map fun x => Name.mkSimple (declaredIdent x).1.name)
    mentioned := mentioned.push ms
  let some i := Fren.Core.firstOutOfOrder? kinds | return
  let msg := Fren.Core.memberOrderMsg kinds[i]! kinds[i - 1]! global
  let mentions := mentioned.map (·.filterMap fun n => names.findIdx? (· == some n))
  let at_ : Span := { start := ranges[i]!.start, stop := ranges[i]!.stop }
  match Fren.Core.memberOrderFix? (← get).src openStop ranges kinds mentions with
  | some edit => lintEdits .arbitrarySourceItemOrdering at_ msg #[edit]
  | none => lint .arbitrarySourceItemOrdering at_ msg

end FrenCli
