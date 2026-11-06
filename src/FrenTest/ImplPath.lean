-- keep-sorted start
import Fren
import Lean.Compiler.LCNF
-- keep-sorted end

/-!
# Implementation paths

Audit the functions in each `impl`'s public output mappings against the
runtime value dependencies of the CLI and hosted front end.
The test driver imports `Impls` to keep this catalog built and current;
the analysis itself needs no dependency on Fren's own requirements.
Lean's compiler input erases proofs and types. Inspecting it before
inlining preserves the identity of applied functions. Walking
backwards from returns and case discriminants drops unused computations;
argument demand is propagated between functions to a fixed point.

This is a static dependency audit, not a proof that every execution uses
an implementation. Branches are joined, higher-order applications demand
all arguments, and external functions are opaque. Compiler replacements
proved equal by `csimp` are explicit proof edges, labelled by their theorem.
This does not establish error precedence (#412) or general equality of
reporting paths. Calls through generated syntax and general correspondence
theorems are not inferred. A missing path is an audit gap, not by itself a
behavior bug.
-/

open Lean Meta Compiler.LCNF

namespace FrenTest.ImplPath

/-- Dependencies of a returned value, including decisions selecting it. -/
structure Flow where
  vars : Std.HashSet FVarId := {}
  calls : NameSet := {}
  deriving Inhabited

def Flow.union (a b : Flow) : Flow :=
  { vars := b.vars.fold (fun s v => s.insert v) a.vars, calls := a.calls ++ b.calls }

def Flow.erase (a : Flow) (v : FVarId) : Flow := { a with vars := a.vars.erase v }

def ofVar (v : FVarId) : Flow := { vars := ({} : Std.HashSet FVarId).insert v }

def arguments (args : Array (Arg .pure)) (needed : Nat → Bool := fun _ => true) : Flow := Id.run do
  let mut out : Flow := {}
  for a in args, i in [:args.size] do
    if needed i then
      if let .fvar v := a then out := out.union (ofVar v)
  return out

/-- Runtime arguments that can affect a function's result. -/
abbrev Demands := NameMap (Array Bool)

def valueFlow (demands : Demands) (redirect : Name → Name) : LetValue .pure → Flow
  | .const original _ args =>
    let n := redirect original
    { arguments args (fun i => ((demands.get? n).bind (·[i]?)).getD true) with calls := ({} : NameSet).insert n }
  | .fvar v args => (ofVar v).union (arguments args)
  | .proj _ _ v => ofVar v
  | .lit _ | .erased => {}

/-- Local closures and join points contribute only when their value is
used. Their arguments are conservatively demanded, including recursive
jumps; a case's fields depend on its discriminant. -/
partial def codeFlow (demands : Demands) (redirect : Name → Name) : Code .pure → Flow
  | .return v => ofVar v
  | .unreach _ => {}
  | .let d k =>
    let rest := codeFlow demands redirect k
    if rest.vars.contains d.fvarId then
      (rest.erase d.fvarId).union (valueFlow demands redirect d.value)
    else rest
  | .fun d k | .jp d k =>
    let rest := codeFlow demands redirect k
    if rest.vars.contains d.fvarId then
      let body := d.params.foldl (fun f p => f.erase p.fvarId) (codeFlow demands redirect d.value)
      ((rest.union body).erase d.fvarId)
    else rest
  | .jmp v args => (ofVar v).union (arguments args)
  | .cases c => c.alts.foldl (init := ofVar c.discr) fun acc alt =>
    let body := codeFlow demands redirect alt.getCode
    let body := match alt with
      | .alt _ ps _ => ps.foldl (fun f p => f.erase p.fvarId) body
      | .default _ => body
    acc.union body

/-- Names owned by the tool, excluding generated requirements and the
proof adapters. No test code is an entry point. -/
def production (n : Name) : Bool :=
  let n := (privateToUserName? n).getD n
  ((`Fren).isPrefixOf n || (`FrenCli).isPrefixOf n) &&
    !(`Fren.Generated).isPrefixOf n && !(`Fren.Impls).isPrefixOf n

/-- Spec values wrap code results in finite sets, sequences and strings.
These representations are adapters, so inspect their arguments instead. -/
def adapter (n : Name) : Bool :=
  #[`Fren.FinSet.ofArray, `Fren.FinSet.ofList, `Fren.Seq.ofList, `Fren.Str.lit].contains n

def declarations (env : Environment) : Array (Decl .pure) := Id.run do
  let mut out := #[]
  let mut pending := env.constants.toList.toArray.map (·.1) |>.filter (fun n => n == `main || production n)
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if seen.contains n then continue
    seen := seen.insert n
    if let some d := getDeclCore? env baseExt n then
      if let .code c := d.value then
        out := out.push d
        -- Compiler-lifted closures and specializations may be absent from
        -- the kernel's constant table, and specializations of library
        -- functions retain the library's namespace. Follow LCNF calls
        -- across that boundary too.
        for callee in (codeFlow {} id c).calls do
          pending := pending.push callee
  return out

/-- Recover compiler input before inlining and specialization erase the
identity of applied functions. Use the compiler's own conversion, so proofs,
types, matchers, partial definitions and runtime replacements follow Lean's
rules, rather than scanning kernel terms for names. Compiler-only auxiliary
declarations retain their saved LCNF. -/
def sourceDeclarations (decls : Array (Decl .pure)) : CoreM (Array (Decl .pure)) := do
  let env ← getEnv
  decls.mapM fun d => do
    if (d.name == `main || production d.name) && env.contains d.name then
      try CompilerM.run (toDecl d.name)
      catch e => throwError "implPaths: compiler input of {d.name}: {e.toMessageData}"
    else pure d

/-- Start with all runtime parameters demanded and remove those that
cannot reach a result. Each round only removes demand, so this terminates.
An unavailable body stays opaque and demands all arguments. -/
def graph (env : Environment) (decls : Array (Decl .pure)) : NameMap Flow := Id.run do
  let redirect := fun n => (Compiler.getImplementedBy? env n).getD n
  let mut demands : Demands := {}
  for d in decls do demands := demands.insert d.name (d.params.map fun _ => true)
  let budget := decls.foldl (fun n d => n + d.params.size) 1
  for _ in [:budget] do
    let mut next := demands
    let mut changed := false
    for d in decls do
      if let .code c := d.value then
        let f := codeFlow demands redirect c
        let used := d.params.map (fun p => f.vars.contains p.fvarId)
        if used != demands.getD d.name #[] then changed := true
        next := next.insert d.name used
    demands := next
    unless changed do break
  let mut out := {}
  for d in decls do
    if let .code c := d.value then out := out.insert d.name (codeFlow demands redirect c)
  -- A compiler replacement proved equal to the bound function is a
  -- valid correspondence. Keep these explicit proof edges in the report.
  out := (Compiler.CSimp.ext.getState env).map.fold (init := out) fun g _ e =>
    if production e.fromDeclName && production e.toDeclName then
      let f := g.getD e.toDeclName {}
      g.insert e.toDeclName { f with calls := f.calls.insert e.fromDeclName }
    else g
  return out

/-- The CLI, every registered hosted command elaborator, and the file-end
linter registered by `initialize addModuleLinter lintsAtEnd` in `Fren.Lint`.
Command registration is read from Lean's attribute. The linter is an
explicit root because its registration stores a closure, not a name. -/
unsafe def roots (env : Environment) : Array Name := Id.run do
  let attr := Lean.Elab.Command.commandElabAttribute.ext.getState env
  let mut out := #[`main, `Fren.lintsAtEnd]
  for (n, _) in env.constants.toList do
    if production n && attr.declNames.contains n && !attr.erased.contains n then out := out.push n
  return out

/-- A reachable function with the path witnessing its value dependency. -/
def paths (g : NameMap Flow) (starts : Array Name) : NameMap (Array Name) := Id.run do
  let mut found : NameMap (Array Name) := {}
  let mut pending := starts.map fun n => (n, #[n])
  while !pending.isEmpty do
    let (n, path) := pending.back!
    pending := pending.pop
    if found.contains n then continue
    found := found.insert n path
    for callee in (g.getD n {}).calls do
      pending := pending.push (callee, path.push callee)
  return found

def showPath (env : Environment) (path : Array Name) : String := Id.run do
  let mut text := toString ((path[0]?).getD Name.anonymous)
  for i in [1:path.size] do
    let before := path[i - 1]!
    let after := path[i]!
    match (Compiler.CSimp.ext.getState env).map.find? after with
    | some e =>
      if e.toDeclName == before then
        text := text ++ s!" =[csimp {e.thmName}]=> {after}"
      else text := text ++ s!" -> {after}"
    | none => text := text ++ s!" -> {after}"
  return text

/-- Functions explicitly applied in a mapped runtime term. Erased proofs,
types and type formers are excluded at every step, including after adapter
unfolding. Adapters in `Impls` and generated spec functions do not count as
production bindings. Unfold adapters once along each path, so direct
argument discards do not count. Stop at the first production function on
each expression branch. Structure projections, recursors, matchers and
instance dictionaries are representation machinery, not the producer of a
mapped result. -/
partial def targets (env : Environment) (e : Expr) (unfolded : NameSet := {}) : MetaM NameSet := do
  if (← isProof e) || (← isTypeFormer e) then return {}
  match e with
  | .app .. | .const .. =>
    let reduced := e.headBeta
    if reduced != e then return ← targets env reduced unfolded
    let fn := e.getAppFn
    if let .const n us := fn then
      if production n && !adapter n && !env.isProjectionFn n && !isAuxRecursor env n &&
          !Meta.isMatcherCore env n && !Meta.isInstanceCore env n then
        if let some ci := env.find? n then
          if ci matches .defnInfo _ | .opaqueInfo _ then return ({} : NameSet).insert n
      let user := (privateToUserName? n).getD n
      if (`Fren.Impls).isPrefixOf user && !unfolded.contains n then
        if let some ci := env.find? n then
          if ci.value?.isSome then
            let value ← Core.instantiateValueLevelParams ci us
            return ← targets env (value.beta e.getAppArgs) (unfolded.insert n)
    let mut out ← if fn.isConst then pure {} else targets env fn unfolded
    for arg in e.getAppArgs do out := out ++ (← targets env arg unfolded)
    return out
  | .lam .. => lambdaTelescope e fun _ body => targets env body unfolded
  | .letE _ _ v b _ => targets env (b.instantiate1 v) unfolded
  | .proj _ _ b | .mdata _ b => targets env b unfolded
  | _ => return {}

structure Binding where
  impl : Name
  comp : Name
  output : Name
  functions : Array Name
  deriving Inhabited

/-- Recover the actual terms in an impl's theorem type, not its proof or
source text. `assumes` receives the mapped public outputs as well as the
inputs, with private variables defaulted (`Fren.mkObligation`). Use the
last matching top-level domain: an impl's own proof binders may mention the
same `assumes` function. Open the binders so erasure checks can infer the
types of dependent mapped terms in their local context. -/
def bindings (env : Environment) : MetaM (Array Binding) := do
  let s := Fren.frenExt.getState env
  let mut out := #[]
  for (comp, impls) in s.impls.toArray do
    let some c := s.comps.get? comp | throwError "missing component {comp}"
    for impl in impls do
      let some ci := env.find? impl | throwError "missing impl {impl}"
      let rows ← forallTelescope ci.type fun xs _ => do
        let mut mapping? := none
        for x in xs do
          let domain ← inferType x
          if domain.isAppOfArity (c.decl ++ `assumes) (c.uses.size + c.vars.size) then
            mapping? := some domain
        let some app := mapping? | throwError "{impl}: cannot recover output mappings"
        let args := app.getAppArgs.extract c.uses.size (c.uses.size + c.vars.size)
        let mut rows : Array Binding := #[]
        if !c.vars.any (fun v => v.role == .output && v.isPub) then
          rows := rows.push { impl, comp, output := .anonymous, functions := #[] }
        for v in c.vars, arg in args do
          if v.role == .output && v.isPub then
            let functions := (← targets env arg).toArray.qsort Name.quickLt
            rows := rows.push { impl, comp, output := v.name, functions }
        return rows
      out := out ++ rows
  return out.qsort fun a b => s!"{a.impl} {a.output}" < s!"{b.impl} {b.output}"

/-- Stable keys for existing gaps. A new disconnected mapping fails even
when the same helper is already disconnected in another impl. -/
def outputName (b : Binding) : String :=
  if b.output.isAnonymous then "<no public output>" else b.output.toString

def key (b : Binding) (fn : Name) : String := s!"{b.impl} {outputName b} {fn}"

/-- The full report is saved even on failure. Existing gaps are explicit,
exact keys; stale exceptions fail as soon as their path becomes connected.
Outputs without a production function, and output-free laws, are listed
separately, never counted as audited code. -/
unsafe def check : IO (Array String) := do
  enableInitializersExecution
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Impls }, { module := `FrenCli.Main }] {} (loadExts := true)
  let (bs, decls) ← (do
    let bs ← MetaM.run' (bindings env)
    let decls ← sourceDeclarations (declarations env)
    pure (bs, decls) : CoreM _).toIO'
    { fileName := "implPaths", fileMap := FileMap.ofString ""
      options := maxRecDepth.set (maxHeartbeats.set {} 0) 8192 } { env }
  let g := graph env decls
  let rs := roots env
  let cli := paths g #[`main]
  let hosted := paths g (rs.filter (· != `main))
  let mut failures := #[]
  if bs.isEmpty || decls.isEmpty || rs.size < 2 then
    failures := failures.push "implPaths: empty bindings, compiler graph or hosted roots"
  for r in rs do
    unless g.contains r do failures := failures.push s!"implPaths: no compiler body for root {r}"
  let knownFile : System.FilePath := "test/impl_paths.txt"
  let known := (← IO.FS.readFile knownFile).splitOn "\n" |>.filter fun s => !s.isEmpty && !s.startsWith "#"
  if known.length != known.eraseDups.length then
    failures := failures.push "implPaths: duplicate inventory entries"
  let mut gaps := #[]
  let mut report := s!"{bs.size} mappings (including output-free laws); {decls.size} compiled functions; {rs.size} reporting roots\n"
  for b in bs do
    if b.functions.isEmpty then
      let k := s!"unbound: {b.impl} {outputName b}"
      gaps := gaps.push k
      report := report ++ k ++ "\n"
      unless known.contains k do
        failures := failures.push s!"implPaths: no production output function bound by {b.impl} {outputName b}"
    for fn in b.functions do
      let k := key b fn
      let cliPath := cli.get? fn
      let hostedPath := hosted.get? fn
      for (front, path?) in [("cli", cliPath), ("hosted", hostedPath)] do
        if let some path := path? then
          report := report ++ s!"connected ({front}): {k} via {showPath env path}\n"
      let gap? := match cliPath, hostedPath with
        | some _, some _ => none
        | some _, none => some s!"cli only: {k}"
        | none, some _ => some s!"hosted only: {k}"
        | none, none => some s!"bypassed: {k}"
      if let some gap := gap? then
        gaps := gaps.push gap
        report := report ++ gap ++ "\n"
        unless known.contains gap do failures := failures.push s!"implPaths: {gap}"
  for k in known do
    unless gaps.contains k do failures := failures.push s!"implPaths: stale inventory entry: {k}"
  IO.FS.createDirAll ".lake/impl-paths"
  IO.FS.writeFile ".lake/impl-paths/report.txt" report
  IO.FS.writeFile ".lake/impl-paths/gaps.txt" (String.intercalate "\n" gaps.toList ++ "\n")
  return failures

end FrenTest.ImplPath
