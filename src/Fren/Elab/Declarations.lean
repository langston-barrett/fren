-- keep-sorted start
import Fren.Elab.Patterns
-- keep-sorted end

/-! # Hosted elaboration: declarations -/

open Lean Elab Command Term Meta

namespace Fren

-- `stx[i]` needs a proof of `True`, which `get_elem_tactic` finds only after
-- trying `assumption` and its other rules: about 10 ms for each of the
-- elaborator's syntax indexes. This rule, tried first, proves it at once,
-- and fails at once for any other bound, which the other rules then prove.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

open Lang in
/-- The expression `e` with its optional `fren_where` `w?`, as the `let` it
means (`Reqs/Lang/Let`), whose definitions are `fren_def`s rather than
`fren_let_def`s. Its `let` has the position of `e`'s first token, so that
it spans `e` in the source. -/
def withWhere (e w? : Syntax) : Syntax :=
  if w?.getNumArgs == 0 then e else
  let w := w?[0]
  mkNode ``Lang.letExpr #[Syntax.atom e.getHeadInfo "let", w[1], w[0], e]

/-- An assumption, requirement, expectation or cover goal: its kind, its name, and its
expression, with its `where` clause. -/
def constraint? (m : Syntax) : Option (PropKind × Syntax × Syntax) :=
  -- A member that failed to parse may lack its last parts.
  if m.getNumArgs < 4 || m.getNumArgs > 5 || !m[0].isAtom then none else
  let kind? := match m[0].getAtomVal.trimAscii.toString with
    | "assume" | "require" => some PropKind.assume
    | "ensure" => some .ensure
    | "expect" => some .expect
    | "cover" => some .cover
    | _ => none
  kind?.map (·, m[1], withWhere m[3] m[4])

/-- The member `m` of a procedure's or a function's block, read as the
elaborator reads it: a precondition, `require n: e`, as the
`assumeMember` that it means (`Reqs/Lang/Procedures#members`), under any
evidence setting. Its keyword keeps the position of `require`. -/
partial def requireAsAssume (m : Syntax) : Syntax :=
  if m.isOfKind ``Lang.evidenceMember then m.setArg 4 (requireAsAssume m[4])
  else if m.isOfKind ``Lang.requireMember then
    mkNode ``Lang.assumeMember (#[mkAtomFrom m[0] "assume "] ++ m.getArgs.extract 1 m.getNumArgs)
  else if m.isOfKind ``Lang.bareRequireMember then
    mkNode ``Lang.bareAssumeMember (#[mkAtomFrom m[0] "assume "] ++ m.getArgs.extract 1 m.getNumArgs)
  else m

/-- The command `stx` with each member of its block, its argument `i`,
read by `requireAsAssume`. -/
def requiresAsAssumes (stx : Syntax) (i : Nat) : Syntax :=
  stx.setArg i (mkNullNode (stx[i].getArgs.map requireAsAssume))

/-- A defined output's definition, with its `where` clause. -/
def definition? (m : Syntax) : Option Syntax :=
  if m[5].isNone then none else some (withWhere m[5][1] m[5][2])

/-- The indexes and tables recorded since the last call, which it forgets,
each with its goal elaborated, rewritten by `subst`, and closed over `fvs`. -/
def takeIndexes (fvs : Array Expr) (subst : Expr → Expr := id) :
    TermElabM (Array (Syntax × Option Core.TableGoal × Expr)) := do
  let xs := (← getLocal).indexes
  let ts := (← getLocal).tables
  modifyLocal fun l => { l with indexes := #[], tables := #[] }
  let sites ← (xs.mapM fun (ref, g) => return (ref, none, subst (← elabProp g)))
    >>= fun indices => return indices ++ (← ts.mapM fun (ref, q, g) => return (ref, some q, subst (← elabProp g)))
  let mut unique : Array (Syntax × Option Core.TableGoal × Expr) := #[]
  for (ref, question, goal) in sites do
    -- A decision tree may translate one source operation along several
    -- paths. Their obligations are guard implications: their conjunction
    -- asks about that source operation under the union of its reach guards.
    let same := if !ref.isOfKind `Fren.booleanSiteRef then none else
      unique.findIdx? fun (previous, previousQuestion, previousGoal) =>
        previous.isOfKind `Fren.booleanSiteRef && ref[0].getPos?.isSome
          && ref[0].getPos? == previous[0].getPos? && ref[0].getTailPos? == previous[0].getTailPos?
          && question == previousQuestion && obligationTy? goal == obligationTy? previousGoal
    if let some i := same then
      let (previous, previousQuestion, previousGoal) := unique[i]!
      unique := unique.set! i (previous, previousQuestion, mkAnd previousGoal goal)
    else unique := unique.push (ref, question, goal)
  unique.mapM fun (ref, question, goal) =>
    return (if ref.isOfKind `Fren.booleanSiteRef then ref[0] else ref, question, ← mkLambdaFVars fvs goal)

/-- Runs `k`, then puts back the name generators, the macro scopes and the
metavariables and Lean's caches as they were before it, so that what is elaborated after it
is named as it would be without it: the solver's queries, and so the
checks' messages, depend on those names (`Reqs/Generated#matches`). What
`k` returns must not mention its metavariables or locals. -/
def keepingNames (k : TermElabM α) : TermElabM α := do
  let s ← getThe Core.State
  -- Its caches too, which may have seen the locals whose names are reused,
  -- and the elaborator's pending metavariables.
  let m ← getThe Meta.State
  let t ← getThe Term.State
  try k finally
    set m
    set t
    modifyThe Core.State fun t => { t with nextMacroScope := s.nextMacroScope, ngen := s.ngen }

/-- What compiled code that applies the constant `c` needs of it
(`Mention`): a proof, which is erased, needs nothing. -/
def mentionOf (c : Name) : MetaM Mention := do
  if c == ``Classical.propDecidable then return .classicalDecision
  if isNoncomputable (← getEnv) c then return .noncomputableDecl
  match (← getEnv).find? c with
  | some (.axiomInfo a) => return if ← isProp a.type then .computable else .dataAxiom
  | _ => return .computable

/-- Compiles the generated definition `name`, of type `type` and value
`value`, or marks it `noncomputable`, as `definitionForm` says from what
its value mentions (`Reqs/Generated#computable-definitions`). Compiled
synchronously, so that a definition that Lean's compiler rejects, which
the rule says it does not, is an error here. -/
def compileGenerated (name : Name) (type value : Expr) : TermElabM Unit := keepingNames do
  let kind : ValueKind ← forallTelescope type fun _ r => return if r.isProp then .proposition else .data
  -- A proposition's mentions do not matter.
  let mentions ← if kind == .proposition then pure #[] else
    (value.foldConsts #[] fun c acc => acc.push c).mapM (liftM <| mentionOf ·)
  match definitionForm kind mentions with
  | .notCompiled => pure ()
  | .markedNoncomputable => modifyEnv (addNoncomputable · name)
  | .compiled => withOptions (Elab.async.set · false) (compileDecls #[name])

/-- Adds the definition `name` of the closed `value`, generalized over the
placeholders `uses` (`Reqs/Generated#procedures`), compiled unless
`compile` is false (`compileGenerated`). -/
def addUsesDef (uses : Array Name) (name : Name) (value : Expr) (compile := true) : TermElabM Unit := do
  let value ← eraseEvaluation value
  let type ← inferType value
  let (type, value) ← withUses uses fun xs => do
    return (← mkForallFVars xs (replaceUses uses xs type), ← mkLambdaFVars xs (replaceUses uses xs value))
  addDecl (.defnDecl { name, levelParams := [], type, value, hints := .abbrev, safety := .safe })
  -- Reducible, like `abbrev`, so that instances such as `Decidable` see
  -- through them.
  setReducibleAttribute name
  if compile then compileGenerated name type value

/-- The name under which a defined function's Lean definition is
elaborated, `decl`'s, so that its matchers are named under it, before
`addLeanDef` adds them under `decl`: not a Fren name, which has no `#`. -/
def leanDeclName (decl : Name) : Name := decl.str "#lean"

/-- Adds the definition `name` of the closed `value`, a defined function's
Lean definition, generalized over the placeholders `uses`, as `addUsesDef`
does: with each of the matchers of its Lean `match`es, which Lean added
under `leanDeclName name` over the placeholders, added again under `name`,
generalized over them too, and registered as a matcher, so that `split`,
`simp` and `#print` see a `match` (`Reqs/Generated#matches`). -/
def addLeanDef (uses : Array Name) (name : Name) (value : Expr) : TermElabM Unit := do
  let tmp := leanDeclName name
  let ms := value.foldConsts #[] fun c acc => if c.getPrefix == tmp && !acc.contains c then acc.push c else acc
  let mut value := value
  for m in ms do
    let some info ← Meta.getMatcherInfo? m | throwError "internal error: `{m}` is not a matcher"
    let .defnInfo ci ← getConstInfo m | throwError "internal error: `{m}` is not a definition"
    let m' := name ++ Name.mkSimple m.getString!
    -- Over the placeholders that it mentions alone: one that it does not,
    -- as a type parameter's `Inhabited` instance, which a `match` never
    -- needs, would be a parameter that Lean's splitter for it drops, and
    -- then `split` could not split it.
    let mUses ← usesOf #[ci.type, ci.value]
    let (type, val) ← withUses mUses fun xs => do
      return (← mkForallFVars xs (replaceUses mUses xs ci.type), ← mkLambdaFVars xs (replaceUses mUses xs ci.value))
    addDecl (.defnDecl { name := m', levelParams := ci.levelParams, type, value := val, hints := ci.hints, safety := .safe })
    Meta.Match.addMatcherInfo m' { info with numParams := info.numParams + mUses.size }
    setInlineAttribute m'
    -- So that `split` in the same file can realize its equations.
    enableRealizationsForConst m'
    let args := mUses.map (Lean.mkConst ·)
    value := value.replace fun e => match e with
      | .const c ls => if c == m then some (mkAppN (.const m' ls) args) else none
      | _ => none
  addUsesDef uses name value

/-- Adds the recursive definition `name` of type `type` and value `value`,
which mentions `name`, as Lean's `def` adds one, by its structural
recursion, compiled where `definitionForm` says that it is
(`Reqs/Generated#computable-definitions`). -/
def addRecursiveDef (ref : Syntax) (name : Name) (type value : Expr) : TermElabM Unit := do
  let kind : ValueKind ← forallTelescope type fun _ r => return if r.isProp then .proposition else .data
  let mentions ← if kind == .proposition then pure #[] else
    ((value.foldConsts #[] fun c acc => if c == name then acc else acc.push c).mapM (liftM <| mentionOf ·))
  let computeKind := if definitionForm kind mentions == .compiled then .regular else .noncomputable
  addPreDefinitions ({}, {}) #[{ ref, kind := .def, levelParams := [], modifiers := { computeKind }, declName := name
                                 binders := .missing, type, value, termination := .none }]

/-- Adds a structural recursion's two definitions
(`lang::structural_recursion`), from `recLean`, its Lean definition's value
over itself first, with the placeholders `uses` as themselves and its
`match`es Lean's, whose matchers are under `leanDeclName decl`: `decl`,
generalized over the placeholders, with the matchers added again under
`decl`, as `addLeanDef` adds them, which Lean's structural recursion
accepts; and the solver's, `solverName decl` (`DefinedInfo.recursive`),
`decl` at the placeholders themselves. The solver never reads the solver's
definition, only its body with the defined functions it applies unfolded
(`DefinedInfo.recBody?`), so the definition is not that body: the body of
a recursion that applies large functions in each arm, as `lint::fix_all`
does, is large, and Lean's structural recursion over it costs as much. -/
def addRecursiveDefs (ref : Syntax) (uses : Array Name) (decl : Name) (recLean : Expr) (typeParams : Array Name := #[]) :
    TermElabM Expr := do
  let recLean ← eraseEvaluation recLean
  let type := recLean.bindingDomain!
  let solver := solverName decl
  let tmp := leanDeclName decl
  let ms := recLean.foldConsts #[] fun c acc => if c.getPrefix == tmp && !acc.contains c then acc.push c else acc
  let args := uses.map (Lean.mkConst ·)
  let mut value := recLean.beta #[mkAppN (Lean.mkConst decl) args]
  for m in ms do
    let some info ← Meta.getMatcherInfo? m | throwError "internal error: `{m}` is not a matcher"
    let .defnInfo ci ← getConstInfo m | throwError "internal error: `{m}` is not a definition"
    let m' := decl ++ Name.mkSimple m.getString!
    -- Over the placeholders that it mentions alone, as `addLeanDef` does.
    let mUses ← usesOf #[ci.type, ci.value]
    let (mty, mval) ← withUses mUses fun xs => do
      return (← mkForallFVars xs (replaceUses mUses xs ci.type), ← mkLambdaFVars xs (replaceUses mUses xs ci.value))
    addDecl (.defnDecl { name := m', levelParams := ci.levelParams, type := mty, value := mval, hints := ci.hints, safety := .safe })
    Meta.Match.addMatcherInfo m' { info with numParams := info.numParams + mUses.size }
    setInlineAttribute m'
    -- Lean's equation lemmas of the recursion are realized from it.
    enableRealizationsForConst m'
    let mArgs := mUses.map (Lean.mkConst ·)
    value := value.replace fun e => match e with
      | .const c ls => if c == m then some (mkAppN (.const m' ls) mArgs) else none
      | _ => none
  let body := value
  let (gType, gValue) ← withUses uses fun xs => do
    return (← mkForallFVars xs (replaceUses uses xs type), ← mkLambdaFVars xs (replaceUses uses xs body))
  addRecursiveDef ref decl gType gValue
  let sv := mkAppN (Lean.mkConst decl) args
  -- A generic one's over its type parameters' placeholders, `typeParams`,
  -- each a type and an `Inhabited` instance, which it takes first: each
  -- instance is the solver form at its type arguments
  -- (`Reqs/Lang/Recursion#generic-recursion`).
  let (type, sv) ← if typeParams.isEmpty then pure (type, sv) else withUses typeParams fun xs => do
    return (← mkForallFVars xs (replaceUses typeParams xs type), ← mkLambdaFVars xs (replaceUses typeParams xs sv))
  addDecl (.defnDecl { name := solver, levelParams := [], type, value := sv, hints := .abbrev, safety := .safe })
  compileGenerated solver type sv
  return body


end Fren
