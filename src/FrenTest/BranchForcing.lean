-- keep-sorted start
import FrenCore.Enumeration
-- keep-sorted end

/-! Finite-model conformance checks of conditional branch explanations.
The backend decides formulas over all four assignments of two Boolean
variables, so both the query protocol and reported source identities are
checked without relying on a particular SMT solver's chosen model. -/

namespace FrenTest.BranchForcing

open Lean Fren.Core

abbrev Formula := Nat → Bool
abbrev Queries := Array (Array Name)

private def x (i : Nat) : Bool := i % 2 == 1
private def y (i : Nat) : Bool := i / 2 == 1
private def yes : Formula := fun _ => true
private def no : Formula := fun _ => false

private def backend (unknownModels := false) (unknownConsistency := false) : Backend (StateM Queries) Formula Bool where
  query hyps goal wantModel := do
    modify (·.push (hyps.map (·.1)))
    if unknownConsistency then return .unknown "consistency unavailable"
    if wantModel && unknownModels then return .unknown "model unavailable"
    match (List.range 4).find? fun i => hyps.all (fun (_, f) => f i) && !goal i with
    | some i => return .sat #[(`x, x i), (`y, y i)]
    | none => return .unsat
  falseF := no
  notF f := fun i => !f i
  conj fs := fun i => fs.all (fun f => f i)
  existsOutputs f := pure fun _ => (List.range 4).any f
  pin n v := pure (some (fun i => (if n == `x then x i else y i) == v))
  pinVariant _ _ := pure none
  render _ v := pure (if v then "true" else "false")
  prime := id
  samePrimed _ := yes
  subst _ f := f

private def variables (role : Role := .output) : Array VarSig :=
  #[{ name := `x, role, isPub := true }, { name := `y, role, isPub := true }]

private def orGroup : BranchGroup Formula :=
  { owner := `policy, kind := .disjunction,
    members := #[{ name := `policy.backoff, formula := x, range? := some ({ start := 10, stop := 20 } : Range), text := "x?" },
                 { name := `policy.give_up, formula := y, range? := some ({ start := 22, stop := 32 } : Range), text := "y?" }] }

private def orComp : Comp Formula :=
  { path := `or_policy, vars := variables,
    assumes := #[], reqs := #[(`policy, fun i => x i || y i), (`no_x, fun i => !x i), (`no_y, fun i => !y i)],
    expects := #[], triggers := #[], branchGroups := #[orGroup] }

private def iffGroup : BranchGroup Formula :=
  { owner := `modes, kind := .equivalence,
    members := #[{ name := `modes.heating, formula := x }, { name := `modes.manual, formula := y }] }

private def iffComp : Comp Formula :=
  { path := `iff_policy, vars := variables,
    assumes := #[], reqs := #[(`modes, fun i => x i == y i), (`override, x), (`too_hot, fun i => !y i)],
    expects := #[], triggers := #[], branchGroups := #[iffGroup] }

private def ensure (ok : Bool) (why : String) : IO Unit :=
  unless ok do throw (IO.userError why)

#eval do
  let (r, _) := (checkRealizable backend orComp).run #[]
  ensure (r.verdict == Verdict.fail) "disjunctive policy must be unrealizable"
  ensure (r.branchConflicts.size == 1) "one in-core source group expected"
  let group := r.branchConflicts[0]!
  ensure (group.cases.size == 2) "the example limit must not truncate a group's alternatives"
  let first := group.cases[0]!
  let second := group.cases[1]!
  ensure (first.name == `policy.backoff && second.name == `policy.give_up) "branch identities lost"
  ensure (first.core == #[`no_x] && second.core == #[`no_y]) "conditional cores must be deletion-minimal"
  ensure (first.clashes.size == 1 && second.clashes.size == 1) "each branch should expose its own forced output"
  ensure (first.clashes[0]!.output == `x && second.clashes[0]!.output == `y) "wrong branch forcing output"
  ensure (first.range? == some ({ start := 10, stop := 20 } : Range) && first.text == "x?") "source range/text lost"
  let notes := branchMessages r
  ensure (notes.all fun m => (m.msg.headline.splitOn "reported input").length == 1 &&
    m.msg.notes.all (fun note => (note.splitOn "reported input").length == 1))
    "an output-only conflict claimed to display an input"
  ensure (notes.any fun m => m.atRange? == some ({ start := 10, stop := 20 } : Range)) "member diagnostic range lost"
  ensure (notes.any fun m => m.msg.headline.contains 'x') "forced output is absent from diagnostics"
  let (without, _) := (checkRealizable backend { orComp with branchGroups := #[] }).run #[]
  ensure (r.verdict == without.verdict) "explanations changed the primary verdict"
  match r.detail, without.detail with
  | .conflict input core, .conflict input' core' =>
    ensure (input == input' && core == core') "explanations changed the unconditional minimal core"
  | _, _ => throw (IO.userError "missing primary conflict")
  let (unrelated, queries) := (branchConflictsOf backend #[orGroup] #[] orComp.reqs #[] #[`x, `y] (some 1)).run #[]
  ensure (unrelated.isEmpty && queries.isEmpty) "out-of-core groups must cost no queries"
  let (disabled, queries) := (branchConflictsOf backend #[orGroup] #[] orComp.reqs #[`policy, `no_x, `no_y]
    #[`x, `y] (some 0)).run #[]
  ensure (disabled.isEmpty && queries.isEmpty) "zero example budget must cost no queries"
  let numbered := { orGroup with members := orGroup.members.mapIdx fun i (member : BranchMember Formula) =>
    { member with name := Name.num `policy (i + 1) } }
  let (numberedResult, _) := (checkRealizable backend { orComp with branchGroups := #[numbered] }).run #[]
  ensure (numberedResult.branchConflicts[0]!.cases[0]!.name == Name.num `policy 1)
    "unlabelled member's one-based identity was lost"
  ensure ((branchMessages numberedResult).any fun m => (m.msg.headline.splitOn "policy.1").length > 1)
    "numeric member name was not rendered"

#eval do
  let (r, _) := (checkRealizable backend iffComp).run #[]
  ensure (r.verdict == Verdict.fail && r.branchConflicts.size == 1) "equivalence conflict missing"
  let cases := r.branchConflicts[0]!.cases
  ensure (cases.size == 2 && cases[0]!.label == "both operands are true" && cases[1]!.label == "both operands are false") "iff must have exactly two explanation branches"
  ensure (cases[0]!.opposed.any fun p => p.member == `modes.manual && p.wanted && p.rest == #[`too_hot])
    "all-hold branch must name the member forced false"
  ensure (cases[1]!.opposed.any fun p => p.member == `modes.heating && !p.wanted && p.rest == #[`override])
    "none-hold branch must name the member forced true"
  let larger := { iffGroup with members := iffGroup.members.push { name := `modes.third, formula := x } }
  ensure ((larger.alternatives backend).size == 2) "n-ary iff was expanded into a parity chain or exponentially many cases"
  let (unknown, _) := (branchConflictsOf (backend true) #[iffGroup] #[] iffComp.reqs
    #[`modes, `override, `too_hot] #[`x, `y] (some 1)).run #[]
  ensure (unknown.all fun g => g.cases.all fun c => c.clashes.isEmpty)
    "unknown candidate models cannot establish output-value forcing"

#eval do
  let impossible : BranchGroup Formula :=
    { owner := `never, kind := .disjunction,
      members := #[{ name := Name.num `never 1, formula := no }, { name := Name.num `never 2, formula := no }] }
  let comp := { orComp with reqs := #[(`never, no)], branchGroups := #[impossible] }
  let (r, _) := (checkRealizable backend comp).run #[]
  ensure (r.branchConflicts[0]!.cases.all fun c => c.impossible && c.core.isEmpty && c.clashes.isEmpty)
    "contradictory branches must not force arbitrary values"
  let assumptions := { orComp with vars := variables .input, assumes := orComp.reqs, reqs := #[] }
  let (r, _) := (checkRealizable backend assumptions).run #[]
  ensure (r.verdict == Verdict.fail && r.branchConflicts.size == 1) "unsatisfiable assumptions lost branch explanations"
  let (r, _) := (checkVacuity backend orComp (`trigger, yes)).run #[]
  ensure (r.verdict == Verdict.fail && r.branchConflicts.size == 1) "vacuity lost branch explanations"
  let (r, _) := (checkCover backend orComp (`scenario, yes)).run #[]
  ensure (r.verdict == Verdict.fail && r.branchConflicts.size == 1) "failed cover lost conditional branch explanations"
  let (atomic, formulas) := Fren.Core.Comp.atoms orComp
  ensure (atomic.branchGroups.size == 1) "atomization dropped source groups"
  for source in orGroup.members, atom in atomic.branchGroups[0]!.members do
    ensure (source.name == atom.name && source.range? == atom.range? && source.text == atom.text) "atomization changed source identity"
    match atom.formula with
    | .atom k =>
      for i in List.range 4 do ensure (source.formula i == formulas[k]! i) "atomization changed a branch formula"
    | _ => throw (IO.userError "branch formula was not atomized")


-- A branch can force only a constructor while allowing several payloads.
-- The competing side fixes the other constructor, so a whole-value-only
-- branch analysis would miss this explanation.
private def variantBackend : Backend (StateM Queries) Formula Nat where
  query hyps goal _ := do
    modify (·.push (hyps.map (·.1)))
    match (List.range 6).find? fun i => hyps.all (fun (_, f) => f i) && !goal i with
    | some i => return .sat #[(`x, i % 3), (`y, i / 3)]
    | none => return .unsat
  falseF := no
  notF f := fun i => !f i
  conj fs := fun i => fs.all (fun f => f i)
  existsOutputs f := pure fun _ => (List.range 6).any f
  pin n v := pure (some (fun i => (if n == `x then i % 3 else i / 3) == v))
  pinVariant n v := pure do
    if n != `x then none else
    let variant : Variant := if v == 0 then ⟨"Decision::GiveUp", 0⟩ else ⟨"Decision::RetryAfter", 1⟩
    some (variant, fun i => if v == 0 then i % 3 == 0 else i % 3 != 0)
  render n v := pure <| if n == `y then (if v == 0 then "false" else "true")
    else if v == 0 then "Decision::GiveUp" else if v == 1 then "Decision::RetryAfter(false)" else "Decision::RetryAfter(true)"
  prime := id
  samePrimed _ := yes
  subst _ f := f

#eval do
  let group : BranchGroup Formula := {
    owner := `policy
    kind := .disjunction
    members := #[{ name := `policy.retry, formula := fun i => i % 3 != 0 },
                 { name := `policy.override, formula := fun i => i / 3 == 1 }]
  }
  let comp : Comp Formula := {
    path := `variants
    vars := variables
    assumes := #[]
    reqs := #[(`policy, fun i => i % 3 != 0 || i / 3 == 1),
              (`give_up, fun i => i % 3 == 0), (`no_override, fun i => i / 3 == 0)]
    expects := #[]
    triggers := #[]
    branchGroups := #[group]
  }
  let (r, _) := (checkRealizable variantBackend comp).run #[]
  let retry := r.branchConflicts[0]!.cases[0]!
  ensure (retry.clashes.size == 1) "variant-only forcing was not explained"
  let clash := retry.clashes[0]!
  ensure (clash.output == `x && clash.forced == Forced.variant ⟨"Decision::RetryAfter", 1⟩
    && clash.restForced == Forced.value "Decision::GiveUp") "wrong constructor forcing result"

-- Exactly-one alternatives contain the chosen positive member and every
-- unchosen negative member, including when three members are true.
#eval do
  let group : BranchGroup Formula := {
    owner := `choice, kind := .exactlyOne,
    members := #[{name := `choice.x, formula := x}, {name := `choice.y, formula := y},
                 {name := `choice.always, formula := yes}] }
  let alternatives := group.alternatives backend
  ensure (alternatives.size == 3) "exactly-one must retain all n alternatives"
  for i in List.range 4 do
    ensure ((alternatives.any fun a => a.formula i) == (!x i && !y i))
      "exactly-one is not parity when three members hold"
  ensure ((alternatives.toList.head?.map (fun (a : BranchAlternative Formula) => a.memberWanted)) == some #[(`choice.x, true), (`choice.y, false), (`choice.always, false)])
    "chosen/unchosen polarities were lost"
  let inactive := { group with guard? := some no }
  ensure ((inactive.alternatives backend).all fun alternative => (List.range 4).all alternative.formula)
    "inactive leading guard must make every completed alternative vacuous"
  let active := { group with guard? := some x }
  for i in List.range 4 do
    ensure (((active.alternatives backend).any fun a => a.formula i) == (!x i || (!x i && !y i)))
      "leading guard must wrap exactly-one as a whole"
  let singleton : BranchGroup Formula := {
    owner := `single, kind := .exactlyOne,
    members := #[{name := `single.x, formula := x}] }
  for i in List.range 4 do
    ensure (((singleton.alternatives backend).any (fun a => a.formula i)) == x i)
      "singleton exactly-one must be identity"
  let empty : BranchGroup Formula := {owner := `empty, kind := .exactlyOne, members := #[]}
  ensure ((empty.alternatives backend).isEmpty) "empty exactly-one has no satisfiable branch"
  let comp := { orComp with
    branchGroups := #[{ orGroup with kind := .exactlyOne }],
    reqs := #[(`policy, fun i => x i != y i), (`no_x, fun i => !x i), (`no_y, fun i => !y i)] }
  let (result, _) := (checkRealizable backend comp).run #[]
  ensure (result.verdict == Verdict.fail && result.branchConflicts[0]!.cases.size == 2)
    "exactly-one conflict must explain every chosen member"
  ensure (result.branchConflicts[0]!.cases[0]!.opposed.any (fun p => p.member == `policy.backoff && p.wanted))
    "chosen member positive forcing was lost"

-- Count actual backend calls for impossible disjuncts. With no candidates,
-- outputs or polarity checks, each alternative has exactly its exclusion
-- query and nonvacuity/model query, plus one shared consistency query. Cost must scale with retained members,
-- and the group budget must not cut a selected group's alternatives in half.
#eval do
  for n in List.range 6 do
    let members := (List.range n).toArray.map fun i =>
      ({ name := Name.num `cost (i + 1), formula := no } : BranchMember Formula)
    let group : BranchGroup Formula := { owner := `cost, kind := .disjunction, members }
    let (results, queries) := (branchConflictsOf backend #[group] #[] #[] #[`cost] #[] (some 1) false).run #[]
    ensure (if n == 0 then results.isEmpty else results.size == 1 && results[0]!.cases.size == n) "one query family per disjunct was not retained"
    ensure (queries.size == 1 + 2 * n) "branch query families contain hidden or missing backend calls"
    for member in members do
      ensure ((queries.filter (fun (query : Array Name) => query.contains member.name)).size == 2) "a branch's query family was duplicated or omitted"

-- Unknown or inconsistent premises cannot establish supplementary facts.
#eval do
  let second := { orGroup with owner := `second }
  let (unknown, queries) := (branchConflictsOf (backend false true) #[orGroup, second]
    #[] (orComp.reqs.push (`second, fun i => x i || y i)) #[`policy, `second, `no_x, `no_y] #[] (some 1)).run #[]
  ensure (unknown.isEmpty && queries.size == 1) "unknown consistency must be silent and consume only the selected group budget"
  let contradictory := #[(`x, x), (`not_x, fun i => !x i)]
  let (vacuous, queries) := (branchConflictsOf backend #[orGroup] #[] contradictory
    #[`policy, `x, `not_x] #[] none).run #[]
  ensure (vacuous.isEmpty && queries.size == 1) "an inconsistent rest cannot force every member by vacuity"
  let (proved, _) := (checkRealizable backend orComp).run #[]
  let bounded := Fren.Core.Enumeration.classify 2 false true proved
  ensure (bounded.clashes.isEmpty && bounded.branchConflicts.isEmpty)
    "inexact enumeration cannot publish unqualified all-model relationships"
  let exact := Fren.Core.Enumeration.classify 2 true true proved
  ensure (!exact.branchConflicts.isEmpty) "exact finite checking lost its general explanations"

-- Two independent input properties and one output: a bad input does not
-- make either equivalence alternative globally impossible.
private def eligible (i : Nat) : Bool := i % 2 == 1
private def budget (i : Nat) : Bool := i / 2 % 2 == 1
private def retry (i : Nat) : Bool := i / 4 == 1
private def inputBackend : Backend Id Formula Bool where
  query hs goal _ := match (List.range 8).find? (fun i => hs.all (fun (_, f) => f i) && !goal i) with
    | some i => .sat #[(`eligible, eligible i), (`budget, budget i), (`retry, retry i)]
    | none => .unsat
  falseF := no
  notF f := fun i => !f i
  conj fs := fun i => fs.all (· i)
  existsOutputs f := fun i => f (i % 4) || f (i % 4 + 4)
  pin name value := some fun i => (if name == `eligible then eligible i else if name == `budget then budget i else retry i) == value
  pinVariant _ _ := none
  render _ value := if value then "true" else "false"
  prime := id
  samePrimed _ := yes
  subst _ f := f
private def inputComp : Comp Formula := {
  path := `input_dependent
  vars := #[{name := `eligible, role := .input, isPub := true},
            {name := `budget, role := .input, isPub := true},
            {name := `retry, role := .output, isPub := true}]
  assumes := #[]
  reqs := #[(`policy, fun i => retry i == eligible i), (`deadline, fun i => !retry i || budget i)]
  expects := #[]
  triggers := #[]
  branchGroups := #[{
    owner := `policy
    kind := .equivalence
    members := #[{name := `policy.retry, formula := retry}, {name := `policy.eligible, formula := eligible}] }]
}
#eval do
  let result := checkRealizable inputBackend inputComp
  ensure (result.verdict == Verdict.fail) "the concrete bad input must remain a counterexample"
  ensure (result.clashes.isEmpty && result.branchConflicts.isEmpty)
    "input-only elimination leaked into a general explanation"
  ensure ((messages false result).size == 1) "an unproved relationship was replaced by repetitive core notes"
  let emptyGroup : BranchGroup Formula := {
    owner := `empty, kind := .disjunction, members := #[], guard? := some eligible }
  let guardedEmpty := { inputComp with reqs := #[(`empty, fun i => !eligible i)], branchGroups := #[emptyGroup] }
  let emptyResult := checkRealizable inputBackend guardedEmpty
  ensure (emptyResult.verdict == Verdict.fail && emptyResult.branchConflicts.isEmpty)
    "an empty guarded group produced a vacuous all-alternatives claim"
  let restricted := { inputComp with assumes := #[(`over_budget, fun i => !budget i)] }
  let general := checkRealizable inputBackend restricted
  ensure (general.verdict == Verdict.fail && general.branchConflicts.size == 1)
    "a genuine all-model relationship was lost"
  let group := general.branchConflicts[0]!
  ensure ((group.cases.filter (fun (alternative : BranchCaseConflict) => alternative.excluded)).size == 1)
    "a globally feasible equivalence alternative was ruled out"
  ensure (group.premises == #[`over_budget]) "general premise identities were not retained"
  let notes := branchMessages general
  ensure (notes.any fun note => (note.msg.headline.splitOn "Both operands of `policy` cannot be true").length > 1)
    "general explanations are not plain source-named sentences"
  ensure (notes.all fun note => (note.msg.headline.splitOn "case \"").length == 1 && (note.msg.headline.splitOn "reported input").length == 1)
    "general explanations reverted to quoted cases or a particular input"

end FrenTest.BranchForcing

-- fren-covers: check::branch_forcing, check::branch_member_polarity, check::branch_query_count, check::branch_query_families, check::conditional_branch_core, check::disjunction_core, lang::equivalence_branches, lang::exactly_one_branch

-- fren-covers: check::general_branch_explanation, check::retry_alternatives_general
