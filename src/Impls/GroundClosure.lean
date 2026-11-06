-- keep-sorted start
import FrenCore.GroundClosure
import Impls.GroundMatching
-- keep-sorted end

open Fren.Lang

namespace Fren.Impls.GroundClosure

open Fren.Core Fren.Core.GroundMatching Fren.Core.GroundClosure
open Fren.Impls.Theories
open Lean (Name)
open _root_.Fren (FinSet)

interp lang::GroundRules := List Rule
interp lang::GroundCandidate := Candidate
interp lang::GroundCandidateResult := Option Candidate
interp lang::GroundCandidates := List Candidate
interp lang::GroundRanks := List (Option Name)
interp lang::ground_rules_empty? := fun (rs : List Rule) => rs.isEmpty
interp lang::ground_first_rule := fun (rs : List Rule) => (rs.headD default).sentence
interp lang::ground_rest_rules := fun (rs : List Rule) => rs.tail
interp lang::ground_add_rule := fun sentence (rs : List Rule) => { sentence } :: rs
interp lang::ground_normalize_rules := fun ds (rs : List Rule) => rs.map (·.normalize ds)
interp lang::ground_closed_rules := fun (rs : List Rule) => rs.flatMap (·.terms)
interp lang::ground_listed_variables := fun ctx ds (vs : List (Name × Ty)) =>
  vs.flatMap fun (_, ty) => ((ctx.normalizeListed ds).listed ty).getD []
interp lang::ground_listed_rules := fun ctx ds (rs : List Rule) =>
  rs.flatMap fun r => r.sentence.variables.flatMap fun (_, ty) => ((ctx.normalizeListed ds).listed ty).getD []
interp lang::ground_subterms := subterms
interp lang::ground_subterms_many := fun (ts : List TheoryTerm) => ts.flatMap subterms
interp lang::ground_ground_terms := fun (ts : List TheoryTerm) => ts.filter (·.ground)
interp lang::ground_unique_terms := fun (ts : List TheoryTerm) => ts.eraseDups
interp lang::ground_all_ground? := fun (ts : List TheoryTerm) => ts.all (·.ground)
interp lang::ground_typed_many := fun ctx ts n ty (ss : List Substitution) => ss.flatMap (typedExtensions ctx n ty ts)
interp lang::ground_assign_one := fun ctx ds s pool n ty ss => assignOne (ctx.normalizeListed ds) { sentence := s } pool n ty ss
interp lang::ground_assign_from := fun ctx ds s pool vs ss => assignFrom (ctx.normalizeListed ds) { sentence := s } pool vs ss
interp lang::ground_assignments := fun ctx ds s pool => _root_.Fren.Core.GroundClosure.assignments (ctx.normalizeListed ds) { sentence := s } pool

impl ground_assignment_step: lang::ground_assignment_step for (ctx : Fren.Core.GroundMatching.Context) (ds : List (TheoryTerm × TheoryTerm))
    (s : TheorySentence) (pool : List TheoryTerm) (n : Name) (ty : Ty) (vs : List (Name × Ty)) (ss : List Substitution) {
  ctx := ctx, defs := ds, sentence := s, pool := pool, name := n, ty := ty, variables := vs, substitutions := ss,
  typed := ss.flatMap (typedExtensions ctx n ty pool),
  extended := assignOne (ctx.normalizeListed ds) { sentence := s } pool n ty ss,
  assigned := assignFrom (ctx.normalizeListed ds) { sentence := s } pool vs ss,
  all_assignments := _root_.Fren.Core.GroundClosure.assignments (ctx.normalizeListed ds) { sentence := s } pool,
} by
  intro ctx ds s pool n ty vs ss _
  refine ⟨?_, ?_, ?_, rfl⟩
  · cases ss <;> simp [fren_spec, List.headD]
  · cases hl : ctx.listed ty <;>
      cases hm : (s.domain :: (s.calls ++ s.claims)).any (_root_.Fren.Core.GroundMatching.mentions n) <;>
      cases ha : (({ sentence := s } : Rule).anchors ctx.items ++ s.calls.filter (outer ·)).any (_root_.Fren.Core.GroundMatching.mentions n) <;>
      simp only [fren_spec, assignOne, Rule.terms, Context.normalizeListed, List.cons_append, hl, hm, ha] <;>
      simp <;> rfl
  · cases vs with
    | nil => rfl
    | cons v vs => rcases v with ⟨n, ty⟩; simp [fren_spec, assignFrom, List.headD]

interp lang::ground_candidate := Candidate.mk
interp lang::ground_no_candidate := fun (_ : TheorySentence) => (none : Option Candidate)
interp lang::ground_some_candidate := fun (c : Candidate) => some c
interp lang::ground_candidate_present? := fun (c : Option Candidate) => c.isSome
interp lang::ground_candidate_value := fun (c : Option Candidate) => c.getD default
interp lang::ground_candidate_sentence := Candidate.sentence
interp lang::ground_candidate_anchors := Candidate.anchors
interp lang::ground_candidate_calls := Candidate.calls
interp lang::ground_candidate_subject := Candidate.subject
interp lang::ground_make_candidate := fun ctx i s images => makeCandidate ctx i { sentence := s } images
interp lang::ground_from_assignments := fun ctx i s ss => fromAssignments ctx i { sentence := s } ss
interp lang::ground_candidates := fun ctx ds i s pool => candidates (ctx.normalizeListed ds) i { sentence := s } pool
interp lang::ground_no_candidates := fun (_ : Nat) => ([] : List Candidate)
interp lang::ground_add_candidate := fun (c : Candidate) cs => c :: cs
interp lang::ground_candidates_empty? := fun (cs : List Candidate) => cs.isEmpty
interp lang::ground_first_candidate := fun (cs : List Candidate) => cs.headD default
interp lang::ground_rest_candidates := fun (cs : List Candidate) => cs.tail
interp lang::ground_append_candidates := fun (a b : List Candidate) => a ++ b
interp lang::ground_unique_candidates := fun (cs : List Candidate) => cs.eraseDups
interp lang::ground_candidate_apps := fun (ctx : Fren.Core.GroundMatching.Context) (cs : List Candidate) => cs.flatMap (·.applications ctx.items)
interp lang::ground_candidate_all_apps := fun (ctx : Fren.Core.GroundMatching.Context) (cs : List Candidate) => cs.flatMap (·.allApplications ctx.items)
interp lang::ground_seed_pool := fun ctx ds rs apps calls => seedPool (ctx.normalizeListed ds) rs { applications := apps, calls }
interp lang::ground_instantiable? := fun (ctx : Fren.Core.GroundMatching.Context) s => ({ sentence := s } : Rule).instantiable ctx by
  intro ctx s
  rfl
interp lang::ground_ranks_empty? := fun (rs : List (Option Name)) => rs.isEmpty
interp lang::ground_first_rank := fun (rs : List (Option Name)) => rs.headD none
interp lang::ground_rest_ranks := fun (rs : List (Option Name)) => rs.tail
interp lang::ground_no_ranks := fun (_ : List Name) => ([] : List (Option Name))
interp lang::ground_single_rank := fun (s : Option Name) => [s]
interp lang::ground_append_ranks := fun (a b : List (Option Name)) => a ++ b
interp lang::ground_reverse_order := fun (ns : List Name) => ns.reverse.map some
interp lang::ground_subject_ranks := fun (ctx : Fren.Core.GroundMatching.Context) => none :: ctx.items.reverse.map some
interp lang::ground_at_rank := fun ctx ds rs subject pool i => atRank (ctx.normalizeListed ds) subject pool i rs
interp lang::ground_build_ranks := fun ctx ds rs subjects pool => ranks (ctx.normalizeListed ds) rs subjects pool
interp lang::ground_universe := fun ctx ds rs apps calls => candidateUniverse (ctx.normalizeListed ds) rs { applications := apps, calls }
impl ground_candidate_step: lang::ground_candidate_step for (ctx : Fren.Core.GroundMatching.Context) (ds : List (TheoryTerm × TheoryTerm))
    (i : Nat) (s : TheorySentence) (images : Substitution) (ss : List Substitution) (pool : List TheoryTerm) {
  ctx := ctx, defs := ds, index := i, sentence := s, images := images, substitutions := ss, pool := pool,
  result := makeCandidate ctx i { sentence := s } images,
  collected := fromAssignments ctx i { sentence := s } ss,
  candidates := candidates (ctx.normalizeListed ds) i { sentence := s } pool,
} by
  intro ctx ds i s images ss pool _
  let sub := fun n => images.lookup n
  let result := s.instantiate sub
  let anchors := (Rule.anchors { sentence := s } ctx.items).map (·.substitute (theorySubstitution s.variables sub))
  let calls := (s.calls.filter (outer ·)).map (·.substitute (theorySubstitution s.variables sub))
  refine ⟨anchors, calls, sub, s, result.isSome, result.getD s, ?_⟩
  have hc : fromAssignments ctx i { sentence := s } ss =
      if ss.isEmpty then [] else
      if (makeCandidate ctx i { sentence := s } (ss.headD [])).isSome then
        (makeCandidate ctx i { sentence := s } (ss.headD [])).getD default ::
          fromAssignments ctx i { sentence := s } ss.tail
      else fromAssignments ctx i { sentence := s } ss.tail := by
    cases ss with
    | nil => rfl
    | cons image rest =>
      cases h : makeCandidate ctx i { sentence := s } image <;> simp [fromAssignments, h, List.headD]

  have hn : ∀ image, makeCandidate (ctx.normalizeListed ds) i { sentence := s } image =
      makeCandidate ctx i { sentence := s } image := by
    intro image
    simp only [makeCandidate, Context.normalizeListed]
  have hp : ∀ xs, fromAssignments (ctx.normalizeListed ds) i { sentence := s } xs =
      fromAssignments ctx i { sentence := s } xs := by
    intro xs
    exact congrArg (fun f => xs.filterMap f) (funext hn)
  have hm : makeCandidate ctx i { sentence := s } images =
      if result.isSome && (anchors ++ calls).all (·.ground) then
        some { rule := i, sentence := result.getD s, anchors, calls, subject := ({ sentence := s } : Rule).subject ctx.items }
      else none := by
    change (result.bind fun sentence =>
      if !(anchors ++ calls).all (·.ground) then none else
        some ({ rule := i, sentence, anchors, calls, subject := ({ sentence := s } : Rule).subject ctx.items } : Candidate)) = _
    cases hi : result <;> cases hg : (anchors ++ calls).all (·.ground) <;> simp
  have hi := _root_.Fren.Impls.Theories.theory_instance s sub (by trivial)
  simpa [fren_spec, hm, hc, candidates, hp, anchors, calls, sub, result] using hi

impl ground_pool_step: lang::ground_pool_step for (ctx : Fren.Core.GroundMatching.Context) (ds : List (TheoryTerm × TheoryTerm))
    (rs : List Rule) (vs : List (Name × Ty)) (ts : List TheoryTerm) (t : TheoryTerm)
    (apps calls : List TheoryTerm) (cs : List Candidate) {
  ctx := ctx, defs := ds, rules := rs, variables := vs, terms := ts, term := t,
  query_apps := apps, query_calls := calls, candidates := cs,
  normalized := rs.map (·.normalize ds),
  closed_terms := rs.flatMap (·.terms),
  listed_variables := vs.flatMap (fun (_, ty) => ((ctx.normalizeListed ds).listed ty).getD []),
  listed_rules := rs.flatMap (fun r => r.sentence.variables.flatMap (fun (_, ty) => ((ctx.normalizeListed ds).listed ty).getD [])),
  subterms := subterms t, many := ts.flatMap subterms,
  apps := cs.flatMap (·.applications ctx.items),
  all_apps := cs.flatMap (·.allApplications ctx.items),
  ground_terms := ts.filter (·.ground), all_ground? := ts.all (·.ground),
  seeds := seedPool (ctx.normalizeListed ds) rs { applications := apps, calls },
} by
  intro ctx ds rs vs ts t apps calls cs _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases rs <;> simp [fren_spec, Rule.normalize, List.headD]
  · cases rs <;> simp [fren_spec, Rule.terms, List.headD]
  · cases vs with
    | nil => rfl
    | cons v vs =>
      rcases v with ⟨n, ty⟩
      cases hl : ctx.listed ty <;> simp [fren_spec, Context.normalizeListed, hl, List.headD]
  · cases rs <;> simp [fren_spec, List.headD]
  · cases t <;> simp [fren_spec, subterms, termKind]
  · cases ts <;> simp [fren_spec, List.headD]
  · cases cs <;> simp [fren_spec, Candidate.applications, Candidate.allApplications, List.headD]
  · cases cs <;> simp [fren_spec, Candidate.allApplications, List.headD]
  · cases ts with
    | nil => rfl
    | cons t ts => cases h : t.ground <;> simp [fren_spec, h, List.headD]
  · cases ts <;> simp [fren_spec, List.headD]
  · simp [fren_spec, seedPool, List.append_assoc]

impl ground_universe_step: lang::ground_universe_step for (ctx : Fren.Core.GroundMatching.Context) (ds : List (TheoryTerm × TheoryTerm))
    (rs : List Rule) (subject : Option Name) (subjects : List (Option Name)) (order : List Name)
    (pool : List TheoryTerm) (i : Nat) (apps calls : List TheoryTerm) {
  ctx := ctx, defs := ds, rules := rs, subject := subject, ranks := subjects, order := order,
  pool := pool, index := i, query_apps := apps, query_calls := calls,
  reversed_ranks := order.reverse.map some, subjects := none :: ctx.items.reverse.map some,
  at_rank := atRank (ctx.normalizeListed ds) subject pool i rs,
  built := ranks (ctx.normalizeListed ds) rs subjects pool,
  universe_candidates := candidateUniverse (ctx.normalizeListed ds) rs { applications := apps, calls },
} by
  intro ctx ds rs subject subjects order pool i apps calls _
  refine ⟨?_, rfl, ?_, ?_, rfl⟩
  · cases order <;> simp [fren_spec, List.headD]
  · cases rs with
    | nil => rfl
    | cons r rs =>
      cases r
      simp only [fren_spec, atRank]
      rw [_root_.Fren.Impls.GroundMatching.instantiable_normalizeListed]
      simp [Context.normalizeListed, List.headD, Bool.and_eq_true, beq_iff_eq]
  · cases subjects <;> simp [fren_spec, ranks, Context.normalizeListed, List.headD]

interp lang::ground_contains? := fun (ts : List TheoryTerm) t => ts.contains t
interp lang::ground_order_contains? := fun (ns : List Name) n => ns.contains n
interp lang::ground_no_order := fun (_ : TheoryTerm) => ([] : List Name)
interp lang::ground_add_name := fun (n : Name) ns => n :: ns
interp lang::ground_term_heads := fun (ts : List TheoryTerm) => ts.filterMap headName
interp lang::ground_query_terms := fun (ctx : Fren.Core.GroundMatching.Context) apps accepted =>
  queryTerms ctx.items { applications := apps } accepted
interp lang::ground_query_subjects := fun (ctx : Fren.Core.GroundMatching.Context) apps calls accepted =>
  subjectNames ctx.items { applications := apps, calls } accepted
interp lang::ground_enabled? := fun (ctx : Fren.Core.GroundMatching.Context) apps calls c (accepted : List Candidate) =>
  enabled ctx.items { applications := apps, calls } c (FinSet.ofList accepted)
interp lang::ground_ready := fun (ctx : Fren.Core.GroundMatching.Context) apps calls (pending initial : List Candidate) =>
  pending.filter (fun c => enabled ctx.items { applications := apps, calls } c (FinSet.ofList initial))
interp lang::ground_remaining := fun (ctx : Fren.Core.GroundMatching.Context) apps calls (pending initial : List Candidate) =>
  pending.filter (fun c => !enabled ctx.items { applications := apps, calls } c (FinSet.ofList initial))
interp lang::ground_saturate := fun (ctx : Fren.Core.GroundMatching.Context) apps calls pending initial =>
  (FiniteActivation.run (enabled ctx.items { applications := apps, calls }) pending initial).members

impl ground_applications_step: lang::ground_applications_step for (ctx : Fren.Core.GroundMatching.Context)
    (apps calls ts : List TheoryTerm) (order : List Name) (accepted : List Candidate) (t : TheoryTerm) (n : Name) {
  ctx := ctx, query_apps := apps, query_calls := calls, accepted := accepted, terms := ts, order := order, term := t, name := n,
  term_present? := ts.contains t, name_present? := order.contains n,
  heads := ts.filterMap headName,
  applications := queryTerms ctx.items { applications := apps } accepted,
  subjects := subjectNames ctx.items { applications := apps, calls } accepted,
} by
  intro ctx apps calls ts order accepted t n _
  refine ⟨?_, ?_, ?_, rfl, rfl⟩
  · cases ts <;> simp [fren_spec, List.headD]
  · cases order <;> simp [fren_spec, List.headD]
  · cases ts with
    | nil => rfl
    | cons t ts =>
      cases h : (spine t).1 <;> simp [fren_spec, headName, h, termKind, List.headD]

impl ground_enabled_step: lang::ground_enabled_step for (ctx : Fren.Core.GroundMatching.Context)
    (apps calls : List TheoryTerm) (c : Candidate) (accepted : List Candidate) {
  ctx := ctx, query_apps := apps, query_calls := calls, candidate := c, accepted := accepted,
  enabled? := enabled ctx.items { applications := apps, calls } c (FinSet.ofList accepted),
} by
  intro ctx apps calls c accepted _
  have hs : subjectsOf ctx.items { applications := apps, calls } (FinSet.ofList accepted) =
      FinSet.ofList (subjectNames ctx.items { applications := apps, calls } accepted) := by
    apply FinSet.ext
    intro n
    simp [subjectsOf, subjectNames, FiniteActivation.mem_collect,
      List.mem_filterMap, or_and_right, exists_or, or_assoc, or_comm]
  cases h : c.subject <;>
    simp [fren_spec, enabled, applicationsOf_ofList, hs, FinSet.subset_def,
      queryTerms, subjectNames, h, List.mem_filterMap]

impl ground_activation_step: lang::ground_activation_step for (ctx : Fren.Core.GroundMatching.Context)
    (apps calls : List TheoryTerm) (pending initial : List Candidate) {
  ctx := ctx, query_apps := apps, query_calls := calls, pending := pending, initial := initial,
  ready := pending.filter (fun c => enabled ctx.items { applications := apps, calls } c (FinSet.ofList initial)),
  remaining := pending.filter (fun c => !enabled ctx.items { applications := apps, calls } c (FinSet.ofList initial)),
  result := (FiniteActivation.run (enabled ctx.items { applications := apps, calls }) pending initial).members,
} by
  intro ctx apps calls pending initial _
  refine ⟨?_, ?_, ?_⟩
  · cases pending with
    | nil => rfl
    | cons c cs =>
      cases h : enabled ctx.items { applications := apps, calls } c (FinSet.ofList initial) <;>
        simp [fren_spec, List.headD, h]
  · cases pending with
    | nil => rfl
    | cons c cs =>
      cases h : enabled ctx.items { applications := apps, calls } c (FinSet.ofList initial) <;>
        simp [fren_spec, List.headD, h]
  · simp only [fren_spec]
    rw [FiniteActivation.run]
    split <;> rfl

impl ground_close_step: lang::ground_close_step for (ctx : Fren.Core.GroundMatching.Context) (rs : List Rule) (apps calls : List TheoryTerm) {
  ctx := ctx, rules := rs, query_apps := apps, query_calls := calls,
  instances := (close ctx rs { applications := apps, calls }).instanceList,
  applications := (close ctx rs { applications := apps, calls }).applicationList,
} by
  intro ctx rs apps calls _
  let ds := _root_.Fren.Core.GroundMatching.definitions ctx.definitions
  let rs' := rs.map (·.normalize ds)
  let q := normalizedQuery ctx ds { applications := apps, calls }
  let cs := candidateUniverse (ctx.normalizeListed ds) rs' q
  let result := FiniteActivation.run (enabled ctx.items q) cs []
  let ready := cs.filter (fun c => enabled ctx.items q c (FinSet.ofList []))
  let remaining := cs.filter (fun c => !enabled ctx.items q c (FinSet.ofList []))
  refine ⟨ds, rs', q.applications, q.calls, cs, ctx, q.applications, q.calls, cs, [], ready, remaining, result.members, ?_⟩
  have ha := ground_activation_step ctx q.applications q.calls cs [] (by trivial)
  simpa [fren_spec, close, prepare, normalizedQuery, GroundMatching.prepareQuery, queryTerms, Context.normalizeListed,
    List.flatMap_map, ds, rs', q, cs, result, ready, remaining] using ha

end Fren.Impls.GroundClosure
