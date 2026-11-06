-- keep-sorted start
import FrenCore.GroundMatching
import Impls.Theories
-- keep-sorted end

open Fren.Lang

namespace Fren.Impls.GroundMatching

open Fren.Core Fren.Core.GroundMatching Fren.Impls.Theories
open Lean (Name)

interp lang::GroundContext := Context
interp lang::GroundImages := Substitution
interp lang::GroundDefinitions := List (TheoryTerm × TheoryTerm)
interp lang::GroundResult := Option Substitution
interp lang::ground_type_present? := fun (ctx : Context) t => (ctx.typeOf t).isSome
interp lang::ground_type := fun (ctx : Context) t => (ctx.typeOf t).getD default
interp lang::ground_image_present? := fun (s : Substitution) n => (s.lookup n).isSome
interp lang::ground_image := fun (s : Substitution) n => (s.lookup n).getD default
interp lang::ground_extend := fun (s : Substitution) n t => s ++ [(n, t)]
interp lang::ground_parameter_present? := fun (vs : List (Name × Ty)) n => (vs.lookup n).isSome
interp lang::ground_parameter := fun (vs : List (Name × Ty)) n => (vs.lookup n).getD default
interp lang::ground_success := fun (s : Substitution) => some s
interp lang::ground_failure := fun (_ : Substitution) => (none : Option Substitution)
interp lang::ground_succeeded? := fun (r : Option Substitution) => r.isSome
interp lang::ground_result_images := fun (r : Option Substitution) => r.getD []
interp lang::ground_match := fun (ctx : Context) vs p t s => Fren.Core.GroundMatching.matchTerm vs ctx.typeOf p t s

impl ground_parameter_step: lang::ground_parameter_step for (vs : List (Name × Ty)) (n : Name) {
  variables := vs,
  name := n,
  present? := (vs.lookup n).isSome,
  result := (vs.lookup n).getD default,
} by
  intro vs n _
  have mem : (vs.lookup n).isSome = true ↔ n ∈ vs.map Prod.fst := by
    simp only [List.lookup_isSome_iff, beq_iff_eq, List.mem_map]
    constructor
    · rintro ⟨p, hp, hn⟩; exact ⟨p, hp, hn.symm⟩
    · rintro ⟨p, hp, hn⟩; exact ⟨p, hp, hn.symm⟩
  simp only [fren_spec]
  constructor
  · simpa only [Fren.FinSet.mem_ofList] using mem
  · cases vs with
    | nil => rfl
    | cons v vs =>
      rcases v with ⟨k, ty⟩
      by_cases h : k = n
      · subst k; simp [List.headD]
      · have hb : (n == k) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
        simp [List.lookup_cons, List.headD, h, hb]

impl ground_extension_step: lang::ground_extension_step for (s : Substitution) (n qn : Name) (t : TheoryTerm) {
  images := s,
  name := n,
  value := t,
  queried := qn,
  present? := ((s ++ [(n, t)]).lookup qn).isSome,
  result := ((s ++ [(n, t)]).lookup qn).getD default,
} by
  intro s n qn t h
  simp only [fren_spec] at h ⊢
  have fresh : s.lookup n = none := by
    cases hs : s.lookup n with
    | none => rfl
    | some v => simp [hs] at h
  have lookup : (s ++ [(n, t)]).lookup qn = if qn = n then some t else s.lookup qn := by
    by_cases hn : qn = n
    · subst qn; simp [List.lookup_append, fresh]
    · have hb : (qn == n) = false := beq_eq_false_iff_ne.mpr hn
      simp [List.lookup_append, List.lookup_cons, hb, hn]
  rw [lookup]
  split <;> simp_all

impl ground_match_step: lang::ground_match_step for (ctx : Context) (vs : List (Name × Ty))
    (p t : TheoryTerm) (s : Substitution) {
  ctx := ctx,
  variables := vs,
  pattern := p,
  target := t,
  images := s,
  result := Fren.Core.GroundMatching.matchTerm vs ctx.typeOf p t s,
} by
  intro ctx vs p t s _
  cases p with
  | «variable» n =>
    cases hv : vs.lookup n with
    | none => simp [fren_spec, termKind, Fren.Core.GroundMatching.matchTerm, hv]
    | some ty =>
      cases ht : ctx.typeOf t <;> cases hs : s.lookup n <;> simp [fren_spec, termKind, Fren.Core.GroundMatching.matchTerm, hv, ht, hs]
  | app f a =>
    cases t with
    | app g b =>
      cases hm : Fren.Core.GroundMatching.matchTerm vs ctx.typeOf f g s <;> simp [fren_spec, termKind, Fren.Core.GroundMatching.matchTerm, hm]
    | _ => simp [fren_spec, termKind, Fren.Core.GroundMatching.matchTerm]
  | all ty b => cases t <;> simp [fren_spec, termKind, Fren.Core.GroundMatching.matchTerm]
  | ex ty b => cases t <;> simp [fren_spec, termKind, Fren.Core.GroundMatching.matchTerm]
  | _ => simp [fren_spec, termKind, Fren.Core.GroundMatching.matchTerm]

interp lang::ground_definitions_empty? := fun (ds : List (TheoryTerm × TheoryTerm)) => ds.isEmpty
interp lang::ground_definition_name := fun (ds : List (TheoryTerm × TheoryTerm)) => (ds.headD default).1
interp lang::ground_definition_value := fun (ds : List (TheoryTerm × TheoryTerm)) => (ds.headD default).2
interp lang::ground_definitions_rest := fun (ds : List (TheoryTerm × TheoryTerm)) => ds.tail
interp lang::ground_add_definition := fun n v (ds : List (TheoryTerm × TheoryTerm)) => (n, v) :: ds
interp lang::ground_lookup := fun (ds : List (TheoryTerm × TheoryTerm)) t => definitionValue ds.toArray t t
interp lang::ground_normalize := Fren.Core.GroundMatching.normalize
interp lang::ground_normalize_definitions := Fren.Core.GroundMatching.definitions

impl ground_normalization: lang::ground_normalization for (ds : List (TheoryTerm × TheoryTerm)) (t other : TheoryTerm) {
  defs := ds,
  term := t,
  other := other,
  lookup_value := definitionValue ds.toArray t t,
  normalized := Fren.Core.GroundMatching.normalize ds t,
  normalized_definitions := Fren.Core.GroundMatching.definitions ds,
  same? := Fren.Core.GroundMatching.same ds t other,
} by
  intro ds t other _
  have hl : definitionValue ds.toArray t t = if ds.isEmpty then t else
      if (ds.headD default).1 == t then (ds.headD default).2 else definitionValue ds.tail.toArray t t := by
    cases ds with
    | nil => rfl
    | cons d ds =>
      by_cases h : d.1 = t
      · simp [definitionValue, List.find?, List.headD, h]
      · have hb : (d.1 == t) = false := beq_eq_false_iff_ne.mpr h
        simp [definitionValue, List.find?, List.headD, hb]
  have hd : Fren.Core.GroundMatching.definitions ds = if ds.isEmpty then ds else
      ((ds.headD default).1, Fren.Core.GroundMatching.normalize (Fren.Core.GroundMatching.definitions ds.tail) (ds.headD default).2) :: Fren.Core.GroundMatching.definitions ds.tail := by
    cases ds <;> rfl
  simp only [fren_spec]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [beq_iff_eq] using hl
  · cases t with
    | app f a => cases f <;> simp [termKind, Matching.normalize, DefinitionSyntax.expand, TheoryTerm.expandDefinitions]
    | _ => simp [termKind, Matching.normalize, DefinitionSyntax.expand, TheoryTerm.expandDefinitions, definitionValue]
  · exact hd
  · simp [Fren.Core.Matching.same]

interp lang::GroundOrder := List Name
interp lang::GroundSubject := Option Name
interp lang::ground_order_empty? := fun (ns : List Name) => ns.isEmpty
interp lang::ground_order_first := fun (ns : List Name) => ns.headD .anonymous
interp lang::ground_order_rest := fun (ns : List Name) => ns.tail
interp lang::ground_no_subject := fun (_ : List Name) => (none : Option Name)
interp lang::ground_named := fun (n : Name) => some n
interp lang::ground_subject_present? := fun (s : Option Name) => s.isSome
interp lang::ground_subject_name := fun (s : Option Name) => s.getD .anonymous
interp lang::ground_subject := Fren.Core.GroundMatching.lastSubject
interp lang::ground_uses? := Fren.Core.GroundMatching.uses
interp lang::ground_items := fun (ctx : Context) => Fren.FinSet.ofList ctx.items
interp lang::ground_head := fun t => (Fren.Core.GroundMatching.spine t).1
interp lang::ground_args := fun t => (Fren.Core.GroundMatching.spine t).2
interp lang::ground_append := fun (a b : List TheoryTerm) => a ++ b
interp lang::ground_no_terms := fun (_ : TheoryTerm) => ([] : List TheoryTerm)
interp lang::ground_outer? := fun (t : TheoryTerm) (depth : Nat) => Fren.Core.GroundMatching.outer t depth
interp lang::ground_mentions? := Fren.Core.GroundMatching.mentions
interp lang::ground_vars_mention? := fun (vs : List (Name × Ty)) t => vs.any fun (n, _) => Fren.Core.GroundMatching.mentions n t
interp lang::ground_compound_arg? := Fren.Core.GroundMatching.compoundArg
interp lang::ground_apps := fun (ctx : Context) t => Fren.Core.GroundMatching.applications ctx.items t
interp lang::ground_argument_apps := fun (ctx : Context) t => Fren.Core.GroundMatching.argumentApps ctx.items t

impl ground_shape_step: lang::ground_shape_step for (ctx : Context) (t : TheoryTerm)
    (vs : List (Name × Ty)) (n : Name) (depth : Nat) {
  ctx := ctx, term := t, variables := vs, name := n, depth := depth,
  head := (Fren.Core.GroundMatching.spine t).1, args := (Fren.Core.GroundMatching.spine t).2, outer? := Fren.Core.GroundMatching.outer t depth,
  mentions? := Fren.Core.GroundMatching.mentions n t, compound? := Fren.Core.GroundMatching.compoundArg vs t,
  apps := Fren.Core.GroundMatching.applications ctx.items t, argument_apps := Fren.Core.GroundMatching.argumentApps ctx.items t,
} by
  intro ctx t vs n depth _
  cases t with
  | app f a =>
    cases hs : Fren.Core.GroundMatching.spine f with
    | mk h args =>
      cases h <;> simp [fren_spec, Fren.Core.GroundMatching.spine, hs, Fren.Core.GroundMatching.outer, Fren.Core.GroundMatching.mentions, Fren.Core.GroundMatching.compoundArg, Fren.Core.GroundMatching.applications, Fren.Core.GroundMatching.argumentApps, termKind]
  | _ => simp [fren_spec, Fren.Core.GroundMatching.spine, Fren.Core.GroundMatching.outer, Fren.Core.GroundMatching.mentions, Fren.Core.GroundMatching.compoundArg, Fren.Core.GroundMatching.applications, Fren.Core.GroundMatching.argumentApps, termKind]

impl ground_subject_step: lang::ground_subject_step for (ns : List Name) (ts : List TheoryTerm) (n : Name) {
  order := ns, apps := ts, name := n,
  subject := Fren.Core.GroundMatching.lastSubject ns ts, subject_used? := Fren.Core.GroundMatching.uses ts n,
} by
  intro ns ts n _
  constructor
  · cases ns with
    | nil => rfl
    | cons x xs => cases h : Fren.Core.GroundMatching.lastSubject xs ts <;> simp [fren_spec, Fren.Core.GroundMatching.lastSubject, h, List.headD]
  · cases ts with
    | nil => simp [fren_spec, Fren.Core.GroundMatching.uses]
    | cons t ts => cases h : (Fren.Core.GroundMatching.spine t).1 <;> simp [fren_spec, Fren.Core.GroundMatching.uses, headName, h, List.headD, termKind]

interp lang::ground_subject_apps := Fren.Core.GroundMatching.subjectApps
interp lang::ground_compound_apps := Fren.Core.GroundMatching.compoundApps
interp lang::ground_anchors := Fren.Core.GroundMatching.anchors
interp lang::ground_any_mentions? := fun n (ts : List TheoryTerm) => ts.any (Fren.Core.GroundMatching.mentions n)
interp lang::ground_listed? := fun (ctx : Context) ty => (ctx.listed ty).isSome
interp lang::ground_binding? := Fren.Core.GroundMatching.binding
interp lang::ground_any_compound? := fun vs (ts : List TheoryTerm) => ts.any (Fren.Core.GroundMatching.compoundArg vs)

impl ground_selection_step: lang::ground_selection_step for (s : Option Name)
    (ts : List TheoryTerm) (vs : List (Name × Ty)) (n : Name) {
  subject := s, apps := ts, variables := vs, name := n,
  subject_apps := Fren.Core.GroundMatching.subjectApps s ts, compounds := Fren.Core.GroundMatching.compoundApps vs ts, anchors := Fren.Core.GroundMatching.anchors vs ts,
  mentioned? := ts.any (Fren.Core.GroundMatching.mentions n), compound_argument? := ts.any (Fren.Core.GroundMatching.compoundArg vs),
} by
  intro s ts vs n _
  cases ts with
  | nil => simp [fren_spec, Fren.Core.GroundMatching.subjectApps, Fren.Core.GroundMatching.compoundApps, Fren.Core.GroundMatching.anchors]
  | cons t ts =>
    cases s <;> cases h : (Fren.Core.GroundMatching.spine t).1 <;>
      simp [fren_spec, Fren.Core.GroundMatching.subjectApps, Fren.Core.GroundMatching.compoundApps, Fren.Core.GroundMatching.anchors, List.filter_cons, headName, h, termKind, List.headD]

impl ground_variables_step: lang::ground_variables_step for (ctx : Context) (vs : List (Name × Ty))
    (t : TheoryTerm) (apps matched : List TheoryTerm) {
  ctx := ctx, variables := vs, term := t, apps := apps, matched := matched,
  mentions? := vs.any (fun (n, _) => Fren.Core.GroundMatching.mentions n t),
  binding? := Fren.Core.GroundMatching.binding ctx apps matched vs,
} by
  intro ctx vs t apps matched _
  cases vs with
  | nil => simp [fren_spec, Fren.Core.GroundMatching.binding]
  | cons v vs => rcases v with ⟨n, ty⟩; simp [fren_spec, Fren.Core.GroundMatching.binding, List.headD]

interp lang::GroundMatches := List Substitution
interp lang::ground_matches_empty? := fun (ss : List Substitution) => ss.isEmpty
interp lang::ground_matches_first := fun (ss : List Substitution) => ss.headD []
interp lang::ground_matches_rest := fun (ss : List Substitution) => ss.tail
interp lang::ground_no_matches := fun (_ : List (Name × Ty)) => ([] : List Substitution)
interp lang::ground_add_match := fun s (ss : List Substitution) => s :: ss
interp lang::ground_append_matches := fun (a b : List Substitution) => a ++ b
interp lang::ground_unique_matches := fun (ss : List Substitution) => ss.eraseDups
interp lang::ground_targets := Fren.Core.GroundMatching.matchTargets
interp lang::ground_many := fun ctx vs p ts (ss : List Substitution) => ss.flatMap (Fren.Core.GroundMatching.matchTargets ctx vs p ts)
interp lang::ground_join := Fren.Core.GroundMatching.join

impl ground_join_step: lang::ground_join_step for (ctx : Context) (vs : List (Name × Ty)) (p : TheoryTerm)
    (ps ts : List TheoryTerm) (s : Substitution) (ss : List Substitution) {
  ctx := ctx, variables := vs, pattern := p, patterns := ps, targets := ts, images := s, substitutions := ss,
  target_matches := Fren.Core.GroundMatching.matchTargets ctx vs p ts s,
  many := ss.flatMap (Fren.Core.GroundMatching.matchTargets ctx vs p ts),
  joined := Fren.Core.GroundMatching.join ctx vs ps ts ss,
} by
  intro ctx vs p ps ts s ss _
  refine ⟨?_, ?_, ?_⟩
  · cases ts with
    | nil => rfl
    | cons t ts =>
      cases hg : t.ground <;> cases hm : Fren.Core.GroundMatching.matchTerm vs ctx.typeOf p t s <;>
        simp [fren_spec, Fren.Core.GroundMatching.matchTargets, hg, hm, List.headD]
  · cases ss <;> simp [fren_spec, List.headD]
  · cases ps <;> simp [fren_spec, Fren.Core.GroundMatching.join, List.headD]

interp lang::ground_listed_values := fun (ctx : Context) ty => (ctx.listed ty).getD []
interp lang::ground_typed_extensions := Fren.Core.GroundMatching.typedExtensions
interp lang::ground_listed_extensions := Fren.Core.GroundMatching.listedExtensions
interp lang::ground_listed_many := fun ctx ts n ty (ss : List Substitution) => ss.flatMap (Fren.Core.GroundMatching.listedExtensions ctx ts n ty)
interp lang::ground_complete_listed := Fren.Core.GroundMatching.completeListed

impl ground_listed_step: lang::ground_listed_step for (ctx : Context) (ts : List TheoryTerm) (n : Name) (ty : Ty)
    (values : List TheoryTerm) (s : Substitution) (ss : List Substitution) (vs : List (Name × Ty)) {
  ctx := ctx, terms := ts, name := n, ty := ty, values := values, images := s, substitutions := ss, variables := vs,
  typed := Fren.Core.GroundMatching.typedExtensions ctx n ty values s,
  extended := Fren.Core.GroundMatching.listedExtensions ctx ts n ty s,
  many := ss.flatMap (Fren.Core.GroundMatching.listedExtensions ctx ts n ty),
  completed := Fren.Core.GroundMatching.completeListed ctx ts vs ss,
} by
  intro ctx ts n ty values s ss vs _
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases values with
    | nil => rfl
    | cons t values =>
      cases ht : ctx.typeOf t with
      | none => simp [fren_spec, Fren.Core.GroundMatching.typedExtensions, ht, List.headD]
      | some ty' =>
        cases hg : t.ground <;> by_cases he : ty' = ty <;>
          simp [fren_spec, Fren.Core.GroundMatching.typedExtensions, ht, hg, he, List.headD]
  · cases hl : ctx.listed ty <;> cases hi : (s.lookup n).isSome <;>
      cases hm : ts.any (Fren.Core.GroundMatching.mentions n) <;> simp [fren_spec, Fren.Core.GroundMatching.listedExtensions, hl, hi, hm]
  · cases ss <;> simp [fren_spec, List.headD]
  · cases vs with
    | nil => rfl
    | cons v vs => rcases v with ⟨n, ty⟩; simp [fren_spec, Fren.Core.GroundMatching.completeListed, List.headD]

interp lang::ground_apps_list := fun (ctx : Context) (ts : List TheoryTerm) => ts.flatMap (Fren.Core.GroundMatching.applications ctx.items)
interp lang::ground_call_apps := fun (ctx : Context) ts => Fren.Core.GroundMatching.callApplications ctx.items ts
interp lang::ground_outer_apps := fun (ts : List TheoryTerm) => ts.filter (Fren.Core.GroundMatching.outer ·)
interp lang::ground_order := Context.items
interp lang::ground_initial_matches := fun (_ : List (Name × Ty)) => ([[]] : List Substitution)

impl ground_sentence_lists_step: lang::ground_sentence_lists_step for (ctx : Context) (ts : List TheoryTerm) {
  ctx := ctx, terms := ts,
  apps := ts.flatMap (Fren.Core.GroundMatching.applications ctx.items),
  calls := Fren.Core.GroundMatching.callApplications ctx.items ts,
  outer_apps := ts.filter (Fren.Core.GroundMatching.outer ·),
} by
  intro ctx ts _
  cases ts <;> simp [fren_spec, Fren.Core.GroundMatching.callApplications, List.filter_cons, List.headD]

interp lang::ground_rule_apps := fun (ctx : Context) s => ({ sentence := s } : Rule).applications ctx.items
interp lang::ground_rule_subject := fun (ctx : Context) s => ({ sentence := s } : Rule).subject ctx.items
interp lang::ground_rule_anchors := fun (ctx : Context) s => ({ sentence := s } : Rule).anchors ctx.items

impl ground_rule_step: lang::ground_rule_step for (ctx : Context) (s : TheorySentence) (apps calls : List TheoryTerm) {
  ctx := ctx, sentence := s, query_apps := apps, query_calls := calls,
  apps := ({ sentence := s } : Rule).applications ctx.items,
  subject := ({ sentence := s } : Rule).subject ctx.items,
  anchors := ({ sentence := s } : Rule).anchors ctx.items,
  binding? := ({ sentence := s } : Rule).instantiable ctx,
  substitutions := Fren.Core.GroundMatching.matchNormalized ctx { sentence := s } { applications := apps, calls },
} by
  intro ctx s apps calls _
  simp only [fren_spec]
  refine ⟨rfl, rfl, rfl, Iff.rfl, ?_⟩
  cases hs : ({ sentence := s } : Rule).subject ctx.items <;>
    simp [Rule.terms, Fren.Core.GroundMatching.matchNormalized, hs]

interp lang::ground_context_definitions := Context.definitions
interp lang::ground_normalize_terms := fun ds (ts : List TheoryTerm) => ts.map (Fren.Core.GroundMatching.normalize ds)
interp lang::ground_normalize_sentence := fun ds s => (({ sentence := s } : Rule).normalize ds).sentence
interp lang::ground_prepare_context := Context.normalizeListed

impl ground_preparation_step: lang::ground_preparation_step for (ctx : Context)
    (ds : List (TheoryTerm × TheoryTerm)) (sentence : TheorySentence) (ts : List TheoryTerm)
    (ty : Ty) (t : TheoryTerm) {
  ctx := ctx, defs := ds, sentence := sentence, terms := ts, ty := ty, term := t,
  normalized_terms := ts.map (Fren.Core.GroundMatching.normalize ds),
  normalized_sentence := (({ sentence } : Rule).normalize ds).sentence,
  normalized_context := ctx.normalizeListed ds,
  prepared_order := (ctx.normalizeListed ds).items,
  prepared_definitions := (ctx.normalizeListed ds).definitions,
  prepared_type_present? := ((ctx.normalizeListed ds).typeOf t).isSome,
  prepared_type := ((ctx.normalizeListed ds).typeOf t).getD default,
  prepared_listed? := ((ctx.normalizeListed ds).listed ty).isSome,
  prepared_values := ((ctx.normalizeListed ds).listed ty).getD [],
} by
  intro ctx ds sentence ts ty t _
  cases ts <;> cases hl : ctx.listed ty <;>
    simp [fren_spec, Rule.normalize, Context.normalizeListed, hl, List.headD]

interp lang::GroundSentences := List TheorySentence
interp lang::ground_no_sentences := fun (_ : TheorySentence) => ([] : List TheorySentence)
interp lang::ground_add_sentence := fun sentence sentences => sentence :: sentences

interp lang::ground_image_substitution := fun (s : Substitution) n => s.lookup n
interp lang::ground_instances_for := fun sentence ss =>
  Fren.Core.GroundMatching.instantiateMatches sentence ss

impl ground_instance_list_step: lang::ground_instance_list_step for (sentence : TheorySentence)
    (ss : List Substitution) (n : Name) {
  sentence := sentence, substitutions := ss, name := n,
  head_image_present? := ((ss.headD []).lookup n).isSome,
  head_image_value := ((ss.headD []).lookup n).getD default,
  instances := Fren.Core.GroundMatching.instantiateMatches sentence ss,
} by
  intro sentence ss n _
  let sub := fun n => (ss.headD []).lookup n
  let result := sentence.instantiate sub
  refine ⟨sub, sentence, result.isSome, result.getD sentence, ?_⟩
  cases ss with
  | nil =>
    simp [fren_spec, sub, result, Fren.Core.GroundMatching.instantiateMatches,
      TheorySentence.instantiate, theoryGroundImages]
    rfl
  | cons image rest =>
    cases h : theoryGroundImages sentence.variables (fun n => image.lookup n) <;>
      simp [fren_spec, sub, result, Fren.Core.GroundMatching.instantiateMatches,
        TheorySentence.instantiate, h, List.headD]

interp lang::ground_normalized_matches := fun ctx sentence apps calls =>
  Fren.Core.GroundMatching.matchNormalized ctx { sentence } { applications := apps, calls }
interp lang::ground_query_matches := fun ctx sentence apps calls =>
  Fren.Core.GroundMatching.matchApplications ctx { sentence } { applications := apps, calls }
interp lang::ground_instances := fun ctx sentence apps calls =>
  Fren.Core.GroundMatching.instances ctx { sentence } { applications := apps, calls }

impl ground_instances_step: lang::ground_instances_step for (ctx : Context) (sentence : TheorySentence)
    (apps calls : List TheoryTerm) {
  ctx := ctx, sentence := sentence, query_apps := apps, query_calls := calls,
  substitutions := Fren.Core.GroundMatching.matchApplications ctx { sentence } { applications := apps, calls },
  instances := Fren.Core.GroundMatching.instances ctx { sentence } { applications := apps, calls },
} by
  intro ctx sentence apps calls _
  simp [fren_spec, Fren.Core.GroundMatching.matchApplications,
    Fren.Core.GroundMatching.instances, List.flatMap_map]

end Fren.Impls.GroundMatching
