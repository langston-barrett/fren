# Subset types

A subset type is a declared alias of a base type restricted by a nonempty,
ordered list of named invariants. It replaces the type syntax `T is P`;
`is` remains a pattern test in expressions. There is no inline subset type.
Ordinary aliases retain `type Name := Base`.

```
subset := ["pub"] "type" IDENT "=" IDENT ":" type "where" conjunct ("and" conjunct)*
conjunct := IDENT ":" expression
```

For example:

```
type Even = n: Int where invariant: n mod 2 = 0
type Byte = b: Int where low: b >= 0 and high: b <= 255
type Warning = s: Severity where invariant: s is Severity::Warning | Severity::Error
struct Octet(Byte)
```

The binder is in scope only in the invariants. Invariants are Boolean
expressions, including applications of earlier functions, constants,
pattern tests and quantifiers; they are not patterns. Free variables
other than the declaration's binder are errors. Constants and function
names are not free variables. Each conjunct needs an identifier label,
and two labels in one declaration may not coincide. A label denotes the
path `Type::label`; the binder and labels do not enter the surrounding
module's variable scope. A subset may restrict another subset: it keeps
its base's invariants followed by its own, without changing the base
representation. Cyclic and forward type references follow ordinary alias
resolution and are rejected. Empty lists and unlabelled conjuncts are
syntax errors. A lone label other than `invariant` is accepted; the
separate lint reports it, without changing the meaning.

## Conjunctions and interpretation

Named conjunctions use the prefix blocks and infix labelled expressions
specified in [Named Boolean blocks](BooleanBlocks.md). Conjunction clauses
split into independent named checks, with distributed guards and nested
member identities; disjunction and all-equivalence blocks remain one
check with per-member result and conflict explanations. Labels are
optional for general Boolean block members, but every subset invariant
requires its own label. An obligation identifies `Byte::high`, rather
than only `Byte`. Repeated predicate applications retain separate source
occurrences as that chapter specifies.

The following executable fragment interprets actual invariant expressions
on integers. General expressions use the existing meaning and definedness
rules; the conjunction, order, inheritance and obligation rules below do
not depend on the expression's particular operators.

```fren
pub mod lang

set_option fren.lint.undecidable "allow"

pub enum SubsetRule { Lower(Int), Upper(Int), Even, Equal(Int) }
pub struct SubsetClause { label: String, rule: SubsetRule }

pub fn subset_rule_holds?(rule: SubsetRule, x: Int) := match rule {
    SubsetRule::Lower(lo) => x >= lo,
    SubsetRule::Upper(hi) => x <= hi,
    SubsetRule::Even => x mod 2 = 0,
    SubsetRule::Equal(value) => x = value,
}

pub proc subset_membership(clauses: Seq<SubsetClause>, value: Int): (member?) {
    ensure conjunction: member? iff (forall (i: Int), when 0 <= i < clauses.len, subset_rule_holds?(clauses[i].rule, value))
    expect labelled_range: when clauses = [SubsetClause { label := "low", rule := SubsetRule::Lower(0) },
    SubsetClause { label := "high", rule := SubsetRule::Upper(255) }], member? iff 0 <= value <= 255
    expect even: when clauses = [SubsetClause { label := "invariant", rule := SubsetRule::Even }],
        member? iff value mod 2 = 0
}

pub proc subset_obligations(clauses: Seq<SubsetClause>, value: Int, label: String): (failed?) {
    ensure named: failed? iff (exists (i: Int), 0 <= i < clauses.len and clauses[i].label = label and not subset_rule_holds?(clauses[i].rule, value))
    expect upper_bound: when clauses = [SubsetClause { label := "high", rule := SubsetRule::Upper(255) }] and label = "high",
        failed? iff value > 255
    expect other_label: when not (exists (i: Int), 0 <= i < clauses.len and clauses[i].label = label), not failed?
}

pub proc subset_closed(binder: String, free_variables: Set<String>): (det accepted?) {
    ensure closure: accepted? iff free_variables subset {binder}
    expect own_binder: when free_variables = {binder}, accepted?
    expect constant_expression: when free_variables = {}, accepted?
}

pub proc subset_labels(clauses: Seq<SubsetClause>): (accepted?) {
    ensure nonempty: when clauses = [], not accepted?
    ensure distinct: when clauses != [], accepted? iff
        (forall (i: Int), forall (j: Int),
        when 0 <= i < clauses.len and 0 <= j < clauses.len and i != j, clauses[i].label != clauses[j].label)
    expect repeated: when clauses = [SubsetClause { label := "same", rule := SubsetRule::Lower(0) },
    SubsetClause { label := "same", rule := SubsetRule::Upper(3) }], not accepted?
}
```

## Static types, assumptions and obligations

A subset alias has its base type for static comparison, recursively through
collection element types and generic arguments. No expression receives a
restricted static type, and no subtyping test decides whether two
invariant lists entail each other. Every place accepted by `widening`
remains accepted; obligations establish membership separately. An `Int`
may therefore be supplied for an `Even`, and an `Even` may be used as an
`Int`; `Even` and `Byte` can be compared as integers. A newtype remains
distinct and its constructor checks its underlying subset's invariants.

Variables, parameters, existential outputs and uninterpreted applications
bring their declared invariants as assumptions. Fields and nonrecursive
payloads bring them for their contained values without a quantifier;
recursive payloads bring them at every depth read by the query. A set,
relation or sequence brings the invariants of every element, and the two
members of each relation pair are checked independently. Generic data
instances substitute their actual element types before these rules apply.

The existing `lang::obligation` placement rule remains authoritative with
its `Matches` cases read as satisfying the named invariants. Defined
outputs and let values, function bodies, constants, function arguments,
record construction/update fields, enum payloads, newtype construction
and newtype arithmetic each ask one obligation per invariant. A procedure
call asks its parameter invariants through its call-assumption checks,
without a duplicate value obligation at the binding. The value is checked
even when its source annotation names the same subset. Base invariants
are checked before derived invariants and keep their original names.

```fren
pub proc subset_inheritance(base: Seq<SubsetClause>, added: Seq<SubsetClause>, value: Int): (member?) {
    ensure inherited: member? iff (forall (i: Int), when 0 <= i < base.len, subset_rule_holds?(base[i].rule, value))
        and (forall (i: Int), when 0 <= i < added.len, subset_rule_holds?(added[i].rule, value))
    expect retains_base: when member?, forall (i: Int), when 0 <= i < base.len, subset_rule_holds?(base[i].rule, value)
    expect no_weakening: when not (forall (i: Int), when 0 <= i < base.len, subset_rule_holds?(base[i].rule, value)), not member?
}
```

## Declaration checks

Every subset declaration is checked even when unused. Inhabitation asks
whether there exists a value of the complete base type meeting all base
and new invariants. An empty subset is an error at its declaration; an
inconclusive query is reported as inconclusive and does not certify it.
There is no witness clause. Invariants are checked for definedness and
function preconditions for every base value, using the base's invariants
and only earlier conjuncts as hypotheses. A later conjunct cannot justify
an earlier index or precondition. The invariant's own truth is never a
hypothesis of its definedness check. A base with no values therefore
cannot make a derived declaration pass vacuously.

```fren
pub proc subset_inhabitation(lower: Int, upper: Int): (inhabited?) {
    ensure interval: inhabited? iff (exists (value: Int), lower <= value <= upper)
    expect nonempty_interval: inhabited? iff lower <= upper
}

pub proc subset_earlier(clauses: Seq<SubsetClause>, position: Int, value: Int): (hypotheses?) {
    assume position_exists: 0 <= position < clauses.len
    ensure earlier_only: hypotheses? iff (forall (i: Int), when 0 <= i < position, subset_rule_holds?(clauses[i].rule, value))
    expect first_unconditional: when position = 0, hypotheses?
}
```

The declaration checks are ordinary checks: they obey the explicitly
selected evidence setting. Their invariant identity is stable across both
front ends. The reserved codes are `F0660` for an empty subset, `F0372` for duplicate
invariant labels, `F0373` for an invariant outside its binder's scope,
`F0661` for a failed named invariant obligation and `F0662` for a subset
declaration's failed definedness or precondition check. An inconclusive
inhabitation check uses the ordinary inconclusive-check result, with the
subset declaration identified. The obsolete pattern-type errors
`F0369` and `F0370` are retired. An expression pattern binder remains valid
where ordinary `is` permits it.

The anonymous pattern-obligation diagnostics `F0622` and `F0623` are
retired too. Each constraint introduced by a declared subset has a named
invariant, including constraints checked at a call argument; failures use
`F0661` and identify that invariant. An internal legacy obligation lacking
a name still uses `F0661`, identifying its declared type, rather than
reintroducing a retired code. This does not add implicit narrowing from
`Int` to `Nat`: such a statically mismatched value remains a type error.

## Decidability, Lean and migration

A subset constraint at the top of a type or in a record field or
nonrecursive payload is in the core exactly when each invariant is in the
core. In collection elements and recursive payloads it quantifies, so
`undecidable` reports that placement in addition to any noncore invariant.
Finite-base subsets remain finite and enumerate by filtering the base's
values. Recognized bounded integer pattern-test invariants retain their
finite integer domain, order and size; arbitrary integer predicates do
not falsely become finite. `Nat` remains built in with its existing rules.
Hosted Lean keeps the base representation with invariant hypotheses, so
static types, generated functions and implementation proofs agree with
the CLI.

The one-off migration script creates named aliases for inline pattern
types, including parameters, results, fields, payloads and element types.
An existing `type Byte := Int is P` becomes
`type Byte = value: Int where invariant: value is P`. Generated aliases
are fresh in their containing module, deterministic across repeated runs,
and precede their first use. Expression `is` tests and their binders are
unchanged. The script handles Fren blocks in Markdown and hosted Lean,
preserves comments and keeps a before/after verdict comparison report for
every migrated spec. No compatibility parser or automatic migration stays
in the executable. `manual_pattern_type` becomes a suggestion to declare
and reuse a subset type, without introducing a new inline spelling.

## Named-conjunct diagnostic semantics

A labelled predicate denotes the same Boolean tree with the labels erased.
`NamedBool` models literals, conjunction, negation and labels explicitly;
other expression operators are evaluated by the ordinary expression
semantics before contributing their Boolean value. A report asks the tree
for the truth it needs: an `ensure` or `expect` needs `true`, and a
negated application needs its operand to be `false`. If a positive
conjunction fails, each false named conjunct is reported. If a negated
conjunction fails, all of its true named conjuncts are reported: jointly
they prevented the negated conjunction from holding. A passing enclosing
expression reports no failed labels. Nested unlabelled conjunctions are
part of their containing label's expression and retain that label.

```fren
pub enum NamedBool { Literal(Bool), Conjunction(NamedBool, NamedBool), Negation(NamedBool), Label(String, NamedBool) }

pub fn named_truth?(NamedBool)
pub fn named_failed(NamedBool, Bool): Set<String>

pub proc named_node(e: NamedBool, wanted?): (det truth?, failed: Set<String>) {
    out truth? := match e {
        NamedBool::Literal(value?) => value?,
        NamedBool::Conjunction(lhs, rhs) => named_truth?(lhs) and named_truth?(rhs),
        NamedBool::Negation(inner) => not named_truth?(inner),
        NamedBool::Label(_, inner) => named_truth?(inner),
    }
    out failed := match e {
        NamedBool::Literal(_) => {},
        NamedBool::Conjunction(lhs, rhs) =>
            if wanted? then named_failed(lhs, true) union named_failed(rhs, true)
            else if truth? then named_failed(lhs, false) union named_failed(rhs, false) else {},
        NamedBool::Negation(inner) => named_failed(inner, not wanted?),
        NamedBool::Label(label, inner) => if named_truth?(inner) = wanted? then {} else {label},
    }
}

pub proc named_conjunction(a?, b?, wanted?): (failed: Set<String>) {
    out failed := if wanted? then (if a? then {} else {"a"}) union (if b? then {} else {"b"})
        else if a? and b? then {"a", "b"} else {}
    expect positive_a: when wanted?, "a" in failed iff not a?
    expect positive_b: when wanted?, "b" in failed iff not b?
    expect negative_both: when not wanted?, failed = if a? and b? then {"a", "b"} else {}
}

pub proc named_identity(first_definition: String, first_occurrence: Nat, first_label: String,
    second_definition: String, second_occurrence: Nat, second_label: String): (det same?) {
    ensure identity: same? iff first_definition = second_definition and first_occurrence = second_occurrence
        and first_label = second_label
    expect repeated_application: when first_occurrence != second_occurrence, not same?
    expect different_predicates: when first_definition != second_definition, not same?
}
```

Inhabitation is universal in the interpretation of earlier uninterpreted
functions: every interpretation admitted by their existing contracts must
have a witness. The declaration adds no axiom restricting those functions.
For example, `fn chosen?(Int)` followed by
`type Chosen = x: Int where invariant: chosen?(x)` fails inhabitation,
because the interpretation making `chosen?` constantly false is admitted.
A contract ensuring some chosen value can instead establish nonemptiness.
The diagnostic shows an interpretation with no witness, rather than a
witness from another interpretation that happens to satisfy the predicate.

A type obligation is checked from the value's base type and the
hypotheses already established at its site. It excludes the target
invariants and excludes the definition being checked as an assumption of
its own membership. Thus `type Positive = x: Int where invariant: x > 0`
followed by `proc bad(): (result: Positive) { out result := 0 }` fails the
`Positive::invariant` obligation. Similarly `struct PositiveBox(Positive)`
rejects `PositiveBox(0)`; `Seq<Positive>` rejects a defined value `[1, 0]`
at the second element. A declared input of `Positive` does supply `x > 0`
when proving an independently declared result of that type.

Earlier-conjunct guards are directional. For a sequence binder `q`,
`where present: q.len > 0 and first: q[0] > 0` is well formed, while
`where first: q[0] > 0 and present: q.len > 0` fails the definedness check
for `first`, even though their conjunction has the same classical truth.
The forward order never assumes `first` to justify its own index.

## Fixed interpretations and inhabitation queries

A subset with only fixed interpreted types and operations can check
inhabitation by satisfiability of the base type facts and every invariant
at a fresh value. This is an optimization of the same existential question;
it does not replace the universal interpretation requirement. It applies
only when the complete base type facts, inherited invariants and new
invariants contain no abstract sorts or uninterpreted functions, including
transitive dependencies through defined functions. Include every base fact
in the satisfiability query. Finding a witness in one interpretation never
justifies this optimization when an interpretation can vary.

```fren
pub enum InhabitationWorld { First, Second }
pub enum InhabitationValue { Zero, One }

pub proc fixed_inhabitation(allowed: Set<InhabitationWorld>,
    membership: Rel<InhabitationWorld, InhabitationValue>): (det satisfiable?, det inhabited_everywhere?) {
    assume some_world: allowed != {}
    assume fixed_meaning: forall (w: InhabitationWorld), forall (other: InhabitationWorld),
        forall (value: InhabitationValue), when w in allowed and other in allowed,
        (w, value) in membership iff (other, value) in membership
    out satisfiable? := exists (w: InhabitationWorld), exists (value: InhabitationValue),
        w in allowed and (w, value) in membership
    out inhabited_everywhere? := forall (w: InhabitationWorld), when w in allowed,
        exists (value: InhabitationValue), (w, value) in membership
    expect same_question: satisfiable? iff inhabited_everywhere?
}

pub proc varying_inhabitation(membership: Rel<InhabitationWorld, InhabitationValue>): (det some_witness?, det inhabited_everywhere?) {
    assume interpretation: membership = {(InhabitationWorld::First, InhabitationValue::Zero)}
    out some_witness? := exists (w: InhabitationWorld), exists (value: InhabitationValue), (w, value) in membership
    out inhabited_everywhere? := forall (w: InhabitationWorld), exists (value: InhabitationValue), (w, value) in membership
    expect one_world_insufficient: some_witness? and not inhabited_everywhere?
}
```
