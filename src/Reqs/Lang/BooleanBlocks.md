# Named Boolean blocks

Prefix `and { ... }`, `or { ... }`, `iff { ... }` and `one { ... }` expressions contain
comma-separated members and permit a trailing comma. Members may start
with `label:`; an unlabelled member is identified by its position, starting
at 1. The existing infix named conjunction spelling remains accepted.
Labels are annotations of an expression's Boolean meaning, and their
source spans and original texts are kept for diagnostics. Subset
invariants remain the exception: their labels are required by the subset
declaration grammar.

```
block := ("and" | "or" | "iff" | "one") "{" [member ("," member)* [","]] "}"
member := [IDENT ":"] expression
```

The block keyword distinguishes these from set and record literals. `one`
is contextual: it starts a block only when followed by `{`; existing
identifiers, labels and function names `one` remain valid elsewhere.
Members are ordinary Boolean expressions and may be guarded or contain
nested blocks. A named infix conjunction has the same meaning as the
corresponding `and` block. A block label need not be `invariant` outside
subset declarations. Duplicate explicit labels among siblings are errors;
the same label in different nested parents is permitted.

## Truth

`and` means every member holds, `or` means some member holds, and `iff`
means all members have the same truth value. In particular a three-member
`iff` is not a binary left-associated `iff` chain. An empty `and` and an
empty `iff` are true; an empty `or` is false. Singleton `and`, `or` and
`iff` reduce respectively to the member, the member and true.

```fren
pub mod lang

set_option fren.lint.undecidable "allow"

pub enum BoolBlockKind { Conjunction, Disjunction, Equivalence, ExactlyOne }
pub enum BoolBlockLabel { Named(String), Index(Nat) }
pub struct BoolBlockMember { label: BoolBlockLabel, value? }

pub proc boolean_block(block_kind: BoolBlockKind, members: Seq<BoolBlockMember>): (holds?) {
    ensure conjunction: when block_kind = BoolBlockKind::Conjunction,
        holds? iff (forall (i: Int), when 0 <= i < members.len, members[i].value?)
    ensure disjunction: when block_kind = BoolBlockKind::Disjunction,
        holds? iff (exists (i: Int), 0 <= i < members.len and members[i].value?)
    ensure equivalence: when block_kind = BoolBlockKind::Equivalence,
        holds? iff (forall (i: Int), forall (j: Int), when 0 <= i < members.len and 0 <= j < members.len,
        members[i].value? iff members[j].value?)
    ensure exactly_one: when block_kind = BoolBlockKind::ExactlyOne,
        holds? iff (exists (i: Int), 0 <= i < members.len and members[i].value? and
        (forall (j: Int), when 0 <= j < members.len and j != i, not members[j].value?))
    expect empty: when members = [], holds? iff block_kind is BoolBlockKind::Conjunction | BoolBlockKind::Equivalence
}

pub proc equivalence_three(first?, second?, third?): (equivalent?) {
    ensure all_same: equivalent? iff ((first? iff second?) and (first? iff third?))
    expect no_parity: when not first? and not second? and third?, not equivalent?
    expect all_false: when not first? and not second? and not third?, equivalent?
}

pub proc equivalence_branches(members: Seq<BoolBlockMember>): (all_hold?, none_hold?, equivalent?) {
    ensure all: all_hold? iff (forall (i: Int), when 0 <= i < members.len, members[i].value?)
    ensure none: none_hold? iff (forall (i: Int), when 0 <= i < members.len, not members[i].value?)
    ensure exactly_two: equivalent? iff all_hold? or none_hold?
    expect empty_both: when members = [], all_hold? and none_hold? and equivalent?
    expect mixed_fails: when not all_hold? and not none_hold?, not equivalent?
}
```

`one` means exactly one member holds. Three true members make it false;
it is not odd parity. The empty block is false and a singleton has its
member's truth. It uses the same optional labels, sibling uniqueness,
source identities and 1-based index paths as other Boolean blocks.

## Evaluation order

These evaluation rules apply to unsplit Boolean expressions. A root
conjunction clause is instead lowered to independent leaf clauses below;
a preceding sibling's truth does not guard a leaf's own checks.
Members are evaluated from left to right. `and` stops at its first false
member and `or` at its first true member. An `iff` with fewer than two
members evaluates none: it is true without reading a member. Otherwise
it evaluates the first member and each later member until the first
value differs from the first. After such a mismatch, later members are
not evaluated. Thus `iff { q[0] > 0 }` needs no definedness check for the
index, and `iff { false, true, q[0] > 0 }` never reads it either. Ordinary
binary `iff` evaluates both operands. `one` evaluates left to right until
the second true member, then returns false without evaluating later
members. If fewer than two are true it evaluates every member, including
a singleton. A member's preconditions and
definedness are obligations only under the guard that reaches it.
Diagnostic inspection never evaluates a skipped member solely to fill a
truth table: it reports that member as not evaluated.

```fren
pub proc block_evaluation(block_kind: BoolBlockKind, values: Seq<Bool>, position: Int): (evaluated?) {
    ensure in_range: when not (0 <= position < values.len), not evaluated?
    ensure conjunction: when 0 <= position < values.len and block_kind = BoolBlockKind::Conjunction,
        evaluated? iff not (exists (j: Int), 0 <= j < position and not values[j])
    ensure disjunction: when 0 <= position < values.len and block_kind = BoolBlockKind::Disjunction,
        evaluated? iff not (exists (j: Int), 0 <= j < position and values[j])
    ensure equivalence: when 0 <= position < values.len and block_kind = BoolBlockKind::Equivalence,
        evaluated? iff values.len > 1 and
        (position = 0 or (forall (j: Int), when 1 <= j < position, values[j] = values[0]))
    ensure exactly_one: when 0 <= position < values.len and block_kind = BoolBlockKind::ExactlyOne,
        evaluated? iff not (exists (i: Int), exists (j: Int),
        0 <= i < j < position and values[i] and values[j])
    expect singleton_iff: when values = [false] and block_kind = BoolBlockKind::Equivalence, not evaluated?
    expect mismatch_stops: when values = [false, true, true] and position = 2 and block_kind = BoolBlockKind::Equivalence,
        not evaluated?
}
```

## Splitting conjunction clauses

An `and` block used as an assumption, guarantee or expectation is sugar
for separate clauses: each member gets its own name, vacuity, redundancy,
realizability role, and source span. This includes a nonrecursive defined
predicate's labelled conjunction after unfolding it at an application.
The original enclosing clause is a grouping name, not an additional
assertion or check. Members of `or`, `iff` and `one` blocks stay within one
clause and one check, and their labels annotate diagnostics.

A leading `when` or `unless` distributes across an `and` block, including
nested guarded conjunctions. Thus `when c, and { a: p, b: q }` lowers to
`a: when c, p` and `b: when c, q`. A member containing another guarded
`and` is split recursively; every leaf receives all ancestor guards,
with `unless c` contributing `not c`. A conjunction under negation or a
disjunction is an ordinary Boolean subexpression, not independent clauses.
No distributed leaf may assume its own truth when its definedness,
vacuity, expectation or membership is checked.

Top-level unlabelled `assume`, `ensure` and `expect` clauses remain
otherwise unchanged: omitting a clause label is accepted only when the
expression, after leading guards, is one of these explicit blocks. Such
a root block's labelled children become sibling clause names; unnamed
children use their 1-based positions. Nested names append `.label` or
`.index` to their parent. Under an explicitly named clause `output`, the
second child is `p::output.2`. An unlabelled top-level block's first child
is `p::1`. Each name corresponds to one source member, never an invented
span covering unrelated members.

```fren
pub proc distributed_guard(ancestor_guards: Seq<Bool>, member?, inactive: Int): (guarded?) {
    ensure implication: guarded? iff (when (forall (i: Int), when 0 <= i < ancestor_guards.len, ancestor_guards[i]), member?)
    expect no_guards: when ancestor_guards = [], guarded? iff member?
    expect inactive_parent: when 0 <= inactive < ancestor_guards.len and not ancestor_guards[inactive], guarded?
    expect nested: when ancestor_guards = [true, true], guarded? iff member?
}

pub enum ClauseAncestor { Conjunct(BoolBlockLabel), When(Bool), Unless(Bool), Disjunct(BoolBlockLabel), Equivalent(BoolBlockLabel), ExactlyOne(BoolBlockLabel), Negated }

pub fn clause_splits?(step: ClauseAncestor) := step is ClauseAncestor::Conjunct(_) | ClauseAncestor::When(_) | ClauseAncestor::Unless(_)

pub fn clause_guard?(step: ClauseAncestor) := match step {
    ClauseAncestor::When(guard?) => guard?,
    ClauseAncestor::Unless(guard?) => not guard?,
    _ => true,
}

pub proc clause_leaf_path(path: Seq<ClauseAncestor>, member?): (split?, active?, guarded?) {
    ensure independent: split? iff (forall (i: Int), when 0 <= i < path.len, clause_splits?(path[i]))
    ensure all_guards: active? iff (forall (i: Int), when 0 <= i < path.len, clause_guard?(path[i]))
    ensure leaf_meaning: guarded? iff (when active?, member?)
    expect nested_named_indexed: when path = [ClauseAncestor::When(true),
    ClauseAncestor::Conjunct(BoolBlockLabel::Named("outer")), ClauseAncestor::Unless(false),
    ClauseAncestor::Conjunct(BoolBlockLabel::Index(2))], split? and active? and (guarded? iff member?)
    expect negation_keeps_one_clause: when path = [ClauseAncestor::Negated], not split?
    expect disjunction_keeps_one_clause: when path = [ClauseAncestor::Disjunct(BoolBlockLabel::Index(1))], not split?
}

pub proc clause_partition(block_kind: BoolBlockKind, members: Seq<BoolBlockMember>): (checks: Nat) {
    ensure counts: checks = if block_kind = BoolBlockKind::Conjunction then members.len else 1
    expect and_is_not_extra: when block_kind = BoolBlockKind::Conjunction and members.len = 2, checks = 2
    expect or_one: when block_kind = BoolBlockKind::Disjunction, checks = 1
    expect iff_one: when block_kind = BoolBlockKind::Equivalence, checks = 1
    expect exactly_one_check: when block_kind = BoolBlockKind::ExactlyOne, checks = 1
}
```

The shared identity of a labelled predicate member consists of its
function definition, its labelled/indexed path and its application
occurrence within the enclosing clause. Occurrences are numbered from 1
in source preorder, separately for each predicate in that clause; nested
calls retain their parent occurrence path. Diagnostics show the function
path plus `@1`, `@2`, etc. at a repeated application, followed by the
member path. They show original member text and span as well. Changing a
predicate's arguments does not merge occurrences. Labels are not bound
variables and cannot capture names in the arguments.

## Results and witnesses

A failed conjunction reports its independently failing clauses. A failed
positive `or` reports every member's false value. A failed negative `or`
reports the evaluated members that held, rather than claiming all failed.
A cover or vacuity witness for an `or` reports the members that hold in
that witness. A failed positive `iff` divides evaluated members into true
and false groups; both groups are nonempty. A failed negative `iff` has
only a true group or only a false group: all members agreed. It does
not report a three-member parity result. A failed positive `one` reports either no true evaluated members (all
members evaluated false), or the two true members that caused failure,
with any later members marked not evaluated. A failed negative `one`
reports the single true member and all other evaluated false members.
A cover or vacuity witness for positive `one` identifies the unique true
member; a negative witness identifies zero or at least two truths using
only evaluated members. A passing enclosing expression
has no failed-member diagnostics, even if some subexpressions are false.
Negating a predicate preserves its labels while reversing the truth
needed from the application. Source spans and occurrence identities are
the same in both front ends.

```fren
pub proc block_values(members: Seq<BoolBlockMember>, position: Int): (det present?, det in_true?, det in_false?) {
    out present? := 0 <= position < members.len
    out in_true? := 0 <= position < members.len and members[position].value?
    out in_false? := present? and not in_true?
    expect partition: when present?, in_true? iff not in_false?
    expect no_extra: when not present?, not in_true? and not in_false?
}
```

The enclosing wanted truth is part of the result. For example,
`expect e: not iff { false, false }` fails with both members in the false
group; `expect e: not or { true, false }` fails with its first member in
the true group and its second not evaluated. A result partition records
evaluation status separately from logical truth and never invents a value
for an undefined skipped expression.

```fren
pub proc block_result(actual?, wanted?, member_value?, evaluated?): (det failed?, det true_group?, det false_group?) {
    out failed? := actual? != wanted?
    out true_group? := failed? and evaluated? and member_value?
    out false_group? := failed? and evaluated? and not member_value?
    expect negative_false_group: when not actual? and wanted? and evaluated? and not member_value?, false_group?
    expect negative_iff: when actual? and not wanted? and evaluated? and not member_value?, false_group?
    expect negative_or: when actual? and not wanted? and evaluated? and member_value?, true_group?
    expect skipped: when not evaluated?, not true_group? and not false_group?
    expect passing_empty: when actual? = wanted?, not true_group? and not false_group?
}
```

```fren
pub proc exactly_one_result(values: Seq<Bool>, wanted?): (det actual?, det failed?, det no_true?, det multiple?) {
    out actual? := exists (i: Int), 0 <= i < values.len and values[i] and
        (forall (j: Int), when 0 <= j < values.len and j != i, not values[j])
    out failed? := actual? != wanted?
    out no_true? := not (exists (i: Int), 0 <= i < values.len and values[i])
    out multiple? := exists (i: Int), exists (j: Int), 0 <= i < j < values.len and values[i] and values[j]
    expect failure_partition: when wanted? and failed?, no_true? iff not multiple?
    expect negative_witness: when not wanted? and failed?, actual? and not no_true? and not multiple?
    expect empty_false: when values = [], not actual? and no_true?
    expect singleton: when values = [true], actual?
    expect three_not_parity: when values = [true, true, true], not actual? and multiple?
}

pub proc exactly_one_reach(values: Seq<Bool>, position: Int): (det reached?) {
    out reached? := 0 <= position < values.len and not (exists (i: Int), exists (j: Int),
        0 <= i < j < position and values[i] and values[j])
    expect second_truth_read: when values = [true, false, true, true] and position = 2, reached?
    expect after_second_skipped: when values.len >= 2 and values[0] and values[1] and position >= 2, not reached?
    expect singleton_read: when values = [true] and position = 0, reached?
    expect no_truth_reads_all: when values = [false, false, false] and 0 <= position < 3, reached?
}

pub proc exactly_one_branch(values: Seq<Bool>, chosen: Int): (det branch?) {
    out branch? := 0 <= chosen < values.len and values[chosen] and
        (forall (j: Int), when 0 <= j < values.len and j != chosen, not values[j])
    expect unique_chosen: when branch?, forall (j: Int), when 0 <= j < values.len, values[j] iff j = chosen
    expect empty_no_branch: when values = [], not branch?
    expect positive_singleton: when values = [true] and chosen = 0, branch?
}
```

## Branch conflict explanations

Only a disjunction that occurs in the minimized conflict core triggers
branch explanation queries. For each branch of `or`, run the existing
whole-value and variant forcing queries under that branch, in its
original guard and interpretation. Compare the forced values with those
of the rest of the core, and name the other guarantees that rule out the
branch. This applies to realizability and to vacuity of an assumption,
with the corresponding hypotheses. An unlabelled branch is named by its
1-based index. Branches not in the core incur no additional queries.

A `one` block with n members has exactly n explanation branches: branch
i requires member i true and every other member false, under the same
leading guards and interpretation as the owner. An empty block has zero
branches and is false. Each branch uses the existing whole-value and
variant forcing family, and names any member whose required polarity is
forced oppositely by the rest of its conditional core. Conditional
member minimization retains the branch assumption and owning block;
branches outside the minimized owner core incur no queries.

An `iff` has exactly two explanation branches, regardless of member count:
all members hold and none holds. In the first branch, query each member
positively; in the second, negatively. Name a member and the other core
clauses that force the opposite polarity. Ordinary binary `iff` receives
the same two-branch treatment. A failed equivalence check still uses the
true/false partition, not a conflict-branch explanation.

The following finite model states forcing using actual satisfying
assignments of two Boolean outputs. Empty sets of behaviours never count
as forcing a value: a contradictory branch cannot prove every output
value by vacuity. A branch's conditional core can name a single member,
but a whole disjunction is inconsistent only if every alternative is
ruled out. Removing a disjunction's other alternatives is not itself a
proof of global inconsistency.

```fren
pub mod check

use lang::BoolBlockKind

pub enum BranchBehaviour { OffOff, OffOn, OnOff, OnOn }
pub fn branch_first?(b: BranchBehaviour) := b is BranchBehaviour::OnOff | BranchBehaviour::OnOn

pub proc branch_forcing(branch: Set<BranchBehaviour>, rest: Set<BranchBehaviour>, forced?): (
    branch_forces?, rest_forces_opposite?, excluded?) {
    ensure branch_value: branch_forces? iff branch != {} and
        (forall (b: BranchBehaviour), when b in branch, branch_first?(b) iff forced?)
    ensure rest_value: rest_forces_opposite? iff rest != {} and
        (forall (b: BranchBehaviour), when b in rest, branch_first?(b) iff not forced?)
    ensure exclusion: excluded? iff branch inter rest = {}
    expect clash_excludes: when branch_forces? and rest_forces_opposite?, excluded?
    expect impossible_not_forcing: when branch = {}, not branch_forces?
}

pub proc disjunction_core(first: Set<BranchBehaviour>, second: Set<BranchBehaviour>, rest: Set<BranchBehaviour>): (inconsistent?) {
    ensure union_meaning: inconsistent? iff (first union second) inter rest = {}
    expect every_branch: inconsistent? iff first inter rest = {} and second inter rest = {}
    expect one_branch_insufficient: when first inter rest = {} and second inter rest != {}, not inconsistent?
}

pub proc branch_query_count(block_kind: BoolBlockKind, members: Nat, in_core?): (branches: Nat) {
    ensure alternatives: branches = if not in_core? or block_kind = BoolBlockKind::Conjunction then 0
        else if block_kind = BoolBlockKind::Equivalence then 2 else members
    expect unrelated_free: when not in_core?, branches = 0
    expect one_per_member: when in_core? and block_kind = BoolBlockKind::ExactlyOne, branches = members
    expect iff_two: when in_core? and block_kind = BoolBlockKind::Equivalence, branches = 2
}

pub proc branch_query_families(block_kind: BoolBlockKind, members: Nat, in_core?,
    per_branch: Nat, family_counts: Seq<Int>): (accounted?) {
    call count := branch_query_count(block_kind, members, in_core?)
    ensure families: accounted? iff family_counts.len = count.branches and
        (forall (i: Int), when 0 <= i < family_counts.len, family_counts[i] = per_branch)
    expect no_hidden_queries: when not in_core?, accounted? iff family_counts = []
    expect equivalence_budget: when in_core? and block_kind = BoolBlockKind::Equivalence and accounted?,
        family_counts.len = 2 and family_counts[0] = per_branch and family_counts[1] = per_branch
}
```

Member-level minimization produces conditional cores and source identities
for the members needed to refute each branch. Every retained member is
necessary within that branch's minimized core; deletion is rechecked.
The displayed explanation retains the owning disjunction and branch
assumption so a conditional core cannot be mistaken for an unconditional
one. Query cost is one existing pin/variant query family per disjunct
under consideration, or two families for equivalence, or one family per member for `one`, with the
per-member polarity questions inside those equivalence families. It
never scans unrelated disjunctions merely to enrich a diagnostic.
