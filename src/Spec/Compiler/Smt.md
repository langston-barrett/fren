# Walking SMT queries

This boundary translates the actual walking OIR questions to SMT-LIB and
asks the existing pinned cvc5 solver in a separate, bounded process per
question. It produces evidence about those questions, with their original
attribution and dependencies. It does not report verified source programs.

## Supported input and translation

The entry point accepts the actual walking source witness and runs
`FrenLirToOir.produce`. Successful scope checking, an edited question array or
a supplied success Boolean is not an alternative admission path. Invalid
source and upstream generation failures remain errors.

Bool and mathematical Int translate to their complete SMT sorts. Each nominal
payload-free enum translates to its own datatype with exactly its canonical
constructors. Parameters remain in written order, with nearest-first local
slots for interpretation. Their local domain components are true because
parameters denote total values, not because a block assumption asserted it.

Every retained nonrecursive function has both its actual value definition and
its actual domain definition. Emit definitions in dependency order, including
unused ones. Calls apply those definitions to their ordered arguments. No
arbitrary axiom may assert that a function is always defined. A dependency
cycle, missing symbol, exhausted translation budget or unsupported construct
must produce an explicit nonanswer, never a weakened formula.

Symbols use separate indexed families for nominal sorts, constructors,
function value/domain components, parameters and local value/domain binders.
Indices come from canonical identities, not readable name concatenation or
hashes. Source identifiers are never inserted as SMT syntax. This prevents
keyword collisions and injection and distinguishes nominal constructors with
the same spelling. Local value and domain lets evaluate their bindings in
the incoming context and extend only the body; shadowing must not capture a
parameter, an argument, a guard or another local.

Translate Boolean operators, equality, integer arithmetic and comparisons
with their actual meanings. Integer division and remainder use Euclidean
semantics, including negative divisors. A zero divisor still has its separate
OIR domain question; the solver's totalized out-of-domain value establishes
nothing about source definedness. Ordinary Boolean operands and unused lets
keep all their static OIR questions even if a concrete evaluator skips them.

The query is precisely the original `Question.search`: assumptions for Sat;
assumptions conjoined with the negated condition inside its original lexical
frames for every refutation. Definitions and enum declarations provide the
interpretation, not extra unproved goals as premises. Preserve every question
ID, owner, origin, request, ordered parameter, dependency and readiness field,
including unsupported or unresolved entries.

## Bounded answers

Use the pinned local cvc5 asset, with explicit per-query solver resource/time
limits and an outer wall deadline. Bound script input and combined stdout and
stderr. Retain command arguments, process exit, both output streams (including
exact captured bytes), elapsed time and timeout/output-limit reasons. Reap
the owned process after completion, failure and normal cancellation. Observe
exit without reaping (`waitid` with `WNOWAIT`), keep the direct leader waitable
through the last process-group signal, and only then reap it. Its unreaped
PID anchors the numeric group against reuse, including on normal completion;
never signal a remembered PID/PGID after releasing that anchor. Unexpected
loss of this ownership is an error and forbids the group signal.
A missing executable, nonzero exit, malformed/multiple answer, solver error
or protocol failure is an error, not Unsat. Unknown remains unknown; reaching
an outer resource bound remains resource exhaustion. Translation unsupported
is distinct from either. Do not discard a question because another failed.

Sat on an assumption search is solver evidence for a possible witness. Sat on
a refutation is evidence for a possible counterexample. Unsat records an
unsatisfiable search or absence of a counterexample, respectively. These raw
answers require independently justified domains/dependencies and later source
model confirmation before reporting source results. This unit does not
extract source assignments or add an aggregate source-success decision.

Mutually partial assumption dependencies remain exactly as OIR records them:
unresolved, even if their search is Unsat. No solver result invents a rule for
simultaneous discharge, treats an undefined assumption as false, or lets a
goal prove itself. Unknown/error/resource/unsupported evidence and all raw
output remain visible alongside unresolved readiness.

## Independent primitive facts

These small current Fren facts constrain arithmetic and polarity independently
of the actual translator. They do not implement a second compiler model.

**Dynamic semantics**

r[smt.primitive.euclidean] smt_primitives::facts::{negative_dividend, negative_divisor, remainder, reconstruction}
The signed division and remainder examples use Euclidean integer semantics.

r[smt.primitive.refutation] smt_primitives::facts::refutation
A counterexample requires true assumptions and a false condition.

```fren
pub mod smt_primitives

pub proc facts(assumption?, condition?, n: Int) {
    expect negative_dividend: when n = -9, n div 2 = -5
    expect negative_divisor: when n = -9, n div (-2) = 5
    expect remainder: when n = -9, n mod (-2) = 1
    expect reconstruction: (n div (-2)) * (-2) + (n mod (-2)) = n
    expect refutation: (not (when assumption?, condition?)) iff (assumption? and not condition?)
}

#fren_check
```

Changing the expected negative-divisor quotient to 4 or replacing
`not condition?` with `condition?` must fail the primitive checker. Tests of
the actual producer also use independently expected signed arithmetic and
query polarities; agreement with a copy of the translator is insufficient.

## Evidence and pending laws

`FrenOirToSmt.retains_oir`, `retains_questions` and `admission` prove that
successful production retains the actual admitted OIR and every original
question. `deterministic`, `distinct_components`, `parameter_domain`,
`classify_nonzero` and `classify_resource` state small actual-code laws.
Native `smt`, `smtControls` and `smtProperties` jobs exercise source-to-query
to-real-solver behavior and nonanswers. The fixed fixture independently checks
32 written requests, signed arithmetic, unused/guarded domains, forward calls,
shadowing, nominal enums and unresolved mutual assumptions. Owned controls
exercise invalid protocols, nonzero exits, exact invalid bytes, time/output
limits, suspended children and repeated cancellation at cleanup. The ownership
regression checks that the direct leader is still waitable at every group
signal, including normal solver exit and repeated cancellation. These tests
and raw receipts are finite evidence, not proofs of universal translation
correctness or SMT soundness, or a new crossover prerequisite.

The following universal obligations remain pending:

- Prove translation preserves each actual typed logical term in related
  complete environments, including nominal identity, Euclidean arithmetic,
  function equations and interleaved lexical frames.
- Prove query correspondence in both directions with the declarative source
  obligations after independently justified applicable domains. OIR's general
  extraction/source correspondence remains pending too.
- Prove injectivity and freshness of every rendered symbol family and
  substitution/capture preservation over all admitted source programs.
- Establish the unresolved mutually partial assumption rule before claiming
  supported source results for that class.
- Bind later model decoding and static source confirmation to actual code;
  raw SAT/UNSAT, bounded tests and solver trust do not close this obligation.
