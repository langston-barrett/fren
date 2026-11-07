-- keep-sorted start
import FrenTest.FuzzFrontends.Corpus
import FrenTest.FuzzFrontends.Main
-- keep-sorted end

/-!
# Differential fuzzing of the front ends (`Reqs/dev/Testing`)

`lake exe fren_fuzz_frontends [--count N] [--seed N] [--out DIR] [--jobs 1|2]` generates
random specs and checks each with both front ends: `fren check`'s pipeline,
in-process, and the Lean front end, which elaborates the spec in an
environment that imports `Fren`, as the ui tests do. Their messages and
summaries must agree (`cli::agreement`); each spec where they differ is
written to `DIR` (default `.lake/fuzz`) with the difference and both
reports in comments.

Brute force is not needed, so the generator is wider than `fren_fuzz`'s,
and aims at the analyses that each front end implements on its own:
constants, defined outputs, defined and uninterpreted functions, the
former of every kind of result, as functions with `:=` and as function
blocks, with bodies that take their type from it (`bodyFns`), the
latter sometimes with contracts whose postconditions may contradict each
other, so that what applies them rests on their realizability, and
chains of contracts whose facts mention applications with facts of their
own (`factChain`), `match`
and tables over a scrutinee,
string methods with constant and non-constant arguments and `++`, products
of every kind of operand, orderings and `min` and `max` of an ordered
enumeration, an enumeration with payloads, whose outputs' variants a
clash note may give, sets and relations with `card`, so that it
reaches `linear_product`, the decidable core and the lints,
expressions that do not synthesize their types at each kind of site
(`sitesProc`), traits, with laws and expectations over their methods
(`traitGroup`), a recursive function applied on several paths of one
expectation (`guardPaths`), and global expectations over recursive
enumerations that induction on a parameter may prove (`inductions`).

What legitimately differs is normalized away by
`FrenTest.Frontends.compare`, whose documentation lists it, as does
`Reqs/dev/Testing`. Specs run in worker processes (`--worker`), so that a
solver that aborts, or a spec that runs too long (`--spec-timeout`), is
recorded against its spec and the run goes on.

`--avoid-known` keeps the generator clear of the differences already
known, to find others: it parenthesizes every method's receiver that is
not a name, and counts a spec whose every difference is of a kind that
`knownDifferences` lists for `--avoid-known`, or that `knownKinds` lists,
as known, not as a finding (`knownIssue?`). `lake test` checks a fixed
corpus of seeds against `knownDifferences` (`corpusFailures`), and that
what `genWide` appends adds no static error (`Wide.genWideCuts`); CI runs
fresh seeds on `main`, and fails only on a difference of a kind that is
not known, a crash or a timeout. Structural theories are compared on every run, with differences written to
`theories-seed*` as an early signal, separately from diagnostic failures.
`--report DIR` gives the results of the
runs in `DIR` as Markdown (`report`), for CI's job summary.
`--guards` generates guarded quantifiers alone
(`Wide.genGuards`), over every type that a guard may bound or not, with
their operands read through fields, so that many run fast; `genWide`
includes such a procedure now and then too. `--sites` generates
`Wide.sitesProc`s alone, the last of which may write an expression that
does not synthesize its type where it is not checked, an error that stops
the spec's other checks; `genWide` includes one without it now and then.
`--inductions` generates global expectations over recursive enumerations
alone (`Wide.inductions`), which induction on a parameter may prove, and
`--induction-forms` the forms in which the front ends read a candidate
for it (`Wide.inductionForms`); `--induction-candidates` generates declared
type, comparison and binder forms (`Wide.inductionCandidates`).
`--generic-functions` generates whole generic function instances
(`FuzzGenericFunctions.spec`), in an independent mode with defined,
uninterpreted, higher-order and recursive functions. Fresh runs reject
static errors from either front end, even when both give the same error.
`--datatype-elements` generates generic enumerations and records with
collection payloads and fields (`FuzzDatatypeElements.spec`).
`--generic-types` adds nested instances with multiple, reordered type
parameters and subset arguments (`FuzzDatatypeElements.genericTypes`).
Its fresh runs fail if a shared static error prevents a spec from reaching
its checks.
`--set-card-fallback` generates native-cardinality boundary and unlisted types.
`--set-card` reproduces #820's set seeds and adds finite cardinalities of
aggregate types and relation pairs (`Wide.genSetCard`). Its corpus and
fresh runs reject shared internal errors and undecided queries too.
`--confirm` generates what the confirmation of models evaluates
(`Wide.genConfirmed`): `div` and `mod`, an index in an argument that a
function's body never reads, the formulas whose value confirmation
knows where an index is out of range, and source questions in ignored
arguments. Main's original bodies and cuts from #940 remain exact prefixes;
the hosted additions follow them, with their own preserved draws: values
of an abstract type and of a type parameter, nested in containers,
tuples, fields and payloads,
quantified over directly and through definitions, given to higher-order
functions and generic structural recursions, and omitted from a model at
`let`s and calls; and it checks them with both front ends misreading models
(`Fren.Core.misreadSet`), so that what one knows and the other does not
is a message that differs.
`--confirm-matches` retains its hosted stream and appends complete
Boolean matches over guarded existential and universal quantifiers, with
empty and nonempty domains, nested quantifiers and unfolded helpers.
Their types include integers, naturals, Booleans, abstract types, type
parameters and containers; both front ends misread models in this mode too.
`--confirm-arguments` keeps the corrected Nat index annotation and its
regression seed in main's ignored-argument stream from #940.
`--confirm-counts` appends count comparisons whose conditions contain
quantifiers, inside connectives, conditionals and strict arguments. It
retains the hosted-sort stream and rejects static errors in its tail.
`--decidable` generates procedures in the decidable core of strings,
sets, relations and sequences (`Wide.genDecidable`), in its own random
stream so that every older mode's seeds are unchanged, then appends
implicit output invariants to check the rule for generated queries
(`Wide.outputInvariantCore`), and opt-outs inherited through helpers and
contracts (`Wide.inheritedCore`).
-/

/-!
The generators live in `FrenTest/FuzzFrontends/`, one mode or construct
family per module. `Wide` assembles the mixed generator, `Generate`
dispatches modes, and `Corpus` lists the fixed seeds. `Running` compares
the front ends; `Checks` checks corpus results, while `Worker`, `Main`
and `Report` run and summarize fresh seeds. This umbrella keeps the
previous imports and declaration names available to existing clients.
-/
