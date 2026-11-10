# Removing the legacy checker and FrenWalking

This is a plan, not a record of work done. It says what must move before the
`Resolved`-based checker and the `FrenWalking` library can be deleted, and in
what order.

## What is legacy

Two pipelines type the same source today.

The separated pipeline works on the shared expression representation. The
resolver's result is read into the HIR module, `FrenHirToThir.Pass.typeModule`
types it into the THIR module, and `FrenThirDesugar.desugar` removes its
parentheses. Each pass takes the previous module as its whole input.

The legacy pipeline works on `FrenModule.Resolved` and `FrenModule.Typed`,
which keep the syntax tree and tables indexed by source position. It consists
of:

- the legacy checker in `FrenHirToThir`: `Check`, `Walk`, `Typing` and
  `Signature`, with the validators `Coverage` and `Nonrecursive`;
- the `FrenWalking` library: `Check` and `Walking`, which re-run the resolver
  to admit a `Resolved` value, and `Program`, the admitted walking program
  with `fromResolved` and `fromSource`;
- `FrenModule.Typed`, and the parts of `FrenModule.Resolved` that only the
  legacy checker reads.

Everything after type checking still consumes `FrenWalking.Program`: the
evaluator, MIR construction, and through MIR the LIR, OIR and SMT producers
and `FrenCli2`. The Thir, Walking, Mir, Lir, Oir and Smt chapter wrappers state
their contracts over it. The Walking chapter (`src/Spec/Compiler/Walking.md`
and its wrapper) holds the walking program's own contract and nothing else.

The walking program is also declared twice. `FrenWalking.Program` and
`FrenEval.Program` are separate structures with the same three fields: the
resolved input, the typed result and the acceptance evidence. The Walking
wrapper's `Evaluator` copies one into the other, and each library proves its
own retention, static and determinism theorems. Both go in the removal; until
then a change to one must be made to the other.

## What must exist first

1. Coverage and non-recursion over the THIR module. The validators read
   `Typed` occurrence tables today. Each becomes a pass or a check over
   `Thir`, with its error naming an item and an origin as `TypeError` does.
2. A static boundary for the separated pipeline: source to desugared THIR, or
   one list of errors. This replaces `fromSource`. It needs spans for
   messages, which origins give through each item's origin table.
3. MIR construction from the desugared module. `FrenThirToMir` reads guards,
   contexts and division sites from the syntax tree; over desugared THIR these
   come from the expression itself, where a local is an index and there is no
   parenthesis.
4. The evaluator over the desugared module, or over MIR. It is the oracle of
   several test suites, so it moves before the passes that are tested against
   it lose their walking input.

## Order of removal

Each step is one small change that builds and passes on its own.

1. Add the THIR validators and the separated static boundary. Check them
   against the Language chapters' rules and the existing accepted and rejected
   corpus, not against the legacy checker's output.
2. Move the evaluator, then MIR construction, to the desugared module. The
   passes after MIR take MIR and do not change, apart from how their tests and
   `FrenCli2` obtain it.
3. Restate over the modules what the Walking wrapper states over the walking
   program: `Guard`, `ScopedChild`, `ScopedAt`, `DomainSite` and `Members`,
   and the Thir wrapper's judgments, lose their `Resolved` and `Typed`
   parameters. They move to the chapters of the passes that read them, and
   the Walking chapter and its wrapper are deleted whole.
4. Delete `FrenWalking`, `FrenEval.Program`, the legacy checker files in `FrenHirToThir`,
   `FrenModule.Typed`, and what remains unused of `FrenModule.Resolved`.
   Remove `FrenWalking` and its exceptions from the `layering` allow-list, so
   that no pass may import the parser or the resolver except the resolver's
   own reader.
5. Remove the agreement tests between the two checkers in
   `FrenHirToThirTests`; they have nothing left to compare.

## What to keep

The rejected-source corpus, the admission theorems' statements (success
exactly when typing and both validators accept) and the division-site
controls remain requirements. They are restated over the modules in step 3,
not dropped with the code that states them today.
