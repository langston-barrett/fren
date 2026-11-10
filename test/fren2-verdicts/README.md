# Known Fren2 verdicts

Each `.fren` file starts with `-- verdict: NAME exit: N`. The `verdictCorpus`
child job discovers every file, runs `FrenCli2.checkFile` (the same pipeline as
`fren2_check`), and checks both the verdict and its exit class. It rejects an
empty corpus or malformed annotation. The child and parent default test
selections run it as its own job (`fren_test --job fren2 verdictCorpus`).

Files whose second comment names a seed come from the independent skeleton
review probes. The corpus includes integer arithmetic, lexical
bindings, nominal enums, calls, inconsistent assumptions, invalid input,
no checks, unresolved dependencies, and the div/mod definedness regressions:
sites in unused lets, uncalled and called functions, assumptions, call
arguments, `if` conditions, `match` arms and divisors that themselves divide.
The `consumed-*` files cover assumptions and goals that consume a division,
directly or through (nested) calls: they verify or are refuted by a
source-confirmed counterexample when strict evaluation at the model is
defined. Three more show the verdicts around a zero divisor reached only
under the model, a skipped `or` operand and a callee defined only for some
inputs; there a definedness row refutes in any case, and the corpus checks
only verdicts. That strict confirmation leaves such rows unconfirmed is pinned
by the unit controls in `src/FrenOirToSmtTests/Model.lean`.
`div-site-under-undefined-let.fren` has a site whose path crosses a let value
that is undefined at the model; the unit controls in
`src/FrenOirToSmtTests/Checker.lean` pin that this site's row stays unconfirmed
there while the row of the division inside the let value is confirmed.
`empty.fren` has a total function, which creates definedness checks and verifies;
`no-checks.fren` has no obligations.

Boolean operands and unused let definitions retain static obligations. An
explicit false conditional guard makes its branch's site unreachable. These
expected verdicts express the static rule, even when dynamic evaluation would
skip the undefined operation. Unit-level producer and confirmation controls
remain in the Lean test modules.
