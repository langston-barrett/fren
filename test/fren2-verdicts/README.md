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
`empty.fren` has a total function, which creates definedness checks and verifies;
`no-checks.fren` has no obligations.

Boolean operands and unused let definitions retain static obligations. An
explicit false conditional guard makes its branch's site unreachable. These
expected verdicts express the static rule, even when dynamic evaluation would
skip the undefined operation. Unit-level producer and confirmation controls
remain in the Lean test modules.
