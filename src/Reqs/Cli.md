# The `fren` command

```
fren check [--timeout SECONDS] [--resource-limit N] [--examples N] [--jobs N] [--dump=resolved|theories|obligations|smt] [--timings] [--tests N]
    [--seed N] [--evidence METHOD] [--query-cache DIR] [--verify-query-cache DIR] [-A|-W|-D|-F LINT]... FILE...
fren trace [--tests GLOB]... [--require LEVEL] [-A|-W|-D|-F LINT]... FILE...
fren fmt [--check] [--ignore GLOB]... FILE...
fren fix [--check] [--fmt] [--only LINT]... [--skip LINT]... [--ignore GLOB]... [-A|-W|-D|-F LINT]... FILE...
fren eval --proc PATH [--set VAR=VALUE]... [--seed N] [-A|-W|-D|-F LINT]... FILE...
fren quickcheck [--tests N] [--seed N] [--jobs N] [-A|-W|-D|-F LINT]... FILE...
fren mutate [--by solver|testing|both] [--proc PATH] [--mutant ID]... [--diff PATCH] [--sample N] [--seed N]
    [--shard K/N] [--list] [--timeout SECONDS] [--resource-limit N] [--examples N] [--tests N]
    [-A|-W|-D|-F LINT]... FILE...
fren --explain CODE
fren --help
fren --version
```

Every form also takes `--color WHEN` (or `--color=WHEN`), anywhere among
its arguments; see [Colour](#colour).

`fren check` checks the spec in the given files, without Lean. `fren trace`
reports the [evidence](Trace.md) for every procedure of the spec, and scans
the tests for `fren-covers:` markers that no claim names; it does not run
the checks. `fren fmt` [formats](Fmt.md) the files, and `fren fix`
[fixes](Lint.md#fixing-lints) the lints that it can. `fren eval`
evaluates a procedure on one behaviour, and `fren quickcheck` tests the
spec on random behaviours, both without the solver (see [Evaluation and
testing](Eval.md)). `fren mutate` checks small changes to the spec, and
reports those that no check rejects (see [Mutation
testing](Mutate.md)). `fren --explain CODE` explains an [error
code](View.md#error-codes), such as `F0105`. `fren --help`
(or `-h`) prints a usage summary, and `fren --version` (or `-V`) prints the
version. `fren` is a self-contained executable: it needs no Lean
installation. It is built by `lake build fren`.

| Option | Meaning |
|---|---|
| `--timeout SECONDS` | `check` and `mutate`: time limit for each solver query (default 10; 0 means none); see [Limits](#limits) |
| `--resource-limit N` | `check` and `mutate`: limit on the solver's work for each query, in cvc5's resource units (default 0, which means none); see [Limits](#limits) |
| `--examples N` | `check` and `mutate`: the most notes of [forced outputs](#forced-outputs) to show for each unrealizable procedure, a whole number or `all` (default 1) |
| `--jobs N` | `check` and `quickcheck`: how many procedures to check or test at once (default: the number of cores); see [Parallel checking](#parallel-checking) |
| `--dump=resolved` | `check`: write the resolved, typed surface to standard output; see [Resolved surface](#resolved-surface) |
| `--dump=theories` | `check`: write the theory structure to standard output; see [Theories](#theories) |
| `--dump=obligations` | `check`: write what each check asks to standard output; see [Obligations](#obligations) |
| `--dump=smt`, `--dump-smt` | `check`: write each solver query to standard output; see [Solver queries](#solver-queries) |
| `--timings` | `check`: report how long each procedure's checks took; see [Timings](#timings) |
| `--evidence METHOD` | `check`: check every check that `set_option fren.evidence` could set by `METHOD`, in place of the spec's own settings; see [Evidence](#evidence) |
| `--query-cache DIR` | `check`: keep the solver's answers in `DIR`, and answer the queries asked before from it; see [Query cache](#query-cache) |
| `--verify-query-cache DIR` | `check`: fail if the solver's answer contradicts one kept in `DIR`; see [Query cache](#query-cache) |
| `--tests GLOB` | `trace`: scan the matching files for markers; may be repeated |
| `--require LEVEL` | `trace`: warn about, and fail on, procedures with weaker evidence than `trusted`, `tested`, `solver` or `proved` |
| `--check` | `fmt` and `fix`: change no file, and print a diff of what would change |
| `--ignore GLOB` | `fmt`: skip the matching files; `fix`: leave them as they are; may be repeated |
| `--fmt` | `fix`: then format the files, as `fren fmt` does |
| `--only LINT`, `--skip LINT` | `fix`: fix only the lints given, or all but them; may be repeated |
| `-A LINT`, `-W LINT`, `-D LINT`, `-F LINT` | `check`, `trace`, `fix`, `eval`, `quickcheck` and `mutate`: set the level of a [lint](Lint.md), or of each lint of a [group](Lint.md#groups), to `allow`, `warn`, `deny` or `forbid`; may be repeated. The long forms are `--allow`, `--warn`, `--deny` and `--forbid` |
| `--proc PATH` | `eval`: the procedure to evaluate; `mutate`: the procedure whose mutants to check |
| `--set VAR=VALUE` | `eval`: the value of a variable; may be repeated |
| `--seed N` | `eval`, `quickcheck`, `mutate`, and `check` for [checks by testing](Check.md#checking-by-testing): where the random search starts (default 0); `mutate`: also which mutants `--sample` takes |
| `--tests N` | `quickcheck` and `mutate`: tests per procedure and global expectation; `check`: tests per procedure or global expectation with [checks by testing](Check.md#checking-by-testing) (default 100) |
| `--by WHAT` | `mutate`: check mutants with the `solver` (the default), by `testing`, or `both` |
| `--mutant ID` | `mutate`: check the mutant `ID`; may be repeated |
| `--diff PATCH` | `mutate`: check the mutants of the items that the unified diff `PATCH` touches, or the one on standard input if `PATCH` is `-`; see [Patches](Mutate.md#patches) |
| `--sample N` | `mutate`: check `N` of the mutants |
| `--shard K/N` | `mutate`: check the `K`th of `N` parts of the mutants, counted from 0; see [Samples and shards](Mutate.md#samples-and-shards) |
| `--list` | `mutate`: list the mutants, and check none |
| `--color WHEN` | colour the output: `auto` (the default), `always` or `never` |

## Completed syntax migrations

`fren fix` accepts the same language as `fren check`. Completed migration
syntax has no separate parsing or elaboration path: global behaviour
binders and top-level `refine` declarations receive ordinary language
errors. Value quantifiers in short expectations, parameter blocks and
`refines` members remain part of the language. No file is written when
its input has a static error, even if other files have fixable lints.
Lint selection, Markdown preservation and formatting retain their normal
meaning.

The retired implementation inventory is the global/refinement rewrite
module, retained declaration source and members, top-level refinement
AST/parser/elaborators (including the unreachable hosted elaborator),
legacy refinement evaluation/mutation branches, dedicated migration
fixtures and promises in the manual. Historical error numbers remain
reserved, without syntax examples that promise their emission. Ordinary
lint fixes are outside this retirement.

The transaction domain is the complete input text of all files, represented
as a sequence of strings. A rejected input preserves that sequence exactly;
there is no partial write of another file's proposed lint edits.

```fren
mod cli

pub proc fix_static_errors(
    original: Seq<String>,
    proposed: Seq<String>,
    static_errors: Set<String>,
): (det written: Seq<String>) {
    out written := if static_errors = {} then proposed else original
    expect rejected_input: when static_errors != {}, written = original
    expect accepted_input: when static_errors = {}, written = proposed
    expect preserves_file_count: when static_errors != {}, written.len = original.len
}
```

## Input files

- A file whose name ends in `.md` is a [Markdown spec](Markdown.md). Any
  other file is read as Fren source, conventionally with the extension
  `.fren`.
- A file may start with `import` and `open` lines, which are skipped, so a
  Lean file that contains only a spec can be checked too. `#fren_check` is
  accepted and ignored. `set_option` is accepted only to set the level of a
  [lint](Lint.md#setting-levels). Any other Lean code, including [Lean-only
  items](Lang/Items.md#lean-only-items) and other options, is an error.
- The files are processed in the order given, with one shared set of modules
  (see [Modules and visibility](Lang/Modules.md#across-files)). Then every
  procedure and [global expectation](Lang/Global.md) is checked, or for
  `fren trace`, the evidence for every procedure is reported. Unlike in
  Lean, this includes those that no `#fren_check` follows.

## Output

Diagnostics, the summary of the checks, and the [timings](#timings) of
`fren check --timings` go to standard error. Standard
output holds only what was asked for: the evidence report of `fren trace`,
the evaluated behaviour of `fren eval`, the kill rates and the list of
mutants of `fren mutate`, the diffs of `fren fmt --check` and `fren fix --check`, the [solver queries](#solver-queries) of `fren check --dump-smt` and the
[obligations](#obligations) of `fren check --dump=obligations`, the
[resolved surface](#resolved-surface) of `fren check --dump=resolved`, the
[theory structure](#theories) of `fren check --dump=theories`, and the
text of `--explain`, `--help` and `--version`.

Each [diagnostic](View.md) is printed with a header
with the severity and [error code](View.md#error-codes), the position as
`file:line:col` (both counted from 1), the source line with the offending
part underlined, notes and help, and suggested edits:

```text
error[F0105]: `==` is not an operator in Fren
 --> spec.fren:2:47
  |
2 | proc c(x: Int): (y?) { ensure r: y? iff x == 1 }
  |                                               ^^ not a Fren operator
  |
help: use `=` to test for equality
  |
2 - proc c(x: Int): (y?) { ensure r: y? iff x == 1 }
2 + proc c(x: Int): (y?) { ensure r: y? iff x = 1 }
  |
```

Information, such as a guarantee of an unrealizable procedure that
forces an output to a value that the rest of its conflict rules out, is
printed as a `note`. After the diagnostics come the summary
of the checks, or, if there were static errors, that they stopped them, and then a
pointer to `fren --explain` for the codes reported.

```fren
pub mod cli

use check::{Kind, Verdict}
use view::Severity
use view::Severity::{Error, Info, Silent, Warning}
```

## Resolved surface

With `--dump=resolved`, `fren check` writes the resolved, typed surface to
standard output, before checking it. The dump retains generic declarations,
module boundaries, calls and surface expressions, before generics and modules
are expanded into verification formulas. Imported item names and enum variants
have their resolved paths; declared types and value expressions have their
types, including inferred types. Type parameters remain parameters, aliases
retain their surface declarations, and newtypes retain their nominal types.
The prelude's declarations, generated instances and hidden checks are omitted.
Subset predicates' generated names are omitted too; their written binders
and invariant expressions retain their annotations.
A shorthand subset's unwritten binder does not turn its base type into a
local reference or value expression.

The dump represents the surface as each file's source text together with
annotations over it. Each `(file "path" ...)` contains `(surface "text")`
and annotations `(KIND START STOP "VALUE")`. `START` and `STOP` are half-open,
zero-based character offsets into that surface, after a Markdown file's prose
is blanked. `name` spans an item reference and gives its resolved path.
`local` spans a local name and any fields read from it, giving that dotted
path in its surface scope. At a declared name, `type` gives its declared type,
or a function's result type; at a written type, it gives the resolved type.
`expr` spans a value expression and gives its type. `arguments` spans a function
application and gives its inferred type arguments, without expanding its
generic definition. Paths and types from the prelude are qualified with
`prelude::` to distinguish them from a user's
items of the same name. Strings use JSON escaping. These annotations describe
the source sites, rather than the formulas or symbols that instantiation and
lowering generate.

Files appear in command-line order, and annotations in increasing order of
their start, then decreasing order of their stop, then by kind. Repeated
elaboration of a site leaves one annotation per kind, with the last value;
an enclosing expression records its type after its parts. The same input in
one build produces the same dump, including with different `--jobs` settings.
There is no parser or format stability promise.

Static errors suppress the dump. Otherwise checking, diagnostics and exit
status are as without the flag, including when a check fails. The flag is
accepted only by `check`, can be repeated, and can be combined with the other
dump flags: the resolved surface precedes their output. Diagnostics and the
summary stay on standard error. The Lean-hosted front end has no resolved
dump option.

## Theories

With `--dump=theories`, `fren check` writes the elaborated theory structure
before checking. A module is a named theory with its signature and sentences;
a trait is an interface theory with `Self` as a parameter and its laws as
axioms. Generic functions and datatypes have theories whose signature
parameters are their type parameters. Functions and procedures have named
theories too, so that calls and generic applications can refer to them.
Their entries also appear in their owning module. Prelude declarations and
hidden checking helpers are omitted.

Signatures identify abstract and defined items and give their types, including
constructors and selectors of datatypes. Sentence headers identify clauses,
their roles and typed variables. Function clause variables have positional
names `arg0`, `arg1`, and so on; procedure variables keep their source names.
Higher-order function parameters are abstract function parameters named
`argument_0`, `argument_1`, and so on, by their position in the signature.
A `require` or an output definition has domain role; an `ensure` is a theorem
of a defined function and an axiom of an abstract function or procedure;
an `expect` is a goal. Cover goals are queries, rather than theory sentences.
Formula bodies, domains, claims and call bindings are
opaque. Named predicates keep their written clause header, without the
checking leaves that elaboration expands from their bodies. Datatype freeness
belongs to its signature, without synthetic axioms.

`cli::theory_clause_role` states the role of each header, independently of
the outcome of checking:

```fren
pub proc theory_clause_role(defined?, keyword: String): (
    det is_domain?,
    det is_theorem?,
    det is_axiom?,
    det is_goal?,
) {
    ensure domain_rule: is_domain? iff keyword is "require" | "define"
    ensure theorem_rule: is_theorem? iff keyword = "ensure" and defined?
    ensure goal_rule: is_goal? iff keyword = "expect"
    ensure axiom_rule: is_axiom? iff not is_domain? and not is_theorem? and not is_goal?

    expect one_role: one {
        domain: is_domain?,
        theorem: is_theorem?,
        axiom: is_axiom?,
        goal: is_goal?,
    }
}
```

The diagram records import inclusions, procedure calls and generic
instantiations, with their type and item maps and instantiated signatures.
A symbolic instance belongs to its caller's scope; a concrete instance belongs
to the generic declaration's module. Repeated applications share one instance
and list their sites. Genuine Lean interpretations and implementations are
opaque named references. The Lean front end logs the same view at
`#fren_check` with `set_option fren.dump "theories"`; the comma separated
value `"theories,obligations"` requests both views.

The dump is delimited by `; theories` and `; end of theories`. Names and types
are JSON strings, with `<root>` naming the root module and `prelude::`
qualifying references into the prelude. Entries, sentences,
links and sites are sorted, independent of map iteration order and job count.
The format is for debugging and front-end comparison: nothing reads it back,
and its spelling may change. A static error suppresses the whole dump.
Diagnostics and exit status remain those of ordinary checking. Repeated
flags print one copy; when combined, the resolved surface precedes theories,
which precede obligations and SMT queries.

## Solver queries

With `--dump-smt`, or `--dump=smt`, `fren check` writes each query it gives the solver to
standard output, as an [SMT-LIB](https://smt-lib.org/) script, before the
query runs. Each script starts with a comment naming its procedure and
numbering the query within it, names each hypothesis in a comment after
its `assert`, and ends with `(check-sat)` and `(reset)`, so the whole
stream can be given to a solver such as cvc5:

```text
fren check --dump-smt spec.fren > queries.smt2
cvc5 queries.smt2
```

The scripts declare variables as quoted symbols, such as `|y|`, and
abstract types as sorts and functions as uninterpreted functions, named by
their paths after `::`, such as `|::lang::Name|`, which no variable can be
named. A variable whose name is also a symbol of one of cvc5's
theories, such as `abs`, `div`, `exp` or an instance's `str.len`, gets a
`#` after its name, `|abs#|`, since `|abs|` is the theory's symbol; no
Fren name contains `#`. A second
copy of a variable, as used by the [determinism](Check.md#determinism)
check, is `|y#'|`. A script declares every variable of its
procedure, but of the spec's abstract types, enumerations, records and
functions only those that its query or model observations mention,
directly or through another declaration: the others cannot change its
answer, and declaring them all is most of the work of a small query. A
[newtype](Lang/Items.md#newtypes) is erased: it is declared as its
underlying type, `Ms(e)` is written as
`e`, `x.0` as `x`, and its operators as its underlying type's. A `Nat` is declared as an `Int`, and what
[natural numbers](Lang/Procedures.md#natural-numbers) bring is asserted
before the query's hypotheses, followed by the comment `; nat`.

`fren check` asks the solver each distinct script once: some checks of a
procedure ask the same query, such as the assumptions' consistency, and a
script asked again gets the answer that it got first, model and all. The
one exception is a script whose first answer was `sat` without a model,
because no model was wanted: asked again for a model, it is asked of the
solver again, and that answer is kept in place of the first, whatever it
is, since under a time limit it can be `unknown`. The
script is the whole query, with its logic, options and limits, so the
same script is the same question. `--dump-smt` still writes each query,
asked again or not. Two procedures that ask the same script at once, in
[parallel](#parallel-checking), may both ask the solver; a fresh solver
gives the same script the same answer, model and all, unless it reaches a
[limit](#limits). [`fren mutate`](Mutate.md) shares the answers between
the spec and all its mutants.

Each query gets a solver of its own, which is freed once the query is
answered, so that the memory of `fren check` grows little with the number
of its queries: what is kept is the answers, and the commands that the
solver parsed from each script, which a fault of the cvc5 bindings keeps
from being freed (`FrenCli.Cvc5`), about 5 kB a query.

Each script sets the [SMT-LIB logic](https://smt-lib.org/logics.shtml) of
its query, so that the solver rejects a query outside the fragment that
Fren's rules keep it in, rather than running an incomplete procedure:
linear integer arithmetic, uninterpreted functions and datatypes (for
enumerations and records). A `match` arm reads the payload with the
datatype's selectors, and tests its scrutinee by comparing it with the
variant built from them. A string literal is written as SMT-LIB writes
it: `""` for `"`, and `\u{h}` for `\` and for every character outside
printable ASCII. A comparison of a string with a literal, such as
`name < "b"`, is written as a match of a pattern of the strings below
the literal, which matches `""`, a string whose first character is
smaller, or one with the same first character whose rest is below the
rest of the literal: cvc5 decides such a match, but often not `str.<`
between a literal and a string of unbounded length. `name <= "b"` also
matches `"b"` itself, and a literal on the left is the negation:
`"b" < name` is `not (name <= "b")`, and `"b" <= name` is
`not (name < "b")`. `>` and `>=` are these with their sides swapped. Other
comparisons use `str.<` and `str.<=`. A defined function that returns a
literal is a literal to the Lean-hosted front end, which unfolds it, but
not to `fren check`, so the two can write such a comparison differently;
like any difference in how a query is written, it can only change
whether the solver answers in time. Only the
[realizability](Check.md#realizability) check quantifies, over outputs, which never occur in a function's arguments (see
[Calls](Lang/Calls.md#call-variables)), unless the spec has
an [unbounded quantifier](Lang/Quantifiers.md#unbounded-quantifiers),
which every query that reads it gives the solver as a quantifier: each
bound name of a type that is not listed is declared by the quantifier at
its type's sort, as `(forall ((|i#0| Int)) ...)`, where `#` and the
bound name's position among those in scope, from 0, keep it apart from
every variable and every other symbol (`cli::query_symbols`, below); a
`Nat` is an `Int` there, with `(>= |n#0| 0)` before
the body, as an implication for `forall` and a conjunct for `exists`, and
a subset type's constraint likewise. Its bound names of listed types are
expanded within it. So does a [refinement
claim](Lang/Refinement.md) whose abstraction has calls: the claim holds
for every value of the abstraction's call variables, which it gives the
solver as a `forall`. A spec with either quantifies, so its queries use a
quantified logic: `UFDTLIA` where they would be `QF_UFDTLIA`. A spec that uses
strings needs the theory of strings, which has no smaller standard logic,
so its queries use `ALL`, and set cvc5's options `strings-exp`, without
which cvc5 refuses some string operations, `re-inter-mode all`, so
that it decides intersections of [patterns](Lang/Expressions.md#patterns),
and `re-elim on`, so that it rewrites a match that needs no automaton,
such as one of `x[0-9]{2}.*`, as constraints on the string's prefixes,
substrings and length, which it decides faster. These rewrites keep the
query's meaning, and introduce no quantifiers.
A spec that uses sets uses `ALL` too, and sets `sets-exp`, without which
cvc5 refuses to count the members of a set of a finite type. A relation's
`domain` is its join with the set of every value of the second type, and
its `range` the same on the other side, written as a literal when that type
is finite. Over a type that is not finite, which is outside the core, they
are cvc5's projections, which it supports only in higher-order logic, so
a query of such a spec whose script has a projection, in its hypotheses,
its goal or the definitions that it includes, uses `HO_ALL`, and its other
queries use `ALL`: cvc5's higher-order extension slows every query that it
is set for. The Lean-hosted front end does the same, for each query with a
projection, by cvc5's option `force-logic`, since lean-smt always sets
`ALL`. A query with a quantifier over a
collection's elements, which a [subset type](Lang/SubsetTypes.md#static-types-assumptions-and-obligations)
within an element type brings, and which is outside the core, sets
`fmf-bound`, with which cvc5 finds models of quantifiers bounded by
membership, as each such quantifier is, rather than giving up; both front
ends set it for exactly those queries. So does a procedure, global
expectation or refinement whose queries have an unbounded quantifier with
a bound name that has a [domain](Lang/Quantifiers.md#guards): in its
own constraints, definitions and arguments, those of its calls'
procedures, and the bodies of the defined functions that they apply. Its queries are still in the
[decidable core](Lang/Decidability.md), unless it opts out. A spec uses
sets if it writes a `Set<…>` or `Rel<…>` type, or a set or relation
literal such as `{1, 2}`, and sequences if it writes a `Seq<…>` type, a
sequence literal such as `[x]`, a [table](Lang/Expressions.md#tables)
without a `_` row, whose value where no row holds is an index out of range
of the empty sequence, or a [`match`](Lang/Expressions.md#matches) whose
arms without guards are not exhaustive, likewise where no arm is taken,
even if no variable has such a type.
A query in a logic with quantifiers, any but `QF_UFDTLIA`, sets cvc5's
`inst-when` to `last-call`, so that cvc5 instantiates quantifiers only
once the rest of the query is satisfied, not also during its search of
the rest. That changes how cvc5 searches, not what a query means. By
default, cvc5 can go on instantiating a contract that quantifies within a
quantifier, such as `lang::resolve`'s, each instance bringing new terms
to instantiate it with, long before it finds a model.
`cli::logic` gives the logic and options from the check, where `QuantifierFree` is
`QF_UFDTLIA`, `Quantified` is `UFDTLIA` and `HigherOrder` is `HO_ALL`:

```fren
pub enum Logic { QuantifierFree, Quantified, All, HigherOrder }

pub enum Theory { Strings, Sets, Sequences }

pub proc logic(
    kind: Kind,
    theories: Set<Theory>,       -- beyond uninterpreted functions, datatypes and linear integer arithmetic
    projection?,                 -- the query's script takes the domain or range of a relation over a type that is not finite
    quantified?,                 -- the spec has an unbounded quantifier, or a refinement claim whose abstraction has calls
): (
    det logic: Logic,
    det strings_exp?,            -- set cvc5's `strings-exp`, `re-inter-mode` and `re-elim` options
    det sets_exp?,               -- set cvc5's `sets-exp` option
    det last_call?,              -- set cvc5's `inst-when` option to `last-call`
) {
    use check::Kind::Realizability
    use self::Logic::{All, HigherOrder, Quantified, QuantifierFree}
    use self::Theory::{Sequences, Sets, Strings}

    require relations_are_sets: when projection?, Sets in theories

    ensure base: when theories = {},
        logic = (if kind = Realizability or quantified? then Quantified else QuantifierFree)
    ensure all: when theories != {}, logic = (if projection? then HigherOrder else All)
    -- cvc5 decides sequences in its strings solver.
    ensure options: (strings_exp? iff (Strings in theories or Sequences in theories))
        and (sets_exp? iff (Sets in theories or Sequences in theories))
    -- cvc5 instantiates quantifiers only once the rest of the query is satisfied.
    ensure instantiation: last_call? iff logic != QuantifierFree

    expect quantifier_free_when_possible: when logic = QuantifierFree, kind != Realizability and not quantified?
    expect sets_alone: when theories = {Sets}, not strings_exp?
    expect higher_order_rarely: when logic = HigherOrder, projection?
    expect realizability_last_call: when kind = Realizability, last_call?
}
```

`projection?` is read from each query's script, with the definitions that it
includes, by `Fren.Core.projectsRelation`. `fren check` first
takes the logic of the spec as a whole, with `projection?` true if the spec
projects such a relation anywhere, and lowers it by the script with
`Fren.Core.queryLogic`. That this gives `logic` with the query's own
`projection?`, for every kind, set of theories and `quantified?`, is
proved (`Fren.Core.queryLogic_logic`, `Fren.Core.queryLogic_unprojected`).
That `queryScript` applies it to each script is backed by the ui tests,
not proved.

`quantified?` is computed before any query is written, from what the spec
says, so a source of quantifiers that it leaves out would have a query
with a quantifier asked in `QF_UFDTLIA`, which cvc5 rejects with an error
that looks like the solver giving up. So `fren check` also reads the
script of each query that it would ask, after any quantifier over
elements is expanded: the definitions that it includes, such as those of
the defined functions that it applies, its declarations, its hypotheses
and its goal. `cli::query_logic` states that a query whose script has a
`forall` or `exists` is never asked in the quantifier-free logic. Such a
query is an internal error, `Unknown` with the reason that it has a
quantifier, never a solver's answer. Every ui test that reaches one then
fails, rather than reporting a solver error. `quantifies?` is read from
the script by `Fren.Core.hasQuantifier`, and the `impl` of `query_logic`
binds the decision, `Fren.Core.queryAsked`; that `runQuery` asks it of
each script is backed by the ui tests, not proved:

```fren
pub proc query_logic(
    logic: Logic,                -- the logic that `cli::logic` gives the query's check
    quantifies?,                 -- the script it would ask, its definitions, declarations, hypotheses and goal, has a `forall` or `exists`
): (det asked?, det internal?) {
    use self::Logic::QuantifierFree

    ensure rule: asked? iff not (logic = QuantifierFree and quantifies?)
    ensure error: internal? iff not asked?
}
```

The Lean-hosted front end asks the same checks' queries, of the same
formulas and with comparisons with literals written as matches, through
lean-smt, but its scripts differ: lean-smt sets the logic `ALL`, and
declares what each query's formulas mention; the front end sets every
option above, whether or not the spec uses strings and sets, which
changes how cvc5 searches, not what a query means; and it answers a
query that a procedure asks again once, as `fren check` does. Otherwise
it poses each query as `fren check` does, so that cvc5 can decide the
same queries: it asserts the hypotheses in the same order, since cvc5's
answer may depend on it, and it sets back to cvc5's defaults the options
that lean-smt sets for its proofs, which Fren does not ask for, such as
turning off cvc5's simplification, which leaves some queries undecided,
except that it still asks for unsat cores, which lean-smt reads.

### Symbols

Each symbol of a query names one thing. A variable's is its name, as
above, with a `#` after it if a theory has that symbol. A quantifier's
bound name `x`, of a type that is not listed, is `|x#k|`, with `k` its
position among the bound names in scope; a variable's second copy is
`|x#'|`; and `fren check` names the parameter `x` of a closure
`|x#closure{n}|`, with `n` the closure's number in the spec. No Fren name
contains `#` ([identifiers](Lang/Lexical.md#identifiers)), so what follows
the first `#` tells these apart, and the name in front of it tells apart
those of one kind. `cli::query_symbols` states that two symbols are the
same only if they are of the same thing: in particular, a bound name's
symbol is distinct from every variable's, every other bound name's, and
every copy's and closure parameter's, so a quantifier never captures a
variable, nor a variable a bound name. `'` would not do as the separator,
since a name may contain it: a variable `i'0` had the symbol of a bound
name `i` at position 0, so that `forall (i: Int), i = i'0` held.

The other symbols are kept apart from these, and from variables, by a
character that no Fren name has, or are chosen fresh:

- a function's, type's, variant's or field's has `::` or `{`, as
  `|::f|`, `|E::V|` or `|R{}|`, but for the prelude's types, written as
  lean-smt writes them, which `query_symbols` leaves out;
- a goal constant's is the first `x#goal{k}` that the query does not have
  (`cli::goal_constant_name`);
- a bound name `x` of a listed type, which each instance replaces, is
  `|k x|`, with a space, at its position `k`;
- a `let`'s name is `let@{n}`, and a record update's value
  `|update@{n}|`, with an `@`, by a number of their own;
- what has no name starts with `#`: the parameters of a function given
  as a closure (`#{k}`, `#_{k}`, `#match{j}`), the element of a
  constraint over a collection (`#e{d}`, `#a{d}`, `#b{d}`), a
  refinement's internal variables (`#refines{i}.x`), and the values that a
  model observes (`#member_observation_…`);
- a bound name renamed apart where a definition is unfolded
  (`cli::substitution_scope`) is `|fren.subst.{n}|`, whose last
  component starts with a digit, which no name's does, and is chosen
  where the formula does not have it.

Besides a bound name's and a copy's, the Lean front end makes only names
that start with `#`, as `fren check` does: `#match{j}` and `#_{k}` for the
parameters of a function given as a closure. lean-smt names each local by
its name. Its locals
for a `let`'s names are `x@k`, and for a closure's parameters
`Fren.Core.boundSymbol` at their position, `x#k`, which the solver never
sees, and which no two binders along one path share.

Both front ends name bound names and copies by `Fren.Core.boundSymbol`
and `Fren.Core.primed`, and `fren check` closures' parameters by
`Fren.Core.closureSymbol`. `cli::query_symbols` states each symbol's
text, by `text`, and that two of them are the same only if they are of
the same thing. Its `impl` binds each symbol to `Fren.Core.QuerySymbol.text`,
which those functions make, so that each symbol's text is pinned down
exactly, and is proved; the checker proves `apart` from the symbols'
definitions and `rule`. Positions and numbers are
written in decimal, so the Req has them as their digits. That each front
end names each symbol by these functions is backed by the ui tests and the
front-end fuzzer, which declares variables named as bound names' symbols
were, not proved. That the determinism check is sound needs the same of
copies: `Fren.Core.checkDeterminism_pass_plain` discharges the copies'
distinctness from the variables and from each other for names without
`#` (`primed_inj_plain`, `primed_ne_plain`). Copies were `y'`, which a
variable could be named, and that premise of `checkDeterminism_pass` was
nowhere checked.

```fren
-- What a symbol of a query is the symbol of.
pub enum QuerySymbol {
    Name(String, Bool),        -- a variable, by its name, and whether a theory has that symbol
    Copy(String),              -- a variable's second copy, for determinism
    Bound(String, String),     -- a quantifier's bound name, and its position among those in scope, in decimal
    Closure(String, String),   -- a closure's parameter, and the closure's number, in decimal
}

-- The name that `s` is made from.
pub fn base(s: QuerySymbol): String := match s {
    QuerySymbol::Name(x, _) => x,
    QuerySymbol::Copy(x) => x,
    QuerySymbol::Bound(x, _) => x,
    QuerySymbol::Closure(x, _) => x,
}

-- The symbol, as the solver is given it.
set_option fren.lint.undecidable "allow" in
pub fn text(s: QuerySymbol): String := match s {
    QuerySymbol::Name(x, theory?) => if theory? then x ++ "#" else x,
    QuerySymbol::Copy(x) => x ++ "#'",
    QuerySymbol::Bound(x, k) => x ++ "#" ++ k,
    QuerySymbol::Closure(x, n) => x ++ "#closure" ++ n,
}

-- Its number, if it has one, is written in decimal.
pub fn decimal?(s: QuerySymbol) := match s {
    QuerySymbol::Bound(_, k) => k.matches?(r"[0-9]+"),
    QuerySymbol::Closure(_, n) => n.matches?(r"[0-9]+"),
    _ => true,
}

set_option fren.lint.undecidable "allow" in
pub proc query_symbols(a: QuerySymbol, b: QuerySymbol): (
    symbol_a: String,            -- `a`'s symbol
    symbol_b: String,            -- `b`'s symbol
    det same?,                   -- `a` and `b` have one symbol
) {
    -- Each is of a name, which never contains `#`, and has its number in decimal.
    require names: not base(a).contains?("#") and not base(b).contains?("#")
    require numbers: decimal?(a) and decimal?(b)

    out symbol_a := text(a)
    out symbol_b := text(b)
    ensure rule: same? iff symbol_a = symbol_b

    expect apart: same? iff a = b

    expect bound_apart: when a is QuerySymbol::Bound(_, _) and b != a, not same?
    expect not_primed: when a = QuerySymbol::Bound("i", "0") and b = QuerySymbol::Name("i'0", false), not same?
}
```

### Goal introduction

Before either front end gives a query to the solver, it introduces the
goal's leading binders. Each bound name of a universal quantifier in front
of the goal is replaced by a fresh constant, declared after the variables;
each premise of an implication in front becomes a hypothesis, asserted
after the others with the comment `; premise`; and a `let` in front has its
definitions substituted into the rest. Then the solver is asked to refute
the hypotheses with the negation of what is left. This keeps the query's
validity, as argued here and not checked: no Req states it, and no test
compares the answers to a query with and without its introduction: the hypotheses entail `forall (x: T), p(x)` exactly when they
entail `p(c)` for a constant `c` of `T` that occurs nowhere else, and
`when p, q` exactly when they and `p` entail `q`. A constant keeps its bound
name's symbol, such as `|x#0|`, unless the query already has that symbol
free, as a variable, a declaration, or an earlier constant, and is otherwise
`|x#0#goal0|`, with the first number that the query does not have
(`cli::goal_constant_name`).

Introducing them changes what cvc5 decides, though not what a query
means. With the constants, the negated goal is ground, and cvc5 can
instantiate a quantified hypothesis, such as a trait's law, with its
terms; under the quantifier, it can fail to find them, and give up on a
query that is unsatisfiable (#543). So both front ends introduce them, in
the one function `Fren.Core.introduceGoal`, and lean-smt, which would
otherwise introduce them itself, is told not to. Each front end reads only
the heads of its own goals: the Lean-hosted front end reads `∀ x, b` as a
premise if `x`'s type is a proposition, as lean-smt's own introduction
would, and as a bound name otherwise, and `fren check` reads
`(forall ((x S) ...) b)` as a bound name, `(=> p q ...)` as a premise and
`(let (...) b)` as a `let`.

`cli::head_introduction` states what becomes of each head when it is
introduced, and `cli::goal_introduction` which heads are: every one in
front of the goal, from the outermost, up to the first that is none of the
three, so that a head is introduced exactly when it and every head in front
of it can be. Their `impl`s bind `Fren.Core.GoalHead.introduced?` and
`Fren.Core.introduceGoal`, and are proved; that the front ends read each
head as it says is backed by the ui tests and the front-end fuzzer, not
proved:

```fren
pub enum GoalHead { Universal, Premise, Definition, Other }

pub enum Introduced { Constant, Hypothesis, Substituted }

-- What a head becomes when it is introduced, if it is.
pub fn introduced_as(h: GoalHead): Option<Introduced> := match h {
    GoalHead::Universal => Option::Some(Introduced::Constant),
    GoalHead::Premise => Option::Some(Introduced::Hypothesis),
    GoalHead::Definition => Option::Some(Introduced::Substituted),
    GoalHead::Other => Option::None,
}

pub proc head_introduction(head: GoalHead): (det introduced: Option<Introduced>) {
    ensure rule: introduced = introduced_as(head)
}

-- `heads[i]` is a head of `heads`, and it and every one in front of it can be introduced.
set_option fren.lint.undecidable "allow" in
pub fn introducible_through?(heads: Seq<GoalHead>, i: Int) := 0 <= i < heads.len
    and (forall (j: Int), when 0 <= j <= i, introduced_as(heads[j]) != Option::None)

pub proc goal_introduction(
    heads: Seq<GoalHead>,        -- the goal's heads, from the outermost; past its last, the rest is `Other`
    i: Int,                      -- a position among them
): (det introduced?) {           -- the head at `i` is introduced
    -- At most `Fren.Core.goalIntroductionLimit` heads; a goal with more, which no spec writes, keeps the rest.
    require within_limit: heads.len <= 1024

    ensure rule: introduced? iff introducible_through?(heads, i)
}
```

`cli::goal_constant_name` states the symbol of each constant, which
`fren check` chooses with `Fren.Core.goalConstantName`, from which
symbols the query has: those of its variables, the free symbols of its
hypotheses and goal, its declarations, and the earlier constants. No
bound name of a goal and no other symbol that `fren check` writes ends in
`#goal` and a number, so the candidates are new unless the query has them.
Its `impl` is proved, for a bound name `x`, over every set of candidates
that the query has; with `fren check`'s bound on how many candidates it
tries, one more than the symbols that the query has, one is always free:

```fren
set_option fren.lint.undecidable "allow" in
pub proc goal_constant_name(
    base_taken?,                 -- the query has the bound name's own symbol
    taken: Set<Int>,             -- the numbers `k`, at least 0, whose `base#goal{k}` the query has
    k: Nat,                      -- a number
): (
    det kept?,                   -- the constant is the bound name's own symbol
    det chosen?,                 -- the constant is `base#goal{k}`
) {
    ensure keeps: kept? iff not base_taken?
    ensure least: chosen? iff (base_taken? and not (k in taken) and (forall (j: Int), when 0 <= j < k, j in taken))
}
```

## Obligations

With `--dump=obligations`, `fren check` writes what each of its checks
asks to standard output, before the results: for each check, its
obligation, the context that its query may use, after instantiation and
desugaring, its goal, and its evidence. It is the level of an intermediate
verification language, such as Boogie's, Viper's or Why3's tasks, after
the instantiation of generic functions and types and the desugaring of
the spec into formulas, as the solver is given them. The Lean-hosted
front end prints a dump of the same form with `set_option fren.dump
"obligations"`, as a message at the `#fren_check`: each `#fren_check` logs a dump of only
the items that it reports, not of the procedures that it checks only for
the evidence that its items rest on. An unknown value is an error for
`fren check`, `--dump=obligation` being an unknown option, which stops it
before it checks anything; the Lean-hosted front end warns of an unknown
`fren.dump` at the `#fren_check`, and checks without a dump. The dump is
for debugging and for comparing the front ends: nothing reads it back, and its format may
change with any version.

```text
; obligations
(obligation
  ; at 6:12
  (item c)
  (check expectation e)
  (evidence solver)
  (signature
    (declare-const m Int)
    (declare-const n Int)
  )
  (context
    (= m (+ (* 2 n) 1))
    (> n 0)
  )
  (goal (> m 1))
)

; end of obligations
```

An obligation names its item, its check, as its kind, the constraint,
call or variable that it is about, and which of the check's questions it
is, such as `(assumptions)` for whether an item's assumptions can hold
together, and its evidence, as `set_option fren.evidence` writes it. Its
signature is its query's declarations of sorts, datatypes, constants and
functions, and its recursive definitions, its context is the sentences that the query assumes, and its goal is
what the query asks to follow from them; a question whether its context
can hold at all has the goal `false`. A comment gives where its
constraint, or its item, is written, as `line:column`: metadata, which
comparisons ignore.

Every check of the items that the run checks is there, whatever its
evidence, and every question that it asks first, such as the redundancy of
each constraint, though a run asks some only after an answer
(`Fren.Core.questionsOf`). A check set to random testing or enumeration
shows the question that the solver would be asked, with that evidence,
though the solver is not asked it. A question that the solver is asked is
shown as it is asked, with the checks set to testing or enumeration taken
out: without the assumptions of a call set to them, in the question of the
item's vacuity under its trait's laws. The dump leaves out:

- the realizability checks of a generic contract at the instances that a
  spec applies, which a run asks only where the check at its type
  parameters' sorts does not pass;
- the queries that a check asks after an answer, to explain or confirm it:
  minimal cores, the pins and clash notes of forced outputs, branch
  explanations, the confirmation of models, and a query asked again
  where confirmation contradicts its model (`Reqs/Models`);
- the expansion of quantifiers over a collection's elements, which a run
  asks of the query that the dump shows
  (`Reqs/Lang/ElementQuantifiers#expansion`).

Both front ends take each question from `Fren.Core.questionsOf`, give the
script of its query as they would give it to the solver, without asking
it, and print them with `Fren.Core.dump`, which makes every decision about
their canonical form:

- the logic, the options and the solver's commands of a script are left
  out; its non-recursive definitions are unfolded where they are used,
  since one front end gives the solver a function's definition and the
  other its body, and so are its sorts' definitions (`define-sort`); and a
  constant or function (`declare-const`, `declare-fun`) that nothing else
  mentions is left out, though its sorts and datatypes stay;
- its symbols for the spec's types, constructors, selectors and functions
  are their names in `fren check`'s queries, without `|`s
  (`Fren.Core.ItemSymbol`). The Lean-hosted front end maps lean-smt's
  names to them for the spec's enumerations, records, their constructors
  and selectors; it names the locals that stand for recursive functions
  and for abstract types and functions by their whole paths, as `fren
  check` names their symbols, so that two of one name in two modules stay
  apart, and apart from every variable, though a generic recursive
  function's instance gets its position among the query's, as `f<0>`; it
  erases a newtype's constructor and field,
  as `fren check` erases newtypes, and names the newtype by its
  underlying sort where that is `Int`, `Nat`, `Bool` or `String`
  (`Fren.dumpSymbols`). Lean's `«»` and `✝` go from a name, but where two
  names would then be one;
- what either front end could write in two ways is written one way
  (`Fren.Core.Sx.normalize`), such as a conjunction of conjunctions, a
  `let`, whose definitions are substituted, or `<=`; a conjunction in the
  context is as many sentences. A definition is unfolded and a `let`
  substituted without capture: a bound name that would capture a free
  name of what is substituted is renamed apart, as `x#s0`. The names
  bound are those of SMT-LIB's binding constructs, which one function
  lists (`Fren.Core.Sx.binder?`): `forall`, `exists` and `lambda`'s
  variables, a `let`'s names in its body, and a `match` case's pattern
  variables in its body; in declarations, a recursive definition's
  parameters and a parametric datatype's `par` sort parameters;
- the declarations and the sentences are each printed once, in order of
  their text (`cli::canonical_sentences`), so that neither their order
  nor a repeated one changes the dump;
- the obligations are in order of their items' paths, then in the order of
  their questions within each item; two items with one path, as a
  function's body and its contract, are in order of their questions, then
  of their text without its metadata, so that where they are written does
  not order them.

So for the same spec, two front ends that build the same queries print the
same dump, and a difference between their dumps, but for the metadata, is
a difference between their queries, found where it starts, before it
changes a verdict or a message, or between the names or simplifications
that the dump does not make canonical, such as the names that lean-smt's
embeddings give `Nat` and `Bool` variables (#493). `fren_fuzz_frontends
--obligations` compares them on every spec that a run generates, but not on the corpus
that `lake test` checks, and reports, without failing, those whose dumps
differ, and of those, the ones that differ other than in the names of
their constants. The Lean-hosted front end keeps elaborating Fren
into Lean terms and proving with them: its dump is printed from the
query that lean-smt is given, in which a Lean term that is not Fren's is a
symbol of its own.

The dump is printed from scripts that are never asked: it asks the solver
nothing, and changes no result of `fren check`. A script that a front end cannot build is
an `(error ...)` command among its obligation's declarations, as is a
query that lean-smt does not show, as where its preprocessing closes the
goal first (`(error "lean-smt showed no query")`), and an item
whose questions the Lean-hosted front end cannot build is one obligation
whose script is such a command. But in the Lean-hosted front end, the
dump's work counts towards the item's heartbeats, and a limit of Lean's that
building it reaches, heartbeats or recursion depth, is the item's failure
to check, as any other is.

`cli::canonical_sentences` states the order: a context's sentences, each
by the place of its text in the order of texts, as a front end gives them
and as the dump prints them, are printed in ascending order, each once,
and are exactly those that the front end gives. Its `impl` is proved of
`Fren.Core.sortedOnce`, which prints them, over every sequence of places,
but of its instance on `Int` with `Int`'s order, not of the instance that
the dump runs, on `String` with `Fren.Core.textLe`. That the two agree is
assumed: that `textLe`, `String`'s order, is total and transitive, and
that two texts are in the same place under it only if they are equal:

```fren
set_option fren.lint.undecidable "allow" in
pub proc canonical_sentences(
    given: Seq<Int>,             -- a context's sentences, as a front end gives them
    printed: Seq<Int>,           -- the sentences that the dump prints, in order
): (
    det ascending?,              -- each is before the next in order, so each is printed once
    det kept?,                   -- each sentence given is printed
    det only?,                   -- each sentence printed is given
) {
    ensure ascending: ascending? iff (forall (i: Int), when 0 <= i and i + 1 < printed.len, printed[i] < printed[i + 1])
    ensure kept: kept? iff (forall (i: Int), when 0 <= i < given.len, given[i] in printed)
    ensure only: only? iff (forall (i: Int), when 0 <= i < printed.len, printed[i] in given)
}
```

## Query cache

With `--query-cache DIR`, `fren check` keeps the solver's answers in the
directory `DIR`, creating it if need be, and answers a query that an
earlier run asked from it, without the solver. Each answer is a file of
its own, `DIR/HH/HHHHHHHHHHHHHHHH`, named by a hash of its key, which it
holds in full. The key, `cli::Key`, is everything that can change the
answer:

- the whole script, as `--dump-smt` writes it without its first comment
  and the `(check-sat)` and `(reset)` after it: its logic, options,
  [limits](#limits), declarations, hypotheses and goal; and the formulas
  whose values its model reads, each with the formula that guards it;
- the version of cvc5, as cvc5 reports it;
- the version of how `fren check` runs a script and stores its answer,
  bumped whenever an answer can change without the script changing, such
  as when it reads models differently.

An entry answers a query only if its key is the query's, in full, so a
hash that two keys share is a miss, never another script's answer.
`unknown` is never kept, whatever its reason: a time limit is reached or
not depending on the machine's load. Nor is an answer whose model, or
whose key's observations, have a name with a numeric component, which an
entry cannot hold; `fren check` never makes one. A `sat` answer keeps its
model, if one was wanted; one without a model does not answer a query
that wants one, which the solver then answers, and its answer replaces
the entry.
cvc5 gives a script the same answer, model and all, every time, unless it
reaches a limit (see [Solver queries](#solver-queries)), so an answer from
the cache is the answer that the solver would give, and the output is the
same with the cache as without it. Entries are written to a file of their
own and renamed into place, so several runs at once may share a
directory. Nothing is ever deleted from it: entries of an old script, an
old cvc5 or an old version are never hit again, and deleting the
directory clears them.

With `--verify-query-cache DIR`, `fren check` reads `DIR` only to compare:
each answer that the solver gives, whose key has an entry in `DIR`, must
agree with that entry. An answer contradicts an entry if one is `unsat`
and the other `sat`, or both have models and they differ. A contradiction
is an internal error, which names the entry, printed with no position,
since it is about the cache rather than a file. It means that the key
leaves out something that changed the answer, or that cvc5 is not
deterministic, so the cache would be wrong. After the summary,
`fren check` writes a line, starting `fren: compared N answers`, of how
many answers it compared, so that comparing nothing cannot pass for
agreeing; a `DIR` that is not a directory is an error, and the checks do
not run. A run with both options, an empty directory for `--query-cache`
and a full one for `--verify-query-cache`, asks every query of the
solver, checks the old answers, and leaves in the new directory exactly
the answers of this run.

The Lean-hosted front end keeps no answers across builds. Only the solver
is skipped on a hit, and most of the hosted front end's time goes to
writing its queries, its own work and lean-smt's, before the solver sees
them. `cli::query_key` states that a query's key is every input of the
solver's run of it: the script and the formulas whose values its model
reads, with their guards. A query has a key only if no name of those
formulas or guards has a numeric component (`kept?`), and then the key's
names are the check's, component by component (`spelled?`). The
variables of its model are the ones that the script declares, and
whether a model is wanted is the answer's, as below. `cli::query_entry`
states which entries are written, and that an entry reads back as it was
written, key, answer and model, whatever characters they hold, so that an
entry is never read as another key's or with another answer. Both are
proved of `fren check`'s code, which [implements](Impl.md) them. In
`cli::query_entry`, the code gives `read`, what it reads back from the
text that it writes, so that `read`'s definition is the round trip. In
`cli::query_key`, the code gives `observations`, those of the key that
it makes, or none, and both `kept?` and `spelled?` are whether it makes
one. The Req alone does not tie `spelled?` to `kept?`: `observations`
cannot be an output, since an output of unbounded size must be defined,
and stating `spelled? iff kept?` would constrain the inputs. The proof
of the implementation is what shows that the two agree, so that the
key's names are the check's whenever a key is made.
`cli::query_cache` states when an entry answers a query,
`cli::kept_answer` which answers are kept, and `cli::contradicts` when a
fresh answer contradicts a kept one:

```fren
pub struct Observation {
    name: Seq<String>,           -- the components of the name of its value in the model
    formula: String,             -- the formula whose value the model reads
    guard: Option<Seq<String>>,  -- the name whose value must be `true` for the formula to be read
}

pub struct Key {
    script: String,                    -- the script
    observations: Seq<Observation>,    -- the formulas whose values its model reads
    solver: String,                    -- cvc5's version
    version: Int,                      -- how `fren check` runs a script and stores its answer
}

pub enum NamePart { Text(String), Number(Int) }   -- a component of a name of the check, which may be numeric

pub fn textual?(part: NamePart) := part is NamePart::Text(_)

-- Every one of `parts` is text.
set_option fren.lint.undecidable "allow" in
pub fn all_text?(parts: Seq<NamePart>) := forall (p: NamePart), when p in parts, textual?(p)

-- `parts` are the texts `texts`, one by one.
set_option fren.lint.undecidable "allow" in
pub fn spells?(parts: Seq<NamePart>, texts: Seq<String>) := parts.len = texts.len
    and (forall (j: Int), when 0 <= j < parts.len, parts[j] = NamePart::Text(texts[j]))

pub struct Observed {
    name: Seq<NamePart>,            -- the name of its value in the model
    formula: String,                -- the formula whose value the model reads
    guard: Option<Seq<NamePart>>,   -- the name whose value must be `true` for the formula to be read
}

pub fn observed_text?(o: Observed) :=
    all_text?(o.name) and match o.guard {
        Option::Some(g) => all_text?(g),
        Option::None => true,
    }

-- The key's observation `k` is the check's `o`.
pub fn holds?(o: Observed, k: Observation) := spells?(o.name, k.name) and k.formula = o.formula
    and match o.guard {
        Option::Some(g) => match k.guard {
            Option::Some(h) => spells?(g, h),
            Option::None => false,
        },
        Option::None => k.guard = Option::None,
    }

set_option fren.lint.undecidable "allow" in
pub proc query_key(
    script: String,
    observed: Seq<Observed>,          -- the formulas whose values its model reads, as the check names them
    observations: Seq<Observation>,   -- the same, as a key holds them
    solver: String,                   -- cvc5's version
    version: Int,                     -- the version of `fren check`'s cache
): (det kept?, det spelled?, det key: Key) {
    ensure kept: kept? iff (forall (o: Observed), when o in observed, observed_text?(o))
    ensure spelled: spelled? iff (observations.len = observed.len
        and (forall (i: Int), when 0 <= i < observed.len, holds?(observed[i], observations[i])))
    out key := Key { script, observations, solver, version }
}

pub enum Answer { Unsat, Sat, SatWithModel, Unknown }

pub proc query_cache(
    asked: Key,           -- the query's key
    want_model?,          -- the check reads a model of a `sat` answer
    found?,               -- an entry is at the path of `asked`'s hash
    stored: Key,          -- its key
    answer: Answer,       -- its answer
): (det hit?) {
    use self::Answer::{Sat, Unknown}

    require kept: when found?, answer != Unknown
    ensure rule: hit? iff (found? and stored = asked and not (want_model? and answer = Sat))

    expect exact: when hit?, stored.script = asked.script and stored.solver = asked.solver
        and stored.version = asked.version
    expect model_kept: when hit? and want_model?, answer != Sat
    cover hash_shared: found? and stored != asked
}

pub struct Binding {
    name: Seq<NamePart>,  -- a name of the model
    value: String,        -- its value
}

pub struct Entry {
    key: Key,
    answer: Answer,
    model: Seq<Binding>,  -- the model of a `SatWithModel` answer
}

set_option fren.lint.undecidable "allow" in
pub proc query_entry(
    written: Entry,       -- what is written, if it is kept
): (det text?, det read: Option<Entry>) {
    use self::Answer::{SatWithModel, Unknown}

    require model_only_kept: when written.answer != SatWithModel, written.model = []
    ensure kept: text? iff (written.answer != Unknown
        and (forall (b: Binding), when b in written.model, all_text?(b.name)))
    out read := if text? then Option::Some(written) else Option::None
}

pub proc kept_answer(answer: Answer): (det kept?) {
    use self::Answer::Unknown

    ensure rule: kept? iff answer != Unknown
}

pub proc contradicts(
    fresh: Answer,        -- the solver's answer
    kept: Answer,         -- the entry's answer to the same key
    same_model?,          -- both have models, and they are the same
): (det contradiction?) {
    use self::Answer::{SatWithModel, Unknown, Unsat}

    require both_kept: fresh != Unknown and kept != Unknown
    ensure rule: contradiction? iff ((fresh = Unsat) != (kept = Unsat)
        or (fresh = SatWithModel and kept = SatWithModel and not same_model?))

    expect agree: when fresh = kept and fresh != SatWithModel, not contradiction?
}
```

## Limits

Each solver query has two limits, and a query that reaches either is
`Unknown` (see [Verdicts](Check.md#verdicts)), with cvc5's explanation of
why it stopped.

- `--timeout SECONDS` limits the query's wall-clock time, by cvc5's
  option `tlimit-per`. Whether a query reaches it depends on the machine
  and on what else runs on it, so under load a check can be inconclusive
  that another run decides.
- `--resource-limit N` limits the solver's work on the query, counted in
  cvc5's resource units, by its option `rlimit-per`. cvc5 counts them the
  same way on every run, whatever the machine's speed and load, so whether
  a query reaches this limit depends only on the query and on the version
  of cvc5. A script sets `rlimit-per` only when the limit is not 0.

With `--timeout 0` and a resource limit, every run of `fren check` on the
same spec has the same results. The limits are those of each query, not of
the whole run.

The Lean-hosted front end has both limits as options: `fren.timeout` and
`fren.resourceLimit` (see [Options](Lean.md#options)). It sets the same
cvc5 options, but its scripts differ from `fren check`'s (see [Solver
queries](#solver-queries)), and the work that a query needs can differ
with its script, so a query near a resource limit can reach it in one front
end and not in the other, as a query near a time limit can.

## Forced outputs

An unrealizable procedure's error names the input on which its
guarantees conflict, and a minimal set of guarantees that conflict on it.
A note at a guarantee of that set says which output it forces to a value
that the rest of the set forces to another, or, for an output of an
enumeration, to a value of a variant that the rest of the set rules out,
where a side may force only the variant and not a whole value (see
[Forced outputs](Check.md#forced-outputs)). `--examples N` shows at most `N` such
notes for each unrealizable procedure, and asks the solver no more of
their questions once it has found them: `--examples 0` asks none, and
`--examples all` shows a note at every guarantee that has one. A note of
variants counts as one note, as a note of values does. The
default is 1, since each note costs solver queries. `fren mutate` takes
it too, as it takes `--timeout`, for the checks of its mutants. The
Lean-hosted front end has the option `fren.examples` (see
[Options](Lean.md#options)), a whole number with the same default.

## Parallel checking

`fren check` checks up to `--jobs` procedures and global expectations at
once, each in a thread of its own, but reports them in the order in which
it would check them one at a time. Its output is the same for every
`--jobs`, and the same as checking them one at a time: the diagnostics and
their counterexamples, in the same order, the summary, the exit status,
and the queries of `--dump-smt`, whatever the order in which the queries
run. A query that reaches a [limit](#limits) is the one exception: a busier
machine can make a query reach `--timeout`, and running queries at once
makes the machine busier. A resource limit does not depend on the load, so
with `--timeout 0` and `--resource-limit`, the output is the same for every
`--jobs` too. A procedure's [checks by
testing](Check.md#checking-by-testing) run with its solver queries, from
a random stream of its own, so they do not depend on the order either.
`--jobs` is at least 1.
`fren quickcheck` tests up to `--jobs` procedures and global expectations
at once in the same way: each from a random stream of its own, reported
in order, so its output is the same for every `--jobs`.
`fren mutate` checks its mutants one at a time.

## Timings

With `--timings`, `fren check` writes to standard error, after the
summary, a line for each procedure and global expectation that it
checked, slowest first, then a line of their total:

```text
timing: 41.3 ms (solver 41.3 ms, testing 0.0 ms): `c` (comp c)
timing: total 41.3 ms (solver 41.3 ms, testing 0.0 ms), of 1 procedures and global expectations
```

Each time is wall-clock time, in milliseconds. `solver` is the time of the
checks that the solver decides, with the confirmation of its models in
Fren's [semantics](Models.md), and `testing` that of the checks [by
testing](Check.md#checking-by-testing) and [by
enumeration](Check.md#checking-by-enumeration). A query that another
procedure asked first is answered without the solver (see [Solver
queries](#solver-queries)), so it counts for whichever asked it first.
Under [`--jobs`](#parallel-checking), the procedures run at once and
share the machine, so each time is longer than it would be alone, and
the total is more than the run's wall-clock time; `--jobs 1` times each
alone. Only these lines differ between two runs that differ only in
`--timings`.

## Evidence

`fren check --evidence METHOD` checks the spec as though `set_option
fren.evidence "METHOD"` were set before every procedure, global
expectation and [refinement](Lang/Refinement.md), and before every member
that a setting can precede, in place of the spec's own settings (see
[Checking by testing](Check.md#checking-by-testing)). `METHOD` is one of
the values of `fren.evidence`: `solver`, `random`, `enumerated` or
`enumerated+random`; any other is an error of the arguments, and nothing is
checked. The spec's own settings are still read, and an invalid or
misplaced one is still an error (`F0214`, `F0215`, `F0216`), but none of
them sets a check's evidence. The checks of functions and constants stay
the solver's, as do those of values given where subset types are declared
(`check::method_run`), and a method that does not run a check still skips
it, as it says (`F0654`). Enumeration's size is the one that the spec sets,
or the default. The option is how the test job `methodsAgree` runs every
check under every method that applies, to compare them
([Agreement of methods](Methods.md#agreement-of-methods)).
`cli::evidence_in_effect` states which evidence a check has:

```fren
pub proc evidence_in_effect(
    given?,                  -- `--evidence` is given
    given_random?,           -- it sets random testing
    given_enumerated?,       -- it sets enumeration
    set?,                    -- a `set_option fren.evidence` is in effect for the check
    set_random?,             -- it sets random testing
    set_enumerated?,         -- it sets enumeration
): (det random?, det enumerated?) {
    ensure random_rule: random? iff (if given? then given_random? else set? and set_random?)
    ensure enumerated_rule: enumerated? iff (if given? then given_enumerated? else set? and set_enumerated?)

    expect option_first: when given?, random? = given_random? and enumerated? = given_enumerated?
    expect solver_default: when not given? and not set?, not random? and not enumerated?
}
```

## Exit status

| Status | Meaning |
|---|---|
| 0 | every check passed |
| 1 | some result is an error: a check failed; or Fren reports an internal error, such as one that reports a refuted model |
| 2 | the checks could not run: an unreadable file, bad arguments, or a static error, including a denied lint |
| 3 | no result is an error, but some diagnostic is a warning: a check was inconclusive, a constraint is redundant, or a [lint](Lint.md) warned |

`fren quickcheck` exits as `fren check` does, and so does `fren mutate`,
with each surviving mutant a warning (`mutate::exit`). Every command follows one
convention, which `cli::exit_status` states: 2 exactly when the command
could not run, and otherwise 0, 1 or 3, with 0 meaning that there is
nothing to report. What 1 and 3 mean is each command's own:

- `fren check` and `fren quickcheck`, the table above (`cli::exit`);
- `fren eval`, a behaviour that does not meet the procedure or makes an
  expectation false, and one that could not be completed (see [Evaluation and
  testing](Eval.md#fren-eval), `eval::eval_exit`);
- `fren trace`, a procedure below `--require` or an unclaimed marker
  (`trace::trace_exit`);
- `fren fmt` and `fren fix`, with `--check`, a file that would change (see
  [Formatting](Fmt.md#exit-status) and [Fixing
  lints](Lint.md#fixing-lints)).

`cli::exit`, `eval::eval_exit`, `trace::trace_exit` and `mutate::exit`
refine `exit_status`. So do `fmt::exit` and `lint::fix_exit`, which say
whether the command could run in terms of what it read, `all_parsed?` and
`loaded?`: their expectation blocks pass it explicitly as the specification argument
(see [Refinement](Lang/Refinement.md#refinement-in-expectation-blocks)).

```fren
pub proc exit_status(
    ran?,                  -- the command could run
): (code: Int) {
    ensure not_run: code = 2 iff not ran?
    ensure documented: code is 0..=3
}
```

`cli::exit` gives the exit status, from whether the checks ran and the
most severe [level](View.md#severity) of their results, of the
[lints](Lint.md) reported along the way, and of its internal errors, each
an `Error`, such as one that reports a refuted model (see [Check
results](View.md#check-results)). So a run with an internal error exits
with 1, even where the result that it reports is inconclusive:

```fren
pub proc exit(
    ran?,                  -- no static errors: checks ran
    worst: Severity,       -- the most severe level over all results, lints and internal errors
): (det code: Int) {
    ensure code_rule: code = table {
        not ran? => 2,
        ran? and worst = Error => 1,
        ran? and worst = Warning => 3,
        ran? and worst <= Info => 0,
    }

    expect zero_means_no_problem: when code = 0, ran? and worst <= Info
    expect documented_codes: 0 <= code <= 3
}

expect check_exit_status(ran?, worst: view::Severity) {
    use view
    call concrete := exit(ran?, worst)
    refines concrete exit_status(ran?)
}
```

`cli::worst_severity` gives the most severe level over all results,
lints and internal errors of a run, from the levels present among them:

```fren
pub proc worst_severity(
    present: Set<Severity>,      -- the levels of the run's results, lints and internal errors
): (det worst: Severity) {
    -- The last row includes runs with no checks at all.
    ensure rule: worst = table {
        Error in present => Error,
        not Error in present and Warning in present => Warning,
        not (Error in present or Warning in present) => Silent,
    }

    expect worst_present: when worst != Silent, worst in present
    -- The maximum of the levels present, counting `Info` as `Silent`.
    expect maximum: (when Error in present, worst >= Error) and (when Warning in present, worst >= Warning)
        and worst != Info
}
```

`cli::run` combines the two: the levels present decide the exit status.

```fren
pub proc run(ran?, present: Set<Severity>): (det code: Int) {
    call counted := worst_severity(present)
    call ends := exit(ran?, counted.worst)

    ensure exit_code: code = ends.code

    expect error_exits_1: when ran? and Error in present, code = 1
    expect warning_exits_3: when ran? and not Error in present and Warning in present, code = 3
    expect clean_exits_0: when ran? and not Error in present and not Warning in present, code = 0
}
```

Put together with the [severity of a result](View.md#severity), this says
what a check's verdict does to the exit status, across the chapters: a
check that fails, other than as redundant, makes `fren check` exit with 1,
whatever else is reported. A check that passes is silent, so a run whose
checks all pass reports at most information and exits with 0, and one in
which a check is inconclusive and nothing worse is reported exits with 3:

```fren
use view::severity

expect failing_check_exits_1(s_kind: Kind, s_verdict: Verdict, r_ran?, r_present: Set<Severity>) {
    call s := severity(s_kind, s_verdict)
    call r := run(r_ran?, r_present)
    expect failing_check_exits_1: when r.ran? and s.level in r.present and s.verdict = Verdict::Fail
        and s.kind != Kind::Redundancy,
        r.code = 1
}

expect passing_checks_exit_0(s_kind: Kind, s_verdict: Verdict, r_ran?, r_present: Set<Severity>) {
    call s := severity(s_kind, s_verdict)
    call r := run(r_ran?, r_present)
    expect passing_checks_exit_0: when r.ran? and s.verdict = Verdict::Pass and r.present subset {s.level, Info},
        s.level = Silent and r.code = 0
}

expect inconclusive_exits_3(s_kind: Kind, s_verdict: Verdict, r_ran?, r_present: Set<Severity>) {
    call s := severity(s_kind, s_verdict)
    call r := run(r_ran?, r_present)
    expect inconclusive_exits_3: when r.ran? and s.verdict = Verdict::Inconclusive and s.level in r.present
        and r.present subset {s.level, Info},
        r.code = 3
}
```

## Colour

The `fren` command colours its diagnostics: the severity's
colour for the header and the underline, blue for the gutter, and red and
green for what a suggested edit removes and adds. `cli::color` says when
they are coloured, from `--color` and whether standard error, where they
go, is a terminal. With `auto`, the environment can turn
colour off, following the [`NO_COLOR`](https://no-color.org/) convention
and the `dumb` terminal of `TERM`; `always` and `never` override it.

```fren
pub enum ColorChoice { Auto, Always, Never }

use self::ColorChoice::{Always, Auto, Never}

set_option fren.evidence "enumerated" in
pub proc color(
    choice: ColorChoice,
    tty?,          -- standard error is a terminal
    no_color?,     -- `NO_COLOR` is set and not empty
    dumb?,         -- `TERM` is `dumb`
): (colored?) {
    ensure always: when choice = Always, colored?
    ensure never: when choice = Never, not colored?
    ensure auto: when choice = Auto, colored? iff (tty? and not no_color? and not dumb?)

    -- Piped output, as in tests and logs, is plain unless asked for.
    expect pipes_plain: when not tty? and choice != Always, not colored?
    -- `always` and `never` decide alone, whatever the environment.
    expect forced: when choice != Auto, colored? iff choice = Always
}
```

## Agreement with Lean

For the same results, the exit status is 1 exactly when a Lean build fails,
and nonzero exactly when `lake build --wfail` fails (see
[Diagnostics](View.md#severity)). `cli::agrees_with_build` confirms this:

```fren
use view::build

pub proc agrees_with_build(worst: Severity) {
    call hosted := build(worst)
    call standalone := exit(true, worst)

    expect failing: standalone.code = 1 iff hosted.fails?
    expect wfail: standalone.code != 0 iff hosted.fails_wfail?
}
```

The `fren` command shares Fren's grammar, name resolution and checks with
Lean. It accepts only Fren, including the `tested` and `trusted` claims of
[Traceability](Trace.md): anything that needs Lean, such as `impl`, is a
static error rather than being ignored. A standalone command also stops
when preparing the evaluator's independent reading reaches its
[expansion limit](Eval.md#expansion-limit). This is a resource failure,
with a diagnostic at the item and exit code 2, rather than a static error.
The hosted checker has no such preparation stage and may accept that
spec. Imposing the same copying allowance there would require preparing
a second, unused evaluator reading. The limit bounds the standalone
reader's work without making the hosted checker do that work.
`cli::accepts` states both the language rule and this exception:

```fren
pub enum Construct { Fren, LeanCode }
pub enum FrontEnd { Hosted, Standalone }
pub enum Reading { Ready, ExpansionLimit }

use self::Construct::Fren

set_option fren.evidence "enumerated" in
pub proc accepts(construct: Construct, front_end: FrontEnd, reading: Reading): (accepted?) {
    ensure rule: accepted? iff front_end = FrontEnd::Hosted
        or (construct = Fren and reading = Reading::Ready)
}
```

On a spec that both accept, Lean and the `fren` command give every check
the same verdict, except a [check by testing](Check.md#checking-by-testing),
which only the `fren` command runs, and for failures name the same conflicting or ruling-out
constraints. Counterexample values may differ, since each comes from its
solver's model, but not those of a [check by
enumeration](Check.md#checking-by-enumeration), which both search in the
same order. So may the guarantees that a realizability failure
names, which are a [minimal](Check.md#minimal-sets) set that conflicts on
the input it reports: each front end's are minimal for its own input, and
for the same input they are the same. Its notes of [forced
outputs](#forced-outputs) are at those guarantees, so they may differ
with them. When the standalone evaluator's reading exceeds its expansion
limit, its commands report that resource failure instead of check
results; Lean's results and summary then have no standalone counterparts.
The front-end comparison still compares static errors and lints and
requires exit code 2, a located expansion-limit diagnostic and no check
results or summary from the standalone command. It does not treat any
other failure or unexplained exit as this exception. `cli::agreement`
states when the common verdict is required:

```fren
set_option fren.evidence "enumerated" in
pub proc agreement(hosted: Verdict, reading: Reading): (checked?, standalone: Verdict) {
    ensure checked: checked? iff reading = Reading::Ready
    ensure same_verdict: when checked?, standalone = hosted
}

#fren_check
```

## Substitution under binders

Expanding a definition or a simultaneous SMT `let` substitutes only free
occurrences of its parameters. Quantifiers (`forall`, `exists`, and the
marked element quantifiers), lambdas, and lets bind their declared names
in their body. A nested binder shadows substitutions for its own names.
Before substituting the remaining replacements, rename every body binder
that occurs in a replacement to a fresh name, consistently throughout its
scope, respecting nested shadowing. Fresh names must avoid all atoms in
the original term, all substitution keys and replacements, and names
already chosen for other binders in the same declaration group. Conservative renaming for an occurrence
that is itself bound in a replacement is permitted.

A let’s right hand sides are outside its binders’ scope: substitute in
those using the original substitution, without renaming their occurrences
of the let’s names. Quantifier and lambda sort annotations are unchanged.
These rules apply whether or not the query mentions a recursive function.
The hosted frontend’s Lean substitution and the CLI’s SMT substitution
must preserve exactly the same free variables and meaning.

The per-name scope decision is bound to the helper used by SMT substitution.
`cli::substitution_scope` comes after the chapter's last `#fren_check`, so
it is named, and the Lean-hosted front end then checks it, as the `fren`
command checks every procedure:

```fren
pub struct SubstitutionName { bound_here?, mentioned_in_replacement? }

pub proc substitution_scope(name: SubstitutionName): (det replace?, det rename?) {
    ensure shadowing: replace? iff not name.bound_here?
    ensure capture: rename? iff name.bound_here? and name.mentioned_in_replacement?
}

#fren_check substitution_scope
```
