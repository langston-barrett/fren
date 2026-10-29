# Fren

Fren is a language for **f**ormal **r**equirements **en**gineering. Fren
consists of a DSL for writing requirements, and a suite of tools for checking
properties of DSL programs such as consistency, determinism, and refinement.

There are two ways to use Fren:

- As a standalone binary, with properties checked by an SMT solver
- As an embedded DSL in [Lean], with properties proved by [lean-smt] or by hand

[Lean]: https://lean-lang.org/
[lean-smt]: https://github.com/verse-lab/lean-smt

Fren is itself specified in Fren.

## Example

Consider the following specification of the retry policy of an HTTP client:

```fren
mod http

ordered struct Seconds(Nat)                    -- newtype with derived ordering
enum Decision { GiveUp, RetryAfter(Seconds) }  -- Rust-style enums
enum Method { Get, Put, Post, Delete }
type Status = status: Nat                      -- type alias with an invariant
    where status_range: status is 100..=599    -- `status_range` is a label
type Pos = n: Nat where positive: n is 1..     -- `is` matches against a pattern

const MAX_ATTEMPTS: Nat := 5
const MAX_DELAY: Seconds := Seconds(30)

proc retry(
    method: Method,
    status: Status,
    attempt: Pos,                    -- attempts made so far
    retry_after: Seconds,            -- the server's `Retry-After`, or 0
): (decision: Decision) {
    use http::Decision::{GiveUp, RetryAfter}

    ensure transient:
        decision is RetryAfter(_)
        iff status is 429 | 503      -- `|` is an or-pattern
        and method != Method::Post
        and attempt < MAX_ATTEMPTS

    ensure when decision is RetryAfter(d), and {
        honor_server:   d >= retry_after,
        backoff:        d >= Seconds(2 * attempt),
        latency_budget: d <= MAX_DELAY,
    }

    expect not_found_fails: when status = 404, decision = GiveUp
}

-- Once the client gives up, a later attempt doesn't start retrying again.
expect gives_up_for_good(
    method: Method,
    status: Status,
    retry_after: Seconds,
    early: Pos,
    late: Pos,
) {
    use http::Decision::RetryAfter

    assume later: early <= late

    call a := retry(method, status, early, retry_after)
    call b := retry(method, status, late, retry_after)

    expect stays_given_up:
        when b.decision is RetryAfter(_), a.decision is RetryAfter(_)
}
```

Each requirement looks reasonable on its own, but together they're infeasible:

```
$ fren check retry.fren
error[F0601]: `http::retry` is not realizable
  --> retry.fren:11:6
   |
11 | proc retry(
   |      ^^^^^ not realizable
   |
   = note: for the input
               method = Method::Get
               status = 429
               attempt = 4
               retry_after = Seconds(31)
           no outputs satisfy `transient`, `honor_server` and `latency_budget`
   = help: weaken one of them, or add an `assume` that rules this input out

note: `transient` forces decision is Decision::RetryAfter(_), but `honor_server` and `latency_budget` force decision = Decision::GiveUp
  --> retry.fren:19:12
   |
19 |     ensure transient:
   |            ^^^^^^^^^

...
```

Here, the server has asked the client to wait 31 seconds before retrying, but
that leaves the client in a state where it can't meet its own delay budget. The
right fix is a nontrivial design question.

## Features

- Readable, high-level DSL for specifying requirements in `.fren` or `.md` files
- Automated, fast, and reliable checks of properties of requirements:

  - Realizability: some system can meet the requirements, for every admissible input
  - Refinement: one procedure refines another
  - Vacuity, redundancy, determinism, and more!

- Fallbacks for when SMT automation fails: randomized testing, exhaustive testing, and Lean proofs
- `impl` blocks for proving that a Lean implementation meets the requirements
- Composition: build procedures from others, using rely/guarantee reasoning
- Extensive tooling: a formatter, linter with auto-fixes, and mutation testing tool

## Design philosophy and comparison to other tools

We believe that Fren sits in a unique niche among formal methods tools.
This niche stems from two factors:

1. It is a language for reasoning about *requirements* (i.e., *specifications*),
   not implementations. This is "lightweight formal methods".
2. It is relentlessly focused on good UX.

In particular, it is designed to avoid certain UX pitfalls of existing formal
methods tooling.

**Opacity**: If your [Verus] or [Dafny] proof fails, you are expected to
fix it with very limited feedback. Fixing it can involve proving, importing,
or instantiating additional lemmas. A variation of Greenspun's tenth rule
applies to the proof languages of such tools: "Any sufficiently complicated
formal methods tool contains an ad hoc, informally-specified, bug-ridden, slow
implementation of half of a proof assistant". Fren avoids this by eschewing
*any* form of user-aided proof. It instead sticks to a decidable subset of
SMT by default, with principled, built-in escape hatches to Lean proofs or
randomized testing where desired.

[Verus]: https://github.com/verus-lang/verus
[Dafny]: http://dafny.org/

**Unpredictability**: Tools like Dafny produce quantified axioms that [slow
down solvers]. In contrast, Fren sticks to a decidable subset of SMT. Tools
like [SAW] also use a decidable subset of SMT, but because they reason about
implementations, their queries are so hairy that solvers still struggle. Fren's
queries stay small and fast from reasoning at the specification level.

[slow down solvers]: https://arxiv.org/abs/2512.03926
[SAW]: https://github.com/GaloisInc/saw-script

**Unmooredness**: Other light-weight formal methods tools like [Alloy] and
[TLA+], while excellent at what they do, are disconnected from implementations
*by design*. Fren can be used this way, but you can also *prove* that your Lean
implementation satisfies your requirements.

[Alloy]: https://alloytools.org/
[TLA+]: https://lamport.azurewebsites.net/tla/tla.html

**Complexity**: Proof assistants such as [Rocq] and [Agda] have incredibly
rich languages, with implicit arguments, typeclasses, metaprogramming, ML-style
module systems, type-level computation, and more. Fren is a simple first-order
language with a straightforward lowering into Lean and SMT.

[Rocq]: https://rocq-prover.org/
[Agda]: https://github.com/agda/agda

Fren is abstract, compositional, simple, fast, and predictable. If you need more
power or expressivity, you can easily drop into Lean.

## Documentation

TODO

## TODO

- Lean API
- Test generation
- Alloy-style `run`
- can global expectations quantify over base types? they should
