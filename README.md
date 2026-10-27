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

enum Method { Get, Put, Post, Delete }   -- Rust-style enums (can have payloads)
type Status := Nat is 100..=599          -- a pattern type
ordered struct Seconds(Nat)              -- a newtype with derived ordering
enum Decision { GiveUp, RetryAfter(Seconds) }

const MAX_ATTEMPTS: Nat := 5
const MAX_DELAY: Seconds := Seconds(30)

proc retry(
    method: Method,
    status: Status,
    attempt: Nat is 1..,       -- attempts made so far
    retry_after: Seconds,      -- the server's `Retry-After`, or 0
): (decision: Decision) {
    use http::Decision::{GiveUp, RetryAfter}

    ensure transient:
        decision is RetryAfter(_)
        iff status is 429 | 503
        and method != Method::Post
        and attempt < MAX_ATTEMPTS
    ensure honor_server: when decision is RetryAfter(d), d >= retry_after
    ensure backoff: when decision is RetryAfter(d), d >= Seconds(2 * attempt)
    ensure latency_budget: when decision is RetryAfter(d), d <= MAX_DELAY

    expect not_found_fails: when status = 404, decision = GiveUp
}

-- Once the client gives up, a later attempt doesn't start retrying again.
expect gives_up_for_good(
    a_method: Method,
    a_status: Status,
    a_attempt: Nat is 1..,
    a_retry_after: Seconds,
    b_method: Method,
    b_status: Status,
    b_attempt: Nat is 1..,
    b_retry_after: Seconds,
) {
    call a := retry(a_method, a_status, a_attempt, a_retry_after)
    call b := retry(b_method, b_status, b_attempt, b_retry_after)
    expect gives_up_for_good: when a.method = b.method and a.status = b.status and a.retry_after = b.retry_after
        and a.attempt <= b.attempt and b.decision is Decision::RetryAfter(_),
        a.decision is Decision::RetryAfter(_)
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

## Why Fren?

- Automation via a decidable logic (`QF_UFDTLIA`)

## Documentation

TODO

## Comparison to other tools

- FRET
- Alloy

## TODO

- Lean API
- Test generation
- Alloy-style `run`
- can global expectations quantify over base types? they should
