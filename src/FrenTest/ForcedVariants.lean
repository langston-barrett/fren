-- keep-sorted start
import Fren.View
-- keep-sorted end
open Fren.Lang

-- A clash of variants (`Reqs/Check#forced-outputs`): a guarantee that
-- forces only an output's variant, against the rest of the conflict, which
-- forces a value of another, in the same text as `fren check` gives
-- (`test/cli/results/f0601_forced_variant.fren`).

enum Method { Get, Put, Post, Delete }
type Status = status: Nat where invariant: status is 100..=599
ordered struct Seconds(Nat)
enum Decision { GiveUp, RetryAfter(Seconds) }
const MAX_ATTEMPTS: Nat := 5
const MAX_DELAY: Seconds := Seconds(30)

type Pos = n: Nat where invariant: n is 1..
proc retry(method: Method, status: Status, attempt: Pos, retry_after: Seconds): (
    decision: Decision,
) {
    ensure transient:
        decision != Decision::GiveUp iff status is 429 | 503
        and method != Method::Post
        and attempt < MAX_ATTEMPTS
    ensure honor_server: match decision { Decision::RetryAfter(d) => d >= retry_after, _ => true }
    ensure backoff: match decision { Decision::RetryAfter(d) => d >= Seconds(2 * attempt), _ => true }
    ensure latency_budget: match decision { Decision::RetryAfter(d) => d <= MAX_DELAY, _ => true }
}

/--
error: `retry` is not realizable

note: for the input
          method = Method::Get
          status = 429
          attempt = 4
          retry_after = Seconds(31)
      no outputs satisfy `transient`, `honor_server` and `latency_budget`
help: weaken one of them, or add an `assume` that rules this input out
---
info: `transient` forces decision is Decision::RetryAfter(_), but `honor_server` and `latency_budget` force decision = Decision::GiveUp
---
info: conflicts with `transient` and `latency_budget`
---
info: conflicts with `transient` and `honor_server`
---
info: no branch of `transient` can hold

note: an `iff` requires matching truth values: all operands true or all operands false
note: each case keeps the reported input, definitions and calls
---
info: case "both operands are true" requires decision is Decision::RetryAfter(_), but `honor_server` and `latency_budget` force decision = Decision::GiveUp

note: this case conflicts with `honor_server` and `latency_budget`
---
info: case "both operands are true": `transient.1` must be true, but must be false to satisfy `honor_server` and `latency_budget`

member: decision != Decision::GiveUp
---
info: case "both operands are false" is impossible for the reported input

note: no other constraint is needed to rule out this case
---
info: case "both operands are false": `transient.2` must be false, but is true for the reported input

member: status is 429 | 503
                and method != Method::Post
                and attempt < MAX_ATTEMPTS
---
info: fren: 6 passed, 1 failed, 0 inconclusive, 0 redundant
-/
#guard_msgs in
#fren_check

-- `fren.examples 0`: no notes of forced variants either.

/--
error: `retry` is not realizable

note: for the input
          method = Method::Get
          status = 429
          attempt = 4
          retry_after = Seconds(31)
      no outputs satisfy `transient`, `honor_server` and `latency_budget`
help: weaken one of them, or add an `assume` that rules this input out
---
info: conflicts with `honor_server` and `latency_budget`
---
info: conflicts with `transient` and `latency_budget`
---
info: conflicts with `transient` and `honor_server`
---
info: fren: 6 passed, 1 failed, 0 inconclusive, 0 redundant
-/
#guard_msgs in
set_option fren.examples 0 in
#fren_check
