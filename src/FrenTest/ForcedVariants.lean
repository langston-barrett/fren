-- keep-sorted start
import Fren.View
-- keep-sorted end
open Fren.Lang

-- A clash of variants (`Reqs/Check#forced-outputs`): a guarantee that
-- forces only an output's variant, against the rest of the conflict, which
-- forces a value of another, in the same text as `fren check` gives
-- (`test/cli/results/f0601_forced_variant.fren`).

enum Method { Get, Put, Post, Delete }
type Status := Nat is 100..=599
ordered struct Seconds(Nat)
enum Decision { GiveUp, RetryAfter(Seconds) }
const MAX_ATTEMPTS: Nat := 5
const MAX_DELAY: Seconds := Seconds(30)

comp retry {
    in method: Method
    in status: Status
    in attempt: Nat is 1..
    in retry_after: Seconds
    pub out decision: Decision
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
info: fren: 4 passed, 1 failed, 0 inconclusive, 0 redundant
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
info: fren: 4 passed, 1 failed, 0 inconclusive, 0 redundant
-/
#guard_msgs in
set_option fren.examples 0 in
#fren_check
