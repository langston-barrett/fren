# Roadmap

## Later

Roughly in order, to be specified in Fren as each is started:

- Lean proofs: generate theorems for passing checks, proved by reconstruction
  (`lean-smt`) or by an explicit trust axiom, and accept user-written proofs
  when the solver gives up.
- Checks: conflict enumeration, model minimisation.
- Bindings that mention the component's own outputs (needs a check that the
  instance's inputs do not depend on its outputs).
- Time: discrete steps and past-time operators.

## Open questions

- `when C, D` uses a comma, and so do instance bindings. A binding cannot be
  a bare `when`, so parsing is unambiguous; readability is untested.
- Should `x in {A, B}` membership exist? `in` is already a keyword.
- `super::`, if relative paths beyond `self` turn out to be needed.
- Does a component with no assumptions, requirements or expectations deserve a
  warning?
