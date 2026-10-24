-- keep-sorted start
import Lean
-- keep-sorted end

/-!
# `fren_spec`

The definitions Fren generates for comps (`p.reqs`, `p.req.n`, ...) are in
this simp set, so `simp [fren_spec]` unfolds a spec in a proof.
-/

register_simp_attr fren_spec
