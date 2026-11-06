-- keep-sorted start
import Fren.Model
import FrenCli.Elab.Model
-- keep-sorted end

/-! The two adapters preserve their literal syntax and realize simultaneous
type images from the shared theory core. -/
-- fren-covers: lang::generic_type_image, lang::generic_translation

open Lean

namespace FrenTest.GenericTheory

private def ph := Fren.placeholderName (Fren.Core.typeParamPath `f 0 `T)
private def other := Fren.placeholderName (Fren.Core.typeParamPath `g 0 `T)

-- A type image containing a source placeholder is not substituted again;
-- dictionaries follow their own target slot, including beneath binders.
private def source : Expr := .forallE `x (.const ph [])
  (.app (.const other []) (.app (.const (Fren.inhabitedName ph) []) (.bvar 0))) .default
private def target : Expr := .forallE `x (.app (.const `Seq []) (.const ph []))
  (.app (.const other []) (.app (.const `dictionary []) (.bvar 0))) .default

#guard Fren.atInstance `f #[`T] #[.app (.const `Seq []) (.const ph []), .const `dictionary []] source == target
#guard Fren.atInstance `g #[] #[] source == source

private def items : Std.HashMap String String :=
  ({} : Std.HashMap String String).insert "|::f|" "|::g|" |>.insert "|::g|" "|::h|"

-- SMT strings, including doubled quotes and text resembling sort names,
-- are literals. Resolved images and compound type arguments are inserted
-- once; they are not scanned for another replacement.
#guard FrenCli.genericText `f #[`T] #[.seq .int] items
  "(forall ((x |::f::0::T|)) (= (|::f| x) \"a\"\"|::f| |::f::0::T|\"))" ==
  "(forall ((x (Seq Int))) (= (|::g| x) \"a\"\"|::f| |::f::0::T|\"))"
#guard FrenCli.genericText `f #[`T] #[.abstract (Fren.Core.typeParamPath `f 0 `T)] items
  "(|::f| |::f::0::T| |::g|)" == "(|::g| |::f::0::T| |::h|)"

end FrenTest.GenericTheory
