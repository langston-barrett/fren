-- keep-sorted start
import FrenCli.Search
-- keep-sorted end

/-! Tests of `VTy.readsSorts` and `Spec.fixedPools`: an abstract type is
seen however it can be reached, through a record's fields, a variant's
payload, generic arguments, newtypes, relations, sets and sequences, and
recursion, polymorphic recursion among it. A type from which none can be
reached has the same values in every world, so its pool is fixed; one
from which one can be reached may not, and a fixed pool of it would
silently leave values out of testing. -/

namespace Fren.Test.FixedPools

open FrenCli.Eval

def S : VTy := .abstract `S

def ctor (n : Lean.Name) (fields : Array VTy) : Ctor := { name := n, fields := fields.map (.anonymous, ·) }

def data (p : Lean.Name) (ctors : Array Ctor) (isRecord := false) : Lean.Name × DataDef := (p, { path := p, isRecord, ctors })

/-- A spec with the abstract type `S` and data types that reach it, or
not, in each way. -/
def sp : Spec :=
  { sorts := #[`S]
    data := [
      -- A record with a field of `S`, and one without.
      data `Box #[{ name := `Box, fields := #[(`a, S)] }] true,
      data `Flags #[{ name := `Flags, fields := #[(`a, .bool), (`b, .int)] }] true,
      -- A variant's payload.
      data `Opt #[ctor `None #[], ctor `Some #[S]],
      -- Generic: `S` only through an argument.
      data `G #[ctor `Leaf #[], ctor `Node #[.param 0]],
      -- Recursion, with and without `S`.
      data `L #[ctor `Nil #[], ctor `Cons #[.bool, .data `L []]],
      data `LS #[ctor `Nil #[], ctor `Cons #[S, .data `LS []]],
      -- Polymorphic recursion: `P<T>` holds a `P<G<T>>`, and `Q<T>` a
      -- `Q<S>`, which reaches `S` whatever `T` is.
      data `P #[ctor `End #[], ctor `More #[.data `P [.data `G [.param 0]]]],
      data `Q #[ctor `End #[], ctor `More #[.data `Q [S]]]
    ].foldl (fun m (p, d) => m.insert p d) {} }

/-- Types from which `S` can be reached. -/
def reaching : Array VTy := #[S, .data `Box [], .data `Opt [], .data `G [S], .data `LS [], .data `P [S], .data `Q [.bool],
  .newtype `W S, .rel S .bool, .rel .bool S, .set S, .seq S, .data `G [.data `Opt []], .seq (.data `Box [])]

/-- Types from which it cannot. -/
def notReaching : Array VTy := #[.bool, .int, .nat, .string, .data `Flags [], .data `G [.bool], .data `L [],
  .data `P [.bool], .newtype `W .bool, .rel .bool .int, .set .bool, .seq .string, .data `G [.data `L []]]

#guard reaching.all (·.readsSorts sp)
#guard notReaching.all (!·.readsSorts sp)

/-- `ty`'s values in a world in which `S` has `n` values. -/
def valuesIn (n : Nat) (ty : VTy) : Array Val :=
  smallValues sp { seed := 0, sizes := ({} : Lean.NameMap Nat).insert `S n } #[0, 1] #[] 24 2 ty

-- What `readsSorts` rests on: a type that does not reach `S` has the same
-- values in every world, and the basic ways of reaching it differ. (`Q`'s
-- values hold an `S` only deeper than `smallValues` goes: `readsSorts`
-- is conservative there.)
#guard notReaching.all fun ty => valuesIn 1 ty == valuesIn 3 ty
#guard #[S, .data `Box [], .data `Opt [], .data `G [S], .data `LS [], .newtype `W S, .set S].all
  fun ty => valuesIn 1 ty != valuesIn 3 ty

-- The fixed pools: those of the types that reach neither `S` nor the
-- integers, and are not sets or sequences.
#guard
  let pools := sp.fixedPools #[] (reaching ++ notReaching)
  (reaching.all (!pools.contains ·)) && pools.contains .bool && pools.contains .string
    && pools.contains (.data `L []) && pools.contains (.data `G [.bool]) && pools.contains (.newtype `W .bool)
    && !pools.contains .int && !pools.contains (.data `Flags []) && !pools.contains (.set .bool)
    && !pools.contains (.seq .string)

end Fren.Test.FixedPools
