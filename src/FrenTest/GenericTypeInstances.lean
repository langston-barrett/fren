-- keep-sorted start
import FrenCore.Patterns
import FrenCore.SubsetTypes
-- keep-sorted end

/-! The adapters for generic datatype instances preserve parameter-valued
images and subset metadata as well as concrete types. -/

open Fren.Core

#guard (PatTy.enum `Nested [.param 0, .enum `Option [.param 1]]).subst
    [.param 1, .bool] == .enum `Nested [.param 1, .enum `Option [.bool]]
#guard (PatTy.enum `Nested [.param 0, .param 1]).subst [.string] ==
  .enum `Nested [.string, .other]
#guard (PatTy.enum `Nested [.param 0]).subst [.enum `Nested [.param 0]] ==
  .enum `Nested [.enum `Nested [.param 0]]

private def small : PTy := {
  ty := .int, text := "Small", invariants := #[{ name := `Small.invariant, predicate := `small? }] }
private def shape : DataShape := {
  parts := #[#[.plain (.record `Pair [.param 1 `B, .enum `Option [.param 0 `A]])]] }
private def translated := shape.inst #[.plain .bool, small]
#guard translated.parts[0]![0]!.ty == .record `Pair [.int, .enum `Option [.bool]]
#guard translated.parts[0]![0]!.parts[0]!.invariants == small.invariants
#guard translated.parts[0]![0]!.parts[1]!.parts[0]!.ty == .bool
#guard (shape.instancePart 0 0 #[.bool, .string]).ty ==
  .record `Pair [.string, .enum `Option [.bool]]
