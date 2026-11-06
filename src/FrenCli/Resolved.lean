-- keep-sorted start
import FrenCli.Lex
import FrenCore.Ty
import Lean.Data.Json.Printer
-- keep-sorted end

/-!
# The resolved surface (`Reqs/Cli#resolved-surface`)

The source and annotations over its character spans, recorded during name
resolution and type checking. Keeping the source retains generic declarations,
module boundaries and surface constructs instead of their lowered formulas.
-/

namespace FrenCli

/-- A resolved item path, distinguishing the prelude from a user's root
items, as `Ty.showQualified` distinguishes their types. -/
def resolvedPath (p : Lean.Name) : String :=
  (if Fren.Core.inPrelude p then "prelude::" else "") ++ Fren.Core.showPath p

/-- One fact about the surface, before instantiation: an item's resolved
path (`name`), a local name and its field reads (`local`), a declared or
written type or function result type (`type`), or an expression's type
(`expr`) or inferred type arguments (`arguments`). Spans are half-open
character offsets. -/
structure ResolvedAnnotation where
  file : Nat
  span : Span
  kind : String
  value : String
  deriving Inhabited, BEq

/-- The resolved surface, in file and source order. Repeated elaboration
of one span keeps its last annotation of each kind: the outer expression
records its type after any synthetic expressions used to elaborate it.
No iteration order of a hash table reaches the output. -/
def dumpResolved (files : Array (String × Array Char)) (annotations : Array ResolvedAnnotation) : String := Id.run do
  let quoted (s : String) := (Lean.Json.str s).compress
  let mut out := "; resolved\n"
  for (path, src) in files, file in [0:files.size] do
    out := out ++ s!"(file {quoted path}\n  (surface {quoted (String.ofList src.toList)})\n"
    let mut bySpan : Std.HashMap (Nat × Nat × String) ResolvedAnnotation := {}
    for a in annotations do
      if a.file == file && a.span.start < a.span.stop && a.span.stop ≤ src.size then
        bySpan := bySpan.insert (a.span.start, a.span.stop, a.kind) a
    let sorted := bySpan.toArray.map (·.2) |>.qsort fun a b =>
      a.span.start < b.span.start || (a.span.start == b.span.start &&
        (a.span.stop > b.span.stop || (a.span.stop == b.span.stop && a.kind < b.kind)))
    for a in sorted do
      out := out ++ s!"  ({a.kind} {a.span.start} {a.span.stop} {quoted a.value})\n"
    out := out ++ ")\n"
  return out ++ "; end of resolved\n"

end FrenCli
