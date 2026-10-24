-- keep-sorted start
import Fren.Lint
import Fren.Model
-- keep-sorted end

/-!
# Name resolution

Adapts Fren's scoping rules (`FrenCore.Names`) to Lean syntax: errors are
reported at the offending path segment.
-/

open Lean

namespace Fren

export Core (Resolved showPath showModule)

/-- A single path segment as a simple name, rejecting Lean-style dotted names. -/
def segName [Monad m] [MonadError m] (seg : Syntax) : m Name := do
  let n := seg.getId
  unless n.isAtomic do
    throwErrorAt seg (Core.dottedNameMsg n #[] (inExpr := false)).text
  return n

variable {m : Type → Type} [Monad m] [MonadEnv m] [MonadError m] [MonadOptions m]

def liftResolve (segs : Array Syntax) : Except Core.Error α → m α
  | .ok a => pure a
  | .error e => throwErrorAt (segs[e.seg]?.getD .missing) e.msg.text

def liftMsg (ref : Syntax) : Except Core.Msg α → m α
  | .ok a => pure a
  | .error msg => throwErrorAt ref msg.text

/-- Resolves a `use` path written in module `from_`. -/
def resolveUsePath (from_ : Name) (segs : Array Syntax) : m Resolved := do
  liftResolve segs ((← getState).table.resolveUse from_ (← segs.mapM segName))

/-- Resolves a path in an expression or type in module `from_`, recording
the import it resolves through, if any (`unused_imports`), and the item it
uses (`dead_code`). -/
def resolvePath (from_ : Name) (segs : Array Syntax) (extra : Array Name := #[]) : m Resolved := do
  let names ← segs.mapM segName
  let table := (← getState).table
  let r ← liftResolve segs (table.resolvePath from_ names extra)
  if let some u := table.importVia from_ names then recordUsed u
  recordUsedItem r
  return r

/-- The generated Lean inductive for an enum. -/
def enumDecl (path : Name) : m Name := do
  match (← getState).enums.get? path with
  | some e => return e.decl
  | none => throwError "internal error: unknown enum `{path}`"

end Fren
