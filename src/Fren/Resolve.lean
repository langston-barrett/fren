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

/-- A single path segment as a simple name, rejecting Lean-style dotted names.
`afterPath` says that it follows a `::`. -/
def segName [Monad m] [MonadError m] (seg : Syntax) (afterPath := false) : m Name := do
  let n := seg.getId
  unless n.isAtomic do
    throwErrorAt seg (Core.dottedNameMsg n #[] (inExpr := false) (afterPath := afterPath)).text
  return n

/-- The segments of a path as simple names. -/
def segNames [Monad m] [MonadError m] (segs : Array Syntax) : m (Array Name) :=
  segs.mapIdxM fun i s => segName s (afterPath := i > 0)

variable {m : Type → Type} [Monad m] [MonadEnv m] [MonadError m] [MonadOptions m]

def liftResolve (segs : Array Syntax) : Except Core.Error α → m α
  | .ok a => pure a
  | .error e => throwErrorAt (segs[e.seg]?.getD .missing) e.msg.text

def liftMsg (ref : Syntax) : Except Core.Msg α → m α
  | .ok a => pure a
  | .error msg => throwErrorAt ref msg.text

/-- The identifier that `x` declares, without the `!` that marks it as
shadowing (`Core.declaredName`), and whether it has one. -/
def declaredIdent (x : Syntax) : Syntax × Bool :=
  let (n, bang) := Core.declaredName x.getId
  (if bang then mkIdentFrom x n else x, bang)

/-- The declaration `x`, without its `!`, checked to be written with `!`
exactly when it hides something: `hidden n` is what a declaration of `n`
hides, if anything (`lang::shadowing`). -/
def declare (x : Syntax) (hidden : Name → Option String) : m Syntax := do
  let (y, bang) := declaredIdent x
  liftMsg x (Core.checkLeanToken y.getId bang)
  liftMsg x (Core.checkShadowing y.getId (hidden y.getId) bang)
  return y

/-- Resolves a `use` path written in module `from_`. -/
def resolveUsePath (from_ : Name) (segs : Array Syntax) : m Resolved := do
  liftResolve segs ((← getState).table.resolveUse from_ (← segNames segs))

/-- Resolves a path in an expression or type in module `from_`, recording
the import it resolves through, if any (`unused_imports`), and the item it
uses (`dead_code`). -/
def resolvePath (from_ : Name) (segs : Array Syntax) (extra : Array Name := #[]) : m Resolved := do
  let names ← segNames segs
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
