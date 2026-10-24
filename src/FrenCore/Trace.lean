-- keep-sorted start
import FrenCore.Check
import FrenCore.Names
import Lean.Data.NameMap
-- keep-sorted end

/-!
# Traceability (`Reqs/Trace`)

The evidence for components, shared by `#fren_trace` and `fren trace`:
levels, the checks of `tested` and `trusted` claims, the scan of tests for
`fren-covers:` markers, and the report.
-/

open Lean

namespace Fren.Core

/-- Evidence, weakest first (`trace::Level`). -/
inductive Level where
  | missing
  | trusted
  | tested
  /-- An `impl` proved by the solver: an axiom. -/
  | solver
  | proved
  deriving Inhabited, BEq, DecidableEq, Repr

/-- `trace::rank`. -/
def Level.rank : Level → Nat
  | .missing => 0
  | .trusted => 1
  | .tested => 2
  | .solver => 3
  | .proved => 4

def Level.name : Level → String
  | .missing => "missing"
  | .trusted => "trusted"
  | .tested => "tested"
  | .solver => "solver"
  | .proved => "proved"

def Level.all : Array Level := #[.missing, .trusted, .tested, .solver, .proved]

def Level.ofName? (s : String) : Option Level := Level.all.find? (·.name == s)

def unknownLevelMsg (s : String) : Msg :=
  { code? := some "F0507", headline := s!"unknown evidence level `{s}`"
    notes := #["note: the levels are `trusted`, `tested`, `solver` and `proved`, weakest first"]
    fixes := similarFixes "a level with a similar name exists" (Name.mkSimple s) ((Level.all.filter (· != .missing)).map (Name.mkSimple ·.name)) }

/-- A component's own evidence (`trace::direct`). -/
def directLevel (proved solver tested trusted : Bool) : Level :=
  if proved then .proved else if solver then .solver
  else if tested then .tested else if trusted then .trusted else .missing

/-- A component's evidence, from its own and its instances' (`trace::evidence`). -/
def evidenceLevel (own : Level) (hasOutputs : Bool) (weakest : Level) : Level :=
  if hasOutputs || own.rank >= weakest.rank then own else weakest

/-- How a component is reported (`trace::required`). -/
def traceSeverity (level threshold : Level) (enforced : Bool) : Option Severity :=
  if enforced && level.rank < threshold.rank then some .warning else none

/-- `trace::tested_file`. -/
def testedFileAccepted (fileExists covers : Bool) : Bool := fileExists && covers

/-- `trace::covers_line`. -/
def coversLineAccepted (componentExists claimed : Bool) : Bool := componentExists && claimed

/-- `trace::trusted_claim`. -/
def trustedAccepted (justified : Bool) : Bool := justified

/-- The exit status of `fren trace` (`trace::trace_exit`). -/
def traceExitCode (ran below stray : Bool) : UInt32 :=
  if !ran then 2 else if below || stray then 1 else 0

/-! ## Claims and markers -/

def marker : String := "fren-covers:"

/-- The components named by the `fren-covers:` marker on a line, if any: a
comma-separated list that ends the line, after any comment syntax. -/
def coversOf (line : String) : Array String :=
  match line.splitOn marker with
  | _ :: rest :: _ =>
    -- Block comments may close after the list.
    let rest := ((rest.trimAscii.toString.dropSuffix? "*/").map (·.toString)).getD rest
    (rest.splitOn ",").toArray.map (·.trimAscii.toString) |>.filter (!·.isEmpty)
  | _ => #[]

/-- Checks one file of a `tested` claim for component `comp`, given its
contents if it could be read (`trace::tested_file`). -/
def checkTestedFile (comp file : String) (src? : Option String) : Except Msg Unit := do
  let covers := src?.any fun src => (src.splitOn "\n").any (coversOf · |>.contains comp)
  if testedFileAccepted src?.isSome covers then return
  match src? with
  | none => throw { code? := some "F0501", headline := s!"cannot read `{file}`", label? := some "no such file, or unreadable"
                    notes := #["note: paths are relative to the directory Fren runs in, usually the project's root"] }
  | some _ => throw { code? := some "F0502", headline := s!"`{file}` does not say that it covers `{comp}`"
                      label? := some s!"no `{marker} {comp}` in this file"
                      notes := #["note: a test names the components it covers, so that claims cannot silently go stale",
                        s!"help: add a comment `{marker} {comp}` to `{file}`"] }

/-- A justification, without surrounding whitespace (`trace::trusted_claim`). -/
def trimmedWhy (why : String) : String := why.trimAscii.toString

def checkTrusted (why : String) : Except Msg Unit := do
  unless trustedAccepted (trimmedWhy why != "") do
    throw { code? := some "F0503", headline := "the justification of a `trusted` claim cannot be empty"
            label? := some "empty justification"
            notes := #["note: a `trusted` claim records why the component holds without a proof or a test",
              "help: say why it can be trusted, e.g. `trusted c: \"checked by hand against the datasheet\"`"] }

/-- The `tested` and `trusted` claims, by component path. -/
structure Claims where
  tested : NameMap (Array String) := {}
  trusted : NameMap (Array String) := {}
  deriving Inhabited

/-- What the report needs to know about a component. -/
structure TraceComp where
  path : Name
  hasOutputs : Bool
  /-- The components of its instances. -/
  insts : Array Name
  /-- Has an `impl` proved by Lean. -/
  proved : Bool := false
  /-- Has an `impl` proved by the solver. -/
  solver : Bool := false
  deriving Inhabited

/-- The evidence for every component. Instances refer to components
declared earlier, so each pass settles those whose instances are settled. -/
def levels (comps : Array TraceComp) (claims : Claims) : NameMap Level := Id.run do
  let mut out : NameMap Level := {}
  for _ in [0:comps.size + 1] do
    for c in comps do
      if out.contains c.path then continue
      let insts := c.insts.map (out.get? ·)
      if insts.any (·.isNone) then continue
      let own := directLevel c.proved c.solver (claims.tested.contains c.path) (claims.trusted.contains c.path)
      let weakest := insts.foldl (init := Level.proved) fun w l? =>
        let l := l?.getD .missing
        if l.rank < w.rank then l else w
      out := out.insert c.path (evidenceLevel own c.hasOutputs weakest)
  return out

/-- A marker in a scanned file that no claim matches (`trace::covers_line`). -/
structure Stray where
  file : String
  line : Nat
  /-- Where the component's name is in the line, in characters, and its
  length. -/
  col : Nat
  len : Nat
  msg : Msg

/-- The markers in `files` (path and contents) that do not name a component
whose `tested` claim names that file. -/
def strays (comps : Array Name) (claims : Claims) (files : Array (String × String)) : Array Stray := Id.run do
  let mut out := #[]
  for (file, src) in files do
    let lines := src.splitOn "\n"
    for line in lines, i in [1:lines.length + 1] do
      for c in coversOf line do
        let path? := comps.find? (showComp · == c)
        let claimed := path?.any fun p => (claims.tested.getD p #[]).contains file
        unless coversLineAccepted path?.isSome claimed do
          let before := (line.splitOn marker).head!
          let rest := (line.drop (before.length + marker.length)).toString
          let col := before.length + marker.length + (rest.splitOn c).head!.length
          out := out.push { file, line := i, col, len := c.length, msg := if path?.isNone
            then { code? := some "F0504", headline := s!"`{marker}` names `{c}`, which is not a component"
                   label? := some s!"no component `{c}`"
                   notes := #["note: components are named by their full path, such as `a::b::c`"]
                   fixes := (similarStr c (comps.map showComp)).toArray.map fun s =>
                     { msg := s!"a component with a similar name exists: `{s}`", replacement := s } }
            else { code? := some "F0505", headline := s!"`{marker}` names `{c}`, but no `tested` claim for it names `{file}`"
                   label? := s!"`{c}` does not claim this file"
                   notes := #["note: a marker records that a test covers a component; a `tested` claim makes it count as evidence",
                     s!"help: add `tested {c}: \"{file}\"`, or `\"{file}\"` to an existing `tested {c}` claim"] } }
  return out

/-- A component below the required level. -/
def belowMsg (path : Name) (l threshold : Level) (how : String) : Msg :=
  { code? := some "F0506", headline := s!"`{showComp path}` has evidence `{l.name}`, below `{threshold.name}` ({how})"
    label? := some s!"evidence `{l.name}`"
    notes := #[s!"note: {how} requires every component to have evidence `{threshold.name}` or stronger",
      "help: add an `impl`, a `tested` claim or a `trusted` claim for it"] }

/-- The report: how many components are at each level, and those below
`proved` by level. -/
def traceSummary (comps : Array Name) (ls : NameMap Level) : String :=
  let at_ (l : Level) := comps.filter (ls.getD · .missing == l)
  let counts := Level.all.reverse.map fun l => s!"{(at_ l).size} {l.name}"
  let lists := (Level.all.filter (· != .proved)).reverse.filterMap fun l =>
    if (at_ l).isEmpty then none
    else some s!"\n{l.name}: {", ".intercalate ((at_ l).toList.map fun c => s!"`{showComp c}`")}"
  s!"evidence: {", ".intercalate counts.toList}{String.join lists.toList}"

/-! ## Globs -/

/-- Whether `path` (segments separated by `/`) matches `pat`: `*` matches
within a segment, `**` any number of segments. -/
partial def globMatch (pat path : List String) : Bool :=
  match pat, path with
  | [], [] => true
  | "**" :: ps, _ => globMatch ps path || (match path with | _ :: rest => globMatch pat rest | [] => false)
  | p :: ps, s :: ss => segMatch p.toList s.toList && globMatch ps ss
  | _, _ => false
where
  segMatch : List Char → List Char → Bool
    | [], [] => true
    | '*' :: ps, s => segMatch ps s || (match s with | _ :: rest => segMatch ('*' :: ps) rest | [] => false)
    | p :: ps, c :: cs => p == c && segMatch ps cs
    | _, _ => false

/-- The files matching the globs, relative to the current directory and
sorted. -/
def expandGlobs (globs : Array String) : IO (Array String) := do
  let mut out := #[]
  for g in globs do
    let segs := g.splitOn "/" |>.filter (· != ".")
    -- Walk from the longest prefix without wildcards.
    let fixed := segs.takeWhile (!·.contains '*')
    let root : System.FilePath := if fixed.isEmpty then "." else System.mkFilePath fixed
    if fixed.length == segs.length then
      if ← root.pathExists then out := out.push root.toString
      continue
    unless ← root.isDir do continue
    for f in ← root.walkDir do
      if ← f.isDir then continue
      let rel := f.toString.dropPrefix? "./" |>.map (·.toString) |>.getD f.toString
      if globMatch segs (rel.splitOn "/") then out := out.push rel
  return out.toList.eraseDups.toArray.qsort (· < ·)

end Fren.Core
