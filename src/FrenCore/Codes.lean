-- keep-sorted start
import Lean.Elab.Term
-- keep-sorted end

/-!
# Error codes

Every error and warning Fren reports, except internal errors, has a code,
explained by `fren --explain CODE` as rustc explains its codes: what is
wrong, an erroneous example, why, and the example fixed.

Each code is explained in a Markdown file of its own, `Codes/CODE.md`. In
each explanation, the first ```` ```fren ```` block is the erroneous
example and the others are fixed versions. `lake test` checks that the
erroneous example reports the code (with `args`, if they are not `none`),
and that the fixed versions do not.

Codes are grouped by hundreds: `F01xx` syntax, `F02xx` names and items,
`F03xx` types, `F04xx` calls and where variables may be mentioned,
`F05xx` traceability, `F06xx` the results of checks, `F07xx` and `F08xx` lints and
their levels.
-/

namespace Fren.Core

structure ErrorCode where
  code : String
  /-- Markdown. -/
  explanation : String
  /-- The `fren` arguments that report the code on the erroneous example,
  before the file; `none` if it needs more than the example, such as other
  files. -/
  args : Option (List String) := some ["check"]
  deriving Inhabited

open Lean Elab Term in
/-- `error_codes% "DIR"`: the codes explained in the Markdown files of `DIR`,
relative to this file, in order of code. The file `CODE.md` explains
`CODE`, and a first line `<!-- args: ARGS -->` gives the arguments that
report it, separated by spaces, or `none`; it is not part of the
explanation. Lake rebuilds this module when a file changes, as its library
needs them (`lakefile.lean`). -/
elab "error_codes% " dir:str : term => do
  let some here := (System.FilePath.mk (← getFileName)).parent | throwError "no directory for `{← getFileName}`"
  let files := ((← (here / dir.getString).readDir).map (·.path)).filter (·.extension == some "md")
  let mut codes := #[]
  for f in files.qsort (·.toString < ·.toString) do
    let some code := f.fileStem | throwError "no code for `{f}`"
    let text ← IO.FS.readFile f
    let (args, explanation) : Option (List String) × String :=
      match text.splitOn "\n" with
      | first :: rest =>
        match (first.dropPrefix? "<!-- args: ").bind (·.toString.dropSuffix? " -->") with
        | some a => (if a.toString == "none" then none else some (a.toString.splitOn " "), "\n".intercalate rest)
        | none => (some ["check"], text)
      | [] => (some ["check"], text)
    codes := codes.push (mkApp3 (Lean.mkConst ``ErrorCode.mk) (toExpr code) (toExpr explanation) (toExpr args))
  Meta.mkArrayLit (Lean.mkConst ``ErrorCode) codes.toList

/-- The codes whose erroneous examples are computed: one too long to write
out, and one that needs a string that is not in NFC. -/
def computedCodes : Array ErrorCode := #[
  { code := "F0797", explanation := r#"A procedure or defined function of more than 100 lines (`too_many_lines`, allowed by default).

Example:

```fren
set_option fren.lint.too_many_lines "warn"

proc c(x: Int): (
"# ++ String.join ((List.range 50).map fun i => s!"    y{i}: Int,\n") ++ r#") {
"# ++ String.join ((List.range 50).map fun i => s!"    ensure r{i}: y{i} = x + {i}\n") ++ r#"}
```

Its lines are counted from its name to its end, but not those that are
blank or only comments. Split it into smaller procedures, as calls:

```fren
proc part(x: Int): (y: Int) { ensure r: y = x + 1 }

proc whole(x: Int): (y: Int) { call p := part(x) ensure r: y = p.y + 1 }
```
"# },
  { code := "F0799", explanation := r#"A string literal that is not in Unicode NFC (`unicode_not_nfc`, allowed by default).

Example, where the `e` is followed by U+0301, a combining acute accent:

```fren
set_option fren.lint.unicode_not_nfc "warn"

proc c(s: String): (p?) { ensure r: p? iff s = "cafe"# ++ "\u0301" ++ r#"" }
```

Strings compare by code point, and text is usually in NFC, where `é` is
the one code point U+00E9, so the literal never equals it. Write it in
NFC, as the message suggests. `fren fix` does not, since that changes the
literal's value:

```fren
proc c(s: String): (p?) { ensure r: p? iff s = "café" }
```
"# } ]

/-- Every code: explained in `Codes/CODE.md`, a file each, so that codes
added at once merge cleanly, or in `computedCodes`. -/
def errorCodes : Array ErrorCode := error_codes% "Codes" ++ computedCodes

/-- The explanation of `code`. Codes are written `F0101`; lower case is
accepted, as are `0101` and `101`. -/
def explain? (code : String) : Option ErrorCode :=
  let digits := (code.toUpper.dropWhile (· == 'F')).toString
  let norm := "F" ++ String.ofList (List.replicate (4 - min 4 digits.length) '0') ++ digits
  errorCodes.find? (·.code == norm)

end Fren.Core
