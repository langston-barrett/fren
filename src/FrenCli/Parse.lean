-- keep-sorted start
import FrenCli.Parse.Items
-- keep-sorted end

/-!
# Parser for `.fren` files

The grammar and precedence of `Fren.Lang` (`Reqs/Lang.md`), lowest first:
`when`/`unless` and the quantifiers `forall`/`exists`, `iff`, `or`, `and`,
`not`, comparisons and `is`, `+ -`, `*`, unary `-`; `if` is an atom whose
`else` branch extends as far right as possible.

A file may start with Lean header lines (`import ...`, `open Fren.Lang`),
which are skipped, so pure-spec Lean files can be checked too. Any other Lean
command is an error (`cli::accepts`).

The implementation lives under `FrenCli/Parse/`: `PatternSyntax`,
`ExprSyntax` and `ItemSyntax` hold the syntax and its lowering helpers;
`State` holds errors, layout and parser state; `Basic` holds token and
layout helpers. `Patterns`, `Types`, `Expressions`, `Members`, `Functions`,
`Procedures` and `Items` parse their respective constructs. This module
keeps the file parser and the public entry points. Public declaration
names are unchanged, and importing this module still brings in the whole
parser.
-/

namespace FrenCli

namespace Parser

/-- Skips `import X` and `open X` lines at the start of the file. -/
def header : P Unit := do
  repeat
    let t ← peek
    if isWord t "import" || isWord t "open" then
      markStart
      let first := (← get).pos
      discard bump
      let n ← peek
      unless n.tok matches .ident _ do fail n "a module name"
      discard bump
      modify fun s => { s with layout.items := s.layout.items.push (first, first + 1) }
    else break

/-- Parses a file, stopping at the first error of its syntax. An item that
has none but has a clause's keyword's error is broken (`lang::item_error`). -/
def file : P (Array Item) := do
  header
  let mut items := #[]
  repeat
    if (← peek).tok == .eof then break
    let start := (← peek).span.start
    let first := (← get).pos
    modify fun s => { s with itemStarts := s.itemStarts.push start, items := #[], clauses := #[] }
    let it ← item
    let shape := Fren.Core.ItemShape.ofList (← get).clauses.toList
    items := items.push (match Fren.Core.itemError? none shape (fun msg span => (span, msg)) with
      | some (span, msg) => it.breakWith span msg
      | none => it)
    modify fun s => { s with layout.items := s.layout.items.push (first, s.pos - 1) }
  return items

/-- The error of the first item of `items` that a keyword error breaks
(`Item.broken`), under any `set_option ... in`, if any. -/
def firstBroken? (items : Array Item) : Option ParseError :=
  items.findSome? brokenIn?
where
  brokenIn? : Item → Option ParseError
    | .broken span msg => some { span, msg }
    | .lintSetting _ _ _ _ _ (some body) => brokenIn? body
    | _ => none

end Parser

/-- The items of a file, or the error of its parser, or of its first broken
item (`Parser.firstBroken?`): what the evaluator reads, which needs a whole
file. -/
def parse (toks : Array Token) (src : Array Char) : Except ParseError (Array Item) := do
  let items ← (Parser.file).run' { toks, src }
  match Parser.firstBroken? items with
  | some e => throw e
  | none => pure items

/-- The items of a file, with where each starts in the source: what the
elaborator reads, which reports a broken item's error and checks the
others (`lang::item_error`). -/
def parseItems (toks : Array Token) (src : Array Char) : Except ParseError (Array Item × Array Nat) :=
  (fun (items, s) => (items, s.itemStarts)) <$> (Parser.file).run { toks, src }

/-- The layout of a file that parses. -/
def parseLayout (toks : Array Token) (src : Array Char) : Except ParseError Layout := do
  let (items, s) ← (Parser.file).run { toks, src }
  match Parser.firstBroken? items with
  | some e => throw e
  | none => pure s.layout

end FrenCli
