module

public import Lean

/-!
The unsqueezed-tactic linter: a `simp` or `grind` without `only` that is not
the last tactic of its goal branch. What such a call leaves behind depends on
the whole simp set, so the tactics after it break when a lemma is added.

The idea is that of Mathlib's flexible linter (`Mathlib/Tactic/Linter/
FlexibleLinter.lean`, Apache 2.0, by Damiano Testa). This one is our own, and
purely syntactic: it reads the parsed source and never elaborates a proof.

A tactic is terminal when it is the last of its sequence and the sequence is
terminal. The sequence of a `by`, `·`, `case`, `next`, `{ }`, `decreasing_by`,
a `match`, `induction` or `cases` alternative, or a branch of a tactic `if` is
terminal, since each must close its goal; so is the sequence after the `by`
of any other syntax, such as the project's `impl ... by` command. `try`, `first`, `all_goals`,
`any_goals`, `repeat`, `iterate`, `focus`, parentheses and a few wrappers pass
on what they have, as does the right of `<;>`; the left of `<;>` is never
terminal. Inside every other tactic nothing is terminal, so an unknown
combinator can only add findings.

Limits.
- It reports more than a goal-aware linter would. `simp; omega` is reported
  although `omega` tolerates any simp result, as is `simp; done`. A sequence
  that closes several goals in turn without bullets (`constructor; simp; simp`)
  has its first `simp` reported.
- It reads only tactics written in the source. A project macro that expands to
  `simp` is not seen, and neither is `simpa`, which closes its goal.
- `simp` inside `conv` is exempt: there it rewrites a chosen subterm.
- The last tactic of a terminal sequence is trusted to close its goal, as Lean
  requires of the sequence as a whole.
-/

public section

namespace FrenTest.ProofLint
open Lean

/-- The commands that change the namespace and the open declarations, and
with them the scoped syntax and the parser names that the rest of the file
may use. -/
private def scoping : List SyntaxNodeKind :=
  [``Parser.Command.namespace, ``Parser.Command.section, ``Parser.Command.end, ``Parser.Command.open]

/-- The commands of a Lean source file, or its parse errors. The environment
supplies the tokens and the syntax of the file's imports. Only the commands
in `scoping` are elaborated, so that scoped syntax parses as it does in a
build; syntax that the file declares for itself is not known. -/
def parseFile (env : Environment) (path source : String) : IO (Except String (Array Syntax)) := do
  let input := Parser.mkInputContext source path
  let (_, initial, initialMessages) ← Parser.parseHeader input
  let context : Elab.Command.Context :=
    { fileName := path, fileMap := input.fileMap, snap? := none, cancelTk? := none }
  let mut state := initial
  let mut messages := initialMessages
  let mut elaboration := Elab.Command.mkState env
  let mut commands := #[]
  for _ in [:source.utf8ByteSize + 1] do
    let scope := elaboration.scopes.head!
    let (command, next, nextMessages) := Parser.parseCommand input
      { env := elaboration.env, options := scope.opts, currNamespace := scope.currNamespace,
        openDecls := scope.openDecls } state messages
    messages := nextMessages
    if command.isOfKind ``Parser.Command.eoi then break
    commands := commands.push command
    state := next
    if scoping.contains command.getKind then
      match ← (Elab.Command.elabCommand command context |>.run elaboration).toIO' with
      | .ok (_, after) => elaboration := after
      | .error error => return .error s!"cannot follow a scope command: {← error.toMessageData.toString}"
  messages := messages ++ elaboration.messages
  if messages.hasErrors then
    let errors ← messages.toList.filterMap (fun message =>
      if message.severity matches .error then some message else none) |>.mapM (·.toString)
    return .error (String.intercalate "; " (errors.map (·.trimAscii.toString)))
  return .ok commands

private def heads : List String :=
  ["simp", "simp?", "simp!", "simp?!", "simp_all", "simp_all?", "simp_all!", "simp_all?!",
   "dsimp", "dsimp?", "dsimp!", "dsimp?!", "simp_arith", "simp_arith!", "simp_all_arith",
   "simp_all_arith!", "grind", "grind?"]

private def only (stx : Syntax) : Bool := stx.isToken "only" || stx.isToken " only"

/-- A `simp`, `dsimp`, `simp_all` or `grind` tactic without `only`. -/
private def flexible : Syntax → Bool
  | .node _ kind args =>
    (`Lean.Parser.Tactic).isPrefixOf kind && !(`Lean.Parser.Tactic.Conv).isPrefixOf kind &&
    (match (args[0]? : Option Syntax) with
      | some (Syntax.atom _ head) => heads.contains head.trimAscii.toString
      | _ => false) &&
    !args.any fun arg => only arg || (arg.getKind == nullKind && arg.getArgs.any only)
  | _ => false

/-- Syntax whose tactic sequence must close its goal. -/
private def closing : List Name :=
  [``Parser.Term.byTactic, ``Parser.Term.byTactic', ``Lean.cdot, ``Parser.Tactic.case,
   ``Parser.Tactic.«tacticNext_=>_», ``Parser.Tactic.inductionAlt, ``Parser.Term.matchAlt,
   ``Parser.Tactic.tacIfThenElse, ``Parser.Tactic.tacDepIfThenElse,
   ``Parser.Termination.decreasingBy]

/-- Tactics that run their sequence on the goal as it stands. -/
private def inheriting : List Name :=
  [nullKind, groupKind, ``Parser.Tactic.tacticSeq, ``Parser.Tactic.paren, ``Parser.Tactic.tacticTry_,
   ``Parser.Tactic.first, ``Parser.Tactic.allGoals, ``Parser.Tactic.anyGoals,
   ``Parser.Tactic.tacticRepeat_, ``Parser.Tactic.tacticIterate____, ``Parser.Tactic.focus,
   ``Parser.Tactic.withReducible, ``Parser.Tactic.set_option, ``Parser.Tactic.open]

private partial def visit (terminal : Bool) (stx : Syntax) (found : Array Syntax) : Array Syntax :=
  match stx with
  | .node _ kind args =>
    let found := if !terminal && flexible stx then found.push stx else found
    let bracketed := kind == ``Parser.Tactic.tacticSeqBracketed
    if bracketed || kind == ``Parser.Tactic.tacticSeq1Indented then
      let tactics := (if bracketed then stx[1] else stx[0]).getSepArgs
      (List.range tactics.size).foldl (init := found) fun found i =>
        visit ((terminal || bracketed) && i + 1 == tactics.size) tactics[i]! found
    else if kind == ``Parser.Tactic.«tactic_<;>_» then
      visit terminal stx[2] (visit false stx[0] found)
    else
      let inner := closing.contains kind || (inheriting.contains kind && terminal)
      (List.range args.size).foldl (init := found) fun found i =>
        -- The sequence after a `by` proves an obligation in any syntax, such
        -- as the project's `impl ... by` command.
        let afterBy := i > 0 && (match args[i - 1]! with
          | .atom _ word => word.trimAscii.toString == "by"
          | _ => false)
        visit (inner || afterBy) args[i]! found
  | _ => found

private partial def declIds (stx : Syntax) : Nat :=
  stx.getArgs.foldl (· + declIds ·) (if stx.isOfKind ``Parser.Command.declId then 1 else 0)

/-- The parts of a command that declare at most one name each: the command
itself, or the declarations of a `mutual` block and the like. -/
private partial def pieces (stx : Syntax) : Array Syntax :=
  if declIds stx ≤ 1 then #[stx] else stx.getArgs.flatMap pieces

/-- The source text of `stx` with each run of white space as one space, so
that neither layout nor position changes it. -/
private def squeezed (stx : Syntax) : String :=
  let text := match stx.getSubstring? (withLeading := false) (withTrailing := false) with
    | some text => text.toString
    | none => stx.reprint.getD ""
  (text.foldl (init := ("", false)) fun (out, gap) c =>
    if c.isWhitespace then (out, true)
    else ((if gap && !out.isEmpty then out.push ' ' else out).push c, false)).1

/-- A name for a declaration that does not depend on where it stands: the
name it declares; else, for an unnamed declaration (`example`, `instance`),
its kind, `@` and a hash of its signature's text, which tells the unnamed
declarations of a file apart; else the first identifier after the keyword of
another command, such as `impl` and `interp`; else the command's kind.
`open ... in` and the like are looked through. -/
private partial def label (stx : Syntax) : String :=
  if stx.isOfKind ``Parser.Command.in then label stx[2] else
  let inner := (stx.find? (·.isOfKind ``Parser.Command.declaration)).getD stx
  let name := match inner.find? (·.isOfKind ``Parser.Command.declId) with
    | some id => toString id[0].getId
    | none =>
      if inner.isOfKind ``Parser.Command.declaration then
        let signature := inner[1].find? fun part =>
          part.isOfKind ``Parser.Command.declSig || part.isOfKind ``Parser.Command.optDeclSig
        let digits := Nat.toDigits 16 ((hash (squeezed (signature.getD inner[1]))).toNat % 2 ^ 32)
        s!"{inner[1].getKind.components.getLast?.getD `declaration}@{String.ofList digits}"
      else match inner[1].find? (·.isIdent) with
        | some id => toString id.getId
        | none => toString (inner.getKind.components.getLast?.getD `command)
  name.replace " " "_"

/-- The unsqueezed `simp` and `grind` calls of a file's commands, each with
its identity in the file: the label of its declaration, `: ` and the call's
squeezed source text, so that the identity changes with neither the call's
position nor its layout, and a call that replaces another has another
identity. Only calls of the same text under the same label are numbered: the
second and later ones end in ` #n`. -/
def unsqueezed (commands : Array Syntax) : Array (String × Syntax) := Id.run do
  let mut found : Array (String × Syntax) := #[]
  let mut keys : Array String := #[]
  for piece in commands.flatMap pieces do
    for stx in visit false piece #[] do
      let key := s!"{label piece}: {squeezed stx}"
      keys := keys.push key
      let nth := (keys.filter (· == key)).size
      found := found.push (if nth == 1 then key else s!"{key} #{nth}", stx)
  return found

/-- Whether any of the commands gives a declaration the `simp` attribute. -/
def hasSimpAttribute (commands : Array Syntax) : Bool :=
  commands.any fun command => (command.find? (·.isOfKind ``Parser.Attr.simp)).isSome

/-- The mentions of the given option names, as `set_option` writes them. -/
partial def optionMentions (names : List Name) (commands : Array Syntax)
    (found : Array Syntax := #[]) : Array Syntax :=
  commands.foldl (init := found) fun found stx =>
    let found := if stx.isIdent && names.contains stx.getId then found.push stx else found
    optionMentions names stx.getArgs found

end FrenTest.ProofLint
