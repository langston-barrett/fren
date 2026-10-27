-- keep-sorted start
import FrenCore.Diagnostic
import FrenCore.Lexical
-- keep-sorted end

/-!
# Global expectations, and the migration from `forall`

A global expectation (`Reqs/Lang/Global`) is written like a procedure: its
parameters, then a block of `assume`, `use`, `let`, `call`, `expect` and
`cover` members. The form that quantified over behaviours, `expect n:
forall (a: c) (m: M), E`, is an error (`F0416`), whose fix writes it as a
block: each binder over behaviours becomes a parameter for each of its
procedure's parameters and a call, each binder over values a parameter,
and the procedures' assumptions `assume` members, so that it means what it
did (`Reqs/Lang/Global#migration`). These are pure functions over plain
data, so that the requirements can state them (`lang::block_member`,
`lang::callee_fix`, `lang::migrated_param`).
-/

namespace Fren.Core

/-! ## Members -/

/-- A member of a global expectation's block, or a result in its
signature (`lang::BlockMember`). -/
inductive BlockMember where
  | result
  | «exists»
  | «let»
  /-- `out r := e`. -/
  | define
  | assume
  | ensure
  | expect
  | cover
  | call
  | use
  deriving Inhabited, BEq, DecidableEq, Repr

/-- Whether a global expectation's block accepts the member `m`, written
with `det` if `det` (`lang::block_member`): it constrains nothing and has
no outputs, so only assumptions, definitions, calls, claims and imports. -/
def blockMemberAccepted (m : BlockMember) (det : Bool) : Bool :=
  !det && match m with
    | .let | .assume | .expect | .cover | .call | .use => true
    | .result | .exists | .define | .ensure => false

/-- How a message names the member `m`. -/
def BlockMember.text : BlockMember → String
  | .result => "results"
  | .exists => "`exists` members"
  | .let => "`let` members"
  | .define => "`out` members"
  | .assume => "`assume` members"
  | .ensure => "`ensure` members"
  | .expect => "`expect` members"
  | .cover => "`cover` members"
  | .call => "calls"
  | .use => "`use` members"

/-- A member that a global expectation's block does not accept (`F0417`):
`m`, or with `det`, any member written with `det`. -/
def blockMemberMsg (m : BlockMember) (det : Bool) : Msg :=
  { code? := some "F0417"
    headline := if det then "global expectations have no `det` members" else s!"global expectations have no {m.text}"
    label? := some "not allowed in a global expectation"
    notes := #["note: a global expectation constrains nothing: its block has `assume`, `use`, `let`, `call`, \
      `expect` and `cover` members only",
      "help: state what the procedures guarantee in the procedures, and claim what follows with `expect`"] }

/-! ## The migration from `forall` -/

/-- What a text that the fix copies reads and declares (`lang::Copied`):
the identifiers written in it, each by its first component, but those
after a `.` or a `::`, which name fields, methods and the items of a path;
and those written with a `!`, which shadow what they name. -/
structure Copied where
  names : Array String := #[]
  bangs : Array String := #[]
  deriving Inhabited, BEq, Repr

instance : Append Copied := ⟨fun a b => { names := a.names ++ b.names, bangs := a.bangs ++ b.bangs }⟩

/-- The identifiers of `text` (`Copied`), as the lexer reads them
(`identEnd`), outside comments and string literals. Both front ends read
the texts that the fix copies with it, so that they agree on what each
reads. -/
def copiedOf (text : String) : Copied := Id.run do
  let src := text.toList.toArray
  let mut out : Copied := {}
  let mut i := 0
  while i < src.size do
    let c := src[i]!
    if c == '-' && src[i + 1]? == some '-' then
      while i < src.size && src[i]! != '\n' do i := i + 1
    else if c == '"' || (c == 'r' && (src[i + 1]? == some '"' || src[i + 1]? == some '#')) then
      -- A string literal, raw or not: its `#`s, then up to its closing quote.
      let mut hashes := 0
      if c == 'r' then
        i := i + 1
        while src[i]? == some '#' do hashes := hashes + 1; i := i + 1
      i := i + 1
      let mut closed := false
      while i < src.size && !closed do
        if src[i]! == '\\' && hashes == 0 then i := i + 2
        else if src[i]! == '"' && (List.range hashes).all (fun k => src[i + 1 + k]? == some '#') then
          i := i + 1 + hashes; closed := true
        else i := i + 1
    else if isIdStart c then
      let j := identEnd src i
      let tok := String.ofList (src.extract i j).toList
      let afterDot := i > 0 && src[i - 1]! == '.'
      let afterPath := i > 1 && src[i - 1]! == ':' && src[i - 2]! == ':'
      unless afterDot || afterPath do
        let root := (tok.splitOn ".").headD tok
        if root.endsWith "!" then out := { out with bangs := out.bangs.push (root.dropEnd 1).toString }
        else out := { out with names := out.names.push root }
      i := j
    else i := i + 1
  return out

/-- What the fix of an old global expectation needs to know of the
procedure of one of its binders over behaviours (`lang::Callee`): its
module; its parameters and its other variables and calls, by name; and
what its parameters' types, and its assumptions, read and declare. -/
structure Callee where
  module : String
  params : Array String
  others : Array String
  types : Copied
  assumes : Copied
  deriving Inhabited, BEq, Repr

/-- Why the fix cannot copy a procedure's text (`lang::CalleeFix`). -/
inductive CalleeFix where
  | fixable
  /-- It is in another module, where its names may mean something else. -/
  | otherModule
  /-- Its assumptions read a variable or call of its own other than a
  parameter, which the global expectation does not have, or declare a
  name that a parameter has, whose uses the renaming would change. -/
  | notClosed
  /-- Its types or assumptions read a name, other than its parameters,
  that a name the global expectation declares would hide. -/
  | captured
  deriving Inhabited, BEq, DecidableEq, Repr

/-- Whether the fix can copy the parameters' types and the assumptions of
`c`, with its `use` members, into a global expectation in `module` whose
block declares the values `block` (`lang::callee_fix`): what they read
then resolves there as it does in `c`, but for `c`'s parameters, which the
fix renames. -/
def calleeFix (module : String) (block : Array String) (c : Callee) : CalleeFix :=
  if c.module != module then .otherModule
  else if c.assumes.names.any c.others.contains || c.assumes.bangs.any c.params.contains then .notClosed
  else if (c.types.names ++ c.assumes.names).any (fun n => !c.params.contains n && block.contains n) then .captured
  else .fixable

/-- The name of the parameter that the fix declares for the parameter `x`
of a binder `w` (`lang::migrated_param`): `w_x`, so `a_ready?` for `a`'s
`ready?`. It names an assumption of `w`'s procedure the same way. -/
def migratedParam (w x : String) : String := w ++ "_" ++ x

/-- A binder of an old global expectation's leading `forall`: its name,
without its `!`, and the procedure it ranges over the behaviours of, if
any. -/
structure OldBinder where
  name : String
  callee? : Option Callee
  deriving Inhabited

/-- Why an old global expectation has no fix. -/
inductive NoFix where
  | callee (binder : String) (why : CalleeFix)
  /-- A name the fix would declare is declared twice, or hides a name in
  scope. -/
  | taken (name : String)
  /-- A quantifier in the body ranges over a procedure, which the fix
  would leave an error (`F0210`). -/
  | nested
  deriving Inhabited, BEq, Repr

/-- Whether the old global expectation `n` in `module`, with the binders
`bs` and its procedures' assumptions' names `assumeNames`, has a fix,
and if not, why (`Reqs/Lang/Global#migration`): each binder's procedure
must be fixable (`calleeFix`), against the values the block declares, and
each name it declares fresh (`lang::migrated_param`): declared once, and,
for a parameter, hiding nothing in scope (`hides`); and no quantifier in
its body may range over a procedure (`nested`), which is an error that the
fix would keep. -/
def globalFix (module n : String) (bs : Array OldBinder) (assumeNames : Array (Array String)) (hides : String → Bool)
    (nested : Bool := false) : Option NoFix := Id.run do
  if nested then return some .nested
  let params := bs.flatMap fun b => match b.callee? with
    | none => #[b.name]
    | some c => c.params.map (migratedParam b.name)
  let block := bs.map (·.name) ++ params
  for b in bs do
    if let some c := b.callee? then
      let why := calleeFix module block c
      if why != .fixable then return some (.callee b.name why)
  let assumed := (bs.zip assumeNames).flatMap fun (b, as) =>
    if b.callee?.isSome then as.map (migratedParam b.name) else #[]
  let fresh := bs.flatMap fun b => match b.callee? with
    | none => #[]
    | some c => c.params.map (migratedParam b.name)
  let declared := bs.map (·.name) ++ fresh ++ assumed ++ #[n]
  for x in declared, k in [0:declared.size] do
    if (declared.extract 0 k).contains x then return some (.taken x)
  if let some q := fresh.find? hides then return some (.taken q)
  return none

/-- The text of the global expectation that an old one migrates to: `head`
(`expect n`), the parameters `params`, each as written, on one line if it
fits in 100 characters and otherwise one to a line, then a block, indented
by `indent` plus 4, of the imports, the assumptions, the calls, and
`expect n: body`,
whose lines after its first keep their indentation relative to it. -/
def globalBlockText (indent : Nat) (head : String) (params : Array String) (uses assumes calls : Array String)
    (claim : String) : String :=
  let pad := String.ofList (List.replicate indent ' ')
  let inner := pad ++ "    "
  let flat := head ++ "(" ++ ", ".intercalate params.toList ++ ") {"
  let sig := if (pad ++ flat).length ≤ 100 || params.isEmpty then flat
    else head ++ "(\n" ++ String.join (params.toList.map (inner ++ · ++ ",\n")) ++ pad ++ ") {"
  -- Each member's lines after its first keep their indentation relative
  -- to it.
  let member (m : String) : String :=
    let ls := m.splitOn "\n"
    "\n".intercalate (ls.headD "" :: (ls.drop 1).map fun l => if l.trimAscii.isEmpty then "" else inner ++ l)
  let lines := (uses ++ assumes ++ calls ++ #[claim]).toList.map fun m => inner ++ member m ++ "\n"
  sig ++ "\n" ++ String.join lines ++ pad ++ "}"

/-- Why an old global expectation has no fix, as a note. -/
def NoFix.note : NoFix → String
  | .callee w .otherModule =>
    s!"note: the procedure of `{w}` is in another module, where the names of its types and assumptions may mean something else, so it has no fix"
  | .callee w .notClosed =>
    s!"note: an assumption of the procedure of `{w}` mentions a variable or call of its own other than a parameter, or declares a name that a parameter has, so it has no fix"
  | .callee w .captured =>
    s!"note: the types or assumptions of the procedure of `{w}` mention a name that a parameter or call of the fix would hide, so it has no fix"
  | .callee _ .fixable => "note: it has no fix"
  | .taken x => s!"note: the fix would declare `{x}`, which is taken, so it has no fix"
  | .nested => "note: a quantifier in its body ranges over a procedure, which the fix would leave an error, so it has no fix"

/-- An old global expectation, which quantified over behaviours with
`forall` (`F0416`): `fixed` is the block it migrates to, or why it has
none. -/
def oldGlobalMsg (fixed : Except NoFix String) : Msg :=
  { code? := some "F0416", headline := "global expectations are written with parameters and calls"
    label? := some "a binder over the behaviours of a procedure"
    notes := #["note: a global expectation takes parameters, and relates procedures by calling them, as in \
      `expect n(x: T) { call a := p(x) ... }`"]
      ++ (match fixed with | .error why => #[why.note] | .ok _ => #[])
    fixes := (match fixed with | .ok t => #[t] | .error _ => #[]).map fun replacement =>
      { msg := "write it with parameters and calls, assuming what its procedures assume", replacement } }

end Fren.Core
