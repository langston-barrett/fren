-- keep-sorted start
import FrenCore.Diagnostic
import FrenCore.Str
import Lean.Data.NameMap
-- keep-sorted end

/-!
# Names, modules and visibility

Fren's scoping rules (`Reqs/Modules`) as pure functions over plain data, shared
by the Lean-hosted front end and the standalone binary. Errors carry the index
of the offending path segment, so each front end can point at it.

Module paths are `Name`s (`check`, `a.b`); the root module is
`Name.anonymous`.

- An item is visible from the module that declares it, from that module's
  descendants, and, if it is `pub`, from everywhere.
- `use` paths are absolute unless they start with `self`.
- In expressions and types, the first segment of a path is looked up in the
  current module's scope: declared items and named imports win; otherwise a
  name opened by exactly one `use E::*` resolves to that variant.
-/

open Lean

namespace Fren.Core

inductive ItemKind where
  | moduleItem
  | enumItem
  /-- A record, declared with `struct`. -/
  | recordItem
  | constItem
  /-- An abstract type, declared with `type`. -/
  | typeItem
  /-- An uninterpreted function, declared with `fn`. -/
  | fnItem
  | compItem
  /-- A global expectation. -/
  | expectItem
  deriving Inhabited, BEq, Repr

/-- An item declared in a Fren module. -/
structure Item where
  kind : ItemKind
  /-- Full path, e.g. `check.Verdict`. -/
  path : Name
  isPub : Bool
  /-- The module that declares the item. -/
  owner : Name
  deriving Inhabited, Repr

structure EnumDef where
  path : Name
  /-- Variant names, in declaration order. -/
  variants : Array Name
  deriving Inhabited, Repr

/-- A `use` in some module, or in a component. -/
structure UseDef where
  /-- The module containing the `use`. -/
  module : Name
  /-- Its scope: the module, or the path of the component containing it. -/
  scope : Name := module
  /-- The full path of the imported item; for a glob, of the opened enum. -/
  target : Name
  glob : Bool
  deriving Inhabited, Repr

/-- Every item, enum and import declared so far. -/
structure Table where
  items : NameMap Item := {}
  enums : NameMap EnumDef := {}
  /-- `use`s, by scope. -/
  uses : NameMap (Array UseDef) := {}
  /-- The module of each component that has `use`s, by its path. -/
  scopes : NameMap Name := {}
  deriving Inhabited

def Table.addItem (t : Table) (i : Item) : Table := { t with items := t.items.insert i.path i }
def Table.addEnum (t : Table) (e : EnumDef) : Table := { t with enums := t.enums.insert e.path e }
def Table.addUse (t : Table) (u : UseDef) : Table :=
  { t with uses := t.uses.insert u.scope ((t.uses.getD u.scope #[]).push u)
           scopes := if u.scope == u.module then t.scopes else t.scopes.insert u.scope u.module }

/-- The module of a scope: a module's is itself, and a component's is the
module that declares it. -/
def Table.moduleOf (t : Table) (scope : Name) : Name := t.scopes.getD scope scope

/-- The `use`s in effect in a scope: its own, then its module's. -/
def Table.usesIn (t : Table) (scope : Name) : Array UseDef :=
  let m := t.moduleOf scope
  t.uses.getD scope #[] ++ (if m == scope then #[] else t.uses.getD m #[])

/-- Whether `scope` is a component's, whose imports shadow its module's
scope. -/
def Table.isComp (t : Table) (scope : Name) : Bool := t.moduleOf scope != scope

/-- Whether a `use` brings the name `n` into scope. -/
def UseDef.brings (u : UseDef) (t : Table) (n : Name) : Bool :=
  if u.glob then (t.enums.get? u.target).any (·.variants.contains n) else u.target.getString! == n.toString

inductive Resolved where
  | item (i : Item)
  | variant (e : EnumDef) (idx : Nat)
  deriving Inhabited

def Resolved.describe : Resolved → String
  | .item { kind := .moduleItem, .. } => "a module"
  | .item { kind := .enumItem, .. } => "an enum"
  | .item { kind := .recordItem, .. } => "a record"
  | .item { kind := .constItem, .. } => "a constant"
  | .item { kind := .typeItem, .. } => "an abstract type"
  | .item { kind := .fnItem, .. } => "a function"
  | .item { kind := .compItem, .. } => "a component"
  | .item { kind := .expectItem, .. } => "a global expectation"
  | .variant .. => "an enum variant"

/-- The full path of what a path resolved to. -/
def Resolved.path : Resolved → Name
  | .item i => i.path
  | .variant e idx => e.path ++ e.variants[idx]!

/-- A resolution error at segment `seg` of the path being resolved. The
message is built only when it is read: those that suggest a similar name
cost an edit distance per name in scope, and many callers only ask whether
a path resolves. -/
structure Error where
  seg : Nat
  msg : Thunk Msg
  deriving Inhabited

/-- `a::b`. -/
def showPath (n : Name) : String :=
  if n.isAnonymous then "the root module" else "::".intercalate (n.components.map (·.toString))

/-- `module `a::b``, or `the root module`. -/
def showModule (n : Name) : String :=
  if n.isAnonymous then "the root module" else s!"module `{showPath n}`"

/-- `a`, `b` and `c`. -/
def showNameList (ns : Array Name) : String :=
  match ns.toList.map (s!"`{·}`") with
  | [] => "(none)"
  | [a] => a
  | l => ", ".intercalate l.dropLast ++ " and " ++ l.getLast!

/-- The edit distance between two strings, counting a transposition of
adjacent characters as one edit (optimal string alignment). -/
def editDistance (a b : String) : Nat := Id.run do
  let a := a.toList.toArray
  let b := b.toList.toArray
  -- `d[i][j]`: the distance between the first `i` of `a` and `j` of `b`.
  let mut d : Array (Array Nat) := #[Array.range (b.size + 1)]
  for i in [1:a.size + 1] do
    let mut row := #[i]
    for j in [1:b.size + 1] do
      let cost := if a[i - 1]! == b[j - 1]! then 0 else 1
      let mut v := min (min (d[i - 1]![j]! + 1) (row[j - 1]! + 1)) (d[i - 1]![j - 1]! + cost)
      if i > 1 && j > 1 && a[i - 1]! == b[j - 2]! && a[i - 2]! == b[j - 1]! then
        v := min v (d[i - 2]![j - 2]! + 1)
      row := row.push v
    d := d.push row
  return d[a.size]![b.size]!

/-- The candidate closest to `s`, if one is close enough to be a likely
typo: at most a third of the name's length away, as rustc allows. A
candidate that differs only in a trailing `?` always counts, and so does one
of at least three characters that is a prefix of `s` or has `s` as a prefix. -/
def similarStr (s : String) (cands : Array String) : Option String :=
  let base (x : String) := (x.dropEndWhile (· == '?')).toString
  let scored := cands.filter (· != s) |>.map fun c =>
    let d := if base c == base s then 0 else editDistance s c
    (c, d)
  let byPrefix := cands.find? fun c => c != s && min c.length s.length ≥ 3 && (s.startsWith c || c.startsWith s)
  let best := scored.foldl (init := none) fun (acc : Option (String × Nat)) (c, d) =>
    match acc with
    | some (_, d') => if d < d' then some (c, d) else acc
    | none => some (c, d)
  match best with
  | some (c, d) => if d ≤ max 1 (s.length / 3) then some c else byPrefix
  | none => byPrefix

def similar (n : Name) (cands : Array Name) : Option Name :=
  (similarStr n.toString (cands.map (·.toString))).bind fun c => cands.find? (·.toString == c)

/-- A fix replacing `n` with a similar candidate, if there is one; `msg`
introduces it. -/
def similarFixes (msg : String) (n : Name) (cands : Array Name) : Array Fix :=
  match similar n cands with
  | some c => #[{ msg := s!"{msg}: `{c}`", replacement := c.toString }]
  | none => #[]

/-- `n` is not found in `where_`, where the names `cands` are. -/
def cannotFindMsg (n : Name) (where_ : String) (cands : Array Name) : Msg :=
  let msg : Msg := { code? := some "F0201", headline := s!"cannot find `{n}` in {where_}", label? := some s!"not found in {where_}"
                     fixes := similarFixes "a similar name exists" n cands }
  -- `x!` declares `x`, and its uses are written `x`.
  match n with
  | .str .anonymous s =>
    if s.endsWith "!" && s.length > 1 then
      let base := (s.dropEnd 1).toString
      { msg with
        notes := #["note: `!` is written only where a name is declared, to shadow another"]
        fixes := #[{ msg := s!"for the name `{base}`, remove the `!`", replacement := base }] }
    else msg
  | _ => msg

/-- `msg`, about the path segment `seg`, with the fix for `!=` first if it
cannot find a name `x!` that `=` directly follows: `x!=1` reads `x!` then
`=`, so `!=` is the likelier meaning, and removing the `!` alone would make
the comparison its opposite. -/
def withBangEqFix (msg : Msg) (seg : String) (beforeEq : Bool) : Msg :=
  if beforeEq && msg.code? == some "F0201" && seg.endsWith "!" && seg.length > 1 then
    { msg with fixes := #[{ msg := "for `!=`, write a space before the `!`", replacement := s!"{(seg.dropEnd 1).toString} !" }]
                          ++ msg.fixes }
  else msg

def rootItem : Item := { kind := .moduleItem, path := .anonymous, isPub := true, owner := .anonymous }

def Table.moduleItem (t : Table) (path : Name) : Item :=
  if path.isAnonymous then rootItem else t.items.getD path rootItem

def isDescendant (m ancestor : Name) : Bool := ancestor.isPrefixOf m

def visibleFrom (from_ : Name) (i : Item) : Bool := i.isPub || isDescendant from_ i.owner

/-- The item named `seg` declared directly in module `mod`. -/
def Table.declared? (t : Table) (mod seg : Name) : Option Item :=
  (t.items.get? (mod ++ seg)).filter (·.owner == mod)

/-- The names of the items declared in module `mod`. -/
def Table.membersOf (t : Table) (mod : Name) : Array Name :=
  t.items.foldl (init := #[]) fun acc _ i =>
    if i.owner == mod && i.path.getPrefix == mod && !i.path.isAnonymous then acc.push (Name.mkSimple i.path.getString!) else acc

/-- The names that the first segment of a path can be in the scope `mod`:
its module's items, its named imports, and the variants it opens. -/
def Table.scopeOf (t : Table) (mod : Name) : Array Name :=
  let uses := t.usesIn mod
  t.membersOf (t.moduleOf mod) ++ uses.foldl (init := #[]) fun acc u =>
    if u.glob then acc ++ ((t.enums.get? u.target).map (·.variants) |>.getD #[])
    else acc.push (Name.mkSimple u.target.getString!)

/-- What a path segment resolved to, as far as its members go
(`modules::Kind`). -/
inductive Parent where
  | module
  | enum
  | other
  deriving Inhabited, DecidableEq, Repr

/-- Whether a later path segment is accepted (`modules::member`): modules
have their visible items as members, enums their variants, and nothing else
has members. -/
def memberAccepted (parent : Parent) (found visible : Bool) : Bool :=
  found && match parent with
    | .module => visible
    | .enum => true
    | .other => false

/-- Resolves `segs[start:]` from `cur`, checking that each segment is visible
from module `from_` (`memberAccepted`). -/
def Table.walk (t : Table) (from_ : Name) (cur : Resolved) (segs : Array Name) (start : Nat) :
    Except Error Resolved := do
  let mut cur := cur
  for i in [start:segs.size] do
    let n := segs[i]!
    -- The member, whether it is visible, and the error if it is not accepted.
    let (parent, next?, visible, err) : Parent × Option Resolved × Bool × Thunk Msg := match cur with
      | .item i'@{ kind := .moduleItem, .. } =>
        match t.declared? i'.path n with
        | none => (.module, none, false, cannotFindMsg n (showModule i'.path) (t.membersOf i'.path))
        | some d => (.module, some (.item d), visibleFrom from_ d,
            { code? := some "F0202", headline := s!"`{n}` is private to {showModule d.owner}", label? := some "private"
              notes := #["note: an item is visible only in the module that declares it and that module's submodules",
                s!"help: declare it `pub` in {showModule d.owner}"] : Msg })
      | .item i'@{ kind := .enumItem, .. } =>
        match t.enums.get? i'.path >>= fun e => (e.variants.idxOf? n).map (e, ·) with
        | some (e, idx) => (.enum, some (.variant e idx), true, Msg.internal "no error")
        | none =>
          let vs := (t.enums.get? i'.path).map (·.variants) |>.getD #[]
          (.enum, none, true, {
            code? := some "F0203", headline := s!"no variant `{n}` in enum `{showPath i'.path}`"
            label? := some s!"not a variant of `{showPath i'.path}`"
            notes := #[s!"note: the variants of `{showPath i'.path}` are {showNameList vs}"]
            fixes := similarFixes "a variant with a similar name exists" n vs : Msg })
      | r => (.other, none, false, {
          code? := some "F0204", headline := s!"`{showPath r.path}` is {r.describe} and has no members"
          label? := some "nothing can follow this"
          notes := #["note: only modules (their items) and enums (their variants) have members"] : Msg })
    match next? with
    | some next => if memberAccepted parent true visible then cur := next else throw { seg := i, msg := err }
    | none => if memberAccepted parent false visible then pure () else throw { seg := i, msg := err }
  return cur

/-- The item or variant a named `use` brought into scope. -/
def Table.resolveTarget (t : Table) (target : Name) : Option Resolved :=
  match t.items.get? target with
  | some i => some (.item i)
  | none => do
    let e ← t.enums.get? target.getPrefix
    let idx ← e.variants.idxOf? (Name.mkSimple target.getString!)
    return .variant e idx

/-- Resolves a `use` path written in the scope `from_`: absolute, or
relative to its module if it starts with `self`. -/
def Table.resolveUse (t : Table) (from_ : Name) (segs : Array Name) : Except Error Resolved :=
  if segs[0]! == `self then t.walk from_ (.item (t.moduleItem (t.moduleOf from_))) segs 1
  else t.walk from_ (.item rootItem) segs 0

/-- How the first segment of a path resolves (`modules::resolve`), from
whether an item of that name is declared in, or imported by name into, the
module, and how many distinct variants of that name are opened by `*`. -/
inductive Resolution where
  | local
  | glob
  | ambiguous
  | unbound
  deriving Inhabited, BEq, DecidableEq, Repr

def resolution (isLocal : Bool) (nGlob : Nat) : Resolution :=
  if isLocal then .local
  else match nGlob with
    | 0 => .unbound
    | 1 => .glob
    | _ => .ambiguous

/-- Resolves a path in an expression or type in the scope `from_`, a
module or a component. `extra` are other names in scope, such as
variables, suggested if `segs[0]` is not found. -/
def Table.resolvePath (t : Table) (from_ : Name) (segs : Array Name) (extra : Array Name := #[]) :
    Except Error Resolved := do
  if segs[0]! == `self then
    return ← t.walk from_ (.item (t.moduleItem (t.moduleOf from_))) segs 1
  let n := segs[0]!
  -- A component's imports shadow its module's scope: they alone are its
  -- scope if they bring in `n`, and its module's scope is otherwise.
  let comp := t.isComp from_ && (t.uses.getD from_ #[]).any (·.brings t n)
  let uses := if comp then t.uses.getD from_ #[] else t.uses.getD (t.moduleOf from_) #[]
  let declared := if comp then none else t.declared? (t.moduleOf from_) n
  let local? ← match declared with
    | some d => pure (some (.item d))
    | none =>
      match uses.find? (fun u => !u.glob && u.target.getString! == n.toString) with
      | some u =>
        match t.resolveTarget u.target with
        | some r => pure (some r)
        | none => throw { seg := 0, msg := Msg.internal s!"dangling import `{u.target}`" }
      | none => pure none
  -- Distinct variants: opening the same enum twice is not ambiguous.
  let hits := uses.foldl (init := #[]) fun (acc : Array Resolved) u => Id.run do
    let some e := (if u.glob then t.enums.get? u.target else none) | return acc
    let some idx := e.variants.idxOf? n | return acc
    let r := Resolved.variant e idx
    return if acc.any (·.path == r.path) then acc else acc.push r
  let start ← match resolution local?.isSome hits.size, local? with
    | .local, some r => pure r
    | .glob, _ => pure hits[0]!
    | .unbound, _ => throw { seg := 0, msg := cannotFindMsg n "this scope" (t.scopeOf from_ ++ extra) }
    | _, _ =>
      let alts := ", ".intercalate (hits.toList.map fun r => s!"`{showPath r.path}`")
      throw { seg := 0, msg := {
        code? := some "F0205", headline := s!"`{n}` is ambiguous: it could be any of {alts}"
        label? := some "ambiguous name"
        notes := #[s!"note: each enum opened with `*` here has a variant `{n}`",
          s!"help: qualify it with its enum's name, e.g. `{hits[0]!.path.getPrefix.getString!}::{n}`"] : Msg } }
  t.walk from_ start segs 1

/-! ## Declarations -/

def builtinTypes : List Name := [`Bool, `Int, `Nat, `String]

/-- The name that `n` declares, and whether it is written with `!`: `x!`
declares `x`, and `ready?!` declares `ready?` (`Reqs/Lang/Components#shadowing`). -/
def declaredName (n : Name) : Name × Bool :=
  match n with
  | .str p s => if s.endsWith "!" then (.str p (s.dropEnd 1).toString, true) else (n, false)
  | _ => (n, false)

/-- A declaration of `n` is written `n!`, but hides nothing; `why` says why
it cannot. -/
def needlessBangMsg (n : Name) (why : String := s!"no `{n}` that a use could mean is in scope here") : Msg :=
  { code? := some "F0218", headline := s!"`{n}!` shadows nothing", label? := some "nothing to shadow"
    notes := #[s!"note: `!` marks a declaration that hides a name in scope, but {why}"]
    fixes := #[{ msg := "remove the `!`", replacement := n.toString }] }

/-- Lean's tokens, with `Fren` imported and `Fren.Lang` open, that are an
identifier followed by `!` (`Reqs/Lang/Lexical#identifiers`). Lean reads
each as a token of its own, so the Lean front end could not declare its
name with `!`; both front ends reject it. -/
def leanBangTokens : List String :=
  ["assert!", "debug_assert!", "f!", "m!", "panic!", "println!", "reportDbgIssue!", "reportEMatchIssue!",
   "reportIssue!", "s!", "unreachable!", "using!"]

/-- Fails if the declaration of `n`, written with `!` if `bang`, is one of
Lean's tokens. -/
def checkLeanToken (n : Name) (bang : Bool) : Except Msg Unit := do
  let text := n.toString ++ "!"
  if bang && leanBangTokens.contains text then
    throw { code? := some "F0219", headline := s!"`{text}` is a Lean token, so it cannot be declared"
            label? := some "a Lean token"
            notes := #[s!"note: Lean reads `{text}` as a token of its own, not as `{n}` followed by `!`",
              "help: rename the declaration"] }

/-- Fails if `n`, the name of a declaration that never shadows, such as an
item's or a constraint's, is written with `!`. -/
def checkNoBang (n : Name) : Except Msg Unit := do
  let (base, bang) := declaredName n
  checkLeanToken base bang
  if bang then
    throw (needlessBangMsg base "only variables, parameters, instances and binders shadow")

/-- A name other than a variable's ends in `?`; `what` is, e.g., `enum`. -/
def questionNameMsg (what : String) (n : Name) : Msg :=
  let base := (n.toString.dropEndWhile (· == '?')).toString
  { code? := some "F0211", headline := s!"{what} names cannot end in `?`", label? := some "ends in `?`"
    notes := #["note: only `Bool` variables end in `?`"]
    fixes := #[{ msg := s!"rename it to `{base}`", replacement := base }] }

/-- Checks the name of a module, enum, variant, comp or instance. -/
def checkItemName (what : String) (n : Name) : Except Msg Unit := do
  checkNoBang n
  if n.toString.endsWith "?" then
    throw (questionNameMsg what n)
  if builtinTypes.contains n then
    throw { code? := some "F0212", headline := s!"`{n}` is a built-in type and cannot be redefined"
            label? := some "built-in type", notes := #["note: the built-in types are `Bool`, `Int`, `Nat` and `String`"] }

/-- Checks a constant's name: like other items' but a `Bool`, it cannot end
in `?`. Its case is a lint (`non_upper_case_constants`). -/
def checkConstName (n : Name) : Except Msg Unit := do
  checkNoBang n
  if n.toString.endsWith "?" then throw (questionNameMsg "constant" n)

/-- Fails if `n` is already declared or imported by name in the module
`mod`, or imported by name into the component `mod`. -/
def Table.checkFresh (t : Table) (mod n : Name) : Except Msg Unit := do
  if let some prev := (if t.isComp mod then none else t.declared? mod n) then
    throw { code? := some "F0206"
            headline := s!"the name `{n}` is already defined in {showModule mod} (as {Resolved.describe (.item prev)})"
            label? := some s!"`{n}` redefined here"
            notes := #[s!"note: `{n}` must be defined only once in {showModule mod}"] }
  if let some u := (t.uses.getD mod #[]).find? (fun u => !u.glob && u.target.getString! == n.toString) then
    let where_ := if u.scope == u.module then showModule u.module else s!"component `{showPath u.scope}`"
    throw { code? := some "F0207", headline := s!"the name `{n}` is already imported into {where_}"
            label? := some s!"`{n}` defined or imported again here"
            notes := #[s!"note: a `use` and an item, or two `use`s, of the same name would make `{n}` ambiguous"] }

/-- The modules that `mod a::b` declares, given that segment `i` failed with
the message, or the new items to record. -/
def Table.declareModule (t : Table) (segs : Array Name) (isPub : Bool) :
    Except Error (Name × Array Item) := do
  let mut path := Name.anonymous
  let mut new := #[]
  for n in segs, i in [0:segs.size] do
    if let .error msg := checkItemName "module" n then throw { seg := i, msg }
    let p := path ++ n
    match t.items.get? p with
    | some { kind := .moduleItem, .. } => pure ()
    | some prev => throw { seg := i, msg := {
        code? := some "F0208", headline := s!"`{showPath p}` is {Resolved.describe (.item prev)}, not a module"
        label? := some "not a module", notes := #["note: modules and other items share one namespace"] : Msg } }
    | none =>
      new := new.push { kind := .moduleItem, path := p, isPub := isPub && i + 1 == segs.size, owner := path }
    path := p
  return (path, new)

/-- The import recorded by a `use` in module `mod`, or, with `scope`, in
the component of that path in `mod`. -/
def Table.declareUse (t : Table) (mod : Name) (segs : Array Name) (glob : Bool) (scope : Name := mod) :
    Except Error UseDef := do
  let t := { t with scopes := if scope == mod then t.scopes else t.scopes.insert scope mod }
  let r ← t.resolveUse scope segs
  if glob then
    let .item { kind := .enumItem, path, .. } := r
      | throw { seg := segs.size - 1, msg := {
          code? := some "F0209", headline := s!"only enums can be opened with `*`, but `{showPath r.path}` is {r.describe}"
          label? := some "not an enum"
          notes := #[s!"help: to import `{r.path.getString!}` itself, remove the `::*`"] : Msg } }
    return { module := mod, scope, target := path, glob := true }
  match t.checkFresh scope (Name.mkSimple r.path.getString!) with
  | .error msg => throw { seg := segs.size - 1, msg }
  | .ok () => return { module := mod, scope, target := r.path, glob := false }

/-- Checks a variable's name against its type (`lang::bool_naming`), given
whether the name ends in `?` (`q`): a name ends in `?` if and only if it is
a `Bool`. `isBool? = none` means no type was written. -/
def checkVarKind (n : Name) (q : Bool) (isBool? : Option Bool) : Except Msg Unit := do
  let base := (n.toString.dropEndWhile (· == '?')).toString
  match isBool? with
  | none =>
    unless q do
      throw { code? := some "F0301", headline := s!"missing type for `{n}`", label? := some "needs a type"
              notes := #["note: only variables whose names end in `?` can omit their type, which is `Bool`"]
              fixes := #[{ msg := "add a type", replacement := ": Int", after := true },
                { msg := s!"if it is a `Bool`, name it `{base}?`", replacement := s!"{base}?" }] }
  | some isBool =>
    if q && !isBool then
      throw { code? := some "F0302", headline := s!"`{n}` ends in `?` but is not a `Bool`", label? := some "ends in `?`"
              notes := #["note: a variable's name ends in `?` if and only if it is a `Bool`"]
              fixes := #[{ msg := s!"rename it to `{base}`", replacement := base }] }
    if !q && isBool then
      throw { code? := some "F0303", headline := s!"`Bool` variable `{n}` must end in `?`", label? := some "does not end in `?`"
              notes := #["note: a variable's name ends in `?` if and only if it is a `Bool`"]
              fixes := #[{ msg := s!"rename it to `{n}?`", replacement := s!"{n}?" }] }

/-- The text of an atomic name, as written: `toString` would escape a name
that is not a Lean identifier. -/
def nameText : Name → String
  | .str .anonymous s => s
  | n => n.toString

/-- `checkVarKind`, reading whether the name ends in `?` from its text. -/
def checkVarName (n : Name) (isBool? : Option Bool) : Except Msg Unit :=
  checkVarKind n (Fren.Str.endsWith (nameText n) "?") isBool?

/-! ## Shadowing (`Reqs/Lang/Components#shadowing`) -/

/-- Whether a declaration is accepted (`lang::shadowing`), from whether its
name hides a name in scope and whether it is written with `!`. -/
def shadowingAccepted (hides bang : Bool) : Bool := hides == bang

/-- What a declaration of `n` in the scope `scope` hides, if anything: the
innermost of `locals`, each with what it is (such as "the input"), or
else the value that the path `n` resolves to, a constant, a function or a
variant. Other items are never read where a variable can be, so nothing
hides them. -/
def Table.hidden? (t : Table) (scope : Name) (locals : Array (Name × String)) (n : Name) : Option String :=
  match locals.reverse.find? (·.1 == n) with
  | some (_, what) => some s!"{what} `{n}`"
  | none =>
    match t.resolvePath scope #[n] with
    | .ok (.item { kind := .constItem, path, .. }) => some s!"the constant `{showPath path}`"
    | .ok (.item { kind := .fnItem, path, .. }) => some s!"the function `{showPath path}`"
    | .ok r@(.variant ..) => some s!"the variant `{showPath r.path}`"
    | _ => none

/-- A declaration of `n` hides `hidden`, but has no `!`. -/
def implicitShadowMsg (n : Name) (hidden : String) : Msg :=
  let msg : Msg := { code? := some "F0217", headline := s!"`{n}` shadows {hidden}", label? := some "shadows without `!`"
                     notes := #[s!"note: shadowing is explicit: a declaration that hides a name in scope is written with `!`, as `{n}!`"]
                     fixes := #[{ msg := s!"to shadow {hidden}, write `{n}!`", replacement := s!"{n}!" }] }
  -- `s!` is a Lean token, which F0219 rejects as a declaration.
  if leanBangTokens.contains (n.toString ++ "!") then
    { msg with
      notes := #[s!"note: shadowing is explicit, but `{n}!` is a Lean token, which cannot be declared (F0219)",
        "help: rename the declaration"]
      fixes := #[] }
  else msg

/-- Checks a declaration of `n`, written with `!` if `bang`, given what it
hides (`lang::shadowing`). -/
def checkShadowing (n : Name) (hidden? : Option String) (bang : Bool) : Except Msg Unit :=
  if shadowingAccepted hidden?.isSome bang then pure ()
  else match hidden? with
    | some h => throw (implicitShadowMsg n h)
    | none => throw (needlessBangMsg n)

/-! ## Instances (`Reqs/Inst`) -/

/-- What a comp variable is. Instance variables are named `w.x`. -/
inductive Role where
  | input
  | output
  /-- An `in` of a direct instance. -/
  | instInput
  /-- A `pub out` of a direct instance. -/
  | instOutput
  /-- A private `out` of an instance, or a variable of an instance's own
  instances. -/
  | instHidden
  deriving Inhabited, DecidableEq, Repr

/-- Universally quantified in checks: everything the comp does not choose. -/
def Role.isUniversal : Role → Bool
  | .output => false
  | _ => true

/-- What a query's symbol is, for what the determinism check's second copy
renames (`check::Symbol`). -/
inductive Symbol where
  | input
  | instanceVariable
  | output
  | function
  deriving Inhabited, DecidableEq, Repr

def Symbol.ofRole : Role → Symbol
  | .input => .input
  | .output => .output
  | _ => .instanceVariable

/-- Whether the second copy renames it (`check::copied`): what the comp
does not get from its environment, but not functions, so that both copies
are under the same interpretation. -/
def Symbol.copied : Symbol → Bool
  | .instanceVariable | .output => true
  | .input | .function => false

/-- Where a variable is mentioned. -/
inductive Place where
  | assume
  | binding
  | prop
  /-- An argument of a function application in a requirement or
  expectation. -/
  | argument
  deriving Inhabited, DecidableEq, Repr

/-- The role, in a comp, of variable `x` of an instance, given its role in
the instantiated comp. -/
def Role.ofInst (inSub : Role) (isPub : Bool) : Role :=
  match inSub with
  | .input => .instInput
  | .output => if isPub then .instOutput else .instHidden
  | _ => .instHidden

/-- The names in scope that a `match` binder may hide, innermost last, each
with what it is (`Table.hidden?`): the variables of one segment, which are
parameters in a function's body (`inFn`), the instances, which are binders
in a global expectation (`inGlobal`), and the binders of enclosing arms. -/
def bindingLocals (vars : Array (Name × Role)) (insts binders : Array Name) (inFn : Bool) (inGlobal := false) :
    Array (Name × String) :=
  let what (r : Role) := if inFn then "the parameter" else if r == .input then "the input" else "the output"
  -- A global expectation's binders are its instances.
  let inst := if inGlobal then "the global expectation's binder" else "the instance"
  (vars.filter (·.1.isAtomic) |>.map fun (n, r) => (n, what r)) ++ insts.map (·, inst)
    ++ binders.map (·, "the binder")

def outInAssumeMsg (n : Name) : Msg :=
  { code? := some "F0401", headline := s!"assumptions may only mention `in` variables, but `{n}` is an `out`"
    label? := some "an `out`"
    notes := #["note: assumptions constrain the environment, not the system", "help: if it constrains the outputs, make it a `req`"] }

/-- `in x := e`: only outputs can be defined (`lang::modifiers`). -/
def inputDefinitionMsg : Msg :=
  { code? := some "F0114", headline := "an input cannot have a definition"
    label? := some "inputs are chosen by the environment"
    notes := #["note: only an output can be defined, as `out x: T := e`",
      "help: make it an output, or state what it equals in an `assume`"] }

/-- A definition that mentions its own output, through the definitions
`cycle`, each mentioning the next. -/
def cyclicDefinitionMsg (cycle : Array Name) : Msg :=
  let path := " -> ".intercalate ((cycle.push cycle[0]!).toList.map fun n => s!"`{n}`")
  { code? := some "F0411", headline := s!"the definition of `{cycle[0]!}` mentions itself: {path}"
    label? := some "a cyclic definition"
    notes := #["note: a defined output stands for its definition, so the definitions must not form a cycle",
      "help: define one of them in terms of the others' inputs, or constrain it with a `req` instead"] }

/-- A variable's mention, `msg`, was not allowed because the defined output
`d` mentions it. -/
def throughDefinition (d : Name) (msg : Msg) : Msg :=
  { msg with notes := #[s!"note: `{d}` is defined, and its definition mentions it"] ++ msg.notes }

/-- Whether variable `n` may be mentioned at `place` (`inst::mention`).
`earlier` says whether `n`'s instance is declared before the binding being
elaborated. -/
def checkMention (place : Place) (role : Role) (earlier : Bool) (n : Name) : Except Msg Unit := do
  let inst := n.getRoot
  match role, place with
  | .input, _ => pure ()
  | .output, .prop => pure ()
  | .output, .assume => throw (outInAssumeMsg n)
  | .output, .argument =>
    throw { code? := some "F0410"
            headline := s!"the arguments of a function may not mention an `out`, but `{n}` is one"
            label? := some "an `out`"
            notes := #["note: a function is applied only to values the system does not choose, so that the checks stay decidable",
              "help: apply the function to the inputs the output depends on, and relate the output to the result in a `req`"] }
  | .output, .binding =>
    throw { code? := some "F0402"
            headline := s!"bindings may only mention `in` variables and earlier instances, but `{n}` is an `out`"
            label? := some "an `out`"
            notes := #["note: an instance's inputs are fixed before the component chooses its outputs",
              "help: to connect an instance to an output, bind it to an `in` and add a `req` relating the two"] }
  | .instHidden, _ =>
    throw { code? := some "F0403", headline := s!"`{n}` is private to instance `{inst}`", label? := some "private"
            notes := #["note: only the `in`s and `pub out`s of an instance can be mentioned",
              "help: to mention it, declare it `pub out` in the instantiated component"] }
  | _, .prop | _, .argument => pure ()
  | _, .assume =>
    throw { code? := some "F0401"
            headline := s!"assumptions may only mention `in` variables, but `{n}` belongs to instance `{inst}`"
            label? := some s!"a variable of instance `{inst}`"
            notes := #["note: assumptions constrain the environment; instances are part of the system",
              "help: if it constrains the instance, make it a `req`"] }
  | _, .binding =>
    unless earlier do
      throw { code? := some "F0404", headline := s!"instance `{inst}` is not declared before this binding"
              label? := some "declared later, or this is its own binding"
              notes := #["note: bindings may only mention earlier instances, so that instances form no cycles",
                s!"help: declare `{inst}` before the instance whose binding mentions it"] }

/-- A dotted name that is not a variable of an instance. `vars` are the
names of the instance's visible variables. -/
def dottedNameMsg (n : Name) (insts : Array Name) (vars : Array Name := #[]) (inExpr := true) (afterPath := false) :
    Msg :=
  if insts.contains n.getRoot then
    let x := n.replacePrefix n.getRoot .anonymous
    let own := vars.filterMap fun v => if v.getRoot == n.getRoot then some (v.replacePrefix v.getRoot .anonymous) else none
    { code? := some "F0405"
      headline := s!"instance `{n.getRoot}` has no `in` or `pub out` named `{x}`"
      label? := some "unknown variable"
      notes := #[s!"note: the variables of `{n.getRoot}` are {showNameList own}"]
      fixes := (similar x own).toArray.map fun v =>
        { msg := s!"a variable with a similar name exists: `{n.getRoot}.{v}`", replacement := s!"{n.getRoot}.{v}" } }
  else
    let path := "::".intercalate (n.components.map (·.toString))
    { code? := some "F0111", headline := s!"`{n}` is not a single name"
      label? := some "`.` reads an instance's variable, or a value's field or method"
      notes := if inExpr then #[s!"note: `{n.getRoot}` is not an instance, a variable or a constant"]
        -- After a `::`, it may be a constant of another module read with `.`.
        else if afterPath then #[s!"help: to read a field or method of a constant of another module, bring it into \
          scope with `use` and write `{n}`"]
        else #[]
      fixes := #[{ msg := "if it is a path, separate its segments with `::`", replacement := path }] }

/-- Whether a name may be bound `n` times by an instance, given what it is
in the instantiated component (`inst::binding`): an `in` exactly once,
anything else never. -/
def bindingOk (target : Option Role) (n : Nat) : Bool :=
  if target == some .input then n == 1 else n == 0

/-- How many of `l` occur again later in it: as many as repeat an earlier one. -/
def repeatsOfList : List Name → Nat
  | [] => 0
  | a :: l => repeatsOfList l + if l.contains a then 1 else 0

/-- How many of `names` repeat an earlier one. -/
def repeatsOf (names : Array Name) : Nat := repeatsOfList names.toList

theorem repeatsOfList_eq_zero : ∀ {l : List Name}, repeatsOfList l = 0 ↔ l.Nodup
  | [] => by simp [repeatsOfList]
  | a :: l => by
    have ih : repeatsOfList l = 0 ↔ l.Nodup := repeatsOfList_eq_zero
    by_cases h : a ∈ l <;> simp [repeatsOfList, h, ih]

theorem repeatsOf_eq_zero {names : Array Name} : repeatsOf names = 0 ↔ names.toList.Nodup :=
  repeatsOfList_eq_zero

/-- The indexes of the names that repeat an earlier one, in order: where a
list of declarations has a name declared again (`lang::distinct_names`). -/
def repeatsAt (names : Array Name) : Array Nat := go [] names.toList 0
where
  go : List Name → List Name → Nat → Array Nat
    | _, [], _ => #[]
    | seen, n :: rest, i => if seen.contains n then #[i] ++ go seen rest (i + 1) else go (n :: seen) rest (i + 1)

theorem repeatsAt_go_eq_empty : ∀ {seen l : List Name} {i : Nat},
    repeatsAt.go seen l i = #[] ↔ (∀ x ∈ l, x ∉ seen) ∧ l.Nodup
  | _, [], _ => by simp [repeatsAt.go]
  | seen, a :: l, i => by
    have ih := @repeatsAt_go_eq_empty (a :: seen) l (i + 1)
    by_cases h : a ∈ seen
    · simp [repeatsAt.go, h]
    · simp [repeatsAt.go, h, ih]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨fun x hx => (h1 x hx).2, fun hm => (h1 a hm).1 rfl, h2⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨fun x hx => ⟨fun e => h2 (e ▸ hx), h1 x hx⟩, h3⟩

theorem repeatsAt_eq_empty {names : Array Name} : repeatsAt names = #[] ↔ names.toList.Nodup := by
  simp [repeatsAt, repeatsAt_go_eq_empty]

/-- The names of the inputs among `vars`. -/
def inputsOf (vars : Array (Name × Role)) : Array Name :=
  vars.filterMap fun (n, r) => if r == .input then some n else none

/-- Whether an instance's bindings `bound` are accepted, where `vars` are the
instantiated component's variables (name and role) (`inst::bindings`):
it binds only inputs, every input, and nothing twice. -/
def bindingsAccepted (vars : Array (Name × Role)) (bound : Array Name) : Bool :=
  let target (n : Name) := (vars.find? (·.1 == n)).map (·.2)
  bound.all (target · == some .input) && (inputsOf vars).all bound.contains && repeatsOf bound == 0

/-- Checks the names bound by an instance of `comp` (`bindingsAccepted`),
explaining the first problem. -/
def checkBindings (comp : Name) (vars : Array (Name × Role)) (bound : Array Name) :
    Except (Option Nat × Msg) Unit := do
  if bindingsAccepted vars bound then return
  let c := showPath comp
  let inputs := inputsOf vars
  let again := repeatsAt bound
  for b in bound, i in [0:bound.size] do
    match vars.find? (·.1 == b) with
    | some (_, .input) =>
      if again.contains i then
        throw (some i, { code? := some "F0406", headline := s!"input `{b}` is bound multiple times"
                         label? := some "bound again here", notes := #["note: each input of an instance is bound exactly once"] })
    | some (_, .output) =>
      throw (some i, { code? := some "F0407", headline := s!"`{b}` is an `out` of `{c}`", label? := some "an `out`"
                       notes := #["note: only `in`s are bound; an instance chooses its own outputs",
                         s!"help: to constrain it, add a `req` that mentions `w.{b}`, where `w` is the instance"] })
    | _ =>
      throw (some i, { code? := some "F0408", headline := s!"`{c}` has no input `{b}`", label? := some "unknown input"
                       notes := #[s!"note: the inputs of `{c}` are {showNameList inputs}"]
                       fixes := similarFixes "an input with a similar name exists" b inputs })
  let missing := vars.filter fun (n, r) => r == .input && !bound.contains n
  unless missing.isEmpty do
    let names := ", ".intercalate (missing.toList.map fun (n, _) => s!"`{n}`")
    let it := if missing.size == 1 then "it" else "them"
    throw (none, { code? := some "F0409", headline := s!"missing input{if missing.size == 1 then "" else "s"} {names} of `{c}`"
                   label? := some s!"does not bind {names}"
                   notes := #["note: an instance binds every input of its component",
                     s!"help: bind {it}, e.g. `{missing[0]!.1} := ...`, or `{missing[0]!.1}` to bind it to a variable of the same name"] })
  throw (none, Msg.internal s!"the bindings of `{c}` are rejected without a reason")

/-- What a path resolved to is the wrong kind of thing. -/
def wrongKindMsg (expected : String) (r : Resolved) (note : Option String := none) : Msg :=
  { code? := some "F0210", headline := s!"expected {expected}, but `{showPath r.path}` is {r.describe}"
    label? := some s!"not {expected}", notes := note.toArray }

def notACompMsg (r : Resolved) : Msg := wrongKindMsg "a component" r

def notAValueMsg (r : Resolved) : Msg :=
  wrongKindMsg "a value" r <| match r with
    | .item { kind := .enumItem, path, .. } => some s!"help: to mean one of its variants, write `{path.getString!}::Variant`"
    | _ => none

def notATypeMsg (r : Resolved) : Msg :=
  wrongKindMsg "a type" r "note: types are `Bool`, `Int`, `Nat`, enums, records and abstract types"

def notAFunctionMsg (r : Resolved) : Msg := wrongKindMsg "a function" r

/-- A variable applied as a function. -/
def varNotAFunctionMsg (n : Name) : Msg :=
  { code? := some "F0210", headline := s!"expected a function, but `{n}` is a variable", label? := some "not a function" }

/-- A function mentioned without being applied. -/
def unappliedMsg (n : Name) : Msg :=
  { code? := some "F0210", headline := s!"function `{showPath n}` must be applied to arguments", label? := some "not applied"
    notes := #["note: a function is mentioned only by applying it, as in `f(x)`"] }

/-- A variant with a payload mentioned without being applied. -/
def unappliedVariantMsg (n : Name) (nPayload : Nat) : Msg :=
  { code? := some "F0210", headline := s!"variant `{showPath n}` must be applied to its payload", label? := some "not applied"
    notes := #[s!"note: `{showPath n}` carries {if nPayload == 1 then "a value" else s!"{nPayload} values"}, \
      as in `{showPath n}({", ".intercalate (List.replicate nPayload "x")})`"] }

def arityMsg (f : Name) (nParams nArgs : Nat) (what := "argument") : Msg :=
  let args (k : Nat) := if k == 1 then s!"1 {what}" else s!"{k} {what}s"
  { code? := some "F0308"
    headline := s!"`{showPath f}` takes {args nParams}, but {nArgs} {if nArgs == 1 then "was" else "were"} given"
    label? := some s!"expected {args nParams}" }

/-- A variant without a payload applied to arguments. -/
def noPayloadMsg (n : Name) : Msg :=
  { code? := some "F0308", headline := s!"variant `{showPath n}` has no payload", label? := some "no payload"
    notes := #[s!"help: write it without parentheses: `{showPath n}`"] }

/-- Whether a variant whose payload has `payload` values is mentioned
rightly: applied to values exactly when it has a payload
(`lang::variant_mention`). -/
def variantMentionAccepted (payload : Nat) (applied : Bool) : Bool := applied == decide (payload > 0)

/-- What is wrong with mentioning the variant `v`, whose payload has
`payload` values, `applied` or not, if anything. -/
def variantMentionMsg? (v : Name) (payload : Nat) (applied : Bool) : Option Msg :=
  if variantMentionAccepted payload applied then none
  else if applied then some (noPayloadMsg v) else some (unappliedVariantMsg v payload)

/-- Whether a constant is accepted, from whether its type is abstract and
whether its value applies an uninterpreted function (`lang::constant`). -/
def constantAccepted (abstract applies : Bool) : Bool := !abstract && !applies

def unknownConstantMsg (abstract : Bool) : Msg :=
  { code? := some "F0309"
    headline := if abstract then "a constant cannot have an abstract type" else "a constant's value cannot apply an uninterpreted function"
    label? := some (if abstract then "an abstract type" else "applies an uninterpreted function")
    notes := #[if abstract then "note: an abstract type has no literals, so no value of it can be written"
      else "note: an uninterpreted function's value is unknown, so the constant would have no fixed value",
      "help: make it an input of the components that use it"] }

/-! ## Defined functions -/

/-- Whether a function's parameters are accepted, from whether it is
defined, its number of parameters, and how many are written with a name
(`lang::function_params`). -/
def functionParamsAccepted (defined : Bool) (nParams nNamed : Nat) : Bool :=
  nNamed == if defined then nParams else 0

/-- A parameter named in an uninterpreted function, or unnamed in a
defined one (`lang::function_params`). -/
def functionParamsMsg (f : Name) (defined : Bool) : Msg :=
  if defined then
    { code? := some "F0330", headline := s!"the parameters of defined function `{showPath f}` must be named"
      label? := some "no name"
      notes := #["note: the body mentions its parameters by name",
        "help: write the parameter as `x: T`, or `x?` for a `Bool`"] }
  else
    { code? := some "F0330", headline := s!"the parameters of uninterpreted function `{showPath f}` have no names"
      label? := some "named"
      notes := #["note: only a defined function's body mentions its parameters",
        "help: write only the parameter's type, or give the function a body with `:= ...`"] }

/-- Whether a defined function's body is accepted, from whether it has the
result type and whether it applies the function itself or an uninterpreted
function (`lang::function_body`). -/
def functionBodyAccepted (typed appliesSelf appliesUninterpreted : Bool) : Bool :=
  typed && !appliesSelf && !appliesUninterpreted

/-- A defined function's body applies the function itself. -/
def recursiveMsg (f : Name) : Msg :=
  { code? := some "F0331", headline := s!"defined function `{showPath f}` applies itself"
    label? := some "applied in its own body"
    notes := #["note: defined functions are not recursive, so that every application has a value",
      "help: use an earlier defined function, or a `match` on the argument"] }

/-- A defined function's body applies an uninterpreted function. -/
def appliesUninterpretedMsg (g : Name) : Msg :=
  { code? := some "F0331", headline := s!"a defined function's body cannot apply uninterpreted function `{showPath g}`"
    label? := some "uninterpreted"
    notes := #["note: a defined function's values are fully known, from those of its arguments",
      "help: make the value a parameter, and apply the uninterpreted function where the defined one is applied"] }

/-- Whether an argument is accepted, from whether its function is defined
and whether it mentions an output of the enclosing component
(`lang::argument`). -/
def argumentAccepted (defined mentionsOutput : Bool) : Bool := defined || !mentionsOutput

/-- Whether `a * b` is linear, from whether each operand mentions a variable
or an uninterpreted function (`lang::linear_product`). -/
def productAccepted (a b : Bool) : Bool := !(a && b)

def nonlinearMsg : Msg :=
  { code? := some "F0307", headline := "nonlinear arithmetic is not supported", label? := some "both sides mention variables or uninterpreted functions"
    notes := #["note: the solver decides only linear integer arithmetic",
      "help: one side of `*` must mention no variable and no uninterpreted function, such as `2 * x` or `(MAX - MIN) * x`"] }

/-- The form of a divisor, without its `-` and parentheses
(`lang::divisor`): an integer literal, a constant whose value is an integer
constant expression, a constant whose value is not, or any other
expression. -/
inductive DivisorForm where
  | literal
  | knownConstant
  | unknownConstant
  | other
  deriving Inhabited, BEq, DecidableEq, Repr

/-- Whether a divisor of `div` or `mod` is accepted, from its form and its
value, which is known for a literal or a known constant
(`lang::divisor`). -/
def divisorAccepted : DivisorForm → Int → Bool
  | .literal, value | .knownConstant, value => value != 0
  | .unknownConstant, _ | .other, _ => false

/-- The divisor of `op`, `div` or `mod`, which is not an integer literal or
a constant. -/
def divisorFormMsg (op : String) : Msg :=
  { code? := some "F0336", headline := s!"the divisor of `{op}` must be an integer literal or a constant"
    label? := some "not a literal or a constant"
    notes := #["note: the solver decides only linear integer arithmetic, which divides only by constants",
      s!"help: divide by a literal or a constant, such as `x {op} 2`, or declare a constant for the divisor"] }

/-- The divisor of `op`, the constant `c`, whose value is not an integer
constant expression. -/
def divisorUnknownMsg (op : String) (c : Name) : Msg :=
  { code? := some "F0336", headline := s!"the value of `{showPath c}`, the divisor of `{op}`, is not known when the spec is read"
    label? := some "value not known"
    notes := #["note: a constant divisor's value is built from integer literals and such constants by `+`, `-`, `*`, `div`, `mod`, `abs`, `min` and `max`",
      s!"help: give `{showPath c}` such a value, or divide by a literal"] }

/-- The divisor of `op`, `div` or `mod`, is `0`. -/
def divisorZeroMsg (op : String) : Msg :=
  { code? := some "F0337", headline := s!"`{op}` by zero", label? := some "the divisor is `0`"
    notes := #["note: SMT-LIB leaves division by zero unspecified, and Lean makes it `0`, so Fren rejects it"] }

/-- Checks the divisor of `op` (`lang::divisor`): of the form `form`, with
the value `value` if it is a literal or a known constant, and, for a
constant, its path `c`. -/
def checkDivisor (op : String) (form : DivisorForm) (value : Int) (c : Name := .anonymous) : Except Msg Unit :=
  if divisorAccepted form value then .ok () else match form with
    | .literal | .knownConstant => .error (divisorZeroMsg op)
    | .unknownConstant => .error (divisorUnknownMsg op c)
    | .other => .error (divisorFormMsg op)

/-- `a op b`, for an operator of an integer constant expression: `+`, `-`,
`*`, and Euclidean `div` and `mod`, which are not defined by `0`. -/
def intConstOp? (op : String) (a b : Int) : Option Int :=
  match op with
  | "+" => some (a + b)
  | "-" => some (a - b)
  | "*" => some (a * b)
  | "div" => if b == 0 then none else some (Int.ediv a b)
  | "mod" => if b == 0 then none else some (Int.emod a b)
  | _ => none

/-- `x.m(args)`, for a method of an integer constant expression: `abs`,
`min` and `max`. -/
def intConstMethod? (m : String) (x : Int) (args : List Int) : Option Int :=
  match m, args with
  | "abs", [] => some (if x < 0 then -x else x)
  | "min", [y] => some (if x ≤ y then x else y)
  | "max", [y] => some (if x ≥ y then x else y)
  | _, _ => none

def dupMemberMsg (n : Name) : Msg :=
  { code? := some "F0213", headline := s!"`{n}` is defined multiple times in this component", label? := some "defined again here"
    notes := #["note: the variables, instances and constraints of a component share one namespace"] }

def dupParamMsg (n : Name) : Msg :=
  { code? := some "F0213", headline := s!"parameter `{n}` is defined multiple times", label? := some "defined again here" }

def dupBinderMsg (n : Name) : Msg :=
  { code? := some "F0213", headline := s!"`{n}` is bound multiple times in this expectation", label? := some "bound again here" }

def dupVariantMsg (n : Name) : Msg :=
  { code? := some "F0213", headline := s!"variant `{n}` is defined multiple times", label? := some "defined again here" }

def dupFieldMsg (n : Name) : Msg :=
  { code? := some "F0213", headline := s!"field `{n}` is defined multiple times", label? := some "defined again here" }

/-- A binder `n` in an alternative of an or-pattern. -/
def orBinderMsg (n : Name) : Msg :=
  { code? := some "F0333", headline := s!"an or-pattern cannot bind `{n}`", label? := some "binds a name"
    notes := #["note: when another alternative matches, the name would have no value"]
    fixes := #[{ msg := "ignore the value", replacement := "_" }] }

def dupPatternBinderMsg (n : Name) : Msg :=
  { code? := some "F0213", headline := s!"`{n}` is bound multiple times in this pattern", label? := some "bound again here" }

/-! ## Records, payloads and matches -/

/-- Whether a field's or payload's type is accepted, from whether an
abstract type occurs within it, whether it is the item being declared or
has it as a set's element type, and whether it is a variant's payload
(`lang::field_type`). -/
def fieldTypeAccepted (abstract own ownInSet payload : Bool) : Bool := !abstract && !ownInSet && (payload || !own)

def recursiveSetMsg (n : Name) : Msg :=
  { code? := some "F0327", headline := s!"`{showPath n}` cannot be an element type within itself"
    label? := some "recursive through a set"
    notes := #["note: a type cannot be built from sets, relations or sequences of itself",
      "help: give the variant a payload of the type itself, or of an enum that lists the cases"] }

/-- A field or payload whose type is the abstract type `ty`, or has it
`within` as a set's element type. -/
def abstractFieldMsg (ty : Name) (payload : Bool) (within := false) : Msg :=
  let what := if payload then "payload" else "field"
  { code? := some "F0310"
    headline := if within then s!"a {what}'s type cannot have the abstract type `{showPath ty}` within it"
      else s!"a {what} cannot have the abstract type `{showPath ty}`"
    label? := some "an abstract type"
    notes := #["note: the values of records and enums are fully described by the spec",
      "help: make the value an input of the components that use it, or a function of the record"] }

def recursiveRecordMsg (n : Name) : Msg :=
  { code? := some "F0311", headline := s!"record `{n}` has a field of its own type", label? := some "recursive field"
    notes := #["note: each value would contain another without end, so the record would have no values",
      "help: use an enum with a variant whose payload does not contain it, e.g. `enum List { Nil, Cons(Int, List) }`"] }

/-- Whether an enumeration has values, from its number of variants and of
those with a payload of its own type (`lang::well_founded`). -/
def wellFounded (nVariants nRecursive : Nat) : Bool := nRecursive < nVariants

def illFoundedMsg (n : Name) : Msg :=
  { code? := some "F0312", headline := s!"enum `{n}` has no values", label? := some "every variant contains itself"
    notes := #[s!"note: every variant of `{n}` has a payload of type `{n}`, so no value can be built",
      "help: add a variant whose payload does not contain it, e.g. `Nil`"] }

/-- Whether a variable's type is accepted, from whether it is an output,
whether its type is unbounded, and whether it is defined
(`lang::variable_type`). -/
def variableTypeAccepted (output unbounded defined : Bool) : Bool := !(output && unbounded && !defined)

def unboundedOutputMsg (n : Name) (ty : String) : Msg :=
  { code? := some "F0313", headline := s!"output `{n}` has the unbounded type `{ty}`"
    label? := some "an unbounded type"
    notes := #["note: the realizability check asks whether outputs exist, which the solver cannot decide for values of unbounded size",
      "help: define it, as `out x: T := e`, make it an input, or describe it by outputs of bounded types"] }

/-- Whether a record literal may give the name `n` times, from whether it
is a field of the record (`lang::field_init`). -/
def fieldInitOk (field : Bool) (n : Nat) : Bool := if field then n == 1 else n == 0

/-- Whether a record literal with the fields `fields` that gives `given` is
accepted (`lang::record_literal`): it gives every field, and nothing
else, once. -/
def recordLiteralAccepted (fields given : Array Name) : Bool :=
  given.all fields.contains && fields.all given.contains && repeatsOf given == 0

/-- Checks the fields `given` by a literal of the record `r` with the fields
`fields`, explaining the first problem, at the index of a given field or
at the literal. -/
def checkFieldInits (r : Name) (fields given : Array Name) : Except (Option Nat × Msg) Unit := do
  if recordLiteralAccepted fields given then return
  let rs := showPath r
  let again := repeatsAt given
  for g in given, i in [0:given.size] do
    unless fieldInitOk (fields.contains g) (given.count g) do
      if fields.contains g then
        if again.contains i then
          throw (some i, { code? := some "F0314", headline := s!"field `{g}` is given multiple times", label? := some "given again here"
                           notes := #["note: a record literal gives each field exactly once"] })
      else
        throw (some i, { code? := some "F0314", headline := s!"record `{rs}` has no field `{g}`", label? := some "unknown field"
                         notes := #[s!"note: the fields of `{rs}` are {showNameList fields}"]
                         fixes := similarFixes "a field with a similar name exists" g fields })
  let missing := fields.filter (!given.contains ·)
  unless missing.isEmpty do
    let names := ", ".intercalate (missing.toList.map fun n => s!"`{n}`")
    throw (none, { code? := some "F0314", headline := s!"missing field{if missing.size == 1 then "" else "s"} {names} of `{rs}`"
                   label? := some s!"does not give {names}"
                   notes := #["note: a record literal gives every field of the record"] })
  throw (none, Msg.internal s!"a literal of `{rs}` is rejected, but no field explains why")

/-- A field read of something that is not a record with that field. -/
def noFieldMsg (field : Name) (ty : String) (fields : Array Name) : Msg :=
  { code? := some "F0315"
    headline := if fields.isEmpty then s!"`{ty}` is not a record, so it has no field `{field}`"
      else s!"record `{ty}` has no field `{field}`"
    label? := some "unknown field"
    notes := if fields.isEmpty then #["note: only records have fields"] else #[s!"note: the fields of `{ty}` are {showNameList fields}"]
    fixes := (similar field fields).toArray.map fun f => { msg := s!"a field with a similar name exists: `{f}`", replacement := f.toString } }

def scrutineeMsg (ty : String) : Msg :=
  { code? := some "F0316", headline := s!"cannot match on `{ty}`", label? := some "not an enum"
    notes := #["note: `match` reads which variant a value of an enum is",
      "help: for other types, use `if ... then ... else`"] }

/-- An arm, or an alternative of a pattern (`alternative`), that never
matches, and `why`. -/
def unreachableMsg (alternative : Bool) (why : String) : Msg :=
  { code? := some "F0318", headline := s!"unreachable {if alternative then "pattern" else "arm"}"
    label? := some "never matches", notes := #[why, "help: remove it"] }

/-- Whether a `match`'s arms are accepted, from the number of variants of
its enumeration, the number with an arm, whether there is a `_` arm, the
arms for an already covered variant, and the arms after `_`
(`lang::match_arms`). -/
def matchArmsAccepted (nVariants nCovered : Nat) (wildcard : Bool) (nRepeated nAfter : Nat) : Bool :=
  nRepeated == 0 && nAfter == 0 && (if wildcard then nCovered < nVariants else nCovered == nVariants)

/-- Checks the arms of a `match` on the enumeration `e` with the variants
`variants`, where each arm's pattern is the variants of its alternatives or
`none` for `_`, explaining the first problem: at an arm and, for a repeated
variant, its alternative, or at the `match`. -/
def checkArms (e : Name) (variants : Array Name) (arms : Array (Option (Array Name))) :
    Except (Option (Nat × Option Nat) × Msg) Unit := do
  -- Each alternative: its arm, its position in the arm, and its variant.
  let alts := (Array.range arms.size).flatMap fun i => match arms[i]! with
    | some vs => vs.mapIdx fun j v => (i, j, v)
    | none => #[]
  let covered := variants.filter fun v => alts.any (·.2.2 == v)
  let wildcard := arms.contains none
  let repeated := (Array.range alts.size).filter fun k => alts[:k].toArray.any (·.2.2 == alts[k]!.2.2)
  let firstWild := arms.idxOf? none
  let after := (Array.range arms.size).filter fun i => firstWild.any (· < i)
  if matchArmsAccepted variants.size covered.size wildcard repeated.size after.size then return
  let unreachable (at_ : Nat × Option Nat) (why : String) : Except (Option (Nat × Option Nat) × Msg) Unit :=
    throw (some at_, unreachableMsg at_.2.isSome why)
  -- The first problem, by arm and then by alternative.
  let firstRepeat := (repeated[0]?.map fun k => alts[k]!).filter fun (i, _) => after[0]?.all (i < ·)
  if let some (i, j, v) := firstRepeat then
    -- An arm of one alternative is unreachable as a whole.
    if arms[i]!.map (·.size) == some 1 then unreachable (i, none) s!"note: an earlier arm matches `{showPath (e ++ v)}`"
    unreachable (i, some j) s!"note: an earlier pattern matches `{showPath (e ++ v)}`"
  if let some a := after[0]? then unreachable (a, none) "note: an earlier `_` arm matches every value"
  if let some i := firstWild then
    unreachable (i, none) s!"note: every variant of `{showPath e}` has an arm before it"
  let missing := variants.filter (!covered.contains ·)
  let names := ", ".intercalate (missing.toList.map fun v => s!"`{showPath (e ++ v)}`")
  throw (none, { code? := some "F0317", headline := s!"non-exhaustive match: {names} not covered"
                 label? := some s!"{names} not covered"
                 notes := #["note: a `match` has an arm for every variant, or a last arm `_`"] })

/-- `e is P`, where `e` is not of an enumeration
(`Reqs/Lang/Expressions#pattern-tests`). -/
def isScrutineeMsg (ty : String) : Msg :=
  { code? := some "F0335", headline := s!"cannot test `{ty}` against a pattern", label? := some "not an enum"
    notes := #["note: `is` tests which variant a value of an enum is",
      "help: for other types, compare with `=` or `in`"] }

/-- A binder of the pattern of `e is P` that names its value. -/
def isBinderMsg (n : Name) : Msg :=
  { code? := some "F0334", headline := s!"a pattern test cannot bind `{n}`", label? := some "binds a name"
    notes := #["note: a pattern test has no body in which to mention the name",
      "help: to read the payload, write a `match`"]
    fixes := #[{ msg := "ignore the value", replacement := "_" }] }

/-- Whether the pattern of `e is P` is accepted, from the number of its
binders that are not `_` and of its alternatives naming a variant that an
earlier one names (`lang::pattern_test`). -/
def patternTestAccepted (nBound nRepeated : Nat) : Bool := nBound == 0 && nRepeated == 0

/-- Checks the pattern of `e is P` on the enumeration `e`, where each
alternative is its variant and the names of its binders, `_` included,
explaining the first problem: at an alternative and, for a binder, its
position. `_`, which has no alternatives, is accepted, and so is a pattern
that matches every value. -/
def checkPatternTest (e : Name) (alts : Array (Name × Array Name)) : Except ((Nat × Option Nat) × Msg) Unit := do
  let bound := alts.flatMap fun (_, bs) => bs.filter (· != `_)
  let repeated := (Array.range alts.size).filter fun k => alts[:k].toArray.any (·.1 == alts[k]!.1)
  if patternTestAccepted bound.size repeated.size then return
  -- The first problem, by alternative.
  for (v, bs) in alts, j in [0:alts.size] do
    if let some k := bs.findIdx? (· != `_) then throw ((j, some k), isBinderMsg bs[k]!)
    if repeated.contains j then
      throw ((j, none), unreachableMsg true s!"note: an earlier pattern matches `{showPath (e ++ v)}`")
  throw ((0, none), Msg.internal "a pattern test is rejected, but no alternative explains why")

/-- A pattern that names something other than a variant of the
scrutinee's enumeration. -/
def notAVariantOfMsg (e : Name) (what : String) : Msg :=
  { code? := some "F0319", headline := s!"expected a variant of `{showPath e}`, but this is {what}"
    label? := some s!"not a variant of `{showPath e}`"
    notes := #[s!"note: the scrutinee is a `{showPath e}`"] }

def armTypesMsg (a b : String) : Msg :=
  { code? := some "F0320", headline := s!"the arms of `match` have different types: `{a}` and `{b}`"
    label? := some "arms of different types"
    notes := #["note: a `match` has the value of one of its arms, so all must have the same type"] }

def propNameMsg (n : Name) : Msg := questionNameMsg "constraint" n

/-! ## Strings and methods (`Reqs/Lang/Expressions#methods`) -/

/-- A character beyond `U+2FFFF` in a literal (`lang::string_char`). -/
def stringCharMsg (c : Char) : Msg :=
  { code? := some "F0116", headline := s!"the character U+{(String.ofList (Nat.toDigits 16 c.toNat)).toUpper} is beyond U+2FFFF, the last character of a `String`"
    label? := some "beyond U+2FFFF"
    notes := #["note: the solver's strings have the characters from 0 to U+2FFFF"] }

/-- Checks that each character of a literal is a `String`'s. -/
def checkStringChars (s : String) : Except Msg Unit := do
  for c in s.toList do
    unless stringCharAccepted c.toNat do throw (stringCharMsg c)

/-- `{}` where nothing gives it a type (`Reqs/Lang/Types#checking-and-synthesis`). -/
def emptySetTypeMsg : Msg :=
  { code? := some "F0324", headline := "the type of `{}` cannot be known here", label? := some "a set of what?"
    notes := #["note: `{}` takes its type from where it is written, as the other side of `=` or a binding gives it one; here, nothing does",
      "help: write it where its type is known, as in `s = {}`, or write a member"] }

/-- `s.m`, where `s` is a set, which has only `card`. -/
def unknownSetMethodMsg (m : String) (ty : String) : Msg :=
  { code? := some "F0321", headline := s!"`{ty}` has no method `{m}`", label? := some "unknown method"
    notes := #["note: the only method of a set is `card`"]
    fixes := if ["size", "length", "len", "count"].contains m then #[{ msg := "the method is called `card`", replacement := "card" }] else #[] }

/-- `r.closure`, where `r`, of type `ty`, relates two different types. -/
def closureTypeMsg (ty : String) : Msg :=
  { code? := some "F0328", headline := s!"`closure` needs a relation of a type with itself, found `{ty}`"
    label? := some "not `Rel(A, A)`"
    notes := #["note: a chain of pairs `(a, b)`, `(b, c)` needs the second members to be of the first members' type"
      ] }

/-- `r join q`, where an operand, of type `ty`, is not a relation, or, with
`q?`, the relations do not meet. -/
def joinTypeMsg (ty : String) (q? : Option String) : Msg :=
  match q? with
  | none =>
    { code? := some "F0328", headline := s!"`join` needs relations, found `{ty}`", label? := some "not a relation"
      notes := #["note: `r join q` composes the relations `r: Rel(A, B)` and `q: Rel(B, C)`"] }
  | some q =>
    { code? := some "F0328", headline := s!"cannot join `{ty}` with `{q}`"
      label? := some "the middle types differ"
      notes := #["note: `r join q` composes `r: Rel(A, B)` with `q: Rel(B, C)`: the second type of `r` is the first of `q`"] }

/-- `x in s`, where `s` has type `found` rather than `expected`, the set or
relation of `x`'s type; `pair` if `x` is a pair. -/
def membershipTypeMsg (expected found : String) (pair : Bool) : Msg :=
  { code? := some "F0325", headline := s!"`in` needs a `{expected}` on its right, found `{found}`"
    label? := some (if pair then s!"a pair and `{found}`" else s!"`{found}`")
    notes := #[if pair then "note: `(x, y) in r` is membership: `r` is a relation between values of `x`'s and `y`'s types"
      else "note: `x in s` is membership: `s` is a set of values of `x`'s type"] }

/-- `[]` where nothing gives it a type (`Reqs/Lang/Types#checking-and-synthesis`). -/
def emptySeqTypeMsg : Msg :=
  { code? := some "F0324", headline := "the type of `[]` cannot be known here", label? := some "a sequence of what?"
    notes := #["note: `[]` takes its type from where it is written, as the other side of `=` or a binding gives it one; here, nothing does",
      "help: write it where its type is known, as in `q = []`, or write a member"] }

/-- `q[i]`, where `q`, of type `ty`, is not a sequence. -/
def notIndexableMsg (ty : String) : Msg :=
  { code? := some "F0332", headline := s!"cannot index a `{ty}`", label? := some "not a sequence"
    notes := #["note: only a sequence, `Seq(T)`, is indexed, as `q[i]`"] }

/-- A pair outside a relation literal and the left of `in`. -/
def pairPlaceMsg : Msg :=
  { code? := some "F0329", headline := "a pair can only be a member of a relation literal or the left of `in`"
    label? := some "a pair"
    notes := #["note: there is no type of pairs; a relation is a set of them, as in `{(a, b)}` and `(a, b) in r`"] }

/-! ## The decidable core (`Reqs/Lang/Decidability`) -/

inductive Construct where
  | stringCompare
  | stringAtom
  | stringIndex
  | stringSearch
  | setAlgebra
  | setFunction
  | relational
  | relationalCard
  | seqArray
  | seqWord
  deriving Inhabited, BEq, DecidableEq, Repr

inductive Method where
  | len
  | startsWith
  | endsWith
  | contains
  | «matches»
  | «at»
  | slice
  | indexOf
  | replace
  | replaceAll
  | card
  | inverse
  | closure
  | image
  | domain
  | range
  | update
  | rev
  | abs
  | min
  | max
  deriving Inhabited, BEq, DecidableEq, Repr

def Method.all : Array Method :=
  #[.len, .startsWith, .endsWith, .contains, .matches, .at, .slice, .indexOf, .replace, .replaceAll, .card,
    .inverse, .closure, .image, .domain, .range, .update, .rev, .abs, .min, .max]

def Method.name : Method → String
  | .len => "len"
  | .startsWith => "starts_with?"
  | .endsWith => "ends_with?"
  | .contains => "contains?"
  | .matches => "matches?"
  | .at => "at"
  | .slice => "slice"
  | .indexOf => "index_of"
  | .replace => "replace"
  | .replaceAll => "replace_all"
  | .card => "card"
  | .inverse => "inverse"
  | .closure => "closure"
  | .image => "image"
  | .domain => "domain"
  | .range => "range"
  | .update => "update"
  | .rev => "rev"
  | .abs => "abs"
  | .min => "min"
  | .max => "max"

def Method.ofName? (s : String) : Option Method := Method.all.find? (·.name == s)

/-- The relational methods' names, for finding them in a receiver. -/
def relationalNames : List String := ["inverse", "closure", "image", "domain", "range"]

/-- Whether the method is a relation's, other than `card`. -/
def Method.relational : Method → Bool
  | .inverse | .closure | .image | .domain | .range => true
  | _ => false

/-- Whether the method applies to a receiver whose type is a `String`
(`string`), a set (`set`), a relation (`rel`), a sequence (`seq`) or an
`Int` (`int`) (`lang::method_type`): `card` is a set's and a relation's,
the relational methods a relation's, `update` and `rev` a sequence's,
`matches?` and `replace_all` a `String`'s, `abs`, `min` and `max` an
`Int`'s, and the others both a `String`'s and a sequence's. -/
def Method.accepts (m : Method) (string set : Bool) (rel := false) (seq := false) (int := false) : Bool :=
  match m with
  | .card => set || rel
  | .update | .rev => seq
  | .matches | .replaceAll => string
  | .abs | .min | .max => int
  | m => if m.relational then rel else string || seq

/-- The kinds of value that methods take and give; a set's or relation's
element types are the receiver's business. `string` is the receiver's
type, a `String` or a sequence, and `elem` a sequence's element type. -/
inductive MethodTy where
  | bool
  | int
  | string
  | set
  | rel
  | elem
  deriving Inhabited, BEq, DecidableEq, Repr

/-- The type of its result. -/
def Method.result : Method → MethodTy
  | .startsWith | .endsWith | .contains | .matches => .bool
  | .len | .indexOf | .card | .abs | .min | .max => .int
  | .at | .slice | .replace | .replaceAll | .update | .rev => .string
  | .inverse | .closure => .rel
  | .image | .domain | .range => .set

/-- The types of its parameters; the pattern of `matches?` is a literal. -/
def Method.params : Method → List MethodTy
  | .len | .card | .inverse | .closure | .domain | .range | .rev | .abs => []
  | .min | .max => [.int]
  | .update => [.int, .elem]
  | .image => [.set]
  | .startsWith | .endsWith | .contains | .matches => [.string]
  | .at => [.int]
  | .slice => [.int, .int]
  | .indexOf => [.string, .int]
  | .replace | .replaceAll => [.string, .string]

def Method.arity (m : Method) : Nat := m.params.length

/-- Whether it searches (`Reqs/Lang/Decidability#strings`), which is outside
the decidable core; `at` and `slice` index, which is in it with constant
positions. -/
def Method.construct : Method → Construct
  | .at | .slice => .stringIndex
  | .indexOf | .replace | .replaceAll => .stringSearch
  | .card => .setAlgebra
  | .inverse | .closure | .image | .domain | .range => .relational
  | .update => .seqArray
  | .rev => .seqWord
  | _ => .stringAtom

/-- Its kind on a sequence (`Reqs/Lang/Decidability#sequences`): `len` and
`update` are an array's, and the rest make word equations. -/
def Method.seqConstruct : Method → Construct
  | .len | .update => .seqArray
  | _ => .seqWord

/-- Names that other languages give the methods. -/
def methodAliases : List (String × String) :=
  [("length", "len"), ("size", "len"), ("count", "len"), ("startsWith", "starts_with?"),
   ("starts_with", "starts_with?"), ("endsWith", "ends_with?"), ("ends_with", "ends_with?"),
   ("contains", "contains?"), ("includes", "contains?"), ("matches", "matches?"), ("is_match", "matches?")]

/-- The argument of `matches?` that is not a string literal. -/
def patternNotLiteralMsg : Msg :=
  { code? := some "F0323", headline := "the argument of `matches?` must be a string literal", label? := some "not a literal"
    notes := #["note: a pattern is parsed when the spec is checked, so it cannot be a variable or a constant",
      "help: write the pattern here, as a raw literal such as `r\"[a-z]+\"`"] }

/-- `e.m`, where the type of `e`, `ty`, has no method `m`. -/
def unknownMethodMsg (m : String) (ty : String) (string := true) (set := false) (rel := false) (seq := false) (int := false) :
    Msg :=
  let names := (Method.all.filter (·.accepts string set rel seq int)).map (·.name)
  let suggestion := ((methodAliases.lookup m) <|> similarStr m names).toArray
  { code? := some "F0321", headline := s!"`{ty}` has no method `{m}`", label? := some "unknown method"
    notes := #[s!"note: the methods of `{ty}` are {", ".intercalate (names.toList.map (s!"`{·}`"))}"]
    fixes := suggestion.map fun s => { msg := s!"the method is called `{s}`", replacement := s } }

/-- `e.m`, where the type of `e`, `ty`, has no methods at all. -/
def noMethodsMsg (m : String) (ty : String) : Msg :=
  { code? := some "F0322", headline := s!"`{ty}` has no methods, so it has no method `{m}`", label? := some "no methods"
    notes := #["note: only `Int`s, `String`s, sets, relations and sequences have methods"] }

/-- Whether a construct is in the decidable core (`lang::in_core`); one
whose operands are all constants (`ground`) has a fixed value. -/
def inCore (c : Construct) (constantArgs comparable infiniteOutput ground : Bool) (infiniteElems : Bool := true)
    (finiteRange : Bool := true) (literalOperand : Bool := false) : Bool :=
  ground || !infiniteOutput && match c with
    | .stringAtom | .stringIndex => constantArgs
    | .stringCompare => comparable
    | .stringSearch => false
    | .setAlgebra => true
    | .setFunction => infiniteElems
    | .relational => finiteRange
    | .relationalCard => false
    | .seqArray => true
    | .seqWord => literalOperand

/-- Why a construct is outside the core, and how to stay in it. -/
def undecidableMsg (c : Construct) (infiniteOutput : Bool) : Msg :=
  let (why, help) := if infiniteOutput then
      ("an operand mentions an output of an infinite type, which the realizability check would search for",
        "help: mention the inputs that the output depends on instead, or define the output")
    else match c with
      | .stringAtom => ("its argument is not a constant", "help: compare with a literal or a constant")
      | .stringIndex => ("its position is not a constant", "help: index at constant positions")
      | .setAlgebra => ("it is an operation on sets", "help: mention the inputs that the output depends on")
      | .setFunction => ("a function of sets whose members' type may be finite does not combine with the theory of sets",
        "help: use a set of an infinite type, such as `Int` or `String`")
      | .relational => ("a relational operator over a type that is not finite quantifies over its values",
        "help: relate values of finite types, such as enums, or opt out where reachability is the point")
      | .relationalCard => ("the solver does not reliably combine counting with relational operators",
        "help: say what the members are, with `in` and `subset`, rather than how many there are")
      | .seqWord => ("an operation on sequences other than indexing, `len` and `update` makes a word equation, which may be undecidable",
        "help: index at positions, or compare with a literal, as in `x in [a, b]` or `q.starts_with?([a])`")
      | .seqArray => ("it is an operation on sequences", "help: mention the inputs that the output depends on")
      | .stringCompare => ("it compares two strings that are not both variables, and neither is a constant",
        "help: compare with a constant, or compare two variables with `=`")
      | .stringSearch => ("searching a string, or `++` here, which makes a word equation, may be undecidable",
        "help: compare a concatenation with a constant, or call a method on it; describe a search with `starts_with?`, `contains?` or a pattern")
  { code? := some "F0714", headline := s!"this is outside the decidable core: {why}"
    label? := some "outside the decidable core"
    notes := #[help] }

/-- An instance, or a binder of a global expectation, of a component
outside the decidable core: its constraints are part of the queries. -/
def undecidableInstMsg (comp : Name) : Msg :=
  { code? := some "F0714", headline := s!"`{showPath comp}` is outside the decidable core, and so is what instantiates it"
    label? := some "outside the decidable core"
    notes := #[s!"note: `{showPath comp}` opts out of the decidable core, and its constraints are part of these queries"] }

end Fren.Core
