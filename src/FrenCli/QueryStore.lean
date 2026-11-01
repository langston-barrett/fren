-- keep-sorted start
import FrenCore.Check
import cvc5
-- keep-sorted end

/-!
# The persistent query cache

`fren check --query-cache DIR` keeps the solver's answers in `DIR` across
runs, and `--verify-query-cache DIR` compares the solver's fresh answers
with those of `DIR` (`Reqs/Cli#query-cache`). An entry is a file of its
own, `DIR/HH/HHHHHHHHHHHHHHHH`, named by the hash of its key, and it holds
the key itself, so that a hash shared by two keys is a miss, never another
script's answer. It is written to a temporary file and renamed, so that
runs at once never read half an entry.
-/

namespace FrenCli

open Fren.Core (Outcome)

/-- The version of how a script is run and its answer stored: bumped
whenever the answer that `solveScript` reads from a script can change
without the script changing, such as how it reads a model, or whenever an
entry's format changes. The cold run on `main` compares its answers with
the previous `main`'s cache, and so finds a missed bump
(`Reqs/Cli#query-cache`). Bumped too when every script changes, such as
its header: the previous cache then has entries of this version that no
query asks, and that run would compare nothing, which fails it
(`Reqs/dev/Testing#query-cache`). -/
def queryCacheVersion : Nat := 2

/-- An answer as the cache sees it (`cli::query_cache`). -/
inductive CachedAnswer where
  | unsat
  | sat (hasModel : Bool)
  | unknown
  deriving DecidableEq, Inhabited, Repr

/-- `o`, with whether its model was wanted, as the cache sees it. -/
def CachedAnswer.of (o : Outcome String) (hasModel : Bool) : CachedAnswer :=
  match o with
  | .unsat => .unsat
  | .sat _ => .sat hasModel
  | .unknown _ => .unknown

/-- Whether an answer is stored: never `unknown`, which a time limit or
the machine's load can give (`cli::query_cache`). -/
def CachedAnswer.stored : CachedAnswer → Bool
  | .unknown => false
  | _ => true

/-- Whether a stored answer answers a query that wants a model if
`wantModel`: `sat` without a model does not (`cli::query_cache`). -/
def CachedAnswer.answers (a : CachedAnswer) (wantModel : Bool) : Bool :=
  match a with
  | .unsat => true
  | .sat hasModel => hasModel || !wantModel
  | .unknown => false

/-- Whether a fresh answer `a` contradicts the answer `b` kept for the same
key, where `sameModel` is that both have models and they are the same: one
is `unsat` and the other `sat`, or both have models and they differ
(`cli::contradicts`). -/
def contradicts (a b : CachedAnswer) (sameModel : Bool) : Bool :=
  (a == .unsat) != (b == .unsat) || (a == .sat true && b == .sat true && !sameModel)

/-- Whether two models are the same. -/
def sameModel (m n : Array (Lean.Name × String)) : Bool :=
  m.map (·.1) == n.map (·.1) && m.map (·.2) == n.map (·.2)

/-- `s` on one line: `\` and line breaks escaped. -/
def escapeLine (s : String) : String :=
  (s.replace "\\" "\\\\").replace "\n" "\\n"

/-- `escapeLine`'s inverse. -/
def unescapeLine (s : String) : String := Id.run do
  let mut out := ""
  let mut escaped := false
  for c in s.toList do
    if escaped then
      out := out.push (if c == 'n' then '\n' else c)
      escaped := false
    else if c == '\\' then escaped := true
    else out := out.push c
  return out

/-- The components of `n`, or `none` if one is numeric: a name as an entry
stores it. -/
def nameParts? (n : Lean.Name) : Option (List String) :=
  n.components.mapM fun
    | .str .anonymous s => some s
    | _ => none

/-- The name whose components are `parts`. -/
def nameOfParts (parts : List String) : Lean.Name :=
  parts.foldl Lean.Name.mkStr .anonymous

/-- Components as an entry stores them: their number, then each, escaped,
on a line of its own. -/
def partsLines (parts : List String) : List String :=
  toString parts.length :: parts.map escapeLine

/-- Components of `partsLines` at the start of `ls`, and the lines after
them. -/
def partsOfLines? : List String → Option (List String × List String)
  | count :: rest => do
    let k ← count.toNat?
    guard (rest.length ≥ k)
    return ((rest.take k).map unescapeLine, rest.drop k)
  | [] => none

/-- A name of a model, as an entry stores it (`partsLines`); `none` if it
has a numeric component. -/
def nameLines? (n : Lean.Name) : Option (List String) :=
  (nameParts? n).map partsLines

/-- A name of `nameLines?` at the start of `ls`, and the lines after it. -/
def nameOfLines? (ls : List String) : Option (Lean.Name × List String) :=
  (partsOfLines? ls).map fun (parts, rest) => (nameOfParts parts, rest)

/-- A formula to read the value of in a query's model (`solveScript`): its
value is read into the name `key`, and only if the value of `guard?`, if
any, is `true` in the model. -/
structure ModelObservation where
  key : Lean.Name
  formula : String
  guard? : Option Lean.Name := none
  deriving BEq, Hashable, Inhabited, Repr

/-- An observation as a key holds it (`cli::Observation`): its name's
components, its formula, and its guard's components, if it has one. -/
structure KeyObservation where
  name : List String
  formula : String
  guard? : Option (List String)
  deriving DecidableEq, Inhabited, Repr

/-- `o` as a key holds it; `none` if a name of it has a numeric
component. -/
def KeyObservation.of? (o : ModelObservation) : Option KeyObservation := do
  let guard? ← match o.guard? with
    | none => some none
    | some g => (nameParts? g).map some
  return { name := ← nameParts? o.key, formula := o.formula, guard? }

/-- What an entry's answer is the answer to (`cli::Key`): every input of
the solver's run of a query (`solveScript`), which are the whole script
and the observations of its model; cvc5's version; and
`queryCacheVersion`. -/
structure CacheKey where
  script : String
  observations : List KeyObservation := []
  solver : String
  version : Nat
  deriving DecidableEq, Inhabited, Repr

/-- The key of the query `script`, with `observations`, for cvc5's version
`solver` (`cli::query_key`). -/
def CacheKey.of (script : String) (observations : List KeyObservation) (solver : String) : CacheKey :=
  { script, observations, solver, version := queryCacheVersion }

/-- The lines of an observation in a key. -/
def KeyObservation.lines (o : KeyObservation) : List String :=
  partsLines o.name ++ [escapeLine o.formula] ++ match o.guard? with
    | none => ["unguarded"]
    | some g => "guarded" :: partsLines g

/-- An observation of `KeyObservation.lines` at the start of `ls`, and the
lines after it. -/
def KeyObservation.read? (ls : List String) : Option (KeyObservation × List String) := do
  let (name, rest) ← partsOfLines? ls
  let formula :: rest := rest | none
  match rest with
  | "unguarded" :: rest => return ({ name, formula := unescapeLine formula, guard? := none }, rest)
  | "guarded" :: rest =>
    let (g, rest) ← partsOfLines? rest
    return ({ name, formula := unescapeLine formula, guard? := some g }, rest)
  | _ => none

/-- `n` observations of `KeyObservation.read?` at the start of `ls`, and
the lines after them. -/
def readObservations? : Nat → List String → Option (List KeyObservation × List String)
  | 0, ls => some ([], ls)
  | n + 1, ls => do
    let (o, rest) ← KeyObservation.read? ls
    let (os, rest) ← readObservations? n rest
    return (o :: os, rest)

/-- The lines that begin `k`'s entry. -/
def CacheKey.lines (k : CacheKey) : String :=
  let ls := [s!"fren query cache {k.version}", s!"cvc5 {escapeLine k.solver}", escapeLine k.script,
    toString k.observations.length] ++ k.observations.flatMap (·.lines)
  String.join (ls.map (· ++ "\n"))

/-- The key at the start of an entry's lines, and the lines after it. -/
def CacheKey.read? : List String → Option (CacheKey × List String)
  | v :: c :: script :: count :: rest => do
    let version ← (v.dropPrefix? "fren query cache ").bind (·.toString.toNat?)
    let solver ← (c.dropPrefix? "cvc5 ").map (unescapeLine ·.toString)
    let (observations, rest) ← readObservations? (← count.toNat?) rest
    return ({ script := unescapeLine script, observations, solver, version }, rest)
  | _ => none

/-- Whether an entry answers a query (`cli::query_cache`): it is there,
for the same key, and it answers whether a model is wanted. -/
def cacheHit (found : Bool) (asked stored : CacheKey) (a : CachedAnswer) (wantModel : Bool) : Bool :=
  found && decide (asked = stored) && a.answers wantModel

/-- A query cache's directories and what they are for, with cvc5's
version. -/
structure QueryStore where
  /-- `--query-cache`: answered from, and written to. -/
  dir? : Option System.FilePath := none
  /-- `--verify-query-cache`: only compared with. -/
  verify? : Option System.FilePath := none
  solver : String := ""
  /-- The entries of `verify?` that a fresh answer contradicts. -/
  mismatches : IO.Ref (Array String)
  /-- How many fresh answers were compared with an entry of `verify?`. -/
  compared : IO.Ref Nat
  /-- How many entries this process has begun to write: the checks of
  several procedures write at once, and each write's temporary file is
  named by its number, taken atomically. -/
  writes : IO.Ref Nat

/-- cvc5's version, as its solver reports it. -/
def cvc5Version : IO String := do
  match ← cvc5.Env.run (do
      let tm ← cvc5.TermManager.new
      let solver ← cvc5.Solver.new tm
      solver.getVersion) with
  | .ok v => return v
  | .error e => throw (IO.userError s!"cannot read cvc5's version: {e}")

/-- A store over `dir?` and `verify?`. -/
def QueryStore.new (dir? verify? : Option System.FilePath) : IO QueryStore := do
  return { dir?, verify?, solver := ← cvc5Version, mismatches := ← IO.mkRef #[], compared := ← IO.mkRef 0, writes := ← IO.mkRef 0 }

/-- The key of the query `script` whose model reads `observations`; `none`
if a name of them has a numeric component, which an entry cannot hold. -/
def QueryStore.key? (st : QueryStore) (script : String) (observations : Array ModelObservation) : Option CacheKey :=
  return CacheKey.of script (← observations.toList.mapM KeyObservation.of?) st.solver

/-- The hex digits of `n`, 16 of them. -/
def hex16 (n : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 n.toNat)
  String.ofList (List.replicate (16 - s.length) '0') ++ s

/-- The path of `k`'s entry in `dir`, by the hash of its lines. -/
def CacheKey.path (k : CacheKey) (dir : System.FilePath) : System.FilePath :=
  let h := hex16 (hash k.lines)
  dir / (h.take 2).toString / h

/-- The text of an entry: `k`'s lines, then the answer `o`, with whether
it has a model, and its model; `none` if `o` is not stored
(`CachedAnswer.stored`) or a name of its model cannot be. -/
def encodeEntry? (k : CacheKey) (o : Outcome String) (hasModel : Bool) : Option String := do
  let body ← match o with
    | .unsat => some "unsat\n"
    | .sat model =>
      if !hasModel then some "sat\n" else do
        let lines ← model.toList.mapM fun (n, v) => return ((← nameLines? n) ++ [escapeLine v]).map (· ++ "\n")
        pure ("sat model\n" ++ String.join lines.flatten)
    | .unknown _ => none
  return k.lines ++ body

/-- The pairs of a model's names and values, from `ls`. -/
partial def modelOfLines? (ls : List String) (acc : Array (Lean.Name × String) := #[]) :
    Option (Array (Lean.Name × String)) :=
  match ls with
  | [] => some acc
  | _ => do
    let (n, rest) ← nameOfLines? ls
    let v :: rest := rest | none
    modelOfLines? rest (acc.push (n, unescapeLine v))

/-- `encodeEntry?`'s inverse: the key, the answer and whether it has a
model. -/
def decodeEntry? (text : String) : Option (CacheKey × Outcome String × Bool) := do
  let (stored, lines) ← CacheKey.read? (text.splitOn "\n")
  match lines with
  | ["unsat", ""] => return (stored, .unsat, true)
  | ["sat", ""] => return (stored, .sat #[], false)
  | "sat model" :: rest => return (stored, .sat (← modelOfLines? rest.dropLast), true)
  | _ => none

/-- The entry at `k`'s path in `dir`, if there is one that can be read:
its key, which may differ from `k`, and its answer, with whether it has a
model. -/
def readEntry? (dir : System.FilePath) (k : CacheKey) : IO (Option (CacheKey × Outcome String × Bool)) := do
  let p := k.path dir
  unless ← p.pathExists do return none
  let some text ← (some <$> IO.FS.readFile p) <|> pure none | return none
  return decodeEntry? text

/-- The answer of the entry of `k` in `dir`, if it is for exactly `k` and
answers a query that wants a model if `wantModel` (`cacheHit`). -/
def lookupEntry? (dir : System.FilePath) (k : CacheKey) (wantModel : Bool) : IO (Option (Outcome String × Bool)) := do
  let entry? ← readEntry? dir k
  let (stored, o, hasModel) := entry?.getD (default, .unknown "", false)
  if cacheHit entry?.isSome k stored (CachedAnswer.of o hasModel) wantModel then return some (o, hasModel)
  else return none

/-- Writes the answer `o` to `k`, with whether it has a model, to `dir`,
if it can be (`encodeEntry?`). `n` is a number that no other write of this
process uses, which names its temporary file. -/
def writeEntry (dir : System.FilePath) (k : CacheKey) (o : Outcome String) (hasModel : Bool) (n : Nat) : IO Unit := do
  let some text := encodeEntry? k o hasModel | return
  let p := k.path dir
  let some parent := p.parent | return
  IO.FS.createDirAll parent
  -- Renamed into place, so that no run reads half an entry.
  let tmp := p.addExtension s!"tmp{← IO.Process.getPID}-{n}"
  IO.FS.writeFile tmp text
  IO.FS.rename tmp p

/-- Whether `dir` holds an entry of this `queryCacheVersion` and of cvc5's
version `solver`: one whose answer a run could compare with. A change to
either alters every key, and leaves none. -/
def comparableEntries (dir : System.FilePath) (solver : String) : IO Bool := do
  unless ← dir.isDir do return false
  for f in ← dir.walkDir do
    if ← f.isDir then continue
    let some text ← (some <$> IO.FS.readFile f) <|> pure none | continue
    if let some (k, _) := CacheKey.read? (text.splitOn "\n") then
      if k.version == queryCacheVersion && k.solver == solver then return true
  return false

/-- The answer that `--query-cache` gives `script` for a query that wants
a model if `wantModel`, if it gives one. -/
def QueryStore.lookup? (st : QueryStore) (script : String) (observations : Array ModelObservation) (wantModel : Bool) :
    IO (Option (Outcome String × Bool)) := do
  let (some dir, some k) := (st.dir?, st.key? script observations) | return none
  lookupEntry? dir k wantModel

/-- Records the solver's fresh answer `o` to `script`: compared with
`--verify-query-cache`'s, and written to `--query-cache`. -/
def QueryStore.record (st : QueryStore) (script : String) (observations : Array ModelObservation) (o : Outcome String)
    (hasModel : Bool) : IO Unit := do
  unless (CachedAnswer.of o hasModel).stored do return
  let some k := st.key? script observations | return
  if let some old := st.verify? then
    if let some (o', hasModel') ← lookupEntry? old k false then
      st.compared.modify (· + 1)
      let same := match o, o' with
        | .sat m, .sat n => sameModel m n
        | _, _ => false
      if contradicts (CachedAnswer.of o hasModel) (CachedAnswer.of o' hasModel') same then
        st.mismatches.modify (·.push (k.path old).toString)
  if let some dir := st.dir? then
    let n ← st.writes.modifyGet fun n => (n, n + 1)
    try writeEntry dir k o hasModel n
    catch e => IO.eprintln s!"warning: cannot write to the query cache: {e}"

end FrenCli
