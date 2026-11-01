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
(`Reqs/Cli#query-cache`). -/
def queryCacheVersion : Nat := 1

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

/-- A name of a model, as an entry stores it: its string components, each
escaped, separated by `\/`; `none` if it has a numeric component. -/
def nameLine? (n : Lean.Name) : Option String := do
  let parts ← n.components.mapM fun
    | .str .anonymous s => some (escapeLine s)
    | _ => none
  return "\\/".intercalate parts

/-- `nameLine?`'s inverse. -/
def nameOfLine (s : String) : Lean.Name :=
  (s.splitOn "\\/").foldl (fun n p => Lean.Name.mkStr n (unescapeLine p)) .anonymous

/-- What an entry's answer is the answer to (`cli::Key`): the whole
script, with the observations of its model; cvc5's version; and
`queryCacheVersion`. -/
structure CacheKey where
  script : String
  solver : String
  version : Nat
  deriving DecidableEq, Inhabited, Repr

/-- The lines that begin `k`'s entry. -/
def CacheKey.lines (k : CacheKey) : String :=
  s!"fren query cache {k.version}\ncvc5 {k.solver}\n{escapeLine k.script}\n"

/-- The key at the start of an entry's lines, and the lines after it. -/
def CacheKey.read? : List String → Option (CacheKey × List String)
  | v :: c :: script :: rest => do
    let version ← (v.dropPrefix? "fren query cache ").bind (·.toString.toNat?)
    let solver ← (c.dropPrefix? "cvc5 ").map (·.toString)
    return ({ script := unescapeLine script, solver, version }, rest)
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
  return { dir?, verify?, solver := ← cvc5Version, mismatches := ← IO.mkRef #[] }

/-- The key of `script`, a script and its model's observations. -/
def QueryStore.key (st : QueryStore) (script : String) : CacheKey :=
  { script, solver := st.solver, version := queryCacheVersion }

/-- The hex digits of `n`, 16 of them. -/
def hex16 (n : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 n.toNat)
  String.ofList (List.replicate (16 - s.length) '0') ++ s

/-- The path of `k`'s entry in `dir`, by the hash of its lines. -/
def CacheKey.path (k : CacheKey) (dir : System.FilePath) : System.FilePath :=
  let h := hex16 (hash k.lines)
  dir / (h.take 2).toString / h

/-- The entry at `k`'s path in `dir`, if there is one that can be read:
its key, which may differ from `k`, and its answer, with whether it has a
model. -/
def readEntry? (dir : System.FilePath) (k : CacheKey) : IO (Option (CacheKey × Outcome String × Bool)) := do
  let p := k.path dir
  unless ← p.pathExists do return none
  let some text ← (some <$> IO.FS.readFile p) <|> pure none | return none
  let some (stored, lines) := CacheKey.read? (text.splitOn "\n") | return none
  match lines with
  | ["unsat", ""] => return some (stored, .unsat, true)
  | ["sat", ""] => return some (stored, .sat #[], false)
  | "sat model" :: rest =>
    let rest := rest.dropLast.toArray
    unless rest.size % 2 == 0 do return none
    let model := (Array.range (rest.size / 2)).map fun i =>
      (nameOfLine rest[2 * i]!, unescapeLine rest[2 * i + 1]!)
    return some (stored, .sat model, true)
  | _ => return none

/-- The answer of the entry of `k` in `dir`, if it is for exactly `k` and
answers a query that wants a model if `wantModel` (`cacheHit`). -/
def lookupEntry? (dir : System.FilePath) (k : CacheKey) (wantModel : Bool) : IO (Option (Outcome String × Bool)) := do
  let entry? ← readEntry? dir k
  let (stored, o, hasModel) := entry?.getD (default, .unknown "", false)
  if cacheHit entry?.isSome k stored (CachedAnswer.of o hasModel) wantModel then return some (o, hasModel)
  else return none

/-- Writes the answer `o` to `k`, with whether it has a model, to `dir`,
if it is stored (`CachedAnswer.stored`) and its model's names can be. -/
def writeEntry (dir : System.FilePath) (k : CacheKey) (o : Outcome String) (hasModel : Bool) : IO Unit := do
  let body? : Option String := match o with
    | .unsat => some "unsat\n"
    | .sat model =>
      if !hasModel then some "sat\n" else do
        let lines ← model.toList.mapM fun (n, v) => return s!"{← nameLine? n}\n{escapeLine v}\n"
        return "sat model\n" ++ String.join lines
    | .unknown _ => none
  let some body := body? | return
  let p := k.path dir
  let some parent := p.parent | return
  IO.FS.createDirAll parent
  -- Renamed into place, so that no run reads half an entry.
  let tmp := p.addExtension s!"tmp{← IO.Process.getPID}-{← IO.monoNanosNow}-{← IO.rand 0 1000000000}"
  IO.FS.writeFile tmp (k.lines ++ body)
  IO.FS.rename tmp p

/-- The answer that `--query-cache` gives `script` for a query that wants
a model if `wantModel`, if it gives one. -/
def QueryStore.lookup? (st : QueryStore) (script : String) (wantModel : Bool) : IO (Option (Outcome String × Bool)) := do
  let some dir := st.dir? | return none
  lookupEntry? dir (st.key script) wantModel

/-- Records the solver's fresh answer `o` to `script`: compared with
`--verify-query-cache`'s, and written to `--query-cache`. -/
def QueryStore.record (st : QueryStore) (script : String) (o : Outcome String) (hasModel : Bool) : IO Unit := do
  unless (CachedAnswer.of o hasModel).stored do return
  let k := st.key script
  if let some old := st.verify? then
    if let some (o', hasModel') ← lookupEntry? old k false then
      let same := match o, o' with
        | .sat m, .sat n => sameModel m n
        | _, _ => false
      if contradicts (CachedAnswer.of o hasModel) (CachedAnswer.of o' hasModel') same then
        st.mismatches.modify (·.push (k.path old).toString)
  if let some dir := st.dir? then
    try writeEntry dir k o hasModel
    catch e => IO.eprintln s!"warning: cannot write to the query cache: {e}"

end FrenCli
