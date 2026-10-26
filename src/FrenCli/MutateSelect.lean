-- keep-sorted start
import FrenCli.Mutate
-- keep-sorted end

/-!
# Selecting mutants

The decisions by which `fren mutate` selects the mutants to run
(`Reqs/Mutate#selecting-mutants`), apart from running them, so that
`Impls` can link them to their requirements: which items a patch
(`--diff`) touches, which mutants a sample takes, and which a shard
(`--shard`) does.
-/

namespace FrenCli.Mutate

/-- Whether a mutant is selected, from whether it passes each filter:
`--comp`, `--mutant`, `--diff`, `--sample` and `--shard`, each `true` if
not given (`mutate::selection`). -/
def chosen (ofComp named touched sampled sharded : Bool) : Bool := ofComp && named && touched && sampled && sharded

/-- Whether a sample of `size` mutants takes the one that comes `rank`th,
from 0, in the order of their hashes (`mutate::sample`). -/
def takes (rank size : Nat) : Bool := rank < size

/-- Whether the shard `k` of `n` takes a mutant whose identifier's hash is
`h` (`mutate::shard`). -/
def inShard (h k n : Nat) : Bool := h % n == k

/-- `K/N` of `--shard K/N`, if `K < N`. -/
def shard? (s : String) : Option (Nat × Nat) :=
  match s.splitOn "/" with
  | [k, n] => do
    let k ← k.toNat?
    let n ← n.toNat?
    if k < n then some (k, n) else none
  | _ => none

/-! ## Patches -/

/-- What a patch changes in the new text of one file: the lines that it
adds, counted from 1, and where it removes lines, each as the line after
which they were, 0 if before the first. A changed line is removed and
added. -/
structure Changes where
  added : Array Nat := #[]
  removed : Array Nat := #[]
  deriving Inhabited

/-- Whether a change at `line` touches an item from line `first` to line
`last` (`mutate::touches`): a line added, or the line after which lines
were removed, if it is one of the item's. -/
def touchesLine (first last line : Nat) : Bool := first ≤ line && line ≤ last

def Changes.touches (c : Changes) (first last : Nat) : Bool :=
  (c.added ++ c.removed).any (touchesLine first last ·)

/-- The start and number of lines of one side of a hunk's header, `S,N`,
or `S`, which means `S,1`. -/
def hunkRange? (s : String) : Option (Nat × Nat) :=
  match s.splitOn "," with
  | [a] => a.toNat?.map (·, 1)
  | [a, b] => do pure (← a.toNat?, ← b.toNat?)
  | _ => none

/-- The old and new ranges of a hunk's header, `@@ -S,N +S,N @@`. -/
def hunkHeader? (line : String) : Option ((Nat × Nat) × (Nat × Nat)) :=
  match line.splitOn " " with
  | "@@" :: old :: new :: "@@" :: _ => do
    let o ← if old.startsWith "-" then hunkRange? (String.ofList (old.toList.drop 1)) else none
    let n ← if new.startsWith "+" then hunkRange? (String.ofList (new.toList.drop 1)) else none
    pure (o, n)
  | _ => none

/-- The path of a `---` or `+++` line, without the date that `diff -u`
writes after a tab; `none` for `/dev/null`. -/
def headerPath (rest : String) : Option String :=
  let p := String.ofList (rest.toList.takeWhile (· != '\t'))
  if p == "/dev/null" then none else some p

/-- What the unified diff `text`, such as the output of `git diff -U0`,
changes in the new text of each file that it names, by the path after
`+++`; or the line, counted from 1, where it is not a diff, and why. A
line outside a hunk is skipped, as `git apply` skips the header of a
commit. -/
def parsePatch (text : String) : Except (Nat × String) (Array (String × Changes)) := Id.run do
  -- Without the `\r` of a line that ends in `\r\n`.
  let lines := (text.splitOn "\n").toArray.map fun l => if l.endsWith "\r" then String.ofList l.toList.dropLast else l
  -- Splitting leaves an empty line after the last newline.
  let lines := if lines.back? == some "" then lines.pop else lines
  let mut out : Array (String × Changes) := #[]
  -- The file that the hunks change, once a `+++` line names it: `none` for
  -- a file removed.
  let mut file? : Option (Option String) := none
  let mut i := 0
  let mut headers := false
  while i < lines.size do
    let line := lines[i]!
    i := i + 1
    -- A file's header: its hunks come after its `+++` line.
    if line.startsWith "diff " then headers := true; file? := none; continue
    if line.startsWith "--- " then headers := true; continue
    if line.startsWith "+++ " then
      headers := true
      file? := some (headerPath (String.ofList (line.toList.drop 4)))
      continue
    unless line.startsWith "@@" do continue
    let some ((_, oldN), (newS, newN)) := hunkHeader? line | return .error (i, "a hunk's header is not `@@ -S,N +S,N @@`")
    let some path? := file? | return .error (i, "a hunk comes before the `+++` line that names its file")
    let mut c : Changes := {}
    -- The next line of the new text; a hunk of no new lines comes after
    -- line `S`.
    let mut cur := if newN == 0 then newS + 1 else newS
    let mut old := oldN
    let mut new := newN
    while old > 0 || new > 0 do
      let some l := lines[i]? | return .error (i, "the patch ends inside a hunk")
      i := i + 1
      if l.startsWith "\\" then continue
      -- Some tools drop the space of an empty line of context.
      if (l.startsWith " " || l.isEmpty) && old > 0 && new > 0 then
        old := old - 1; new := new - 1; cur := cur + 1
      else if l.startsWith "+" && new > 0 then
        c := { c with added := c.added.push cur }
        new := new - 1; cur := cur + 1
      else if l.startsWith "-" && old > 0 then
        c := { c with removed := c.removed.push (cur - 1) }
        old := old - 1
      else return .error (i, "a line of a hunk does not fit its header")
    -- A line of a hunk past its header's count, other than the next file's
    -- header.
    if let some l := lines[i]? then
      if (l.startsWith " " || l.startsWith "+" || l.startsWith "-") && !l.startsWith "+++ " && !l.startsWith "--- " then
        return .error (i + 1, "a hunk has more lines than its header says")
    -- No file has the hunks of a file removed.
    let some path := path? | continue
    match out.findIdx? (·.1 == path) with
    | some k => out := out.modify k fun (p, d) => (p, { added := d.added ++ c.added, removed := d.removed ++ c.removed })
    | none => out := out.push (path, c)
  if !headers && lines.any (!·.trimAscii.isEmpty) then return .error (1, "it has no `diff`, `---` or `+++` line")
  return .ok out

/-- Whether the path `p`, which a patch names, is the file at `path`: as
written, or without the `a/` or `b/` that `git diff` writes before it. -/
def patchNames (p path : String) : Bool :=
  let path := idPath path
  idPath p == path || ((p.startsWith "a/" || p.startsWith "b/") && idPath (String.ofList (p.toList.drop 2)) == path)

/-- Whether some path of `changes`, from `parsePatch`, names one of the
files at `paths`. -/
def namesAny (changes : Array (String × Changes)) (paths : Array String) : Bool :=
  changes.any fun (p, _) => paths.any (patchNames p)

/-- What `changes`, from `parsePatch`, change in the file at `path`. -/
def changesOf (changes : Array (String × Changes)) (path : String) : Changes :=
  changes.foldl (init := {}) fun acc (p, c) =>
    if patchNames p path then { added := acc.added ++ c.added, removed := acc.removed ++ c.removed } else acc

/-- Where each item of a file starts, and its first and last lines,
counted from 1: from its first token to its last. `chars` is the file's
text, `toks` its tokens, and `starts` where each item starts
(`parseItems`). -/
def itemLines (chars : Array Char) (toks : Array Token) (starts : Array Nat) : Array (Nat × Nat × Nat) := Id.run do
  let newlines := (Array.range chars.size).filter (chars[·]! == '\n')
  -- One more than the number of newlines before `pos`.
  let line (pos : Nat) : Nat := Id.run do
    let mut lo := 0
    let mut hi := newlines.size
    while lo < hi do
      let mid := (lo + hi) / 2
      if newlines[mid]! < pos then lo := mid + 1 else hi := mid
    return lo + 1
  -- Where the last token of each item ends.
  let mut stops := starts
  let mut k := 0
  for t in toks do
    if t.tok == .eof then continue
    while k + 1 < starts.size && starts[k + 1]! ≤ t.span.start do k := k + 1
    if starts[k]?.any (· ≤ t.span.start) then stops := stops.set! k t.span.stop
  return (starts.zip stops).map fun (a, b) => (a, line a, line (max a (b - 1)))

/-- Whether `c` touches the item that contains the offset `pos`, whose
items are `items` (`itemLines`). -/
def touchedAt (c : Changes) (items : Array (Nat × Nat × Nat)) (pos : Nat) : Bool :=
  match items.findRev? (·.1 ≤ pos) with
  | some (_, first, last) => c.touches first last
  | none => false

end FrenCli.Mutate
