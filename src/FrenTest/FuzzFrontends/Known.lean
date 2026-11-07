-- keep-sorted start
import FrenTest.Frontends
import FrenTest.FuzzFrontends.Mode
-- keep-sorted end

open Lean
open FrenTest.Frontends (maskBetween)

namespace FrenTest.FuzzFrontends

/-- `s` with each number written right after `pre`, and followed by
`post`, as `N`. -/
def maskNumberAfter (s pre : String) (post : String := "") : String :=
  match s.splitOn pre with
  | [] => s
  | first :: rest => first ++ String.join (rest.map fun piece =>
    let digits := piece.toList.takeWhile Char.isDigit
    let after := String.ofList (piece.toList.drop digits.length)
    pre ++ if !digits.isEmpty && after.startsWith post then "N" ++ after else piece)

#guard maskNumberAfter "rows 1 and 2 of a table" "rows " == "rows N and 2 of a table"
#guard maskNumberAfter "has 12 behaviours, has 3 checks" "has " " behaviours" == "has N behaviours, has 3 checks"

/-- A difference without its line, names and values, to group the
specs that differ alike. Of the numbers, it masks, as `N`, only those that
name a place or count what a spec happens to have: a line (`line N`), a
row or an arm of a table or a `match` (`row N`, `rows N and N`, `arm N`,
`arms N and N`), and a count of behaviours (`has N behaviours`). Every
other number is part of the kind, so that two differences that it
tells apart stay apart: an exit code, a size bound, and the counts of
checks of a summary or a note. -/
def signature (f : String) : String := Id.run do
  let f := match f.splitOn ": " with
    | l :: rest => if l.startsWith "line " then ": ".intercalate rest else f
    | [] => f
  let mut out := ""
  let mut inQuote := false
  for c in f.toList do
    if c == '`' then
      inQuote := !inQuote
      if inQuote then out := out ++ "`_`"
    else if !inQuote then out := out.push c
  for pre in ["line ", "row ", "rows ", "arm ", "arms ", "rows N and ", "arms N and "] do
    out := maskNumberAfter out pre
  out := maskNumberAfter out "has " " behaviours"
  let masked := maskBetween out "for the input " [", no outputs", ", it can be"]
  return maskBetween (maskBetween masked "fren says " [", Lean says"]) "Lean says " []

/-! ### Known differences -/

/-- A difference that the front ends are known to make on a spec, until
its issue is fixed: the spec's mode and seed, the difference as `compare`
gives it, line and names included, and the issue that tracks it. -/
structure Known where
  mode : Mode
  seed : Nat
  difference : String
  issue : Nat
  /-- As a kind for `--avoid-known` (`knownKind`), it is known only after a
  static error: on a spec where both front ends report one, at the same
  line and column (`sharedStaticErrorLines`), at or before the
  difference's line, which their recovery from the error explains. -/
  afterStaticError : Bool := false
  /-- As a kind, it is known only on a spec that also has a difference of
  this kind (a `signature`), which explains it. -/
  alongside? : Option String := none
  /-- Whether the kind of `alongside?` must be at the same line, so that it
  explains the difference at that check only. -/
  onItsLine : Bool := false
  deriving BEq

/-- The kind of the `fren` command's internal error on a formula that its
evaluator cannot read (#493), which explains the differences listed
`alongside?` it. -/
def evaluatorUnread : String :=
  "only fren reports error[-]: internal error: the evaluator does not know the meaning of a formula of `_`"

/-- The differences that the front ends make on the specs of the corpus
(`corpusSpecs?`) on `main`, each with its issue: #493 and its sub-issues,
and #555. As with `knownColumnDifferences` in `FrenTestMain`, the corpus
fails on a difference that is not listed, on a listed one that no longer
occurs, and on one that occurs more often than it is listed, so that the
list only shrinks. A change to the generator leaves every seed's spec as
it was, up to what it appends (`Wide.genWideCuts`), so this list stays as
it is; never list a difference here to absorb a changed corpus. A
difference that the run of fresh seeds on `main` finds is listed with its
seed and mode, and the corpus then checks that seed too (`listedOutside`).
`--avoid-known` counts a spec whose every difference is of a kind (its
`signature`) listed here for `--avoid-known`, or in `knownKinds`, as
known. An entry holds the
whole difference: its line and column, the names that a front end gives
its own facts, as Lean's `f0.equation0.1`, and the message's wording. A
change to any of those, such as to where a front end places a message or
to the generated text before it on its line, makes an unlisted and a
vanished difference on the same line, which is relisted, not a
regression; on a spec with an undecided check, only the unlisted one
shows, since a vanished entry does not fail there. -/
def knownDifferences : List Known :=
  -- Lean reports `ob1?`, an output that a table in an expectation reads,
  -- as unknown, in a spec with other errors (F0391 in `c0`), once any
  -- later item with checks is declared after it, even a constant, as
  -- `sitesDecls` and `contractTable` declare (also on main's front ends,
  -- which agree on the spec without them).
  [{ mode := {}, seed := 28, issue := 493,
     difference := "line 21:35: only Lean reports error: Unknown identifier `ob1?`" },
   { mode := {}, seed := 153, issue := 478,
     difference := "line 37:28: only fren reports error[F0714]: this is outside the decidable core: \
       a relational operator over a type that is not finite quantifies over its values" },
   -- Lean reports `F0743` twice on `((({(1, 2)}).inverse).domain).card`.
   { mode := { avoidKnown := true }, seed := 41, issue := 493,
     difference := "line 23:16: only Lean reports warning: this chain of methods has a shorter form" },
   -- Kinds of #493 and #295 that `--avoid-known` found on fresh seeds:
   -- those below 2000000 in runs on `main` (`fuzz-frontends`), the others in
   -- a run of 13,800 seeds from 3000000, at 8a0c3978.
   -- After a static error, the front ends recover differently: only `fren`
   -- reports the lints of what follows it, and only Lean reports an error
   -- of its own (`Type mismatch`, `Application type mismatch`, `cannot
   -- find`, or a lint).
   { mode := { avoidKnown := true }, seed := 1156065, issue := 493, afterStaticError := true,
     difference := "line 49:16: only fren reports warning[F0712]: this `Bool` expression can be simpler" },
   { mode := { avoidKnown := true }, seed := 1156065, issue := 493, afterStaticError := true,
     difference := "line 48:34: only fren reports warning[F0710]: unused variable `n`" },
   { mode := { avoidKnown := true }, seed := 1160095, issue := 493, afterStaticError := true,
     difference := "line 102:33: only fren reports warning[F0739]: parentheses directly around parentheses" },
   { mode := { avoidKnown := true }, seed := 1160095, issue := 493, afterStaticError := true,
     difference := "line 102:11: only fren reports warning[F0710]: unused parameter `x0`" },
   { mode := { avoidKnown := true }, seed := 1160095, issue := 493, afterStaticError := true,
     difference := "line 100:37: only Lean reports error: Type mismatch" },
   { mode := { avoidKnown := true }, seed := 3000319, issue := 493, afterStaticError := true,
     difference := "line 44:36: only fren reports warning[F0737]: both branches of `if` are written the \
       same" },
   { mode := { avoidKnown := true }, seed := 3000319, issue := 493, afterStaticError := true,
     difference := "line 44:34: only fren reports warning[F0739]: parentheses directly around parentheses" },
   { mode := { avoidKnown := true }, seed := 3000319, issue := 493, afterStaticError := true,
     difference := "line 44:14: only fren reports warning[F0710]: unused parameter `x`" },
   { mode := { avoidKnown := true }, seed := 3102696, issue := 493, afterStaticError := true,
     difference := "line 58:41: only Lean reports error: Type mismatch" },
   { mode := { avoidKnown := true }, seed := 3102696, issue := 493, afterStaticError := true,
     difference := "line 60:28: only Lean reports error: cannot find `Small` in this scope" },
   { mode := { avoidKnown := true }, seed := 3103202, issue := 493, afterStaticError := true,
     difference := "line 28:103: only Lean reports error: Application type mismatch: The argument" },
   { mode := { avoidKnown := true }, seed := 3100624, issue := 493, afterStaticError := true,
     difference := "line 41:18: only Lean reports warning: `n1` is never negative, so it can be a `Nat`" },
   -- After a static error, only Lean reports a name as an `Unknown
   -- identifier`.
   { mode := { avoidKnown := true }, seed := 1159002, issue := 295, afterStaticError := true,
     difference := "line 17:61: only Lean reports error: Unknown identifier `b0?`" },
   { mode := { avoidKnown := true }, seed := 3102505, issue := 295, afterStaticError := true,
     difference := "line 25:18: only fren reports warning[F0736]: the condition and the body of `when` are \
       written the same" },
   { mode := { avoidKnown := true }, seed := 3102505, issue := 295, afterStaticError := true,
     difference := "line 25:18: only fren reports warning[F0712]: this `Bool` expression can be simpler" },
   { mode := { avoidKnown := true }, seed := 3102505, issue := 295, afterStaticError := true,
     difference := "line 21:35: only Lean reports error: Unknown identifier `on2`" },
   { mode := { avoidKnown := true }, seed := 3101311, issue := 295, afterStaticError := true,
     difference := "line 49:16: only fren reports warning[F0761]: this expectation mentions no variable" },
   { mode := { avoidKnown := true }, seed := 3101311, issue := 295, afterStaticError := true,
     difference := "line 43:34: only fren reports warning[F0710]: unused variable `n`" },
   { mode := { avoidKnown := true }, seed := 3101311, issue := 295, afterStaticError := true,
     difference := "line 37:24: only Lean reports error: Unknown identifier `b1?`" },
   { mode := { avoidKnown := true }, seed := 3104511, issue := 295, afterStaticError := true,
     difference := "line 50:5: only fren reports warning[F0719]: defined output `k1` is the same in every \
       behaviour" },
   { mode := { avoidKnown := true }, seed := 3104511, issue := 295, afterStaticError := true,
     difference := "line 48:43: only fren reports warning[F0710]: unused variable `b?`" },
   { mode := { avoidKnown := true }, seed := 3104511, issue := 295, afterStaticError := true,
     difference := "line 48:47: only fren reports warning[F0710]: unused variable `n`" },
   { mode := { avoidKnown := true }, seed := 3104511, issue := 295, afterStaticError := true,
     difference := "line 42:59: only Lean reports error: Unknown identifier `s1`" },
   -- Only Lean notes that two clauses force an output both ways.
   { mode := { avoidKnown := true }, seed := 1157147, issue := 493,
     difference := "line 11: for the same input, fren notes #[], Lean notes #[line 18: `q1` forces ob1? = \
       false, but `q2` forces ob1? = true]" },
   { mode := { avoidKnown := true }, seed := 1158050, issue := 493,
     difference := "line 9: for the same input, fren notes #[], Lean notes #[line 20: `q0` forces ob1? = \
       true, but `q1` forces ob1? = false]" },
   { mode := { avoidKnown := true }, seed := 3000892, issue := 493,
     difference := "line 10: for the same input, fren notes #[], Lean notes #[line 19: `q1` forces ob0? = \
       false, but `q2` forces ob0? = true]" },
   { mode := { avoidKnown := true }, seed := 3102156, issue := 493,
     difference := "line 4: for the same input, fren notes #[], Lean notes #[line 13: `q1` forces ob0? = \
       true, but `q2` forces ob0? = false]" },
   -- Only `fren` reports F0111 on `K0.card` in a guard of a `match` arm.
   { mode := { avoidKnown := true }, seed := 1157298, issue := 493,
     difference := "line 34:45: only fren reports error[F0111]: `K0.card` is not a single name (and Lean \
       reports no parse error at or just before that line, in its item)" },
   -- Only Lean notes why unsatisfiable assumptions cannot hold.
   { mode := { avoidKnown := true }, seed := 1160124, issue := 493,
     difference := "line 21:13: only Lean reports info: `a0` cannot hold." },
   { mode := { avoidKnown := true }, seed := 1160124, issue := 493,
     difference := "line 10:88: only Lean reports info: Both operands of `a0` cannot be true: the stated \
       premises require `a0.fz::f1?@1.2` to be false." },
   { mode := { avoidKnown := true }, seed := 1160124, issue := 493,
     difference := "line 10:33: only Lean reports info: Both operands of `a0` cannot be false: the stated \
       premises require `a0.fz::f1?@1.1` to be true." },
   -- The CLI's evaluator cannot read a formula that Lean counts the
   -- behaviours of.
   { mode := { avoidKnown := true }, seed := 1160173, issue := 493,
     difference := "line 28:10: only fren reports error[-]: internal error: the evaluator does not know the \
       meaning of a formula of `fz::c1`" },
   { mode := { avoidKnown := true }, seed := 1160173, issue := 493, alongside? := some evaluatorUnread,
     difference := "line 28:10: only Lean reports error: `fz::c1` has 442137500 behaviours up to size 2, too \
       many to enumerate" },
   { mode := { avoidKnown := true }, seed := 1160173, issue := 493, alongside? := some evaluatorUnread,
     difference := "exit: fren exits 1, and Lean's messages call for 2" },
   -- Run 267 found these on main; both seeds reproduce at dd28d924,
   -- before #817. Lean cannot decide the expectation, while `fren`
   -- reports its dependency or failure (#493).
   { mode := { avoidKnown := true }, seed := 1267162, issue := 493, onItsLine := true,
     alongside? := some "only Lean reports warning: could not decide whether `_` holds: INCOMPLETE",
     difference := "line 141:12: only fren reports warning[F0664]: `fz::zpn::zpe1` rests on the realizability of \
       `fz::zpn`, which did not pass" },
   { mode := { avoidKnown := true }, seed := 1267162, issue := 493, onItsLine := true,
     alongside? := some "only fren reports warning[F0664]: `_` rests on the realizability of `_`, which did not pass",
     difference := "line 141:12: only Lean reports warning: could not decide whether `fz::zpn::zpe1` holds: INCOMPLETE" },
   { mode := { avoidKnown := true }, seed := 1267186, issue := 493, onItsLine := true,
     alongside? := some "only Lean reports warning: could not decide whether `_` holds",
     difference := "line 167:12: only fren reports error[F0603]: expectation `fz::gr_apps::gr1` does not hold" },
   { mode := { avoidKnown := true }, seed := 1267186, issue := 493, onItsLine := true,
     alongside? := some "only fren reports error[F0603]: expectation `_` does not hold",
     difference := "line 167:12: only Lean reports warning: could not decide whether `fz::gr_apps::gr1` holds" },
   { mode := { avoidKnown := true }, seed := 1267186, issue := 493,
     alongside? := some "only fren reports error[F0603]: expectation `_` does not hold",
     difference := "summary: fren says `57 passed (1 by bounded enumeration), 17 failed, 18 inconclusive, 0 redundant`, \
       Lean says `57 passed (1 by bounded enumeration), 16 failed, 19 inconclusive, 0 redundant`" }]

/-- Whether the kind `s` (a `signature`) is of the pattern `p`, where each
`*` stands for any text, and every other character for itself. -/
partial def kindMatches (p s : String) : Bool :=
  go p.toList s.toList
where
  go : List Char → List Char → Bool
    | [], s => s.isEmpty
    | '*' :: p, s => go p s || match s with
      | [] => false
      | _ :: s => go ('*' :: p) s
    | c :: p, d :: s => c == d && go p s
    | _ :: _, [] => false

#guard kindMatches "only fren reports warning[F07*"
  "only fren reports warning[F0712]: this `_` expression can be simpler"
#guard !kindMatches "only fren reports warning[F07*" "only fren reports warning[F0608]: could not decide"
#guard kindMatches "a * b * c" "a x b y b z c"
#guard !kindMatches "a * c" "a x c d"
#guard kindMatches "exit" "exit" && !kindMatches "exit" "exits"

/-- A kind of difference that an issue tracks, which runs of fresh seeds
find, but that no spec of the corpus has, so that `knownDifferences` does
not list it: `--avoid-known` counts it as known, like the kinds that
`knownDifferences` lists, and `lake test` does not check it. -/
structure KnownKind where
  /-- The kind, as a `signature`, where `*` stands for any text
  (`kindMatches`). -/
  kind : String
  issue : Nat
  /-- The spec where a run found it first, to reproduce it with. -/
  mode : Mode := { avoidKnown := true }
  seed : Nat
  /-- As `Known.afterStaticError`. -/
  afterStaticError : Bool := false
  /-- As `Known.alongside?`, a kind that may have `*`s too. -/
  alongside? : Option String := none
  /-- Whether the kind of `alongside?` must be at the same line, so that it
  explains the difference at that check only. -/
  onItsLine : Bool := false
  /-- A condition on the difference itself, given the spec's differences,
  for what its kind masks: the names, as which clauses a conflict core
  has (`leanCoreHasMore`), or which procedure a message is about
  (`aboutUnreadProcedure`). -/
  test? : Option (Array String → String → Bool) := none

/-- The kind of Lean's failure, through lean-smt, on a query that has the
same closed application twice under different binders (#493), whatever
it could not decide. -/
def leanSmtArrow : String :=
  "only Lean reports warning: could not decide whether * cvc5.Error.error \
    \"Symbol '->' not declared as a variable\""

/-- The kind of Lean's failure to enumerate a procedure that the `fren`
command enumerates (#485), which explains the inconclusive results and
the summary that only `fren` gives there. -/
def leanEnumerationFails : String :=
  "only Lean reports error: internal error: enumerating `_` in Lean failed: failed to synthesize"

/-- The kind of the `fren` command's warning that a trait's expectation
rests on an uninterpreted function's contract whose realizability did not
pass, which Lean does not give (#493). -/
def traitRestsOnContract : String :=
  "only fren reports warning[F0664]: `_` rests on the realizability of the contract of `_`, which did not pass"

/-- The clauses of one side of a conflict core, as `compare` writes it
after `no outputs satisfy`: `` `q2` `` or `` `q0`, `q1` and `q2` ``, each
name in backticks, separated by `, ` or ` and `. -/
def coreClauses? (side : String) : Option (List String) := do
  let parts := side.splitOn "`"
  guard (parts.length ≥ 3 && parts.length % 2 == 1 && parts.head? == some "" && parts.getLast? == some "")
  let inner := (parts.drop 1).dropLast
  let names := inner.zipIdx.filterMap fun (p, i) => if i % 2 == 0 then some p else none
  let seps := inner.zipIdx.filterMap fun (p, i) => if i % 2 == 1 then some p else none
  guard (names.all (!·.isEmpty) && seps.all (· ∈ [", ", " and "]))
  return names

#guard coreClauses? "`q2`" == some ["q2"]
#guard coreClauses? "`q0`, `q1` and `q2`" == some ["q0", "q1", "q2"]
#guard coreClauses? "`q0` or `q1`" == none
#guard coreClauses? "q0" == none

/-- The difference `f` is a conflict core where `fren`'s clauses are a
proper subset of Lean's: for the same input, `fren` says `no outputs
satisfy` some clauses, and Lean says it of those and more (#493). -/
def leanCoreHasMore (_ : Array String) (f : String) : Bool := Id.run do
  let pre := "for the same input, fren says `no outputs satisfy "
  let mid := "`, Lean says `no outputs satisfy "
  let some rest := (f.splitOn pre)[1]? | return false
  let [frenSide, leanSide] := rest.splitOn mid | return false
  let some leanSide := leanSide.dropSuffix? "`" | return false
  let (some fren, some lean) := (coreClauses? frenSide, coreClauses? leanSide.toString) | return false
  return fren.all (· ∈ lean) && lean.any (· ∉ fren)

section
private def core (fren lean : String) : String :=
  s!"line 43: for the same input, fren says `no outputs satisfy {fren}`, Lean says `no outputs satisfy {lean}`"
#guard leanCoreHasMore #[] (core "`q2`" "`q0`, `q1` and `q2`")
#guard leanCoreHasMore #[] (core "`q0` and `q2`" "`q0`, `q1` and `q2`")
-- Not where the cores are disjoint, equal, or `fren`'s is the larger.
#guard !leanCoreHasMore #[] (core "`q0` and `q2`" "`q1` and `q3`")
#guard !leanCoreHasMore #[] (core "`q0`, `q1` and `q2`" "`q3` and `q4`")
#guard !leanCoreHasMore #[] (core "`q0` and `q1`" "`q1` and `q0`")
#guard !leanCoreHasMore #[] (core "`q0`, `q1` and `q2`" "`q2`")
#guard !leanCoreHasMore #[] (core "`q2`" "`q0` and `q3`")
end

/-- The procedure that the `fren` command's evaluator cannot read a
formula of, in a difference of the kind `evaluatorUnread`. -/
def unreadProcedure? (g : String) : Option String := do
  guard (signature g == evaluatorUnread)
  let name ← (g.splitOn "a formula of `")[1]?
  (name.dropSuffix? "`").map (·.toString)

/-- The subject of the message of the difference `f`: its first name in
backticks. -/
def subject? (f : String) : Option String := (f.splitOn "`")[1]?

/-- The difference `f` is about the procedure `p`, or one of its items: its
subject is `p` or a name in `p`. -/
def isAbout (p f : String) : Bool := (subject? f).any fun n => n == p || n.startsWith s!"{p}::"

/-- The difference `f` is about a procedure that the `fren` command's
evaluator cannot read a formula of, by a difference among `found`: what
Lean reports of that procedure (#484). -/
def aboutUnreadProcedure (found : Array String) (f : String) : Bool :=
  found.any fun g => (unreadProcedure? g).any (isAbout · f)

/-- The procedure that Lean fails to enumerate, in a difference of the
kind `leanEnumerationFails`. -/
def enumerationFailedProcedure? (g : String) : Option String := do
  guard (signature g == leanEnumerationFails)
  let name ← (g.splitOn "enumerating `")[1]?
  return (name.splitOn "`")[0]!

/-- The difference `f` is about a procedure that Lean fails to enumerate,
by a difference among `found`: what only `fren` reports of it (#485). -/
def aboutUnenumeratedProcedure (found : Array String) (f : String) : Bool :=
  found.any fun g => (enumerationFailedProcedure? g).any (isAbout · f)

/-- The difference `f` is a check's result, of an `F06xx` code. -/
def checkResult (_ : Array String) (f : String) : Bool := (f.splitOn "reports warning[F06").length > 1
  || (f.splitOn "reports error[F06").length > 1 || (f.splitOn "reports info[F06").length > 1

section
private def unread : String :=
  "line 13:10: only fren reports error[-]: internal error: the evaluator does not know the meaning of a formula of `fz::c0`"
#guard unreadProcedure? unread == some "fz::c0"
#guard aboutUnreadProcedure #[unread] "line 40:12: only Lean reports warning: `fz::c0::x0` rests on the realizability of \
  `fz::c0`, which did not pass"
#guard aboutUnreadProcedure #[unread] "line 13:10: only Lean reports error: `fz::c0` is not realizable"
-- Not what Lean reports of another procedure, nor of one whose name only
-- starts the same, nor of one that only mentions it.
#guard !aboutUnreadProcedure #[unread] "line 50:10: only Lean reports error: `fz::c1` is not realizable"
#guard !aboutUnreadProcedure #[unread] "line 50:10: only Lean reports error: `fz::c1` calls `fz::c0`, so x"
#guard !aboutUnreadProcedure #[unread] "line 50:10: only Lean reports error: `fz::c01` is not realizable"
#guard !aboutUnreadProcedure #[] "line 13:10: only Lean reports error: `fz::c0` is not realizable"
end

/-- The difference `f` is no check's result: a static error's, not one of
the `F06xx` codes of checks. -/
def notCheckResult (_ : Array String) (f : String) : Bool := (f.splitOn "reports error[F06").length == 1

/-- The kinds of the issues that runs of `--avoid-known` on fresh seeds
found, beyond those that `knownDifferences` lists: `fuzz-frontends` in
`lean ci` fails on a difference of any other kind. Each entry gives the
first seed where a run found it. A kind is listed here once its issue
records it, with the seed, under the most specific issue that tracks it,
#493 only where none does; when the issue is fixed, its kinds are
removed. -/
def knownKinds : List KnownKind :=
  -- After a static error, only `fren` reports the lints of what follows
  -- it (#493): any lint, as `knownDifferences` lists a few.
  [{ kind := "only fren reports warning[F07*", issue := 493, seed := 1175152, afterStaticError := true },
   { kind := "only fren reports warning[F08*", issue := 493, seed := 6000809, afterStaticError := true },
   -- and its static errors after one that both report, as the decidable
   -- core's: not a check's result.
   { kind := "only fren reports error[F0*", issue := 493, seed := 6000809, afterStaticError := true,
     test? := some notCheckResult },
   -- Only Lean notes why an assumption's operands cannot both hold, in
   -- any wording (#493; `knownDifferences` lists two at seed 1160124).
   { kind := "only Lean reports info: Both operands of `_` cannot be *", issue := 493, seed := 1190787 },
   -- For the same input, Lean gives a realizability conflict core that
   -- has `fren`'s clauses and more (#493).
   { kind := "for the same input, fren says …, Lean says …", issue := 493, seed := 6001014,
     test? := some leanCoreHasMore },
   -- Only `fren` reports that an assumption constrains only parameters
   -- that nothing uses (F0792, #493).
   { kind := "only fren reports warning[F0792]: the assumption `_` constrains only parameters that nothing uses",
     issue := 493, seed := 1175274 },
   -- and on other specs, only Lean does.
   { kind := "only Lean reports warning: the assumption `_` constrains only parameters that nothing uses",
     issue := 493, seed := 1182701 },
   -- The CLI's evaluator cannot read a formula of a procedure that Lean
   -- enumerates (#484), so only Lean reports what enumerating that
   -- procedure found, and what rests on it, at any size bound; and the
   -- summaries differ.
   { kind := "only Lean reports *", issue := 484, seed := 1187360, alongside? := some evaluatorUnread,
     test? := some aboutUnreadProcedure },
   { kind := "summary: fren says …, Lean says …", issue := 484, seed := 1187360, alongside? := some evaluatorUnread },
   -- A trait's check that Lean cannot decide (`leanSmtArrow`): what only
   -- `fren` reports of the check at its line, as that it rests on the
   -- trait's laws (F0665), on its assumptions and calls (F0664), that its
   -- assumptions contradict each other (F0602), or that an arm is never
   -- taken (F0626), and so the summaries' counts (#493).
   { kind := leanSmtArrow, issue := 493, seed := 1179170 },
   { kind := "only fren reports *", issue := 493, seed := 1179170, alongside? := some leanSmtArrow, onItsLine := true,
     test? := some checkResult },
   { kind := "summary: fren says …, Lean says …", issue := 493, seed := 1179061, alongside? := some leanSmtArrow },
   -- A trait's expectation rests on a contract whose realizability did
   -- not pass: only `fren` warns, and counts it inconclusive (#493).
   { kind := traitRestsOnContract, issue := 493, seed := 1179203 },
   { kind := "summary: fren says …, Lean says …", issue := 493, seed := 1179203,
     alongside? := some traitRestsOnContract },
   -- Lean fails to enumerate a procedure (#485), so only `fren` reports
   -- what enumerating it found, and what rests on it.
   { kind := leanEnumerationFails, issue := 485, seed := 1175253 },
   { kind := "only fren reports warning[F0608]: could not decide whether *", issue := 485, seed := 1175253,
     alongside? := some leanEnumerationFails, test? := some aboutUnenumeratedProcedure },
   { kind := "only fren reports info[F0646]: * checks of `_` hold for every behaviour up to size *", issue := 485,
     seed := 1175253, alongside? := some leanEnumerationFails, test? := some aboutUnenumeratedProcedure },
   { kind := "only fren reports warning[F0664]: * rests on the realizability of `_`, which did not pass",
     issue := 485, seed := 1175253, alongside? := some leanEnumerationFails, test? := some aboutUnenumeratedProcedure },
   { kind := "summary: fren says …, Lean says …", issue := 485, seed := 1175253,
     alongside? := some leanEnumerationFails }]

/-- The line of the difference `f`, if it has one: `line N:` or `line
N:COL:` at its start. -/
def differenceLine? (f : String) : Option Nat := do
  let first ← (f.splitOn ": ").head?
  let rest ← first.dropPrefix? "line "
  (rest.toString.splitOn ":").head?.bind String.toNat?

#guard differenceLine? "line 48:34: only fren reports warning[F0710]: unused variable `n`" == some 48
#guard differenceLine? "line 11: for the same input, fren notes #[]" == some 11
#guard differenceLine? "exit: fren exits 1, and Lean's messages call for 2" == none

/-- The issue of the known kind of the difference `f`, on a spec whose
differences are `found` and where both front ends report static errors
at the lines `staticLines` (`sharedStaticErrorLines`): a kind that `knownDifferences` lists for a seed
of `--avoid-known`, of either generator, or one of `knownKinds`, where
`mode` is of `--avoid-known` too: on the fresh seeds that CI checks with
it, those kinds go unchecked. An entry that holds only after a static
error (`afterStaticError`) matches only where one is at or before `f`'s
line, and one that holds only alongside another kind (`alongside?`) only
where `found` has that kind, on the same line when `onItsLine` is set;
one with a `test?`, only where the
difference passes it. -/
def knownIssue? (mode : Mode) (staticLines : Array Nat) (found : Array String) (f : String) : Option Nat :=
  let sig := signature f
  let holds (afterStaticError : Bool) (alongside? : Option String) (onItsLine := false) :=
    (!afterStaticError || (differenceLine? f).any fun l => staticLines.any (· ≤ l))
      && alongside?.all fun a => found.any fun g =>
        kindMatches a (signature g) && (!onItsLine || (differenceLine? f).isSome && differenceLine? g == differenceLine? f)
  if !mode.avoidKnown then none
  else match knownDifferences.find? (fun k =>
      k.mode.avoidKnown && signature k.difference == sig && holds k.afterStaticError k.alongside? k.onItsLine) with
    | some k => some k.issue
    | none =>
      (knownKinds.find? fun k =>
        kindMatches k.kind sig && holds k.afterStaticError k.alongside? k.onItsLine && k.test?.all (· found f)).map
        (·.issue)

/-- Whether the difference `f` is of a known kind (`knownIssue?`). -/
def knownKind (mode : Mode) (staticLines : Array Nat) (found : Array String) (f : String) : Bool :=
  (knownIssue? mode staticLines found f).isSome

section
private def known (f : String) (staticLines : Array Nat := #[]) (found : Array String := #[f])
    (mode : Mode := { avoidKnown := true }) : Bool :=
  knownKind mode staticLines found f
#guard known "line 23:16: only Lean reports warning: this chain of methods has a shorter form"
#guard known "line 23:16: only Lean reports warning: this chain of methods has a shorter form"
  (mode := { avoidKnown := true, guards := true })
#guard !known "line 23:16: only Lean reports warning: this chain of methods has a shorter form" (mode := {})
-- A kind listed only for the default generator is not known to
-- `--avoid-known`.
#guard !known "line 37:28: only fren reports error[F0714]: this is outside the decidable core: \
  a relational operator over a type that is not finite quantifies over its values"
-- A lint that only `fren` reports is known after a static error, which
-- explains it, and not on a spec without one, or with one only after it.
#guard known "line 48:34: only fren reports warning[F0710]: unused variable `n`" #[12]
#guard !known "line 48:34: only fren reports warning[F0710]: unused variable `n`"
#guard !known "line 48:34: only fren reports warning[F0710]: unused variable `n`" #[50]
-- An exit code that the evaluator's internal error explains is known only
-- alongside that error.
#guard !known "exit: fren exits 1, and Lean's messages call for 2"
#guard known "exit: fren exits 1, and Lean's messages call for 2"
  (found := #["exit: fren exits 1, and Lean's messages call for 2", "line 13:10: only fren reports error[-]: \
    internal error: the evaluator does not know the meaning of a formula of `fz::c0`"])
-- A verdict count on its own, and another exit code, are no known kind, so
-- a spec that has one is a finding.
#guard !known "summary: fren says `15 passed, 19 failed, 1 inconclusive, 0 redundant`, Lean says `14 passed, \
  20 failed, 1 inconclusive, 0 redundant`" #[1]
-- A conflict core is known only where Lean's has more clauses than `fren`'s.
#guard known "line 23: for the same input, fren says `no outputs satisfy `q2``, Lean says `no outputs \
  satisfy `q0`, `q1` and `q2``"
#guard !known "line 23: for the same input, fren says `no outputs satisfy `q0` and `q2``, Lean says `no outputs \
  satisfy `q2``"
#guard !known "exit: fren exits 0, and Lean's messages call for 1" #[1]
-- Of `knownKinds`: any lint that only `fren` reports after a static error,
-- of a code that `knownDifferences` does not list, but no other warning.
#guard known "line 21:25: only fren reports warning[F0736]: both operands of `=` are written the same" #[11]
-- A static error that only `fren` reports, with no earlier one that both
-- report, is a finding; and a check's result is none of this kind.
#guard known "line 53:21: only fren reports error[F0307]: nonlinear arithmetic is not supported" #[42]
#guard !known "line 53:21: only fren reports error[F0307]: nonlinear arithmetic is not supported"
#guard !known "line 53:21: only fren reports error[F0603]: expectation `fz::c0::e` does not hold" #[42]
-- The pairs from seeds 1267162 and 1267186 excuse only their own line:
-- an inconclusive expectation elsewhere cannot hide a decided result.
section
private def failed : String :=
  "line 53:21: only fren reports error[F0603]: expectation `fz::c0::e` does not hold"
private def rests : String :=
  "line 53:21: only fren reports warning[F0664]: `fz::c0::e` rests on the realizability of `fz::c0`, which did not pass"
private def unknown : String :=
  "line 53:21: only Lean reports warning: could not decide whether `fz::c0::e` holds"
private def incomplete : String := unknown ++ ": INCOMPLETE"
#guard known failed (found := #[failed, unknown]) && known unknown (found := #[failed, unknown])
#guard known rests (found := #[rests, incomplete]) && known incomplete (found := #[rests, incomplete])
#guard !known failed (found := #[failed, unknown.replace "line 53:" "line 54:"])
#guard !known rests (found := #[rests, incomplete.replace "line 53:" "line 54:"])
#guard !known unknown (found := #[failed.replace "line 53:" "line 54:", unknown])
#guard !known incomplete (found := #[rests.replace "line 53:" "line 54:", incomplete])
end
#guard !known "line 21:25: only fren reports warning[F0736]: both operands of `=` are written the same"
#guard known "line 10:33: only Lean reports info: Both operands of `a0` cannot be false: this would require `b0?` to \
  equal false, while `a1` requires `b0?` to equal true."
#guard !known "line 65:72: only fren reports warning[F0806]: this guard is always `false`, so the arm is never taken"
#guard known "line 65:72: only fren reports warning[F0806]: this guard is always `false`, so the arm is never taken"
  #[46]
#guard known "line 22:12: only fren reports warning[F0792]: the assumption `a0` constrains only parameters that \
  nothing uses"
#guard !known "line 31:10: only fren reports warning[F0608]: could not decide whether `fz::c0` is realizable: no \
  outputs up to size 2, but larger ones may exist" #[1]
-- A trait's expectation that Lean cannot decide: the warning that only
-- `fren` gives, and the summary, are known only alongside Lean's failure.
section
private def arrow : String := "line 95:12: only Lean reports warning: could not decide whether `fz::Tr::e0` holds: \
  cvc5.Error.error \"Symbol '->' not declared as a variable\""
private def laws : String :=
  "line 95:12: only fren reports warning[F0665]: `fz::Tr::e0` rests on the laws of `fz::Tr`, whose consistency is \
    not checked"
private def summary : String := "summary: fren says `12 passed, 2 failed, 2 inconclusive, 0 redundant`, Lean says \
  `11 passed, 2 failed, 3 inconclusive, 0 redundant`"
#guard known arrow
#guard known laws (found := #[laws, arrow]) && known summary (found := #[laws, arrow, summary])
#guard !known laws && !known summary (found := #[laws, summary])
-- only at the line of Lean's failure.
#guard !known laws (found := #[laws, arrow.replace "line 95:12" "line 96:12"])
-- and only a check's result: not a static error nor a lint at its line.
#guard !known "line 95:40: only fren reports error[F0307]: nonlinear arithmetic is not supported"
  (found := #["line 95:40: only fren reports error[F0307]: nonlinear arithmetic is not supported", arrow])
#guard !known "line 95:40: only fren reports warning[F0806]: this guard is always `false`, so the arm is never taken"
  (found := #["line 95:40: only fren reports warning[F0806]: this guard is always `false`, so the arm is never taken",
    arrow])
#guard knownIssue? { avoidKnown := true } #[] #[laws, arrow] laws == some 493
#guard knownIssue? {} #[] #[laws, arrow] laws == none
-- Lean's failure is known whatever it could not decide.
#guard known "line 61:12: only Lean reports warning: could not decide whether the assumptions and calls of \
  `fz::Tr::e1` can hold together with its trait's laws: cvc5.Error.error \"Symbol '->' not declared as a variable\""
end
-- The evaluator's failure explains what only Lean's enumeration reports,
-- and nothing else.
#guard known "line 40:12: only Lean reports warning: `fz::c0::x0` rests on the realizability of `fz::c0`, which did \
  not pass" (found := #["line 40:12: only Lean reports warning: `fz::c0::x0` rests on the realizability of `fz::c0`, \
  which did not pass", "line 13:10: only fren reports error[-]: internal error: the evaluator does not know the \
  meaning of a formula of `fz::c0`"])
-- of that procedure only.
#guard !known "line 50:12: only Lean reports error: `fz::c1` is not realizable" (found := #["line 50:12: only Lean \
  reports error: `fz::c1` is not realizable", "line 13:10: only fren reports error[-]: internal error: the evaluator \
  does not know the meaning of a formula of `fz::c0`"])
#guard !known "line 40:12: only Lean reports warning: `fz::c0::x0` rests on the realizability of `fz::c0`, which did \
  not pass"
-- Lean's failure to enumerate explains what only `fren` reports of that
-- procedure, at any size bound, and is #485's; but not of another.
section
private def enumFails : String :=
  "line 31:10: only Lean reports error: internal error: enumerating `fz::c0` in Lean failed: failed to synthesize"
private def ofEnum (f : String) : Option Nat := knownIssue? { avoidKnown := true } #[] #[enumFails, f] f
#guard enumerationFailedProcedure? enumFails == some "fz::c0"
#guard ofEnum "line 31:10: only fren reports info[F0646]: 7 checks of `fz::c0` hold for every behaviour up to size 3"
  == some 485
#guard ofEnum "line 31:10: only fren reports info[F0646]: 7 checks of `fz::c9` hold for every behaviour up to size 3"
  == none
#guard ofEnum "line 43:12: only fren reports warning[F0608]: could not decide whether `fz::c0::x0` is vacuous: no \
  witness up to size 2, but a larger one may exist" == some 485
#guard ofEnum "line 43:12: only fren reports warning[F0608]: could not decide whether `fz::c9` holds: INCOMPLETE" == none
#guard ofEnum "line 41:12: only fren reports warning[F0664]: `fz::c0::cx0` rests on the realizability of `fz::c0`, \
  which did not pass" == some 485
#guard ofEnum "line 41:12: only fren reports warning[F0664]: `fz::c9::cx0` rests on the realizability of `fz::c9`, \
  which did not pass" == none
end
end

-- The numbers that place a difference or count what the spec has are
-- masked; a code's digits and a name's are not.
#guard signature "line 28:10: only Lean reports error: `fz::c1` has 442137500 behaviours up to size 2, \
    too many to enumerate"
  == "only Lean reports error: `_` has N behaviours up to size 2, too many to enumerate"
#guard signature "line 11: for the same input, fren notes #[], Lean notes #[line 18: `q1` forces ob1? = false, \
    but `q2` forces ob1? = true]"
  == "for the same input, fren notes #[], Lean notes #[line N: `_` forces ob1? = false, but `_` forces ob1? = true]"
#guard signature "line 48:34: only fren reports warning[F0710]: unused variable `n`"
  == "only fren reports warning[F0710]: unused variable `_`"
#guard signature "line 3:1: only Lean reports error: rows 1 and 2 of a table in `f` may both hold"
  == signature "line 9:4: only Lean reports error: rows 2 and 3 of a table in `g` may both hold"
-- Every other number stays, so that differences that it tells apart stay
-- apart: exit codes, size bounds and counts of checks.
#guard signature "exit: fren exits 0, and Lean's messages call for 1"
  != signature "exit: fren exits 1, and Lean's messages call for 2"
#guard signature "line 1:1: only Lean reports info: 4 checks of `c` hold for every behaviour up to size 2"
  != signature "line 1:1: only Lean reports info: 3 checks of `c` hold for every behaviour up to size 2"
#guard signature "line 2:5: only Lean reports warning: could not decide whether `q` is vacuous: no witness up to size 2, \
    but a larger one may exist"
  != signature "line 2:5: only Lean reports warning: could not decide whether `q` is vacuous: no witness up to size 3, \
    but a larger one may exist"

end FrenTest.FuzzFrontends
