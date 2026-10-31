-- keep-sorted start
import FrenCore.Table
import FrenCore.Ty
-- keep-sorted end

/-!
# Patterns

The patterns of `match` arms and of pattern tests, once a front end has
resolved them (`Pat`), and the checks that a `match` is exhaustive and that
each of its arms and alternatives is reachable
(`Reqs/Lang/Expressions#matches`, `Reqs/Lang/Patterns`). Both front ends
resolve their syntax to `Pat` and call `checkMatch` and `checkPatternTest`,
so they accept and reject the same matches.

The checks are the usefulness algorithm of Maranget, "Warnings for pattern
matching" (JFP 2007): a vector of patterns is *useful* with respect to a
matrix of rows of patterns when some vector of values matches it and no row.
An arm is reachable when it is useful with respect to the arms before it,
and a `match` is exhaustive when `_` would not be useful after its last arm.
Each step of the algorithm looks at the first column, and is stated for one
kind of pattern at a time (`usefulStep`, `specializeHead`,
`signatureComplete`). Integers are split into intervals within which every
row behaves alike, so that a range is a finite or-pattern of intervals.
-/

namespace Fren.Core

open Lean (Name)

/-- The type of the value that a pattern matches, as patterns see it. -/
inductive PatTy where
  | bool
  | int
  /-- `Nat`: the integers that are at least 0. -/
  | nat
  | string
  /-- An enumeration, with its type arguments if it is generic. -/
  | enum (path : Name) (args : List PatTy)
  /-- The `k`th type parameter of a generic enumeration, in a payload's
  type, for which an instance's `k`th argument stands. -/
  | param (k : Nat)
  /-- A type that only `_` and binders match: a record, a set, ... -/
  | other
  deriving Inhabited, BEq, Repr

/-- Whether `t` is `Nat`. `PatTy`, whose type arguments are a `List`, has
no derived `DecidableEq` to decide `t = .nat` with. -/
def PatTy.isNat : PatTy → Bool
  | .nat => true
  | _ => false

@[simp] theorem PatTy.isNat_eq_true (t : PatTy) : t.isNat = true ↔ t = .nat := by
  cases t <;> simp [PatTy.isNat]

/-- `ty` as patterns see it. -/
partial def Ty.patTy (ty : Ty) : PatTy :=
  match ty with
  | .bool => .bool
  | .int => .int
  | .nat => .nat
  | .string => .string
  | .enum p args => .enum p (args.map (·.patTy))
  | .param k _ => .param k
  | _ => .other

/-- `t`, with the `k`th of `args` for each `.param k`. -/
partial def PatTy.subst (args : List PatTy) : PatTy → PatTy
  | .param k => args[k]?.getD .other
  | .enum p as => .enum p (as.map (·.subst args))
  | t => t

/-- The variants of each enumeration, each with its payload's types, which
mention its type parameters as `.param`. -/
abbrev Sigs := Name → Array (Name × Array PatTy)

/-- A pattern, resolved. -/
inductive Pat where
  /-- `_`, or a binder (`binder`): matches any value. -/
  | wild (binder : Bool := false)
  | bool (b : Bool)
  /-- The integers from `lo` to `hi`, both included; `none` is unbounded.
  A literal `n` is `n..=n`, and `a..b` is `a..=b - 1`. -/
  | int (lo hi : Option Int)
  | str (s : String)
  /-- The variant `idx` of an enumeration, with a pattern for each value of
  its payload. -/
  | ctor (idx : Nat) (args : Array Pat)
  /-- An or-pattern. -/
  | or (alts : Array Pat)
  deriving Inhabited

/-! ## Ranges -/

/-- The bounds of the range `lo..=hi`, or of `lo..hi` unless `inclusive`,
as the interval of the integers it contains. -/
def rangeInterval (lo hi : Option Int) (inclusive : Bool) : Option Int × Option Int :=
  (lo, if inclusive then hi else hi.map (· - 1))

/-- Whether a range matches no integer (`lang::range_pattern`). -/
def rangeEmpty (lo hi : Option Int) (inclusive : Bool) : Bool :=
  match lo, hi with
  | some l, some h => if inclusive then decide (h < l) else decide (h ≤ l)
  | _, _ => false

/-- Whether a range matches the integer `v` (`lang::range_pattern`). -/
def rangeMatches (lo hi : Option Int) (inclusive : Bool) (v : Int) : Bool :=
  lo.all (decide <| · ≤ v) && hi.all fun h => if inclusive then decide (v ≤ h) else decide (v < h)

/-- Whether the interval `inner` is within `outer`. -/
def intervalWithin (inner outer : Option Int × Option Int) : Bool :=
  (match outer.1, inner.1 with
    | none, _ => true
    | some _, none => false
    | some l, some l' => decide (l ≤ l')) &&
  (match outer.2, inner.2 with
    | none, _ => true
    | some _, none => false
    | some h, some h' => decide (h' ≤ h))

/-- The intervals that split the integers at the bounds of `ivs`, in order:
each interval of `ivs` is a union of them. -/
def splitIntervals (ivs : Array (Option Int × Option Int)) : Array (Option Int × Option Int) :=
  let cuts := (ivs.flatMap fun (lo, hi) => lo.toArray ++ (hi.map (· + 1)).toArray).qsort (· < ·)
  let cuts := cuts.foldl (init := #[]) fun acc c => if acc.back? == some c then acc else acc.push c
  match cuts[0]?, cuts.back? with
  | some first, some last =>
    #[(none, some (first - 1))] ++ (Array.range (cuts.size - 1)).map (fun i => (some cuts[i]!, some (cuts[i + 1]! - 1)))
      ++ #[(some last, none)]
  | _, _ => #[(none, none)]

/-! ## The rules, one kind of pattern at a time -/

/-- The kinds of pattern at the head of a vector (`lang::HeadKind`). -/
inductive HeadKind where
  | constructor
  | wildcard
  | or
  deriving Inhabited, BEq, DecidableEq, Repr

def Pat.headKind : Pat → HeadKind
  | .wild _ => .wildcard
  | .or _ => .or
  | _ => .constructor

/-- One step of usefulness (`lang::usefulness`): whether a vector of
`columns` patterns is useful with respect to a matrix of `rows` rows, from
the kind of its first pattern, whether the constructors at the heads of the
rows are all those of the column's type, and the usefulness of the smaller
problems: for a constructor, of the vector and matrix specialized by it;
for a wildcard, of those specialized by some constructor of the type, or of
the default matrix; for an or-pattern, of some alternative. The smaller
problems are passed as functions, so that only the one the rule needs is
solved. -/
def usefulStep (columns rows : Nat) (head : HeadKind) (complete : Bool)
    (specialized someSpecialized default someAlternative : Unit → Bool) : Bool :=
  if columns == 0 then rows == 0 else
  match head with
  | .constructor => specialized ()
  | .wildcard => if complete then someSpecialized () else default ()
  | .or => someAlternative ()

/-- A constructor of a type, as the usefulness rules specialize by it: a
variant, a `Bool`, an interval of integers, or a string. -/
inductive Ctor where
  | variant (idx : Nat)
  | bool (b : Bool)
  | int (lo hi : Option Int)
  | str (s : String)
  deriving Inhabited

/-- Whether the or-free pattern `p`, not a wildcard, is the constructor
`c`: the same variant or literal, or a range that contains `c`'s interval. -/
def Pat.sameCtor (c : Ctor) : Pat → Bool
  | .ctor i _ => match c with
    | .variant j => i == j
    | _ => false
  | .bool b => match c with
    | .bool b' => b == b'
    | _ => false
  | .int lo hi => match c with
    | .int lo' hi' => intervalWithin (lo', hi') (lo, hi)
    | _ => false
  | .str s => match c with
    | .str s' => s == s'
    | _ => false
  | .wild _ | .or _ => false

/-- The patterns of a variant's payload; none for other patterns. -/
def Pat.args : Pat → List Pat
  | .ctor _ args => args.toList
  | _ => []

/-- The patterns that replace a row's first pattern `p` once specialized by
the constructor `c` of arity `arity`, or `none` when the row is dropped
(`lang::specialize`): `arity` wildcards for a wildcard, and its arguments
for the same constructor. An or-pattern is split into rows before. -/
def specializeHead (c : Ctor) (arity : Nat) (p : Pat) : Option (List Pat) :=
  match p.headKind with
  | .wildcard => some (List.replicate arity (.wild))
  | .constructor => if p.sameCtor c then some p.args else none
  | .or => none

/-- What an identifier of one segment, not applied, is in a pattern
(`lang::PatternName`). -/
inductive PatternName where
  | boolLiteral
  | variant
  | binder
  deriving Inhabited, BEq, DecidableEq, Repr

/-- What an identifier of one segment, not applied, is in a pattern, from
whether it is `true` or `false`, whether it ends in `!`, and whether it
resolves to a variant (`lang::pattern_name`). -/
def patternName (boolWord bang variant : Bool) : PatternName :=
  if boolWord && !bang then .boolLiteral else if variant && !bang then .variant else .binder

/-- The kinds of type, for completeness (`lang::ColumnType`). -/
inductive ColumnKind where
  | enumeration
  | boolean
  | integer
  | string
  | other
  deriving Inhabited, BEq, DecidableEq, Repr

def PatTy.kind : PatTy → ColumnKind
  | .enum .. => .enumeration
  | .bool => .boolean
  | .int | .nat => .integer
  | .string => .string
  | .param _ | .other => .other

/-- Whether the constructors at the heads of a column are all those of its
type (`lang::signature_complete`): every variant of an enumeration, from
the number of its variants and of those named; `true` and `false`; and for
`Int` and `Nat`, intervals that cover every value of the type. No set of strings is complete,
and no pattern but `_` and binders matches a value of another type. -/
def signatureComplete (k : ColumnKind) (nVariants nNamed : Nat) (hasTrue hasFalse coversIntegers : Bool) : Bool :=
  match k with
  | .enumeration => nNamed == nVariants
  | .boolean => hasTrue && hasFalse
  | .integer => coversIntegers
  | .string | .other => false

/-! ## Usefulness -/

/-- The rows that a row stands for, with the or-pattern at its head split
into one row for each alternative, in order. -/
partial def expandRow : List Pat → Array (List Pat)
  | .or alts :: rest => alts.flatMap fun a => expandRow (a :: rest)
  | r => #[r]

/-- The types of the payload of the constructor `c` of `ty`: of an
instance of a generic enumeration, with its arguments for its parameters;
of any other, as declared, since it has none. -/
def ctorTys (sigs : Sigs) (ty : PatTy) (c : Ctor) : Array PatTy :=
  match ty, c with
  | .enum p args, .variant i =>
    let tys := ((sigs p)[i]?.map (·.2)).getD #[]
    if args.isEmpty then tys else tys.map (·.subst args)
  | _, _ => #[]

/-- The intervals of the integer patterns among `heads`. -/
def intervals (heads : Array Pat) : Array (Option Int × Option Int) :=
  heads.filterMap fun | .int lo hi => some (lo, hi) | _ => none

/-- The constructors of `ty`, in order, each with whether a pattern among
`heads` (or-free) names it, and whether they are all named. For `Int`,
the constructors are the intervals that split the integers at the bounds
of the patterns' intervals and of `extra`, and for `Nat`, those of them
that are at least 0. A string that no pattern names
stands for every other string, so it is not listed. -/
def columnCtors (sigs : Sigs) (ty : PatTy) (heads : Array Pat) (extra : Array (Option Int × Option Int) := #[]) :
    Array (Ctor × Bool) × Bool :=
  match ty with
  | .enum p _ =>
    let cs := (Array.range (sigs p).size).map fun i => (Ctor.variant i, heads.any fun | .ctor j _ => j == i | _ => false)
    (cs, signatureComplete .enumeration (sigs p).size (cs.filter (·.2)).size false false false)
  | .bool =>
    let named (b : Bool) := heads.any fun | .bool b' => b == b' | _ => false
    (#[(.bool true, named true), (.bool false, named false)], signatureComplete .boolean 0 0 (named true) (named false) false)
  | .int | .nat =>
    let ivs := intervals heads
    let nat := ty == .nat
    let parts := splitIntervals (ivs ++ extra ++ (if nat then #[(some 0, none)] else #[]))
    let parts := if nat then parts.filter (intervalWithin · (some 0, none)) else parts
    let cs := parts.map fun iv => (Ctor.int iv.1 iv.2, ivs.any (intervalWithin iv ·))
    (cs, signatureComplete .integer 0 0 false false (cs.all (·.2)))
  | .string =>
    let ss := heads.filterMap fun | .str s => some s | _ => none
    let ss := ss.foldl (init := #[]) fun acc s => if acc.contains s then acc else acc.push s
    (ss.map (Ctor.str ·, true), signatureComplete .string 0 0 false false false)
  | .param _ | .other => (#[], signatureComplete .other 0 0 false false false)

/-- The constructors that the or-free pattern `q`, not a wildcard, matches,
among those that split the column of `heads`. -/
def patCtors (sigs : Sigs) (ty : PatTy) (heads : Array Pat) (q : Pat) : Array Ctor :=
  match q with
  | .ctor i _ => #[.variant i]
  | .bool b => #[.bool b]
  | .str s => #[.str s]
  | .int lo hi =>
    ((columnCtors sigs ty heads #[(lo, hi)]).1.map (·.1)).filter fun
      | .int lo' hi' => intervalWithin (lo', hi') (lo, hi)
      | _ => false
  | _ => #[]

/-- The rows of `rows` specialized by the constructor `c` of arity `arity`. -/
def specializeRows (c : Ctor) (arity : Nat) (rows : Array (List Pat)) : Array (List Pat) :=
  rows.filterMap fun
    | h :: t => (specializeHead c arity h).map (· ++ t)
    | [] => none

/-- The default matrix: the rows whose first pattern is a wildcard, without
it. -/
def defaultRows (rows : Array (List Pat)) : Array (List Pat) :=
  rows.filterMap fun
    | .wild _ :: t => some t
    | _ => none

/-- Whether the vector `q`, of the types `tys`, is useful with respect to
the rows `rows` (`lang::usefulness`). -/
partial def useful (sigs : Sigs) : List PatTy → Array (List Pat) → List Pat → Bool
  | ty :: tys, rows, q :: qs =>
    let rows := rows.flatMap expandRow
    let heads := rows.filterMap (·.head?)
    let (ctors, complete) := columnCtors sigs ty heads
    let spec (c : Ctor) (args : List Pat) : Bool :=
      let ar := ctorTys sigs ty c
      useful sigs (ar.toList ++ tys) (specializeRows c ar.size rows) (args ++ qs)
    usefulStep (tys.length + 1) rows.size q.headKind complete
      (fun _ => (patCtors sigs ty heads q).any fun c =>
        spec c ((specializeHead c (ctorTys sigs ty c).size q).getD []))
      (fun _ => ctors.any fun (c, _) => spec c (List.replicate (ctorTys sigs ty c).size .wild))
      (fun _ => useful sigs tys (defaultRows rows) qs)
      (fun _ => match q with
        | .or alts => alts.any fun a => useful sigs (ty :: tys) rows (a :: qs)
        | _ => false)
  | _, rows, _ => usefulStep 0 rows.size .wildcard false (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false)

/-! ## Witnesses -/

/-- A value, or a set of values, that no arm matches, as a pattern. -/
inductive Wit where
  | any
  | bool (b : Bool)
  | int (lo hi : Option Int)
  | str (s : String)
  /-- A variant, by its full path. -/
  | ctor (path : Name) (args : Array Wit)
  deriving Inhabited

/-- The witness as a pattern. -/
partial def Wit.show : Wit → String
  | .any => "_"
  | .bool b => toString b
  | .int (some a) (some b) => if a == b then toString a else s!"{a}..={b}"
  | .int none (some b) => s!"..={b}"
  | .int (some a) none => s!"{a}.."
  | .int none none => "_"
  | .str s => s.quote
  | .ctor p args => showPath p ++ if args.isEmpty then "" else s!"({", ".intercalate (args.map Wit.show).toList})"

/-- The witness that the constructor `c` of `ty` builds from `args`. -/
def Ctor.wit (sigs : Sigs) (ty : PatTy) (c : Ctor) (args : Array Wit) : Wit :=
  match ty, c with
  | .enum p _, .variant i => .ctor (p ++ ((sigs p)[i]?.map (·.1)).getD .anonymous) args
  | _, .bool b => .bool b
  | _, .int lo hi => .int lo hi
  | _, .str s => .str s
  | _, .variant _ => .any

/-- The vectors of values of the types `tys` that no row of `rows`
matches, as witnesses, at most `limit` of them (Maranget's algorithm I).
Each constructor that a row names is followed into; the others, when some
vector of the default matrix is not matched, are each a witness, or `_`
when no row names any. -/
partial def missing (sigs : Sigs) (limit : Nat) : List PatTy → Array (List Pat) → Array (List Wit)
  | [], rows => if rows.isEmpty then #[[]] else #[]
  | ty :: tys, rows =>
    let rows := rows.flatMap expandRow
    let heads := rows.filterMap (·.head?)
    let (ctors, complete) := columnCtors sigs ty heads
    let rest := if complete then #[] else missing sigs limit tys (defaultRows rows)
    let follow (c : Ctor) : Array (List Wit) :=
      let ar := (ctorTys sigs ty c).size
      (missing sigs limit ((ctorTys sigs ty c).toList ++ tys) (specializeRows c ar rows)).map fun ws =>
        c.wit sigs ty (ws.take ar).toArray :: ws.drop ar
    let out : Array (List Wit) :=
      if !ctors.any (·.2) then rest.map (.any :: ·)
      else
        let named := ctors.flatMap fun (c, n) =>
          if n then follow c
          else rest.map (c.wit sigs ty ((ctorTys sigs ty c).map fun _ => .any) :: ·)
        -- A string that no arm names.
        if ty == .string then named ++ rest.map (.any :: ·) else named
    out.extract 0 limit

/-! ## Checks -/

/-- The or-free patterns that `p` stands for, in order, each with the
alternatives of `p`'s or-patterns that it takes, numbered in preorder from
`next`, and the number after the last. -/
partial def Pat.expand (p : Pat) (next : Nat := 0) : Array (Pat × Array Nat) × Nat :=
  match p with
  | .or alts => alts.foldl (init := (#[], next)) fun (acc, n) a =>
    let (es, n') := a.expand (n + 1)
    (acc ++ es.map fun (e, ids) => (e, #[n] ++ ids), n')
  | .ctor i args =>
    let (combos, n) := args.foldl (init := (#[((#[] : Array Pat), (#[] : Array Nat))], next)) fun (acc, n) a =>
      let (es, n') := a.expand n
      (acc.flatMap fun (ps, ids) => es.map fun (e, ids') => (ps.push e, ids ++ ids'), n')
    (combos.map fun (ps, ids) => (.ctor i ps, ids), n)
  | p => (#[(p, #[])], next)

/-- Whether a `match`'s arms are accepted, from the number of its arms and
alternatives that are not useful and whether it is exhaustive
(`lang::match_arms`). -/
def matchArmsAccepted (nUseless : Nat) (exhaustive : Bool) : Bool := nUseless == 0 && exhaustive

/-- What the chain of `and` that a pattern test is an operand of is a
part of: the operands of a chain are those of `and`, through parentheses,
and a test that is not an operand of `and` is a chain of one
(`lang::test_scope`). -/
inductive TestContext where
  /-- The condition of `when`. -/
  | whenCondition
  /-- The condition of `unless`. -/
  | unlessCondition
  /-- The condition of `if`. -/
  | ifCondition
  /-- An operand of `or`. -/
  | orOperand
  /-- The operand of `not`. -/
  | notOperand
  /-- Anything else: a whole constraint, a definition, or an operand or
  argument of another form. -/
  | standalone
  deriving BEq, DecidableEq, Inhabited, Repr

/-- Where a name is mentioned, in and around a chain of `and`
(`lang::test_scope`). -/
inductive TestSite where
  /-- The chain's operand at this position, from 0. -/
  | operand (k : Nat)
  /-- The body of the `when` or `unless`, or the `then` branch of the
  `if`, whose condition the chain is. -/
  | body
  /-- The `else` branch of the `if` whose condition the chain is. -/
  | elseBranch
  /-- Anywhere else. -/
  | outside
  deriving BEq, DecidableEq, Inhabited, Repr

/-- Whether the conditions of `context` see the names that their chain's
pattern tests bind in their body: those of `when` and of `if`, whose body
and `then` branch are evaluated where the patterns match. -/
def TestContext.bodySees : TestContext → Bool
  | .whenCondition | .ifCondition => true
  | _ => false

/-- Whether a name that the pattern test at `testAt` of a chain of `and` of
`operands` operands, a part of `context`, binds is in scope at `site`
(`lang::test_scope`): in the later operands of the chain, and in the body
of `when` and the `then` branch of `if`, where the pattern matches. -/
def binderVisible (context : TestContext) (testAt operands : Nat) : TestSite → Bool
  | .operand k => testAt < k && k < operands
  | .body => context.bodySees
  | .elseBranch | .outside => false

/-- Whether the pattern test at `testAt` of a chain of `and` of `operands`
operands, a part of `context`, may bind names: whether they are in scope
somewhere, in the next operand or in the body (`lang::test_scope`). -/
def testBinds (context : TestContext) (testAt operands : Nat) : Bool :=
  binderVisible context testAt operands (.operand (testAt + 1)) || binderVisible context testAt operands .body

/-- Whether the pattern of `e is P` is accepted, from whether the test may
bind names (`testBinds`), the number of its binders that are not `_` and
of its alternatives that are not useful, and whether it matches some value
(`lang::pattern_test`). -/
def patternTestAccepted (binds : Bool) (nBound nUseless : Nat) (matchesSome : Bool) : Bool :=
  (binds || nBound == 0) && nUseless == 0 && matchesSome

/-- The number of or-free patterns that `p` stands for (`Pat.expand`): the
product of the payload's, and the sum of an or-pattern's alternatives'. -/
partial def Pat.cases : Pat → Nat
  | .or alts => alts.foldl (· + ·.cases) 0
  | .ctor _ args => args.foldl (· * ·.cases) 1
  | _ => 1

/-- The most or-free patterns that one pattern may stand for, so that
checking a `match` stays fast: an or-pattern within each of several values
of a payload multiplies their numbers. -/
def maxCases : Nat := 256

/-- A pattern that stands for more than `maxCases` or-free patterns. -/
def tooManyCasesMsg (n : Nat) : Msg :=
  { code? := some "F0368", headline := s!"this pattern stands for {n} cases, more than {maxCases}"
    label? := some "too many cases"
    notes := #["note: or-patterns within several values of a payload multiply: `V(A | B, A | B)` stands for 4 cases",
      "help: split the arm, or match the payload with a `match` in the arm's body"] }

/-- `p`, an or-free pattern of `ty` whose payloads are all wildcards, as a
witness, if it is one. -/
def Pat.flatWit? (sigs : Sigs) (ty : PatTy) : Pat → Option Wit
  | .ctor i args => if args.all (· matches .wild _) then
      some ((Ctor.variant i).wit sigs ty (args.map fun _ => .any)) else none
  | .bool b => some (.bool b)
  | .int (some a) (some b) => if a == b then some (.int (some a) (some b)) else none
  | .str s => some (.str s)
  | _ => none

/-- Whether two or-free patterns are the same variant with wildcard
payloads, or the same literal. -/
def Pat.sameFlat : Pat → Pat → Bool
  | .ctor i as, .ctor j bs => i == j && as.all (· matches .wild _) && bs.all (· matches .wild _)
  | .bool a, .bool b => a == b
  | .int (some a) (some b), .int (some c) (some d) => a == b && c == d && a == c
  | .str a, .str b => a == b
  | _, _ => false

/-- Why the pattern `p` of `ty`, an arm's or an alternative's of the
arm's top-level or-pattern, never matches, given the or-free patterns
before it, `earlier`, and the earlier arm that matches every value, if
any, with whether it is a binder. -/
def unreachableNote (sigs : Sigs) (ty : PatTy) (alternative : Bool) (p? : Option Pat) (earlier : Array Pat)
    (wild? : Option Bool) : String :=
  let what := if alternative then "pattern" else "arm"
  match wild?, p? with
  | some false, _ => "note: an earlier `_` arm matches every value"
  | some true, _ => "note: an earlier arm binds every value"
  | none, some (.wild _) => match ty with
    | .enum e _ => s!"note: every variant of `{showPath e}` has an arm before it"
    | .bool => "note: `true` and `false` each have an arm before it"
    | .int => "note: the earlier arms cover every integer"
    | .nat => "note: the earlier arms cover every natural number"
    | _ => "note: the earlier arms match every value"
  | none, some p =>
    let negative : Bool := match p with
      | .int _ (some h) => ty == .nat && decide (h < 0)
      | _ => false
    if negative then "note: a `Nat` is never negative" else
    match p.flatWit? sigs ty, earlier.any p.sameFlat with
    | some w, true => s!"note: an earlier {what} matches `{w.show}`"
    | _, _ => s!"note: the earlier {what}s match every value that it matches"
  | none, none => s!"note: the earlier {what}s match every value that it matches"

/-- An arm, or an alternative of a pattern (`alternative`), that never
matches, and `why`. -/
def unreachableMsg (alternative : Bool) (why : String) : Msg :=
  { code? := some "F0318", headline := s!"unreachable {if alternative then "pattern" else "arm"}"
    label? := some "never matches", notes := #[why, "help: remove it"] }

/-- A `match` on a value of `ty` that the witnesses `ws` show is not
exhaustive. -/
def nonExhaustiveMsg (ty : PatTy) (ws : Array Wit) (table := false) : Msg :=
  let names := ", ".intercalate (ws.toList.map fun w => s!"`{w.show}`")
  let what (t : String) := if table then t.replace "a `match`" "a table" else t
  { code? := some "F0317", headline := s!"non-exhaustive {if table then "table" else "match"}: {names} not covered"
    label? := some s!"{names} not covered"
    notes := #[what <| match ty with
      | .enum .. => "note: a `match` has an arm for every variant, or a last arm `_`"
      | .bool => "note: a `match` on a `Bool` has arms for `true` and `false`, or a last arm `_`"
      | .int => "note: a `match` on an `Int` has a last arm `_`, unless its ranges cover every integer"
      | .nat => "note: a `match` on a `Nat` has a last arm `_`, unless its ranges cover every natural number"
      | _ => s!"note: a `match` on a `String` has a last arm `_`"] }

/-- The or-patterns' alternatives of `p`, in preorder, as `Pat.expand`
numbers them. -/
partial def Pat.alternatives : Pat → Array Pat
  | .or alts => alts.flatMap fun a => #[a] ++ a.alternatives
  | .ctor _ args => args.flatMap Pat.alternatives
  | _ => #[]

/-- The alternatives of `p`'s own or-pattern, if it is one, each with its
number in preorder. -/
def Pat.directAlternatives : Pat → Array (Nat × Pat)
  | .or alts => (alts.foldl (init := ((#[] : Array (Nat × Pat)), 0)) fun (acc, n) (a : Pat) =>
      (acc.push (n, a), n + 1 + a.alternatives.size)).1
  | _ => #[]

/-- For the arms `arms`, each pattern's or-free patterns, whether each is
useful with respect to those of the arms before it without a guard and
those of its own arm before it, and the alternatives each takes. The arms
that have a guard are `guarded`: one may not be taken where its pattern
matches, so it hides nothing from the arms after it. -/
def usefulness (sigs : Sigs) (ty : PatTy) (arms : Array Pat) (guarded : Array Bool := #[]) :
    Array (Array (Pat × Bool × Array Nat)) := Id.run do
  let mut rows : Array (List Pat) := #[]
  let mut out := #[]
  for arm in arms, i in [0:arms.size] do
    let mut here := #[]
    let mut own := rows
    for (e, ids) in (arm.expand).1 do
      here := here.push (e, useful sigs [ty] own [e], ids)
      own := own.push [e]
    unless guarded[i]?.getD false do rows := own
    out := out.push here
  return out

/-- The alternatives of `p`'s or-patterns that no useful or-free pattern of
`es` takes. -/
def uselessAlternatives (p : Pat) (es : Array (Pat × Bool × Array Nat)) : Array Nat :=
  (Array.range (p.alternatives.size)).filter fun j => !es.any fun (_, u, ids) => u && ids.contains j

/-- Whether `p` is a flat pattern of an enumeration: `_`, a binder, or a
variant whose payload's patterns are `_` or binders. -/
def Pat.flatEnum : Pat → Bool
  | .wild _ => true
  | .ctor _ args => args.all (· matches .wild _)
  | _ => false

/-- Whether `p` names the variant `i`. -/
def Pat.names (i : Nat) : Pat → Bool
  | .ctor j _ => j == i
  | _ => false

/-- Whether the arms of a `match` on an enumeration of `nCtors ty` variants,
each with whether it has a guard, are exhaustive without the arms with guards,
where every pattern is flat (`Pat.flatEnum`): an arm without a guard
matches every value, or each variant is named by one; `none` otherwise.
It is what the usefulness of `_` after them comes to there
(`check::flat_completeness_asked`). -/
def flatUnguardedExhaustive? (nCtors : Name → Nat) (ty : PatTy) (arms : Array (Pat × Bool)) : Option Bool :=
  match ty with
  | .enum e _ =>
    if !arms.all (·.1.flatEnum) then none else
    let unguarded := (arms.filter (!·.2)).map (·.1)
    some (unguarded.any (· matches .wild _) || (List.range (nCtors e)).all fun i => unguarded.any (Pat.names i))
  | _ => none

/-- Checks the arms of a `match` on a value of `ty`, each its pattern, of
which those that have a guard are `guarded`, explaining the first problem:
at an arm and, for an alternative, its number in preorder
(`Pat.alternatives`), or at the `match`. Gives whether the arms without a
guard are exhaustive, without which the checks ask whether some arm is
taken (`check::completeness_asked`). -/
def checkMatch (sigs : Sigs) (ty : PatTy) (arms : Array Pat) (guarded : Array Bool := #[]) (ordered := true) :
    Except (Option (Nat × Option Nat) × Msg) Bool := do
  if let some i := arms.findIdx? (·.cases > maxCases) then throw (some (i, none), tooManyCasesMsg arms[i]!.cases)
  let isGuarded (i : Nat) : Bool := guarded[i]?.getD false
  -- In a table over a scrutinee, no arm hides another: each is useful
  -- with respect to its own cases alone (`checkTableArms`).
  let hides := if ordered then guarded else arms.map fun _ => true
  let us := usefulness sigs ty arms hides
  let uselessArms := (Array.range arms.size).filter fun i => !us[i]!.any (·.2.1)
  let uselessAlts := (Array.range arms.size).flatMap fun i =>
    if uselessArms.contains i then #[] else (uselessAlternatives arms[i]! us[i]!).map (i, ·)
  let rows := us.flatMap (·.map fun (e, _) => [e])
  let ws := missing sigs 64 [ty] rows
  if matchArmsAccepted (uselessArms.size + uselessAlts.size) ws.isEmpty then
    -- The guards are ignored for exhaustiveness, but not for whether some
    -- arm is always taken.
    let unguarded := (us.zipIdx.filter (!isGuarded ·.2)).flatMap (·.1.map fun (e, _) => [e])
    let paired := arms.mapIdx fun i p => (p, isGuarded i)
    return (flatUnguardedExhaustive? (sigs · |>.size) ty paired).getD (!useful sigs [ty] unguarded [.wild false])
  -- The first problem, by arm and then by alternative.
  for arm in arms, i in [0:arms.size] do
    -- Only the arms before it without guards hide what it matches, and
    -- none in a table over a scrutinee.
    let before := if ordered then (Array.range i).filter (!isGuarded ·) else #[]
    let earlier := before.flatMap fun k => us[k]!.map (·.1)
    let wild? := before.findSome? fun k => match arms[k]! with | .wild b => some b | _ => none
    if uselessArms.contains i then
      let p? := if arm matches .or _ then none else some arm
      throw (some (i, none), unreachableMsg false (unreachableNote sigs ty false p? earlier wild?))
    if let some (_, j) := uselessAlts.find? (·.1 == i) then
      -- Only an alternative of the arm's own or-pattern is compared with
      -- the patterns before it.
      let direct := arm.directAlternatives
      let p? := (direct.find? (·.1 == j)).map (·.2)
      let before := earlier ++ ((direct.filter (·.1 < j)).map (·.2))
      throw (some (i, some j), unreachableMsg true (unreachableNote sigs ty true p? before wild?))
  throw (none, nonExhaustiveMsg ty (ws.filterMap (·.head?)) (table := !ordered))

/-- The matrix carrier cannot be named by a source identifier. -/
def matchVectorPath : Name := Name.mkSimple "#match_arguments"

/-- The multi-column matrix, represented by a fresh single constructor for
Maranget's existing specialization algorithm. No product value or source
constructor is introduced. -/
def matchVector (sigs : Sigs) (types : Array PatTy) (rows : Array (Array Pat)) : Sigs × PatTy × Array Pat :=
  let path := matchVectorPath
  let signatures : Sigs := fun p => if p == path then #[(`arguments, types)] else sigs p
  (signatures, .enum path [], rows.map fun ps => if ps.all (· matches .wild false) then .wild false else .ctor 0 ps)

/-- Explain a vector mismatch without exposing the internal matrix constructor. -/
def vectorMsg (msg : Msg) : Msg :=
  let f (s : String) := s.replace (showPath (matchVectorPath ++ `arguments)) ""
  let label := msg.label?.map f
  let notes := msg.notes.map fun n =>
    if n == "note: a `match` has an arm for every variant, or a last arm `_`" ||
        n == s!"note: every variant of `{showPath matchVectorPath}` has an arm before it" then
      "note: a `match` has an arm for every combination of its scrutinees" else f n
  { msg with headline := f msg.headline, label? := label, notes := notes }

/-! ## Overlap -/

/-- One step of overlap (`lang::overlap`): what two patterns, whose heads
are `first` and `second`, have in common, if anything, from the smaller
problems, passed as functions so that only the one the rule needs is
solved: for an or-pattern, an alternative of either that overlaps the
other; for a wildcard, what the other pattern matches, if anything; and
for two constructors that are the same, what the values of their payloads
have in common. Both decisions and witnesses are read from it: `α` is a
witness, or `Unit`. -/
def overlapStep (first second : HeadKind) (same : Bool)
    (args firstSome secondSome someAlternative : Unit → Option α) : Option α :=
  if first matches .or || second matches .or then someAlternative ()
  else match first, second with
    | .wildcard, _ => secondSome ()
    | _, .wildcard => firstSome ()
    | _, _ => if same then args () else none

/-- The greater of two lower bounds, `none` for none. -/
def maxBound : Option Int → Option Int → Option Int
  | some x, some y => some (max x y)
  | x, none => x
  | none, y => y

/-- The lesser of two upper bounds, `none` for none. -/
def minBound : Option Int → Option Int → Option Int
  | some x, some y => some (min x y)
  | x, none => x
  | none, y => y

/-- The integers that both of two intervals contain, if any, of those that
`ty` has: at least 0 for a `Nat`. -/
def meetIntervals (ty : PatTy) (a b : Option Int × Option Int) : Option (Option Int × Option Int) :=
  let lo := if ty.isNat then some (max ((maxBound a.1 b.1).getD 0) 0) else maxBound a.1 b.1
  let hi := minBound a.2 b.2
  if (match lo, hi with | some l, some h => decide (l ≤ h) | _, _ => true) then some (lo, hi) else none

/-- An integer of the interval `iv`, as a witness. -/
def Wit.ofInterval : Option Int × Option Int → Wit
  | (some l, _) => .int (some l) (some l)
  | (none, some h) => .int (some h) (some h)
  | (none, none) => .int (some 0) (some 0)

/-- A value that the or-free pattern `p` of `ty` matches, as a witness, if
it matches any: every pattern does, but one with a range that matches no
value of its type, such as `..=-1` within a `Nat`. -/
def Pat.someWit? (sigs : Sigs) (ty : PatTy) (p : Pat) : Option Wit :=
  match p with
  | .wild _ => some .any
  | .bool b => some (.bool b)
  | .str v => some (.str v)
  | .int lo hi => (meetIntervals ty (lo, hi) (none, none)).map Wit.ofInterval
  | .ctor i args =>
    let tys := ctorTys sigs ty (.variant i)
    ((List.range args.size).mapM fun k =>
      if h : k < args.size then args[k].someWit? sigs (tys[k]?.getD .other) else none).map
      fun ws => (Ctor.variant i).wit sigs ty ws.toArray
  | .or alts => (List.range alts.size).findSome? fun k =>
      if h : k < alts.size then alts[k].someWit? sigs ty else none
termination_by sizeOf p
decreasing_by
  all_goals simp_wf
  all_goals have := Array.sizeOf_getElem _ _ h
  all_goals omega

/-- Whether two constructor patterns, neither a wildcard nor an
or-pattern, are the same constructor, and the witness of what they have in
common at the head: two integer patterns are the same where some integer
of `ty` matches both. -/
def Pat.sameHead (ty : PatTy) : Pat → Pat → Bool × Option Wit
  | .ctor i _, .ctor j _ => (i == j, none)
  | .bool a, .bool b => (a == b, some (.bool a))
  | .str a, .str b => (a == b, some (.str a))
  | .int l h, .int l' h' => match meetIntervals ty (l, h) (l', h') with
    | some iv => (true, some (Wit.ofInterval iv))
    | none => (false, none)
  | _, _ => (false, none)

/-- A value that both patterns `p` and `q` of `ty` match, as a witness, if
they overlap (`lang::overlap`, `lang::pattern_overlap`): one step of
`overlapStep`, whose smaller problems are those of the payloads' values,
in order, and of the alternatives. -/
def Pat.overlapWit? (sigs : Sigs) (ty : PatTy) (p q : Pat) : Option Wit :=
  overlapStep p.headKind q.headKind (p.sameHead ty q).1
    (fun _ => match hp : p, hq : q with
      | .ctor i as, .ctor _ bs =>
        let tys := ctorTys sigs ty (.variant i)
        ((List.range (min as.size bs.size)).mapM fun k =>
          if h : k < as.size ∧ k < bs.size then as[k].overlapWit? sigs (tys[k]?.getD .other) bs[k] else none).map
          fun ws => (Ctor.variant i).wit sigs ty ws.toArray
      | _, _ => (p.sameHead ty q).2)
    (fun _ => p.someWit? sigs ty) (fun _ => q.someWit? sigs ty)
    (fun _ => match hp : p, hq : q with
      | .or alts, _ => (List.range alts.size).findSome? fun k =>
          if h : k < alts.size then alts[k].overlapWit? sigs ty q else none
      | _, .or alts => (List.range alts.size).findSome? fun k =>
          if h : k < alts.size then p.overlapWit? sigs ty alts[k] else none
      | _, _ => none)
termination_by sizeOf p + sizeOf q
decreasing_by
  all_goals subst_vars
  all_goals simp_wf
  all_goals first
    | (have := Array.sizeOf_getElem _ _ h.1; have := Array.sizeOf_getElem _ _ h.2; omega)
    | (have := Array.sizeOf_getElem _ _ h; omega)

/-- Two arms of a table over a scrutinee without guards whose patterns
overlap, both matching `w`: the later arm, which overlaps arm `i`, counted
from 0. -/
def armsOverlapMsg (i : Nat) (w : Wit) : Msg :=
  { code? := some "F0391", headline := s!"this arm overlaps arm {i + 1}", label? := some s!"overlaps arm {i + 1}"
    notes := #[s!"note: both match `{w.show}`",
      "note: the arms of a table are disjoint, so that its value does not depend on their order",
      "help: narrow one of the patterns, tell the arms apart with guards, or write a `match`, which takes the first arm that matches"] }

/-- Whether arm `k` of a table over a scrutinee, of the arms of which
those that are `_` are `wild` and those that have a guard are `guarded`, is
the otherwise: the last, `_`, without a guard. -/
def isOtherwise (wild guarded : Array Bool) (k : Nat) : Bool :=
  k + 1 == wild.size && (wild[k]?.getD false) && !(guarded[k]?.getD false)

/-- Whether the static rules reject arms `i` and `j` of a table over a
scrutinee, `i < j`, and whether the disjointness check asks about them,
from whether their patterns overlap (`lang::table_arms`): only the later
arm can be the otherwise. -/
def armPair (wild guarded : Array Bool) (overlap : Bool) (i j : Nat) : Bool × Bool :=
  tableArmPair overlap ((guarded[i]?.getD false) || (guarded[j]?.getD false)) (isOtherwise wild guarded j)

/-- The pairs `(i, j)` of `n` arms, `i < j`, in order: by `j`, then by `i`. -/
def armPairs (n : Nat) : List (Nat × Nat) := (List.range n).flatMap fun j => (List.range j).map (·, j)

/-- The first pair of `n` arms, in order (`armPairs`), that is `rejected`:
the static rules report the table there (`lang::table_arms`). -/
def firstRejected? (n : Nat) (rejected : Nat → Nat → Bool) : Option (Nat × Nat) :=
  (armPairs n).find? fun (i, j) => rejected i j

/-- An arm of a table over a scrutinee after its `_` arm. -/
def armAfterWildMsg : Msg :=
  { code? := some "F0359", headline := "an arm after `_` can never be reached", label? := some "unreachable arm"
    notes := #["note: `_` is taken wherever no other arm is, so it is the last arm",
      "help: remove this arm, or move it before `_`"] }

/-- Whether the static rules reject arms `i` and `j`, `i < j`, of a table
over a scrutinee of `ty`, each its pattern, of which those that have a
guard are `guarded`, and whether the disjointness check asks about them
(`armPair`), from whether their patterns overlap (`Pat.overlapWit?`). -/
def tableArmVerdict (sigs : Sigs) (ty : PatTy) (arms : Array Pat) (guarded : Array Bool) (i j : Nat) : Bool × Bool :=
  armPair (arms.map (· matches .wild false)) guarded (arms[i]!.overlapWit? sigs ty arms[j]!).isSome i j

/-- Checks the arms of a table over a scrutinee of `ty`, each its pattern,
of which those that have a guard are `guarded`, explaining the first
problem, as `checkMatch` does (`Reqs/Lang/Expressions#tables-over-a-scrutinee`):
the first pair of arms that the static rules reject, without guards and
whose patterns overlap, but for the otherwise (`lang::table_arms`); an
otherwise that the arms without guards cover, which is never taken; and
then the rules of a `match`, in which no arm hides another. Gives whether
the arms without guards are exhaustive, and the pairs of arms, in order,
that the disjointness check asks about. -/
def checkTableArms (sigs : Sigs) (ty : PatTy) (arms : Array Pat) (guarded : Array Bool) :
    Except (Option (Nat × Option Nat) × Msg) (Bool × Array (Nat × Nat)) := do
  if let some i := arms.findIdx? (·.cases > maxCases) then throw (some (i, none), tooManyCasesMsg arms[i]!.cases)
  let wild := arms.map (· matches .wild false)
  if let some (i, j) := firstRejected? arms.size fun i j => (tableArmVerdict sigs ty arms guarded i j).1 then
    throw (some (j, none), armsOverlapMsg i (arms[i]!.overlapWit? sigs ty arms[j]!).get!)
  -- The otherwise is taken where no other arm is, which never happens
  -- where the arms without guards cover every value.
  let last := arms.size - 1
  if arms.size > 0 && isOtherwise wild guarded last then
    let before := ((Array.range last).filter fun k => !(guarded[k]?.getD false)).map (arms[·]!)
    unless useful sigs [ty] (before.map ([·])) [.wild false] do
      throw (some (last, none), unreachableMsg false (unreachableNote sigs ty false (some (.wild false)) before none))
  return (← checkMatch sigs ty arms guarded (ordered := false),
    ((armPairs arms.size).filter fun (i, j) => (tableArmVerdict sigs ty arms guarded i j).2).toArray)

/-- Where a problem of a pattern test is: a binder, numbered in preorder,
or an alternative. -/
inductive TestAt where
  | binder (k : Nat)
  | alternative (j : Nat)
  /-- The whole pattern. -/
  | whole
  deriving Inhabited

/-- `e is P`, where `e` is not of a type that patterns match
(`Reqs/Lang/Expressions#pattern-tests`); with `shorthand`, the pattern
shorthand `type T = U is P`, whose value is not written, and which is
reported at `U` (`Reqs/Lang/SubsetTypes#the-pattern-shorthand`). -/
def isScrutineeMsg (ty : String) (shorthand := false) : Msg :=
  { code? := some "F0335", headline := s!"cannot test `{ty}` against a pattern", label? := some "no patterns of this type"
    notes := #["note: `is` tests a value of an enum, `Bool`, `Int`, `Nat` or `String`",
      if shorthand then s!"help: for other types, declare the type in full, as `type T = x: {ty} where …`, and compare `x` with `=` or `in`"
      else "help: for other types, compare with `=` or `in`"] }

/-- The name that a binder `n` or `n!` would declare, as a message names
it: without its `!` (`Reqs/Lang/Procedures#shadowing`). -/
def binderName (n : Name) : Name :=
  match n with
  | .str p s => if s.endsWith "!" && s.length > 1 then .str p (s.dropEnd 1).toString else n
  | _ => n

/-- A binder of the pattern of `e is P`, a part of `context`, where nothing
sees the names that it binds (`testBinds`), named as `binderName` gives
it. -/
def isBinderMsg (n : Name) (context : TestContext := .standalone) : Msg :=
  let n := binderName n
  let why := match context with
    | .unlessCondition => s!"note: the body of `unless` holds where the pattern does not match, where `{n}` has no value"
    | .orOperand => s!"note: an operand of `or` binds no names: where the other operand holds, the pattern need not match, and `{n}` would have no value"
    | .notOperand => s!"note: under `not`, what follows holds where the pattern does not match, where `{n}` has no value"
    | _ => "note: a pattern test binds names only for what follows it where it matches: the later operands of its `and`, the body of `when`, or the `then` branch of `if`"
  { code? := some "F0334", headline := s!"a pattern test cannot bind `{n}` here", label? := some "binds a name"
    notes := #[why, s!"help: to read the payload, bind it in a `when`'s condition, as in `when x is P({n}), ...`, or write a `match`"]
    fixes := #[{ msg := "ignore the value", replacement := "_" }] }

/-- Checks the pattern `p` of `e is P` on a value of `ty`, whose binders,
`_` excluded, are `binders`, in preorder, explaining the first problem,
where the test, a part of `context`, may bind names if `binds`
(`testBinds`). A pattern that matches every value is accepted. -/
def checkPatternTest (sigs : Sigs) (ty : PatTy) (p : Pat) (binders : Array Name) (binds : Bool)
    (context : TestContext) : Except (TestAt × Msg) Unit := do
  if p.cases > maxCases then throw (.whole, tooManyCasesMsg p.cases)
  let us := usefulness sigs ty #[p]
  let useless := uselessAlternatives p us[0]!
  let matchesSome := us[0]!.any (·.2.1)
  if patternTestAccepted binds binders.size useless.size matchesSome then return
  if let (some n, false) := (binders[0]?, binds) then throw (.binder 0, isBinderMsg n context)
  unless matchesSome do
    throw (.whole, unreachableMsg true (unreachableNote sigs ty true (if p matches .or _ then none else some p) #[] none))
  let j := useless[0]!
  let direct := p.directAlternatives
  let p? := (direct.find? (·.1 == j)).map (·.2)
  let before := (direct.filter (·.1 < j)).map (·.2)
  throw (.alternative j, unreachableMsg true (unreachableNote sigs ty true p? before none))

/-! ## Messages -/

/-- A `match` on a value of a type that patterns do not match. -/
def scrutineeMsg (ty : String) : Msg :=
  { code? := some "F0316", headline := s!"cannot match on `{ty}`", label? := some "no patterns of this type"
    notes := #["note: `match` reads a value of an enum, `Bool`, `Int`, `Nat` or `String`",
      "help: for other types, use `if ... then ... else`"] }

/-- A pattern, `what` (such as ``a pattern of `Int` ``), where a value of
`expected` is matched. -/
def patternTypeMsg (expected what : String) : Msg :=
  { code? := some "F0348", headline := s!"expected a pattern of `{expected}`, but this is {what}"
    label? := some s!"not a pattern of `{expected}`"
    notes := #[s!"note: the value matched here has type `{expected}`"] }

/-- Whether `p` is `_`, a binder, `true`, `false`, a variant whose payload's
patterns are `_` or binders, or an or-pattern of these: a pattern that no
other such pattern overlaps without containing it, as the match lints that
move or remove arms need. -/
def Pat.flat : Pat → Bool
  | .wild _ | .bool _ => true
  | .ctor _ args => args.all (· matches .wild _)
  | .or alts => alts.all fun
    | .ctor _ args => args.all (· matches .wild _)
    | .bool _ => true
    | _ => false
  | _ => false

/-- Whether `p` is `_`, a variant without a payload, or an or-pattern of
these: a pattern that `=` or `in` can express (`lint::match_like_membership`). -/
def Pat.noPayload : Pat → Bool
  | .wild false => true
  | .ctor _ args => args.isEmpty
  | .or alts => alts.all fun
    | .ctor _ args => args.isEmpty
    | _ => false
  | _ => false

/-- A range pattern that matches no integer, written `text`. -/
def emptyRangeMsg (text : String) : Msg :=
  { code? := some "F0349", headline := s!"the range `{text}` matches no integer", label? := some "empty range"
    notes := #["note: `a..=b` matches the integers from `a` to `b`, and `a..b` those from `a` to `b - 1`"] }

/-- A bound of a range pattern that is not an integer literal or a
constant of `Int` or `Nat`: `what` it is. -/
def rangeBoundMsg (what : String) : Msg :=
  { code? := some "F0350", headline := s!"a range's bound must be an integer or a constant of `Int` or `Nat`, but this is {what}"
    label? := some "not an integer" }

/-- A constant as a range's bound, whose value is not an integer
constant expression (`Reqs/Lang/Expressions#division-and-remainder`). -/
def rangeConstantMsg (c : Name) : Msg :=
  { code? := some "F0351", headline := s!"the value of `{showPath c}` is not known where the range is checked"
    label? := some "value not known"
    notes := #["note: a constant used as a range's bound has an integer constant expression as its value: integer literals and such constants, by `+`, `-`, `*`, `div`, `mod`, `abs`, `min` and `max`"] }

end Fren.Core
