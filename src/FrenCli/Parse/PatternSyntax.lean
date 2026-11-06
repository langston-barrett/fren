-- keep-sorted start
import FrenCli.Lex
import FrenCore.Generics
-- keep-sorted end

/-! Identifiers, patterns and their encoding within types. -/

namespace FrenCli

structure Ident where
  name : String
  span : Span
  deriving Inhabited

/-- A bound of a range pattern: an integer, possibly negated, or a path to
a constant. -/
inductive Bound where
  | num (span : Span) (value : Int)
  | path (span : Span) (segs : Array Ident)
  deriving Inhabited

def Bound.span : Bound → Span
  | .num s _ | .path s _ => s

/-- A pattern (`Reqs/Lang/Patterns`). -/
inductive Pattern where
  /-- `_` -/
  | wild (span : Span)
  /-- `x`, `E::V` or `E::V(p, q)`: a path of one segment, not applied, is a
  binder, `true`, `false`, or a variant, once resolved
  (`lang::pattern_name`). -/
  | variant (span : Span) (path : Array Ident) (args : Option (Array Pattern))
  /-- An integer literal, possibly negated. -/
  | num (span : Span) (value : Int)
  | str (span : Span) (value : String)
  /-- `a..=b`, `a..b`, `a..` or `..=b`. -/
  | range (span : Span) (lo hi : Option Bound) (inclusive : Bool)
  /-- `A | B`, or `| A`. -/
  | or (span : Span) (alts : Array Pattern)
  deriving Inhabited

def Pattern.span : Pattern → Span
  | .wild s | .variant s .. | .num s _ | .str s _ | .range s .. | .or s _ => s

/-- The alternatives of a pattern's own or-pattern, or the pattern itself. -/
def Pattern.alts : Pattern → Array Pattern
  | .or _ alts => alts
  | p => #[p]

/-- The alternatives of the or-patterns of a pattern, in preorder
(`Fren.Core.Pat.alternatives`). -/
partial def Pattern.alternatives : Pattern → Array Pattern
  | .or _ alts => alts.flatMap fun a => #[a] ++ a.alternatives
  | .variant _ _ (some args) => args.flatMap Pattern.alternatives
  | _ => #[]

/-- The identifiers of one segment, not applied, of a pattern, in
preorder: its binders, once those that name variants, `true` and `false`
are told apart. -/
partial def Pattern.names : Pattern → Array Ident
  | .variant _ #[x] none => #[x]
  | .variant _ _ (some args) => args.flatMap Pattern.names
  | .or _ alts => alts.flatMap Pattern.names
  | _ => #[]

/-- A binder of a quantifier or of a global expectation's leading
`forall`, `(x y: T)`: its names, its type, and its span, with its
parentheses. -/
structure Binder where
  names : Array Ident
  ty : Array Ident
  span : Span
  deriving Inhabited

/-! ### Patterns within types

A type is a flat array of segments (`typeExpr`), so a type's pattern, the
pattern of a pattern-test invariant, is a segment of its own, whose name
holds the pattern written out by `Pattern.encode`, and which
`Pattern.decode` reads back. -/

/-- The atoms of an encoded pattern, each prefixed by its length, so that
any string literal's characters fit. -/
private def atom (s : String) : String := s!"{s.length}:{s}"

private def spanAtoms (sp : Span) : String := atom (toString sp.start) ++ atom (toString sp.stop)

private def segAtoms (segs : Array Ident) : String :=
  atom (toString segs.size) ++ String.join (segs.toList.map fun i => atom i.name ++ spanAtoms i.span)

/-- `p`, written as atoms (`Pattern.decode`). -/
partial def Pattern.encode : Pattern → String
  | .wild sp => atom "w" ++ spanAtoms sp
  | .num sp v => atom "n" ++ spanAtoms sp ++ atom (toString v)
  | .str sp v => atom "s" ++ spanAtoms sp ++ atom v
  | .range sp lo hi inclusive =>
    let bound : Option Bound → String
      | none => atom "-"
      | some (.num bs v) => atom "bn" ++ spanAtoms bs ++ atom (toString v)
      | some (.path bs segs) => atom "bp" ++ spanAtoms bs ++ segAtoms segs
    atom "r" ++ spanAtoms sp ++ atom (if inclusive then "1" else "0") ++ bound lo ++ bound hi
  | .variant sp segs args =>
    atom "v" ++ spanAtoms sp ++ segAtoms segs ++ match args with
      | none => atom "0"
      | some as => atom "1" ++ atom (toString as.size) ++ String.join (as.toList.map Pattern.encode)
  | .or sp alts => atom "o" ++ spanAtoms sp ++ atom (toString alts.size) ++ String.join (alts.toList.map Pattern.encode)

/-- The atoms of `s`, as `atom` writes them. -/
private partial def atomsOf (s : List Char) (acc : Array String := #[]) : Array String :=
  if s.isEmpty then acc else
  let digits := s.takeWhile (·.isDigit)
  let n := (String.ofList digits).toNat!
  let rest := s.drop (digits.length + 1)
  atomsOf (rest.drop n) (acc.push (String.ofList (rest.take n)))

private abbrev D := StateT Nat (Except String)

private def next (as : Array String) : D String := do
  let i ← get
  let some a := as[i]? | throw "a truncated pattern"
  set (i + 1)
  return a

private def nextNat (as : Array String) : D Nat := return (← next as).toNat!

private def nextInt (as : Array String) : D Int := do
  let a ← next as
  return if a.startsWith "-" then -((a.drop 1).toString.toNat! : Int) else (a.toNat! : Int)

private def nextSpan (as : Array String) : D Span := return { start := ← nextNat as, stop := ← nextNat as }

private def nextSegs (as : Array String) : D (Array Ident) := do
  let n ← nextNat as
  (Array.range n).mapM fun _ => do return { name := ← next as, span := ← nextSpan as }

private partial def decodeAt (as : Array String) : D Pattern := do
  match ← next as with
  | "w" => return .wild (← nextSpan as)
  | "n" => return .num (← nextSpan as) (← nextInt as)
  | "s" => return .str (← nextSpan as) (← next as)
  | "r" =>
    let sp ← nextSpan as
    let inclusive := (← next as) == "1"
    let bound : D (Option Bound) := do
      match ← next as with
      | "bn" => return some (.num (← nextSpan as) (← nextInt as))
      | "bp" => return some (.path (← nextSpan as) (← nextSegs as))
      | _ => return none
    let lo ← bound
    let hi ← bound
    return .range sp lo hi inclusive
  | "v" =>
    let sp ← nextSpan as
    let segs ← nextSegs as
    if (← next as) == "0" then return .variant sp segs none
    let n ← nextNat as
    return .variant sp segs (some (← (Array.range n).mapM fun _ => decodeAt as))
  | "o" =>
    let sp ← nextSpan as
    let n ← nextNat as
    return .or sp (← (Array.range n).mapM fun _ => decodeAt as)
  | t => throw s!"an unknown pattern `{t}`"

/-- The pattern that `Pattern.encode` wrote as `s`. -/
def Pattern.decode (s : String) : Except String Pattern := (decodeAt (atomsOf s.toList)).run' 0

/-- The prefix of the name of a type's pattern's segment, which no
identifier can start with: it follows the segments of the base type, or,
for a base type that is a set, relation or sequence, precedes them
(`patOuterSeg`), so that it is never read as an element type's. -/
def patSeg : String := Fren.Core.patSeg

def patOuterSeg : String := Fren.Core.patOuterSeg

/-- The segment of the pattern `p`, after the base type, or before it if
`outer`. -/
def Pattern.seg (p : Pattern) (outer : Bool) : Ident :=
  { name := (if outer then patOuterSeg else patSeg) ++ p.encode, span := p.span }

/-- The type `segs`, split into its base type and its pattern's segment,
if it has one (`patSeg`). -/
def splitPatternSeg (segs : Array Ident) : Array Ident × Option Ident :=
  match segs[0]?, segs.back? with
  | some f, some b =>
    if f.name.startsWith patOuterSeg then (segs.extract 1, some f)
    -- A set's, relation's or sequence's last segment is its element type's.
    else if f.name == "Set(" || f.name == "Seq(" || f.name == "Rel(" then (segs, none)
    else if b.name.startsWith patSeg && segs.size > 1 then (segs.pop, some b) else (segs, none)
  | _, _ => (segs, none)

/-- Whether the segment `s` is a type's pattern's. -/
def Ident.isPatternSeg (s : Ident) : Bool := s.name.startsWith patSeg || s.name.startsWith patOuterSeg

/-- The pattern of the segment `seg` that `Pattern.seg` made. -/
def Ident.pattern? (seg : Ident) : Option Pattern :=
  let text := if seg.name.startsWith patOuterSeg then seg.name.drop patOuterSeg.length
    else if seg.name.startsWith patSeg then seg.name.drop patSeg.length else ""
  if text.isEmpty then none else (Pattern.decode text.toString).toOption

end FrenCli
