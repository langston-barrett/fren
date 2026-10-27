-- keep-sorted start
import FrenCore.Generics
import FrenCore.Guards
-- keep-sorted end

/-!
# Higher-order functions (`Reqs/Lang/HigherOrder`)

What both front ends share about function types and closures: where a
function type may be written, what an argument for a function parameter
may be, that functions are not compared, and how the `fren` command unfolds
a closure into a higher-order function's body without capturing its names.
-/

namespace Fren.Core

/-! ## Function types -/

/-- A function type, `fn(A, B) -> R` (`Reqs/Lang/HigherOrder#function-types`),
the type of a defined function's parameter. -/
structure FnTy where
  params : Array Ty
  result : Ty
  deriving Inhabited, BEq

/-- `fn(A, B) -> R`, as written. -/
def FnTy.show (f : FnTy) : String := s!"fn({", ".intercalate (f.params.toList.map Ty.show)}) -> {f.result.show}"

/-- The function type with the type arguments `args` for the type parameters
that it mentions. -/
def FnTy.subst (f : FnTy) (args : Array Ty) : FnTy := { params := f.params.map (·.subst args), result := f.result.subst args }

/-- Whether the function type mentions the type parameter `k`. -/
def FnTy.mentions (f : FnTy) (k : Nat) : Bool := f.result.mentions k || f.params.any (·.mentions k)

/-- `f` as its function's signature declares it (`Ty.asParams`). -/
def FnTy.asParams (fn : Lean.Name) (params : Array Lean.Name) (f : FnTy) : FnTy :=
  { params := f.params.map (·.asParams fn params), result := f.result.asParams fn params }

/-- The segments of a function type, as both front ends see a type's
(`Fren.Core.setSeg`): `fn(A, B) -> R` is `fnSeg`, `A`'s, `fnSep`, `B`'s,
`fnArrow` and `R`'s, none of which an identifier can be. -/
def fnSeg : String := "fn("

def fnSep : String := "fn,"

def fnArrow : String := ")->"

/-- The parameters' and the result's segments of the function type
`segs`, if it is one: those of a function type within are its own. -/
def splitFnSegs (segs : Array String) : Option (Array (Array String) × Array String) := Id.run do
  unless segs[0]? == some fnSeg do return none
  let mut depth := 0
  let mut params := #[]
  let mut cur := #[]
  for i in [1:segs.size] do
    let s := segs[i]!
    if s == fnArrow && depth == 0 then
      return some (params.push cur, segs.extract (i + 1))
    if s == fnSeg then depth := depth + 1
    else if s == fnArrow then depth := depth - 1
    if s == fnSep && depth == 0 then
      params := params.push cur
      cur := #[]
    else cur := cur.push s
  return none

/-- Where a type is written (`lang::TypeSite`). -/
inductive TypeSite where
  | definedParameter
  | uninterpretedParameter
  | result
  | constant
  | variable
  | field
  | payload
  | definition
  | boundName
  | alias
  | closureParameter
  deriving Inhabited, DecidableEq, Repr

/-- A step from a type into one that it is built from (`lang::Within`). -/
inductive Within where
  | element
  | argument
  | fnParameter
  | fnResult
  deriving Inhabited, DecidableEq, Repr

/-- The steps from the type whose segments are `segs` (`setSeg`) down to
the first function type within it, outermost first, if there is one: each
element type of a set, relation or sequence, each type argument of an
instance, and each parameter or result of a function type on the way. -/
def fnTypeWithin (segs : List String) : Option (List Within) :=
  go segs []
where
  /-- `stack` holds the steps so far, innermost first, each with whether it
  is an instance's argument, which `argsSep` and `argsClose` end. -/
  go : List String → List Within → Option (List Within)
    | [], _ => none
    | s :: rest, stack =>
      if s == fnSeg then some stack.reverse
      else if s == setSeg || s == seqSeg || s == relSeg then go rest (.element :: stack)
      else if s == argsOpen then go rest (.argument :: stack)
      else if s == argsSep then go rest (.argument :: (stack.dropWhile (· != .argument)).drop 1)
      else if s == argsClose then go rest ((stack.dropWhile (· != .argument)).drop 1)
      else go rest stack

/-- The code of the error of a function type written at `site`, at the
steps `within` from the written type down to it, or `none` if it may be
written there (`lang::function_type_place`). -/
def fnTypeCode? (site : TypeSite) (within : List Within) : Option String :=
  if site == .definedParameter && within.isEmpty then none
  else if !within.isEmpty then some "F0435"
  else match site with
    | .field | .payload => some "F0432"
    | .variable => some "F0433"
    | _ => some "F0434"

/-- A function type written at `site`, at the steps `within` from the
written type down to it, where it may not be (`fnTypeCode?`). -/
def fnTypePlaceMsg (site : TypeSite) (within : List Within) : Msg :=
  let code := (fnTypeCode? site within).getD "F0434"
  let note := "note: functions are not values: a function type is only the whole type of a defined function's parameter, which an application gives a closure or a function's name"
  if code == "F0435" then
    { code? := some code, headline := "a function type cannot be within another type"
      label? := some "a function type here"
      notes := #[note] }
  else if code == "F0432" then
    { code? := some code, headline := "a function type cannot be the type of a field or a payload"
      label? := some "a function type"
      notes := #[note] }
  else if code == "F0433" then
    { code? := some code, headline := "a function type cannot be the type of a component's variable"
      label? := some "a function type"
      notes := #[note, "help: make the component's requirement a defined function's, with a function parameter"] }
  else
    { code? := some code, headline := "a function type is only the type of a defined function's parameter"
      label? := some "a function type"
      notes := #[note] }

/-- What a function type's parameter's or result's type is
(`lang::FnPart`). -/
inductive FnPart where
  | plain
  | nat
  | pattern
  | function
  deriving Inhabited, DecidableEq, Repr

/-- Whether a function type whose parameters' and result's types are
`parts` is accepted (`lang::function_type_parts`). -/
def fnPartsAccepted (parts : List FnPart) : Bool := parts.all (· == .plain)

/-- A `Nat` or a pattern type, `what`, within a function type
(`lang::function_type_parts`). -/
def fnPartMsg (what : String) : Msg :=
  { code? := some "F0435", headline := s!"a function type's parameter or result cannot be {what}, for now"
    label? := some s!"{what}"
    notes := #["note: a `Nat` or a pattern type brings a fact or an obligation of its values, which would be a contract of the function given, and a function parameter has none",
      "help: use the base type, as `Int`"] }

/-! ## Arguments -/

/-- What a parameter takes (`lang::ParamKind`). -/
inductive ParamKind where
  | value
  /-- A function of `n` parameters. -/
  | function (n : Nat)
  deriving Inhabited, DecidableEq, Repr

/-- An argument, as written (`lang::ArgShape`). -/
inductive ArgShape where
  /-- A closure of `n` parameters. -/
  | closure (n : Nat)
  | definedName
  | uninterpretedName
  | fnParameterName
  | other
  deriving Inhabited, DecidableEq, Repr

/-- The code of the error of the argument `arg` for a parameter that takes
`param`, or `none` if it is accepted (`lang::function_argument`). -/
def argumentCode? : ParamKind → ArgShape → Option String
  | .value, .other => none
  | .value, .definedName | .value, .uninterpretedName | .value, .fnParameterName => some "F0210"
  | .value, .closure _ => some "F0436"
  | .function n, .closure m => if n == m then none else some "F0436"
  | .function _, .definedName | .function _, .fnParameterName => none
  | .function _, .uninterpretedName | .function _, .other => some "F0436"

/-- A closure where no function is expected. -/
def closurePlaceMsg : Msg :=
  { code? := some "F0436", headline := "a closure is only an argument for a function parameter"
    label? := some "a closure here"
    notes := #["note: functions are not values: a closure is written only as an argument of a higher-order function, for its parameter of a function type"] }

/-- An argument for the function parameter of type `t` that is neither a
closure nor the name of a function. -/
def notAClosureMsg (t : FnTy) : Msg :=
  { code? := some "F0436", headline := s!"expected a closure or a function's name of type `{t.show}`"
    label? := some "not a function"
    notes := #["note: a function parameter takes a closure, as `|x| x + 1`, or the name of a defined function"] }

/-- The uninterpreted function `g` given for a function parameter. -/
def uninterpretedArgMsg (g : Lean.Name) : Msg :=
  { code? := some "F0436", headline := s!"the uninterpreted function `{showPath g}` cannot be given for a function parameter"
    label? := some "uninterpreted"
    notes := #["note: its applications would be within the higher-order function's body, where their arguments may mention an output of the component",
      "help: give a closure that applies a defined function, or apply the uninterpreted function outside and give its value"] }

/-- A closure of `n` parameters for a function parameter of type `t`. -/
def closureArityMsg (t : FnTy) (n : Nat) : Msg :=
  let ps (k : Nat) := if k == 1 then "1 parameter" else s!"{k} parameters"
  { code? := some "F0436", headline := s!"expected a closure of {ps t.params.size}, of type `{t.show}`, but it has {ps n}"
    label? := some s!"expected {ps t.params.size}" }

/-- The error of the argument `shape` for a function parameter of type `t`,
if it is not accepted (`argumentCode?`, `lang::function_argument`): `g` is
the function that a name names. -/
def argumentMsg? (t : FnTy) (shape : ArgShape) (g : Lean.Name := .anonymous) : Option Msg :=
  (argumentCode? (.function t.params.size) shape).map fun _ =>
    match shape with
    | .closure n => closureArityMsg t n
    | .uninterpretedName => uninterpretedArgMsg g
    | _ => notAClosureMsg t

/-- The error of a function type's parameter's or result's type, of the
kind `k`, if it is not accepted (`fnPartsAccepted`, `lang::function_type_parts`). -/
def fnPartMsg? (k : FnPart) : Option Msg :=
  if fnPartsAccepted [k] then none
  else some (match k with
    | .nat => fnPartMsg "a `Nat`"
    | .pattern => fnPartMsg "a pattern type"
    | _ => fnTypePlaceMsg .definedParameter [.fnParameter])

/-- The closure's body applies the uninterpreted function `g`. -/
def closureUninterpretedMsg (g : Lean.Name) : Msg :=
  { code? := some "F0331", headline := s!"a closure's body cannot apply uninterpreted function `{showPath g}`"
    label? := some "uninterpreted"
    notes := #["note: a closure's body is unfolded within a defined function's body, which applies no uninterpreted function",
      "help: apply it outside the closure, with `let`, and mention its value"] }

/-- A closure's parameter's type, which a type parameter that has no
argument yet mentions. -/
def closureParamUnknownMsg (f : String) : Msg :=
  { code? := some "F0400", headline := s!"cannot infer the type of this closure's parameter of `{f}`"
    label? := some "type not known"
    notes := #[s!"note: a closure's parameters take their types from `{f}`'s other arguments, or from their written types",
      "help: write its type, as `|x: Int| ...`"] }

/-! ## Applications -/

/-- A parameter of a higher-order function, as its signature declares it:
a value's type, or a function type, either of which may mention the
function's type parameters. -/
inductive HoParam where
  | value (t : Ty)
  | function (f : FnTy)
  deriving Inhabited, BEq

/-- The type of a value parameter, or the result type of a function one. -/
def HoParam.ty : HoParam → Ty
  | .value t => t
  | .function f => f.result

/-- Whether the parameter's declared type mentions the type parameter `k`. -/
def HoParam.mentions (k : Nat) : HoParam → Bool
  | .value t => t.mentions k
  | .function f => f.mentions k

/-- `b` with the arguments that matching `found` against the declared type
`d` gives the type parameters that have none yet, widened. -/
def giveArgs (b : Array (Option Ty)) (d found : Ty) : Array (Option Ty) :=
  b.mapIdx fun i a => if a.isNone && d.mentions i then (matchParam i d found).map (·.widen) else a

/-- Elaborates the arguments of an application of a higher-order function
(`Reqs/Lang/HigherOrder#applications`) with the type parameters `params`,
whose parameters are `declared` and whose result has the declared type
`result`, and returns its type arguments, as `inferCall` does those of a
generic function: what matching the expected type `expected?` against the
result gives first; then the values that do not wait, in order, each
giving the type parameters that its declared type mentions and that have
no argument yet; then the functions, in order, each elaborated by `elabFn`
with its parameters' types and its result's, where they are known, which
gives its parameters' types and its body's, and so arguments; and last
the values that wait. `unknown` reports type arguments that cannot be
inferred: before any argument is elaborated, if a type parameter has
neither an argument from what is expected nor an argument that could give
it one, and at the end, if one still has none. -/
def inferHigherOrder [Monad m] (params : Array Lean.Name) (declared : Array HoParam) (result : Ty) (synth : Array Bool)
    (expected? : Option Ty) (unknown : m Unit) (elabValue : Nat → Option Ty → m (Option Ty))
    (check : Nat → Ty → Ty → m Unit) (elabFn : Nat → Array (Option Ty) → Option Ty → m (Option (Array Ty × Ty)))
    (checkFn : Nat → FnTy → Array Ty × Ty → m Unit) : m (Array Ty) := do
  let init := expectedArgs result expected? params.size
  let gives (k : Nat) := (List.range declared.size).any fun j => match declared[j]! with
    | .value d => synth[j]?.getD false && d.mentions k
    | .function f => f.mentions k
  if (List.range params.size).any fun k => (init[k]?.join).isNone && !gives k then unknown
  let mut b := init
  let current (b : Array (Option Ty)) : Array Ty := b.mapIdx fun i a => a.getD (.param i params[i]!)
  let mut waiting := #[]
  for d in declared, k in [0:declared.size] do
    let .value d := d | continue
    if !d.unknownIn b then
      let x := d.subst (current b)
      if let some f ← elabValue k (some x) then check k x f
    else if synth[k]?.getD false then
      if let some f ← elabValue k none then
        b := giveArgs b d f
        check k (d.subst (current b)) f
    else waiting := waiting.push k
  for d in declared, k in [0:declared.size] do
    let .function ft := d | continue
    let ps := ft.params.map fun t => if t.unknownIn b then none else some (t.subst (current b))
    let r := if ft.result.unknownIn b then none else some (ft.result.subst (current b))
    if let some (pts, rt) ← elabFn k ps r then
      for t in ft.params, pt in pts do b := giveArgs b t pt
      b := giveArgs b ft.result rt
      checkFn k (ft.subst (current b)) (pts, rt)
  for k in waiting do
    let x := declared[k]!.ty.subst (current b)
    if let some f ← elabValue k (some x) then check k x f
  if b.any (·.isNone) then unknown
  return current b

/-- The note of a check of a closure's obligation, which the higher-order
function `f` gives it where it applies the closure (`lang::closure_obligation`). -/
def viaNote (f : Lean.Name) : String :=
  s!"note: in a closure given to `{showPath f}`, checked where `{showPath f}` applies it"

/-! ## Comparisons -/

/-- An operand of `=` or `!=`, as written (`lang::Comparand`). -/
inductive Comparand where
  | value
  | closure
  | functionName
  deriving Inhabited, DecidableEq, Repr

/-- Whether a comparison of `operands` is accepted
(`lang::function_comparison`). -/
def comparisonAccepted (operands : List Comparand) : Bool := operands.all (· == .value)

/-- A comparison, `op`, of a function. -/
def functionComparisonMsg (op : String) : Msg :=
  { code? := some "F0437", headline := s!"functions cannot be compared with `{op}`"
    label? := some "a function"
    notes := #["note: two functions are equal when they agree at every argument, which the solver cannot decide",
      "help: compare their values at an argument, as `f(x) = g(x)`"] }

/-! ## Capture (`lang::closure_capture`) -/

/-- The capture symbol numbered `k`, as the solver knows it, quoted: no
other symbol starts with `|#`. -/
def captureSym (k : Nat) : String := "|#" ++ toString k ++ "|"

/-- The capture symbols of the names `captured`, numbered from `next`, in
order. -/
def captureNames (next : Nat) (captured : List String) : List String :=
  (List.range captured.length).map fun i => captureSym (next + i)

/-- What a mention of `x` in a closure's body becomes, where `x` is not
bound within the body: a parameter's name is kept, and a captured name is
its capture symbol, numbered from `next` in the order of `captured`. -/
def captureRename (next : Nat) (captured params : List String) (x : String) : String :=
  if x ∈ params then x else
  match captured.idxOf? x with
  | some k => captureSym (next + k)
  | none => x

/-! ## Terms

The `fren` command's formulas are SMT-LIB text. To unfold a closure into a
higher-order function's body, it reads both as terms, whose atoms keep their
text: a quoted symbol is an atom with its `|`s. -/

/-- An SMT-LIB term. -/
inductive STerm where
  | atom (s : String)
  | list (ts : List STerm)
  deriving Inhabited, BEq, Repr

/-- The terms of `cs` from `i`, up to an unmatched `)`, and where they end. -/
partial def STerm.parseFrom (cs : Array Char) (i : Nat) : List STerm × Nat := Id.run do
  let mut i := i
  let mut out : Array STerm := #[]
  while i < cs.size do
    let c := cs[i]!
    if c.isWhitespace then i := i + 1
    else if c == ')' then return (out.toList, i + 1)
    else if c == '(' then
      let (ts, j) := STerm.parseFrom cs (i + 1)
      out := out.push (.list ts)
      i := j
    else if c == '"' then
      -- A string literal, in which `""` is a `"`.
      let mut j := i + 1
      while j < cs.size && !(cs[j]! == '"' && cs[j + 1]? != some '"') do
        j := if cs[j]! == '"' then j + 2 else j + 1
      out := out.push (.atom (String.ofList (cs.extract i (j + 1)).toList))
      i := j + 1
    else if c == '|' then
      let mut j := i + 1
      while j < cs.size && cs[j]! != '|' do j := j + 1
      out := out.push (.atom (String.ofList (cs.extract i (j + 1)).toList))
      i := j + 1
    else
      let mut j := i
      while j < cs.size && !(cs[j]!.isWhitespace || cs[j]! == '(' || cs[j]! == ')') do j := j + 1
      out := out.push (.atom (String.ofList (cs.extract i j).toList))
      i := j
  return (out.toList, i)

/-- The one term of `s`. -/
def STerm.parse (s : String) : STerm :=
  match (STerm.parseFrom s.toList.toArray 0).1 with
  | [t] => t
  | ts => .list ts

/-- The term as SMT-LIB text. -/
partial def STerm.print : STerm → String
  | .atom s => s
  | .list ts => "(" ++ " ".intercalate (ts.map STerm.print) ++ ")"

/-- The symbols that a binder form binds, and its body: `let`'s, and the
quantifiers'. -/
def STerm.binds? : List STerm → Option (List String × List STerm × STerm)
  | [.atom kw, .list bs, body] =>
    if kw == "let" || kw == "forall" || kw == "exists" || kw == "lambda" then
      some (bs.filterMap fun | .list (.atom x :: _) => some x | _ => none,
        bs.map fun | .list (_ :: rest) => .list rest | b => b, body)
    else none
  | _ => none

/-- Whether `kw` starts a binder form: `let`, or a quantifier. -/
def binderKw (kw : String) : Bool := kw == "let" || kw == "forall" || kw == "exists" || kw == "lambda"

/-- The symbol that a binding `(x ...)` of a binder form binds. -/
def bindName : STerm → Option String
  | .list (.atom x :: _) => some x
  | _ => none

/-- Whether the bindings `bs` of a binder form bind the symbol `s`. -/
def STerm.bound (bs : List STerm) (s : String) : Bool := (bs.filterMap bindName).contains s

mutual
/-- The atoms of `t` that no binder of `t` around them binds, in order. A
`let`'s definitions are outside its binders, a quantifier's sorts too. -/
def STerm.free : STerm → List String
  | .atom s => [s]
  | .list ts => STerm.freeL ts

/-- The free atoms of the list term `(ts)`, which may be a binder form. -/
def STerm.freeL : List STerm → List String
  | [.atom kw, .list bs, body] =>
    if binderKw kw then
      (if kw == "let" then STerm.freeDefs bs else []) ++ body.free.filter fun s => !STerm.bound bs s
    else kw :: (STerm.freeL bs ++ body.free)
  | [] => []
  | t :: ts => t.free ++ STerm.freeEach ts

/-- The free atoms of each of `ts`. -/
def STerm.freeEach : List STerm → List String
  | [] => []
  | t :: ts => t.free ++ STerm.freeEach ts

/-- The free atoms of the definitions of a `let`'s bindings `bs`. -/
def STerm.freeDefs : List STerm → List String
  | [] => []
  | .list (_ :: rest) :: bs => STerm.freeEach rest ++ STerm.freeDefs bs
  | b :: bs => b.free ++ STerm.freeDefs bs
end

mutual
/-- `t` with each atom that no binder of `t` around it binds renamed by
`σ`, where `σ` gives a new name: the new names are bound by no binder of
`t`, so that none is captured (`lang::closure_capture`). -/
def STerm.renameFree (σ : String → Option String) : STerm → STerm
  | .atom s => .atom ((σ s).getD s)
  | .list ts => .list (STerm.renameL σ ts)

/-- `renameFree` of the list term `(ts)`, which may be a binder form. -/
def STerm.renameL (σ : String → Option String) : List STerm → List STerm
  | [.atom kw, .list bs, body] =>
    if binderKw kw then
      [.atom kw, .list (if kw == "let" then STerm.renameDefs σ bs else bs),
        body.renameFree fun s => if STerm.bound bs s then none else σ s]
    else [.atom ((σ kw).getD kw), .list (STerm.renameL σ bs), body.renameFree σ]
  | [] => []
  | t :: ts => t.renameFree σ :: STerm.renameEach σ ts

/-- `renameFree` of each of `ts`. -/
def STerm.renameEach (σ : String → Option String) : List STerm → List STerm
  | [] => []
  | t :: ts => t.renameFree σ :: STerm.renameEach σ ts

/-- `renameFree` of the definitions of a `let`'s bindings `bs`. -/
def STerm.renameDefs (σ : String → Option String) : List STerm → List STerm
  | [] => []
  | .list (x :: rest) :: bs => .list (x :: STerm.renameEach σ rest) :: STerm.renameDefs σ bs
  | b :: bs => b.renameFree σ :: STerm.renameDefs σ bs
end

/-- A closure, as the solver sees it: its parameters' symbols and its body. -/
structure SClosure where
  params : List String
  body : STerm
  deriving Inhabited, Repr

/-- The list term `(ts)`, whose parts are unfolded already, unfolded if it
applies `f` (`STerm.inlineApps`). -/
def STerm.inlineList (f : String) (c : SClosure) (ts : List STerm) : STerm :=
  match ts with
  | .atom g :: args =>
    if g != f then .list ts else
    match c.body with
    | .list (.atom h :: xs) =>
      if xs == c.params.map .atom then .list (.atom h :: args)
      else .list [.atom "let", .list ((c.params.zip args).map fun (p, a) => .list [.atom p, a]), c.body]
    | _ => .list [.atom "let", .list ((c.params.zip args).map fun (p, a) => .list [.atom p, a]), c.body]
  | _ => .list ts

mutual
/-- `t` with each application of `f` replaced by the closure `c`: a `let` of
its parameters, at the application's arguments, around its body; or, if
`c` only applies `g` to its parameters, in order, the application of `g`.
The arguments are unfolded first. `c`'s free symbols other than its
parameters are capture symbols or global, which no binder of `t` binds. -/
def STerm.inlineApps (f : String) (c : SClosure) : STerm → STerm
  | .atom s => .atom s
  | .list ts => STerm.inlineList f c (STerm.inlineEach f c ts)

/-- `inlineApps` of each of `ts`. -/
def STerm.inlineEach (f : String) (c : SClosure) : List STerm → List STerm
  | [] => []
  | t :: ts => t.inlineApps f c :: STerm.inlineEach f c ts
end

/-- `t`, whose free symbols in `locals` other than `params` are renamed to
capture symbols numbered from `next`: the term, the capture symbols each
with the name it stands for, and the next number (`lang::closure_capture`). -/
def captureFree (t : STerm) (params : List String) (locals : String → Bool) (next : Nat) :
    STerm × List (String × String) × Nat :=
  let captured := t.free.eraseDups.filter fun s => locals s && !params.contains s
  let t' := t.renameFree fun s =>
    let r := captureRename next captured params s
    if r == s then none else some r
  (t', (captureNames next captured).zip captured, next + captured.length)

/-- An application of the higher-order function whose body is `body`
(SMT-LIB text), unfolded (`Reqs/Lang/HigherOrder#meaning`): `values` are
its other parameters' symbols with their arguments' terms, and `fns` its
function parameters' symbols, each with its closure, whose free symbols in
`locals` are captured. Capture symbols are numbered from `next`; gives the
term and the next number. -/
def inlineCall (body : String) (values : List (String × String)) (fns : List (String × SClosure))
    (locals : String → Bool) (next : Nat) : String × Nat := Id.run do
  let mut t := STerm.parse body
  let mut next := next
  let mut lets : List (String × String) := []
  for (f, c) in fns do
    let (b, ls, n) := captureFree c.body c.params locals next
    lets := lets ++ ls
    next := n
    t := t.inlineApps f { c with body := b }
  let binds := lets ++ values
  if binds.isEmpty then return (t.print, next)
  let bs := " ".intercalate (binds.map fun (x, v) => s!"({x} {v})")
  return (s!"(let ({bs}) {t.print})", next)

/-! ## Obligations of closures (`lang::closure_obligation`)

A closure's body is checked where it is unfolded: at each application of
its function parameter within the higher-order function's body, under the
guards around it there and at its arguments. -/

/-- What lies between a term and an application within it: an operand
evaluated only under a condition (`lang::guard`), or a binder, such as a
`let` or a quantifier's, which the front end reads. -/
inductive SiteFrame (α β : Type) where
  | guard (o : GuardedOperand) (c : α)
  | binder (b : β)
  deriving Inhabited

/-- The obligation `goal` at an application within a term, the frames
around which, outermost first, are `frames`: under each guard and binder.
`notF` negates a condition, `impF` makes an implication, and `bind` puts a
term under a binder. -/
def siteGoal (notF : α → α) (impF : α → α → α) (bind : β → α → α) : List (SiteFrame α β) → α → α
  | [], g => g
  | .guard o c :: fs, g => impF (o.guard c (notF c)) (siteGoal notF impF bind fs g)
  | .binder b :: fs, g => bind b (siteGoal notF impF bind fs g)

/-- Whether an obligation holds at an application under guards whose
conditions have the values of `frames`, where it holds there exactly when
`p`: as `siteGoal` gives it, of `Bool`s. -/
def siteHolds (frames : List (GuardedOperand × Bool)) (p : Bool) : Bool :=
  siteGoal (fun c => !c) (fun c a => !c || a) (fun (_ : Unit) a => a) (frames.map fun (o, c) => .guard o c) p

/-- The applications of the symbol `f` in `t`, each with the frames around
it, outermost first, and its arguments: `ite`'s branches, `=>`'s
conclusion, and `and`'s and `or`'s later operands are guarded; `let`s and
quantifiers are binders, each as the list `[kw, bindings]`, whose
definitions are not under them. -/
partial def STerm.sites (f : String) : STerm → List (List (SiteFrame STerm (List STerm)) × List STerm)
  | .atom _ => []
  | .list ts =>
    let inArgs := fun (xs : List STerm) => xs.flatMap (STerm.sites f)
    match ts with
    | .atom g :: args =>
      if g == f then ([], args) :: inArgs args
      else if g == "ite" then match args with
        | [c, a, b] => c.sites f ++ (a.sites f).map (fun (fs, xs) => (.guard .thenBranch c :: fs, xs))
            ++ (b.sites f).map (fun (fs, xs) => (.guard .elseBranch c :: fs, xs))
        | _ => inArgs args
      else if g == "=>" then match args with
        | [c, d] => c.sites f ++ (d.sites f).map (fun (fs, xs) => (.guard .whenBody c :: fs, xs))
        | _ => inArgs args
      else if g == "and" || g == "or" then
        let op : GuardedOperand := if g == "and" then .andRight else .orRight
        (args.zipIdx.flatMap fun (a, k) =>
          (a.sites f).map fun (fs, xs) => ((args.take k).map (SiteFrame.guard op) ++ fs, xs))
      else if (g == "let" || g == "forall" || g == "exists") then match args with
        | [.list bs, body] =>
          let defs := if g == "let" then bs.flatMap (fun | .list (_ :: d) => d.flatMap (STerm.sites f) | _ => []) else []
          defs ++ (body.sites f).map fun (fs, xs) => (.binder [.atom (if g == "let" then "let" else "forall"), .list bs] :: fs, xs)
        | _ => inArgs args
      else inArgs args
    | _ => inArgs ts

/-- An obligation `goal` of a closure whose parameters' symbols are
`params`, at each application of `f` in `body`, as one term: the
conjunction over the applications of `siteGoal`, at the application's
arguments, or `none` if `body` never applies `f`. -/
def closureObligation (body : STerm) (f : String) (params : List String) (goal : STerm) : Option STerm :=
  let gs := (body.sites f).map fun (fs, args) =>
    siteGoal (fun c => .list [.atom "not", c]) (fun c a => .list [.atom "=>", c, a])
      (fun b a => .list (b ++ [a])) fs
      (.list [.atom "let", .list ((params.zip args).map fun (p, a) => .list [.atom p, a]), goal])
  match gs with
  | [] => none
  | [g] => some g
  | gs => some (.list (.atom "and" :: gs))

end Fren.Core
