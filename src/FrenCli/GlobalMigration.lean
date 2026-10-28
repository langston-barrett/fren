-- keep-sorted start
import FrenCli.Elab
-- keep-sorted end

/-! Migration of the removed global behaviour binders. Normal elaboration
still rejects procedure names as quantifier types. Only `fren fix` calls
this source transformation, before applying ordinary lint fixes. -/
namespace FrenCli.GlobalMigration

open Lean Fren.Core

abbrev Edits := Array (Range × String)
abbrev Substitution := Array (String × String)
abbrev Translate := StateM (Array String)

def typeSpanIn (src : Array Char) (ty : Array Ident) : Span := Id.run do
  let sp := typeSpan ty
  let mut depth : Int := 0
  for c in src.extract sp.start sp.stop do
    if c == '<' then depth := depth + 1 else if c == '>' then depth := depth - 1
  let mut stop := sp.stop
  while depth > 0 && stop < src.size do
    if src[stop]! == '>' then depth := depth - 1
    stop := stop + 1
  return { sp with stop }

def slice (src : Array Char) (sp : Span) : String :=
  String.ofList (src.extract sp.start sp.stop).toList

/-- Render a reference in its original scope, remembering the absolute
imports needed by the generated block. Local substitutions apply only to
unqualified names, and preserve field projections. -/
def reference (table : Table) (scope : Name) (subs : Substitution)
    (segs : Array Ident) : Translate Edits := do
  if segs.isEmpty then return #[]
  let sp := segs[0]!.span.to segs.back!.span
  let parts := segs[0]!.name.splitOn "."
  if segs.size == 1 then
    if let some (_, value) := subs.reverse.find? (·.1 == parts.head!) then
      let suffix := if parts.length == 1 then "" else "." ++ ".".intercalate parts.tail
      return #[(toRange sp, value ++ suffix)]
  let tail := segs.back!.name.splitOn "."
  let reference := segs.set! (segs.size - 1) { segs.back! with name := tail.head! }
  let suffix := if tail.length == 1 then "" else "." ++ ".".intercalate tail.tail
  match table.resolvePath scope (segNames reference) with
  | .error _ => return #[] -- builtins, or a locally bound name
  | .ok r =>
    let path := r.path
    let text := showPath path ++ suffix
    -- Prelude names are already in scope and their private module is not
    -- writable in source.
    unless path.components.head? == some preludeModule do
      let root := path.components.headD .anonymous
      modify fun imports => if imports.contains root.toString then imports else imports.push root.toString
    return #[(toRange sp, text)]

/-- A copied local declaration no longer needs `!` when the name it hid
was an input that has just been renamed (or an inlined local definition).
Keep the marker if an item of that name remains in its original scope. -/
def declaration (table : Table) (scope : Name) (subs : Substitution) (x : Ident) : Edits :=
  let n := (declaredIdent x).1.name
  if x.name.endsWith "!" && (subs.reverse.find? (·.1 == n)).any (·.2 != n) &&
      (table.resolvePath scope #[Name.mkSimple n]).toOption.isNone then
    #[(toRange x.span, n)]
  else #[]

partial def pattern (table : Table) (scope : Name) (subs : Substitution) : Pattern → Translate Edits
  | .variant _ segs args => do
    let binder := segs.size == 1 && args.isNone &&
      !((table.resolvePath scope (segNames segs)).toOption.any fun r => match r with | .variant .. => true | _ => false)
    let own ← if binder then pure (declaration table scope subs segs[0]!) else reference table scope subs segs
    return own ++ (← (args.getD #[]).foldlM (fun es p => return es ++ (← pattern table scope subs p)) #[])
  | .or _ ps => ps.foldlM (fun es p => return es ++ (← pattern table scope subs p)) #[]
  | .range _ lo hi _ => (lo.toArray ++ hi.toArray).foldlM (fun es b => do
      match b with
      | .path _ segs => return es ++ (← reference table scope subs segs)
      | _ => return es) #[]
  | _ => pure #[]

def patternLocals (table : Table) (scope : Name) (p : Pattern) : Substitution :=
  p.names.filterMap fun x =>
    if ((table.resolvePath scope #[Name.mkSimple x.name]).toOption.any fun r =>
        match r with | .variant .. => true | _ => false) then none
    else let n := (declaredIdent x).1.name; some (n, n)

partial def testLocals (table : Table) (scope : Name) : Expr → Substitution
  | .is _ _ p => patternLocals table scope p
  | .bin _ "and" a b => testLocals table scope a ++ testLocals table scope b
  | _ => #[]

/-- Types are flattened by the parser. Resolve each maximal path, leaving
punctuators and built-in type constructors alone. -/
def typeEdits (table : Table) (scope : Name) (segs : Array Ident) : Translate Edits := do
  let mut es := #[]
  let mut path := #[]
  for seg in segs do
    if #[setSeg, seqSeg, relSeg, relSep, argsOpen, argsClose, argsSep, fnSeg, fnSep, fnArrow].contains seg.name then
      es := es ++ (← reference table scope #[] path)
      path := #[]
    else if let some p := seg.pattern? then
      es := es ++ (← reference table scope #[] path) ++ (← pattern table scope #[] p)
      path := #[]
    else path := path.push seg
  return es ++ (← reference table scope #[] path)

/-- Patch only references in the syntax tree, never comments, strings or
field labels. Local binders mask the substitution in precisely their scope. -/
partial def expression (table : Table) (scope : Name) (subs : Substitution) (e : Expr) : Translate Edits := do
  let mask (xs : Array String) := subs.filter fun (n, _) => !xs.contains n
  match e with
  | .path _ segs => reference table scope subs segs
  | .when _ negated cond body => do
    return (← expression table scope subs cond) ++
      (← expression table scope (subs ++ if negated then #[] else testLocals table scope cond) body)
  | .bin _ "and" a b => do
    return (← expression table scope subs a) ++
      (← expression table scope (subs ++ testLocals table scope a) b)
  | .ite _ cond yes no => do
    return (← expression table scope subs cond) ++
      (← expression table scope (subs ++ testLocals table scope cond) yes) ++
      (← expression table scope subs no)
  | .quant _ _ bs body => do
    let mut es := #[]
    for b in bs do
      es := es ++ (← typeEdits table scope b.ty)
      for x in b.names do es := es ++ declaration table scope subs x
    -- Identity substitutions also prevent qualification of bound names.
    let names := bs.flatMap (·.names) |>.map fun x => (declaredIdent x).1.name
    return es ++ (← expression table scope (mask names ++ names.map (fun n => (n, n))) body)
  | .«let» _ defs body _ => do
    let mut es := #[]
    let mut locals := subs
    for (x, ty, value) in defs do
      es := es ++ (← expression table scope locals value)
      if let some ty := ty then es := es ++ (← typeEdits table scope ty)
      es := es ++ declaration table scope locals x
      let n := (declaredIdent x).1.name
      locals := locals.push (n, n)
    return es ++ (← expression table scope locals body)
  | .closure _ ps body => do
    let mut es := #[]
    for (x, ty) in ps do
      if let some ty := ty then es := es ++ (← typeEdits table scope ty)
      es := es ++ declaration table scope subs x
    let names := ps.map fun (x, _) => (declaredIdent x).1.name
    return es ++ (← expression table scope (mask names ++ names.map (fun n => (n, n))) body)
  | .match _ scrutinee arms _ => do
    let mut es ← expression table scope subs scrutinee
    for (p, guard, body) in arms do
      es := es ++ (← pattern table scope subs p)
      let locals := subs ++ patternLocals table scope p
      for g in guard.toArray do es := es ++ (← expression table scope locals g)
      es := es ++ (← expression table scope locals body)
    return es
  | _ =>
    let mut es := #[]
    match e with
    | .app _ segs _ | .record _ segs _ => es := es ++ (← reference table scope subs segs)
    | .is _ _ p => es := es ++ (← pattern table scope subs p)
    | _ => pure ()
    match e with
    | .record _ _ fs | .update _ _ fs =>
      for (field, value) in fs do
        if value.isNone then
          let edits ← reference table scope subs #[field]
          for (r, text) in edits do es := es.push (r, field.name ++ " := " ++ text)
    | _ => pure ()
    for child in e.operands do es := es ++ (← expression table scope subs child)
    return es

def rewritten (src : Array Char) (sp : Span) (es : Edits) : String :=
  let es := es.filterMap fun (r, t) =>
    if sp.start <= r.start && r.stop <= sp.stop then
      some ({ start := r.start - sp.start, stop := r.stop - sp.start : Range }, t)
    else none
  applyEdits (src.extract sp.start sp.stop) es

/-- A globally fresh source name. Boolean names keep their required `?`. -/
def fresh (used : Array String) (base : String) : String := Id.run do
  let bool := base.endsWith "?"
  let stem := if bool then (base.dropEnd 1).toString else base
  let mut n := base
  let mut k := 0
  while used.contains n do
    k := k + 1
    n := stem ++ "_" ++ toString k ++ (if bool then "?" else "")
  return n

def identifiers (src : Array Char) : Array String :=
  match lex src with
  | .ok ts => ts.filterMap fun t => match t.tok with
    | .ident n =>
      let n := (n.splitOn ".").head!
      some (if n.endsWith "!" then (n.dropEnd 1).toString else n)
    | _ => none
  | .error _ => #[]

/-- One old item, including value-only binders. All names occurring in
any source text are reserved before allocating parameters or assumptions. -/
def global (st : State) (module : Name) (src : Array Char) (start : Nat)
    (name : Ident) (bs : Array Binder) (body : Expr) : Option (Range × String) := do
  guard (!bs.isEmpty)
  -- A value-only leading quantifier remains an ordinary expression in
  -- the supported short form. The migration concerns behaviour binders.
  guard (bs.any fun b => ((st.table.resolvePath module (segNames b.ty)).toOption).any fun r =>
    st.comps.any (·.path == r.path))
  let mut used := identifiers src ++ (st.table.scopeOf module).map nameText
  for c in st.comps do
    used := used ++ identifiers c.migrationSource
  let mut parameters : Array String := #[]
  let mut assumptions : Array String := #[]
  let mut calls : Array String := #[]
  let mut imports := #[]
  for b in bs do
    let callee? := (st.table.resolvePath module (segNames b.ty)).toOption.bind fun r =>
      st.comps.find? (·.path == r.path)
    for x in b.names do
      if let some c := callee? then
        let mut subs : Substitution := #[]
        let mut args := #[]
        for v in c.vars.filter (fun v => v.role == .input && v.name.isAtomic) do
          let n := fresh used ((declaredIdent x).1.name ++ "_" ++ nameText v.name)
          used := used.push n
          let ty := c.migrationMembers.findSome? fun
            | .var true _ _ y ty _ => if (declaredIdent y).1.name == nameText v.name then ty else none
            | _ => none
          let (text, more) := match ty with
            | some ty => ((rewritten c.migrationSource (typeSpanIn c.migrationSource ty)) <$>
                typeEdits st.table c.path ty).run imports
            | none => ("Bool", imports)
          imports := more
          parameters := parameters.push (n ++ ": " ++ text)
          subs := subs.push (nameText v.name, n)
          args := args.push n
        -- Definitions are already sorted by dependency by elaboration.
        -- Collect all of them before translating any assumption.
        for (decl, _) in c.defs do
          if let some (y, value) := c.migrationMembers.findSome? fun
              | .var false false _ y _ (some value) =>
                if Name.mkSimple (declaredIdent y).1.name == decl then some (y, value) else none
              | _ => none then
            let (es, more) := (expression st.table c.path subs value).run imports
            imports := more
            let text := rewritten c.migrationSource (value.writtenSpan c.migrationSource) es
            subs := subs.push ((declaredIdent y).1.name, "(" ++ text ++ ")")
        for m in c.migrationMembers do
          if let .prop .assume y value := m then
            let (es, more) := (expression st.table c.path subs value).run imports
            imports := more
            let n := fresh used ((declaredIdent x).1.name ++ "_" ++ y.name)
            used := used.push n
            assumptions := assumptions.push ("    assume " ++ n ++ ": " ++
              rewritten c.migrationSource (value.writtenSpan c.migrationSource) es)
        calls := calls.push ("    call " ++ x.name ++ " := " ++ slice src (typeSpanIn src b.ty) ++
          "(" ++ ", ".intercalate args.toList ++ ")")
      else
        parameters := parameters.push (x.name ++ ": " ++ slice src (typeSpanIn src b.ty))
  let end_ := (body.writtenSpan src).stop
  let uses := imports.map ("    use " ++ ·)
  let text := "expect " ++ name.name ++ "(" ++ ", ".intercalate parameters.toList ++ ") {\n" ++
    "\n".intercalate (uses ++ assumptions ++ calls ++
      #["    expect " ++ name.name ++ ": " ++ slice src (body.writtenSpan src)]).toList ++ "\n}"
  return ({ start, stop := end_ }, text)

partial def item (st : State) (src : Array Char) (module : Name) : Item → Name × Edits
  | .mod _ path => ((segNames path).foldl (· ++ ·) .anonymous, #[])
  | .global name bs body =>
    (module, (global st module src (wordStart src name.span.start) name bs body).toArray)
  | .lintSetting _ _ _ _ _ (some body) => item st src module body
  | _ => (module, #[])

def file (st : State) (src : Array Char) (items : Array Item) : Edits :=
  (items.foldl (init := (Name.anonymous, #[])) fun (module, es) i =>
    let (module, more) := item st src module i
    (module, es ++ more)).2

end FrenCli.GlobalMigration
