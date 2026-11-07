-- keep-sorted start
import FrenTest.FuzzFrontends.Random
-- keep-sorted end

open Lean FrenCli FrenCli.Eval

namespace FrenTest.FuzzFrontends.Wide

/-- Relation obligations below fields, payloads and collection quantifiers,
at calls and in the procedure's own inputs and defined outputs.
Drawn after `enumerationObligations`' original cases. `natural` appends
Nat-based subset types without changing the original draws. -/
def enumerationRelations (natural : Bool := false) : R String := do
  let (base, good, bad) ← if natural then pure ("Nat", "0", "1") else pick #[
    ("Bool", "true", "false"), ("Int", "0", "1"), ("String", "\"\"", "\"a\""),
    ("E", "E::A", "E::B"), ("N", "N(0)", "N(1)"),
    ("R", "R { value := 0 }", "R { value := 1 }"),
    ("Set<Bool>", "{}", "{true}"), ("Seq<Bool>", "[]", "[true]"),
    ("Rel<Bool, Bool>", "{}", "{(true, true)}"),
    ("Option<Int>", "Option::None", "Option::Some(1)")]
  let valueName := if base == "Bool" then "value?" else "value"
  let left ← pick #[good, bad]
  let right ← pick #[good, bad]
  let otherLeft ← pick #[good, bad]
  let otherRight ← pick #[good, bad]
  -- Nat may occur in fields and non-recursive payloads, but not directly
  -- as an element or type argument. Put the Nat-based subset in a field
  -- before using it inside relations and their surrounding types.
  let wrap (v : String) := if natural then s!"NatBox \{ value := {v} }" else v
  let (left, right, otherLeft, otherRight) := (wrap left, wrap right, wrap otherLeft, wrap otherRight)
  let (relation, first, second) ← pick #[
    ("Rel<Narrow, Narrow>", s!"\{({left}, {right})}", s!"\{({otherLeft}, {otherRight})}"),
    ("Rel<Narrow, Bool>", s!"\{({left}, true)}", s!"\{({otherLeft}, false)}"),
    ("Rel<Bool, Narrow>", s!"\{(false, {right})}", s!"\{(true, {otherRight})}")]
  let (ty, arg, other) ← pick #[
    (relation, first, second),
    (s!"Pair<{relation}, Narrow>", s!"Pair \{ first := {first}, second := {left} }", s!"Pair \{ first := {second}, second := {otherLeft} }"),
    (s!"Pair<Narrow, {relation}>", s!"Pair \{ first := {left}, second := {first} }", s!"Pair \{ first := {otherLeft}, second := {second} }"),
    (s!"Option<{relation}>", s!"Option::Some({first})", "Option::None"),
    (s!"Choice<{relation}>", s!"Choice::Two({first}, {second})", "Choice::Empty"),
    (s!"Set<{relation}>", s!"\{{first}}", "{}"),
    (s!"Seq<{relation}>", s!"[{first}]", s!"[{second}]"),
    (s!"Rel<{relation}, Narrow>", s!"\{({first}, {left})}", s!"\{({second}, {otherLeft})}"),
    (s!"Rel<Narrow, {relation}>", s!"\{({left}, {first})}", s!"\{({otherLeft}, {second})}"),
    (s!"Rel<{relation}, {relation}>", s!"\{({first}, {second})}", s!"\{({second}, {first})}"),
    (s!"Option<Pair<{relation}, {relation}>>", s!"Option::Some(Pair \{ first := {first}, second := {second} })", "Option::None"),
    (s!"Pair<Option<{relation}>, Choice<{relation}>>", s!"Pair \{ first := Option::Some({first}), second := Choice::One({second}) }", "Pair { first := Option::None, second := Choice::Empty }"),
    (s!"Set<Option<{relation}>>", s!"\{Option::Some({first})}", "{Option::None}"),
    (s!"Seq<Set<{relation}>>", s!"[\{{first}}]", "[{}]"),
    ("RelBox", first, second)]
  let relation := if natural then relation.replace "Narrow" "NatBox" else relation
  let ty := if natural then ty.replace "Narrow" "NatBox" else ty
  -- Newtypes have no type parameters. Keep the function's result erased
  -- and construct the constrained newtype at its giving site instead.
  let erased := (if ty == "RelBox" then relation else ty).replace "Narrow" base
  let definition ← pick #[arg, s!"if flag? then {arg} else {other}",
    s!"let saved: {erased} := {arg} in saved"]
  let options := "set_option fren.enumeration.size 1 in\nset_option fren.evidence \"enumerated\" in\n"
  let given := if ty == "RelBox" then "RelBox(nested_value(flag?))" else "nested_value(flag?)"
  -- Copying the input exercises both type facts. The call separately
  -- checks its named parts; output type-giving checks use the solver.
  let moduleName := if natural then "enum_natural_relation_obligations" else "enum_relation_obligations"
  return s!"\nmod {moduleName}\nset_option fren.lint.undecidable \"allow\"\n" ++
    "pub enum E { A, B }\npub struct N(Int)\npub struct R { value: Int }\n" ++
    "pub struct Pair<A, B> { first: A, second: B }\npub enum Choice<T> { Empty, One(T), Two(T, T) }\n" ++
    s!"pub type Narrow = {valueName}: {base} where first: {valueName} != {bad} and second: {valueName} = {good}\n" ++
    (if natural then "pub struct NatBox { value: Narrow }\n" else "") ++
    s!"pub struct RelBox({relation})\n" ++
    s!"pub proc accept_nested(arg: {ty}) \{}\n" ++
    s!"pub fn nested_value(flag?): {erased} := {definition}\n" ++ options ++
    s!"pub proc caller(flag?) \{ call c := accept_nested({given}) }\n" ++ options ++
    s!"pub proc own_membership(value: {ty}): (copy: {ty}) \{\n" ++
    "    call c := accept_nested(value)\n    out copy := value\n    expect same: copy = value\n}\n"

/-- Call-input obligations with two named parts, and predicate leaves with
inherited evidence (#813). `natural` generates additional Nat-based cases
and `guardOrders` further wrapper orders over every base type, drawn after
both modes' original cases. -/
def enumerationObligationCases (natural : Bool := false) (guardOrders : Bool := false) : R String := do
  let (base, good, bad) ← if natural then pure ("Nat", "0", "1") else pick #[
    ("Bool", "true", "false"), ("Int", "0", "1"), ("Nat", "0", "1"),
    ("String", "\"\"", "\"a\""), ("E", "E::A", "E::B"),
    ("N", "N(0)", "N(1)"), ("R", "R { value := 0 }", "R { value := 1 }"),
    ("Set<Bool>", "{}", "{true}"), ("Seq<Bool>", "[]", "[true]"),
    ("Rel<Bool, Bool>", "{}", "{(true, true)}"),
    ("Option<Int>", "Option::None", "Option::Some(1)")]
  let valueName := if base == "Bool" then "value?" else "value"
  let localName := if base == "Bool" then "saved?" else "saved"
  let moduleName := if natural then "enum_natural_obligations" else if guardOrders then "enum_guard_obligations" else "enum_obligations"
  let declarations := s!"mod {moduleName}\nset_option fren.lint.undecidable \"allow\"\n" ++
    "pub enum E { A, B }\npub struct N(Int)\npub struct R { value: Int }\n" ++
    "pub struct Pair<A, B> { first: A, second: B }\npub enum Choice<T> { Empty, One(T), Two(T, T) }\n" ++
    s!"pub type Narrow = {valueName}: {base} where first: {valueName} != {bad} and second: {valueName} = {good}\n" ++
    (if natural then "pub struct NatField { value: Narrow }\npub struct NatNewtype(Narrow)\n" ++
      "pub enum NatPayload { Empty, One(Narrow), Two(Narrow, Narrow) }\n" else "")
  let value ← pick #[good, bad]
  -- Every giving site, including nested generic payloads and fields.
  let field := s!"NatField \{ value := {value} }"
  let payload := s!"NatPayload::Two({value}, {good})"
  let (ty, arg) ← if natural then pick #[
    ("Narrow", value), ("NatField", field), ("NatNewtype", s!"NatNewtype({value})"),
    ("NatPayload", payload), ("Set<NatField>", s!"\{{field}}"), ("Seq<NatPayload>", s!"[{payload}]"),
    ("Rel<NatField, NatPayload>", s!"\{({field}, {payload})}"),
    ("Option<NatField>", s!"Option::Some({field})"),
    ("Pair<NatField, NatPayload>", s!"Pair \{ first := {field}, second := {payload} }"),
    ("Option<Pair<NatField, NatPayload>>", s!"Option::Some(Pair \{ first := {field}, second := {payload} })"),
    ("Pair<Option<NatField>, Choice<NatPayload>>", s!"Pair \{ first := Option::Some({field}), second := Choice::One({payload}) }")]
    else if base == "Nat" then pure ("Narrow", value) else pick #[
    ("Narrow", value), ("Pair<Narrow, Narrow>", s!"Pair \{ first := {value}, second := {good} }"),
    ("Option<Narrow>", s!"Option::Some({value})"),
    ("Choice<Narrow>", s!"Choice::Two({value}, {good})"),
    ("Set<Narrow>", s!"\{{value}}"), ("Seq<Narrow>", s!"[{value}]"),
    ("Rel<Narrow, Narrow>", s!"\{({value}, {good})}"),
    ("Option<Pair<Narrow, Narrow>>", s!"Option::Some(Pair \{ first := {good}, second := {value} })"),
    ("Pair<Option<Narrow>, Choice<Narrow>>", s!"Pair \{ first := Option::Some({value}), second := Choice::One({good}) }")]
  let argument := if base == "Bool" && ty == "Narrow" then "arg?" else "arg"
  let copy := if base == "Bool" && ty == "Narrow" then "copy?" else "copy"
  let definition ← pick #[arg, s!"if flag? then {arg} else {arg}", s!"let {copy}: {ty.replace "Narrow" base} := {arg} in {copy}"]
  let option ← pick #["enumerated", "enumerated+random"]
  let wrapper ← if natural || guardOrders then pick #[
    "let saved := value in when flag?, p?(saved)",
    "let saved := value in unless flag?, p?(saved)",
    "(when flag?, p?(saved)) where saved := value",
    "(unless flag?, p?(saved)) where saved := value",
    "let saved := value in when gate?, p?(saved) where gate? := flag?",
    "let saved := value in unless gate?, p?(saved) where gate? := flag?",
    "when flag?, let saved := value in p?(saved)",
    "unless flag?, let saved := value in p?(saved)"] else pick #[
    "p?(value)", "when flag?, p?(value)", "unless flag?, p?(value)",
    "let saved := value in p?(saved)", "not p?(value)",
    "p?(saved) where saved := value", "when flag?, let saved := value in p?(saved)",
    "let saved := value in not p?(saved)", "not (when flag?, p?(value))"]
  let wrapper := (wrapper.replace "value" valueName).replace "saved" localName
  let member ← pick #["", "set_option fren.evidence \"solver\" in ", "set_option fren.evidence \"enumerated\" in "]
  return declarations ++ s!"pub proc accept({argument}: {ty}) \{}\n" ++
    s!"set_option fren.enumeration.size 1 in\nset_option fren.evidence \"{option}\" in\n" ++
    s!"pub proc caller(flag?) \{ call c := accept({definition}) }\n" ++
    s!"pub fn p?({valueName}: {base}) := and \{ first: {valueName} != {bad}, second: {valueName} = {good} }\n" ++
    s!"set_option fren.enumeration.size 1 in\nset_option fren.evidence \"{option}\" in\n" ++
    s!"pub proc predicates({valueName}: {base}, flag?) \{ {member}expect property: {wrapper} }\n"

/-- Whole and split predicate checks under guards, negation and bindings.
These draws follow all existing enumeration cases. -/
def predicateCheckLocations : R String := do
  let (base, good, bad) ← pick #[
    ("Bool", "true", "false"), ("Int", "0", "1"), ("Nat", "0", "1"),
    ("String", "\"\"", "\"a\""), ("E", "E::A", "E::B"),
    ("N", "N(0)", "N(1)"), ("R", "R { value := 0 }", "R { value := 1 }"),
    ("Set<Bool>", "{}", "{true}"), ("Seq<Bool>", "[]", "[true]"),
    ("Rel<Bool, Bool>", "{}", "{(true, true)}"),
    ("Option<Int>", "Option::None", "Option::Some(1)")]
  let value := if base == "Bool" then "value?" else "value"
  let saved := if base == "Bool" then "saved?" else "saved"
  let option ← pick #["solver", "enumerated", "enumerated+random"]
  let guard ← pick #["when", "unless"]
  let order ← below 8
  let wrap (representative expression : String) : String :=
    let bound := expression.replace "VALUE" saved
    let expression := expression.replace "VALUE" representative
    match order with
    | 0 => s!"{guard} active?, {expression}"
    | 1 => s!"let {saved}: {base} := {representative} in {guard} active?, {bound}"
    | 2 => s!"{guard} active?, let {saved}: {base} := {representative} in {bound}"
    | 3 => s!"({guard} active?, {bound}) where {saved}: {base} := {representative}"
    | 4 => s!"{guard} active?, ({bound}) where {saved}: {base} := {representative}"
    | 5 => s!"let {saved}: {base} := {representative} in {guard} gate?, {bound} where gate? := active?"
    | 6 => s!"when active?, unless other?, {expression}"
    | _ => s!"unless active?, when other?, {expression}"
  -- A separate lint gap under `where` is outside these placement cases.
  -- Keep cover goals, but do not compare the unrelated trigger lint.
  let mut out := "\nmod enum_predicate_locations\nset_option fren.lint.trivial_cover \"allow\"\n" ++
    "pub enum E { A, B }\npub struct N(Int)\npub struct R { value: Int }\n"
  for op in #["and", "or", "iff", "one"] do
    out := out ++ s!"pub fn p_{op}?({value}: {base}, other?) := {op} \{ first: {value} != {bad}, second: other? }\n"
  for op in #["and", "or", "iff", "one"] do
    -- Closed typed representatives make member notes comparable without
    -- relying on which valid data model each backend chooses.
    let representative := if op == "and" then good else bad
    out := out ++ s!"set_option fren.enumeration.size 1 in\nset_option fren.evidence \"{option}\" in\n" ++
      s!"pub proc {op}_checks(active?, other?) \{\n" ++
      s!"    expect positive: {wrap representative s!"p_{op}?(VALUE, other?)"}\n" ++
      s!"    expect negative: {wrap representative s!"not p_{op}?(VALUE, other?)"}\n" ++
      s!"    cover witness: {wrap representative s!"p_{op}?(VALUE, other?)"}\n}\n"
  -- Contracts use the same source policy as procedure constraints.
  let op ← pick #["and", "or", "iff", "one"]
  out := out ++ s!"pub fn contracted?(active?): (result?) \{\n" ++
    "    out result? := true\n" ++
    s!"    ensure post: {guard} active?, not p_{op}?({good}, result?)\n}\n"
  return out

/-- The original enumeration cases, optionally followed by relation cases,
then Nat-based subset types, further `let`/`where` guard orders and whole
predicate check locations. All new draws follow both modes' existing
draws, preserving their original specs as prefixes. -/
def enumerationObligations (relations : Bool := false) : R String := do
  let original ← enumerationObligationCases
  let originalRelations ← if relations then enumerationRelations else pure ""
  let natural ← enumerationObligationCases true
  let naturalRelations ← if relations then enumerationRelations true else pure ""
  let guardOrders ← enumerationObligationCases (guardOrders := true)
  let locations ← predicateCheckLocations
  return original ++ originalRelations ++ "\n" ++ natural ++ naturalRelations ++ "\n" ++ guardOrders ++ locations

end FrenTest.FuzzFrontends.Wide
