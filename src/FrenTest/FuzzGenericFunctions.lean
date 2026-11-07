import FrenCli.Search

/-! Generic function instances, in an independent generator so extending
their forms never changes an existing mode's seed. -/

namespace FrenTest.FuzzGenericFunctions

open FrenCli.Eval

/-- Defined, uninterpreted, higher-order and recursive generic functions.
Type arguments include every type family and nested collections and
datatypes; calls occur in bodies, preconditions and postconditions, with
permuted parameters, quantifiers and unspecified values. -/
def spec : R String := do
  let bases := #["Int", "Nat", "Bool", "String", "Atom", "Label", "Count", "Option<Int>", "Box<Bool>"]
  let base := bases[← below bases.size]!
  -- Generic calls widen Nat to Int; collection element types cannot be Nat.
  let image := if base == "Nat" then "Int" else base
  let mut ty := image
  let mut mayFinite := !#["Int", "Nat", "String", "Count", "Option<Int>"].contains base
  for _ in [0:(← below 3)] do
    let relation := (ty.splitOn "Rel<").length == 1
    let form ← below (if relation then 7 else 4)
    -- Abstract types may be collection elements, but not datatype payloads.
    let form := if base == "Atom" && (form == 2 || form == 3) then 0 else form
    if form == 0 then mayFinite := false
    ty := match form with
      | 0 => s!"Seq<{ty}>"
      | 1 => s!"Set<{ty}>"
      | 2 => s!"Option<{ty}>"
      | 3 => s!"Box<{ty}>"
      | 4 => s!"Rel<{ty}, Bool>"
      | 5 => s!"Rel<Bool, {ty}>"
      | _ => s!"Rel<{ty}, {ty}>"
  let cmp := #["=", "!="][← below 2]!
  let order := #["<", "<=", ">", ">=", "=", "!="][← below 6]!
  let x := if ty == "Bool" then "x?" else "x"
  let y := if base == "Bool" then "y?" else "y"
  let z := if ty == "Bool" then "z?" else "z"
  let orderedY := if image == "Bool" then "ordered_y?" else "ordered_y"
  -- Uninterpreted functions of finite-element sets are outside the core.
  let contractArg := if mayFinite && (ty.startsWith "Set<" || ty.startsWith "Rel<") then y else x
  -- String ordering with a function result needs a literal operand.
  let rhs := if base == "String" then "\"m\"" else y
  let ordered := if #["Int", "Nat", "String", "Label", "Count"].contains base then
    s!"    expect ordering: {orderedY} {order} {rhs}\n" else ""
  let v := if ty == "Bool" then "v?" else "v"
  let call := #[s!"identity({x})", s!"nested({x})", s!"apply({x}, |{v}| identity({v}))"][← below 3]!
  return "mod generic_instances\n" ++
    "pub type Atom\npub ordered enum Label { A, B }\npub ordered struct Count(Int)\npub struct Box<T> { value: T }\n" ++
    "pub enum GList<T> { Nil, Cons(T, GList<T>) }\n" ++
    "pub fn identity<T>(x: T): T := x\n" ++
    "pub fn apply<T>(x: T, f: fn(T) -> T): T := f(x)\n" ++
    "pub fn nested<T>(x: T): T := identity(identity(x))\n" ++
    "pub fn swap<A, B>(a: A, b: B): (r: A) {\n" ++
    "    out r := identity(a)\n    ensure same: r = a and identity(b) = b\n}\n" ++
    "pub fn permuted<A, B>(a: A, b: B): B := swap(b, a)\n" ++
    "pub fn choose<T>(a: T, b: T): (r: T) {\n" ++
    "    require equal: identity(a) = identity(b)\n    ensure same: r = a\n}\n" ++
    "pub fn unknown<T>(T): T\n" ++
    "pub fn coupled<A, B>(a: A, b: B): (r: A) {\n" ++
    "    ensure uses: r = choose(a, a) and unknown(b) = unknown(b)\n}\n" ++
    "pub fn shape<A, B>(x: Box<Seq<Option<A>>>, y: Rel<B, A>): Box<Seq<Option<A>>> := x\n" ++
    "pub fn first<T>(q: Seq<T>): T := q[0]\n" ++
    "pub fn missing<T>(x: T): T := first([])\n" ++
    "pub fn contains?<T>(q: Seq<T>, x: T) := exists (v: T), v in q and identity(v) = x\n" ++
    "pub fn length<T>(q: GList<T>): Nat := match q { GList::Nil => 0, GList::Cons(_, r) => 1 + length(r) }\n" ++
    s!"pub proc instances({x}: {ty}, {y}: {base}): (det {z}: {ty}, det {orderedY}: {image}) \{\n" ++
    s!"    out {z} := {call}\n" ++
    s!"    out {orderedY} := identity({y})\n" ++
    s!"    expect defined: {z} {cmp} {x}\n" ++
    s!"    expect permutation: swap({x}, {y}) = {x} and swap({y}, {x}) = {y} and permuted({x}, {y}) = {y}\n" ++
    s!"    expect contract: choose({contractArg}, {contractArg}) = {contractArg}\n" ++
    s!"    expect through_contract: coupled({contractArg}, {y}) = {contractArg}\n" ++
    s!"    expect nested_shape: shape(Box \{ value := [Option::Some({x})] }, \{({y}, {x})}) = Box \{ value := [Option::Some({x})] }\n" ++
    s!"    expect unspecified: missing({x}) = first([])\n" ++
    s!"    expect quantified: contains?([{x}], {x})\n" ++
    s!"    expect recursive: length(GList::Cons({x}, GList::Nil)) = 1\n" ++ ordered ++ "}\n"

end FrenTest.FuzzGenericFunctions
