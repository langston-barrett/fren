# Meaning

The rules of the other chapters rest on a few facts about what an
expression means: an expression that mentions no variable has the same
value in every behaviour, where it is specified, which is why `2 * x` is
linear; the same expression has the same value wherever it is written,
which is what a lint such as `eq_op` relies on. This chapter states that
meaning once, as a model that the other chapters
[call](Calls.md) or [refine](Refinement.md), so that the rules
are stated over it rather than over facts given as inputs.

```fren
pub mod lang
```

## Values

`lang::Value` is the value of an expression, of any type: a `Bool`, an
`Int` (a `Nat` too), a `String`, a list, or a value of an enumeration,
record or newtype, by its variant, record or newtype and its payload's or
fields' values as a list, a record's in the order the record declares its
fields. A sequence is a list of its elements, and a set or relation a list
of its members, in an order the spec does not fix. A list is `Nil` or
`Cons(v, rest)`, since an enumeration may not contain itself within a
sequence (see [Sequences](Types.md#sequences)). A value of an abstract
type is not one of these: it is read from the environment, and compared
only with `=`. Names are `Id`s (see [Bindings](Scope.md#bindings)):

```fren
pub enum Value { B(Bool), I(Int), S(String), Nil, Cons(Value, Value), C(Id, Value) }
```

## Layers

An expression is a tree of *layers*. Each layer is a `lang::Head`, the
form of the expression at its root with everything in it that is not an
expression, and has the expressions below it as its *parts*: `x + f(y)` is
the layer `Op("+", "")` with parts `x` and `f(y)`, and `f(y)` is the layer
`Uninterpreted("f")` with the part `y`.

- `Literal(v)` is a literal, with its value `v`, and `Bound(v)` is a
  [quantifier's](Quantifiers.md) bound name of a listed type, with its
  value `v` in one instance of the quantifier.
- `Constant(c)` is a [constant](Items.md#constants), a variant without a
  payload, or another path of more than one segment.
- `Variable(x)` is a variable of the procedure or of one of its
  [calls](Calls.md#call-variables), or a field read from one,
  as `x` or `w.x`, or the bound name of an [unbounded
  quantifier](Quantifiers.md#unbounded-quantifiers), which stands for
  every value of its type at once.
- `Definition(x)` is a variable with a
  [definition](Procedures.md#definitions), a result or a `let`
  variable, or a name of a [`let` or `where`](Let.md), whose one part is its
  definition.
- `Binder(b)` is a binder of a [`match` arm](Expressions.md#matches) or of
  a [pattern test](Expressions.md#pattern-tests), whose one part is its
  scrutinee. `b` is not its name but where its pattern declares it: the
  variants and fields that lead from the pattern's root to it, such as
  `Pair.1` for `y` in `Pair(_, y)`. So the `y` of `Pair(y, _)` is another
  head, and a binder never shares a head with a name of a `let`.
- `Construction(c, order)` is a
  [variant](Expressions.md#variants-with-payloads), a [record
  literal](Expressions.md#records) or a [newtype](Expressions.md#newtypes)
  `c` built from its parts. A record literal's parts are its fields'
  values in the order the record declares them, and `order` is the order
  in which they are written, which does not change the value.
- `Method(m)`, `Uninterpreted(f)` and `Defined(f)` are a
  [method](Expressions.md#methods) call, whose parts are its receiver and
  arguments, and applications of an uninterpreted and of a defined
  [function](Items.md#functions), whose parts are the arguments.
- `Op(o, s)` is any other expression, named by its operator `o`, with its
  static parts `s`: an operator, `when` and `unless`, a conditional, a
  `match` (whose parts are its scrutinee and its arms' guards and bodies,
  and whose static parts are its arms' patterns), a
  [table](Expressions.md#tables), a [pattern
  test](Expressions.md#pattern-tests) (with its pattern), a [cardinality
  operator](Expressions.md#cardinality), indexing, as `Op("[]", "")`, a
  field read from an expression that is not a name, as `Op(".", f)` with
  the field `f`, a [record
  update](Expressions.md#record-updates) (with the fields it sets), a
  literal of a set, pair or sequence (as `Op("[..]", "")`), and a `let` (whose only part is its
  body).

A [quantifier](Quantifiers.md) is not one layer: its body is evaluated at
every value of its bound names, so its value is not a function of one
value of each part. Its body's layers are, each in one instance, or with
its bound names read from the environment. A later slice of the model
states quantifiers.

```fren
pub enum Head {
    Literal(Value),
    Bound(Value),
    Constant(Id),
    Variable(Id),
    Definition(Id),
    Binder(Id),
    Construction(Id, Id),
    Method(Id),
    Uninterpreted(Id),
    Defined(Id),
    Op(Id, Id),
}
```

A name written alone is the layer that its binding says (see [Laws of
scope](ScopeLaws.md#names-as-layers)).

What an expression mentions is named apart, so that a variable and a
function of the same name are two mentions:

```fren
pub enum Mention { Var(Id), Fn(Id) }
```

## Environments

An `Env` is a behaviour together with an [interpretation](Procedures.md#interpretations)
of the spec's abstract types and functions: everything that the spec
does not fix, including the values of the bound names of unbounded
quantifiers. It is read in three ways: `lookup(env, x)` is the value of
the variable or bound name `x`, `meaning(env, f, args)` the value of the
uninterpreted function `f` at the arguments `args`, and
`unspecified(env, head, parts)` the value of a layer where the language
leaves it unspecified. These three are all an expression reads of its
environment.

Everything else is fixed by the *program*, the spec being read: its
declarations, of constants, defined functions, records and the rest. A
`Program` is the same in every behaviour, so it is apart from the `Env`.
`fixed_value(program, head, parts)` is the value of a layer whose meaning
the spec states, at its parts' values: the value of a constant, the body
of a defined function at its arguments, a method, the part of a
scrutinee's value where a binder is declared, and an operator.
`fixed_specified?(program, head, parts)` says that it is specified. It is
not where the operator is an [index out of range](Expressions.md#sequences),
a `match` or table where no arm is taken, or a binder whose scrutinee does
not have its variant, and not where a constant's value or a defined
function's body is unspecified, or applies a function outside its
[preconditions](Items.md#contracts) (see
[Definedness](../Check.md#definedness)). Neither function takes an `Env`,
so neither differs between behaviours. Their values are stated by the
chapters on each construct, and this chapter states those of constants and
defined functions: `definition_value(program, x, args)` is the value of
the definition of the constant or defined function `x`, its body, as an
expression, in every environment that binds its parameters to the
arguments `args`, none for a constant: a body reads only its parameters,
so every such environment gives it one value, where it is specified.
Where `fixed_specified?` holds, `step` gives `Constant(c)` the value of
`c`'s definition, and `Defined(f)` that of `f`'s body at the parts'
values: the parameters substituted by the arguments, as [Defined
functions](Items.md#defined-functions) states. A body applies only
earlier declarations, so its value is well-founded on the order of the
declarations. Recursion in defined functions (#279) would break that
order, and the evaluation would need another measure.

A parameter of a function type (#305) would add one case here: it is
bound to a closure, whose body is substituted for its applications, rather
than to a value: `definition_value` then takes such an argument as a
closure, and the environment of the body binds it in the program, not as a
variable. A body then reads more than its parameters, which is the premise
of `frame` for a definition, so the closure's own mentions join the
application's. An [uninterpreted function with type
parameters](GenericFunctions.md#uninterpreted-generic-functions) is one
unknown function for each instance of them: its `Uninterpreted(f)` head
names the instance in `f`, as `pick<Int>`, so that `meaning`, which is read
at that name, is one function for each.

Their [interpretation](../Impl.md#interpretations) in Lean,
`Fren.Core.Meaning`'s, takes a program to be its declarations in order,
and evaluates each definition with the declarations before it. It covers
only a fragment, and is unspecified elsewhere: the operators `not`,
`iff`, `-`, `+`, `*`, and `div` and `mod` by a divisor other than `0`;
`<`, `<=`, `>` and `>=` over integers; `=` and `!=` over values built
from `Bool`s, integers and strings by variants, records and newtypes;
`++` over two strings or two sequences; `at_most_one?`, `exactly_one?` and
the pattern test; indexing in range, `Op("[]", "")`, and a field read,
`Op(".", f)`, of a record or a newtype; the methods `abs`, `min` and
`max` of integers and `len` of a string or a sequence; a binder; a
choice, by the arm that fires; a sequence literal, `Op("[..]", "")`; and
constants and defined functions whose definitions are in that fragment.
It takes a definition to be specified only where each of its body's
layers is, including those that the body does not evaluate, so it is
stricter than the language: `fn safe(q: Seq<Int>, i: Int): Int := if 0 <= i
< q.len then q[i] else 0` is unspecified there where `i` is out of range,
though the language gives it `0`. `=` over sets, relations and sequences,
`<` over strings, and the operators of sets and relations are unspecified
there.

`unspecified` is coarser than the language: it may give each head and
parts' values a value of its own, while the language gives every `match`
where no arm is taken, and every table where no row holds, of one type,
the same value, that of `[][0]` (see [Tables](Expressions.md#tables)), and
an index out of range the value of one unknown function of the sequence
and the position. What holds of every `unspecified` holds of the
language's.

```fren
pub type Env

pub fn lookup(Env, Id): Value
pub fn meaning(Env, Id, Seq<Value>): Value
pub fn unspecified(Env, Head, Seq<Value>): Value

-- The spec being read: its declarations.
pub type Program

pub fn definition_value(Program, Id, Seq<Value>): Value

-- The name of a constant or of a defined function, and `""` for any other layer.
pub fn declared(head: Head): Id := match head {
    Head::Constant(c) => c,
    Head::Defined(f) => f,
    _ => "",
}

pub fn fixed_specified?(Program, Head, Seq<Value>)

pub fn fixed_value(Program, Head, Seq<Value>): Value

-- The value of the variant, record or newtype `c` built from its parts'
-- values: `C(c, l)`, with `l` the list of them.
pub fn construct(Id, Seq<Value>): Value
```

## Guards

A *connective* is a layer that evaluates a part only under a condition, its
first part (see [Sequences](Expressions.md#sequences)): `and`, `or`,
`when`, `unless` and the conditional `if`, as `Op("and", "")` and so on. A
[chained comparison](Expressions.md#chained-comparisons) is the `and` of
its comparisons, and is guarded as those are. `lang::guard` states which
part a condition guards, and whether it is evaluated, from the operand and
the condition's value. For a `match` arm's guard, the condition is that
its pattern matches and no earlier arm is taken, and for its body, that
the arm is the first that is taken; the rows of a
[table](Expressions.md#tables) are guarded as `match` arms are, by the
earlier rows' conditions, which are their guards. An operand is evaluated
exactly when its guard holds, and an operand that is not one of these is
evaluated whenever the expression it is in is.

```fren
-- The operands evaluated only under a condition.
pub enum GuardedOperand { WhenBody, UnlessBody, ThenBranch, ElseBranch, AndRight, OrRight, ArmGuard, ArmBody }

pub proc guard(
    operand: GuardedOperand,
    condition: Value,          -- the condition's value
): (
    det holds?,
    det evaluated?,          -- it is evaluated: its guard holds
) {
    use self::GuardedOperand::{
        AndRight,
        ArmBody,
        ArmGuard,
        ElseBranch,
        OrRight,
        ThenBranch,
        UnlessBody,
        WhenBody,
    }

    out holds? := condition = Value::B(true)

    ensure rule: evaluated? iff match operand {
        WhenBody | ThenBranch | AndRight | ArmGuard | ArmBody => holds?,
        UnlessBody | ElseBranch | OrRight => not holds?,
    }

    -- `a and b` is false without `b` once `a` is, and `a or b` true once `a` is.
    expect and_short_circuits: when operand = AndRight and not holds?, not evaluated?
    expect or_short_circuits: when operand = OrRight and holds?, not evaluated?
    -- The bodies of `when C` and `unless C` are evaluated under opposite conditions.
    expect opposite: when operand is WhenBody | UnlessBody, evaluated? iff (holds? iff operand = WhenBody)
}
```

The branches of a conditional have opposite guards, as do the bodies of
`when C, D` and `unless C, D`: of each pair, exactly one is evaluated,
whatever `C`. A connective's second part is guarded by its condition as
`second_guard` says, and a conditional's third by the condition's
negation, and its value is that of the parts it evaluates:
`a and b` is `false` where `a` is, `when C, D` is `true` where `C` is not,
and so on.

```fren
-- The value of the part at position `k`, and `Nil` where there is none.
pub fn part(values: Seq<Value>, k: Int): Value := if 0 <= k < values.len then values[k] else Value::Nil

-- The operator of a layer, and `""` for a layer that is not an operator.
pub fn operator(head: Head): Id := match head {
    Head::Op(o, _) => o,
    _ => "",
}

pub fn connective?(o: Id) := o in {"and", "or", "when", "unless", "if"}

-- The operators whose value is always specified. The cardinality operators
-- are listed by name; a later slice derives this from their meaning.
pub fn total?(o: Id) := connective?(o) or o in {"at_most_one?", "exactly_one?"}

-- What guards a connective's second part.
pub fn second_guard(o: Id): GuardedOperand := if o = "or" then GuardedOperand::OrRight
    else if o = "when" then GuardedOperand::WhenBody
    else if o = "unless" then GuardedOperand::UnlessBody
    else if o = "if" then GuardedOperand::ThenBranch
    else GuardedOperand::AndRight

-- The value of the connective `o` at its parts' values.
pub fn connective_value(o: Id, values: Seq<Value>): Value := let c? := part(values, 0) = Value::B(true),
    second := part(values, 1)
    in if o = "and" then (if c? then second else Value::B(false))
    else if o = "or" then (if c? then Value::B(true) else second)
    else if o = "when" then (if c? then second else Value::B(true))
    else if o = "unless" then (if c? then Value::B(true) else second)
    else if c? then second
    else part(values, 2)
```

### Arms

A *choice* is a `match` or a [table](Expressions.md#tables), as
`Op("match", s)` and `Op("table", s)`. A `match`'s parts are its
scrutinee and then each arm's guard and body. A table of rows is
`Op("table", s)`: its rows have no patterns, and its parts are, after a
first part that stands for no scrutinee, each row's condition and value. A
[table over a scrutinee](Expressions.md#tables-over-a-scrutinee), whose
arms have patterns, is `Op("match", s)`, as a `match` is. So arm `i`'s guard is at position `guard_at(i)`, and
its body just after it. An arm without a guard has
the literal `true` as its guard, and a row `_` the literal `true` as its
condition. Arm `i` is *open* where its pattern matches the scrutinee's
value, and every row is: `arm_matches?(program, head, i, v)` says that the pattern
of arm `i` of the choice `head` matches the value `v`, which a later slice
ties to the model of [Patterns](Patterns.md). An arm *fires* where it is
open, its guard holds and no earlier arm fires, as
[`lang::guarded_match`](Expressions.md#matches) states with `Taken`. Arm
`i`'s guard is evaluated where it is open and no earlier arm fires, and
its body where it fires, as `guard` states for `ArmGuard` and `ArmBody`.
The choice has the value of the body of the arm that fires, and is
unspecified where none does, with a value that does not depend on its
parts, as the language's is that of `[][0]` of its type. The rows of a table are disjoint where the
[disjointness check](../Check.md#disjointness) passes, so their order
does not matter there.

Fren has no recursion over lists, so the model reads the parts at fixed
positions, and states the first three arms of a choice. A choice with
more is evaluated by the same rule, arm by arm, which the model does not
spell out: where none of the first three fires, its value is the one the
spec fixes, `fixed_value`, where that is specified, and
`later_unevaluated(program, head, values)` are the positions of the later arms'
guards and bodies that it does not evaluate. The laws are stated of
choices of at most three arms.

```fren
pub fn choice?(o: Id) := o in {"match", "table"}

-- The positions of arm `i`'s guard and body, after the scrutinee.
pub fn guard_at(i: Int): Int := 1 + 2 * i

-- Arm `i`'s guard's and body's values, and whether it exists, for the
-- arms that the model states.
pub fn arm_guard(values: Seq<Value>, i: Int): Value := part(values, guard_at(i))

pub fn arm_body(values: Seq<Value>, i: Int): Value := part(values, guard_at(i) + 1)

pub fn arm_present?(values: Seq<Value>, i: Int) := guard_at(i) + 1 < values.len

-- The arms that the model states, and the positions of their parts.
pub type ArmIndex := Int is 0..=2

pub type PartAt := Int is 0..=6

pub fn arm_matches?(Program, Head, Int, Value)

-- Arm `i` exists and is open: its pattern matches the scrutinee's value,
-- as `matched?` says.
pub fn arm_open?(head: Head, values: Seq<Value>, i: Int, matched?) := choice?(operator(head)) and arm_present?(values, i)
    and (operator(head) = "table" or matched?)

-- Arm `i` fires, from whether each of the first three arms is open: it is
-- open, its guard holds, and no earlier arm fires.
pub fn fires_at?(values: Seq<Value>, open0?, open1?, open2?, i: Int) := let holds0? := open0? and arm_guard(values, 0) = Value::B(true),
    holds1? := open1? and arm_guard(values, 1) = Value::B(true),
    holds2? := open2? and arm_guard(values, 2) = Value::B(true)
    in if i = 0 then holds0? else if i = 1 then not holds0? and holds1? else not holds0? and not holds1? and holds2?

-- The choice has an arm after the third, and the positions of the guards
-- and bodies of those arms that it does not evaluate.
pub fn more_arms?(head: Head, values: Seq<Value>) := choice?(operator(head)) and values.len > 7

pub fn later_unevaluated(Program, Head, Seq<Value>): Set<Int>

-- The positions of arm `i`'s guard and body that are not evaluated.
pub fn unevaluated_arm(i: Int, guard?, body?): Set<Int> :=
    (if guard? then {} else {guard_at(i)}) union (if body? then {} else {guard_at(i) + 1})
```

## One layer

The value of a layer is `step` of its head, its environment and its
parts' values: a literal is its value, a variable is read from the
environment, a definition has its one part's value, a construction is its
variant and its parts, an application of an uninterpreted function is
read from the environment at the function and its arguments, a
[connective](#guards) has the value of the parts it evaluates, a
[choice](#arms) the value of the body of the arm that fires, a constant
and an application of a defined function the value of its
[definition](#environments), and every other layer has the value the
spec fixes, each where that is specified, and the unspecified one
elsewhere. A connective, and a [cardinality
operator](Expressions.md#cardinality), is always specified. `step` is a function with a contract, rather
than a defined function, since it applies the functions above, and a
defined function applies no uninterpreted function (see [Defined
functions](Items.md#defined-functions)). Its postcondition determines it:

```fren
pub fn step(program: Program, head: Head, env: Env, values: Seq<Value>): Value
    ensure layer: step(program, head, env, values) = match head {
    Head::Literal(v) => v,
    Head::Bound(v) => v,
    Head::Variable(x) => lookup(env, x),
    Head::Definition(_) => part(values, 0),
    Head::Construction(c, _) => construct(c, values),
    Head::Uninterpreted(f) => meaning(env, f, values),
    Head::Op(o, _) => if connective?(o) then connective_value(o, values)
        else if choice?(o) then (if fires_at?(values, open0?, open1?, open2?, 0) then arm_body(values, 0)
        else if fires_at?(values, open0?, open1?, open2?, 1) then arm_body(values, 1)
        else if fires_at?(values, open0?, open1?, open2?, 2) then arm_body(values, 2)
        else if more_arms?(head, values) and fixed_specified?(program, head, values) then fixed_value(program, head, values)
        else unspecified(env, head, []))
        else if total?(o) or fixed_specified?(program, head, values) then fixed_value(program, head, values)
        else unspecified(env, head, values),
    Head::Constant(_) | Head::Defined(_) => if fixed_specified?(program, head, values)
        then definition_value(program, declared(head), values) else unspecified(env, head, values),
    _ => if fixed_specified?(program, head, values) then fixed_value(program, head, values) else unspecified(env, head, values),
}
    where open0? := arm_open?(head, values, 0, arm_matches?(program, head, 0, part(values, 0))),
    open1? := arm_open?(head, values, 1, arm_matches?(program, head, 1, part(values, 0))),
    open2? := arm_open?(head, values, 2, arm_matches?(program, head, 2, part(values, 0)))
```

What a layer *mentions* is the set of the variables and uninterpreted
functions whose values it may depend on, from what its parts mention
together (see [Mentions](Expressions.md#mentions)): a variable mentions
itself, an application of an uninterpreted function the function and what
its arguments mention, a literal, a bound name of a listed type and a
constant nothing, and every other layer what its parts mention, since its
meaning is fixed:

```fren
pub fn mentioned_by(head: Head, parts_mentioned: Set<Mention>): Set<Mention> := match head {
    Head::Literal(_) | Head::Bound(_) | Head::Constant(_) => {},
    Head::Variable(x) => {Mention::Var(x)},
    Head::Uninterpreted(f) => parts_mentioned union {Mention::Fn(f)},
    _ => parts_mentioned,
}
```

`lang::choice_arms` states which arms of a choice are open, which fires,
and which of their guards and bodies are evaluated, with a call of
`guard` for each:

```fren
pub proc choice_arms(
    program: Program,
    head: Head,
    values: Seq<Value>,        -- the choice's parts' values
): (
    det open0?,
    det open1?,
    det open2?,
    det fired0?,
    det fired1?,
    det fired2?,
    det specified?,
    det stated: Set<Int>,
    det unevaluated: Set<Int>,
) {
    out open0? := arm_open?(head, values, 0, arm_matches?(program, head, 0, part(values, 0)))
    out open1? := arm_open?(head, values, 1, arm_matches?(program, head, 1, part(values, 0)))
    out open2? := arm_open?(head, values, 2, arm_matches?(program, head, 2, part(values, 0)))
    out fired0? := fires_at?(values, open0?, open1?, open2?, 0)
    out fired1? := fires_at?(values, open0?, open1?, open2?, 1)
    out fired2? := fires_at?(values, open0?, open1?, open2?, 2)
    -- Some arm fires, or, of a choice of more arms, the value the spec fixes is specified.
    out specified? := fired0? or fired1? or fired2? or (more_arms?(head, values) and fixed_specified?(program, head, values))
    -- The first three arms' guards and bodies that are not evaluated, and
    -- those of every arm.
    out stated := unevaluated_arm(0, guard0.evaluated?, body0.evaluated?)
        union unevaluated_arm(1, guard1.evaluated?, body1.evaluated?)
        union unevaluated_arm(2, guard2.evaluated?, body2.evaluated?)
    out unevaluated := stated
        union (if more_arms?(head, values) then later_unevaluated(program, head, values) minus {0, 1, 2, 3, 4, 5, 6} else {})

    call guard0 := guard(GuardedOperand::ArmGuard, Value::B(open0?))
    call body0 := guard(GuardedOperand::ArmBody, Value::B(fired0?))
    call guard1 := guard(GuardedOperand::ArmGuard, Value::B(open1? and not fired0?))
    call body1 := guard(GuardedOperand::ArmBody, Value::B(fired1?))
    call guard2 := guard(GuardedOperand::ArmGuard, Value::B(open2? and not fired0? and not fired1?))
    call body2 := guard(GuardedOperand::ArmBody, Value::B(fired2?))

    -- At most one arm fires, and the first three arms are evaluated alike,
    -- whatever arms come after them.
    expect one_fires: at_most_one?(fired0?, fired1?, fired2?)
    expect first_three: forall (k: PartAt), k in unevaluated iff k in stated
    -- An arm without a body is no arm, and every row of a table is open.
    expect absent_arms: forall (i: ArmIndex), when values.len <= guard_at(i) + 1,
        not (if i = 0 then open0? else if i = 1 then open1? else open2?)
    expect table_rows: forall (i: ArmIndex), when operator(head) = "table" and guard_at(i) + 1 < values.len,
        if i = 0 then open0? else if i = 1 then open1? else open2?
}
```

`lang::node` is one layer. Its inputs are the program, its head, its
environment, its parts' values in order, and what its parts mention,
together; a literal,
a bound name, a constant and a variable have no parts, so theirs mention
nothing. Its `value` is its `step`, and `mentioned` what it mentions.
`read` is what it reads of the environment at its own name: a variable's
value, or an uninterpreted function's at the parts' values, and `Nil` for
a layer that has no name of its own to read at. `specified?` says that its
value is not the unspecified one. `undefined_parts` are the positions,
from 0, of its parts that are not [defined](../Check.md#definedness), and
`unevaluated` those that it does not evaluate: a connective's second part
where its guard fails, a conditional's third where the condition holds,
and a choice's arms' guards and bodies where `guard` says they are not. The layer is `defined?` where it is specified and every part it
evaluates is defined. Guards nest by conjunction: a part is evaluated
where its layer is and its own guard holds. A definition of a `let` or
`where` is not a part of the `let`, whose only part is its body, but of
each `Definition` layer that mentions it, so it is guarded where its name
is mentioned, as if written there, and not at all where it is never
mentioned:

```fren
pub proc node(
    program: Program,                -- the spec being read
    head: Head,
    env: Env,
    values: Seq<Value>,                -- its parts' values, in order
    parts_mentioned: Set<Mention>,    -- what its parts mention, together
    undefined_parts: Set<Int>,       -- the positions of its parts that are not defined
): (
    det value: Value,
    det mentioned: Set<Mention>,
    det mentions?,
    det read: Value,
    det specified?,
    det unevaluated: Set<Int>,
    det defined?,
) {
    use self::Head::{Bound, Constant, Construction, Definition, Literal, Op, Uninterpreted, Variable}

    assume leaves: when head is Literal(_) | Bound(_) | Constant(_) | Variable(_), parts_mentioned = {}

    out value := step(program, head, env, values)
    out mentioned := mentioned_by(head, parts_mentioned)
    out mentions? := mentioned != {}
    out read := match head {
        Variable(x) => lookup(env, x),
        Uninterpreted(f) => meaning(env, f, values),
        _ => Value::Nil,
    }
    out specified? := match head {
        Literal(_) | Bound(_) | Variable(_) | Definition(_) | Construction(_, _) | Uninterpreted(_) => true,
        Op(o, _) => if choice?(o) then arms.specified? else total?(o) or fixed_specified?(program, head, values),
        _ => fixed_specified?(program, head, values),
    }
    out unevaluated := (if connective?(operator(head)) and not second.evaluated? then {1} else {})
        union (if operator(head) = "if" and not third.evaluated? then {2} else {})
        union (if choice?(operator(head)) then arms.unevaluated else {})
    out defined? := specified? and undefined_parts subset unevaluated

    call second := guard(second_guard(operator(head)), part(values, 0))
    call third := guard(GuardedOperand::ElseBranch, part(values, 0))
    call arms := choice_arms(program, head, values)

    -- What a part mentions, the whole does, and so does a layer's own name.
    expect parts_kept: parts_mentioned subset mentioned
    expect own_name: match head {
        Variable(x) => Mention::Var(x) in mentioned,
        Uninterpreted(f) => Mention::Fn(f) in mentioned,
        _ => true,
    }
    -- Where a layer is not specified, its value is the unspecified one.
    expect unspecified_value: unless specified?,
        value = unspecified(env, head, if choice?(operator(head)) then [] else values)
    -- Only a layer whose value the spec fixes can be unspecified.
    expect fixed_only: when head is Literal(_) | Bound(_) | Variable(_) | Definition(_) | Construction(_, _)
        | Uninterpreted(_), specified?
    -- Only a connective or a choice leaves a part unevaluated, and never
    -- its first: a connective's condition, or a choice's scrutinee.
    expect evaluates_first: not 0 in unevaluated
    expect all_evaluated: unless connective?(operator(head)) or choice?(operator(head)), unevaluated = {}
    -- Of a conditional, exactly one branch is evaluated.
    expect branches: when operator(head) = "if",
        (1 in unevaluated iff part(values, 0) != Value::B(true)) and (2 in unevaluated iff part(values, 0) = Value::B(true))
    -- Of a choice of at most three arms: the body of the arm that fires is
    -- evaluated, and no other body; an arm whose pattern does not match is not
    -- evaluated; an open arm's guard is evaluated where no earlier arm fires,
    -- and no arm after the one that fires is.
    expect bodies: forall (i: ArmIndex), when choice?(operator(head)) and not more_arms?(head, values),
        guard_at(i) + 1 in unevaluated iff not fires_at?(values, arms.open0?, arms.open1?, arms.open2?, i)
    -- A choice has the value of the body of the arm that fires, as
    -- `lang::guarded_match`'s `valued` states.
    expect fired_value: forall (i: ArmIndex), when choice?(operator(head)) and fires_at?(values, arms.open0?, arms.open1?, arms.open2?, i),
        value = arm_body(values, i)
    expect closed_arms: forall (i: ArmIndex),
        when choice?(operator(head)) and not more_arms?(head, values) and not (if i = 0 then arms.open0? else if i = 1 then arms.open1? else arms.open2?),
        guard_at(i) in unevaluated
    expect open_guards: forall (i: ArmIndex), when choice?(operator(head)) and not more_arms?(head, values)
        and (if i = 0 then arms.open0? else if i = 1 then arms.open1? else arms.open2?) and (forall (j: ArmIndex), when j < i, not fires_at?(values, arms.open0?, arms.open1?, arms.open2?, j)),
        not guard_at(i) in unevaluated
    expect after_firing: forall (i j: ArmIndex),
        when choice?(operator(head)) and not more_arms?(head, values) and i < j and fires_at?(values, arms.open0?, arms.open1?, arms.open2?, i),
        guard_at(j) in unevaluated
    -- A choice where no arm fires is not defined.
    expect none_fires: when choice?(operator(head)) and not specified?, not defined?
    -- A layer whose parts are all defined is defined where it is specified.
    expect parts_defined: when undefined_parts = {}, defined? iff specified?
    -- Its first part is evaluated where it is, so it must be defined.
    expect first_evaluated: when 0 in undefined_parts, not defined?

    cover guarded: defined? and undefined_parts != {}
    cover arm_guarded: choice?(operator(head)) and defined? and undefined_parts != {}
}
```

The laws that relate behaviours of `node` are in [Laws of
meaning](MeaningLaws.md).
