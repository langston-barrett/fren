# Higher-order functions

A [defined function](Items.md#defined-functions)'s parameter may be a
function, whose type is a *function type*, and an application gives it a
*closure* or the name of a function. Such a function is *higher-order*:

```text
pub enum Option<T> { None, Some(T) }

fn map<T, U>(o: Option<T>, f: fn(T) -> U): Option<U> := match o {
    Option::Some(x) => Option::Some(f(x)),
    Option::None => Option::None,
}

fn twice(f: fn(Int) -> Int, x: Int): Int := f(f(x))

proc c(o: Option<Int>, step: Int): (det p: Option<Int>, det q: Int) {
    out p := map(o, |x| x + step)
    out q := twice(|n: Int| 2 * n, step)
}
```

Functions are *second-class*: a function is applied, or given to a
higher-order function, and never held in a variable, a field, a
collection or a constant, nor compared. So an application of a
higher-order function is [unfolded](#meaning), and its closures with it,
and nothing of a function type is left for the solver, which sees the
first-order formulas that it sees without them.

```
type          := base ["is" pattern] | "fn" "(" type ("," type)* ")" "->" type
closure       := "|" closure-param ("," closure-param)* "|" expr
               | "match" "{" match-arm ("," match-arm)* [","] "}"
match-arm     := pattern ("," pattern)* ["if" expr] "=>" expr
closure-param := (DECL | "_") [":" base]
```

## Function types

`fn(T) -> U` is the type of the functions from a `T` to a `U`, and
`fn(T1, T2) -> U` of those of two parameters, and so on: a function type
has at least one parameter, as a function does. A function type is
written only as the whole type of a defined function's parameter: not as
a field's or payload's type (`F0432`), a procedure's parameter's or output's (`F0433`),
nor a constant's, a function's result's, an uninterpreted function's
parameter's, a definition's of a `let` or `where`, a bound name's, a type
alias's or a closure's parameter's (`F0434`), and never within another
type, as an element type, a type argument, or a function type's parameter
or result (`F0435`). `lang::function_type_place` states where it may be
written, from where the type is written and the steps from that type down
to the function type within it, which both front ends read from the type
as written (`Core.fnTypeWithin`):

```fren
pub mod lang

-- Where a type is written.
pub enum TypeSite {
    DefinedParameter,
    UninterpretedParameter,
    Result,
    Constant,
    Variable,
    Field,
    Payload,
    Definition,
    BoundName,
    Alias,
    ClosureParameter,
}

-- A step from a type into one that it is built from: an element type of a
-- set, relation or sequence, a type argument of an instance, or a function
-- type's parameter or result.
pub enum Within { Element, Argument, FnParameter, FnResult }

-- Comparing sequences is outside the decidable core.
set_option fren.lint.undecidable "allow" in
pub proc function_type_place(
    site: TypeSite,
    within: Seq<Within>,     -- the steps from the written type down to the function type, outermost first
): (det accepted?, det code: Id) {
    use self::TypeSite::{DefinedParameter, Field, Payload, Variable}
    -- The error's code, `""` where it is accepted.
    out code := if accepted? then "" else if within != [] then "F0435"
        else if site in {Field, Payload} then "F0432" else if site = Variable then "F0433" else "F0434"

    ensure rule: accepted? iff (site = DefinedParameter and within = [])

    expect parameter: when site = DefinedParameter and within = [], accepted?
    expect nested: when within != [], not accepted?
    expect not_in_data: when site in {Field, Payload} and within = [], code = "F0432"
}
```

A function type's parameters and result are types of values, which may
mention the function's [type parameters](GenericFunctions.md), as
`fn(T) -> U` does above, but are not `Nat`s nor [subset
types](SubsetTypes.md) (`F0435`): those bring a fact or an
obligation of their values, which would be a [contract](Items.md#contracts)
of the function given, and the parameter has none, for now. Nor is one a
function type, as above. `lang::function_type_parts` states this, from
what each of its parameters' types and its result's is:

```fren
-- What a function type's parameter's or result's type is.
pub enum FnPart { Plain, Natural, Patterned, Function }

set_option fren.lint.undecidable "allow" in
pub proc function_type_parts(
    kinds: Seq<FnPart>,      -- what its parameters' types are, then its result's
): (det accepted?) {
    ensure rule: accepted? iff not (FnPart::Natural in kinds or FnPart::Patterned in kinds or FnPart::Function in kinds)

    expect plain: when kinds = [FnPart::Plain, FnPart::Plain], accepted?
    expect no_nat: when FnPart::Natural in kinds, not accepted?
}
```

## Function parameters

Within a higher-order function's body, a parameter `f` of type `fn(T) ->
U` is applied as a function is, `f(e)`, which gives as many arguments as
the function type has parameters (`F0308`), each of its parameter's type,
or a `Nat` where it is an `Int`, and has the function type's result type.
It may also be given, by its name, to another higher-order function's
parameter of its type. Mentioned in any other way it is a function that
is not applied (`F0210`). Its contract's clauses may apply it too, as its
body may: a precondition that applies `f` is one about the function
given.

For the function's own checks (see [Defined
functions](Items.md#defined-functions)), each function parameter is an
[uninterpreted function](Items.md#uninterpreted-functions) of its type, of
which nothing is known: the body's tables, the preconditions of the
functions it applies, its pattern types' obligations and its
postconditions are checked once, for every function that an application
could give, as they are for every value of the other parameters. So a
higher-order function's body is checked once, not at each application.
Since a function type has no `Nat` and no pattern type, an application of
`f` brings no fact. A counterexample of such a check shows the other
parameters' values, never a function's, as a counterexample shows no
uninterpreted function's.

## Arguments

An application of a higher-order function gives each function parameter a
closure or the name of a function of its type: a defined function,
generic or not, or, within another higher-order function, a function
parameter of the enclosing one. Anything else there is an error
(`F0436`), as is a closure anywhere else, and so is the name of an
uninterpreted function there: its applications would be within the
higher-order function's body, where its arguments may mention an output
of the enclosing component (see [Function
applications](Expressions.md#function-applications)). A function's name
anywhere else is a function that is not applied (`F0210`), as before.
`lang::function_argument` states this, from what the parameter takes and
the argument as written:

```fren
-- What a parameter takes: a value, or a function of `n` parameters.
pub enum ParamKind { Value, Function(Nat) }

-- An argument, as written: a closure of `n` parameters, the name of a
-- defined function, of an uninterpreted function or of the enclosing
-- function's function parameter, or any other expression.
pub enum ArgShape { Closure(Nat), DefinedName, UninterpretedName, FnParameterName, Other }

pub proc function_argument(param: ParamKind, arg: ArgShape): (det accepted?, det code: Id) {
    use self::ArgShape::{Closure, DefinedName, FnParameterName, Other, UninterpretedName}
    -- The error's code, `""` where it is accepted.
    out code := if accepted? then ""
        else if param = ParamKind::Value and arg is DefinedName | UninterpretedName | FnParameterName then "F0210"
        else "F0436"

    ensure rule: accepted? iff match param {
        ParamKind::Value => arg = Other,
        ParamKind::Function(n) => arg = Closure(n) or arg = DefinedName or arg = FnParameterName,
    }

    expect values: when param = ParamKind::Value, accepted? iff arg = Other
    expect closures: when param = ParamKind::Function(1), accepted? iff arg in {Closure(1), DefinedName, FnParameterName}
    expect no_uninterpreted: when arg = UninterpretedName, not accepted?
}
```

A closure's parameters are declared as a quantifier's bound names are:
their names are distinct (`F0213`), follow the [Boolean
names](Types.md#boolean-names) rule for their types, and are written with
`!` exactly when they [shadow](Procedures.md#shadowing) a name in scope.
A parameter written `_` declares no name, so the body cannot mention it,
and a closure may have several: `|_, y| y` ignores its first argument, as
a function type may require.
A closure has as many parameters as the function type (`F0436`); a
parameter's type is the function type's, and if it is written, `|x: T|`,
it must be that type (`F0304`), which a [generic
function's](GenericFunctions.md) closure may need. Its body is an
expression of the function type's result type, or a `Nat` where that is an
`Int`. Like a defined function's body, it applies no uninterpreted
function (`F0331`).

The name of a function `g` given to a parameter of type `fn(T1, ..., Tn)
-> U` means the closure `|x1, ..., xn| g(x1, ..., xn)`, so it is checked
as that application is: `g` takes `n` arguments, of the types `T1` to
`Tn`, and its result is a `U`.

A closure's body may mention anything in scope where it is written, not
only its parameters: the procedure's parameters and outputs, the enclosing function's
parameters, the binders of `match` arms and quantifiers, and the names of
`let`s and `where`s. It *captures* them, and they keep their meaning
where its body is unfolded (see [Meaning](#meaning)). Mentioning a
closure's parameter counts as mentioning a value that varies, as an
unbounded quantifier's bound name does, for the rules of [linear
arithmetic](Expressions.md#linear-arithmetic) and of constant divisors:
`|x| x * 2` is linear, and `|x| x * y` is not where `y` is a variable.

A closure's body's *obligations*, its tables' questions, the
preconditions of the functions it applies, its indexes and its pattern
types' obligations, are checked where it is unfolded: at each application
`f(e1, ..., en)` of its function parameter within the higher-order
function's body, unfolded as at the application, under the guards around
it there (`lang::guard`), and with the closure's parameters standing for
`e1` to `en`; under the conditions where the closure is written too. Since
closures are always unfolded and nothing is recursive, this is exact: a
closure applied only where its argument is in range, as in `if q.len > 0
then f(0) else 0` with `|i| q[i]`, has no index out of range, and one that
is never applied has nothing to check. An obligation is reported at the
closure, and its counterexample shows the values that reach it. The
higher-order function's own checks still treat its function parameters as
uninterpreted functions.

`lang::closure_obligation` states this of one application, from the
guarded operands around it, outermost first, with their conditions'
values, and whether the obligation holds at its arguments: it is checked
there exactly where the application is evaluated, which is where each
guard holds, as `lang::guard` states for each. The obligation of the
closure is the conjunction of this over the applications. Here an
application has three guards around it at most, and the rule is the same
for more:

```fren
-- Whether the operand `o`, whose condition has the value `c?`, is evaluated
-- (`lang::guard`).
pub fn guard_holds?(o: GuardedOperand, c?) := match o {
    GuardedOperand::WhenBody | GuardedOperand::ThenBranch | GuardedOperand::AndRight
    | GuardedOperand::ArmGuard | GuardedOperand::ArmBody => c?,
    _ => not c?,
}

set_option fren.lint.length_zero "allow" in
pub proc closure_obligation(
    frames: Seq<GuardedOperand>,     -- the guarded operands around the application, outermost first
    conditions: Seq<Bool>,           -- their conditions' values, in the same order
    at_args?,                        -- the obligation holds at the application's arguments
): (
    det evaluated?,
    det holds?,                      -- the obligation, as it is checked there
) {
    assume same: frames.len = conditions.len and frames.len <= 3
    out evaluated? := (frames.len <= 0 or guard_holds?(frames[0], conditions[0]))
        and (frames.len <= 1 or guard_holds?(frames[1], conditions[1]))
        and (frames.len <= 2 or guard_holds?(frames[2], conditions[2]))

    ensure rule: holds? iff (not evaluated? or at_args?)

    expect unguarded: when frames.len = 0, holds? iff at_args?
    expect unevaluated: when frames = [GuardedOperand::ThenBranch] and conditions = [false], holds?
}
```

Function parameters and closures are not values, so neither is compared:
`=` and `!=` with an operand that is a closure, a function's name or a
function parameter is an error (`F0437`), whatever the other operand.
Two functions would be compared by their values at every argument, which
the solver cannot decide; written as closures they would be compared by
how they are written, which is not what `=` means. `lang::function_comparison`
states this, over the operands of a comparison, or of a chain of them:

```fren
-- An operand of `=` or `!=`, as written: a closure, the name of a
-- function or of a function parameter, or any other expression.
pub enum Comparand { Value, Closure, FunctionName }

set_option fren.lint.undecidable "allow" in
pub proc function_comparison(operands: Seq<Comparand>): (det accepted?) {
    ensure rule: accepted? iff not (Comparand::Closure in operands or Comparand::FunctionName in operands)

    expect values: when operands = [Comparand::Value, Comparand::Value], accepted?
    expect functions: when operands = [Comparand::FunctionName, Comparand::FunctionName], not accepted?
}
```

## Applications

An application of a higher-order function is typed as any other is (see
[Function applications](Expressions.md#function-applications)), and those
of a generic one have their type arguments inferred as in [Generic
functions](GenericFunctions.md#applications), where a function parameter's
type mentions the type parameters as any parameter's does, and its
argument is elaborated between the others: first the arguments that do
not wait, in order, then the functions, in order, each once the types of
its parameters are known, and last those that wait. A closure gives a
type parameter the argument that its body's type gives, if the result
type of the function type mentions it, or that its parameter's written
type gives; a function's name, those that its parameters' and its
result's types give. So in `map(o, |x| x + 1)` with `o: Option<Int>`,
`o` gives `T` the argument `Int`, which is the type of `x`, and the body,
an `Int`, gives `U` the argument `Int`. A closure whose parameter's type
mentions a type parameter that has no argument yet, and is not written,
cannot be elaborated (`F0400`).

## Meaning

An application of a higher-order function has the value of its body, as
any defined function's does, with each parameter standing for its
argument: a function parameter stands for its closure, so that each
application `f(e1, ..., en)` within the body has the value of the
closure's body, with each of its parameters standing for the value of
`ei`. The body is *unfolded* at the application, with each closure
unfolded within it. Fren has no recursion, so unfolding ends, and nothing
of a function type is left: the solver's queries are first-order, a
closure's body is in the [decidable core](Decidability.md) exactly when
its expression would be, and neither front end gives the solver a
function value.

The names that a closure captures keep the meaning that they have where
the closure is written, wherever its body is unfolded: a name that the
higher-order function's body binds around the application of `f`, such as
a `let` of the same name, or one of its own parameters, never captures a
name of the closure's body. Unfolding is *capture-avoiding*:

- The Lean-hosted front end gives a function type as a Lean arrow, `T → U`
  and `T1 → T2 → U`, and a closure as a Lean `fun`; it unfolds defined
  functions and reduces their applications to closures, as it gives any
  query to the solver, and Lean's bound variables cannot be captured.
- The `fren` command gives the higher-order function's body to the solver
  as a `let` of its other parameters, at their arguments, around its body,
  in which each application of a function parameter is a `let` of the
  closure's parameters, at the application's arguments, around the
  closure's body. First the names that the closure's body mentions free,
  other than its parameters, are renamed to *capture symbols*, `|#0|`,
  `|#1|` and so on, which no other symbol of the query is, and bound to
  those names by the outer `let`, beside the parameters. A closure's
  parameters' symbols are their names with a number of their own, so that
  neither is ever a symbol of another binder.

The names that the `fren` command gives the solver are of two kinds:
quoted symbols, `|x|`, and the symbols `let@N` of the definitions of `let`s
and `where`s. Each `let@N` is numbered as its definition is elaborated, by
one count that only grows, so each is bound by exactly one definition of the
spec, which a body's text binds wherever it is copied. A higher-order
function's body is elaborated before any application of it, since a
function is declared before it is used and is never recursive, so its text
binds no `let@N` that a closure at an application mentions. The `fren`
command does not rely on this: a closure's free `let@N`s are captured as
its quoted local symbols are. Each free symbol of the renamed closure's body
is then one of its parameters, one of its capture symbols, or a symbol of
the prelude, which nothing binds (`Core.captureFree`, proved in Lean of the
functions that run).

`lang::closure_capture` states this of a mention of a name `x` in the
closure's body, from the binders around it once the body is unfolded,
outermost first: the outer `let`'s capture symbols, `symbols`, and the
other parameters, `values`; the higher-order body's binders around the
application, `around`; the inner `let`'s closure parameters, `params`; and
the closure body's own binders around the mention, `inner`. A mention
means the innermost binder of its name. Where `x` is captured, the mention
is the capture symbol bound to `x`, and no later binder has that symbol,
so it means that binding, and so the value that `x` has where the closure
is written; where it is a parameter of the closure, it means the
closure's parameter; and where the closure's body binds it, that binder.
The capture symbols are `Core.captureNames`'s, one for each name captured,
told apart by their numbers (proved in Lean), and new: numbered from where
the query's count of them is, which no binder of the query has yet:

```fren
set_option fren.lint.undecidable "allow" in
pub proc closure_capture(
    captured: Seq<Id>,       -- the names that the closure's body mentions free, other than its parameters
    symbols: Seq<Id>,        -- their capture symbols, in order
    params: Seq<Id>,         -- the closure's parameters' symbols
    values: Seq<Id>,         -- the higher-order function's other parameters
    around: Seq<Id>,         -- the higher-order body's binders around the application, outermost first
    inner: Seq<Id>,          -- the closure body's binders around the mention, outermost first
    x: Id,                   -- the name mentioned
    k: Int,                  -- where `x` is first among `captured`, if it is captured
    j: Int,                  -- where `x` is last among `params`, if it is a parameter
): (det mention: Id) {
    -- One capture symbol for each name captured, each its own.
    assume named: symbols.len = captured.len
        and (forall (a b: Int), when 0 <= a < symbols.len and 0 <= b < symbols.len and a != b, symbols[a] != symbols[b])
    -- The capture symbols are new: no other binder has one.
    assume fresh: forall (s: Id), when s in symbols,
        not s in values and not s in around and not s in params and not s in inner
    -- A free name is captured, a parameter or bound within the body.
    assume free: x in captured or x in params or x in inner
    assume first: when x in captured, 0 <= k < captured.len and captured[k] = x
        and (forall (a: Int), when 0 <= a < k, captured[a] != x)
    assume last: when x in params, 0 <= j < params.len and params[j] = x
        and (forall (a: Int), when j < a < params.len, params[a] != x)
    -- The parameters and the names captured are told apart.
    assume apart: not (x in captured and x in params)

    -- What the mention is renamed to (`Core.captureRename`).
    out mention := if x in inner or x in params then x else symbols[k]

    expect own_binders: when x in inner, mention = x
    -- Captured: the capture symbol, which no later binder has.
    expect captures: when not x in inner and x in captured, 0 <= k < symbols.len and mention = symbols[k]
        and (forall (a: Int), when k < a < symbols.len, symbols[a] != mention)
        and not mention in values and not mention in around and not mention in params and not mention in inner
    -- A parameter: the inner `let`'s, which no later binder has.
    expect parameters: when not x in inner and x in params, 0 <= j < params.len and mention = params[j]
        and (forall (a: Int), when j < a < params.len, params[a] != mention) and not mention in inner
}
```

The front ends unfold alike, so they ask the same queries of the same
formulas, and report the same counterexamples, which never show a
function: a closure's parameters are bound within the queries, and a
function parameter is never a variable of a component.

## Lambda matches and multiple scrutinees

`match { P => e, ... }` is a closure whose parameters are implicit. It is
accepted wherever a closure is accepted, with its parameter types and
arity supplied by the expected function type. For example,
`match { Option::Some(x) => x, Option::None => 0 }` does not
introduce a name merely to match it. It captures surrounding values as an
ordinary closure does. It is second-class, has no zero-argument form,
and cannot stand where a value expression is required (`F0436`). A generic
function supplies concrete types in exactly the same way as for `|x| e`;
when they cannot be inferred, the existing unknown-parameter diagnostic
applies rather than inventing a type.

A defined function may instead leave all its parameters unnamed and give
this body: `fn area(Shape): Int := match { ... }`. Their declared types
supply the implicit parameters. Mixed named and unnamed parameters remain
invalid. An unnamed parameter is never a source-visible binder, and a
nested explicit match cannot accidentally refer to its generated name.
The shorthand expands before normal function checking, including generic
instantiation, contracts, recursive descent and generated Lean definitions.

An ordinary match may inspect multiple expressions:
`match left, right { P, Q => e, ... }`. Each row has exactly one pattern
per scrutinee, with constructor payload commas remaining inside their
parentheses. The implicit closure form uses the same rows, with one
implicit argument per column. A row matches iff all its patterns match,
and binds each name to the value or payload of its own column. Binders
must be distinct across the whole row, are in scope only in that row's
guard and body, and retain the mentions and recursive origin of their own
scrutinee. Later columns do not bring earlier columns' binders into scope.
An arity mismatch is rejected before resolving patterns (`F0308`).

Rows are ordered. Their guards run only after every pattern in that row
matches; their bodies run only when that guard holds and no earlier row
was taken. Coverage and reachability concern vectors of values, not
independent coverage of each column. As with a single scrutinee, ignoring
guards must give exhaustive patterns; guards then generate the ordinary
completeness obligations. The same rules apply to `table left, right`,
with existing table disjointness and otherwise semantics; the otherwise
is a row of wildcards, one per column. `table { C => e }` remains a table
of conditions and does not denote an implicit-argument closure.

The following model uses the actual four worlds of two Boolean arguments.
Each row denotes a Cartesian rectangle and its own guard. It records the
first matching row, preserving correlated coverage holes and guard
fallthrough, and returns the actual arguments rather than fresh values.

```fren
pub enum VectorChoice { First, Second, Missing }

pub proc match_vector(
    left?, right?,
    first_left: Set<Bool>, first_right: Set<Bool>, first_guard?,
    second_left: Set<Bool>, second_right: Set<Bool>, second_guard?,
): (det choice: VectorChoice, det bound_left?, det bound_right?) {
    out choice := if left? in first_left and right? in first_right and first_guard? then VectorChoice::First
        else if left? in second_left and right? in second_right and second_guard? then VectorChoice::Second
        else VectorChoice::Missing
    out bound_left? := left?
    out bound_right? := right?

    expect first_wins: when left? in first_left and right? in first_right and first_guard?, choice = VectorChoice::First
    expect fallthrough: when not first_guard? and left? in second_left and right? in second_right and second_guard?, choice = VectorChoice::Second
    expect both_columns: when first_right = {} and second_right = {}, choice = VectorChoice::Missing
    expect exact_binders: bound_left? = left? and bound_right? = right?
    cover correlated_hole: first_left = {true} and first_right = {true}
        and second_left = {false} and second_right = {false}
        and first_guard? and second_guard? and choice = VectorChoice::Missing
}

pub proc match_vector_coverage(first: Rel<Bool, Bool>, second: Rel<Bool, Bool>): (det complete?) {
    out complete? := forall (left? right?: Bool), (left?, right?) in first or (left?, right?) in second
    expect all_worlds: complete? iff (true, true) in first union second and (true, false) in first union second
        and (false, true) in first union second and (false, false) in first union second
    expect diagonal_is_incomplete: when first = {(true, true)} and second = {(false, false)}, not complete?
    expect complementary_rows: when first = {(true, true), (true, false)} and second = {(false, true), (false, false)}, complete?
}
```

The internal matrix carrier has a name outside the source identifier
grammar. A legal user type, module or constructor name must never capture
that carrier or change coverage, including names that resemble generated
implementation names. The following model quantifies over actual source
identifier strings, including `_fren_match_arguments`, which is a legal
user declaration rather than a reserved implementation namespace.

```fren
pub proc match_namespace(user_type: Id): (det distinct?) {
    assume source_identifier: user_type.matches?("[A-Za-z_][A-Za-z0-9_']*")
    out distinct? := user_type != "#match_arguments"

    expect no_capture: distinct?
    cover implementation_like_name: user_type = "_fren_match_arguments"
}
```

Rewriting lints must preserve the closure role and the implicit function
parameters. A rewrite that only replaces a match by a value expression
cannot be applied to an implicit-argument match: without a valid closure
rewrite, omit that lint and fix. This applies equally to the standalone
formatter/fixer and the hosted diagnostics.

Both frontends must accept and reject the same source, preserve ordinary
single-scrutinee matches, and format lists of scrutinees and patterns
without changing their grouping. Tests compare shorthand to explicit
closures and explicit matches, including heterogeneous columns, nested
constructors, or-patterns, captures, generic functions, guards, type and
arity errors, cross-column duplicate binders, correlated coverage holes,
and recursive calls through payloads from each column. Generated Lean
matches must bind the same values and retain structural recursive descent.

This chapter comes after the last `#fren_check` of the chapters that share
its Lean file, so it names its own procedures, which the Lean-hosted front
end then checks, as the `fren` command checks every procedure:

```fren
#fren_check function_type_place
#fren_check function_type_parts
#fren_check function_argument
#fren_check closure_obligation
#fren_check function_comparison
#fren_check closure_capture
#fren_check match_vector
#fren_check match_vector_coverage
#fren_check match_namespace
```
