# Grammar

## Notation

| Notation | Meaning |
|---|---|
| `"mod"` | the literal token `mod` |
| `x := ...` | defines the nonterminal `x` |
| `a \| b` | `a` or `b` |
| `[a]` | `a`, optionally |
| `a*`, `a+` | zero or more, one or more `a` |
| `( ... )` | grouping |
| `a"("` | `a` and then `(`, with nothing between them, not even a space (see [Punctuators](Lang/Lexical.md#punctuators)); the same for `[` and `<` |
| `IDENT`, `INT`, `STRING` | an identifier, an integer literal, a string literal, raw or not (see [Lexical structure](Lang/Lexical.md)) |
| `DIGITS` | decimal digits, which name a field after `.`, as in `x.0` (see [Newtypes](Lang/Expressions.md#newtypes)) |
| `DECL` | an identifier that declares a name, which ends in `!` if it shadows another (see [Shadowing](Lang/Procedures.md#shadowing)); no other `IDENT` ends in `!` |
| `TERM`, `TACTICS` | a Lean term, a Lean tactic sequence |

## Items

```
spec           := item*
item           := module | use | enumeration | record | abstract-type | type-alias | function | constant
                | procedure | expectation | refinement | check | claim | lint-setting | evidence-setting ["in" item] | lean-item

module         := ["pub"] "mod" path
use            := "use" path ["::*" | "::{" path ("," path)* [","] "}"]
enumeration    := ["pub"] ["ordered"] "enum" declared-type "{" variant ("," variant)* [","] "}"
variant        := IDENT | IDENT"(" type ("," type)* ")"
declared-type  := IDENT | IDENT"<" IDENT ("," IDENT)* ">"
record         := ["pub"] ["ordered"] "struct" declared-type "{" field ("," field)* [","] "}"
                | ["pub"] ["ordered"] "struct" IDENT"(" [type ("," type)*] ")"
field          := IDENT [":" type]
abstract-type  := ["pub"] "type" IDENT
type-alias     := ["pub"] "type" IDENT ":=" type
function       := ["pub"] "fn" declared-type"(" type ("," type)* ")" [":" type]
                | ["pub"] "fn" declared-type"(" variable ("," variable)* ")" [":" type] [":=" top] clause+
                | ["pub"] "fn" declared-type"(" variable ("," variable)* ")" [":" type] ":=" top
clause         := ("assume" | "ensure") IDENT ":" top
constant       := ["pub"] "const" IDENT ":" type ":=" top
procedure      := ["pub"] "proc" IDENT"(" [variable ("," variable)* [","]] ")"
                  [":" "(" result ("," result)* [","] ")"] "{" member* "}"
expectation    := "expect" IDENT ":" ["forall" binder+ ","] top
refinement     := "refine" IDENT ":" path "refines" path ["{" [binding ("," binding)* [","]] "}"] ["by" TACTICS]
check          := "#fren_check" [path] | "#fren_trace"
claim          := "tested" path ":" STRING ("," STRING)* [","]
                | "trusted" path ":" STRING
lint-setting   := "set_option" lint-option STRING ["in" item]
evidence-setting := "set_option" "fren.evidence" STRING
lint-option    := "fren.lint." IDENT

lean-item      := implementation
                | interpretation
                | "#fren_md" STRING
implementation := "impl" IDENT ":" path ["for" lean-binder+]
                  "{" [map ("," map)* [","]] "}" ["by" TACTICS]
lean-binder    := "(" IDENT+ ":" TERM ")"
map            := IDENT ":=" TERM
interpretation := "interp" path ":=" TERM ["by" TACTICS]
```

## Procedures

```
result         := [evidence-setting "in"] ["det"] variable
member         := ["det"] "exists" variable
                | ["det"] "let" variable ":=" top
                | "out" IDENT ":=" top
                | "assume" IDENT ":" top
                | "ensure" IDENT ":" top
                | "expect" IDENT ":" top
                | "cover" IDENT ":" top
                | call
                | use
                | evidence-setting "in" member
variable       := DECL [":" type]
call           := "call" DECL ":=" path"(" [expr ("," expr)* [","]] ")"
binding        := IDENT [":=" expr]
type           := base ["is" pattern] | "fn" "(" type ("," type)* ")" "->" type
base           := "Bool" | "Int" | "Nat" | "String" | "Set""<" type ">" | "Seq""<" type ">" | "Rel""<" type "," type ">"
                | path | path"<" type ("," type)* ">"
path           := IDENT ("::" IDENT)*
```

## Expressions

```
top            := expr ["where" definition ("," definition)*]
expr           := ("when" | "unless") iff "," expr
                | "let" definition ("," definition)* "in" expr
                | ("forall" | "exists") binder+ "," expr
                | iff
definition     := DECL [":" type] ":=" iff
binder         := "(" DECL+ ":" type ")"
iff            := or ["iff" or]
or             := or "or" and | and
and            := and "and" not | not
not            := "not" not | cmp
cmp            := sum [("=" | "!=" | "in" | "subset") sum]
                | sum (("<" | "<=") sum)+
                | sum ((">" | ">=") sum)+
                | pair "in" sum
                | sum "is" pattern
sum            := sum ("+" | "-" | "++" | "union" | "minus") prod | prod
prod           := prod ("*" | "div" | "mod" | "inter" | "join") neg | neg
neg            := "-" neg | atom
atom           := INT | STRING | "true" | "false" | path | IDENT ("." IDENT)+ | "(" expr ")"
                | "if" expr "then" expr "else" expr
                | path"(" expr ("," expr)* ")"
                | path "{" field-init ("," field-init)* [","] "}"
                | atom "." IDENT | atom "." IDENT"(" expr ("," expr)* ")"
                | atom "." DIGITS
                | IDENT ("." IDENT)+"(" expr ("," expr)* ")"
                | "match" atom "{" arm ("," arm)* [","] "}"
                | "table" "{" row ("," row)* [","] "}"
                | "table" atom "{" arm ("," arm)* [","] "}"
                | "{" [element ("," element)* [","]] "}"
                | "{" expr "with" field-init ("," field-init)* [","] "}"
                | "[" [expr ("," expr)* [","]] "]"
                | atom"[" expr "]"
                | "|" closure-param ("," closure-param)* "|" expr
closure-param  := DECL [":" base]
element        := expr | pair
pair           := "(" expr "," expr ")"
field-init     := IDENT [":=" expr]
arm            := pattern ["if" iff] "=>" expr
row            := ["|"] (iff | "_") "=>" iff
pattern        := ["|"] or-pattern
or-pattern     := primary ("|" primary)*
primary        := "_" | DECL | literal | range
                | path | path"(" or-pattern ("," or-pattern)* ")"
literal        := ["-"] INT | STRING | "true" | "false"
range          := bound "..=" bound | bound ".." [bound] | "..=" bound
bound          := ["-"] INT | path
```

In a range, there are no spaces around `..=` and `..` (see
[Patterns](Lang/Patterns.md)). A function type is written only as a
defined function's parameter's type, and a closure only as an argument for
such a parameter (see [Higher-order functions](Lang/HigherOrder.md)); a
`|` where an operand is expected opens a closure's parameters.

Where a rule is written with left recursion, the operator is
left-associative. A `cmp` with more than one operator is a [chained
comparison](Lang/Expressions.md#chained-comparisons). For precedence and typing, see
[Expressions](Lang/Expressions.md). In the definitions of a `let`, an
`in` outside brackets, the condition and `then` branch of an `if` and a
`match`'s or a table's scrutinee ends the last definition rather than starting a
membership (an `else` branch keeps that restriction), and a nested `let` ends its own definitions with its own `in`
(see [Local definitions](Lang/Let.md#parentheses)). A `binder` of a
quantifier names a type, and one of a global expectation's leading
`forall` a type or a procedure (see [Quantifiers](Lang/Quantifiers.md)).
`exists` and `let` start a member where a `member` starts, and an `expr`
within one: a member starts after the `{` of a procedure's block, and
after the end of the member before it, so an `exists` or a `let` there is
a member, and one within an expression is a quantifier or a local
definition. A `top` ends at the first token that cannot continue it,
where the next member, or the `}` of the block, starts. `call`, `out` and
`det` are not reserved: where a member starts, they are its keyword, and
anywhere else, names.
Components, `in` and `out x: T` members and instances, as components were
written before procedures, are errors whose fixes write them as procedures
(see [Migration](Lang/Procedures.md#migration)).
A `type` is written only where the rules above say, never within an
expression, so a `<` in an expression is a comparison, and the `<` of a
`base` or a `declared-type` opens type arguments or type parameters; the
`>` that closes them is one character, even where Lean lexes `>>` (see
[Angle brackets](Lang/Generics.md#angle-brackets)).
