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
| `DECL` | an identifier that declares a name, which ends in `!` if it shadows another (see [Shadowing](Lang/Components.md#shadowing)); no other `IDENT` ends in `!` |
| `TERM`, `TACTICS` | a Lean term, a Lean tactic sequence |

## Items

```
spec           := item*
item           := module | use | enumeration | record | abstract-type | type-alias | function | constant
                | component | expectation | refinement | check | claim | lint-setting | evidence-setting ["in" item] | lean-item

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
component      := ["pub"] "comp" IDENT "{" member* "}"
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

## Components

```
member         := "in" variable
                | ["pub"] ["det"] "out" variable [":=" top]
                | "assume" IDENT ":" top
                | "ensure" IDENT ":" top
                | "expect" IDENT ":" top
                | "cover" IDENT ":" top
                | instance
                | use
                | evidence-setting "in" member
variable       := DECL [":" type]
instance       := "inst" DECL ":" path "{" [binding ("," binding)* [","]] "}"
binding        := IDENT [":=" expr]
type           := base ["is" pattern]
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
[Patterns](Lang/Patterns.md)).

Where a rule is written with left recursion, the operator is
left-associative. A `cmp` with more than one operator is a [chained
comparison](Lang/Expressions.md#chained-comparisons). For precedence and typing, see
[Expressions](Lang/Expressions.md). In the definitions of a `let`, an
`in` outside brackets, the condition and `then` branch of an `if` and a
`match`'s or a table's scrutinee ends the last definition rather than starting a
membership (an `else` branch keeps that restriction), and a nested `let` ends its own definitions with its own `in`
(see [Local definitions](Lang/Let.md#parentheses)). A `binder` of a
quantifier names a type, and one of a global expectation's leading
`forall` a type or a component (see [Quantifiers](Lang/Quantifiers.md)).
A `type` is written only where the rules above say, never within an
expression, so a `<` in an expression is a comparison, and the `<` of a
`base` or a `declared-type` opens type arguments or type parameters; the
`>` that closes them is one character, even where Lean lexes `>>` (see
[Angle brackets](Lang/Generics.md#angle-brackets)).
