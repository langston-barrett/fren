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
| `IDENT`, `INT`, `STRING` | an identifier, an integer literal, a string literal, raw or not (see [Lexical structure](Lang/Lexical.md)) |
| `TERM`, `TACTICS` | a Lean term, a Lean tactic sequence |

## Items

```
spec           := item*
item           := module | use | enumeration | record | abstract-type | function | constant
                | component | expectation | refinement | check | claim | lint-setting | evidence-setting ["in" item] | lean-item

module         := ["pub"] "mod" path
use            := "use" path ["::*" | "::{" path ("," path)* [","] "}"]
enumeration    := ["pub"] "enum" IDENT "{" variant ("," variant)* [","] "}"
variant        := IDENT ["(" type ("," type)* ")"]
record         := ["pub"] "struct" IDENT "{" field ("," field)* [","] "}"
field          := IDENT [":" type]
abstract-type  := ["pub"] "type" IDENT
function       := ["pub"] "fn" IDENT "(" type ("," type)* ")" [":" type]
                | ["pub"] "fn" IDENT "(" variable ("," variable)* ")" [":" type] ":=" expr
constant       := ["pub"] "const" IDENT ":" type ":=" expr
component      := ["pub"] "comp" IDENT "{" member* "}"
expectation    := "expect" IDENT ":" ["forall" forall-binder+ ","] expr
forall-binder  := "(" IDENT+ ":" path ")"
refinement     := "refine" IDENT ":" path "refines" path ["by" TACTICS]
check          := "#fren_check" [path] | "#fren_trace"
claim          := "tested" path ":" STRING ("," STRING)* [","]
                | "trusted" path ":" STRING
lint-setting   := "set_option" lint-option STRING ["in" item]
evidence-setting := "set_option" "fren.evidence" STRING
lint-option    := "fren.lint." IDENT

lean-item      := implementation
                | interpretation
                | "#fren_md" STRING
implementation := "impl" IDENT ":" path ["for" binder+]
                  "{" [map ("," map)* [","]] "}" ["by" TACTICS]
binder         := "(" IDENT+ ":" TERM ")"
map            := IDENT ":=" TERM
interpretation := "interp" path ":=" TERM
```

## Components

```
member         := "in" variable
                | ["pub"] ["det"] "out" variable [":=" expr]
                | "assume" IDENT ":" expr
                | "req" IDENT ":" expr
                | "expect" IDENT ":" expr
                | instance
                | use
                | evidence-setting "in" member
variable       := IDENT [":" type]
instance       := "inst" IDENT ":" path "{" [binding ("," binding)* [","]] "}"
binding        := IDENT [":=" expr]
type           := "Bool" | "Int" | "String" | "Set" "(" type ")" | "Seq" "(" type ")" | "Rel" "(" type "," type ")"
                | path
path           := IDENT ("::" IDENT)*
```

## Expressions

```
expr           := ("when" | "unless") iff "," expr
                | iff
iff            := or ["iff" or]
or             := or "or" and | and
and            := and "and" not | not
not            := "not" not | cmp
cmp            := sum [("=" | "!=" | "<" | "<=" | ">" | ">=" | "in" | "subset") sum]
                | pair "in" sum
sum            := sum ("+" | "-" | "++" | "union" | "minus") prod | prod
prod           := prod ("*" | "inter" | "join") neg | neg
neg            := "-" neg | atom
atom           := INT | STRING | "true" | "false" | path | IDENT ("." IDENT)+ | "(" expr ")"
                | "if" expr "then" expr "else" expr
                | path "(" expr ("," expr)* ")"
                | path "{" field-init ("," field-init)* [","] "}"
                | atom "." IDENT ["(" expr ("," expr)* ")"]
                | IDENT ("." IDENT)+ "(" expr ("," expr)* ")"
                | "match" expr "{" arm ("," arm)* [","] "}"
                | "{" [element ("," element)* [","]] "}"
                | "[" [expr ("," expr)* [","]] "]"
                | atom "[" expr "]"
element        := expr | pair
pair           := "(" expr "," expr ")"
field-init     := IDENT [":=" expr]
arm            := pattern "=>" expr
pattern        := "_" | ["|"] alternative ("|" alternative)*
alternative    := path ["(" pattern-binder ("," pattern-binder)* ")"]
pattern-binder := IDENT | "_"
```

Where a rule is written with left recursion, the operator is
left-associative. For precedence and typing, see
[Expressions](Lang/Expressions.md).
