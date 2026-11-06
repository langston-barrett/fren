-- keep-sorted start
import FrenCli.Parse.ItemSyntax
import FrenCore.Procedures
-- keep-sorted end

/-! Parser errors, formatter layout and parser state. -/

namespace FrenCli

structure ParseError where
  span : Span
  msg : Fren.Core.Msg

/-- Lean commands that may not appear in a `.fren` file. -/
def leanCommands : List String :=
  ["impl", "interp", "def", "theorem", "lemma", "example", "abbrev", "instance", "structure", "inductive", "class",
   "namespace", "section", "end", "variable", "set_option", "attribute", "macro", "syntax",
   "notation", "#check", "#eval", "#print", "#guard_msgs"]

/-- The form of the right side of a `:=` or `=>`, its outermost expression
(`fmt::Form`). -/
inductive RightForm where
  /-- A `match` or a table, with arms. -/
  | arms
  /-- An `if`. -/
  | conditional
  /-- A call, a parenthesized expression, a literal, a record update or a
  Boolean block. -/
  | bracketed
  | other
  deriving BEq, DecidableEq, Repr, Inhabited

/-- A list or block whose line breaks the formatter decides
(`fmt::list_layout`), by how its elements may be laid out. -/
inductive ListKind where
  /-- The arms of a `match` or the rows of a table, always one to a line. -/
  | arms
  /-- The arguments of a `call` member or of a refinement. -/
  | arguments
  /-- The arguments of an application or a method call, which may not end
  with a comma. -/
  | applicationArguments
  /-- The parameters or results of a procedure, or a function's results. -/
  | parameters
  /-- A function's parameters, which may not end with a comma. -/
  | functionParameters
  /-- The elements of a sequence or set literal, or the members of a
  Boolean block. -/
  | elements
  /-- The fields of a record literal or of a record update. -/
  | fields
  /-- The members of a procedure's, a function's or a global expectation's
  block, one to a line but for a single member that fits, with no
  commas. -/
  | members
  deriving BEq, DecidableEq, Repr, Inhabited

/-- A list or block: its kind, its opening and closing brackets, the token
after which its first element starts, and the commas after its elements,
as indices of tokens. The first element starts after the opening bracket,
but for a record update's, which start after its `with`. A block of members
has no commas: in their place are the last tokens of the members that
another follows, but for an evidence setting, which stays with the member
after it. `items` are the first tokens of the items that it is in. -/
structure Bracketed where
  kind : ListKind
  opening : Nat
  lead : Nat
  closing : Nat := 0
  commas : Array Nat := #[]
  items : Array Nat := #[]
  deriving Inhabited, Repr

/-- What the formatter needs to know of a file's structure, as indices of
tokens. -/
structure Layout where
  /-- Tokens that start an item, a member or an element of a list. -/
  starts : Array Nat := #[]
  /-- `-` as a unary operator. -/
  unary : Array Nat := #[]
  /-- `{` and `::{` that open a list, whose elements are separated by commas. -/
  lists : Array Nat := #[]
  /-- `tested` claims: the `tested` and the last string. -/
  claims : Array (Nat × Nat) := #[]
  /-- `use` items: their first and last tokens. -/
  uses : Array (Nat × Nat) := #[]
  /-- The `(` after a function's name, opening its parameters or arguments,
  and the `<` and `>` of type arguments and type parameters. -/
  calls : Array Nat := #[]
  /-- The `{` of a set literal, spaced like `(`. -/
  sets : Array Nat := #[]
  /-- The `..=` and `..` of ranges with a lower bound. -/
  rangeLower : Array Nat := #[]
  /-- The `..=` and `..` of ranges with an upper bound. -/
  rangeUpper : Array Nat := #[]
  /-- The `|` that open a closure's parameters, and those that close them. -/
  closureOpens : Array Nat := #[]
  closureCloses : Array Nat := #[]
  /-- The lists and blocks whose line breaks the formatter decides. -/
  bracketed : Array Bracketed := #[]
  /-- The spans of expressions that a list may start: each that `expr`
  parses, each operation of a binary operator and its operands, and each
  `if`. -/
  exprs : Array Span := #[]
  /-- The spans of the operations of binary operators, each with that of
  its right operand. -/
  pairs : Array (Span × Span) := #[]
  /-- The right sides of `:=` and `=>` that are expressions: the operator,
  and the first and last tokens of its right side. -/
  rightSides : Array (Nat × Nat × Nat × RightForm) := #[]
  /-- The top-level items, the `import` and `open` lines of the header
  included, in order: the first and last tokens of each, an item's first
  being that of the `set_option ... in` before it, if any. -/
  items : Array (Nat × Nat) := #[]

/-- What a procedure's members need of its header: its results' names. -/
structure ProcHeader where
  results : Array String
  /-- The block is a global expectation's, which has no results. -/
  global : Bool := false
  deriving Inhabited

structure PState where
  toks : Array Token
  /-- The source. -/
  src : Array Char
  pos : Nat := 0
  layout : Layout := {}
  /-- In a `match`'s scrutinee, where `R {` starts the arms rather than a
  record literal. -/
  noRecord : Bool := false
  /-- Where each item starts, in the source. -/
  itemStarts : Array Nat := #[]
  /-- The first tokens of the items that the current token is in, outermost
  first: a top-level item and those after its `set_option ... in`. -/
  items : Array Nat := #[]
  /-- In a definition of a `let`, outside brackets, where `in` ends the
  definitions rather than starting a membership (`Reqs/Lang/Let#parentheses`). -/
  noIn : Bool := false
  stopNamedAnd : Bool := false
  /-- In a procedure's block: its header, whose results `out` defines
  (`F0444`). -/
  proc? : Option ProcHeader := none
  /-- In a function's block: its result's name, which `out` defines
  (`F0444`). -/
  fnResult? : Option String := none
  /-- The lists and blocks open at the current token, innermost last, with
  their commas so far. -/
  openLists : Array Bracketed := #[]
  /-- The clauses of the item being read, in source order, each with its
  keyword, whether it is in a global expectation's block, and where its
  keyword is: the item's structure (`Fren.Core.ItemShape`), from which it
  reports a keyword error once it is read whole (`Fren.Core.itemError?`). -/
  clauses : Array (Fren.Core.ClauseWord × Bool × Span) := #[]

abbrev P := StateT PState (Except ParseError)

end FrenCli
