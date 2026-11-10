module

public import FrenSource

public section
namespace FrenAst

inductive LexicalKind where
  | identifier | keyword | numeral | punctuation | trivia | rejected
  deriving Repr, BEq, DecidableEq, ReflBEq, LawfulBEq

/-- The tape owns bytes once; syntax references tape positions. Spelling is
stored per slice, so emission never reads the retained source string. -/
structure Slice where
  kind : LexicalKind
  text : String
  span : FrenSource.Span
  deriving Repr, BEq

structure Token where
  slice : Nat
  text : String
  span : FrenSource.Span
  kind : LexicalKind
  deriving Repr, BEq, DecidableEq, ReflBEq, LawfulBEq

structure Path where
  head : Token
  tail : Array (Token × Token) := #[] -- separator, name, in written order
  deriving Repr, BEq, DecidableEq, ReflBEq, LawfulBEq

inductive Ty where
  | bool (token : Token)
  | int (token : Token)
  | named (path : Path)
  deriving Repr, BEq, ReflBEq, LawfulBEq

/-- Implicit Bool is written with a question-mark suffix on the name. -/
structure Parameter where
  name : Token
  annotation : Option (Token × Ty)
  deriving Repr, BEq, ReflBEq, LawfulBEq

inductive UnaryOp where
  | neg | not
  deriving Repr, BEq, DecidableEq

inductive BinaryOp where
  | add | sub | mul | div | rem | eq | ne | lt | le | gt | ge | and | or | iff
  deriving Repr, BEq, DecidableEq

/-- Syntax, not a resolved or typed IR. Repeated names have distinct tokens.
All delimiters and operator occurrences remain explicit. -/
inductive Expr where
  | name (path : Path)
  | bool (token : Token) (value : Bool)
  | integer (token : Token) (value : Nat)
  | paren (openToken : Token) (body : Expr) (closeToken : Token)
  | unary (token : Token) (op : UnaryOp) (body : Expr)
  | binary (left : Expr) (token : Token) (op : BinaryOp) (right : Expr)
  | call (callee : Expr) (openToken : Token) (args : Array Expr)
      (commas : Array Token) (closeToken : Token)
  | ifE (ifToken : Token) (condition : Expr) (thenToken : Token)
      (yes : Expr) (elseToken : Token) (no : Expr)
  | letE (letToken name assign : Token) (value : Expr) (inToken : Token) (body : Expr)
  | matchE (matchToken : Token) (scrutinee : Expr) (openToken : Token)
      (arms : Array (Path × Token × Expr × Option Token)) (closeToken : Token)
  deriving Repr, BEq

structure Parameters where
  openToken : Token
  values : Array Parameter
  commas : Array Token
  closeToken : Token
  deriving Repr, BEq

inductive MemberKind where
  | assume | expect
  deriving Repr, BEq, DecidableEq

structure Member where
  keyword : Token
  kind : MemberKind
  label : Token
  colon : Token
  body : Expr
  deriving Repr, BEq

inductive Decl where
  | moduleDecl (visibility : Option Token) (keyword : Token) (path : Path)
  | enumDecl (visibility : Option Token) (keyword name openToken : Token)
      (variants : Array Token) (commas : Array Token) (closeToken : Token)
  | function (visibility : Option Token) (keyword name : Token) (params : Parameters)
      (colon : Token) (result : Ty) (assign : Token) (body : Expr)
  | expectation (keyword name : Token) (params : Parameters) (openToken : Token)
      (members : Array Member) (closeToken : Token)
  deriving Repr, BEq

inductive Entry where
  | file | context | expression
  deriving Repr, BEq, DecidableEq

inductive Root where
  | declarations (values : Array Decl)
  | expression (value : Expr)
  deriving Repr, BEq

structure Document where
  file : FrenSource.FileId
  source : String
  tape : Array Slice
  entry : Entry
  root : Root
  deriving Repr, BEq

/-- Reconstruct the actual owned lexical pieces, including their original EOLs. -/
def emitTape (tape : Array Slice) : String :=
  tape.foldl (fun text piece => text ++ piece.text) ""

/-- Independent executable audit of lexical ownership against actual bytes.
This is evidence to check, never a caller-supplied validity flag. -/
def ownsSource (file : FrenSource.FileId) (source : String) (tape : Array Slice) : Bool := Id.run do
  let mut offset := 0
  for piece in tape do
    if piece.text.isEmpty || piece.span.file != file || piece.span.start != offset ||
        piece.span.stop != offset + piece.text.utf8ByteSize then return false
    offset := piece.span.stop
  return offset == source.utf8ByteSize && emitTape tape == source

end FrenAst
