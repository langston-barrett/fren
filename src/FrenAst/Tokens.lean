module

public import FrenAst.Basic

public section
namespace FrenAst

def Path.tokens (path : Path) : List Token :=
  path.head :: (path.tail.toList.flatMap fun (separator, name) => [separator, name])

def Ty.tokens : Ty → List Token
  | .bool t | .int t => [t]
  | .named path => path.tokens

private def separated (values : Array (List Token)) (commas : Array Token) : List Token :=
  (values.toList.zipIdx.flatMap fun (value, i) => value ++ (commas[i]?).toList)

/-- Traverse written terminals in grammar order, independently of the lexical
scanner. This lets clients audit that the structured tree uses every token. -/
def Expr.tokens : Expr → List Token
  | .name path => path.tokens
  | .bool t _ | .integer t _ => [t]
  | .paren o body c => [o] ++ body.tokens ++ [c]
  | .unary t _ body => [t] ++ body.tokens
  | .binary left t _ right => left.tokens ++ [t] ++ right.tokens
  | .call callee o args commas c =>
    callee.tokens ++ [o] ++ separated (args.map Expr.tokens) commas ++ [c]
  | .ifE i condition t yes e no =>
    [i] ++ condition.tokens ++ [t] ++ yes.tokens ++ [e] ++ no.tokens
  | .letE l binder assign value i body => [l, binder, assign] ++ value.tokens ++ [i] ++ body.tokens
  | .matchE m scrutinee o arms c =>
    [m] ++ scrutinee.tokens ++ [o] ++ (arms.toList.flatMap fun arm =>
      arm.1.tokens ++ [arm.2.1] ++ arm.2.2.1.tokens ++ arm.2.2.2.toList) ++ [c]
termination_by e => sizeOf e
decreasing_by
  all_goals first | decreasing_tactic |
    have h := Array.sizeOf_lt_of_mem (show arm ∈ arms from by simpa using ‹arm ∈ arms.toList›)
    have hchild : sizeOf arm.snd.snd.fst < sizeOf arm := by
      rcases arm with ⟨p, arrow, body, comma⟩
      simp only [Prod.mk.sizeOf_spec]
      omega
    simp only [Expr.matchE.sizeOf_spec]
    omega

def Parameter.tokens (param : Parameter) : List Token :=
  [param.name] ++ (param.annotation.toList.flatMap fun (colon, ty) => [colon] ++ ty.tokens)

def Parameters.tokens (params : Parameters) : List Token :=
  [params.openToken] ++ separated (params.values.map Parameter.tokens) params.commas ++ [params.closeToken]

def Member.tokens (member : Member) : List Token :=
  [member.keyword, member.label, member.colon] ++ member.body.tokens

def Decl.tokens : Decl → List Token
  | .moduleDecl visibility keyword path => visibility.toList ++ [keyword] ++ path.tokens
  | .enumDecl visibility keyword name o variants commas c =>
    visibility.toList ++ [keyword, name, o] ++ separated (variants.map (fun t => [t])) commas ++ [c]
  | .function visibility keyword name params colon result assign body =>
    visibility.toList ++ [keyword, name] ++ params.tokens ++ [colon] ++ result.tokens ++ [assign] ++ body.tokens
  | .expectation keyword name params o members c =>
    [keyword, name] ++ params.tokens ++ [o] ++ (members.toList.flatMap Member.tokens) ++ [c]

def Root.tokens : Root → List Token
  | .declarations values => values.toList.flatMap Decl.tokens
  | .expression value => value.tokens

/-- Reconstruct from syntax terminals in grammar order and the tape's trivia.
Nontrivia tape slices are never copied in place of absent syntax nodes. A
parsed document has one matching terminal per nontrivia tape slice; arbitrary
edited trees need the corresponding well-formedness invariant to roundtrip. -/
@[expose] def Document.emit (doc : Document) : String := Id.run do
  let mut cursor := 0
  let mut text := ""
  for token in doc.root.tokens do
    for piece in doc.tape.extract cursor token.slice do
      if piece.kind == .trivia then text := text ++ piece.text
    text := text ++ token.text
    cursor := token.slice + 1
  for piece in doc.tape.extract cursor doc.tape.size do
    if piece.kind == .trivia then text := text ++ piece.text
  return text

/-- Retained source storage is not an escape hatch for emission. -/
theorem Document.emit_source_irrelevant (doc : Document) (source : String) :
    ({doc with source} : Document).emit = doc.emit := rfl

/-- A node's enclosure is computed from its written terminals, not raw character
indices. Empty declaration sequences have no written-node span. -/
def Root.span? (root : Root) (size : Nat) : Option FrenSource.Span := do
  let first ← root.tokens.head?
  let last ← root.tokens.getLast?
  FrenSource.Span.checked first.span.file first.span.start last.span.stop size

end FrenAst
