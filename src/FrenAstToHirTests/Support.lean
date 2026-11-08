module

public import FrenAstToHir
public import FrenParse

public section
namespace FrenAstToHirTests
open FrenAst FrenModule FrenAstToHir

def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def parsed (text : String) (file : Nat := 47) : IO Document := do
  match FrenParse.parseFile ⟨file⟩ text with
  | .ok doc => return doc
  | .error error => throw (IO.userError s!"unexpected parse failure: {repr error.diagnostic}")

def resolved (text : String) : IO Resolved := do
  let doc ← parsed text
  match resolve doc with
  | .ok result => return result
  | .error error => throw (IO.userError s!"unexpected resolution failure: {repr error}")

def failure (text code name : String) : IO FrenDiag.Diagnostic := do
  let doc ← parsed text
  let .error diagnostic := resolve doc | throw (IO.userError s!"unexpected resolution success: {text}")
  require (diagnostic.code == some code && diagnostic.headline.contains name.toSlice)
    s!"wrong diagnostic: {repr diagnostic}"
  return diagnostic

def expressionRefs (result : Resolved) : Array Reference :=
  result.references.filter (·.role == .expression)

def targets (result : Resolved) : Array Target :=
  (expressionRefs result).map (·.target)

def writtenTokens : Written → List Token
  | .path path => path.tokens
  | .builtin token | .implicitBool token => [token]

/-- Audit source occurrences against the actual tape and local targets against
actual binding entries. This does not recompute resolver lookup. -/
def audit (doc : Document) (result : Resolved) : Bool :=
  result.document == doc && result.document.emit == doc.source &&
  result.references.all (fun ref =>
    (writtenTokens ref.written).all (fun t =>
      doc.tape[t.slice]?.any (fun piece => piece.text == t.text && piece.span == t.span &&
        piece.kind == t.kind) && t.span.file == doc.file &&
      t.span.start < t.span.stop && t.span.stop ≤ doc.source.utf8ByteSize) &&
    (match ref.target with
     | .local i =>
       i < ref.context.length &&
         (FrenBase.Binding.lookup ref.context i).any (·.text == ref.written.anchor.text)
     | .item id => id == result.scope.id || result.scope.items.any (·.id == id)
     | .boolType | .intType => ref.role == .annotation)) &&
  (result.references.toList.map (·.written.anchor.slice)).eraseDups.length == result.references.size

def describe (ref : Reference) : String :=
  let role := match ref.role with | .expression => "E" | .annotation => "A" | .pattern => "P"
  let text := match ref.written with
    | .path path => "".intercalate (path.tokens.map (fun (t : Token) => t.text))
    | .builtin t => t.text
    | .implicitBool t => t.text ++ "(implicit Bool)"
  let target := match ref.target with
    | .item id => "item:" ++ id.render
    | .local i => s!"local:{i}"
    | .boolType => "Bool" | .intType => "Int"
  let first := ref.written.anchor.span
  let last := ((writtenTokens ref.written).getLast?).getD ref.written.anchor
  s!"{role} {text} {target} {first.file.value}:{first.start}-{last.span.stop}"

end FrenAstToHirTests
