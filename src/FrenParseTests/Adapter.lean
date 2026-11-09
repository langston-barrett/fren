module

public import FrenParse
public import FrenTextTests

public section
namespace FrenParseTests
open FrenAst FrenParse

/-- Development adapter for library textual tests. The context grammar is
exactly the production declaration entry; callbacks receive its typed tree.
No lookup or evaluation is performed here. -/
def contextRunner (file : FrenSource.FileId)
    (run : Document → String → IO (Except String String)) : Fren.TextTests.Runner :=
  .of (fun raw => (parseContext file raw).mapError (·.diagnostic.render)) run

/-- An inspection codec for tests, deliberately independent of lexical emission. -/
def describe : Expr → String
  | .name path => "::".intercalate (path.tokens.filter (·.text != "::") |>.map (·.text))
  | .bool _ b => if b then "true" else "false"
  | .integer _ n => toString n
  | .paren _ body _ => s!"(paren {describe body})"
  | .unary t _ body => s!"({t.text} {describe body})"
  | .binary l t _ r => s!"({t.text} {describe l} {describe r})"
  | .call f _ args _ _ => "(call " ++ describe f ++
      (args.foldl (fun s e => s ++ " " ++ describe e) "") ++ ")"
  | .ifE _ condition _ yes _ no => s!"(if {describe condition} {describe yes} {describe no})"
  | .letE _ name _ value _ body => s!"(let {name.text} {describe value} {describe body})"
  | .matchE _ scrutinee _ arms _ => "(match " ++ describe scrutinee ++
      (arms.toList.foldl (fun s arm =>
        s ++ " (" ++ "".intercalate (arm.1.tokens.map (·.text)) ++ " " ++ describe arm.2.2.1 ++ ")") "") ++ ")"
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

def describeDecl : Decl → String
  | .moduleDecl _ _ path => "mod " ++ "".intercalate (path.tokens.map (·.text))
  | .enumDecl _ _ name _ variants _ _ =>
    "enum " ++ name.text ++ " [" ++ ",".intercalate (variants.toList.map (·.text)) ++ "]"
  | .function _ _ name _ _ _ _ body => s!"fn {name.text} {describe body}"
  | .expectation _ name _ _ members _ => "expect " ++ name.text ++ " [" ++
      ",".intercalate (members.toList.map fun m =>
        s!"{m.keyword.text} {m.label.text} {describe m.body}") ++ "]"

def sameResult [BEq ε] [BEq α] (left right : Except ε α) : Bool :=
  match left, right with
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false

--@ reference: parsing.tree.structure
/-- Audit actual terminal occurrences against independently scanned tokens. -/
def coherent (doc : Document) : Bool :=
  let lexed := tokenize doc.file doc.source
  ownsSource doc.file doc.source doc.tape && doc.tape == lexed.tape &&
    doc.tape.all (·.kind != .rejected) &&
    doc.root.tokens.toArray == lexed.tokens &&
    doc.tape.all (fun piece => boundary doc.source piece.span.start && boundary doc.source piece.span.stop)

--@ reference: parsing.lossless.ownership
--@ reference: parsing.source.bounds
--@ reference: parsing.source.utf8
--@ reference: parsing.complete
--@ reference: parsing.failure
--@ reference: parsing.diagnostic.anchor
--@ reference: parsing.roundtrip
/-- Both outcomes are checked. No accepted-parse implication can discard a
malformed sample, and failure retains and audits the full lexical tape. -/
def audit (entry : Entry) (file : FrenSource.FileId) (text : String) : Bool :=
  match parse entry file text with
  | .ok doc => coherent doc && doc.emit == text && sameResult (parse entry file doc.emit) (.ok doc) &&
      doc.file == file && doc.entry == entry && doc.source == text &&
      (match entry, doc.root with
       | .expression, .expression _ => true
       | .file, .declarations _ | .context, .declarations _ => true
       | _, _ => false)
  | .error failed =>
    let d := failed.diagnostic
    ownsSource file text failed.lexed.tape && failed.emit == text &&
      d.span.file == file && d.span.start ≤ d.span.stop && d.span.stop ≤ text.utf8ByteSize &&
      boundary text d.span.start && boundary text d.span.stop && !d.expected.isEmpty &&
      (d.span == failed.lexed.eof || failed.lexed.tokens.any (·.span == d.span))

--@ reference: parsing.shared.entry
/-- The file and context entries give the same tree or the same diagnostic. -/
def entriesAgree (text : String) (file : Nat) : Bool :=
  match parseFile ⟨file⟩ text, parseContext ⟨file⟩ text with
  | .ok a, .ok b => a.root == b.root && a.tape == b.tape && a.emit == b.emit
  | .error a, .error b => a == b
  | _, _ => false

@[fren_text_tests "test/FrenParse"]
def parserRunner : Fren.TextTests.Runner := contextRunner ⟨17⟩ fun context input => do
  let .declarations ctx := context.root | return .error "context root"
  match parseFile ⟨18⟩ input with
  | .error failure =>
    if failure.emit != input then return .error "failed-input ownership"
    return .ok ("syntax " ++ failure.diagnostic.render)
  | .ok doc =>
    if !coherent doc || doc.emit != input || !sameResult (parseFile ⟨18⟩ doc.emit) (.ok doc) then
      return .error "tree/lossless audit"
    let .declarations decls := doc.root | return .error "file root"
    return .ok (s!"context={ctx.size};" ++
      (if decls.isEmpty then "" else " " ++ "; ".intercalate (decls.toList.map describeDecl)))

end FrenParseTests
