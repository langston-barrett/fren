module

public import FrenParse.Parser

public section
namespace FrenParse
open FrenAst

/-- Requirements of the actual producer, not axioms. The normal test root runs
Plausible and textual instances of these obligations. Except for the primitive
classifier theorems and functional determinism, evidence is sampled, not a
universal parser correctness proof. -/
def Ownership : Prop := ∀ file source,
  ownsSource file source (tokenize file source).tape = true

def SourceBounds : Prop := ∀ entry file source,
  let lexed := tokenize file source
  (∀ piece ∈ lexed.tape, piece.span.file = file ∧ piece.span.start < piece.span.stop ∧
    piece.span.stop ≤ source.utf8ByteSize) ∧
  (∀ failure, parse entry file source = .error failure →
    failure.diagnostic.span.file = file ∧
    failure.diagnostic.span.start ≤ failure.diagnostic.span.stop ∧
    failure.diagnostic.span.stop ≤ source.utf8ByteSize)

def Utf8Boundaries : Prop := ∀ entry file source,
  let lexed := tokenize file source
  (∀ piece ∈ lexed.tape, boundary source piece.span.start = true ∧
    boundary source piece.span.stop = true) ∧
  (∀ failure, parse entry file source = .error failure →
    boundary source failure.diagnostic.span.start = true ∧
    boundary source failure.diagnostic.span.stop = true)

/-- Complete success has the requested root and exactly the independently
scanned terminal sequence, without rejected slices or unconsumed tokens. -/
def CompleteInput : Prop := ∀ entry file source doc,
  parse entry file source = .ok doc →
  doc.file = file ∧ doc.source = source ∧ doc.entry = entry ∧
  doc.tape = (tokenize file source).tape ∧
  doc.root.tokens.toArray = (tokenize file source).tokens ∧
  (∀ piece ∈ doc.tape, piece.kind ≠ .rejected) ∧
  (match entry, doc.root with
   | .expression, .expression _ => True
   | .file, .declarations _ | .context, .declarations _ => True
   | _, _ => False)

def FailureAnchors : Prop := ∀ entry file source failure,
  parse entry file source = .error failure →
  failure.emit = source ∧ failure.diagnostic.expected ≠ "" ∧
  (failure.diagnostic.span = failure.lexed.eof ∨
    ∃ token ∈ failure.lexed.tokens, token.span = failure.diagnostic.span)

end FrenParse
