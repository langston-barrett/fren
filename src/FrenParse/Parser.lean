module

public import FrenParse.Lex

public section
namespace FrenParse
open FrenAst

private structure Cursor where
  lexed : Lexed
  index : Nat := 0

private def peek (c : Cursor) : Option Token := c.lexed.tokens[c.index]?
private def hasText (c : Cursor) (text : String) : Bool := (peek c).any (·.text == text)
/-- Only LF and CRLF end a line in the walking grammar. The decision uses
actual intervening trivia after the left operand's last token, including
comments and a closing parenthesis on a later line. -/
private def newlineBefore (c : Cursor) : Bool :=
  match peek c, c.lexed.tokens[c.index - 1]? with
  | some current, some previous =>
    (c.lexed.tape.extract (previous.slice + 1) current.slice).any
      (fun piece => piece.text.toList.contains '\n')
  | _, _ => false

private def advance (c : Cursor) : Cursor := { c with index := c.index + 1 }
private def fail (c : Cursor) (expected : String) : Except Diagnostic α :=
  .error ⟨(peek c).map (·.span) |>.getD c.lexed.eof, expected⟩

private def take (c : Cursor) (text : String) : Except Diagnostic (Token × Cursor) :=
  match peek c with
  | some token => if token.text == text then .ok (token, advance c) else fail c s!"`{text}`"
  | none => fail c s!"`{text}`"

private def identifier (c : Cursor) : Except Diagnostic (Token × Cursor) :=
  match peek c with
  | some t => if t.kind == .identifier then .ok (t, advance c) else fail c "an identifier"
  | none => fail c "an identifier"

private def path (c : Cursor) : Except Diagnostic (Path × Cursor) := do
  let (head, c) ← identifier c
  let mut c := c
  let mut tail := #[]
  -- Each iteration consumes :: and one identifier or fails.
  for _ in [:c.lexed.tokens.size + 1] do
    if !hasText c "::" then return (⟨head, tail⟩, c)
    let (separator, rest) ← take c "::"
    let (name, rest) ← identifier rest
    tail := tail.push (separator, name)
    c := rest
  fail c "a finite name path"

private def typeSyntax (c : Cursor) : Except Diagnostic (Ty × Cursor) := do
  if hasText c "Bool" then
    let (t, c) ← take c "Bool"
    return (.bool t, c)
  if hasText c "Int" then
    let (t, c) ← take c "Int"
    return (.int t, c)
  let (p, c) ← path c
  return (.named p, c)

private def parameters (c : Cursor) : Except Diagnostic (Parameters × Cursor) := do
  let (openToken, c) ← take c "("
  let mut c := c
  let mut values : Array Parameter := #[]
  let mut commas := #[]
  for _ in [:c.lexed.tokens.size + 1] do
    if hasText c ")" then
      let (closeToken, rest) ← take c ")"
      return (⟨openToken, values, commas, closeToken⟩, rest)
    let (name, rest) ← identifier c
    let (annotation, rest) ← if name.text.endsWith "?" then pure (none, rest) else do
      let (colon, rest) ← take rest ":"
      let (ty, rest) ← typeSyntax rest
      pure (some (colon, ty), rest)
    values := values.push ⟨name, annotation⟩
    c := rest
    if !hasText c "," then
      let (closeToken, rest) ← take c ")"
      return (⟨openToken, values, commas, closeToken⟩, rest)
    let (comma, rest) ← take c ","
    commas := commas.push comma
    c := rest
  fail c "`)`"

/-- Larger numbers bind more tightly. Comparisons bind inside `not`. -/
def binaryOperator (text : String) : Option (BinaryOp × Nat) :=
  match text with
  | "iff" => some (.iff, 1)
  | "or" => some (.or, 2)
  | "and" => some (.and, 3)
  | "=" => some (.eq, 5) | "!=" => some (.ne, 5)
  | "<" => some (.lt, 5) | "<=" => some (.le, 5)
  | ">" => some (.gt, 5) | ">=" => some (.ge, 5)
  | "+" => some (.add, 6) | "-" => some (.sub, 6)
  | "*" => some (.mul, 7) | "div" => some (.div, 7) | "mod" => some (.mod, 7)
  | _ => none

private def comparison : BinaryOp → Bool
  | .eq | .ne | .lt | .le | .gt | .ge => true
  | _ => false

/-- The walking AST represents binary comparisons, not full-language chains.
An explicit paren node ends this restriction; typing still remains later. -/
private def unsupportedChain (left : Expr) (op : BinaryOp) : Bool :=
  match left with
  | .binary _ _ previous _ =>
    (comparison previous && comparison op) || (previous == .iff && op == .iff)
  | _ => false

-- Structural recursion on a token-derived budget, with no fixed nesting cap.
-- An expression/leading transition costs one, and each tail/list transition
-- either consumes a token or finishes. Four units per input token plus four
-- cover these transitions, including empty lists. Exhaustion is a failure,
-- never a fabricated successful node. Repetition bounds likewise derive from
-- the actual token count. These bounds are not caller-controlled.
mutual
private def expression : Nat → Nat → Cursor → Except Diagnostic (Expr × Cursor)
  | 0, _, c => fail c "an expression"
  | fuel + 1, minPrec, c => do
    let (left, c) ← leading fuel minPrec c
    tails fuel minPrec left c

private def leading : Nat → Nat → Cursor → Except Diagnostic (Expr × Cursor)
  | 0, _, c => fail c "an expression"
  | fuel + 1, minPrec, c => do
    let some token := peek c | fail c "an expression"
    if token.text == "not" && 4 < minPrec then
      fail c "parentheses around `not` in a tighter operand"
    if token.text == "let" && 0 < minPrec then
      fail c "parentheses around `let` in an operator operand"
    if token.text == "-" || token.text == "not" then
      let op := if token.text == "-" then UnaryOp.neg else UnaryOp.not
      let (body, c) ← expression fuel (if op == .neg then 8 else 4) (advance c)
      return (.unary token op body, c)
    if token.text == "(" then
      let (body, c) ← expression fuel 0 (advance c)
      let (closeToken, c) ← take c ")"
      return (.paren token body closeToken, c)
    if token.text == "if" then
      let (condition, c) ← expression fuel 0 (advance c)
      let (thenToken, c) ← take c "then"
      let (yes, c) ← expression fuel 0 c
      let (elseToken, c) ← take c "else"
      let (no, c) ← expression fuel 0 c
      return (.ifE token condition thenToken yes elseToken no, c)
    if token.text == "let" then
      let (name, c) ← identifier (advance c)
      let (assign, c) ← take c ":="
      let (value, c) ← expression fuel 0 c
      let (inToken, c) ← take c "in"
      let (body, c) ← expression fuel 0 c
      return (.letE token name assign value inToken body, c)
    if token.text == "match" then
      let (scrutinee, c) ← expression fuel 0 (advance c)
      let (openToken, c) ← take c "{"
      let (arms, c) ← matchArms fuel c
      let (closeToken, c) ← take c "}"
      return (.matchE token scrutinee openToken arms closeToken, c)
    if token.text == "true" || token.text == "false" then
      return (.bool token (token.text == "true"), advance c)
    if token.kind == .numeral then
      let some value := token.text.toNat? | fail c "a decimal integer"
      return (.integer token value, advance c)
    if token.kind == .identifier then
      let (p, c) ← path c
      return (.name p, c)
    fail c "an expression"

private def tails : Nat → Nat → Expr → Cursor → Except Diagnostic (Expr × Cursor)
  | 0, _, _, c => fail c "an expression continuation"
  | fuel + 1, minPrec, left, c => do
    if hasText c "(" then
      let (openToken, c) ← take c "("
      let (args, commas, c) ← arguments fuel c
      let (closeToken, c) ← take c ")"
      tails fuel minPrec (.call left openToken args commas closeToken) c
    else
      if hasText c "mod" && newlineBefore c then return (left, c)
      match (peek c).bind (fun t => binaryOperator t.text) with
      | some (op, prec) =>
        if prec < minPrec then return (left, c)
        if unsupportedChain left op then
          fail c "parentheses around nested comparisons or `iff` (chains are outside the walking subset)"
        let some token := peek c | fail c "an operator"
        let (right, c) ← expression fuel (prec + 1) (advance c)
        tails fuel minPrec (.binary left token op right) c
      | none => return (left, c)

private def arguments : Nat → Cursor → Except Diagnostic (Array Expr × Array Token × Cursor)
  | 0, c => fail c "an argument or `)`"
  | fuel + 1, c => do
    if hasText c ")" then return (#[], #[], c)
    let (value, c) ← expression fuel 0 c
    if !hasText c "," then return (#[value], #[], c)
    let (comma, c) ← take c ","
    let (values, commas, c) ← arguments fuel c
    return (#[value] ++ values, #[comma] ++ commas, c)

private def matchArms : Nat → Cursor → Except Diagnostic
    (Array (Path × Token × Expr × Option Token) × Cursor)
  | 0, c => fail c "a qualified variant arm or `}`"
  | fuel + 1, c => do
    if hasText c "}" then return (#[], c)
    let (variant, c) ← path c
    if variant.tail.isEmpty then fail c "`::` and a variant name"
    let (arrow, c) ← take c "=>"
    let (body, c) ← expression fuel 0 c
    if !hasText c "," then return (#[⟨variant, arrow, body, none⟩], c)
    let (comma, c) ← take c ","
    let (arms, c) ← matchArms fuel c
    return (#[⟨variant, arrow, body, some comma⟩] ++ arms, c)
end

private def readExpression (c : Cursor) : Except Diagnostic (Expr × Cursor) :=
  expression (4 * c.lexed.tokens.size + 4) 0 c

private def declaration (c : Cursor) : Except Diagnostic (Decl × Cursor) := do
  let (visibility, c) ← if hasText c "pub" then do
    let (token, c) ← take c "pub"
    pure (some token, c)
    else pure (none, c)
  if hasText c "mod" then
    let (keyword, c) ← take c "mod"
    let (p, c) ← path c
    return (.moduleDecl visibility keyword p, c)
  if hasText c "enum" then
    let (keyword, c) ← take c "enum"
    let (name, c) ← identifier c
    let (openToken, c) ← take c "{"
    let mut c := c
    let mut variants := #[]
    let mut commas := #[]
    for _ in [:c.lexed.tokens.size + 1] do
      if hasText c "}" then
        let (closeToken, rest) ← take c "}"
        return (.enumDecl visibility keyword name openToken variants commas closeToken, rest)
      let (variant, rest) ← identifier c
      variants := variants.push variant
      c := rest
      if !hasText c "," then
        let (closeToken, rest) ← take c "}"
        return (.enumDecl visibility keyword name openToken variants commas closeToken, rest)
      let (comma, rest) ← take c ","
      commas := commas.push comma
      c := rest
    fail c "`}`"
  if hasText c "fn" then
    let (keyword, c) ← take c "fn"
    let (name, c) ← identifier c
    let (params, c) ← parameters c
    let (colon, c) ← take c ":"
    let (result, c) ← typeSyntax c
    let (assign, c) ← take c ":="
    let (body, c) ← readExpression c
    return (.function visibility keyword name params colon result assign body, c)
  if visibility.isNone && hasText c "expect" then
    let (keyword, c) ← take c "expect"
    let (name, c) ← identifier c
    let (params, c) ← parameters c
    let (openToken, c) ← take c "{"
    let mut c := c
    let mut members : Array Member := #[]
    for _ in [:c.lexed.tokens.size + 1] do
      if hasText c "}" then
        let (closeToken, rest) ← take c "}"
        return (.expectation keyword name params openToken members closeToken, rest)
      let some memberToken := peek c | fail c "`assume`, `expect` or `}`"
      let kind ← if memberToken.text == "assume" then pure MemberKind.assume
        else if memberToken.text == "expect" then pure MemberKind.expect
        else fail c "`assume`, `expect` or `}`"
      let (label, rest) ← identifier (advance c)
      let (colon, rest) ← take rest ":"
      let (body, rest) ← readExpression rest
      members := members.push ⟨memberToken, kind, label, colon, body⟩
      c := rest
    fail c "`}`"
  fail c "a module, enum, function or expectation declaration"

private def declarations (c : Cursor) : Except Diagnostic ((Array Decl) × Cursor) := do
  let mut c := c
  let mut values := #[]
  for _ in [:c.lexed.tokens.size + 1] do
    if (peek c).isNone then return (values, c)
    let (value, rest) ← declaration c
    values := values.push value
    c := rest
  fail c "end of declarations"

/-- Failure retains every lexical byte but cannot be confused with a complete
Document. No recovery or later semantic pass is claimed. -/
structure Failure where
  lexed : Lexed
  diagnostic : Diagnostic
  deriving Repr, BEq

def Failure.emit (failure : Failure) : String := emitTape failure.lexed.tape

/-- The single grammar implementation. Entry selects only the root category. -/
def parse (entry : Entry) (file : FrenSource.FileId) (source : String) : Except Failure Document :=
  let lexed := tokenize file source
  let c : Cursor := ⟨lexed, 0⟩
  let result : Except Diagnostic (Root × Cursor) := do
    match entry with
    | .file | .context =>
      let (values, c) ← declarations c
      return (.declarations values, c)
    | .expression =>
      let (value, c) ← readExpression c
      return (.expression value, c)
  let completed := do
    let (root, c) ← result
    if (peek c).isSome then fail c "end of input"
    return ({ file, source, tape := lexed.tape, entry, root } : Document)
  completed.mapError fun diagnostic => ⟨lexed, diagnostic⟩

def parseFile := parse .file
def parseContext := parse .context
def parseExpression := parse .expression

/-- The decoded-text parser is also the only grammar behind byte ingestion. -/
def parseBytes (entry : Entry) (file : FrenSource.FileId) (bytes : ByteArray) :
    Except String Document := do
  let source ← decode bytes
  (parse entry file source).mapError (·.diagnostic.render)

--@ reference: parsing.determinism
theorem deterministic (entry : Entry) (file : FrenSource.FileId) (text : String)
    (first second : Except Failure Document)
    (hfirst : parse entry file text = first) (hsecond : parse entry file text = second) :
    first = second := hfirst.symm.trans hsecond

/-- Actual producer laws. Tested below with accepted, rejected and partial text;
these definitions do not assert their universal truth. -/
def LosslessOnSuccess : Prop := ∀ entry file source doc,
  parse entry file source = .ok doc → doc.emit = source

def ReparseOnSuccess : Prop := ∀ entry file source doc,
  parse entry file source = .ok doc → parse entry file doc.emit = .ok doc

end FrenParse
