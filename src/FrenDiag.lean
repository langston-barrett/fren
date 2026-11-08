module

public import FrenSource

public section
namespace FrenDiag

/-- A source diagnostic in Fren2 byte coordinates. Catalogue codes are reused;
`none` denotes an unsupported API input, not a new language error code. -/
structure Diagnostic where
  code : Option String
  headline : String
  span : FrenSource.Span
  deriving Repr, BEq

end FrenDiag
