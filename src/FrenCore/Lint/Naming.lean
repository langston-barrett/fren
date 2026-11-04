-- keep-sorted start
import FrenCore.Lint.Model
import FrenCore.Names
-- keep-sorted end

/-!
# Naming and item size lints

Part of `FrenCore.Lint`, shared by both front ends.
-/

open Lean

namespace Fren.Core

/-! ## Naming conventions -/

inductive Case where
  | snake
  | camel
  | upper
  deriving Inhabited, BEq, DecidableEq, Repr

/-- What a declared name names (`lint::Named`). -/
inductive Named where
  | module
  | component
  | variable
  /-- A field of a record. -/
  | field
  /-- A binder of a `match` pattern. -/
  | binder
  | function
  | instance
  | constraint
  | global
  | enumeration
  | variant
  | record
  | abstractType
  | typeAlias
  | constant
  /-- A trait (`Reqs/Lang/Traits`). -/
  | «trait»
  /-- A law of a trait. -/
  | law
  /-- A method of a trait, which is part of it, and never dead. -/
  | method
  deriving Inhabited, BEq, DecidableEq, Repr

def Named.describe : Named → String
  | .module => "module"
  | .component => "procedure"
  | .variable => "variable"
  | .field => "field"
  | .binder => "binder"
  | .function => "function"
  | .instance => "call"
  | .constraint => "constraint"
  | .global => "global expectation"
  | .enumeration => "enum"
  | .variant => "variant"
  | .record => "record"
  | .abstractType => "abstract type"
  | .typeAlias => "type alias"
  | .constant => "constant"
  | .trait => "trait"
  | .law => "law"
  | .method => "method"

/-- The case of a name (`lint::naming_case`). -/
def Named.case : Named → Case
  | .enumeration | .variant | .record | .abstractType | .typeAlias | .trait => .camel
  | .constant => .upper
  | _ => .snake

def Case.lint : Case → Lint
  | .snake => .nonSnakeCase
  | .camel => .nonCamelCaseTypes
  | .upper => .nonUpperCaseConstants

def Case.describe : Case → String
  | .snake => "a snake case"
  | .camel => "a camel case"
  | .upper => "an upper case"

/-- Whether a name is in a case, from its letters (`lint::in_case`). -/
def inCase (c : Case) (startsUpper hasUpper hasLower hasUnderscore : Bool) : Bool :=
  match c with
  | .snake => !hasUpper
  | .camel => startsUpper && !hasUnderscore
  | .upper => startsUpper && !hasLower

def isUpperAscii (c : Char) : Bool := 'A' ≤ c && c ≤ 'Z'
def isLowerAscii (c : Char) : Bool := 'a' ≤ c && c ≤ 'z'

/-- The name without a variable's final `?`. -/
def baseName (s : String) : String := (s.dropEndWhile (· == '?')).toString

/-- Whether `s` is in case `c` (`lint::in_case`). A variable's final `?`
is neither a letter nor `_`, so it changes nothing. -/
def nameInCase (s : String) (c : Case) : Bool :=
  let cs := s.toList
  inCase c (cs.head?.any isUpperAscii) (cs.any isUpperAscii) (cs.any isLowerAscii) (cs.contains '_')

/-- The words of a name: split at `_` and before an uppercase letter that
follows a lowercase letter or a digit. -/
def words (s : String) : List String := Id.run do
  let mut out : Array String := #[]
  let mut cur := ""
  let mut prev : Option Char := none
  for c in s.toList do
    if c == '_' then
      out := out.push cur; cur := ""
    else
      if isUpperAscii c && prev.any (fun p => isLowerAscii p || p.isDigit) then
        out := out.push cur; cur := ""
      cur := cur.push c
    prev := some c
  return (out.push cur).toList.filter (!·.isEmpty)

/-- `s` converted to case `c`, keeping a final `?`. -/
def toCase (c : Case) (s : String) : String :=
  let q := String.ofList (s.toList.reverse.takeWhile (· == '?'))
  let ws := words (baseName s)
  let base := match c with
    | .snake => "_".intercalate (ws.map String.toLower)
    | .upper => "_".intercalate (ws.map String.toUpper)
    | .camel => String.join (ws.map fun w => (w.toLower.capitalize))
  base ++ q

/-- The naming lint for a declared name, if it is not in its case. -/
def namingMsg? (what : Named) (n : Name) : Option (Lint × Msg) :=
  let s := n.toString
  let c := what.case
  if nameInCase s c then none else
  let fixed := toCase c s
  let fixes := if fixed.isEmpty || fixed == s || (fixed.front.isDigit) || !nameInCase fixed c then #[]
    else #[{ msg := s!"rename it to `{fixed}`", replacement := fixed : Fix }]
  some (c.lint, {
    code? := some c.lint.code, headline := s!"{what.describe} `{s}` should have {c.describe} name"
    label? := some s!"not in {match c with | .snake => "snake_case" | .camel => "CamelCase" | .upper => "UPPER_CASE"}"
    fixes })

/-! ## Names -/

/-- Whether `module_inception` fires on a module named `name` whose parent
is named `parent`, `""` for a top-level module (`lint::module_inception`). -/
def moduleInception (name parent : String) : Bool := name == parent

/-- `module_inception` for the module at `path`, if its last segment repeats
its parent's. -/
def moduleInceptionMsg? (path : Name) : Option Msg :=
  match path.components.reverse with
  | n :: p :: _ =>
    if moduleInception (nameText n) (nameText p) then
      some { code? := some Lint.moduleInception.code
             headline := s!"module `{showPath path}` has the same name as its parent"
             label? := some s!"inside `{nameText p}`"
             notes := #["note: every path to it, or to an item in it, repeats the name",
               s!"help: rename it, or declare its items in `{showPath path.getPrefix}`"] }
    else none
  | _ => none

/-- Whether `enum_variant_names` fires on an enumeration of `nVariants`
variants, each of two or more words, all of which start, or end, with the
same word (`lint::enum_variant_names`). -/
def enumVariantNames (nVariants : Nat) (sharedFirst sharedLast : Bool) : Bool :=
  nVariants ≥ 2 && (sharedFirst || sharedLast)

/-- The word that each of the variants has first, or last, if each has two
or more words. -/
def sharedWord? (variants : Array Name) (last : Bool) : Option String :=
  let ws := variants.map (words ∘ nameText)
  let pick := fun (w : List String) => if last then w.getLast? else w.head?
  match ws[0]? with
  | some w0 => if ws.any (·.length < 2) then none else
    match pick w0 with
    | some w => if ws.all (pick · == some w) then some w else none
    | none => none
  | none => none

/-- `enum_variant_names` for the enumeration `n` of `variants`, if they share
a first or a last word. -/
def enumVariantNamesMsg? (n : Name) (variants : Array Name) : Option Msg :=
  let first? := sharedWord? variants false
  let last? := sharedWord? variants true
  if !enumVariantNames variants.size first?.isSome last?.isSome then none else
  let what := match first?, last? with
    | some f, some l => s!"starts with `{f}` and ends with `{l}`"
    | some f, none => s!"starts with `{f}`"
    | none, some l => s!"ends with `{l}`"
    | none, none => ""
  let ws := first?.toList ++ last?.toList
  some { code? := some Lint.enumVariantNames.code, headline := s!"every variant of `{nameText n}` {what}"
         label? := some "its variants share a word"
         notes := #[s!"help: remove {" and ".intercalate (ws.map (s!"`{·}`"))} from each variant's name, or put it in the enumeration's"] }

/-- Whether the words `sub` are consecutive words of `ws`. -/
def containsWords (ws sub : List String) : Bool :=
  (List.range (ws.length + 1)).any fun i => (ws.drop i).take sub.length == sub

/-- Whether `enum_variant_names` fires on a variant of `nWords` words, whose
words contain the `nEnumWords` words of its enumeration's name if
`contains` (`lint::variant_has_enum_name`). -/
def variantHasEnumName (nWords nEnumWords : Nat) (contains : Bool) : Bool := contains && nWords > nEnumWords

/-- `enum_variant_names` for the variant `v` of the enumeration `n`, if it
contains the enumeration's name. -/
def variantNameMsg? (n v : Name) : Option Msg :=
  let ws := words (nameText v)
  let es := words (nameText n)
  if !variantHasEnumName ws.length es.length (containsWords ws es) then none else
  some { code? := some Lint.enumVariantNames.code
         headline := s!"variant `{nameText v}` contains the name of its enumeration `{nameText n}`"
         label? := some s!"contains `{nameText n}`"
         notes := #[s!"note: a path to it names the enumeration already, as `{nameText n}::{nameText v}` does",
           s!"help: remove `{nameText n}` from its name"] }

/-- The words of a field's name, in lower case, without its `?`. -/
def fieldWords (n : Name) : List String := (words (baseName (nameText n))).map String.toLower

/-- `struct_field_names` for the record `n` of `fields`, if they share a
first or a last word (`lint::struct_field_names`, decided as for
`enum_variant_names`). -/
def structFieldNamesMsg? (n : Name) (fields : Array Name) : Option Msg :=
  let names := fields.map fun f => Name.mkSimple ("_".intercalate (fieldWords f))
  let first? := sharedWord? names false
  let last? := sharedWord? names true
  if !enumVariantNames fields.size first?.isSome last?.isSome then none else
  let what := match first?, last? with
    | some f, some l => s!"starts with `{f}` and ends with `{l}`"
    | some f, none => s!"starts with `{f}`"
    | none, some l => s!"ends with `{l}`"
    | none, none => ""
  let ws := first?.toList ++ last?.toList
  some { code? := some Lint.structFieldNames.code, headline := s!"every field of `{nameText n}` {what}"
         label? := some "its fields share a word"
         notes := #[s!"help: remove {" and ".intercalate (ws.map (s!"`{·}`"))} from each field's name, or put it in the record's"] }

/-- `struct_field_names` for the field `f` of the record `n`, if it
contains the record's name, its words compared in lower case
(`lint::field_has_record_name`, decided as for `enum_variant_names`). -/
def fieldNameMsg? (n f : Name) : Option Msg :=
  let ws := fieldWords f
  let rs := (words (nameText n)).map String.toLower
  if !variantHasEnumName ws.length rs.length (containsWords ws rs) then none else
  let recName := "_".intercalate rs
  some { code? := some Lint.structFieldNames.code
         headline := s!"field `{nameText f}` contains the name of its record `{nameText n}`"
         label? := some s!"contains `{recName}`"
         notes := #["note: a field is read from a value of its record, which says what the field is of",
           s!"help: remove `{recName}` from its name"] }

/-- Whether `fn_params_excessive_bools` fires on a function with `nBools`
`Bool` parameters (`lint::fn_params_excessive_bools`): more than 3, as in
Clippy. -/
def fnParamsExcessiveBools (nBools : Nat) : Bool := nBools > 3

/-- The function `f`, with `n` `Bool` parameters. -/
def fnParamsExcessiveBoolsMsg (f : Name) (n : Nat) : Msg :=
  { code? := some Lint.fnParamsExcessiveBools.code, headline := s!"function `{nameText f}` has {n} `Bool` parameters"
    label? := some "more than 3 `Bool` parameters"
    notes := #[s!"note: a call such as `{nameText f}({", ".intercalate (List.replicate n "true")})` does not say which is which",
      "help: replace some of them with an enumeration, or with a record of named `Bool` fields"] }

/-- Whether `struct_excessive_bools` fires on a record with `nBools`
`Bool` fields (`lint::struct_excessive_bools`): more than 3, as in Clippy. -/
def structExcessiveBools (nBools : Nat) : Bool := nBools > 3

/-- The record `r`, with `n` `Bool` fields. -/
def structExcessiveBoolsMsg (r : Name) (n : Nat) : Msg :=
  { code? := some Lint.structExcessiveBools.code, headline := s!"record `{nameText r}` has {n} `Bool` fields"
    label? := some "more than 3 `Bool` fields"
    notes := #["note: every combination of their values is allowed, though some are probably not meant",
      "help: replace some of them with an enumeration of the combinations that are meant"] }

/-- Whether the characters have a run of three or more uppercase letters. -/
def hasUpperRun (cs : List Char) : Bool :=
  (cs.foldl (fun (run, found) c => if isUpperAscii c then (run + 1, found || run + 1 ≥ 3) else (0, found))
    ((0 : Nat), false)).2

/-- Whether `upper_case_acronyms` fires on a name of `what`
(`lint::upper_case_acronyms`): it is in `CamelCase`, as its case requires,
with a run of three or more uppercase letters. -/
def upperCaseAcronyms (what : Named) (s : String) : Bool :=
  what.case == .camel && nameInCase s .camel && hasUpperRun s.toList

/-- `cs` with each run of three or more uppercase letters in lowercase but
for its first letter, and for its last if a lowercase letter follows it,
which starts the next word: `HTTPStatus` becomes `HttpStatus`. -/
def lowerUpperRuns (cs : List Char) : List Char :=
  let rec go : List Char → List Char → List Char
    | run, [] => flush run false
    | run, c :: rest =>
      if isUpperAscii c then go (run ++ [c]) rest
      else flush run (isLowerAscii c) ++ c :: go [] rest
  termination_by _ cs => cs.length
  go [] cs
where
  /-- A run of uppercase letters, followed by a lowercase letter if `lower`. -/
  flush (run : List Char) (lower : Bool) : List Char :=
    if run.length < 3 then run else
    match run with
    | [] => []
    | c :: rest =>
      if lower then c :: (rest.dropLast.map Char.toLower ++ rest.getLast?.toList)
      else c :: rest.map Char.toLower

def upperCaseAcronymsMsg (what : Named) (s : String) : Msg :=
  let fixed := String.ofList (lowerUpperRuns s.toList)
  { code? := some Lint.upperCaseAcronyms.code, headline := s!"{what.describe} `{s}` has an acronym in upper case"
    label? := some "three or more uppercase letters in a row"
    notes := #["note: in `CamelCase`, an acronym is a word, with only its first letter in upper case"]
    fixes := #[{ msg := s!"rename it to `{fixed}`", replacement := fixed }] }

/-- Whether `just_underscores_and_digits` fires on the name `s`
(`lint::just_underscores_and_digits`): without a final `?`, it is made of
`_` and digits, and is not the wildcard `_`. -/
def justUnderscoresAndDigits (s : String) : Bool :=
  let b := baseName s
  s != "_" && !b.isEmpty && b.all fun c => c == '_' || c.isDigit

def justUnderscoresAndDigitsMsg (what : Named) (s : String) : Msg :=
  { code? := some Lint.justUnderscoresAndDigits.code
    headline := s!"{what.describe} `{s}` is named only with `_` and digits"
    label? := some "says nothing of what it is"
    notes := #["help: give it a name that says what it is"] }

/-- The names that are placeholders (`lint::disallowed_names`), in lower
case. -/
def disallowedNames : List String := ["foo", "baz", "quux"]

/-- Whether `disallowed_names` fires on the name `s`
(`lint::disallowed_names`): without a final `?`, it is a placeholder, in
any case. -/
def disallowedName (s : String) : Bool := disallowedNames.contains (baseName s).toLower

def disallowedNameMsg (what : Named) (s : String) : Msg :=
  { code? := some Lint.disallowedNames.code, headline := s!"{what.describe} `{s}` has a placeholder name"
    label? := some "a placeholder"
    notes := #["help: give it a name that says what it is"] }

/-- Whether `min_ident_chars` fires on the name `s`
(`lint::min_ident_chars`): without a final `?`, it is one character, other
than `_`. -/
def minIdentChars (s : String) : Bool :=
  let b := baseName s
  b.length == 1 && b != "_"

def minIdentCharsMsg (what : Named) (s : String) : Msg :=
  { code? := some Lint.minIdentChars.code, headline := s!"{what.describe} `{s}` has a name of one character"
    label? := some "too short to say what it is"
    notes := #["help: give it a name that says what it is"] }

/-- The lints about a declared name alone: its case
(`lint::naming_case`), and the lints of the `style` and `restriction`
groups that look only at the name. -/
def nameMsgs (what : Named) (n : Name) : Array (Lint × Msg) :=
  let s := nameText n
  (namingMsg? what n).toArray
    ++ (if upperCaseAcronyms what s then #[(.upperCaseAcronyms, upperCaseAcronymsMsg what s)] else #[])
    ++ (if justUnderscoresAndDigits s then #[(.justUnderscoresAndDigits, justUnderscoresAndDigitsMsg what s)] else #[])
    ++ (if disallowedName s then #[(.disallowedNames, disallowedNameMsg what s)] else #[])
    ++ (if minIdentChars s then #[(.minIdentChars, minIdentCharsMsg what s)] else #[])

/-- Whether a declared name of `what` is an item's, which a path from
outside its module reaches through the module's name. -/
def Named.isItem : Named → Bool
  | .module | .component | .function | .global | .enumeration | .record | .abstractType | .typeAlias | .constant => true
  | _ => false

/-- Whether `module_name_repetitions` fires on an item whose name has
`nWords` words, which contain the `nModuleWords` words of its module's last
segment if `contains` (`lint::module_name_repetitions`). -/
def moduleNameRepetitions (nWords nModuleWords : Nat) (contains : Bool) : Bool := contains && nWords > nModuleWords

/-- `module_name_repetitions` for the item `n` of `what`, declared in the
module `mod`, if its words contain those of the module's last segment, in
any case. -/
def moduleNameMsg? (what : Named) (mod n : Name) : Option Msg := do
  guard what.isItem
  let .str _ m := mod | none
  let ws := (words (nameText n)).map String.toLower
  let ms := (words m).map String.toLower
  guard (moduleNameRepetitions ws.length ms.length (containsWords ws ms))
  some { code? := some Lint.moduleNameRepetitions.code
         headline := s!"{what.describe} `{nameText n}` contains the name of its module `{showPath mod}`"
         label? := some s!"contains `{m}`"
         notes := #[s!"note: a path to it names the module already, as `{m}::{nameText n}` does",
           s!"help: remove `{m}` from its name"] }

/-! ## Names and sizes -/

/-- `a`, `b` and `c`. -/
def andList (xs : Array String) : String :=
  match xs.toList.reverse with
  | last :: rest@(_ :: _) => s!"{", ".intercalate rest.reverse} and {last}"
  | _ => ", ".intercalate xs.toList

/-- Whether a declared name has one character, not counting a final `?`. -/
def singleChar (n : Name) : Bool := (baseName (nameText n)).length == 1

/-- Whether `many_single_char_names` fires on an item that declares `n`
distinct single-character names (`lint::many_single_char_names`): more
than 4, as Clippy's threshold is. -/
def manySingleCharNames (n : Nat) : Bool := n ≥ 5

/-- The `what` named `n` declares the single-character `names`. -/
def manySingleCharNamesMsg (what : Named) (n : Name) (names : Array Name) : Msg :=
  { code? := some "F0795", headline := s!"{what.describe} `{nameText n}` declares {names.size} single-character names"
    label? := some "too many to tell apart"
    notes := #[s!"note: they are {andList (names.map (s!"`{nameText ·}`"))}",
      "help: name them for what they stand for"] }

/-- If one of `a` and `b` is the other with one character substituted,
inserted or deleted, the characters that differ, and whether one character
is substituted for another that are each a word of their names, between
`_`s or the name's ends. They differ in what is left of each once their
longest common prefix and then their longest common suffix are removed,
if neither has more than one character left, and they are not equal. -/
def oneEdit? (a b : List Char) : Option (List Char × Bool) :=
  let p := ((a.zip b).takeWhile fun (x, y) => x == y).length
  let (a', b') := (a.drop p, b.drop p)
  let s := ((a'.reverse.zip b'.reverse).takeWhile fun (x, y) => x == y).length
  let (ra, rb) := (a'.take (a'.length - s), b'.take (b'.length - s))
  let word := ra.length == 1 && rb.length == 1 && (p == 0 || a[p - 1]? == some '_')
    && (p + 1 == a.length || a[p + 1]? == some '_')
  if ra.length ≤ 1 && rb.length ≤ 1 && !(ra.isEmpty && rb.isEmpty) then some (ra ++ rb, word) else none

/-- Whether `similar_names` fires on two names of `lenA` and `lenB`
characters, without a final `?`, one of which is the other with one
character substituted, inserted or deleted if `oneEdit`, where the
characters that differ are digits if `digits`, and words of their own if
`word`, and the pair is one of `similarAllowed` if `allowed`
(`lint::similar_names`). -/
def similarNames (lenA lenB : Nat) (oneEdit digits word allowed : Bool) : Bool :=
  lenA ≥ 3 && lenB ≥ 3 && oneEdit && !digits && !word && !allowed

/-- The pairs of names that Clippy allows to be similar, of those that
apply to Fren. -/
def similarAllowed : List (String × String) := [
  -- keep-sorted start
  ("args", "arms"),
  ("lhs", "rhs"),
  ("lit", "lint"),
  ("set", "get"),
  -- keep-sorted end
]

/-- `similarNames` of two declared names. -/
def namesSimilar (a b : Name) : Bool :=
  let (a, b) := (baseName (nameText a), baseName (nameText b))
  let d? := oneEdit? a.toList b.toList
  let allowed := similarAllowed.any fun (x, y) => (a == x && b == y) || (a == y && b == x)
  similarNames a.length b.length d?.isSome (d?.any (·.1.all Char.isDigit)) (d?.any (·.2)) allowed

/-- `b`, declared after `a` in the `what` named `n`. -/
def similarNamesMsg (a b : Name) (what : Named) (n : Name) : Msg :=
  { code? := some "F0796", headline := s!"`{nameText b}` differs from `{nameText a}` by one character"
    label? := some "easily mistaken for the other"
    notes := #[s!"note: both are declared in {what.describe} `{nameText n}`",
      "help: rename one, so that they differ at a glance"] }

/-- The lines of the text of `cs` from `start` up to `stop`, read in place,
that have something other than whitespace and comments: `--` to the end
of the line, and `/-` to `-/`, which nest. A `--` in a string literal
starts no comment. -/
def codeLinesIn (cs : Array Char) (start stop : Nat) : Nat :=
  go (min stop cs.size) start 0 false 0 false
where
  /-- The index of the first line break at or after `i`, or `stop`. -/
  lineEnd (stop i : Nat) : Nat :=
    if h : i < stop then if cs[i]! == '\n' then i else lineEnd stop (i + 1) else i
  termination_by stop - i
  /-- From `i`, with `n` lines counted, `code` if the current line has
  code, in `depth` nested comments, and `inString` if in a string literal.
  A loop of its own, so that its state is not boxed at each character. -/
  go (stop i n : Nat) (code : Bool) (depth : Nat) (inString : Bool) : Nat :=
    if h : i < stop then
      let c := cs[i]!
      let next := if i + 1 < stop then cs[i + 1]? else none
      if c == '\n' then go stop (i + 1) (if code then n + 1 else n) false depth false
      else if depth > 0 then
        if c == '-' && next == some '/' then go stop (i + 2) n code (depth - 1) inString
        else if c == '/' && next == some '-' then go stop (i + 2) n code (depth + 1) inString
        else go stop (i + 1) n code depth inString
      else if inString then
        if c == '\\' then go stop (i + 2) n code depth inString
        else go stop (i + 1) n code depth (c != '"')
      -- `c` is no line break, so the line's end is past `i`.
      else if c == '-' && next == some '-' then go stop (max (lineEnd stop i) (i + 1)) n code depth inString
      else if c == '/' && next == some '-' then go stop (i + 2) n code 1 inString
      else go stop (i + 1) n (code || !c.isWhitespace) depth (c == '"')
    else if code then n + 1 else n
  termination_by stop - i

/-- `codeLinesIn` of all of `text`. -/
def codeLines (text : String) : Nat :=
  let cs := text.toList.toArray
  codeLinesIn cs 0 cs.size

/-- Whether `too_many_lines` fires on an item of `n` lines of code
(`lint::too_many_lines`). -/
def tooManyLines (n : Nat) : Bool := n > 100

/-- The `what` named `n`, of `lines` lines of code. -/
def tooManyLinesMsg (what : Named) (n : Name) (lines : Nat) : Msg :=
  { code? := some "F0797", headline := s!"{what.describe} `{nameText n}` has {lines} lines"
    label? := some "longer than 100 lines"
    notes := #["note: blank lines and comments are not counted",
      if what == .function then "help: move parts of it into smaller functions, and apply them"
      else "help: move parts of it into smaller procedures, and call them"] }

end Fren.Core
