-- keep-sorted start
import FrenCore.Diagnostic
import FrenCore.Global
-- keep-sorted end

/-!
# Procedures

A procedure (`Reqs/Lang/Procedures`) declares its inputs as parameters and
its public outputs as named results, and its other members in its block.
A call gives an argument for each of the called procedure's parameters,
in order (`call::arguments`).
-/

namespace Fren.Core

/-! ## A call's arguments -/

/-- Whether a call gives each parameter of the called procedure an argument
(`call::Arity`). -/
inductive CallArity where
  | fits
  | tooMany
  | tooFew
  deriving Inhabited, DecidableEq, Repr

/-- Whether a call with `nArgs` arguments gives each of `nParams` parameters
one (`call::arguments`). -/
def callArity (nParams nArgs : Nat) : CallArity :=
  if nArgs == nParams then .fits else if nArgs > nParams then .tooMany else .tooFew

/-- What a call binds, if its arguments fit the called procedure's
parameters `params`: each parameter to the argument in its position
(`call::arguments`). Both front ends and the evaluator bind a call's
arguments so. -/
def callBindings {α : Type} (params : Array String) (args : Array α) : Option (Array (String × α)) :=
  if callArity params.size args.size == .fits then some (params.zip args) else none

/-! ## Messages -/

/-- A parameter declared with the modifier `mod`, `pub` or `det` (`F0110`),
whose fix removes it at `fix?`. -/
def paramModifierMsg (mod : String) (fix? : Option Range := none) : Msg :=
  { code? := some "F0110", headline := s!"parameters cannot be declared `{mod}`"
    label? := some "not allowed on a parameter"
    notes := #["note: a parameter is an input: the environment chooses it, sees it, and determines it"]
    fixes := #[{ msg := s!"remove `{mod}`", replacement := "", range? := fix? }] }

/-- A result defined by more than one `out` member (`F0421`). -/
def resultDefinedTwiceMsg (r : String) : Msg :=
  { code? := some "F0421", headline := s!"result `{r}` is defined more than once"
    label? := some "defined again here"
    notes := #["note: a result is defined by one `out` member at most, or is chosen by the system"] }

/-- A call with `given` arguments, of a procedure with `params`
(`F0408`, `F0409`). -/
def callArityMsg (callee : String) (params : Array String) (given : Nat) : Msg :=
  let n := params.size
  let takes := if n == 0 then "takes no arguments"
    else s!"takes {n} argument{if n == 1 then "" else "s"}, {", ".intercalate (params.toList.map fun p => s!"`{p}`")}"
  if given > n then
    { code? := some "F0408", headline := s!"too many arguments: `{callee}` {takes}"
      label? := some s!"{given} arguments", notes := #["note: a call gives one argument for each parameter, in order"] }
  else
    let missing := params.extract given n
    { code? := some "F0409", headline := s!"too few arguments: `{callee}` {takes}"
      label? := some s!"{given} argument{if given == 1 then "" else "s"}"
      notes := #["note: a call gives one argument for each parameter, in order",
        s!"help: add {", ".intercalate (missing.toList.map fun p => s!"`{p}`")}"] }

/-! ## The order of a block's errors -/

/-- A kind of static error of the syntax of one part of a block, a result
or a member, in the order that the part is read (`lang::BlockCheck`): a
modifier that the part does not take (`det`, or an evidence setting, on a
function's result), before the part is read; an error of the part's own
syntax, as it is read, among them a clause without a label that is not a
Boolean block (`clauseSyntaxError?`); and that the block does not take the
part (`F0442`, `F0443`, `F0444`, `F0445`, a second definition of a result,
`refines`), once the part is read. -/
inductive BlockCheck where
  | modifier
  | syntax
  | rejected
  deriving Inhabited, BEq, DecidableEq, Repr

/-- The kinds of `BlockCheck`, in the order they are reported. -/
def BlockCheck.inOrder : List BlockCheck := [.modifier, .syntax, .rejected]

/-- The error that both front ends report of one part of a block, of the
errors `errs` that they found in it, each with its kind
(`lang::part_error`): one of the earliest kind, the first of those. -/
def firstPartError? {α : Type} (errs : List (BlockCheck × α)) : Option α :=
  BlockCheck.inOrder.findSome? fun c => (errs.find? (·.1 == c)).map (·.2)

/-- The error that both front ends report of a block's syntax, whose parts,
in source order, have the errors `parts` (`lang::block_errors`): the first
part's that has one. -/
def firstBlockError? {α : Type} (parts : List (List (BlockCheck × α))) : Option α :=
  parts.findSome? firstPartError?

/-- The error that both front ends report of an item (`lang::item_error`):
the first static error of its syntax, `parse`, if it has one, which a
grammar error anywhere in the item is; else the first error of a clause's
keyword, of `keywords` in source order (`clauseKeywordError?`). So a
keyword error is reported only once the whole item is read, as the other
members that a block does not accept are. -/
def firstItemError? {α : Type} (parse : Option α) (keywords : List α) : Option α :=
  parse <|> keywords.head?

/-- The keyword that starts a clause of a block (`lang::ClauseWord`). -/
inductive ClauseWord where
  | require
  | assume
  | ensure
  | expect
  | cover
  deriving Inhabited, BEq, DecidableEq, Repr

/-- The keyword, as written. -/
def ClauseWord.text : ClauseWord → String
  | .require => "require" | .assume => "assume" | .ensure => "ensure" | .expect => "expect" | .cover => "cover"

/-- The keyword, if it starts a precondition or an assumption. -/
def ClauseWord.precondition? : ClauseWord → Option PreconditionWord
  | .require => some .require
  | .assume => some .assume
  | _ => none

/-- How a clause is written after its keyword, once it is read
(`lang::clause_errors`): with a label, `kw n: e`, or without one, and
whether its expression is a Boolean block, under any leading `when`,
`unless` or `let`. -/
structure ClauseForm where
  labelled : Bool
  blockRoot : Bool
  deriving Inhabited, BEq, Repr

/-- Whether a clause that starts with `word`, read as `form?`, has no label
but is not a Boolean block, or is a `cover` without a label: `false` where
it is not read. -/
def ClauseWord.bare (word : ClauseWord) : Option ClauseForm → Bool
  | some f => !f.labelled && (word matches .cover || !f.blockRoot)
  | none => false

/-- An unlabelled clause whose expression is not a Boolean block, or an
unlabelled `cover` (`lang::clause_errors`), an error of its own syntax. -/
def bareClauseMsg (kw : String) : Msg :=
  { code? := some "F0104", headline := "expected a named clause or a Boolean block"
    label? := some "expected a named clause or a Boolean block"
    notes := #[s!"note: a clause without a name is a Boolean block, as in `{kw} and \{ a: p, b: q }`; \
      one condition takes a name, as in `{kw} a: p`"] }

/-- The error of a clause's keyword (`lang::clause_errors`), in a global
expectation's block if `global`, reported at the keyword: that the block
writes its preconditions with the other keyword (`preconditionReport?`:
`F0169` for `assume` in a procedure's or a function's block, `F0417` for
`require` in a global expectation's). It is reported only once the item is
read (`firstItemError?`). -/
def clauseKeywordError? (global : Bool) (word : ClauseWord) : Option Msg :=
  word.precondition?.bind (preconditionReport? global)

/-- The error of how a clause is written, once it is read as `form?`
(`lang::clause_errors`): that it has no label but is not a Boolean block
(`bareClauseMsg`), an error of its own syntax (`BlockCheck.syntax`). -/
def clauseSyntaxError? (word : ClauseWord) (form? : Option ClauseForm) : Option Msg :=
  if word.bare form? then some (bareClauseMsg word.text) else none

/-- The clauses of an item, as both front ends read its structure
(`lang::ItemShape`): none; a clause that starts with `word`, in a global
expectation's block if `global`, reported at `at_`, then the rest; or a
member's own shape, then the rest. Every clause of every block of the item
is in it, at any depth: a procedure's, a function's and a global
expectation's members, and a trait's members, a method's, a procedure's
or an expectation's, those that the trait does not take included, and
those of an item under a `set_option ... in`. -/
inductive ItemShape (α : Type) where
  | done
  | clause (word : ClauseWord) (global : Bool) (at_ : α) (rest : ItemShape α)
  | member (shape rest : ItemShape α)
  deriving Inhabited

/-- The shape of clauses in sequence, with no members. -/
def ItemShape.ofList {α : Type} : List (ClauseWord × Bool × α) → ItemShape α
  | [] => .done
  | (w, g, a) :: rest => .clause w g a (ofList rest)

/-- The shape of members in sequence. -/
def ItemShape.members {α : Type} : List (ItemShape α) → ItemShape α
  | [] => .done
  | m :: rest => .member m (members rest)

/-- The errors of the keywords of every clause of an item of the shape
`s`, in source order, each with where it is reported (`lang::item_error`,
`clauseKeywordError?`). -/
def ItemShape.keywordErrors {α : Type} : ItemShape α → List (Msg × α)
  | .done => []
  | .clause w g a rest => ((clauseKeywordError? g w).map (·, a)).toList ++ rest.keywordErrors
  | .member m rest => m.keywordErrors ++ rest.keywordErrors

/-- The error that both front ends report of an item whose first error of
its syntax, if any, is `parse`, and whose clauses have the shape `s`
(`lang::item_error`): that one, else the first error of a clause's
keyword, as `report` reports it. -/
def itemError? {α β : Type} (parse : Option β) (s : ItemShape α) (report : Msg → α → β) : Option β :=
  firstItemError? parse (s.keywordErrors.map fun (msg, a) => report msg a)

end Fren.Core
