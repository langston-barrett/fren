-- keep-sorted start
import Std.Sync.Mutex
import cvc5
-- keep-sorted end

/-!
# cvc5's functions, with borrowed arguments

lean-cvc5 declares the arguments of its functions as owned, so a call is
handed a reference that it must release, but its C functions only read
their arguments and never release them. So every object passed to one of
them was kept until the process ended, a solver with all that it holds:
about 1.5 MB a query, and 9.5 GB for `fren check` of Fren's own
requirements. These declarations bind the same C functions with their
arguments borrowed, as the C functions treat them, so that each object is
freed once Fren drops it.

cvc5's objects point to those they are made from without keeping them
alive: a solver to its term manager, a parser to its solver. So each is
made in a function of its own, which borrows the object it is made from
and drops what it made before it returns: `FrenCli.solveScript` makes the
term manager, `FrenCli.solveWith` the solver, and `FrenCli.solveOn` the
parser, the symbol manager and the terms, which are therefore freed in the
reverse order.

A command is never freed: lean-cvc5's finalizer of a command deletes it as
a `Grammar` (`command_finalize`), which crashes. So the functions that
take a command take it as owned, as lean-cvc5 declares them.

cvc5's solvers also share one object across threads: libpoly's default
variable database, whose reference count is not atomic. A solver of a
logic with nonlinear arithmetic, such as `ALL`, takes a reference when it
initializes its theories, at its first assertion or definition, and drops
it when it is freed. Solvers that are never freed only ever add to the
count, but once they are, two threads that change it at once can lose a
change, and the database is then freed while it is in use. So a solver of
such a logic (`sharesLibpoly`) initializes and is freed while it holds
`solverLock` (`exclusively`): every command up to and including the first
that `initializes` lists, or its `checkSat` too if no command did. So a
command that initializes the solver without being on that list still
holds the lock, and the list only decides when the lock is let go: the
declarations before the first assertion, which are cheap, are the only
ones that wait for it. Solvers parse and solve in parallel,
and those of a linear logic, such as `QF_UFDTLIA`, take no lock. A
solver that never initializes, such as `version`'s, takes no reference.

That `checkSat` and `getValue` need no lock rests on what cvc5 1.3.2 was
observed to do, not on anything that cvc5 promises: in a nonlinear logic
whose integers are used, such as `ALL`, cvc5 turns its coverings solver
(`nl-cov`) off, and nothing else in solving creates libpoly's variables.
A query over the reals, setting `nl-cov`, or another cvc5 could make
solving use libpoly too, and then `checkSat` would need the lock, or a
solver of its own process.

The Lean front end's solvers, which lean-smt makes, are never freed, and
take no lock: they only ever take a reference. `fren_test` runs both
front ends in one process, one after the other (`uiTests`), never at
once. If they ran at once, a binary solver's free under the lock could
race with a hosted solver's unlocked initialization while the count was
1, and free the database. So freeing lean-smt's solvers too, to fix its
leak, needs them to take `solverLock` as these do.
-/

namespace FrenCli.Cvc5

open cvc5

/-- Held while a solver initializes its theories or is freed. -/
initialize solverLock : Std.BaseMutex ← Std.BaseMutex.new

/-- `act`, if `shared`, while no other solver initializes its theories or
is freed; otherwise `act` alone. -/
def exclusively (shared : Bool) (act : Env α) : Env α := if !shared then act else ExceptT.mk do
  Std.BaseMutex.lock solverLock
  let r ← act.run
  Std.BaseMutex.unlock solverLock
  return r

/-- The logic that `script` sets: the symbol after its first
`(set-logic `, or `ALL`, which shares libpoly's state, if it sets none. -/
def scriptLogic (script : String) : String :=
  match script.splitOn "(set-logic " with
  | _ :: rest :: _ => (rest.takeWhile (fun c => c != ')' && !c.isWhitespace)).toString
  | _ => "ALL"

/-- Whether a solver of the SMT-LIB logic `logic` has nonlinear
arithmetic, and so takes a reference to libpoly's state: `ALL` and the
`*_ALL` logics, and those of nonlinear integer or real arithmetic. -/
def sharesLibpoly (logic : String) : Bool :=
  logic == "ALL" || logic.endsWith "_ALL" || logic.contains "NIA" || logic.contains "NRA" || logic.contains "NIRA"

#guard scriptLogic "(set-logic QF_UFDTLIA)\n(set-option :produce-models true)\n" == "QF_UFDTLIA"
#guard scriptLogic "(declare-const x Int)\n" == "ALL"
#guard sharesLibpoly "ALL" && sharesLibpoly "HO_ALL" && sharesLibpoly "QF_NIA" && sharesLibpoly "QF_UFNRA"
#guard !sharesLibpoly "QF_UFDTLIA" && !sharesLibpoly "UFDTLIA" && !sharesLibpoly "QF_LIA"

/-- Whether the command named `name` may initialize its solver's theories:
an assertion or a definition does, by cvc5's `SolverEngine::beginCall`. -/
def initializes (name : String) : Bool :=
  name == "assert" || name == "define-fun" || name == "define-fun-rec"

@[extern "solver_new"]
opaque solverNew (tm : @& TermManager) : Env Solver

@[extern "solver_setOption"]
opaque setOption (solver : @& Solver) (option value : @& String) : Env Unit

@[extern "solver_getVersion"]
opaque getVersion (solver : @& Solver) : Env String

@[extern "solver_checkSat"]
opaque checkSat (solver : @& Solver) : Env Result

@[extern "solver_getValue"]
opaque getValue (solver : @& Solver) (term : @& Term) : Env Term

@[extern "inputParser_ofSolver"]
opaque parserNew (solver : @& Solver) : Env InputParser

@[extern "inputParser_getSymbolManager"]
opaque getSymbolManager (parser : @& InputParser) : Env SymbolManager

@[extern "inputParser_setStringInput"]
opaque setStringInput (parser : @& InputParser) (input : @& String) (lang : InputLanguage) (name : @& String) : Env Unit

@[extern "inputParser_nextCommand"]
opaque nextCommand (parser : @& InputParser) : Env Command

@[extern "inputParser_nextTerm"]
opaque nextTerm (parser : @& InputParser) : Env Term

/- A command is never freed (see above): these take it as owned. -/

@[extern "command_isNull"]
opaque isNull (cmd : Command) : Bool

@[extern "command_getCommandName"]
opaque commandName (cmd : Command) : String

@[extern "command_invoke"]
opaque invoke (cmd : Command) (solver : @& Solver) (sm : @& SymbolManager) : Env String

@[extern "symbolManager_getDeclaredTerms"]
opaque getDeclaredTerms (sm : @& SymbolManager) : Env (Array Term)

@[extern "result_isSat"]
opaque isSat (r : @& Result) : Bool

@[extern "result_isUnknown"]
opaque isUnknown (r : @& Result) : Bool

@[extern "result_isUnsat"]
opaque isUnsat (r : @& Result) : Bool

@[extern "result_getUnknownExplanation"]
opaque unknownExplanation (r : @& Result) : UnknownExplanation

@[extern "term_toString"]
opaque termText (t : @& Term) : String

/-- cvc5's version, from a solver of the term manager `tm`, which it frees
before it returns. -/
@[noinline] def versionWith (tm : @& TermManager) : Env String := do
  getVersion (← solverNew tm)

/-- cvc5's version, as its solver reports it. -/
def version : Env String := do
  versionWith (← TermManager.new)

end FrenCli.Cvc5
