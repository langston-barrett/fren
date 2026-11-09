import Heavy.Process

/-! Selected-module policy and raw application checks; no Fren or OS imports.
The IO caller supplies canonical source paths and raw kernel readbacks. -/
namespace Heavy.ModuleMemory

def defaultBytes : Nat := 1073741824

/-- Ordinary direct compilation excludes query, stdin and program execution.
Consume known option operands first, so an output named --run cannot bypass it.
After a genuine -- terminator, every remaining argument is a literal operand.
Unknown syntax remains eligible for the observer's fail-closed source check. -/
def directFile : List String → Bool
  | [] => true
  | arg :: rest =>
    if Heavy.Process.valueFlag arg then
      match rest with | [] => true | _ :: tail => directFile tail
    else if arg == "--" then true
    else if arg == "--run" || arg == "-r" || arg == "--stdin" || Heavy.Process.queryFlag arg then false
    else directFile rest

def inRoot (root source owner : String) : Bool :=
  source == root ++ "/" ++ owner ++ ".lean" || (root ++ "/" ++ owner ++ "/").toList.isPrefixOf source.toList

def selected (root source : String) : Bool :=
  ("/".toList.isPrefixOf root.toList) && root != "/" && (
    inRoot root source "FrenBase" ||
    inRoot root source "FrenSource" ||
    inRoot root source "FrenDiag" ||
    inRoot root source "FrenSexp" ||
    inRoot root source "FrenProp" ||
    inRoot root source "FrenAst" ||
    inRoot root source "FrenModule" ||
    inRoot root source "FrenExpr" ||
    inRoot root source "FrenMir" ||
    inRoot root source "FrenLir" ||
    inRoot root source "FrenOir" ||
    inRoot root source "FrenParse" ||
    inRoot root source "FrenAstToHir" ||
    inRoot root source "FrenHirToThir" ||
    inRoot root source "FrenThirDesugar" ||
    inRoot root source "FrenThirToMir" ||
    inRoot root source "FrenMirToMono" ||
    inRoot root source "FrenMonoToFo" ||
    inRoot root source "FrenFoToFlat" ||
    inRoot root source "FrenMirToLean" ||
    inRoot root source "FrenFlatToLir" ||
    inRoot root source "FrenLirToOir" ||
    inRoot root source "FrenOirToSmt" ||
    inRoot root source "FrenEval" ||
    inRoot root source "FrenLirEval" ||
    inRoot root source "FrenGen" ||
    inRoot root source "FrenCli2" ||
    inRoot root source "FrenHosted2" ||
    inRoot root source "FrenBaseTests" ||
    inRoot root source "FrenSourceTests" ||
    inRoot root source "FrenDiagTests" ||
    inRoot root source "FrenSexpTests" ||
    inRoot root source "FrenPropTests" ||
    inRoot root source "FrenAstTests" ||
    inRoot root source "FrenModuleTests" ||
    inRoot root source "FrenExprTests" ||
    inRoot root source "FrenMirTests" ||
    inRoot root source "FrenLirTests" ||
    inRoot root source "FrenOirTests" ||
    inRoot root source "FrenParseTests" ||
    inRoot root source "FrenAstToHirTests" ||
    inRoot root source "FrenHirToThirTests" ||
    inRoot root source "FrenThirDesugarTests" ||
    inRoot root source "FrenThirToMirTests" ||
    inRoot root source "FrenMirToMonoTests" ||
    inRoot root source "FrenMonoToFoTests" ||
    inRoot root source "FrenFoToFlatTests" ||
    inRoot root source "FrenMirToLeanTests" ||
    inRoot root source "FrenFlatToLirTests" ||
    inRoot root source "FrenLirToOirTests" ||
    inRoot root source "FrenOirToSmtTests" ||
    inRoot root source "FrenEvalTests" ||
    inRoot root source "FrenLirEvalTests" ||
    inRoot root source "FrenGenTests" ||
    inRoot root source "FrenCli2Tests" ||
    inRoot root source "FrenHosted2Tests" ||
    inRoot root source "FrenTextTests" ||
    inRoot root source "FrenTextTestsTests" ||
    inRoot root source "FrenTextDemo" ||
    inRoot root source "FrenTextDemoTests" ||
    inRoot root source "Fren2TestMain" ||
    inRoot root source "FrenTest/Layering" ||
    inRoot root source "FrenTest/Fren2Resolver" ||
    inRoot root source "FrenTest/Fren2Typing" ||
    inRoot root source "FrenTest/Fren2Mir" ||
    inRoot root source "FrenTest/Fren2Lir")

/-- Scan every canonical argv candidate. Its raw spelling/extension never
excludes a resolved selected source; later selected candidates take precedence.
The IO caller resolves every raw argument before invoking this function. -/
def ambiguousSource (root : String) : List String → String → String
  | [], source => source
  | canonical :: rest, source =>
    ambiguousSource root rest (if selected root canonical then canonical else source)

def limit (root source kind : String) (configured : Nat) : Option Nat :=
  if kind == "query" || kind == "stdin" then some 0
  else if selected root source then
    if kind != "file" || configured == 0 || configured > 2^50 then none else some configured
  else some 0

def effective : List Nat → Nat → Nat
  | [], requested => requested
  | value :: rest, requested => effective rest (if value > 0 && value < requested then value else requested)

def applied (error requested readback swap expectedPid observedPid expectedInode observedInode : Nat)
    (limits : List Nat) : Option (Nat × Nat) :=
  if error == 0 && requested > 0 && requested ≤ 2^50 && readback == requested && swap == 0 &&
      expectedPid > 0 && expectedPid == observedPid && expectedInode > 0 && expectedInode == observedInode
  then some (requested, effective limits requested) else none

end Heavy.ModuleMemory
