/-!
# Markdown specs

A Markdown file is a spec whose Fren code is in ```` ```fren ```` fenced
blocks. Both front ends read it as the code with everything else blanked
out: each line outside a block becomes empty, and code lines are kept as
they are, so line and column numbers are those of the Markdown file.

A fence is a line that starts with ```` ``` ````, after up to three spaces.
A block opens at ```` ```fren ```` and closes at the next fence with no
info string. Other
blocks (```` ```lean ````, plain ```` ``` ````) are prose.
-/

namespace Fren.Core

def isMarkdownFile (path : String) : Bool := path.endsWith ".md"

/-- The fence's info string, if `line` is a fence. -/
def fenceInfo? (line : String) : Option String :=
  let rest := line.trimAsciiStart.toString
  if line.length - rest.length ≤ 3 && rest.startsWith "```" then
    some (rest.drop 3).trimAscii.toString
  else none

/-- The Fren code of a Markdown spec, with everything else blanked out. -/
def unwrapMarkdown (src : String) : String := Id.run do
  let mut out := #[]
  -- `none` outside a block; `some true` inside a Fren block
  let mut block : Option Bool := none
  for line in src.splitOn "\n" do
    match block, fenceInfo? line with
    | none, some info => block := some (info == "fren"); out := out.push ""
    | some _, some "" => block := none; out := out.push ""
    | some true, _ => out := out.push line
    | _, _ => out := out.push ""
  return "\n".intercalate out.toList

end Fren.Core
