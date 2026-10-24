/-! # When the `fren` command colours its output (`cli::color`) -/

namespace FrenCli

/-- `--color WHEN`. -/
inductive ColorChoice where
  | auto
  | always
  | never
  deriving BEq, DecidableEq, Repr

def ColorChoice.ofString? : String → Option ColorChoice
  | "auto" => some .auto
  | "always" => some .always
  | "never" => some .never
  | _ => none

/-- Whether to colour output written to a stream, given whether the stream
is a terminal, whether `NO_COLOR` is set (and not empty), and whether
`TERM` is `dumb`. -/
def useColor (choice : ColorChoice) (tty noColor dumb : Bool) : Bool :=
  match choice with
  | .always => true
  | .never => false
  | .auto => tty && !noColor && !dumb

end FrenCli
