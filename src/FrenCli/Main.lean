-- keep-sorted start
import FrenCli.Run
-- keep-sorted end

/-! # `fren`: check `.fren` files and report their traceability -/

def main (args : List String) : IO UInt32 := FrenCli.run args
