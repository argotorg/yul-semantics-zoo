import YulSemnaticsZoo
import Tests
import Fuzz.Asm
import Fuzz.Yul

/-!
# `lake test [-- cases [seed]]`

The proofs in `YulSemnaticsZoo` and the tests in `Tests` are checked when this file builds. Then
the fuzzers `Fuzz.fuzz` (EVM encoding) and `Fuzz.Yul.fuzz` (Yul parser) run; `solc` must be on
the path.
-/

def main (args : List String) : IO UInt32 := do
  let asm ← Fuzz.fuzz args
  let yul ← Fuzz.Yul.fuzz args
  return max asm yul
