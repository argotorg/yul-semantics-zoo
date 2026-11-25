import YulSemnaticsZoo
import Tests
import Fuzz.Asm
import Fuzz.Yul
import Fuzz.Clocked

/-!
# `lake test [-- cases [seed]]`

The proofs in `YulSemnaticsZoo` and the tests in `Tests` are checked when this file builds. Then
the fuzzers `Fuzz.fuzz` (EVM encoding), `Fuzz.Yul.fuzz` (Yul parser) and `Fuzz.Clocked.fuzz`
(clocked Yul semantics) run; `solc` and `evm` (geth) must be on the path.
-/

def main (args : List String) : IO UInt32 := do
  let asm ← Fuzz.fuzz args
  let yul ← Fuzz.Yul.fuzz args
  let clocked ← Fuzz.Clocked.fuzz args
  return max asm (max yul clocked)
