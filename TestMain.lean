import YulSemnaticsZoo
import Tests
import Fuzz.Asm
import Fuzz.Yul
import Fuzz.Geth
import Fuzz.Clocked

/-!
# `lake test [-- cases [seed]]`

The proofs in `YulSemnaticsZoo` and the tests in `Tests` are checked when this file builds. Then
the fuzzers `Fuzz.fuzz` (EVM encoding), `Fuzz.Yul.fuzz` (Yul parser), `Fuzz.Geth.fuzz` (EVM
semantics and gas) and `Fuzz.Clocked.fuzz` (clocked Yul semantics) run; `solc` and `evm` (of geth)
must be on the path.
-/

def main (args : List String) : IO UInt32 := do
  let asm ← Fuzz.fuzz args
  let yul ← Fuzz.Yul.fuzz args
  let geth ← Fuzz.Geth.fuzz args
  let clocked ← Fuzz.Clocked.fuzz args
  return max (max asm yul) (max geth clocked)
