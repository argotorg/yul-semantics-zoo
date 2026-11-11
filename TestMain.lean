import YulSemnaticsZoo
import Tests
import Fuzz.Asm

/-!
# `lake test [-- cases [seed]]`

The proofs in `YulSemnaticsZoo` and the tests in `Tests` are checked when this file builds. Then
the fuzzer `Fuzz.fuzz` runs; `solc` must be on the path.
-/

def main (args : List String) : IO UInt32 := Fuzz.fuzz args
