import YulSemnaticsZoo.EVM.Printer

/-!
# Fuzzing the EVM encoding against solc

`solc --import-asm-json --bin --opcodes` assembles a list of instructions, and prints the
bytes and its disassembly of the bytes. This module makes the input for solc and checks its
output against `EVM.Instr.encode` and `EVM.decode`.
-/

namespace Fuzz
open EVM Instr

/-- The asm JSON of `instrs` followed by the bytes `data`. solc picks the width of each push,
so each push in `instrs` must have its minimal width. -/
def asmJson (instrs : List Instr) (data : List UInt8) : String :=
  let item (k : Nat) : Instr → List String
    | .Push _ imm => [s!"\{\"name\":\"PUSH\",\"value\":\"{hexDigits (natOfBytes imm.toList)}\"}"]
    | .Jumpdest => [s!"\{\"name\":\"tag\",\"value\":\"{k}\"}", "{\"name\":\"JUMPDEST\"}"]
    | i => [s!"\{\"name\":\"{i.name}\"}"]
  let tags := instrs.foldl (fun (k, items) i =>
    (if i == .Jumpdest then k + 1 else k, items ++ item (k + 1) i)) (0, [])
  let verbatim :=
    if data.isEmpty then [] else [s!"\{\"name\":\"VERBATIM\",\"value\":\"{hex data}\"}"]
  "{\".code\":[" ++ ",".intercalate (tags.2 ++ verbatim) ++ "],\"sourceList\":[]}"

/-- the names of the instructions in the tiny EVM -/
def names : List String :=
  ["STOP", "ADD", "EQ", "CODECOPY", "EXTCODECOPY", "POP", "MLOAD", "MSTORE", "JUMP", "JUMPI",
   "GAS", "JUMPDEST", "CREATE", "CALL", "RETURN"]
  ++ (List.range 33).map (s!"PUSH{·}")
  ++ (List.range 16).map (s!"DUP{· + 1}") ++ (List.range 16).map (s!"SWAP{· + 1}")

/-- `instrs` agrees with the disassembly `solc` that solc prints: each instruction has the same
text, and where `instrs` has no instruction, solc prints a name that is not in the tiny EVM -/
def agrees (instrs : List (Option Instr)) (solc : String) : Bool :=
  go instrs ((solc.splitOn " ").filter (· ≠ ""))
where
  go : List (Option Instr) → List String → Bool
    | [], ts => ts.isEmpty
    | some i :: is, ts =>
      let m := (mnemonic i).splitOn " "
      m.isPrefixOf ts && go is (ts.drop m.length)
    | none :: is, t :: ts => !names.contains t && go is ts
    | none :: _, [] => false

/-- The bytes that the disassembler of solc 0.8.33 reads with an immediate also in legacy
code: the EOF instructions `DATALOADN`, `RJUMP`, `RJUMPI`, `CALLF`, `JUMPF`, `DUPN`, `SWAPN`,
`EOFCREATE`, `RETURNCONTRACT`. The fuzzer does not give them to solc. In legacy code these
bytes are not defined, and `Tests/Fuzz.lean` checks that they decode to `none`. -/
def eofImmediate : List Nat := [0xd1, 0xe0, 0xe1, 0xe3, 0xe5, 0xe6, 0xe7, 0xec, 0xee]

end Fuzz
