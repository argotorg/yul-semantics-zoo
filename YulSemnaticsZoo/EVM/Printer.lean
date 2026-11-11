import YulSemnaticsZoo.EVM.Syntax

/-!
# EVM: printer

Text for bytes and instructions. An instruction prints as in `solc --opcodes`.
-/

namespace EVM

/-- lower case hex digits, without leading zeros -/
def hexDigits (k : Nat) : String := String.ofList (Nat.toDigits 16 k)

/-- two lower case hex digits for each byte -/
def hex (bytes : List UInt8) : String :=
  String.join (bytes.map fun b => if b < 16 then "0" ++ hexDigits b.toNat else hexDigits b.toNat)

/-- the value of big-endian bytes -/
def natOfBytes (bytes : List UInt8) : Nat := bytes.foldl (fun v b => 256 * v + b.toNat) 0

namespace Instr

def name : Instr → String
  | Stop => "STOP"
  | Add => "ADD"
  | Eq => "EQ"
  | Codecopy => "CODECOPY"
  | Extcodecopy => "EXTCODECOPY"
  | Pop => "POP"
  | Mload => "MLOAD"
  | Mstore => "MSTORE"
  | Jump => "JUMP"
  | Jumpi => "JUMPI"
  | Gas => "GAS"
  | Jumpdest => "JUMPDEST"
  | Push n _ => s!"PUSH{n}"
  | Dup n _ => s!"DUP{n}"
  | Swap n _ => s!"SWAP{n}"
  | Create => "CREATE"
  | Call => "CALL"
  | Return => "RETURN"

/-- the name, and for a push its value in upper case hex -/
def mnemonic : Instr → String
  | Push 0 _ => "PUSH0"
  | Push n imm => s!"PUSH{n} 0x{(hexDigits (natOfBytes imm.toList)).toUpper}"
  | i => i.name

end Instr

end EVM
