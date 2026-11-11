/-!
# Tiny EVM: syntax

EVM code is a list of bytes. Code can read code (`CODECOPY`, `EXTCODECOPY`) and create
code (`CREATE`), so programs are bytes, not `Instr`s. `Instr` is an instruction decoded from
those bytes.

The instructions are a subset of the real EVM instructions, with the same opcode bytes and
stack arguments, so a program of the tiny EVM is a program of the real EVM. There is no
ether and no calldata: each balance is 0, and no instruction reads calldata, but `CALL` and
`CREATE` take the `value` and calldata arguments of the real EVM.
-/

namespace EVM

inductive Instr where
  | Stop
  | Add
  | Eq
  | Codecopy
  | Extcodecopy
  | Pop
  | Mload
  | Mstore
  | Jump
  | Jumpi
  | Gas
  | Jumpdest
  /-- `PUSHn`, with its immediate of `n` bytes in big-endian order -/
  | Push (n : Fin 33) (imm : Vector UInt8 n)
  /-- `DUPn` -/
  | Dup (n : Nat) (h : 0 < n ∧ n ≤ 16 := by omega)
  /-- `SWAPn` -/
  | Swap (n : Nat) (h : 0 < n ∧ n ≤ 16 := by omega)
  /-- `CREATE(value, offset, size)` -/
  | Create
  /-- `CALL(gas, addr, value, argsOffset, argsSize, retOffset, retSize)` -/
  | Call
  /-- `RETURN(offset, size)` -/
  | Return
  deriving DecidableEq, Repr

namespace Instr

def opcode : Instr → UInt8
  | Stop => 0x00
  | Add => 0x01
  | Eq => 0x14
  | Codecopy => 0x39
  | Extcodecopy => 0x3c
  | Pop => 0x50
  | Mload => 0x51
  | Mstore => 0x52
  | Jump => 0x56
  | Jumpi => 0x57
  | Gas => 0x5a
  | Jumpdest => 0x5b
  | Push n _ => (0x5f + n.val).toUInt8
  | Dup n _ => (0x7f + n).toUInt8
  | Swap n _ => (0x8f + n).toUInt8
  | Create => 0xf0
  | Call => 0xf1
  | Return => 0xf3

/-- the bytes after the opcode -/
def immediate : Instr → List UInt8
  | Push _ imm => imm.toList
  | _ => []

def encode (i : Instr) : List UInt8 := i.opcode :: i.immediate

/-- the instruction for an opcode byte that has no immediate -/
def ofByte (b : UInt8) : Option Instr :=
  if h : 0x80 ≤ b.toNat ∧ b.toNat < 0x90 then some (Dup (b.toNat - 0x7f))
  else if h : 0x90 ≤ b.toNat ∧ b.toNat < 0xa0 then some (Swap (b.toNat - 0x8f))
  else match b.toNat with
    | 0x00 => some Stop
    | 0x01 => some Add
    | 0x14 => some Eq
    | 0x39 => some Codecopy
    | 0x3c => some Extcodecopy
    | 0x50 => some Pop
    | 0x51 => some Mload
    | 0x52 => some Mstore
    | 0x56 => some Jump
    | 0x57 => some Jumpi
    | 0x5a => some Gas
    | 0x5b => some Jumpdest
    | 0xf0 => some Create
    | 0xf1 => some Call
    | 0xf3 => some Return
    | _ => none

/-- the first `k` bytes, padded with zeros on the right if there are fewer -/
def takeImmediate (k : Nat) (bytes : List UInt8) : Vector UInt8 k :=
  ⟨(bytes.take k ++ List.replicate (k - (bytes.take k).length) 0).toArray, by simp; omega⟩

/-- `PUSHn` with its immediate taken from `rest`, and the bytes after the immediate -/
def decodePush (n : Fin 33) (rest : List UInt8) : Instr × List UInt8 :=
  (Push n (takeImmediate n rest), rest.drop n)

end Instr

open Instr in
/-- Decode the instruction with opcode `b` and the bytes `rest` after it. Gives the
instruction and the bytes after it, or `none` if `b` is not a defined opcode. -/
def decode (b : UInt8) (rest : List UInt8) : Option (Instr × List UInt8) :=
  if h : 0x5f ≤ b.toNat ∧ b.toNat < 0x80 then
    some (decodePush ⟨b.toNat - 0x5f, by omega⟩ rest)
  else (ofByte b).map (·, rest)

end EVM
