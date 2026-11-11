import YulSemnaticsZoo.EVM.Syntax

namespace EVM.Test
open EVM Instr

/-- decoding an encoded instruction gives back the instruction and the bytes after it -/
theorem decode_encode (i : Instr) (rest : List UInt8) :
    decode i.opcode (i.immediate ++ rest) = some (i, rest) := by
  cases i with
  | Push n imm =>
    have h : (0x5f + n.val).toUInt8.toNat = 0x5f + n.val := by simp; omega
    show decode (0x5f + n.val).toUInt8 _ = _
    rw [decode, dite_eq_left (by omega)]
    have hn : (⟨(0x5f + n.val).toUInt8.toNat - 0x5f, by omega⟩ : Fin 33) = n :=
      Fin.ext (by simp; omega)
    rw [hn]
    simp [decodePush, immediate, takeImmediate, Vector.toList]
  | Dup n h =>
    have : (0x7f + n).toUInt8.toNat = 0x7f + n := by simp; omega
    show decode (0x7f + n).toUInt8 ([] ++ rest) = _
    rw [decode, dite_eq_right (by omega), ofByte, dite_eq_left (by omega)]
    simp; omega
  | Swap n h =>
    have : (0x8f + n).toUInt8.toNat = 0x8f + n := by simp; omega
    show decode (0x8f + n).toUInt8 ([] ++ rest) = _
    rw [decode, dite_eq_right (by omega), ofByte, dite_eq_right (by omega),
      dite_eq_left (by omega)]
    simp; omega
  | _ => simp [decode, opcode, immediate, ofByte]

end EVM.Test
