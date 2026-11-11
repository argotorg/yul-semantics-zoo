import YulSemnaticsZoo.EVM.Syntax

/-!
# EVM: lemmas about encoding and decoding
-/

namespace EVM
open Instr

/-- decoding the opcode and the immediate of an instruction gives back the instruction and the
bytes after it -/
theorem decode_opcode_immediate (i : Instr) (rest : List UInt8) :
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

/-- with enough steps, `disassemble.go` decodes each encoded instruction -/
theorem disassemble_go_encode (l : List Instr) (k : Nat) (h : (l.flatMap encode).length ≤ k) :
    disassemble.go k (l.flatMap encode) = l.map some := by
  induction l generalizing k with
  | nil => cases k <;> simp [disassemble.go]
  | cons i l ih =>
    simp only [List.flatMap_cons, encode, List.cons_append, List.length_cons,
      List.length_append] at h ⊢
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [disassemble.go, decode_opcode_immediate, List.map_cons]
    rw [ih k (by omega)]

/-- an opcode byte without an immediate encodes to itself -/
theorem ofByte_encode {b : UInt8} {i : Instr} (h : ofByte b = some i) : i.encode = [b] := by
  unfold ofByte at h
  split at h
  · cases h; simp [encode, opcode, immediate]; apply UInt8.toNat_inj.mp; simp; omega
  · split at h
    · cases h; simp [encode, opcode, immediate]; apply UInt8.toNat_inj.mp; simp; omega
    · split at h <;> cases h <;> simp [encode, opcode, immediate] <;>
        apply UInt8.toNat_inj.mp <;> simp_all

end EVM
