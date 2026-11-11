import YulSemnaticsZoo.EVM.Lemmas.Encode

/-!
# Tiny EVM: theorems

Decoding an encoded instruction or program gives it back, and encoding a decoded instruction
gives back the bytes.
-/

namespace EVM
open Instr

/-- decoding an encoded instruction gives back the instruction and the bytes after it -/
theorem decode_encode (i : Instr) (rest : List UInt8) :
    decode i.opcode (i.immediate ++ rest) = some (i, rest) :=
  decode_opcode_immediate i rest

/-- disassembling an encoded program gives back its instructions -/
theorem disassemble_encode (l : List Instr) : disassemble (l.flatMap encode) = l.map some :=
  disassemble_go_encode l _ (Nat.le_refl _)

/-- encoding a decoded instruction gives back the bytes, with zeros after them where the
immediate is cut off -/
theorem encode_decode {b : UInt8} {rest rest' : List UInt8} {i : Instr}
    (h : decode b rest = some (i, rest')) :
    i.encode ++ rest' = b :: rest ++ List.replicate (i.immediate.length - rest.length) 0 := by
  unfold decode at h
  split at h
  · simp [decodePush] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [encode, opcode, immediate, takeImmediate]
    refine ⟨UInt8.toNat_inj.mp (by simp; omega), ?_⟩
    generalize b.toNat - 95 = n
    by_cases hn : n ≤ rest.length
    · simp [Nat.min_eq_left hn]; omega
    · have hn : rest.length ≤ n := by omega
      simp [Nat.min_eq_right hn, List.take_of_length_le hn, List.drop_of_length_le hn]
  · simp at h
    obtain ⟨i, hi, rfl, rfl⟩ := h
    have he := ofByte_encode hi
    have : i.immediate = [] := by simp [encode] at he; exact he.2
    simp [he, this]

/-- if the immediate is not cut off, encoding a decoded instruction gives back the bytes -/
theorem encode_decode_of_le {b : UInt8} {rest rest' : List UInt8} {i : Instr}
    (h : decode b rest = some (i, rest')) (hl : i.immediate.length ≤ rest.length) :
    i.encode ++ rest' = b :: rest := by
  simpa [Nat.sub_eq_zero_of_le hl] using encode_decode h

/-- if the immediate is cut off, it is `rest` with zeros after it, and no bytes are left -/
theorem decode_cut {b : UInt8} {rest rest' : List UInt8} {i : Instr}
    (h : decode b rest = some (i, rest')) (hl : rest.length < i.immediate.length) :
    i.immediate = rest ++ List.replicate (i.immediate.length - rest.length) 0 ∧ rest' = [] := by
  have he := encode_decode h
  simp only [encode, List.cons_append, List.cons.injEq] at he
  have : rest' = [] := List.eq_nil_of_length_eq_zero (by
    have := congrArg List.length he.2; simp at this; omega)
  subst this
  simpa using he.2

end EVM
