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

/-- the opcode bytes the tiny EVM defines, from the yellow paper -/
def defined : List Nat :=
  [0x00, 0x01, 0x14, 0x39, 0x3c, 0x50, 0x51, 0x52, 0x56, 0x57, 0x5a, 0x5b, 0xf0, 0xf1, 0xf3]
  ++ (List.range 33).map (0x5f + ·)
  ++ (List.range 16).map (0x80 + ·)
  ++ (List.range 16).map (0x90 + ·)

-- exactly the defined bytes decode
#guard (List.range 256).all fun n => (decode n.toUInt8 []).isSome == defined.contains n

-- the ends of the Push / Dup / Swap ranges
#guard (Push 0 #v[]).opcode == 0x5f
#guard (Push 1 #v[0]).opcode == 0x60
#guard (Push 32 (Vector.replicate 32 0)).opcode == 0x7f
#guard (Dup 1).opcode == 0x80
#guard (Dup 16).opcode == 0x8f
#guard (Swap 1).opcode == 0x90
#guard (Swap 16).opcode == 0x9f
-- DUPn and SWAPn exist only for 1 ≤ n ≤ 16
#guard_msgs (drop info) in #check_failure Dup 0
#guard_msgs (drop info) in #check_failure Dup 17
#guard_msgs (drop info) in #check_failure Swap 0
#guard_msgs (drop info) in #check_failure Swap 17

#guard decode 0xa0 [] == none -- LOG0 is not in the tiny EVM
#guard decode 0x35 [] == none -- CALLDATALOAD is not in the tiny EVM

-- Push takes only its immediate
#guard decode 0x5f [0x01] == some (Push 0 #v[], [0x01])
#guard decode 0x60 [0x01, 0x02] == some (Push 1 #v[0x01], [0x02])
-- a Push cut off by the end of the code is padded with zeros on the right
#guard decode 0x61 [0xab] == some (Push 2 #v[0xab, 0x00], [])
#guard decode 0x7f [] == some (Push 32 (Vector.replicate 32 0), [])

end EVM.Test
