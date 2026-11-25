import YulSemnaticsZoo.Compiler.Compile
import YulSemnaticsZoo.EVM.Semantics.Clocked.Step
import YulSemnaticsZoo.EVM.Syntax.Theorems

set_option doc.verso true

/-!
# Compiler: lemmas about the layout

{lit}`At prog p c`: the code {lit}`c` is in the program {lit}`prog` at the byte position
{lit}`p`. For a program with unique labels that fits in {lit}`2 ^ 16` bytes ({lit}`Good`), the
instruction of the first item of {lit}`c` is at {lit}`p` in the bytes ({lit}`fetch_at`), the
position of each label of {lit}`c` is known ({lit}`pos_at`), and each label is a
{lit}`JUMPDEST` ({lit}`jumpdest_at`).
-/

namespace Compiler
open Semantics

/-- the number of bytes of the code -/
def size (c : Code) : Nat := (c.map Item.size).sum

@[simp] theorem size_nil : size [] = 0 := rfl
@[simp] theorem size_cons : size (it :: c) = it.size + size c := by simp [size]
@[simp] theorem size_append : size (a ++ b) = size a + size b := by simp [size]
@[simp] theorem size_replicate : size (List.replicate k it) = k * it.size := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ, ih, Nat.succ_mul]; omega

@[simp] theorem Item.size_label : (Item.label l).size = 1 := rfl
@[simp] theorem Item.size_push : (Item.push l).size = 3 := rfl
@[simp] theorem Item.size_push0 : push0.size = 1 := rfl
@[simp] theorem Item.size_op : (Item.op i).size = i.immediate.length + 1 := by
  simp [Item.size, EVM.Instr.encode, Nat.add_comm]
@[simp] theorem immediate_pushNat : (pushNat n v).immediate.length = n := by
  simp [pushNat, EVM.Instr.immediate, toBytes_length]

/-- the labels of the program are unique, and each position fits in 2 bytes -/
structure Good (prog : Code) : Prop where
  nodup : ((offsets prog 0).map (·.1)).Nodup
  small : size prog ≤ 2 ^ 16

/-- the position of the label {name}`l` -/
def pos (prog : Code) (l : Label) : Nat := ((offsets prog 0).lookup l).getD 0

/-- the code {name}`c` is in {name}`prog` at the byte position {name}`p` -/
def At (prog : Code) (p : Nat) (c : Code) : Prop :=
  ∃ pre post, prog = pre ++ c ++ post ∧ size pre = p

theorem At.left (h : At prog p (a ++ b)) : At prog p a := by
  obtain ⟨pre, post, rfl, rfl⟩ := h
  exact ⟨pre, b ++ post, by simp, rfl⟩

theorem At.right (h : At prog p (a ++ b)) : At prog (p + size a) b := by
  obtain ⟨pre, post, rfl, rfl⟩ := h
  exact ⟨pre ++ a, post, by simp, by simp⟩

theorem At.tail (h : At prog p (it :: c)) : At prog (p + it.size) c := by
  have := At.right (a := [it]) h
  simpa using this

theorem At.mid (h : At prog p (a ++ b ++ c)) : At prog (p + size a) b := (At.right h.left)

theorem At.shift (h : At prog p c) (e : p = p') : At prog p' c := e ▸ h

/-! ## Bytes -/

theorem pushNat_encode_length : (pushNat n v).encode.length = n + 1 := by
  simp [pushNat, EVM.Instr.encode, EVM.Instr.immediate, toBytes_length]

theorem resolve_size (f : Label → Nat) (it : Item) : (it.resolve f).encode.length = it.size := by
  cases it with
  | op i => rfl
  | label l => rfl
  | push l => simp [Item.resolve, Item.size, pushNat_encode_length]

theorem bytes_length (f : Label → Nat) (c : Code) :
    ((c.map (Item.resolve f)).flatMap EVM.Instr.encode).length = size c := by
  induction c <;> simp_all [resolve_size]

theorem layout_eq (prog : Code) :
    layout prog = (prog.map (Item.resolve (pos prog))).flatMap EVM.Instr.encode := rfl

theorem fetch_at (hA : At prog p (it :: c)) (hu : (it.resolve (pos prog)).unsupported = false) :
    EVM.fetch (layout prog) p = .ok (it.resolve (pos prog)) := by
  obtain ⟨pre, post, rfl, rfl⟩ := hA
  rw [layout_eq]
  generalize pos (pre ++ it :: c ++ post) = f at hu ⊢
  have e : ((pre ++ it :: c ++ post).map (Item.resolve f)).flatMap EVM.Instr.encode =
      (pre.map (Item.resolve f)).flatMap EVM.Instr.encode ++
        ((it.resolve f).encode ++ ((c ++ post).map (Item.resolve f)).flatMap EVM.Instr.encode) := by
    simp
  rw [e, EVM.fetch, List.drop_left' (bytes_length f pre)]
  generalize it.resolve f = i at hu ⊢
  generalize ((c ++ post).map (Item.resolve f)).flatMap EVM.Instr.encode = rest
  simp [EVM.Instr.encode, EVM.decode_encode, hu]

/-! ## Positions of labels -/

theorem offsets_append (a b : Code) (p : Nat) :
    offsets (a ++ b) p = offsets a p ++ offsets b (p + size a) := by
  induction a generalizing p with
  | nil => simp [offsets]
  | cons it a ih =>
    cases it <;> simp [offsets, ih, Item.size, Nat.add_assoc]

theorem lookup_of_mem {l : List (Label × Nat)} (hn : (l.map (·.1)).Nodup) (hm : (k, v) ∈ l) :
    l.lookup k = some v := by
  induction l with
  | nil => simp at hm
  | cons x l ih =>
    obtain ⟨k', v'⟩ := x
    simp only [List.map_cons, List.nodup_cons] at hn
    simp only [List.mem_cons, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | hm
    · simp [List.lookup]
    · have hk : k ≠ k' := fun h => hn.1 (h ▸ List.mem_map_of_mem (f := (·.1)) hm)
      have hb : (k == k') = false := by simpa using hk
      simp [List.lookup, hb, ih hn.2 hm]

theorem pos_at (hg : Good prog) (hA : At prog p (a ++ .label l :: b)) : pos prog l = p + size a := by
  obtain ⟨pre, post, rfl, rfl⟩ := hA
  have hm : (l, size pre + size a) ∈ offsets (pre ++ (a ++ .label l :: b) ++ post) 0 := by
    simp [offsets_append, offsets]
  rw [pos, lookup_of_mem hg.nodup hm]; rfl

theorem pos_lt (hg : Good prog) (hA : At prog p (a ++ .label l :: b)) : pos prog l < 2 ^ 16 := by
  have hs := hg.small
  rw [pos_at hg hA]
  obtain ⟨pre, post, rfl, rfl⟩ := hA
  simp [Item.size] at hs
  omega

/-! ## Jump destinations -/

/-- the decoding of {lit}`jumpdests` steps over each encoded instruction -/
theorem jumpdests_go_encode (i : EVM.Instr) (pc : Nat) (rest : List UInt8) :
    EVM.jumpdests.go pc (i.encode ++ rest) =
      (if i = .Jumpdest then [pc] else []) ++ EVM.jumpdests.go (pc + i.encode.length) rest := by
  rw [EVM.Instr.encode, List.cons_append, EVM.jumpdests.go]
  cases i with
  | Push n imm =>
    obtain ⟨n, hn⟩ := n
    have hb : (EVM.Instr.Push ⟨n, hn⟩ imm).opcode.toNat = 0x5f + n := by
      simp [EVM.Instr.opcode]; omega
    have hk : (if 0x60 ≤ (EVM.Instr.Push ⟨n, hn⟩ imm).opcode.toNat ∧
        (EVM.Instr.Push ⟨n, hn⟩ imm).opcode.toNat < 0x80 then
        (EVM.Instr.Push ⟨n, hn⟩ imm).opcode.toNat - 0x5f else 0) = n := by
      rw [hb]; split <;> omega
    have h5b : (EVM.Instr.Push ⟨n, hn⟩ imm).opcode ≠ 0x5b := by
      intro h; have := congrArg UInt8.toNat h; rw [hb] at this; simp at this; omega
    simp only [hk, h5b, ite_false, EVM.Instr.immediate, reduceCtorEq]
    simp only [List.nil_append, Vector.length_toList, List.length_cons]
    rw [List.drop_left' (by simp)]
    congr 1; omega
  | Dup n h =>
    have hb : (EVM.Instr.Dup n h).opcode.toNat = 0x7f + n := by
      simp [EVM.Instr.opcode]; omega
    have hk : ¬(0x60 ≤ (EVM.Instr.Dup n h).opcode.toNat ∧
        (EVM.Instr.Dup n h).opcode.toNat < 0x80) := by rw [hb]; omega
    have h5b : (EVM.Instr.Dup n h).opcode ≠ 0x5b := by
      intro h'; have := congrArg UInt8.toNat h'; rw [hb] at this; simp at this; omega
    simp [hk, h5b, EVM.Instr.immediate]
  | Swap n h =>
    have hb : (EVM.Instr.Swap n h).opcode.toNat = 0x8f + n := by
      simp [EVM.Instr.opcode]; omega
    have hk : ¬(0x60 ≤ (EVM.Instr.Swap n h).opcode.toNat ∧
        (EVM.Instr.Swap n h).opcode.toNat < 0x80) := by rw [hb]; omega
    have h5b : (EVM.Instr.Swap n h).opcode ≠ 0x5b := by
      intro h'; have := congrArg UInt8.toNat h'; rw [hb] at this; simp at this; omega
    simp [hk, h5b, EVM.Instr.immediate]
  | _ => simp [EVM.Instr.opcode, EVM.Instr.immediate]

theorem jumpdests_go_flatMap (l : List EVM.Instr) (pc : Nat) (rest : List UInt8) :
    ∃ ds, EVM.jumpdests.go pc (l.flatMap EVM.Instr.encode ++ rest) =
      ds ++ EVM.jumpdests.go (pc + (l.flatMap EVM.Instr.encode).length) rest := by
  induction l generalizing pc with
  | nil => exact ⟨[], by simp⟩
  | cons i l ih =>
    obtain ⟨ds, h⟩ := ih (pc + i.encode.length)
    refine ⟨(if i = .Jumpdest then [pc] else []) ++ ds, ?_⟩
    rw [List.flatMap_cons, List.append_assoc, jumpdests_go_encode, h]
    simp [Nat.add_assoc]

theorem jumpdest_at (hA : At prog p (.label l :: c)) : p ∈ EVM.jumpdests (layout prog) := by
  obtain ⟨pre, post, rfl, rfl⟩ := hA
  rw [EVM.jumpdests, layout_eq]
  generalize pos (pre ++ .label l :: c ++ post) = f
  have e : ((pre ++ .label l :: c ++ post).map (Item.resolve f)).flatMap EVM.Instr.encode =
      (pre.map (Item.resolve f)).flatMap EVM.Instr.encode ++
        (EVM.Instr.Jumpdest.encode ++ ((c ++ post).map (Item.resolve f)).flatMap EVM.Instr.encode) := by
    simp [Item.resolve]
  rw [e]
  obtain ⟨ds, h⟩ := jumpdests_go_flatMap (pre.map (Item.resolve f)) 0 _
  rw [h, jumpdests_go_encode]
  have hl : (List.map ((fun a => a.encode.length) ∘ Item.resolve f) pre).sum = size pre := by
    have := bytes_length f pre; simpa [List.length_flatMap] using this
  simp [List.length_flatMap, hl]

/-! ## Values of pushes -/

theorem ofBytes_append (l : List UInt8) (b : UInt8) :
    ofBytes (l ++ [b]) = ofBytes l <<< 8 ||| b.toBitVec.setWidth 256 := by
  simp [ofBytes, List.foldl_append]

theorem ofBytes_toBytes (h : n ≤ 32) :
    ofBytes (toBytes n v) = BitVec.ofNat 256 (v % 2 ^ (8 * n)) := by
  induction n generalizing v with
  | zero => simp [toBytes, ofBytes, Nat.mod_one]
  | succ n ih =>
    rw [toBytes, ofBytes_append, ih (by omega)]
    apply BitVec.eq_of_toNat_eq
    have hp : 0 < 2 ^ (8 * n) := Nat.pow_pos (by omega)
    have hx : (v / 256) % 2 ^ (8 * n) < 2 ^ (8 * n) := Nat.mod_lt _ hp
    have h248 : 2 ^ (8 * n) ≤ 2 ^ 248 := Nat.pow_le_pow_right (by omega) (by omega)
    have hb : v % 256 < 2 ^ 8 := Nat.mod_lt _ (by omega)
    have hm : v % 2 ^ (8 * (n + 1)) = v % 256 + 256 * ((v / 256) % 2 ^ (8 * n)) := by
      rw [show 8 * (n + 1) = 8 + 8 * n by omega, Nat.pow_add, Nat.mod_mul]
    have hu : ((v % 256).toUInt8.toBitVec.setWidth 256).toNat = v % 256 := by
      simp; omega
    simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, hu]
    generalize (v / 256) % 2 ^ (8 * n) = x at hx hm
    have h1 : x % 2 ^ 256 = x := Nat.mod_eq_of_lt (by omega)
    have h2 : x <<< 8 % 2 ^ 256 = x <<< 8 := Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega)
    rw [h1, h2, ← Nat.shiftLeft_add_eq_or_of_lt hb, hm, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (a := v % 256 + 256 * x) (by omega)]
    omega

/-- the value that {lit}`pushNat n v` pushes -/
theorem ofBytes_pushNat {n : Fin 33} (hv : v < 2 ^ (8 * n.val)) :
    ofBytes (toBytes n v) = BitVec.ofNat 256 v := by
  rw [ofBytes_toBytes (by omega), Nat.mod_eq_of_lt hv]

end Compiler
