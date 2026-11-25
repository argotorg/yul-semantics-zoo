import YulSemnaticsZoo.Compiler.Lemmas.Layout

set_option doc.verso true

/-!
# Compiler: lemmas about steps of the abstract EVM

{lit}`Steps B i ρ s n k s' n'`: {lit}`k` steps of the abstract EVM go from the state {lit}`s` with
{lit}`n` reads to {lit}`s'` with {lit}`n'` reads, without a halt. The lemmas give the steps of
each item of the compiled code, and of the sequences {lit}`pops`, {lit}`PUSH0 …` and
{lit}`rotate`.
-/

namespace Compiler
open Semantics

section
variable (B : List UInt8) (inp : Input) (ρ : Readings)

/-- {lit}`k` steps without a halt -/
inductive Steps : EVM.State → Nat → Nat → EVM.State → Nat → Prop
  | refl : Steps s n 0 s n
  | step : EVM.step (EVM.abstract ρ) B inp s n = .next s₁ n₁ → Steps s₁ n₁ k s₂ n₂ →
      Steps s n (k + 1) s₂ n₂

/-- the run can do {name}`k` steps without a halt: with clock {name}`k`, it times out -/
def Survives (s : EVM.State) (n k : Nat) : Prop := ∃ s' n', Steps B inp ρ s n k s' n'

/-- the run halts with {name}`r` -/
def Halts (s : EVM.State) (n : Nat) (r : Result) : Prop :=
  ∃ k s' n' n'', Steps B inp ρ s n k s' n' ∧ EVM.step (EVM.abstract ρ) B inp s' n' = .halt r n''

end

variable {B : List UInt8} {inp : Input} {ρ : Readings}

theorem Steps.trans (h : Steps B inp ρ s n k s' n') (h' : Steps B inp ρ s' n' k' s'' n'') :
    Steps B inp ρ s n (k + k') s'' n'' := by
  induction h with
  | refl => simpa using h'
  | step hs _ ih => rw [Nat.add_right_comm]; exact .step hs (ih h')

theorem Steps.one (h : EVM.step (EVM.abstract ρ) B inp s n = .next s' n') :
    Steps B inp ρ s n 1 s' n' := .step h .refl

theorem Steps.run (h : Steps B inp ρ s n k s' n') (j : Nat) :
    EVM.run (EVM.abstract ρ) B inp (k + j) s n = EVM.run (EVM.abstract ρ) B inp j s' n' := by
  induction h with
  | refl => simp
  | step hs _ ih => rw [Nat.add_right_comm, EVM.run, hs]; exact ih

theorem Steps.prefix (h : Steps B inp ρ s n k s' n') (hj : j ≤ k) :
    ∃ s'' n'', Steps B inp ρ s n j s'' n'' := by
  induction h generalizing j with
  | refl => exact ⟨_, _, by rw [Nat.le_zero.mp hj]; exact .refl⟩
  | step hs _ ih =>
    cases j with
    | zero => exact ⟨_, _, .refl⟩
    | succ j =>
      obtain ⟨s'', n'', h⟩ := ih (j := j) (by omega)
      exact ⟨s'', n'', .step hs h⟩

theorem Survives.of_steps (h : Steps B inp ρ s n k s' n') (h' : Survives B inp ρ s' n' k')
    (hk : m ≤ k + k') : Survives B inp ρ s n m := by
  obtain ⟨s'', n'', h'⟩ := h'
  exact (h.trans h').prefix hk

theorem Survives.of_le (h : Steps B inp ρ s n k s' n') (hk : m ≤ k) : Survives B inp ρ s n m :=
  h.prefix hk

theorem Halts.of_steps (h : Steps B inp ρ s n k s' n') (h' : Halts B inp ρ s' n' r) :
    Halts B inp ρ s n r := by
  obtain ⟨k', s'', n'', m, h', hh⟩ := h'
  exact ⟨_, _, _, _, h.trans h', hh⟩

theorem Survives.run (h : Survives B inp ρ s n k) : EVM.run (EVM.abstract ρ) B inp k s n = .timeout := by
  obtain ⟨s', n', h⟩ := h
  simpa [EVM.run] using h.run 0

theorem Halts.run (h : Halts B inp ρ s n r) :
    ∃ k m, EVM.run (EVM.abstract ρ) B inp k s n = .halt r m := by
  obtain ⟨k, s', n', m, h, hh⟩ := h
  exact ⟨k + 1, m, by rw [h.run 1, EVM.run, hh]⟩

/-! ## One instruction -/

/-- the step of an instruction that is not unsupported, with enough words on the stack -/
theorem step_ok (hf : EVM.fetch B s.pc = .ok i) (ha : i.arity.1 ≤ s.stack.length) :
    EVM.step (EVM.abstract ρ) B inp s n =
      match EVM.exec B inp i { s with words := max s.words (i.memWords s.stack) } with
      | .next s => .next s n
      | .halt r => .halt r n
      | .gas k => .next (k (ρ n)) (n + 1) := by
  simp only [EVM.step, hf, EVM.abstract, Option.any, Bool.false_eq_true, ite_false,
    Nat.not_lt.mpr ha]
  split <;> simp_all

/-- the state has the pc, the stack and the memory -/
def Is (s : EVM.State) (pc : Nat) (stack : List Word) (mem : Memory) : Prop :=
  s.pc = pc ∧ s.stack = stack ∧ s.mem = mem

variable {prog : Code}

/-- an instruction that goes to the next item -/
theorem step_op (hA : At prog s.pc (.op i :: c)) (hu : i.unsupported = false)
    (ha : i.arity.1 ≤ s.stack.length)
    (he : EVM.exec (layout prog) inp i { s with words := max s.words (i.memWords s.stack) } =
      .next s') :
    EVM.step (EVM.abstract ρ) (layout prog) inp s n = .next s' n := by
  have hf : EVM.fetch (layout prog) s.pc = .ok i := fetch_at hA hu
  rw [step_ok hf ha, he]


/-- an instruction that goes to a state with the pc, the stack and the memory -/
theorem st_next (hA : At prog s.pc (.op i :: c)) (hu : i.unsupported = false)
    (ha : i.arity.1 ≤ s.stack.length)
    (he : ∃ s', EVM.exec (layout prog) inp i { s with words := max s.words (i.memWords s.stack) } =
      .next s' ∧ Is s' pc st m) :
    ∃ s', Steps (layout prog) inp ρ s n 1 s' n ∧ Is s' pc st m := by
  obtain ⟨s', he, hs⟩ := he
  exact ⟨s', .one (step_op hA hu ha he), hs⟩

theorem st_pop (hA : At prog s.pc (.op .Pop :: c)) (hs : s.stack = a :: st) :
    ∃ s', Steps (layout prog) inp ρ s n 1 s' n ∧ Is s' (s.pc + 1) st s.mem :=
  st_next hA rfl (by simp [hs, EVM.Instr.arity]) (by simp [EVM.exec, hs, Is, EVM.Instr.immediate])

theorem st_push (hA : At prog s.pc (.op (pushNat k v) :: c)) (hv : v < 2 ^ (8 * k.val)) :
    ∃ s', Steps (layout prog) inp ρ s n 1 s' n ∧
      Is s' (s.pc + 1 + k) (BitVec.ofNat 256 v :: s.stack) s.mem :=
  st_next hA rfl (by simp [pushNat, EVM.Instr.arity])
    (by simp [pushNat, EVM.exec, Is, EVM.Instr.immediate, toBytes_length, ofBytes_pushNat hv])

theorem st_push0 (hA : At prog s.pc (push0 :: c)) :
    ∃ s', Steps (layout prog) inp ρ s n 1 s' n ∧ Is s' (s.pc + 1) (0 :: s.stack) s.mem := by
  simpa using st_push (k := 0) (v := 0) hA (by simp)

/-- an item that is not an instruction: its instruction goes to a state with the pc, the stack
and the memory -/
theorem st_item (hA : At prog s.pc (it :: c)) (hu : (it.resolve (pos prog)).unsupported = false)
    (ha : (it.resolve (pos prog)).arity.1 ≤ s.stack.length)
    (he : ∃ s', EVM.exec (layout prog) inp (it.resolve (pos prog))
      { s with words := max s.words ((it.resolve (pos prog)).memWords s.stack) } =
      .next s' ∧ Is s' pc st m) :
    ∃ s', Steps (layout prog) inp ρ s n 1 s' n ∧ Is s' pc st m := by
  obtain ⟨s', he, hs⟩ := he
  exact ⟨s', .one (by rw [step_ok (fetch_at hA hu) ha, he]), hs⟩

theorem st_label (hA : At prog s.pc (.label l :: c)) :
    ∃ s', Steps (layout prog) inp ρ s n 1 s' n ∧ Is s' (s.pc + 1) s.stack s.mem :=
  st_item hA rfl (by simp [Item.resolve, EVM.Instr.arity])
    (by simp [Item.resolve, EVM.exec, Is, EVM.Instr.immediate])

theorem st_pushLabel (hA : At prog s.pc (.push l :: c)) :
    ∃ s', Steps (layout prog) inp ρ s n 1 s' n ∧
      Is s' (s.pc + 3) (BitVec.ofNat 256 (pos prog l % 2 ^ 16) :: s.stack) s.mem :=
  st_item hA rfl (by simp [Item.resolve, pushNat, EVM.Instr.arity])
    (by simp [Item.resolve, pushNat, EVM.exec, Is, EVM.Instr.immediate, toBytes_length,
      ofBytes_toBytes])

theorem st_dup (hA : At prog s.pc (.op (.Dup k hk) :: c)) (hv : s.stack[k - 1]? = some v) :
    ∃ s', Steps (layout prog) inp ρ s n 1 s' n ∧ Is s' (s.pc + 1) (v :: s.stack) s.mem := by
  have hl : k ≤ s.stack.length := by
    obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.mp hv; omega
  exact st_next hA rfl (by simp [EVM.Instr.arity, hl])
    (by simp [EVM.exec, hv, Is, EVM.Instr.immediate])

theorem st_swap (hA : At prog s.pc (.op (.Swap k hk) :: c)) (hs : s.stack = a :: st)
    (hv : st[k - 1]? = some b) :
    ∃ s', Steps (layout prog) inp ρ s n 1 s' n ∧
      Is s' (s.pc + 1) (b :: st.set (k - 1) a) s.mem := by
  have hl : k + 1 ≤ s.stack.length := by
    obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.mp hv; simp [hs]; omega
  exact st_next hA rfl (by simp [EVM.Instr.arity, hl])
    (by simp [EVM.exec, hs, hv, Is, EVM.Instr.immediate])

theorem st_add (hA : At prog s.pc (.op .Add :: c)) (hs : s.stack = a :: b :: st) :
    ∃ s', Steps (layout prog) inp ρ s n 1 s' n ∧ Is s' (s.pc + 1) ((a + b) :: st) s.mem :=
  st_next hA rfl (by simp [EVM.Instr.arity, hs]) (by simp [EVM.exec, hs, Is, EVM.Instr.immediate])

theorem st_lt (hA : At prog s.pc (.op .Lt :: c)) (hs : s.stack = a :: b :: st) :
    ∃ s', Steps (layout prog) inp ρ s n 1 s' n ∧ Is s' (s.pc + 1) (lt a b :: st) s.mem :=
  st_next hA rfl (by simp [EVM.Instr.arity, hs]) (by simp [EVM.exec, hs, Is, EVM.Instr.immediate])

theorem st_eq (hA : At prog s.pc (.op .Eq :: c)) (hs : s.stack = a :: b :: st) :
    ∃ s', Steps (layout prog) inp ρ s n 1 s' n ∧ Is s' (s.pc + 1) (eq a b :: st) s.mem :=
  st_next hA rfl (by simp [EVM.Instr.arity, hs]) (by simp [EVM.exec, hs, Is, EVM.Instr.immediate])

theorem st_calldataload (hA : At prog s.pc (.op .Calldataload :: c)) (hs : s.stack = a :: st) :
    ∃ s', Steps (layout prog) inp ρ s n 1 s' n ∧
      Is s' (s.pc + 1) (calldataload inp a :: st) s.mem :=
  st_next hA rfl (by simp [EVM.Instr.arity, hs]) (by simp [EVM.exec, hs, Is, EVM.Instr.immediate])

theorem st_mload (hA : At prog s.pc (.op .Mload :: c)) (hs : s.stack = a :: st) :
    ∃ s', Steps (layout prog) inp ρ s n 1 s' n ∧ Is s' (s.pc + 1) (mload s.mem a :: st) s.mem :=
  st_next hA rfl (by simp [EVM.Instr.arity, hs]) (by simp [EVM.exec, hs, Is, EVM.Instr.immediate])

theorem st_mstore (hA : At prog s.pc (.op .Mstore :: c)) (hs : s.stack = a :: v :: st) :
    ∃ s', Steps (layout prog) inp ρ s n 1 s' n ∧ Is s' (s.pc + 1) st (mstore s.mem a v) :=
  st_next hA rfl (by simp [EVM.Instr.arity, hs]) (by simp [EVM.exec, hs, Is, EVM.Instr.immediate])

theorem st_gas (hA : At prog s.pc (.op .Gas :: c)) :
    ∃ s', Steps (layout prog) inp ρ s n 1 s' (n + 1) ∧
      Is s' (s.pc + 1) (ρ n :: s.stack) s.mem := by
  have hf : EVM.fetch (layout prog) s.pc = .ok .Gas := fetch_at hA rfl
  refine ⟨⟨s.pc + 1, ρ n :: s.stack, s.mem, max s.words (EVM.Instr.Gas.memWords s.stack)⟩,
    .one ?_, by simp [Is]⟩
  rw [step_ok hf (by simp [EVM.Instr.arity])]
  simp [EVM.exec, EVM.Instr.immediate]

theorem st_jump (hA : At prog s.pc (.op .Jump :: c)) (hs : s.stack = d :: st)
    (hd : d.toNat ∈ EVM.jumpdests (layout prog)) :
    ∃ s', Steps (layout prog) inp ρ s n 1 s' n ∧ Is s' d.toNat st s.mem :=
  st_next hA rfl (by simp [EVM.Instr.arity, hs]) (by simp [EVM.exec, hs, EVM.jump, hd, Is])

theorem st_jumpi_zero (hA : At prog s.pc (.op .Jumpi :: c)) (hs : s.stack = d :: 0 :: st) :
    ∃ s', Steps (layout prog) inp ρ s n 1 s' n ∧ Is s' (s.pc + 1) st s.mem :=
  st_next hA rfl (by simp [EVM.Instr.arity, hs]) (by simp [EVM.exec, hs, Is, EVM.Instr.immediate])

theorem st_jumpi_ne (hA : At prog s.pc (.op .Jumpi :: c)) (hs : s.stack = d :: v :: st)
    (hv : v ≠ 0) (hd : d.toNat ∈ EVM.jumpdests (layout prog)) :
    ∃ s', Steps (layout prog) inp ρ s n 1 s' n ∧ Is s' d.toNat st s.mem :=
  have hv' : ¬ v = 0#256 := hv
  st_next hA rfl (by simp [EVM.Instr.arity, hs]) (by simp [EVM.exec, hs, hv', EVM.jump, hd, Is])

theorem st_return (hA : At prog s.pc (.op .Return :: c)) (hs : s.stack = off :: sz :: st) :
    EVM.step (EVM.abstract ρ) (layout prog) inp s n = .halt (.ret (read s.mem off sz)) n := by
  have hf : EVM.fetch (layout prog) s.pc = .ok .Return := fetch_at hA rfl
  rw [step_ok hf (by simp [EVM.Instr.arity, hs])]
  simp [EVM.exec, hs]

theorem st_stop (hA : At prog s.pc (.op .Stop :: c)) :
    EVM.step (EVM.abstract ρ) (layout prog) inp s n = .halt (.ret []) n := by
  have hf : EVM.fetch (layout prog) s.pc = .ok .Stop := fetch_at hA rfl
  rw [step_ok hf (by simp [EVM.Instr.arity])]
  simp [EVM.exec]

/-! ## Sequences -/

theorem st_pops (hA : At prog s.pc (pops k ++ c)) (hs : s.stack = l ++ st) (hl : l.length = k) :
    ∃ s', Steps (layout prog) inp ρ s n k s' n ∧ Is s' (s.pc + k) st s.mem := by
  induction l generalizing s k with
  | nil => subst hl; exact ⟨s, .refl, by simp [Is, hs]⟩
  | cons a l ih =>
    subst hl
    have hA' : At prog s.pc (.op .Pop :: (pops l.length ++ c)) := by
      simpa [pops, List.replicate_succ] using hA
    obtain ⟨s1, h1, hp, hs1, hm⟩ := st_pop (n := n) (ρ := ρ) (inp := inp) hA' hs
    have hA1 : At prog s1.pc (pops l.length ++ c) := by
      rw [hp]; simpa [Item.size, EVM.Instr.encode, EVM.Instr.immediate] using hA'.tail
    obtain ⟨s2, h2, hp2, hs2, hm2⟩ := ih hA1 hs1 rfl
    refine ⟨s2, by simpa [Nat.add_comm] using h1.trans h2, ?_, hs2, by rw [hm2, hm]⟩
    simp [hp2, hp]; omega

theorem st_push0s (hA : At prog s.pc (List.replicate k push0 ++ c)) :
    ∃ s', Steps (layout prog) inp ρ s n k s' n ∧
      Is s' (s.pc + k) (List.replicate k 0 ++ s.stack) s.mem := by
  induction k generalizing s with
  | zero => exact ⟨s, .refl, by simp [Is]⟩
  | succ k ih =>
    have hA' : At prog s.pc (push0 :: (List.replicate k push0 ++ c)) := by
      simpa [List.replicate_succ] using hA
    obtain ⟨s1, h1, hp, hs1, hm⟩ := st_push0 (n := n) (ρ := ρ) (inp := inp) hA'
    have hA1 : At prog s1.pc (List.replicate k push0 ++ c) := by
      rw [hp]; simpa [push0, Item.size, pushNat_encode_length] using hA'.tail
    obtain ⟨s2, h2, hp2, hs2, hm2⟩ := ih hA1
    refine ⟨s2, by simpa [Nat.add_comm] using h1.trans h2, ?_, ?_, by rw [hm2, hm]⟩
    · simp [hp2, hp]; omega
    · rw [hs2, hs1, List.replicate_succ']; simp

theorem swap_ok (h : swap k = .ok it) : ∃ hk, it = .op (.Swap k hk) := by
  unfold swap at h
  split at h
  · next hk => exact ⟨hk, by cases h; rfl⟩
  · cases h

theorem rotate_succ (h : rotate (m + 1) = .ok c) :
    ∃ c' it, rotate m = .ok c' ∧ swap (m + 1) = .ok it ∧ c = c' ++ [it] := by
  unfold rotate at h ⊢
  rw [List.range_succ, List.mapM_append] at h
  cases hr : (List.range m).mapM fun j => swap (j + 1) with
  | error e => simp [hr] at h; cases h
  | ok c' =>
    cases hs : swap (m + 1) with
    | error e => simp [hr, hs] at h; cases h
    | ok it => simp [hr, hs] at h; cases h; exact ⟨c', it, rfl, rfl, rfl⟩

theorem rotate_size (h : rotate m = .ok c) : size c = m := by
  induction m generalizing c with
  | zero => cases h; rfl
  | succ m ih =>
    obtain ⟨c', it, h', hs, rfl⟩ := rotate_succ h
    obtain ⟨hk, rfl⟩ := swap_ok hs
    simp [ih h', Item.size, EVM.Instr.encode, EVM.Instr.immediate]

theorem st_rotate (hr : rotate m = .ok c) (hA : At prog s.pc (c ++ c'))
    (hs : s.stack = l ++ x :: st) (hl : l.length = m) :
    ∃ s', Steps (layout prog) inp ρ s n m s' n ∧ Is s' (s.pc + m) (x :: l ++ st) s.mem := by
  induction m generalizing s c c' l x st with
  | zero =>
    cases hr; obtain rfl := List.eq_nil_of_length_eq_zero hl
    exact ⟨s, .refl, by simp [Is, hs]⟩
  | succ m ih =>
    obtain ⟨c₀, it, hr₀, hsw, rfl⟩ := rotate_succ hr
    obtain ⟨hk, rfl⟩ := swap_ok hsw
    obtain ⟨l', y, rfl⟩ : ∃ l' y, l = l' ++ [y] :=
      ⟨l.dropLast, l.getLast (by intro h; simp [h] at hl), (List.dropLast_concat_getLast _).symm⟩
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hl
    have hA' : At prog s.pc (c₀ ++ (.op (.Swap (m + 1) hk) :: c')) := by simpa using hA
    obtain ⟨s1, h1, hp, hs1, hm⟩ := ih hr₀ hA' (x := y) (st := x :: st) (by simp [hs]) hl
    have hA1 : At prog s1.pc (.op (.Swap (m + 1) hk) :: c') := by
      have := hA'.right; rwa [rotate_size hr₀, ← hp] at this
    have hv : (l' ++ x :: st)[m + 1 - 1]? = some x := by
      simp [hl]
    obtain ⟨s2, h2, hp2, hs2, hm2⟩ := st_swap (n := n) (ρ := ρ) (inp := inp) hA1
      (by rw [hs1]; rfl) hv
    refine ⟨s2, h1.trans h2, by simp [hp2, hp]; omega, ?_, by rw [hm2, hm]⟩
    rw [hs2]
    simp [List.set_append_right, hl]

end Compiler
