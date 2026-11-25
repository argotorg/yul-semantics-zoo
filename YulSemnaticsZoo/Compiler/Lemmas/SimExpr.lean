import YulSemnaticsZoo.Compiler.Lemmas.Sim

set_option doc.verso true

/-!
# Compiler: the simulation of expressions

The cases of {lit}`sim` for {lit}`eval` and {lit}`evals`.
-/

namespace Compiler
open Semantics Yul Yul.Clocked

variable {prog : Code} {inp : Input} {ρ : Readings}

theorem sim_literal : M5 prog inp ρ fs st (.Literal l) := by
  intro ctx q d k code hc p hA hF hN s0 n T rest hT hp hs hm hn
  rw [compileExpr] at hc
  inv hc
  obtain ⟨rfl, rfl⟩ := hc
  rw [eval]
  refine ⟨rfl, rfl, Goes.done (st_push (hA.at hp) (BitVec.isLt _)) ?_ ?_ hm hn (by dsimp only; omega)⟩
  · simp [hp, Item.size, pushNat_encode_length]; omega
  · simp

theorem dup_ok (h : dup k = .ok it) : ∃ hk, it = .op (.Dup k hk) := by
  unfold dup at h
  split at h
  · next hk => exact ⟨hk, by cases h; rfl⟩
  · cases h

theorem sim_identifier : M5 prog inp ρ fs st (.Identifier x) := by
  intro ctx q d k code hc p hA hF hN s0 n T rest hT hp hs hm hn
  rw [compileExpr] at hc
  inv hc
  obtain ⟨rfl, hc⟩ := hc
  split at hc
  · next j hj =>
    inv hc
    obtain ⟨it, hd, rfl⟩ := hc
    obtain ⟨hk, rfl⟩ := dup_ok hd
    rw [eval]
    have hv : s0.stack[d + j + 1 - 1]? = some (Vars.get st.vars x) := by
      rw [hs, show d + j + 1 - 1 = T.length + j by omega, List.append_assoc,
        List.getElem?_append_right (by omega), show T.length + j - T.length = j by omega,
        List.getElem?_append_left]
      · exact get_of_idx (hN ▸ hj)
      · have := List.idxOf?_eq_some_iff.mp (hN ▸ hj) |>.1; simpa using this
    refine ⟨rfl, rfl, Goes.done (st_dup (hA.at hp) hv) ?_ ?_ hm hn (by dsimp only; omega)⟩
    · simp [hp, Item.size, EVM.Instr.encode, EVM.Instr.immediate]
    · simp
  · inv hc

theorem sim_args_nil : M6 prog inp ρ fs st [] := by
  intro ctx q d code hc p hA hF hN s0 n T rest hT hp hs hm hn
  rw [compileArgs] at hc
  cases hc
  rw [evals]
  exact ⟨rfl, rfl, Goes.refl ⟨by simp [hp], rfl, hm⟩ hn (Nat.le_refl _)⟩

theorem compileArgs_cons (h : compileArgs ctx q d (e :: es) = .ok code) :
    ∃ c1 c2, compileArgs ctx q d es = .ok c1 ∧
      compileExpr ctx (q ++ [es.length]) (d + es.length) e 1 = .ok c2 ∧ code = c1 ++ c2 := by
  rw [compileArgs] at h
  inv h
  obtain ⟨c1, h1, c2, h2, rfl⟩ := h
  exact ⟨c1, c2, h1, h2, rfl⟩

theorem sim_args_ok (he : evals inp ρ fs st es = ⟨.ok vs1, st1, h1⟩)
    (he' : eval inp ρ fs st1 e = ⟨.ok vs, st2, h2⟩)
    (ih : M6 prog inp ρ fs st es) (ih' : M5 prog inp ρ fs st1 e) :
    M6 prog inp ρ fs st (e :: es) := by
  intro ctx q d code hc p hA hF hN s0 n T rest hT hp hs hm hn
  obtain ⟨c1, c2, hc1, hc2, rfl⟩ := compileArgs_cons hc
  have r1 := ih ctx q d c1 hc1 p hA.left hF hN s0 n T rest hT hp hs hm hn
  rw [he] at r1
  obtain ⟨hl1, hv1, g1⟩ := r1
  dsimp only at hv1 g1
  rw [evals, he]
  dsimp only
  rw [he']
  dsimp only
  have r2 : ∀ s1, Is s1 (p + size c1) (vs1 ++ s0.stack) st1.mem →
      EvalPost prog inp ρ s1 st1.reads st1 1 (p + size c1 + size c2)
        ((eval inp ρ fs st1 e).val, (eval inp ρ fs st1 e).st) := fun s1 hs1 =>
    ih' ctx (q ++ [es.length]) (d + es.length) 1 c2 hc2 _ hA.right hF (by rw [hN, hv1])
      s1 st1.reads (vs1 ++ T) rest (by simp [hl1, hT]; omega) hs1.1
      (by rw [hs1.2.1, hs, hv1]; simp) hs1.2.2 rfl
  rw [he'] at r2
  have r2' := r2 ⟨p + size c1, vs1 ++ s0.stack, st1.mem, 0⟩ ⟨rfl, rfl, rfl⟩
  have hv2 : st2.vars = st1.vars := r2'.2.1
  have hl2 : vs.length = 1 := r2'.1
  obtain ⟨v, rfl⟩ : ∃ v, vs = [v] := by
    match vs, hl2 with | [v], _ => exact ⟨v, rfl⟩
  refine ⟨by simp [hl1], by rw [hv2, hv1], ?_⟩
  refine (g1.bind fun s1 hs1 => ((r2 s1 hs1).2.2.cast (by simp [Nat.add_assoc]) ?_))
  rw [hs1.2.1]; rfl

theorem sim_args_err2 (he : evals inp ρ fs st es = ⟨.ok vs1, st1, h1⟩)
    (he' : eval inp ρ fs st1 e = ⟨v, st2, h2⟩) (hv : ∀ vs, v = .ok vs → False)
    (ih : M6 prog inp ρ fs st es) (ih' : M5 prog inp ρ fs st1 e) :
    M6 prog inp ρ fs st (e :: es) := by
  intro ctx q d code hc p hA hF hN s0 n T rest hT hp hs hm hn
  obtain ⟨c1, c2, hc1, hc2, rfl⟩ := compileArgs_cons hc
  have r1 := ih ctx q d c1 hc1 p hA.left hF hN s0 n T rest hT hp hs hm hn
  rw [he] at r1
  obtain ⟨hl1, hv1, g1⟩ := r1
  dsimp only at hv1 g1
  have r2 : ∀ s1, Is s1 (p + size c1) (vs1 ++ s0.stack) st1.mem →
      EvalPost prog inp ρ s1 st1.reads st1 1 (p + size c1 + size c2)
        ((eval inp ρ fs st1 e).val, (eval inp ρ fs st1 e).st) := fun s1 hs1 =>
    ih' ctx (q ++ [es.length]) (d + es.length) 1 c2 hc2 _ hA.right hF (by rw [hN, hv1])
      s1 st1.reads (vs1 ++ T) rest (by simp [hl1, hT]; omega) hs1.1
      (by rw [hs1.2.1, hs, hv1]; simp) hs1.2.2 rfl
  rw [he'] at r2
  rw [evals, he]
  dsimp only
  rw [he']
  dsimp only
  cases v with
  | ok vs => exact absurd rfl (hv vs)
  | halt r => exact g1.halts fun s1 hs1 => r2 s1 hs1
  | timeout => exact g1.survives fun s1 hs1 => r2 s1 hs1

theorem sim_args_err1 (he : evals inp ρ fs st es = ⟨v, st1, h1⟩) (hv : ∀ vs, v = .ok vs → False)
    (ih : M6 prog inp ρ fs st es) : M6 prog inp ρ fs st (e :: es) := by
  intro ctx q d code hc p hA hF hN s0 n T rest hT hp hs hm hn
  obtain ⟨c1, c2, hc1, hc2, rfl⟩ := compileArgs_cons hc
  have r1 := ih ctx q d c1 hc1 p hA.left hF hN s0 n T rest hT hp hs hm hn
  rw [he] at r1
  rw [evals, he]
  dsimp only
  cases v with
  | ok vs => exact absurd rfl (hv vs)
  | halt r => exact r1
  | timeout => exact r1

end Compiler
