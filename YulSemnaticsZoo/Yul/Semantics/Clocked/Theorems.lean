import YulSemnaticsZoo.Yul.Semantics.Clocked.Lemmas

set_option doc.verso true

/-!
# Yul: theorems of the clocked semantics

(Mono), (Det) and (Total) of {lit}`doc/gas-equivalence.md` for {lit}`Yul.Clocked`.

{lit}`st.addClock d` is the state {lit}`st` with {lit}`d` more clock, and {lit}`r.shift d` is the
result {lit}`r` with {lit}`d` more clock at the end. The proof of (Mono) for each function of the
interpreter is in {lit}`YulSemnaticsZoo/Yul/Semantics/Clocked/Lemmas.lean`.
-/

namespace Yul.Clocked
open Semantics

variable {P : Object} {i : Input} {ρ : Readings}

/-- (Mono) for a statement: if the statement gives an outcome that is not a timeout, then with
{name}`d` more clock at the start it gives the same outcome and the same state, with {name}`d` more
clock at the end -/
theorem exec_mono (fs : Funs) (st : State) (s : Statement) (d : Nat)
    (h : (exec i ρ fs st s).val ≠ .timeout) :
    exec i ρ fs (st.addClock d) s = (exec i ρ fs st s).shift d :=
  (mono i ρ).1 fs st s d h

/-- (Mono) for a block -/
theorem execBlock_mono (fs : Funs) (st : State) (b : Block) (d : Nat)
    (h : (execBlock i ρ fs st b).val ≠ .timeout) :
    execBlock i ρ fs (st.addClock d) b = (execBlock i ρ fs st b).shift d :=
  (mono i ρ).2.2.1 fs st b d h

/-- (Mono) for a run: a larger clock gives the same result -/
theorem run_mono (h : run P i ρ k = some r) (hk : k ≤ k') : run P i ρ k' = some r := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hnt : (execBlock i ρ [] (start k) P.code).val ≠ .timeout := by
    intro ht
    simp [run, top, ht, Outcome.result] at h
  have hm := execBlock_mono [] (start k) P.code d hnt
  simp only [run, top] at h ⊢
  rw [show start (k + d) = (start k).addClock d from rfl, hm]
  exact h

/-- (Det): a run has at most one behaviour -/
theorem det (h : ⟪P, i, ρ⟫ ⇝ b) (h' : ⟪P, i, ρ⟫ ⇝ b') : b = b' := by
  cases b <;> cases b' <;> simp only [Behaves] at h h'
  · obtain ⟨k, hk⟩ := h
    obtain ⟨k', hk'⟩ := h'
    have := (run_mono hk (Nat.le_max_left k k')).symm.trans (run_mono hk' (Nat.le_max_right k k'))
    simp_all
  · obtain ⟨k, hk⟩ := h
    simp_all
  · obtain ⟨k, hk⟩ := h'
    simp_all
  · rfl

/-- {name}`beh` is a behaviour of the run -/
theorem behaves_beh : ⟪P, i, ρ⟫ ⇝ beh P i ρ := by
  unfold beh
  split
  · next h => exact h.choose_spec
  · next h =>
    intro k
    cases hk : run P i ρ k
    · rfl
    · exact absurd ⟨_, k, hk⟩ h

/-- (Total): a run has a behaviour -/
theorem total : ∃ b, ⟪P, i, ρ⟫ ⇝ b := ⟨_, behaves_beh⟩

/-- {name}`beh` is the behaviour of the run -/
theorem beh_eq (h : ⟪P, i, ρ⟫ ⇝ b) : beh P i ρ = b := det behaves_beh h

end Yul.Clocked
