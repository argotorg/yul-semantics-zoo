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

variable {P : WFObject} {i : Input} {ρ : Readings} {N : List String}

/-- (Mono) for a statement: if the statement gives an outcome that is not a timeout, then with
{name}`d` more clock at the start it gives the same outcome and the same state, with {name}`d` more
clock at the end -/
theorem exec_mono (fs : Funs) (st : State) (Γ : Scope) (s : Statement)
    (h : s.WellFormed EVM.dialect N Γ) (hI : Agrees N fs st.vars Γ) (d : Nat)
    (hnt : (exec i ρ N fs st Γ s h hI).val ≠ .timeout) :
    exec i ρ N fs (st.addClock d) Γ s h hI = (exec i ρ N fs st Γ s h hI).shift d :=
  (mono i ρ N).1 fs st Γ s h hI d hnt

/-- (Mono) for a block -/
theorem execBlock_mono (fs : Funs) (st : State) (Γ : Scope) (b : Block)
    (h : b.WellFormed EVM.dialect N Γ) (hI : Agrees N fs st.vars Γ) (d : Nat)
    (hnt : (execBlock i ρ N fs st Γ b h hI).val ≠ .timeout) :
    execBlock i ρ N fs (st.addClock d) Γ b h hI = (execBlock i ρ N fs st Γ b h hI).shift d :=
  (mono i ρ N).2.2.1 fs st Γ b h hI d hnt

/-- (Mono) for the code of an object -/
theorem top_mono (hnt : (top P i ρ k).val ≠ .timeout) :
    top P i ρ (d + k) = (top P i ρ k).shift d :=
  execBlock_mono [] (start k) {} P.1.code _ _ d hnt

/-- (Mono) for a run: a larger clock gives the same result -/
theorem run_mono (h : run P i ρ k = some r) (hk : k ≤ k') : run P i ρ k' = some r := by
  obtain ⟨d, rfl⟩ : ∃ d, k' = d + k := ⟨k' - k, by omega⟩
  have hnt : (top P i ρ k).val ≠ .timeout := fun ht => by
    simp [run, Res.result_eq_none.mpr ht] at h
  unfold run
  rw [top_mono hnt]
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
