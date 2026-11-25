import YulSemnaticsZoo.EVM.Semantics.Clocked.Gas

set_option doc.verso true

/-!
# EVM: the concrete run refines the abstract run

Obligation 3 of {lit}`doc/gas-equivalence.md`: if the concrete run halts with {lit}`r`, then the
abstract run with the readings of the concrete run halts with {lit}`r`.

The proof is a simulation. The two runs have the same state. The abstract gas state is the number
of reads, and the concrete meter records the reads. Thus the abstract gas state is the length of
the record. A concrete step that does not fail gives the same step in the abstract model, if the
readings agree with the record of the concrete run at its end.
-/

namespace EVM
open Semantics

/-- the readings {name}`ρ` agree with the reads {name}`l` at each position of {name}`l` -/
def Agrees (ρ : Readings) (l : List Word) : Prop := ∀ j (h : j < l.length), ρ j = l[j]

/-- readings that agree with a list agree with each prefix of it -/
theorem Agrees.prefix (h : Agrees ρ l') (hp : l <+: l') : Agrees ρ l := fun j hj => by
  rw [h j (by have := hp.length_le; omega), hp.getElem]

/-- a concrete step that halts reads no value, and the abstract step halts with the same
result -/
theorem step_refines_halt (h : step concrete code i s m = .halt r m') :
    m'.reads = m.reads ∧ step (abstract ρ) code i s m.reads.length = .halt r m.reads.length := by
  unfold step at h ⊢
  rcases hf : fetch code s.pc with r₀ | ins <;> simp only [hf] at h ⊢
  · cases h; simp
  by_cases ha : s.stack.length < ins.arity.1 <;> simp only [ha, ite_true, ite_false] at h ⊢
  · cases h; simp
  by_cases hl : 1024 < s.stack.length - ins.arity.1 + ins.arity.2 <;>
    simp [concrete, abstract, hl] at h ⊢
  by_cases hc : cost ins s ≤ m.gas <;> simp only [hc, ite_true, ite_false, reduceCtorEq] at h
  rcases he : exec code i ins { s with words := max s.words (ins.memWords s.stack) }
    with s₁ | r₁ | k₁ <;> simp only [he] at h ⊢
  · cases h
  · cases h; simp
  · cases h

/-- a concrete step that does not halt reads at most one value, and the abstract step gives the
same state, if {name}`ρ` agrees with the reads after the step -/
theorem step_refines_next (h : step concrete code i s m = .next s' m')
    (hρ : Agrees ρ m'.reads) :
    m.reads <+: m'.reads ∧
      step (abstract ρ) code i s m.reads.length = .next s' m'.reads.length := by
  unfold step at h ⊢
  rcases hf : fetch code s.pc with r₀ | ins <;> simp only [hf] at h ⊢
  · cases h
  by_cases ha : s.stack.length < ins.arity.1 <;> simp only [ha, ite_true, ite_false] at h ⊢
  · cases h
  by_cases hl : 1024 < s.stack.length - ins.arity.1 + ins.arity.2 <;>
    simp [concrete, abstract, hl] at h ⊢
  by_cases hc : cost ins s ≤ m.gas <;> simp only [hc, ite_true, ite_false, reduceCtorEq] at h
  rcases he : exec code i ins { s with words := max s.words (ins.memWords s.stack) }
    with s₁ | r₁ | k₁ <;> simp only [he] at h ⊢
  · cases h; simp
  · cases h
  · cases h
    have := hρ m.reads.length (by simp)
    simp_all

/-- The simulation: a concrete run that halts reads more values, and the abstract run with the
same clock halts with the same result, if {name}`ρ` agrees with the reads at the halt. The
abstract gas state at the halt is the number of reads. -/
theorem run_refines (h : run concrete code i k s m = .halt r m') (hρ : Agrees ρ m'.reads) :
    m.reads <+: m'.reads ∧
      run (abstract ρ) code i k s m.reads.length = .halt r m'.reads.length := by
  induction k generalizing s m with
  | zero => simp [run] at h
  | succ k ih =>
    simp only [run] at h ⊢
    split at h
    · next s₁ m₁ hs =>
      obtain ⟨hp, hr⟩ := ih h
      obtain ⟨hp₁, hs₁⟩ := step_refines_next hs (hρ.prefix hp)
      exact ⟨hp₁.trans hp, by rw [hs₁]; exact hr⟩
    · next r₁ m₁ hs =>
      cases h
      obtain ⟨hm, hs₁⟩ := step_refines_halt (ρ := ρ) hs
      exact ⟨hm ▸ List.prefix_refl _, by rw [hs₁, hm]⟩
    · cases h

/-- the readings of a concrete run that halts are the reads of its meter -/
theorem reads_agrees (h : runC code i g = .halt r m) : Agrees (reads code i g) m.reads :=
  fun j hj => by simp [reads, h, hj]

/-- Obligation 3, the strong form: if the concrete run with gas {name}`g` halts with {name}`r`,
then the abstract run with each readings {name}`ρ` that agree with the reads of the concrete run
halts with {name}`r` at the same clock {lit}`g + 1` -/
theorem runA_of_runC (h : runC code i g = .halt r m) (hρ : Agrees ρ m.reads) :
    runA code i ρ (g + 1) = .halt r m.reads.length :=
  (run_refines h hρ).2

/-- Obligation 3: if the concrete run halts with {name}`r`, then the abstract run with the
readings of the concrete run ends with {name}`r` -/
theorem refines (h : result_C code i g = some r) : ⟪code, i, reads code i g⟫ ⇝ .ends r := by
  unfold result_C at h
  split at h
  · next r₁ m hc =>
    cases h
    exact ⟨g + 1, m.reads.length, runA_of_runC hc (reads_agrees hc)⟩
  · simp at h

end EVM
