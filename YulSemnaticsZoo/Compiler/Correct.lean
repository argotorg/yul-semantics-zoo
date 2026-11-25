import YulSemnaticsZoo.Compiler.Lemmas.Main
import YulSemnaticsZoo.Yul.Semantics.Clocked.Theorems
import YulSemnaticsZoo.EVM.Semantics.Clocked.Gas

set_option doc.verso true

/-!
# Compiler: correctness

Obligation 1 of {lit}`doc/gas-equivalence.md` for {lit}`compile`: if the compiler gives code, the
code and the object have the same behaviour for each input {lit}`i` and each readings
{lit}`ρ`. There is no condition on the run: the compiler rejects each builtin that the semantics
does not define.

The proof is a forward simulation (in {lit}`YulSemnaticsZoo/Compiler/Lemmas`). For each
function of the interpreter, the EVM run of the compiled code gives the same outcome, after at
least as many steps as the Yul clock decreases. This gives two statements:

* (Fwd-Ends) {lit}`fwd_ends`: if the Yul run with clock {lit}`k` ends with {lit}`r`, then the EVM
  run ends with {lit}`r` for some clock.
* (Fwd-Timeout) {lit}`fwd_timeout`: if the Yul run with clock {lit}`k` times out, then the EVM run
  with clock {lit}`k` times out.

With (Total) of Yul and (Det) of the EVM, they give the two directions of the equivalence: if Yul
ends, the EVM ends with the same result; if Yul diverges, the EVM diverges; and the EVM has only
one behaviour.
-/

namespace Yul.Clocked

/-- {lit}`P ≈ Q`: the two objects have the same behaviour for each input and each readings -/
def Equiv (P Q : Object) : Prop := ∀ i ρ b, ⟪P, i, ρ⟫ ⇝ b ↔ ⟪Q, i, ρ⟫ ⇝ b

instance : HasEquiv Object := ⟨Equiv⟩

end Yul.Clocked

namespace EVM

/-- {lit}`B ≈ₑ C`: the two programs have the same behaviour for each input and each readings.
The notation is not {lit}`≈`: Lean has {lit}`≈` on lists already (the permutations). -/
def Equiv (B C : List UInt8) : Prop := ∀ i ρ b, ⟪B, i, ρ⟫ ⇝ b ↔ ⟪C, i, ρ⟫ ⇝ b

@[inherit_doc] scoped infix:50 " ≈ₑ " => EVM.Equiv

end EVM

namespace Compiler
open Semantics Yul.Clocked EVM

/-- the EVM code {name}`B` and the Yul object {name}`P` have the same behaviour for each input and
each readings -/
def Equiv (B : List UInt8) (P : Yul.Object) : Prop :=
  ∀ i ρ b, (⟪B, i, ρ⟫ ⇝ b ↔ ⟪P, i, ρ⟫ ⇝ b)

theorem compileE_of_compile (h : compile P = some B) : compileE P = .ok B := by
  unfold compile at h
  cases e : compileE P <;> simp_all [Except.toOption]

/-- Obligation 1: the code of the compiler has the behaviour of the object -/
theorem compile_correct (h : compile P = some B) : Equiv B P := by
  have hc := compileE_of_compile h
  -- each Yul behaviour is an EVM behaviour
  have fwd : ∀ i ρ b, ⟪P, i, ρ⟫ ⇝ b → ⟪B, i, ρ⟫ ⇝ b := by
    intro i ρ b hb
    cases b with
    | ends r =>
      obtain ⟨k, hk⟩ := hb
      exact fwd_ends hc hk
    | diverges => exact fun k => fwd_timeout hc (hb k)
  intro i ρ b
  refine ⟨fun hb => ?_, fwd i ρ b⟩
  obtain ⟨b', hb'⟩ := Yul.Clocked.total (P := P) (i := i) (ρ := ρ)
  rw [Runs.det hb (fwd i ρ b' hb')]
  exact hb'

/-- the compiler keeps the equivalence: equivalent objects give equivalent code -/
theorem compile_congr (hPQ : P ≈ Q) (hP : compile P = some B) (hQ : compile Q = some C) :
    B ≈ₑ C := fun i ρ b =>
  (compile_correct hP i ρ b).trans ((hPQ i ρ b).trans (compile_correct hQ i ρ b).symm)

/-- With obligation 3 for the code {name}`B` (the hypothesis {name}`h3`): if the concrete run of
{name}`B` with gas {name}`g` halts with {name}`r`, then the object ends with {name}`r` for the
readings of that run. -/
theorem compile_concrete
    (h3 : ∀ i g r, result_C B i g = some r → ⟪B, i, reads B i g⟫ ⇝ .ends r)
    (hP : compile P = some B) (hr : result_C B i g = some r) : ⟪P, i, reads B i g⟫ ⇝ .ends r :=
  (compile_correct hP i (reads B i g) (.ends r)).mp (h3 i g r hr)

end Compiler
