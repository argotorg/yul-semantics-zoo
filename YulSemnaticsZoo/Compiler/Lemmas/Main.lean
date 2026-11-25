import YulSemnaticsZoo.Compiler.Lemmas.SimLoop

set_option doc.verso true

/-!
# Compiler: the simulation, and the forward theorems

{lit}`sim` collects the cases: for each case of the functional induction, {lit}`sim_case` finds
the lemma whose premises are the hypotheses of the case. {lit}`fwd_ends` and {lit}`fwd_timeout`
are the two forward statements of the proof plan: a Yul result gives the same EVM result, and a
Yul timeout at the clock {lit}`k` gives an EVM timeout at the same clock.
-/

namespace Compiler
open Semantics Yul Yul.Clocked

variable {prog : Code} {inp : Input} {ρ : Readings} {N : List String}

/-- apply the lemma {lit}`l`, and prove its premises with the hypotheses of the case: an
equation or an induction hypothesis, or a fact about constructors -/
macro "sim_by " l:term : tactic => `(tactic| (apply $l <;> first
  | assumption
  | (intro _ h; cases h; done)
  | (simp; done)))

theorem sim (hg : Good prog) :
    (∀ fs st Γ s h hI, M1 prog inp ρ N fs st Γ s h hI) ∧
    (∀ fs st Γ c post body hc hb hp hl hI, M2 prog inp ρ N fs st Γ c post body hc hb hp hl hI) ∧
    (∀ fs st Γ b h hI, M3 prog inp ρ N fs st Γ b h hI) ∧
    (∀ fs st Γ ss h hI, M4 prog inp ρ N fs st Γ ss h hI) ∧
    (∀ fs st Γ e n h hI, M5 prog inp ρ N fs st Γ e n h hI) ∧
    (∀ fs st Γ es h hI, M6 prog inp ρ N fs st Γ es h hI) := by
  apply exec.mutual_induct inp ρ N
  all_goals intros
  all_goals first
    | sim_by sim_block
    | sim_by sim_fundef hg
    | sim_by sim_let_none
    | sim_by sim_let
    | sim_by sim_let_err
    | sim_by sim_assign
    | sim_by sim_assign_err
    | sim_by sim_if_zero hg
    | sim_by sim_if_ne hg
    | sim_by sim_if_err
    | sim_by sim_expr
    | sim_by sim_for
    | sim_by sim_for_init
    | sim_by sim_break hg
    | sim_by sim_continue hg
    | sim_by sim_leave hg
    | sim_by sim_execBlock
    | sim_by sim_execs_nil
    | sim_by sim_execs_cons
    | sim_by sim_execs_stop
    | sim_by sim_loop_zero
    | sim_by sim_loop_false hg
    | sim_by sim_loop_cond_err
    | sim_by sim_loop_brk hg
    | sim_by sim_loop_stop hg
    | sim_by sim_loop_post_stop hg
    | sim_by sim_loop_next hg
    | sim_by sim_literal
    | sim_by sim_identifier
    | sim_by sim_builtin
    | sim_by sim_builtin_args
    | sim_by sim_call hg
    | sim_by sim_call_zero
    | sim_by sim_call_args
    | sim_by sim_args_nil
    | sim_by sim_args_ok
    | sim_by sim_args_err2
    | sim_by sim_args_err1

/-! ## The top object -/

theorem assemble_ok (h : assemble prog = .ok B) : Good prog ∧ B = layout prog := by
  rw [assemble] at h
  inv h
  obtain ⟨hn, hs, h⟩ := h
  exact ⟨⟨hn, hs⟩, h.symm⟩

theorem compileE_ok {P : WFObject} (h : compileE P = .ok B) :
    ∃ c, compileBlock { vars := [], funs := [] } [] P.1.code = .ok c ∧
      Good (c ++ [.op .Stop]) ∧ B = layout (c ++ [.op .Stop]) := by
  rw [compileE] at h
  inv h
  obtain ⟨c, hc, ha⟩ := h
  exact ⟨c, hc, assemble_ok ha⟩

/-- the compiled code of the top object simulates the Yul run -/
theorem top_post {P : WFObject} (hc : compileBlock { vars := [], funs := [] } [] P.1.code = .ok c)
    (hg : Good (c ++ [.op .Stop])) :
    StmtPost (c ++ [.op .Stop]) inp ρ { vars := [], funs := [] } EVM.State.init 0 (start k)
      (0 + size c) [] ((top P inp ρ k).val, (top P inp ρ k).st) :=
  (sim (N := P.1.dataNames) hg).2.2.1 [] (start k) {} P.1.code _ _ { vars := [], funs := [] } [] c
    hc 0 ⟨[], [.op .Stop], by simp, rfl⟩ EVM.State.init 0 [] rfl
    { funs := trivial
      names := rfl
      loop := by simp
      leave := by simp
      stack := rfl
      mem := rfl
      reads := rfl }

/-- (Fwd-Ends): if the Yul run with clock {name}`k` ends with {name}`r`, then the EVM run ends with
{name}`r` -/
theorem fwd_ends {P : WFObject} (h : compileE P = .ok B) (hr : run P i ρ k = some r) :
    ∃ k' n, EVM.runA B i ρ k' = .halt r n := by
  obtain ⟨c, hc, hg, rfl⟩ := compileE_ok h
  have ht := top_post (inp := i) (ρ := ρ) (k := k) hc hg
  unfold run at hr
  revert ht hr
  generalize top P i ρ k = t
  obtain ⟨o, st', le, post⟩ := t
  intro hr ht
  apply Halts.run
  cases o with
  | normal =>
    simp [Res.result, Outcome.result] at hr; subst hr
    obtain ⟨j, s', hst, hs, -⟩ := ht
    exact ⟨j, s', _, _, hst, st_stop (c := []) (by rw [hs.1]; exact ⟨c, [], by simp, by simp⟩)⟩
  | brk => exact absurd post.fits (by simp [Outcome.Fits])
  | cont => exact absurd post.fits (by simp [Outcome.Fits])
  | leave => exact absurd post.fits (by simp [Outcome.Fits])
  | halt r' => simp [Res.result, Outcome.result] at hr; subst hr; exact ht
  | timeout => simp [Res.result, Outcome.result] at hr

/-- (Fwd-Timeout): if the Yul run with clock {name}`k` times out, then the EVM run with clock
{name}`k` times out -/
theorem fwd_timeout {P : WFObject} (h : compileE P = .ok B) (hr : run P i ρ k = none) :
    EVM.runA B i ρ k = .timeout := by
  obtain ⟨c, hc, hg, rfl⟩ := compileE_ok h
  have ht := top_post (inp := i) (ρ := ρ) (k := k) hc hg
  unfold run at hr
  rw [Res.result_eq_none] at hr
  revert ht hr
  generalize top P i ρ k = t
  obtain ⟨o, st', le, post⟩ := t
  intro hr ht
  dsimp only at hr
  subst hr
  exact Survives.run ht

end Compiler
