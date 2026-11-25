import YulSemnaticsZoo.Compiler.Lemmas.SimLoop

set_option doc.verso true

/-!
# Compiler: the simulation, and the forward theorems

{lit}`sim` collects the cases. {lit}`fwd_ends` and {lit}`fwd_timeout` are the two forward
statements of the proof plan: a Yul result gives the same EVM result, and a Yul timeout at the
clock {lit}`k` gives an EVM timeout at the same clock.
-/

namespace Compiler
open Semantics Yul Yul.Clocked

variable {prog : Code} {inp : Input} {ρ : Readings}

theorem sim (hg : Good prog) :
    (∀ fs st s, M1 prog inp ρ fs st s) ∧ (∀ fs st c post body, M2 prog inp ρ fs st c post body) ∧
    (∀ fs st b, M3 prog inp ρ fs st b) ∧ (∀ fs st ss, M4 prog inp ρ fs st ss) ∧
    (∀ fs st e, M5 prog inp ρ fs st e) ∧ (∀ fs st es, M6 prog inp ρ fs st es) := by
  apply exec.mutual_induct inp ρ
  case case1 => intro fs st b ih; exact sim_block ih
  case case2 => intro fs st f ps rs body; exact sim_fundef hg
  case case3 => intro fs st xs; exact sim_let_none
  case case4 => intro fs st xs e st1 h1 vs he ih; exact sim_let he ih
  case case5 => intro fs st xs e st1 h1 v hv he ih; exact sim_let_err he hv ih
  case case6 => intro fs st xs e st1 h1 vs he ih; exact sim_assign he ih
  case case7 => intro fs st xs e st1 h1 v hv he ih; exact sim_assign_err he hv ih
  case case8 => intro fs st c b st1 h1 vs hz he ih; exact sim_if_zero hg he hz ih
  case case9 => intro fs st c b st1 h1 vs hz he ih ihb; exact sim_if_ne hg he hz ih ihb
  case case10 => intro fs st c b st1 h1 v hv he ih; exact sim_if_err he hv ih
  case case11 => intro fs st e v st1 h1 he ih; exact sim_expr he ih
  case case12 =>
    intro fs st init c post body st2 h2 o st3 h3 hl he ih1 ih2; exact sim_for he hl ih1 ih2
  case case13 =>
    intro fs st init c post body st2 h2 o ho he ih; exact sim_for_init he ho ih
  case case14 => intro fs st; exact sim_break hg
  case case15 => intro fs st; exact sim_continue hg
  case case16 => intro fs st; exact sim_leave hg
  case case17 => intro fs st c post body h0; exact sim_loop_zero h0
  case case18 =>
    intro fs st c post body h0 st1 h1 hc vs hz he ih
    exact sim_loop hg h0 he ih (fun vs' hv hz' => by cases hv; exact absurd hz hz')
      (fun vs' hv hz' => by cases hv; exact absurd hz hz')
      (fun vs' hv hz' => by cases hv; exact absurd hz hz')
  case case19 =>
    intro fs st c post body h0 st1 h1 hc vs hz st2 h2 he hb ihc ihb
    exact sim_loop hg h0 he ihc (fun _ _ _ => ihb)
      (fun _ _ _ hor => by rw [hb] at hor; simp at hor)
      (fun _ _ _ hor => by rw [hb] at hor; simp at hor)
  case case20 =>
    intro fs st c post body h0 st1 h1 hc vs hz st2 h2 st3 h3 he hb hp ihc ihb ihp ihl
    exact sim_loop hg h0 he ihc (fun _ _ _ => ihb) (fun _ _ _ _ => by rw [hb]; exact ihp)
      (fun _ _ _ _ hpn => by rw [hb]; rw [hb] at hpn; dsimp only at hpn ⊢; rw [hp]; exact ihl)
  case case21 =>
    intro fs st c post body h0 st1 h1 hc vs hz st2 h2 st3 h3 he hb hp ihc ihb ihp ihl
    exact sim_loop hg h0 he ihc (fun _ _ _ => ihb) (fun _ _ _ _ => by rw [hb]; exact ihp)
      (fun _ _ _ _ hpn => by rw [hb] at hpn; dsimp only at hpn; rw [hp] at hpn; simp at hpn)
  case case22 =>
    intro fs st c post body h0 st1 h1 hc vs hz st2 h2 st3 h3 he hb hp ihc ihb ihp ihl
    exact sim_loop hg h0 he ihc (fun _ _ _ => ihb) (fun _ _ _ _ => by rw [hb]; exact ihp)
      (fun _ _ _ _ hpn => by rw [hb] at hpn; dsimp only at hpn; rw [hp] at hpn; simp at hpn)
  case case23 =>
    intro fs st c post body h0 st1 h1 hc vs hz st2 h2 st3 h3 o hon hob hoc he hb hp ihc ihb ihp
    exact sim_loop hg h0 he ihc (fun _ _ _ => ihb) (fun _ _ _ _ => by rw [hb]; exact ihp)
      (fun _ _ _ _ hpn => by rw [hb] at hpn; dsimp only at hpn; rw [hp] at hpn; exact absurd hpn hon)
  case case24 =>
    intro fs st c post body h0 st1 h1 hc vs hz st2 h2 st3 h3 he hb hp ihc ihb ihp ihl
    exact sim_loop hg h0 he ihc (fun _ _ _ => ihb) (fun _ _ _ _ => by rw [hb]; exact ihp)
      (fun _ _ _ _ hpn => by rw [hb]; rw [hb] at hpn; dsimp only at hpn ⊢; rw [hp]; exact ihl)
  case case25 =>
    intro fs st c post body h0 st1 h1 hc vs hz st2 h2 st3 h3 he hb hp ihc ihb ihp ihl
    exact sim_loop hg h0 he ihc (fun _ _ _ => ihb) (fun _ _ _ _ => by rw [hb]; exact ihp)
      (fun _ _ _ _ hpn => by rw [hb] at hpn; dsimp only at hpn; rw [hp] at hpn; simp at hpn)
  case case26 =>
    intro fs st c post body h0 st1 h1 hc vs hz st2 h2 st3 h3 he hb hp ihc ihb ihp ihl
    exact sim_loop hg h0 he ihc (fun _ _ _ => ihb) (fun _ _ _ _ => by rw [hb]; exact ihp)
      (fun _ _ _ _ hpn => by rw [hb] at hpn; dsimp only at hpn; rw [hp] at hpn; simp at hpn)
  case case27 =>
    intro fs st c post body h0 st1 h1 hc vs hz st2 h2 st3 h3 o hon hob hoc he hb hp ihc ihb ihp
    exact sim_loop hg h0 he ihc (fun _ _ _ => ihb) (fun _ _ _ _ => by rw [hb]; exact ihp)
      (fun _ _ _ _ hpn => by rw [hb] at hpn; dsimp only at hpn; rw [hp] at hpn; exact absurd hpn hon)
  case case28 =>
    intro fs st c post body h0 st1 h1 hc vs hz st2 h2 o hob hon hoc he hb ihc ihb
    exact sim_loop hg h0 he ihc (fun _ _ _ => ihb)
      (fun _ _ _ hor => by rw [hb] at hor; rcases hor with h | h; exact absurd h hon; exact absurd h hoc)
      (fun _ _ _ hor => by rw [hb] at hor; rcases hor with h | h; exact absurd h hon; exact absurd h hoc)
  case case29 =>
    intro fs st c post body h0 st1 h1 hc v hv he ihc
    exact sim_loop hg h0 he ihc (fun vs h => (hv vs h).elim) (fun vs h => (hv vs h).elim)
      (fun vs h => (hv vs h).elim)
  case case30 => intro fs st ss o st2 h2 he ih; exact sim_execBlock he ih
  case case31 => intro fs st; exact sim_execs_nil
  case case32 => intro fs st s ss st2 h2 he ih1 ih2; exact sim_execs_cons he ih1 ih2
  case case33 => intro fs st s ss st2 h2 o ho he ih; exact sim_execs_stop he ho ih
  case case34 => intro fs st l; exact sim_literal
  case case35 => intro fs st x; exact sim_identifier
  case case36 => intro fs st f args st1 h1 vs kinds mk hb he ih; exact sim_builtin hb he ih
  case case37 => intro fs st f args st1 h1 vs hf hb he ih; exact sim_call_unbound hb hf
  case case38 =>
    intro fs st f args st1 h1 vs fn fs' hf hb h0 he ih
    exact sim_call hg hb hf he ih (fun h => absurd h0 h)
  case case39 =>
    intro fs st f args st1 h1 vs fn fs' hf hb h0 callee st2 h2 h r he hx ih ihb
    exact sim_call hg hb hf he ih (fun _ => ihb)
  case case40 =>
    intro fs st f args st1 h1 vs fn fs' hf hb h0 callee st2 h2 h he hx ih ihb
    exact sim_call hg hb hf he ih (fun _ => ihb)
  case case41 =>
    intro fs st f args st1 h1 vs fn fs' hf hb h0 callee o st2 h2 hx h hh ht he ih ihb
    exact sim_call hg hb hf he ih (fun _ => ihb)
  case case42 => intro fs st f args st1 h1 v hv he ih; exact sim_call_args he hv ih
  case case43 => intro fs st; exact sim_args_nil
  case case44 =>
    intro fs st e es st1 h1 vs1 st2 h2 vs he he' ih ih'; exact sim_args_ok he he' ih ih'
  case case45 =>
    intro fs st e es st1 h1 vs st2 h2 v hv he he' ih ih'; exact sim_args_err2 he he' hv ih ih'
  case case46 => intro fs st e es st1 h1 v hv he ih; exact sim_args_err1 he hv ih

/-! ## The top object -/

theorem assemble_ok (h : assemble prog = .ok B) : Good prog ∧ B = layout prog := by
  rw [assemble] at h
  inv h
  obtain ⟨hn, hs, h⟩ := h
  exact ⟨⟨hn, hs⟩, h.symm⟩

theorem compileE_ok (h : compileE P = .ok B) :
    ∃ c, compileBlock { vars := [], funs := [] } [] P.code = .ok c ∧
      Good (c ++ [.op .Stop]) ∧ B = layout (c ++ [.op .Stop]) := by
  rw [compileE] at h
  inv h
  obtain ⟨-, c, hc, ha⟩ := h
  exact ⟨c, hc, assemble_ok ha⟩

/-- the compiled code of the top object simulates the Yul run -/
theorem top_post (hc : compileBlock { vars := [], funs := [] } [] P.code = .ok c)
    (hg : Good (c ++ [.op .Stop])) :
    StmtPost (c ++ [.op .Stop]) inp ρ { vars := [], funs := [] } EVM.State.init 0 (start k)
      (0 + size c) [] (top P inp ρ k) :=
  (sim hg).2.2.1 [] (start k) P.code { vars := [], funs := [] } [] c hc 0
    ⟨[], [.op .Stop], by simp, rfl⟩ EVM.State.init 0 [] rfl
    { funs := trivial
      names := rfl
      loop := by simp
      leave := by simp
      stack := rfl
      mem := rfl
      reads := rfl }

theorem result_eq_none {o : Outcome} : o.result = none ↔ o = .timeout := by
  cases o <;> simp [Outcome.result]

/-- (Fwd-Ends): if the Yul run with clock {name}`k` ends with {name}`r`, then the EVM run ends with
{name}`r` -/
theorem fwd_ends (h : compileE P = .ok B) (hr : run P i ρ k = some r) :
    ∃ k' n, EVM.runA B i ρ k' = .halt r n := by
  obtain ⟨c, hc, hg, rfl⟩ := compileE_ok h
  have ht := top_post (inp := i) (ρ := ρ) (k := k) hc hg
  unfold run at hr
  revert ht hr
  generalize top P i ρ k = t
  obtain ⟨o, st'⟩ := t
  intro hr ht
  apply Halts.run
  cases o with
  | normal =>
    simp [Outcome.result] at hr; subst hr
    obtain ⟨j, s', hst, hs, -⟩ := ht
    exact ⟨j, s', _, _, hst, st_stop (c := []) (by rw [hs.1]; exact ⟨c, [], by simp, by simp⟩)⟩
  | brk => obtain ⟨l, lc, d, h, -⟩ := ht; simp at h
  | cont => obtain ⟨l, lc, d, h, -⟩ := ht; simp at h
  | leave => obtain ⟨l, d, h, -⟩ := ht; simp at h
  | halt r' => simp [Outcome.result] at hr; subst hr; exact ht
  | timeout => simp [Outcome.result] at hr

/-- (Fwd-Timeout): if the Yul run with clock {name}`k` times out, then the EVM run with clock
{name}`k` times out -/
theorem fwd_timeout (h : compileE P = .ok B) (hr : run P i ρ k = none) :
    EVM.runA B i ρ k = .timeout := by
  obtain ⟨c, hc, hg, rfl⟩ := compileE_ok h
  have ht := top_post (inp := i) (ρ := ρ) (k := k) hc hg
  unfold run at hr
  rw [result_eq_none] at hr
  revert ht hr
  generalize top P i ρ k = t
  obtain ⟨o, st'⟩ := t
  intro hr ht
  subst hr
  exact Survives.run ht

end Compiler
