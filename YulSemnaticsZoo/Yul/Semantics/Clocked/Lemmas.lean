import YulSemnaticsZoo.Yul.Semantics.Clocked.Tactic

set_option doc.verso true

/-!
# Yul: the clocked semantics is monotone in the clock

{lit}`mono`: if a function of the interpreter gives an outcome that is not a timeout, then with
{lit}`d` more clock at the start it gives the same outcome and the same state, with {lit}`d` more
clock at the end.

The proof is by the functional induction of the interpreter. In each case, it unfolds one step
on the two sides. Then it rewrites each recursive call with its equation from the induction
({lit}`rw_res`), and each recursive call with more clock with its induction hypothesis
({lit}`rw_ih`), until the matches of the interpreter reduce. A match of the interpreter can
have a proof about the result of a recursive call, thus {lit}`simp` cannot rewrite the result
there, but {lit}`rw` of the full result can.

At a loop iteration and a call, the state has 1 less clock. With the clock {lit}`c + 1`, the
state with {lit}`d` more clock and 1 less clock has the clock {lit}`d + (c + 1) - 1`, which is
{lit}`d + c` by definition ({lit}`subst_clock`). Thus {lit}`State.addClock` adds {lit}`d` at the
left.
-/

namespace Yul.Clocked
open Semantics

/-- the state with {name}`d` more clock -/
abbrev State.addClock (st : State) (d : Nat) : State := { st with clock := d + st.clock }

/-- the result with {name}`d` more clock at the end -/
abbrev Res.shift (d : Nat) (r : Res c α Q) : Res (d + c) α Q :=
  ⟨r.val, r.st.addClock d, Nat.add_le_add_left r.le d, r.post⟩

theorem Values.outcome_eq_timeout {v : Values} : v.outcome = .timeout ↔ v = .timeout := by
  cases v <;> simp [Values.outcome]

variable (i : Input) (ρ : Readings) (N : List String)

/-- a builtin does not use the clock -/
theorem builtin_addClock :
    builtin i ρ b vs h (st.addClock d) = (builtin i ρ b vs h st).shift d := by
  cases b <;> rfl

set_option hygiene false in
/-- the premise of an induction hypothesis: the result is not a timeout -/
macro "mono_premise" : tactic => `(tactic| first
  | (rw_res; simp; done)
  | ((try rw_res); simpa [Res.up, Res.shift, Values.outcome_eq_timeout] using hnt))

-- 57 cases, each with some rewrites of large terms
set_option maxHeartbeats 1000000 in
theorem mono :
    (∀ fs st Γ s h hI d, (exec i ρ N fs st Γ s h hI).val ≠ .timeout →
      exec i ρ N fs (st.addClock d) Γ s h hI = (exec i ρ N fs st Γ s h hI).shift d) ∧
    (∀ fs st Γ c post body hc hb hp hl hI d,
      (loop i ρ N fs st Γ c post body hc hb hp hl hI).val ≠ .timeout →
      loop i ρ N fs (st.addClock d) Γ c post body hc hb hp hl hI =
        (loop i ρ N fs st Γ c post body hc hb hp hl hI).shift d) ∧
    (∀ fs st Γ b h hI d, (execBlock i ρ N fs st Γ b h hI).val ≠ .timeout →
      execBlock i ρ N fs (st.addClock d) Γ b h hI = (execBlock i ρ N fs st Γ b h hI).shift d) ∧
    (∀ fs st Γ ss h hI d, (execs i ρ N fs st Γ ss h hI).val ≠ .timeout →
      execs i ρ N fs (st.addClock d) Γ ss h hI = (execs i ρ N fs st Γ ss h hI).shift d) ∧
    (∀ fs st Γ e n h hI d, (eval i ρ N fs st Γ e n h hI).val ≠ .timeout →
      eval i ρ N fs (st.addClock d) Γ e n h hI = (eval i ρ N fs st Γ e n h hI).shift d) ∧
    (∀ fs st Γ es h hI d, (evals i ρ N fs st Γ es h hI).val ≠ .timeout →
      evals i ρ N fs (st.addClock d) Γ es h hI = (evals i ρ N fs st Γ es h hI).shift d) := by
  apply exec.mutual_induct i ρ N
  all_goals
    intros
    rename_i d hnt
    -- at a loop iteration or a call: the clock is c + 1
    try subst_clock
    -- one step on the two sides and in the hypothesis that the outcome is not a timeout
    first
    | rw [loop] at hnt; (conv => lhs; rw [loop]); (conv => rhs; rw [loop])
    | rw [exec] at hnt; rw [exec, exec]
    | rw [execBlock] at hnt; rw [execBlock, execBlock]
    | rw [execs] at hnt; rw [execs, execs]
    | rw [eval] at hnt; rw [eval, eval]
    | rw [evals] at hnt; rw [evals, evals]
  -- rewrite until the matches reduce; the equations also rewrite `hnt`
  all_goals
    repeat (first
      | exact absurd rfl hnt
      | rw_ih d using mono_premise
      | (revert hnt; rw_res; intro hnt)
      | (revert hnt; rw_cases; intro hnt)
      | simp_conds
      | rw [builtin_addClock]
      | dsimp_res [Res.shift, Res.up])
    try rfl

end Yul.Clocked
