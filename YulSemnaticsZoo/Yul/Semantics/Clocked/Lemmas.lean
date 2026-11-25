import YulSemnaticsZoo.Yul.Semantics.Clocked.Interp

set_option doc.verso true

/-!
# Yul: the clocked semantics is monotone in the clock

{lit}`mono`: if a function of the interpreter gives an outcome that is not a timeout, then with
{lit}`d` more clock at the start it gives the same outcome and the same state, with {lit}`d` more
clock at the end.

The proof is by the functional induction of the interpreter. In each case, it unfolds one step
on the two sides, and then rewrites the results of the recursive calls with the equations and the
induction hypotheses. The type of a result ({lit}`Res st.clock`) depends on the state at the
start, thus {lit}`simp` cannot rewrite the state in a term such as
{lit}`(execBlock i ρ fs st b).val`. Thus the proof first changes each such term to a function
without this dependency ({lit}`execBlockP` and the others).
-/

namespace Yul.Clocked
open Semantics

/-- the state with {name}`d` more clock -/
abbrev State.addClock (st : State) (d : Nat) : State := { st with clock := st.clock + d }

/-- the result with {name}`d` more clock at the end -/
def Res.shift (d : Nat) (r : Res c α) : Res (c + d) α :=
  ⟨r.val, r.st.addClock d, Nat.add_le_add_right r.le d⟩

theorem Res.eq_iff_pair {r r' : Res c α} : r = r' ↔ (r.val, r.st) = (r'.val, r'.st) := by
  cases r; cases r'; simp

theorem Values.outcome_eq_timeout {v : Values} : v.outcome = .timeout ↔ v = .timeout := by
  cases v <;> simp [Values.outcome]

theorem restrict_addClock {st st' : State} :
    restrict (st.addClock d) (st'.addClock d) = (restrict st st').addClock d := rfl

/-- the state at a loop iteration or a function call, with {name}`d` more clock -/
theorem mk_pred {c : Nat} (h : ¬c = 0) :
    State.mk vs m r (c + d - 1) = State.addClock (State.mk vs m r (c - 1)) d := by
  simp only [State.addClock, State.mk.injEq, true_and]; omega

variable (i : Input) (ρ : Readings)

/-! The functions of the interpreter, with a result type that does not depend on the arguments -/

def builtinP b vs st := ((builtin i ρ b vs st).val, (builtin i ρ b vs st).st)
def execP fs st s := ((exec i ρ fs st s).val, (exec i ρ fs st s).st)
def loopP fs st c post body := ((loop i ρ fs st c post body).val, (loop i ρ fs st c post body).st)
def execBlockP fs st b := ((execBlock i ρ fs st b).val, (execBlock i ρ fs st b).st)
def execsP fs st ss := ((execs i ρ fs st ss).val, (execs i ρ fs st ss).st)
def evalP fs st e := ((eval i ρ fs st e).val, (eval i ρ fs st e).st)
def evalsP fs st es := ((evals i ρ fs st es).val, (evals i ρ fs st es).st)

theorem builtin_val : (builtin i ρ b vs st).val = (builtinP i ρ b vs st).1 := rfl
theorem builtin_st : (builtin i ρ b vs st).st = (builtinP i ρ b vs st).2 := rfl
theorem exec_val : (exec i ρ fs st s).val = (execP i ρ fs st s).1 := rfl
theorem exec_st : (exec i ρ fs st s).st = (execP i ρ fs st s).2 := rfl
theorem loop_val : (loop i ρ fs st c post body).val = (loopP i ρ fs st c post body).1 := rfl
theorem loop_st : (loop i ρ fs st c post body).st = (loopP i ρ fs st c post body).2 := rfl
theorem execBlock_val : (execBlock i ρ fs st b).val = (execBlockP i ρ fs st b).1 := rfl
theorem execBlock_st : (execBlock i ρ fs st b).st = (execBlockP i ρ fs st b).2 := rfl
theorem execs_val : (execs i ρ fs st ss).val = (execsP i ρ fs st ss).1 := rfl
theorem execs_st : (execs i ρ fs st ss).st = (execsP i ρ fs st ss).2 := rfl
theorem eval_val : (eval i ρ fs st e).val = (evalP i ρ fs st e).1 := rfl
theorem eval_st : (eval i ρ fs st e).st = (evalP i ρ fs st e).2 := rfl
theorem evals_val : (evals i ρ fs st es).val = (evalsP i ρ fs st es).1 := rfl
theorem evals_st : (evals i ρ fs st es).st = (evalsP i ρ fs st es).2 := rfl

/-- a builtin does not use the clock -/
theorem builtinP_addClock : builtinP i ρ b vs (st.addClock d) =
    ((builtinP i ρ b vs st).1, (builtinP i ρ b vs st).2.addClock d) := by
  rcases b with _ | b
  · rfl
  · cases b <;> rfl

-- each case uses only some of the lemmas
set_option linter.unusedSimpArgs false in
theorem mono :
    (∀ fs st s d, (exec i ρ fs st s).val ≠ .timeout →
      exec i ρ fs (st.addClock d) s = (exec i ρ fs st s).shift d) ∧
    (∀ fs st c post body d, (loop i ρ fs st c post body).val ≠ .timeout →
      loop i ρ fs (st.addClock d) c post body = (loop i ρ fs st c post body).shift d) ∧
    (∀ fs st b d, (execBlock i ρ fs st b).val ≠ .timeout →
      execBlock i ρ fs (st.addClock d) b = (execBlock i ρ fs st b).shift d) ∧
    (∀ fs st ss d, (execs i ρ fs st ss).val ≠ .timeout →
      execs i ρ fs (st.addClock d) ss = (execs i ρ fs st ss).shift d) ∧
    (∀ fs st e d, (eval i ρ fs st e).val ≠ .timeout →
      eval i ρ fs (st.addClock d) e = (eval i ρ fs st e).shift d) ∧
    (∀ fs st es d, (evals i ρ fs st es).val ≠ .timeout →
      evals i ρ fs (st.addClock d) es = (evals i ρ fs st es).shift d) := by
  apply exec.mutual_induct i ρ
  all_goals
    intros
    rename_i d hnt
    -- one step on the two sides and in the hypothesis that the outcome is not a timeout
    first
    | (conv => lhs; rw [loop]); (conv => rhs; rw [loop]); rw [loop] at hnt
    | rw [exec, exec]; rw [exec] at hnt
    | rw [execBlock, execBlock]; rw [execBlock] at hnt
    | rw [execs, execs]; rw [execs] at hnt
    | rw [eval, eval]; rw [eval] at hnt
    | rw [evals, evals]; rw [evals] at hnt
    simp only [Res.eq_iff_pair, Res.shift, Prod.eta, exec_val, exec_st, loop_val, loop_st,
      execBlock_val, execBlock_st, execs_val, execs_st, eval_val, eval_st, evals_val,
      evals_st] at *
  all_goals
    simp_all +zetaDelta [Res.up, restrict_addClock, mk_pred, builtin_val, builtin_st,
      builtinP_addClock, Values.outcome_eq_timeout, exec_val, exec_st, loop_val, loop_st,
      execBlock_val, execBlock_st, execs_val, execs_st, eval_val, eval_st, evals_val, evals_st]

end Yul.Clocked
