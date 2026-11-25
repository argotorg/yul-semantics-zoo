import YulSemnaticsZoo.Compiler.Lemmas.Tactic

set_option doc.verso true

/-!
# Compiler: the names of the variables in a Yul run

An expression does not change the variables. A block and a loop do not change the names of the
variables, only their values. A statement adds names at the start ({lit}`let`). The compiler
uses this: it knows the names at each point of the code.
-/

namespace Yul.Clocked
open Semantics

/-- the names of the variables -/
abbrev names (vs : Vars) : List Identifier := vs.map (·.1)

@[simp] theorem names_set : names (Vars.set vs x v) = names vs := by
  induction vs with
  | nil => rfl
  | cons a vs ih => obtain ⟨y, w⟩ := a; by_cases h : y = x <;> simp_all [Vars.set]

@[simp] theorem names_assign : names (Vars.assign vs xs ws) = names vs := by
  induction xs generalizing vs ws <;> simp_all [Vars.assign]

@[simp] theorem names_bind : names (bind xs ws) = xs := by
  apply List.ext_getElem <;> simp [bind]

/-- the names after a block that adds names at the start -/
theorem names_restrict {st st' : State} (h : names st'.vars = X ++ names st.vars) :
    names (restrict st st').vars = names st.vars := by
  have hl := congrArg List.length h
  simp only [names, List.length_map, List.length_append] at hl
  simp only [restrict, names, List.map_drop] at h ⊢
  rw [h, hl, show X.length + st.vars.length - st.vars.length = X.length by omega,
    List.drop_left]

variable (i : Input) (ρ : Readings)

@[simp] theorem names_append : names (a ++ b) = names a ++ names b := List.map_append

theorem names_restrict' {st st' : State} (h : names st.vars <:+ names st'.vars) :
    names (restrict st st').vars = names st.vars := by
  obtain ⟨X, hX⟩ := h
  exact names_restrict hX.symm

theorem builtin_vars : (builtin i ρ b vs st).st.vars = st.vars := by
  rcases b with _ | b
  · rfl
  · cases b <;> rfl

set_option linter.unusedSimpArgs false in
theorem names_mono :
    (∀ fs st s, names st.vars <:+ names (exec i ρ fs st s).st.vars) ∧
    (∀ fs st c post body, names (loop i ρ fs st c post body).st.vars = names st.vars) ∧
    (∀ fs st b, names (execBlock i ρ fs st b).st.vars = names st.vars) ∧
    (∀ fs st ss, names st.vars <:+ names (execs i ρ fs st ss).st.vars) ∧
    (∀ fs st e, (eval i ρ fs st e).st.vars = st.vars) ∧
    (∀ fs st es, (evals i ρ fs st es).st.vars = st.vars) := by
  apply exec.mutual_induct i ρ
  all_goals
    intros
    first
    | (rw [loop]) | (rw [exec]) | (rw [execBlock]) | (rw [execs]) | (rw [eval]) | (rw [evals])
    rw_res
  all_goals
    simp_all only [Res.up, Values.outcome, builtin_vars, names_restrict', names_bind,
      names_assign, names_append, List.suffix_refl, List.suffix_append, dite_true, dite_false,
      ite_true, ite_false, not_false_eq_true]
  all_goals (try rw_res)
  all_goals (try simp_all only [Res.up, names_restrict', List.suffix_refl])
  all_goals first
    | exact List.IsSuffix.trans ‹_› ‹_›
    | (split <;> simp_all)
    | skip

end Yul.Clocked
