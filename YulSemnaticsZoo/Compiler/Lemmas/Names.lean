import YulSemnaticsZoo.Yul.Semantics.Clocked.Interp

set_option doc.verso true

/-!
# Compiler: the names of the variables in a Yul run

An expression does not change the variables. A block and a loop do not change the names of the
variables, only their values. A statement adds names at the start ({lit}`let`). The compiler
uses this: it knows the names at each point of the code. The facts after each function of the
interpreter ({lit}`AfterExpr`, {lit}`AfterStmt`, {lit}`AfterBlock`) give these lemmas.
-/

namespace Yul.Clocked
open Semantics

variable {i : Input} {ρ : Readings} {N : List String}

@[simp] theorem names_append : names (a ++ b) = names a ++ names b := List.map_append

theorem names_restrict' {st st' : State} (h : names st.vars <:+ names st'.vars) :
    names (restrict st st').vars = names st.vars := names_restrict h

theorem names_exec : names st.vars <:+ names (exec i ρ N fs st Γ s h hI).st.vars := by
  rw [hI.vars]; exact (exec i ρ N fs st Γ s h hI).post.suffix

theorem names_execs : names st.vars <:+ names (execs i ρ N fs st Γ ss h hI).st.vars := by
  rw [hI.vars]; exact (execs i ρ N fs st Γ ss h hI).post.suffix

theorem names_execBlock : names (execBlock i ρ N fs st Γ b h hI).st.vars = names st.vars :=
  (execBlock i ρ N fs st Γ b h hI).post.vars.trans hI.vars.symm

theorem names_loop :
    names (loop i ρ N fs st Γ c post body hc hb hp hl hI).st.vars = names st.vars :=
  (loop i ρ N fs st Γ c post body hc hb hp hl hI).post.vars.trans hI.vars.symm

theorem eval_vars : (eval i ρ N fs st Γ e n h hI).st.vars = st.vars :=
  (eval i ρ N fs st Γ e n h hI).post.vars

theorem evals_vars : (evals i ρ N fs st Γ es h hI).st.vars = st.vars :=
  (evals i ρ N fs st Γ es h hI).post.vars

theorem builtin_vars : (builtin i ρ b vs h st).st.vars = st.vars := (builtin i ρ b vs h st).post.vars

end Yul.Clocked
