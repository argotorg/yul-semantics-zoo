import Lean
import YulSemnaticsZoo.Yul.Semantics.Clocked.Interp

/-!
# Compiler: a tactic for the proofs about the interpreter

{lit}`rw_res` rewrites the goal with each hypothesis {lit}`f … = r` where {lit}`f` is a function
of the Yul interpreter, until none applies. The functional induction of the interpreter gives
these hypotheses. {lit}`simp` cannot use them where the type of a result depends on the state
({lit}`Res st.clock`); {lit}`rw` with one hypothesis at a time can.
-/

namespace Yul.Clocked
open Lean Elab Tactic Meta

elab "rw_res" : tactic => do
  let fns := [``exec, ``loop, ``execBlock, ``execs, ``eval, ``evals]
  let mut progress := true
  while progress do
    progress := false
    if (← getGoals).isEmpty then return
    let hs ← withMainContext do return (← getLCtx).decls.toList.filterMap id
    for h in hs do
      if h.isImplementationDetail then continue
      let ok ← withMainContext do
        let ty ← instantiateMVars h.type
        let some (_, lhs, _) := ty.eq? | return false
        unless fns.any (lhs.isAppOf ·) do return false
        try
          let g ← getMainGoal
          let r ← g.rewrite (← g.getType) h.toExpr
          let g' ← g.replaceTargetEq r.eNew r.eqProof
          replaceMainGoal (g' :: r.mvarIds)
          return true
        catch _ => return false
      if ok then progress := true

end Yul.Clocked
