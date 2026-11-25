import Lean
import YulSemnaticsZoo.Yul.Semantics.Clocked.Interp

set_option doc.verso true

/-!
# Yul: tactics for the proofs about the interpreter

The functional induction of the interpreter gives, for each recursive call, an equation
{lit}`f … = r` and an induction hypothesis. {lit}`simp` cannot rewrite with these equations where
the type of a result depends on the state ({lit}`Res st.clock`), or where a match of the
interpreter has a proof about the result. A {lit}`rw` of the full result can: then the matches
reduce.

* {lit}`rw_res` rewrites the goal with each equation {lit}`f … = r`, until none applies.
* {lit}`rw_ih d using t` rewrites the left side of the goal with an induction hypothesis
  {lit}`∀ d, p → f … = r` of {lit}`mono`. The tactic {lit}`t` proves the premise {lit}`p`.
* {lit}`rw_cases` rewrites the goal with an equation {lit}`e = C …` of a match.
* {lit}`subst_clock` replaces a state whose clock is not 0 with a state with the clock
  {lit}`c + 1`.
* {lit}`simp_conds` and {lit}`dsimp_res` simplify the goal and the hypothesis {lit}`hnt` without
  simprocs: a simproc changes the form of a literal, and then a hypothesis does not match.
-/

namespace Yul.Clocked
open Lean Elab Tactic Meta

/-- the functions of the interpreter -/
def interpFns : List Name := [``exec, ``loop, ``execBlock, ``execs, ``eval, ``evals]

/-- the type is an equation with a function of the interpreter on the left -/
def isInterpEq (ty : Expr) : Bool :=
  match ty.eq? with
  | some (_, lhs, _) => interpFns.any (lhs.isAppOf ·)
  | none => false

/-- rewrite the main goal with the proof {name}`pf`; the premises are new goals -/
def rewriteMain (pf : Expr) : TacticM (List MVarId) := do
  let g ← getMainGoal
  let r ← g.rewrite (← g.getType) pf
  let g' ← g.replaceTargetEq r.eNew r.eqProof
  replaceMainGoal [g']
  return r.mvarIds

/-- rewrite the main goal with each hypothesis {lit}`f … = r`, until none applies; fail if none
applies at the start -/
elab "rw_res" : tactic => do
  let mut progress := true
  let mut any := false
  while progress do
    progress := false
    if (← getGoals).isEmpty then break
    let hs ← withMainContext do return (← getLCtx).decls.toList.filterMap id
    for h in hs do
      if h.isImplementationDetail then continue
      let ok ← withMainContext do
        let ty ← instantiateMVars h.type
        unless isInterpEq ty do return false
        try
          let gs ← rewriteMain h.toExpr
          appendGoals gs
          return true
        catch _ => return false
      if ok then progress := true; any := true
  unless any do throwError "rw_res: no equation applies"

/-- rewrite the left side of the main goal {lit}`l = r` with the proof {name}`pf`; the premises
are new goals -/
def rewriteLhs (pf : Expr) (t : TransparencyMode := .instances) : TacticM (List MVarId) := do
  let g ← getMainGoal
  g.withContext do
    let some (_, l, r) := (← instantiateMVars (← g.getType)).eq? | throwError "not an equation"
    let res ← g.rewrite l pf (config := { transparency := t })
    let g' ← mkFreshExprSyntheticOpaqueMVar (← mkEq res.eNew r)
    g.assign (← mkEqTrans res.eqProof g')
    replaceMainGoal [g'.mvarId!]
    return res.mvarIds

/-- rewrite the left side of the main goal with a hypothesis {lit}`∀ d, p → f … = r`, for the
clock {lit}`d`; the tactic {lit}`t` proves the premise {lit}`p` -/
elab "rw_ih " d:term " using " t:tacticSeq : tactic => do
  let hs ← withMainContext do return (← getLCtx).decls.toList.filterMap id
  for h in hs do
    if h.isImplementationDetail then continue
    let s ← saveState
    let ok ← withMainContext do
      try
        let dE ← elabTerm d (some (mkConst ``Nat))
        let .forallE _ (.const ``Nat []) _ _ ← whnfR (← instantiateMVars h.type) | return false
        let e := mkApp h.toExpr dE
        let (ms, _, ty) ← forallMetaTelescopeReducing (← inferType e)
        unless isInterpEq ty do return false
        let gs ← rewriteLhs (mkAppN e ms) .default
        let main ← getMainGoal
        for m in gs do
          if ← m.isAssigned then continue
          setGoals [m]
          evalTactic t
          unless (← getGoals).isEmpty do throwError "premise"
        setGoals [main]
        return true
      catch _ => return false
    if ok then return
    s.restore
  throwError "rw_ih: no induction hypothesis applies"


/-- a hypothesis {lit}`¬s.clock = 0` for a local state {lit}`s`: replace {lit}`s` with
{lit}`⟨vars, mem, reads, c + 1⟩` -/
elab "subst_clock" : tactic => do
  let g ← getMainGoal
  let some s ← g.withContext do
      for h in (← getLCtx) do
        if h.isImplementationDetail then continue
        let some p := (← instantiateMVars h.type).not? | continue
        let some (_, l, _) := p.eq? | continue
        if l.isAppOfArity ``State.clock 1 then
          if let .fvar s := l.appArg! then return some s
      return none
    | throwError "subst_clock: no hypothesis ¬s.clock = 0"
  let gs ← g.cases s
  let [sg] := gs.toList | throwError "subst_clock: cases"
  let g := sg.mvarId
  let .fvar clk := sg.fields[3]! | throwError "subst_clock: field"
  let some hc ← g.withContext do
      for h in (← getLCtx) do
        let some p := (← instantiateMVars h.type).not? | continue
        let some (_, l, _) := p.eq? | continue
        if (← whnfR l) == .fvar clk then return some h.fvarId
      return none
    | throwError "subst_clock: no hypothesis ¬clock = 0"
  let g ← g.rename hc `hclk
  replaceMainGoal [g]
  let hclk := mkIdent `hclk
  evalTactic (← `(tactic|
    (dsimp only at $hclk:ident
     obtain ⟨_, $(mkIdent `rfl):ident⟩ := Nat.exists_eq_add_one_of_ne_zero $hclk)))

/-- the hypotheses {lit}`¬a = b` and {lit}`a = 0`: the conditions of {lit}`if` -/
def condHyps : MetaM (Array LocalDecl) := do
  let mut hs := #[]
  for h in (← getLCtx) do
    if h.isImplementationDetail then continue
    let ty ← instantiateMVars h.type
    let isCond := match ty.not? with
      | some p => p.isEq
      | none => match ty.eq? with
        | some (_, _, r) => r.isAppOfArity ``OfNat.ofNat 3 && !isInterpEq ty
        | none => false
    if isCond then hs := hs.push h
  return hs

/-- the hypothesis {lit}`hnt`, if there is one -/
def hntHyp : MetaM (Array FVarId) := do
  match (← getLCtx).findFromUserName? `hnt with
  | some h => return #[h.fvarId]
  | none => return #[]

/-- {lit}`simp only` at the goal and at {lit}`hnt`, with the conditions of {lit}`if`
({name}`condHyps`), without simprocs: a simproc changes the form of literals, and then a
condition does not match -/
elab "simp_conds" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let mut thms : SimpTheorems := {}
    for h in ← condHyps do thms ← thms.add (.fvar h.fvarId) #[] h.toExpr
    for n in [``Nat.add_eq_zero_iff, ``Nat.add_one_ne_zero, ``and_false, ``false_and,
        ``and_true, ``true_and, ``dite_true, ``dite_false, ``ite_true, ``ite_false,
        ``not_false_eq_true, ``not_true_eq_false, ``eq_self_iff_true, ``ne_eq,
        ``dite_eq_left_of_eq_true, ``dite_eq_right_of_eq_false, ``ite_eq_left_of_eq_true,
        ``ite_eq_right_of_eq_false] do
      thms ← thms.addConst n
    let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
    let (r, _) ← simpGoal g ctx #[] (fvarIdsToSimp := ← hntHyp)
    match r with
    | none => replaceMainGoal []
    | some (_, g') =>
      if g' == g then throwError "simp_conds: no progress"
      replaceMainGoal [g']

/-- {lit}`dsimp only [ls]` at the goal and at {lit}`hnt`, without simprocs -/
elab "dsimp_res " "[" ls:ident,* "]" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let mut thms : SimpTheorems := {}
    for l in ls.getElems do thms ← thms.addDeclToUnfold (← realizeGlobalConstNoOverload l)
    let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
    let (r, _) ← dsimpGoal g ctx #[] (fvarIdsToSimp := ← hntHyp)
    match r with
    | none => replaceMainGoal []
    | some g' =>
      if g' == g then throwError "dsimp_res: no progress"
      replaceMainGoal [g']


/-- rewrite the main goal with a hypothesis {lit}`e = C …` for a constructor {lit}`C`, from a
match of the interpreter, where {lit}`e` is not a call of the interpreter; with the reducible
definitions in {lit}`e` unfolded, as the goal has them after {lit}`dsimp` -/
elab "rw_cases" : tactic => do
  let hs ← withMainContext do return (← getLCtx).decls.toList.filterMap id
  for h in hs do
    if h.isImplementationDetail then continue
    let s ← saveState
    let ok ← withMainContext do
      let ty ← instantiateMVars h.type
      let some (_, l, r) := ty.eq? | return false
      unless (← isConstructorApp r) do return false
      if isInterpEq ty || l.isFVar then return false
      try
        let pf ← mkExpectedTypeHint h.toExpr (← mkEq (← whnfR l) r)
        let gs ← rewriteMain pf
        appendGoals gs
        return true
      catch _ => return false
    if ok then return
    s.restore
  throwError "rw_cases: no hypothesis applies"

end Yul.Clocked
