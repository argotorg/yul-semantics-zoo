import YulSemnaticsZoo.Yul.Syntax.EVM
import YulSemnaticsZoo.Yul.Syntax.WellFormed
import YulSemnaticsZoo.Yul.Syntax.Lemmas.WellFormed
import YulSemnaticsZoo.Semantics

set_option doc.verso true

/-!
# Yul: a clocked semantics

Reference: [the formal specification of Yul](https://docs.soliditylang.org/en/v0.8.38/yul.html#formal-specification)

A big-step interpreter for Yul objects that are well-formed in the EVM dialect
({lit}`Yul.EVM.dialect`). The type {lit}`WFObject` has only these objects. The clock is part of
the state. It decreases by 1 at each loop iteration (before the condition) and at each call of a
Yul function. When the clock is 0 at one of these points, the outcome is {lit}`timeout`. Nothing
else uses the clock.

The semantics defines 8 builtins: {lit}`add`, {lit}`lt`, {lit}`eq`, {lit}`calldataload`,
{lit}`mload`, {lit}`mstore`, {lit}`gas` and {lit}`return`. A call of each other builtin of the
dialect halts the run with {lit}`unsupported`, as the EVM semantics does for an instruction that it
does not define. The halt comes after the arguments that are not literals, as for the 8 builtins:
the arguments can read gas, halt or time out before it.

The input {lit}`i` and the readings {lit}`ρ` are parameters. The n-th call of {lit}`gas()` gives
{lit}`ρ n`. There is no gas counter. Memory has no size limit, and the depth of function calls has
no limit.

The state has the variables, the memory, the number of gas reads before, and the clock. The
functions in scope are an argument ({lit}`Funs`), because they do not change in a run: a block
adds its functions for all of its statements. A function call finds the function with lexical
scope.

Each function gives a result with a clock that is not more than the clock before (the type
{lit}`Res`). Thus the recursion ends: at each recursive call, the clock decreases, or the clock
does not increase and the AST is smaller.

## Well-formed ASTs

Each function of the interpreter has three more arguments: the scope {lit}`Γ` of the AST part
({lit}`Scope` of {lit}`Object.WellFormed`), the proof that the part is well-formed in
{lit}`Γ`, and the proof that the state agrees with {lit}`Γ` ({lit}`Agrees`):
* the names of the variables of the run are the variables of {lit}`Γ`;
* the functions of {lit}`Γ` are the names and the numbers of parameters and return variables of
  the functions in scope ({lit}`sigs`);
* the body of each function in scope is well-formed in its scope: its parameters and return
  variables, and the functions in scope at its definition ({lit}`Funs.WellFormed`).

Each result has a proof of the facts after it ({lit}`AfterExpr`, {lit}`AfterStmt`,
{lit}`AfterBlock`): an expression does not change the variables and gives the number of values
that its place needs; a statement keeps the variables before it, and adds the variables of its
declaration; a {lit}`break` or {lit}`continue` comes only from the body of a loop, and a
{lit}`leave` only from a function ({lit}`Outcome.Fits`). With these proofs, each case of an AST
that is not well-formed is impossible, and the interpreter has no rule for it.
-/

namespace Yul

/-- a Yul object that is well-formed in the EVM dialect -/
abbrev WFObject := { P : Object // P.WellFormed EVM.dialect }

namespace Clocked
open Semantics

/-- the outcome of a statement -/
inductive Outcome where
  | normal
  | brk
  | cont
  | leave
  | halt (r : Result)
  -- the clock is 0 at a loop iteration or a function call
  | timeout
  deriving DecidableEq, Repr

/-- the outcome of an expression: its values, a halt, or a timeout -/
inductive Values where
  | ok (vs : List Word)
  | halt (r : Result)
  | timeout
  deriving DecidableEq, Repr

/-- the outcome of a statement that stops in its expression -/
def Values.outcome : Values → Outcome
  | .ok _ => .normal
  | .halt r => .halt r
  | .timeout => .timeout

/-- the variables in scope with their values; the last declaration is first -/
abbrev Vars := List (Identifier × Word)

/-- the names of the variables -/
abbrev names (vs : Vars) : List Identifier := vs.map (·.1)

theorem mem_names_tail (h : x ∈ names ((y, w) :: vs)) (hy : ¬y = x) : x ∈ names vs :=
  (List.mem_cons.mp h).resolve_left fun e => hy e.symm

/-- the value of the variable {name}`x` -/
def Vars.get : (vs : Vars) → (x : Identifier) → x ∈ names vs → Word
  | (y, w) :: vs, x, h => if hy : y = x then w else Vars.get vs x (mem_names_tail h hy)
  | [], _, h => absurd h List.not_mem_nil

/-- the variables with the value {lit}`v` for the first variable with the name {lit}`x` -/
def Vars.set : (vs : Vars) → (x : Identifier) → x ∈ names vs → Word → Vars
  | (y, w) :: vs, x, h, v =>
    if hy : y = x then (y, v) :: vs else (y, w) :: Vars.set vs x (mem_names_tail h hy) v
  | [], _, h, _ => absurd h List.not_mem_nil

@[simp] theorem names_set {vs : Vars} {x : Identifier} {h : x ∈ names vs} {v : Word} :
    names (Vars.set vs x h v) = names vs := by
  induction vs with
  | nil => exact absurd h List.not_mem_nil
  | cons a vs ih =>
    obtain ⟨y, w⟩ := a
    unfold Vars.set
    split
    · rfl
    · simp [ih]

/-- the variables after an assignment of the values {name}`vs` to the variables {name}`xs` in
order -/
def Vars.assign : (vars : Vars) → (xs : List Identifier) → (vs : List Word) →
    (∀ x ∈ xs, x ∈ names vars) → vs.length = xs.length → Vars
  | vars, [], [], _, _ => vars
  | vars, x :: xs, v :: vs, h, hl =>
    Vars.assign (Vars.set vars x (h x (by simp)) v) xs vs
      (fun y hy => by rw [names_set]; exact h y (by simp [hy])) (by simpa using hl)
  | _, [], _ :: _, _, hl => absurd hl (by simp)
  | _, _ :: _, [], _, hl => absurd hl (by simp)

@[simp] theorem names_assign {vars : Vars} {xs : List Identifier} {vs : List Word}
    {h : ∀ x ∈ xs, x ∈ names vars} {hl : vs.length = xs.length} :
    names (Vars.assign vars xs vs h hl) = names vars := by
  induction xs generalizing vars vs with
  | nil => cases vs with
    | nil => rfl
    | cons => simp at hl
  | cons x xs ih => cases vs with
    | nil => simp at hl
    | cons v vs => simp only [Vars.assign, ih, names_set]

/-- new variables {name}`xs` with the values {name}`vs` in order -/
def bind : (xs : List Identifier) → (vs : List Word) → vs.length = xs.length → Vars
  | [], [], _ => []
  | x :: xs, v :: vs, h => (x, v) :: bind xs vs (by simpa using h)
  | [], _ :: _, h => absurd h (by simp)
  | _ :: _, [], h => absurd h (by simp)

@[simp] theorem names_bind {xs : List Identifier} {vs : List Word} {h : vs.length = xs.length} :
    names (bind xs vs h) = xs := by
  induction xs generalizing vs with
  | nil => cases vs with
    | nil => rfl
    | cons => simp at h
  | cons x xs ih => cases vs with
    | nil => simp at h
    | cons v vs => simp only [bind, List.map_cons, ih]

/-- a Yul function -/
structure Fun where
  params : List Identifier
  rets : List Identifier
  body : Block

/-- the functions that the statements of a block define -/
def defs : List Statement → List (Identifier × Fun)
  | [] => []
  | .FunctionDefinition f ps rs b :: ss => (f, ⟨ps, rs, b⟩) :: defs ss
  | _ :: ss => defs ss

/-- the functions in scope: for each block around the statement, the innermost first, the
functions that it defines. A function is in scope in all of its block. -/
abbrev Funs := List (List (Identifier × Fun))

/-- the function {name}`f` in scope, and the functions in scope at its definition -/
def Funs.find? (f : Identifier) : Funs → Option (Fun × Funs)
  | [] => none
  | l :: ls =>
    match l.lookup f with
    | some fn => some (fn, l :: ls)
    | none => find? f ls

/-- the name, the number of parameters and the number of return variables of a function -/
def sig (p : Identifier × Fun) : Identifier × Nat × Nat :=
  (p.1, p.2.params.length, p.2.rets.length)

/-- the {name}`sig` of each function in scope, as in {name}`Scope.funs` -/
def sigs (fs : Funs) : List (Identifier × Nat × Nat) := fs.flatMap (·.map sig)

/-- the scope of the body of {name}`fn`, with the functions {name}`fs` in scope at its
definition -/
def Fun.scope (fn : Fun) (fs : Funs) : Scope :=
  { vars := fn.params ++ fn.rets, funs := sigs fs, inFunction := true }

section
-- the names of the sub-objects and data that the code can refer to
variable (N : List String)

/-- the body of each function in scope is well-formed in its scope -/
def Funs.WellFormed : Funs → Prop
  | [] => True
  | l :: ls => (∀ p ∈ l, p.2.body.WellFormed EVM.dialect N (p.2.scope (l :: ls))) ∧
      Funs.WellFormed ls

/-- the variables {name}`vars` and the functions {name}`fs` of a run agree with the scope
{name}`Γ` -/
structure Agrees (fs : Funs) (vars : Vars) (Γ : Scope) : Prop where
  vars : names vars = Γ.vars
  funs : Γ.funs = sigs fs
  wf : Funs.WellFormed N fs

end

theorem Agrees.of_vars (hI : Agrees N fs vs Γ) (h : vs' = vs) : Agrees N fs vs' Γ :=
  h ▸ hI

/-- the outcome can end code in the scope {name}`Γ`: {lit}`break` and {lit}`continue` only in the
body of a loop, {lit}`leave` only in a function -/
def Outcome.Fits (Γ : Scope) : Outcome → Prop
  | .brk | .cont => Γ.inLoopBody
  | .leave => Γ.inFunction
  | .normal | .halt _ | .timeout => True

/-- {name}`n` values, or no values: a halt or a timeout -/
abbrev Values.Count (n : Nat) : Values → Prop
  | .ok vs => vs.length = n
  | .halt _ | .timeout => True

/-- the facts after an expression that starts with the variables {name}`vars₀` and has
{name}`n` values -/
structure AfterExpr (vars₀ : Vars) (n : Nat) (v : Values) (vars : Vars) : Prop where
  vars : vars = vars₀
  count : v.Count n

/-- the facts after statements in the scope {name}`Γ`, with the variables {name}`X` after them -/
structure AfterStmt (Γ : Scope) (X : List Identifier) (o : Outcome) (vars : Vars) : Prop where
  fits : o.Fits Γ
  suffix : Γ.vars <:+ names vars
  normal : o = .normal → names vars = X

/-- the facts after a block or a loop in the scope {name}`Γ` -/
structure AfterBlock (Γ : Scope) (o : Outcome) (vars : Vars) : Prop where
  fits : o.Fits Γ
  vars : names vars = Γ.vars

/-- the value of a literal; a string is left-aligned, as in solc. A well-formed literal fits in
a word. -/
def literalValue : Literal → Word
  | .NumberLiteral n => BitVec.ofNat 256 n
  | .StringLiteral bs => ofBytes ((bs ++ List.replicate 32 0).take 32)
  | .TrueLiteral => 1
  | .FalseLiteral => 0

structure State where
  vars : Vars
  mem : Memory
  -- the number of gas reads before
  reads : Nat
  clock : Nat

/-- the state at the start of a run with clock {name}`k` -/
def start (k : Nat) : State := { vars := [], mem := Memory.empty, reads := 0, clock := k }

/-- the state {name}`st'` after a block that starts in {name}`st`: the variables of the block are
removed. A block only adds variables at the start of the list. -/
def restrict (st st' : State) : State :=
  { st' with vars := st'.vars.drop (st'.vars.length - st.vars.length) }

/-- a result, the state after it and the facts {name}`Q` after it, with a clock that is not more
than {name}`c` -/
structure Res (c : Nat) (α : Type) (Q : α → Vars → Prop) where
  val : α
  st : State
  le : st.clock ≤ c
  post : Q val st.vars

/-- the result with a larger bound {name}`c'` of the clock, and the facts {name}`Q'` that
follow from {name}`Q` -/
abbrev Res.up {Q Q' : α → Vars → Prop} (h : c ≤ c') (hq : ∀ a vs, Q a vs → Q' a vs)
    (r : Res c α Q) :
    Res c' α Q' :=
  ⟨r.val, r.st, Nat.le_trans r.le h, hq _ _ r.post⟩

/-- the measure of the recursion decreases: the clock decreases, or the clock does not increase and
the AST is smaller -/
theorem lex_lt {a a' b b' : Nat} (h : a' < a ∨ a' ≤ a ∧ b' < b) :
    Prod.Lex (· < ·) (· < ·) (a', b') (a, b) := by
  rcases h with h | ⟨h, hb⟩
  · exact .left _ _ h
  · rcases Nat.lt_or_eq_of_le h with h | rfl
    · exact .left _ _ h
    · exact .right _ hb

/-- the arguments of a builtin that are not literals -/
def exprArgs : List Arg → List Expression → List Expression
  | .Expression :: ks, e :: es => e :: exprArgs ks es
  | .Literal :: ks, _ :: es => exprArgs ks es
  | _, _ => []

theorem sizeOf_exprArgs : sizeOf (exprArgs ks es) ≤ sizeOf es := by
  induction es generalizing ks with
  | nil => cases ks <;> simp [exprArgs]
  | cons e es ih =>
    rcases ks with _ | ⟨_ | _, ks⟩
    · simp [exprArgs]; omega
    · have := @ih ks; simp [exprArgs]; omega
    · have := @ih ks; simp [exprArgs]; omega

/-- the proof that the measure decreases at a recursive call -/
macro "decreasing_clock" : tactic =>
  `(tactic| ((try apply lex_lt) <;> simp_all <;> omega))

/-! ## The proofs that the interpreter uses -/

section
variable {N : List String}

theorem ne_nil_of_length (h : vs.length = 1) : vs ≠ [] := by rintro rfl; simp at h

theorem Values.outcome_fits {v : Values} : v.outcome.Fits Γ := by cases v <;> trivial

theorem Outcome.fits_after {o : Outcome} (h : o.Fits (Scope.after Γ s)) : o.Fits Γ := by
  cases o <;> simp_all [Outcome.Fits]

/-- facts after code that does not change the names of the variables -/
theorem AfterStmt.same (h : names vars = Γ.vars) (hf : o.Fits Γ) : AfterStmt Γ Γ.vars o vars :=
  ⟨hf, h ▸ List.suffix_refl _, fun _ => h⟩

theorem AfterStmt.stop (h : names vars = Γ.vars) (hf : o.Fits Γ) (ho : o ≠ .normal) :
    AfterStmt Γ X o vars :=
  ⟨hf, h ▸ List.suffix_refl _, fun e => absurd e ho⟩

theorem AfterStmt.cons (p : AfterStmt Γ (Scope.after Γ s).vars .normal vars)
    (q : AfterStmt (Scope.after Γ s) X o vars') : AfterStmt Γ X o vars' :=
  ⟨Outcome.fits_after q.fits, (p.normal rfl ▸ p.suffix).trans q.suffix, q.normal⟩

theorem names_restrict {st st' : State} (h : names st.vars <:+ names st'.vars) :
    names (restrict st st').vars = names st.vars := by
  obtain ⟨X, hX⟩ := h
  have hl := congrArg List.length hX
  simp only [names, List.length_map, List.length_append] at hl
  simp only [restrict, names, List.map_drop] at hX ⊢
  rw [← hX, ← hl, show X.length + st.vars.length - st.vars.length = X.length by omega,
    List.drop_left]

theorem argsWellFormed_exprArgs (h : builtinArgsWellFormed d N Γ ks es) :
    argsWellFormed d N Γ (exprArgs ks es) := by
  induction es generalizing ks with
  | nil => cases ks <;> simp [exprArgs, argsWellFormed]
  | cons e es ih =>
    rcases ks with _ | ⟨_ | _, ks⟩
    · simp [builtinArgsWellFormed] at h
    · exact ⟨h.1, ih h.2⟩
    · exact ih h.2

theorem length_exprArgs (h : builtinArgsWellFormed d N Γ ks es) :
    (exprArgs ks es).length = ks.count .Expression := by
  induction es generalizing ks with
  | nil => rcases ks with _ | ⟨_ | _, ks⟩ <;> simp_all [exprArgs, builtinArgsWellFormed]
  | cons e es ih =>
    rcases ks with _ | ⟨_ | _, ks⟩ <;> simp_all [exprArgs, builtinArgsWellFormed]

theorem sigs_defs : (defs ss).map sig = functions ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih => cases s <;> simp_all [defs, functions, sig]

theorem lookup_sigs {l : List (Identifier × Fun)} :
    (l.map sig).lookup f = (l.lookup f).map fun fn => (fn.params.length, fn.rets.length) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨g, fn⟩ := a
    by_cases h : f = g
    · subst h; simp [sig]
    · have hb : (f == g) = false := by simpa using h
      simp [List.lookup, sig, hb, ih]

theorem mem_of_lookup {l : List (Identifier × Fun)} (h : l.lookup f = some fn) :
    (f, fn) ∈ l := by
  obtain ⟨l₁, l₂, rfl, -⟩ := List.lookup_eq_some_iff.mp h; simp


/-- the function that {name}`Funs.find?` gives -/
theorem find_some (hw : Funs.WellFormed N fs) (hf : Funs.find? f fs = some (fn, fs')) :
    (sigs fs).lookup f = some (fn.params.length, fn.rets.length) ∧ Funs.WellFormed N fs' ∧
      fn.body.WellFormed EVM.dialect N (fn.scope fs') := by
  induction fs with
  | nil => simp [Funs.find?] at hf
  | cons l ls ih =>
    simp only [Funs.find?] at hf
    split at hf
    · next fn' hl =>
      cases hf
      refine ⟨?_, hw, hw.1 (f, fn) (mem_of_lookup hl)⟩
      have : (l.map sig).lookup f = some (fn.params.length, fn.rets.length) := by
        rw [lookup_sigs, hl]; rfl
      simp only [sigs, List.flatMap_cons, List.lookup_append, this, Option.some_or]
    · next hl =>
      obtain ⟨h1, h2, h3⟩ := ih hw.2 hf
      refine ⟨?_, h2, h3⟩
      simp only [sigs, List.flatMap_cons]
      rw [List.lookup_append, lookup_sigs, hl]; simp only [Option.map_none, Option.none_or]
      exact h1

theorem find_none (hf : Funs.find? f fs = none) : (sigs fs).lookup f = none := by
  induction fs with
  | nil => rfl
  | cons l ls ih =>
    simp only [Funs.find?] at hf
    split at hf
    · cases hf
    · next hl =>
      simp only [sigs, List.flatMap_cons]
      rw [List.lookup_append, lookup_sigs, hl]; simp only [Option.map_none, Option.none_or]
      exact ih hf

/-- the functions of the statements {name}`ss` of a block {name}`L` -/
theorem defs_wellFormed (h : statementsWellFormed EVM.dialect N Γ ss) (hf : Γ.funs = sigs L) :
    ∀ p ∈ defs ss, p.2.body.WellFormed EVM.dialect N (p.2.scope L) := by
  induction ss generalizing Γ with
  | nil => simp [defs]
  | cons s ss ih =>
    have ih' := ih h.2 (by simpa using hf)
    cases s with
    | FunctionDefinition f ps rs body =>
      intro p hp
      simp only [defs, List.mem_cons] at hp
      rcases hp with rfl | hp
      · have := Block.wellFormed_hidden (H := []) (List.nil_subset _) body h.1.2.2
        simpa [Fun.scope, hf] using this
      · exact ih' p hp
    | _ => exact ih'

theorem agrees_block (h : Block.WellFormed EVM.dialect N Γ ⟨ss⟩) (hI : Agrees N fs vars Γ) :
    Agrees N (defs ss :: fs) vars { Γ with funs := functions ss ++ Γ.funs } where
  vars := hI.vars
  funs := by simp [sigs, ← sigs_defs, hI.funs]
  wf := ⟨defs_wellFormed h.2 (by simp [sigs, ← sigs_defs, hI.funs]), hI.wf⟩

theorem agrees_after (hI : Agrees N fs vars Γ) (h : names vars' = (Scope.after Γ s).vars) :
    Agrees N fs vars' (Scope.after Γ s) := ⟨h, by simp [hI.funs], hI.wf⟩

theorem wf_builtin (h : (Expression.FunctionCall f args).WellFormed EVM.dialect N Γ n)
    (hb : EVM.dialect.builtin f = some (kinds, mk)) (hm : mk (literalArgs kinds args) = some b) :
    argsWellFormed EVM.dialect N Γ (exprArgs kinds args) ∧
      (exprArgs kinds args).length = EVM.ins b ∧ EVM.outs b = n := by
  rw [Expression.WellFormed, hb] at h
  simp only [hm] at h
  exact ⟨argsWellFormed_exprArgs h.1, (length_exprArgs h.1).trans (EVM.builtin_ins hb hm),
    h.2.1⟩

theorem wf_builtin_none (h : (Expression.FunctionCall f args).WellFormed EVM.dialect N Γ n)
    (hb : EVM.dialect.builtin f = some (kinds, mk)) (hm : mk (literalArgs kinds args) = none) :
    False := by
  rw [Expression.WellFormed, hb] at h
  simp only [hm] at h
  exact h.2

theorem wf_call (h : (Expression.FunctionCall f args).WellFormed EVM.dialect N Γ n)
    (hb : EVM.dialect.builtin f = none) (hI : Agrees N fs vars Γ)
    (hf : Funs.find? f fs = some (fn, fs')) :
    argsWellFormed EVM.dialect N Γ args ∧ args.length = fn.params.length ∧
      n = fn.rets.length ∧ Funs.WellFormed N fs' ∧
      fn.body.WellFormed EVM.dialect N (fn.scope fs') := by
  obtain ⟨hl, hw, hbody⟩ := find_some hI.wf hf
  rw [Expression.WellFormed, hb] at h
  simp only [hI.funs, hl] at h
  exact ⟨h.2.1, h.1, h.2.2, hw, hbody⟩

theorem wf_call_none (h : (Expression.FunctionCall f args).WellFormed EVM.dialect N Γ n)
    (hb : EVM.dialect.builtin f = none) (hI : Agrees N fs vars Γ)
    (hf : Funs.find? f fs = none) : False := by
  rw [Expression.WellFormed, hb] at h
  simp only [hI.funs, find_none hf] at h

theorem rets_count {fn : Fun} (h : names vars = fn.params ++ fn.rets) :
    ((vars.drop fn.params.length).map Prod.snd).length = fn.rets.length := by
  have := congrArg List.length h
  simp only [names, List.length_map, List.length_append] at this
  simp [this]

end

/-! ## The interpreter -/

/-- what a call with the arguments {name}`args` and {name}`n` values calls: a builtin, with its
arguments that are not literals, or a Yul function in scope, with the functions in scope at its
definition. Each case has the facts that the interpreter uses. -/
inductive Callee (N : List String) (Γ : Scope) (args : List Expression) (n : Nat) where
  | builtin (b : EVM.Builtin) (es : List Expression) (wf : argsWellFormed EVM.dialect N Γ es)
      (ins : es.length = EVM.ins b) (outs : EVM.outs b = n) (size : sizeOf es ≤ sizeOf args)
  | fn (fn : Fun) (fs' : Funs) (wf : argsWellFormed EVM.dialect N Γ args)
      (params : args.length = fn.params.length) (rets : n = fn.rets.length)
      (funs : Funs.WellFormed N fs') (body : fn.body.WellFormed EVM.dialect N (fn.scope fs'))

/-- the callee of a well-formed call of {name}`f`: a builtin name is always the builtin -/
def callee (h : (Expression.FunctionCall f args).WellFormed EVM.dialect N Γ n)
    (hI : Agrees N fs vars Γ) : Callee N Γ args n :=
  match hb : EVM.dialect.builtin f with
  | some (kinds, mk) =>
    match hm : mk (literalArgs kinds args) with
    | some b =>
      have hw := wf_builtin h hb hm
      .builtin b (exprArgs kinds args) hw.1 hw.2.1 hw.2.2 sizeOf_exprArgs
    | none => absurd h fun h => wf_builtin_none h hb hm
  | none =>
    match hf : Funs.find? f fs with
    | some (fn, fs') =>
      have hw := wf_call h hb hI hf
      .fn fn fs' hw.1 hw.2.1 hw.2.2.1 hw.2.2.2.1 hw.2.2.2.2
    | none => absurd h fun h => wf_call_none h hb hI hf

/-- the proof that an index is less than the number of arguments of a builtin -/
macro "arg_lt" : tactic => `(tactic| (simp only [EVM.ins] at *; omega))

section

variable (i : Input) (ρ : Readings) (N : List String)

/-- a builtin with the values {name}`args` of its arguments that are not literals. Each builtin
outside the 8 halts with {name}`Result.unsupported`. -/
def builtin (b : EVM.Builtin) (args : List Word) (h : args.length = EVM.ins b) (st : State) :
    Res st.clock Values (AfterExpr st.vars (EVM.outs b)) :=
  match b, h with
  | .Add, _ => ⟨.ok [args[0]'(by arg_lt) + args[1]'(by arg_lt)], st, Nat.le_refl _, rfl, rfl⟩
  | .Lt, _ =>
    ⟨.ok [lt (args[0]'(by arg_lt)) (args[1]'(by arg_lt))], st, Nat.le_refl _, rfl, rfl⟩
  | .Eq, _ =>
    ⟨.ok [eq (args[0]'(by arg_lt)) (args[1]'(by arg_lt))], st, Nat.le_refl _, rfl, rfl⟩
  | .Calldataload, _ =>
    ⟨.ok [calldataload i (args[0]'(by arg_lt))], st, Nat.le_refl _, rfl, rfl⟩
  | .Mload, _ => ⟨.ok [mload st.mem (args[0]'(by arg_lt))], st, Nat.le_refl _, rfl, rfl⟩
  | .Mstore, _ =>
    ⟨.ok [], { st with mem := mstore st.mem (args[0]'(by arg_lt)) (args[1]'(by arg_lt)) },
      Nat.le_refl _, rfl, rfl⟩
  | .Gas, _ => ⟨.ok [ρ st.reads], { st with reads := st.reads + 1 }, Nat.le_refl _, rfl, rfl⟩
  | .Return, _ =>
    ⟨.halt (.ret (read st.mem (args[0]'(by arg_lt)) (args[1]'(by arg_lt)))), st, Nat.le_refl _,
      rfl, trivial⟩
  | _, _ => ⟨.halt .unsupported, st, Nat.le_refl _, rfl, trivial⟩

mutual

/-- a statement -/
def exec (fs : Funs) (st : State) (Γ : Scope) :
    (s : Statement) → s.WellFormed EVM.dialect N Γ → Agrees N fs st.vars Γ →
      Res st.clock Outcome (AfterStmt Γ (Γ.after s).vars)
  | .Block b, h, hI =>
    (execBlock fs st Γ b h hI).up (Nat.le_refl _) fun _ _ q => AfterStmt.same q.vars q.fits
  | .FunctionDefinition .., _, hI =>
    ⟨.normal, st, Nat.le_refl _, AfterStmt.same hI.vars trivial⟩
  | .VariableDeclaration xs none, _, hI =>
    ⟨.normal, { st with vars := bind xs (List.replicate xs.length 0) (by simp) ++ st.vars },
      Nat.le_refl _, trivial, by simp [hI.vars], fun _ => by simp [hI.vars, Scope.after]⟩
  | .VariableDeclaration xs (some e), h, hI =>
    let ⟨v, st1, h1, p1⟩ := eval fs st Γ e xs.length h.2 hI
    have hv : names st1.vars = Γ.vars := by rw [p1.vars]; exact hI.vars
    match v, p1 with
    | .ok vs, p1 =>
      ⟨.normal, { st1 with vars := bind xs vs p1.count ++ st1.vars }, h1, trivial,
        by simp [hv], fun _ => by simp [hv, Scope.after]⟩
    | .halt r, _ => ⟨.halt r, st1, h1, AfterStmt.stop hv trivial (by simp)⟩
    | .timeout, _ => ⟨.timeout, st1, h1, AfterStmt.stop hv trivial (by simp)⟩
  | .Assignment xs e, h, hI =>
    let ⟨v, st1, h1, p1⟩ := eval fs st Γ e xs.length h.2.2 hI
    have hv : names st1.vars = Γ.vars := by rw [p1.vars]; exact hI.vars
    match v, p1 with
    | .ok vs, p1 =>
      ⟨.normal,
        { st1 with vars := st1.vars.assign xs vs (fun x hx => hv ▸ h.2.1 x hx) p1.count },
        h1, AfterStmt.same (by simp only [names_assign, hv]) trivial⟩
    | .halt r, _ => ⟨.halt r, st1, h1, AfterStmt.same hv trivial⟩
    | .timeout, _ => ⟨.timeout, st1, h1, AfterStmt.same hv trivial⟩
  | .If c b, h, hI =>
    let ⟨v, st1, h1, p1⟩ := eval fs st Γ c 1 h.1 hI
    have hI1 : Agrees N fs st1.vars Γ := hI.of_vars p1.vars
    match v, p1 with
    | .ok vs, p1 =>
      if vs.head (ne_nil_of_length p1.count) = 0 then
        ⟨.normal, st1, h1, AfterStmt.same hI1.vars trivial⟩
      else
        (execBlock fs st1 Γ b h.2 hI1).up h1 fun _ _ q => AfterStmt.same q.vars q.fits
    | .halt r, _ => ⟨.halt r, st1, h1, AfterStmt.same hI1.vars trivial⟩
    | .timeout, _ => ⟨.timeout, st1, h1, AfterStmt.same hI1.vars trivial⟩
  | .Expression e, h, hI =>
    let ⟨v, st1, h1, p1⟩ := eval fs st Γ e 0 h hI
    ⟨v.outcome, st1, h1, AfterStmt.same (by rw [p1.vars]; exact hI.vars) Values.outcome_fits⟩
  -- the variables of the init block are in scope in all of the loop
  | .ForLoop ⟨init⟩ c post body, h, hI =>
    let ⟨o, st1, h1, p1⟩ :=
      execs fs st { Γ with inLoopBody := false, inInit := true } init h.1
        ⟨hI.vars, hI.funs, hI.wf⟩
    if ho : o = .normal then
      let ⟨o, st2, h2, p2⟩ := loop fs st1
        { init.foldl Scope.after { Γ with inLoopBody := false, inInit := true } with
          inInit := Γ.inInit } c post body h.2.1 h.2.2.1 h.2.2.2 (by simp)
        ⟨p1.normal ho, by simp [hI.funs], hI.wf⟩
      ⟨o, restrict st st2, Nat.le_trans h2 h1, AfterStmt.same
        (by rw [names_restrict (by
              rw [p2.vars, hI.vars]
              exact Scope.foldl_vars_suffix (Γ := { Γ with inLoopBody := false, inInit := true })
                (ss := init))]
            exact hI.vars)
        (by have := p2.fits; cases o <;> simp_all [Outcome.Fits])⟩
    else
      ⟨o, restrict st st1, h1, AfterStmt.same
        (by rw [names_restrict (by rw [hI.vars]; exact p1.suffix)]; exact hI.vars)
        (by have := p1.fits; cases o <;> simp_all [Outcome.Fits])⟩
  | .Break, h, hI => ⟨.brk, st, Nat.le_refl _, AfterStmt.stop hI.vars h (by simp)⟩
  | .Continue, h, hI => ⟨.cont, st, Nat.le_refl _, AfterStmt.stop hI.vars h (by simp)⟩
  | .Leave, h, hI => ⟨.leave, st, Nat.le_refl _, AfterStmt.stop hI.vars h (by simp)⟩
termination_by s => (st.clock, sizeOf s)
decreasing_by all_goals decreasing_clock

/-- a block: its functions are in scope in all of it, and its variables only in it -/
def execBlock (fs : Funs) (st : State) (Γ : Scope) :
    (b : Block) → b.WellFormed EVM.dialect N Γ → Agrees N fs st.vars Γ →
      Res st.clock Outcome (AfterBlock Γ)
  | ⟨ss⟩, h, hI =>
    let ⟨o, st1, h1, p1⟩ :=
      execs (defs ss :: fs) st { Γ with funs := functions ss ++ Γ.funs } ss h.2
        (agrees_block h hI)
    ⟨o, restrict st st1, h1, p1.fits,
      by rw [names_restrict (by rw [hI.vars]; exact p1.suffix)]; exact hI.vars⟩
termination_by b => (st.clock, sizeOf b)
decreasing_by all_goals decreasing_clock

/-- statements in order, until one has an outcome that is not normal -/
def execs (fs : Funs) (st : State) (Γ : Scope) :
    (ss : List Statement) → statementsWellFormed EVM.dialect N Γ ss →
      Agrees N fs st.vars Γ →
      Res st.clock Outcome (AfterStmt Γ (ss.foldl Scope.after Γ).vars)
  | [], _, hI => ⟨.normal, st, Nat.le_refl _, AfterStmt.same hI.vars trivial⟩
  | s :: ss, h, hI =>
    let ⟨o, st1, h1, p1⟩ := exec fs st Γ s h.1 hI
    if ho : o = .normal then
      (execs fs st1 (Γ.after s) ss h.2 (agrees_after hI (p1.normal ho))).up h1
        fun _ _ q => AfterStmt.cons (ho ▸ p1) q
    else ⟨o, st1, h1, p1.fits, p1.suffix, fun e => absurd e ho⟩
termination_by ss => (st.clock, sizeOf ss)
decreasing_by all_goals decreasing_clock

/-- the iterations of a loop in the scope {name}`Γ` of its condition and post block -/
def loop (fs : Funs) (st : State) (Γ : Scope) (c : Expression) (post body : Block)
    (hc : c.WellFormed EVM.dialect N Γ 1)
    (hb : body.WellFormed EVM.dialect N { Γ with inLoopBody := true })
    (hp : post.WellFormed EVM.dialect N Γ) (hl : Γ.inLoopBody = false)
    (hI : Agrees N fs st.vars Γ) : Res st.clock Outcome (AfterBlock Γ) :=
  if _h0 : st.clock = 0 then ⟨.timeout, st, Nat.le_refl _, trivial, hI.vars⟩ else
  let ⟨v, st1, h1, p1⟩ := eval fs { st with clock := st.clock - 1 } Γ c 1 hc hI
  have hcl : st1.clock ≤ st.clock := Nat.le_trans h1 (Nat.sub_le _ _)
  have hI1 : Agrees N fs st1.vars Γ := hI.of_vars p1.vars
  match v, p1 with
  | .ok vs, p1 =>
    if vs.head (ne_nil_of_length p1.count) = 0 then ⟨.normal, st1, hcl, trivial, hI1.vars⟩ else
    let ⟨o, st2, h2, f2, n2⟩ :=
      execBlock fs st1 { Γ with inLoopBody := true } body hb ⟨hI1.vars, hI1.funs, hI1.wf⟩
    have hI2 : Agrees N fs st2.vars Γ := ⟨n2, hI.funs, hI.wf⟩
    match o, f2 with
    | .brk, _ => ⟨.normal, st2, Nat.le_trans h2 hcl, trivial, n2⟩
    | .normal, _ | .cont, _ =>
      let ⟨o, st3, h3, p3⟩ := execBlock fs st2 Γ post hp hI2
      match o, p3 with
      | .normal, p3 =>
        (loop fs st3 Γ c post body hc hb hp hl ⟨p3.vars, hI.funs, hI.wf⟩).up
          (Nat.le_trans h3 (Nat.le_trans h2 hcl)) fun _ _ q => q
      | .brk, p3 => absurd p3.fits (by simp [Outcome.Fits, hl])
      | .cont, p3 => absurd p3.fits (by simp [Outcome.Fits, hl])
      | .leave, p3 => ⟨.leave, st3, Nat.le_trans h3 (Nat.le_trans h2 hcl), p3⟩
      | .halt r, p3 => ⟨.halt r, st3, Nat.le_trans h3 (Nat.le_trans h2 hcl), p3⟩
      | .timeout, p3 => ⟨.timeout, st3, Nat.le_trans h3 (Nat.le_trans h2 hcl), p3⟩
    | .leave, f2 => ⟨.leave, st2, Nat.le_trans h2 hcl, f2, n2⟩
    | .halt r, _ => ⟨.halt r, st2, Nat.le_trans h2 hcl, trivial, n2⟩
    | .timeout, _ => ⟨.timeout, st2, Nat.le_trans h2 hcl, trivial, n2⟩
  | .halt r, _ => ⟨.halt r, st1, hcl, trivial, hI1.vars⟩
  | .timeout, _ => ⟨.timeout, st1, hcl, trivial, hI1.vars⟩
termination_by (st.clock, 0)
decreasing_by all_goals decreasing_clock

/-- an expression with {name}`n` values -/
def eval (fs : Funs) (st : State) (Γ : Scope) :
    (e : Expression) → (n : Nat) → e.WellFormed EVM.dialect N Γ n →
      Agrees N fs st.vars Γ →
      Res st.clock Values (AfterExpr st.vars n)
  | .Literal l, _, h, _ => ⟨.ok [literalValue l], st, Nat.le_refl _, rfl, h.2.symm⟩
  | .Identifier x, _, h, hI =>
    ⟨.ok [st.vars.get x (hI.vars ▸ h.1)], st, Nat.le_refl _, rfl, h.2.symm⟩
  | .FunctionCall _ args, n, h, hI =>
    match callee h hI with
    | .builtin b es hw hl hn _ =>
      let ⟨v, st1, h1, p1⟩ := evals fs st Γ es hw hI
      match v, p1 with
      | .ok vs, p1 =>
        (builtin i ρ b vs (p1.count.trans hl) st1).up h1
          fun _ _ q => ⟨q.vars.trans p1.vars, hn ▸ q.count⟩
      | .halt r, p1 => ⟨.halt r, st1, h1, p1.vars, trivial⟩
      | .timeout, p1 => ⟨.timeout, st1, h1, p1.vars, trivial⟩
    | .fn fn fs' hw hl hn hfs hbody =>
      let ⟨v, st1, h1, p1⟩ := evals fs st Γ args hw hI
      match v, p1 with
      | .ok vs, p1 =>
        if _h0 : st1.clock = 0 then ⟨.timeout, st1, h1, p1.vars, trivial⟩ else
        let callee : State :=
          { st1 with
            vars := bind fn.params vs (p1.count.trans hl) ++
              bind fn.rets (List.replicate fn.rets.length 0) (by simp)
            clock := st1.clock - 1 }
        let ⟨o, st2, h2, f2, n2⟩ :=
          execBlock fs' callee (fn.scope fs') fn.body hbody
            ⟨by simp [callee, Fun.scope], rfl, hfs⟩
        have hle : st2.clock ≤ st.clock := Nat.le_trans h2 (Nat.le_trans (Nat.sub_le _ _) h1)
        match o, f2 with
        | .halt r, _ => ⟨.halt r, { st2 with vars := st1.vars }, hle, p1.vars, trivial⟩
        | .timeout, _ => ⟨.timeout, { st2 with vars := st1.vars }, hle, p1.vars, trivial⟩
        -- the values of the return variables: the variables after the parameters
        | .normal, _ | .leave, _ =>
          ⟨.ok ((st2.vars.drop fn.params.length).map Prod.snd), { st2 with vars := st1.vars },
            hle,
            p1.vars, (rets_count n2).trans hn.symm⟩
        | .brk, f2 => absurd f2 (by simp [Outcome.Fits, Fun.scope])
        | .cont, f2 => absurd f2 (by simp [Outcome.Fits, Fun.scope])
      | .halt r, p1 => ⟨.halt r, st1, h1, p1.vars, trivial⟩
      | .timeout, p1 => ⟨.timeout, st1, h1, p1.vars, trivial⟩
termination_by e => (st.clock, sizeOf e)
decreasing_by all_goals decreasing_clock

/-- arguments, from the last to the first, as in Yul; each gives one value -/
def evals (fs : Funs) (st : State) (Γ : Scope) :
    (es : List Expression) → argsWellFormed EVM.dialect N Γ es → Agrees N fs st.vars Γ →
      Res st.clock Values (AfterExpr st.vars es.length)
  | [], _, _ => ⟨.ok [], st, Nat.le_refl _, rfl, rfl⟩
  | e :: es, h, hI =>
    let ⟨v, st1, h1, p1⟩ := evals fs st Γ es h.2 hI
    match v, p1 with
    | .ok vs, p1 =>
      let ⟨v, st2, h2, p2⟩ := eval fs st1 Γ e 1 h.1 (hI.of_vars p1.vars)
      match v, p2 with
      | .ok w, p2 =>
        ⟨.ok (w.head (ne_nil_of_length p2.count) :: vs), st2, Nat.le_trans h2 h1,
          p2.vars.trans p1.vars, congrArg (· + 1) p1.count⟩
      | .halt r, p2 => ⟨.halt r, st2, Nat.le_trans h2 h1, p2.vars.trans p1.vars, trivial⟩
      | .timeout, p2 => ⟨.timeout, st2, Nat.le_trans h2 h1, p2.vars.trans p1.vars, trivial⟩
    | .halt r, p1 => ⟨.halt r, st1, h1, p1.vars, trivial⟩
    | .timeout, p1 => ⟨.timeout, st1, h1, p1.vars, trivial⟩
termination_by es => (st.clock, sizeOf es)
decreasing_by all_goals decreasing_clock

end

end

/-- the outcome and the state at the end of the code of {name}`P` with clock {name}`k` -/
def top (P : WFObject) (i : Input) (ρ : Readings) (k : Nat) : Res k Outcome (AfterBlock {}) :=
  execBlock i ρ P.1.dataNames [] (start k) {} P.1.code (Object.wellFormed_code P.2)
    ⟨rfl, rfl, trivial⟩

/-- the result of a run with this outcome at the end of the code, or {name}`none` at a timeout.
The end of the code is a halt with no data. -/
def Outcome.result : (o : Outcome) → o.Fits {} → Option Result
  | .normal, _ => some (.ret [])
  | .halt r, _ => some r
  | .timeout, _ => none
  | .brk, h => absurd h (by simp [Outcome.Fits])
  | .cont, h => absurd h (by simp [Outcome.Fits])
  | .leave, h => absurd h (by simp [Outcome.Fits])

/-- the result of a run with the outcome and the state {name}`r` at the end of the code -/
def Res.result (r : Res c Outcome (AfterBlock {})) : Option Result := r.val.result r.post.fits

theorem Res.result_eq_none {r : Res c Outcome (AfterBlock {})} :
    r.result = none ↔ r.val = .timeout := by
  obtain ⟨o, st, le, f, v⟩ := r
  cases o <;> first
    | (simp [Res.result, Outcome.result]; done)
    | exact absurd f (by simp [Outcome.Fits])

/-- the result of the code of {name}`P` with clock {name}`k`, or {name}`none` at a timeout -/
def run (P : WFObject) (i : Input) (ρ : Readings) (k : Nat) : Option Result :=
  (top P i ρ k).result

/-! ## Behaviours

As in the clocked interpreter row of the table in {lit}`doc/gas-equivalence.md`: a run ends with
{lit}`r` if some clock gives {lit}`r`, and it diverges if each clock gives a timeout.
-/

/-- {lit}`⟪P, i, ρ⟫ ⇝ b`: the run of the code of {name}`P` with input {name}`i` and readings
{name}`ρ` has the behaviour {lit}`b` -/
def Behaves (P : WFObject) (i : Input) (ρ : Readings) : Beh → Prop
  | .ends r => ∃ k, run P i ρ k = some r
  | .diverges => ∀ k, run P i ρ k = none

@[inherit_doc] scoped notation:50 "⟪" P ", " i ", " ρ "⟫" " ⇝ " b:50 => Behaves P i ρ b

open Classical in
/-- the behaviour of the run: the result of a clock that gives one, else divergence.
The theorem {lit}`beh_eq` shows that it is the only behaviour. -/
noncomputable def beh (P : WFObject) (i : Input) (ρ : Readings) : Beh :=
  if h : ∃ r k, run P i ρ k = some r then .ends h.choose else .diverges

end Clocked

end Yul
