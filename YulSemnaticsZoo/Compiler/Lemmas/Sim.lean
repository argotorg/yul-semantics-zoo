import YulSemnaticsZoo.Compiler.Lemmas.Steps
import YulSemnaticsZoo.Compiler.Lemmas.Names

set_option doc.verso true

/-!
# Compiler: the simulation

The relation between a Yul state and an EVM state at the code of a statement: the stack has the
values of the Yul variables (in the order of {lit}`Vars`) on the words {lit}`rest` of the code
around it, the memory and the number of reads are the same, the compiler knows the names of the
variables, and each function in scope is compiled in the program ({lit}`Pre`, {lit}`FunsOK`).

{lit}`sim`: for each function of the interpreter and each outcome, the EVM run of the compiled
code gives the same outcome: a halt with the same result, a timeout with the same clock, or the
code after it (or the target of {lit}`break`, {lit}`continue` and {lit}`leave`) in the same
state, after at least as many steps as the Yul clock decreases ({lit}`StmtPost`,
{lit}`EvalPost`).
-/

namespace Compiler
open Semantics Yul Yul.Clocked

theorem except_bind_ok {x : Except ε α} {f : α → Except ε β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [Bind.bind, Except.bind]

theorem except_pure_ok {a b : α} : (pure a : Except ε α) = .ok b ↔ a = b := by
  simp [pure, Except.pure]

theorem except_throw_ok : (throw e : Except ε α) = .ok b ↔ False := by
  simp [throw, throwThe, MonadExceptOf.throw]

theorem except_ite_ok [Decidable c] {a b : Except ε α} :
    (if c then a else b) = .ok x ↔ (c ∧ a = .ok x) ∨ (¬c ∧ b = .ok x) := by
  by_cases h : c <;> simp [h]

theorem except_unless_ok [Decidable c] {e : ε} {a : Unit} :
    ((if c then pure PUnit.unit else throw e : Except ε Unit) = .ok a) ↔ c := by
  by_cases h : c <;> simp [h, except_pure_ok, except_throw_ok]

/-- the simp set that inverts a compile step that gives code -/
macro "inv" h:ident : tactic => `(tactic| simp only [except_bind_ok, except_pure_ok, except_unless_ok,
  except_ite_ok, or_false, false_or, and_true, true_and, not_and, exists_prop, exists_const,
  except_throw_ok, Prod.mk.injEq, ite_true, ite_false, pure_bind, exists_and_left, false_and,
  exists_false, and_false, exists_eq_left'] at $h:ident)

/-- the values of the variables -/
abbrev vals (vs : Vars) : List Word := vs.map (·.2)

section
variable (prog : Code) (inp : Input) (ρ : Readings) (N : List String)

/-- the function is compiled in the scope {name}`scope`, and its code is in the program -/
def FunAt (scope : CFuns) (fn : Fun) (info : FunInfo) : Prop :=
  info.params = fn.params.length ∧ info.rets = fn.rets.length ∧
  ∃ q, info.label = (q, 0) ∧
    ∃ cb c, compileBlock (funCtx scope q fn.params fn.rets) (q ++ [0]) fn.body = .ok cb ∧
      funCode q fn.params.length fn.rets.length cb = .ok c ∧ ∃ p, At prog p c

/-- the functions of a block in Yul and in the compiler, in the same order, with the same names,
and {name}`P` for each pair -/
def Match (P : Fun → FunInfo → Prop) : List (Identifier × Fun) → List (Identifier × FunInfo) → Prop
  | [], [] => True
  | (f, fn) :: l, (g, info) :: cl => f = g ∧ P fn info ∧ Match P l cl
  | _, _ => False

/-- the functions in scope in Yul and in the compiler have the same names, and each is compiled
in the program -/
def FunsOK : Funs → CFuns → Prop
  | [], [] => True
  | l :: ls, cl :: cls => Match (FunAt prog (cl :: cls)) l cl ∧ FunsOK ls cls
  | _, _ => False

/-- the EVM goes from {name}`s` to a state with the pc, the stack, and the memory and the reads
of {name}`st'`, in at least {lit}`c - st'.clock` steps -/
def Goes (s : EVM.State) (n c : Nat) (st' : State) (pc : Nat) (stack : List Word) : Prop :=
  ∃ j s', Steps (layout prog) inp ρ s n j s' st'.reads ∧ Is s' pc stack st'.mem ∧ c ≤ j + st'.clock

/-- the EVM has the outcome of an expression that starts in {name}`st` and has {name}`k` values:
its values on the stack at {name}`pc`, the same halt, or a timeout -/
def EvalPost (s : EVM.State) (n : Nat) (st : State) (k pc : Nat) : Values × State → Prop
  | (.ok vs, st') =>
    vs.length = k ∧ st'.vars = st.vars ∧ Goes prog inp ρ s n st.clock st' pc (vs ++ s.stack)
  | (.halt r, _) => Halts (layout prog) inp ρ s n r
  | (.timeout, _) => Survives (layout prog) inp ρ s n st.clock

/-- the EVM has the outcome of a statement that starts in {name}`st`: the variables on
{name}`rest` at {name}`pc`, or at the target of {lit}`break`, {lit}`continue` or {lit}`leave`
with the variables of the loop or function, the same halt, or a timeout -/
def StmtPost (ctx : Ctx) (s : EVM.State) (n : Nat) (st : State) (pc : Nat) (rest : List Word) :
    Outcome × State → Prop
  | (.normal, st') => Goes prog inp ρ s n st.clock st' pc (vals st'.vars ++ rest)
  | (.brk, st') => ∃ l lc d, ctx.loop = some (l, lc, d) ∧
    Goes prog inp ρ s n st.clock st' (pos prog l) (vals (st'.vars.drop (st'.vars.length - d)) ++ rest)
  | (.cont, st') => ∃ l lc d, ctx.loop = some (l, lc, d) ∧
    Goes prog inp ρ s n st.clock st' (pos prog lc) (vals (st'.vars.drop (st'.vars.length - d)) ++ rest)
  | (.leave, st') => ∃ l d, ctx.leave = some (l, d) ∧
    Goes prog inp ρ s n st.clock st' (pos prog l) (vals (st'.vars.drop (st'.vars.length - d)) ++ rest)
  | (.halt r, _) => Halts (layout prog) inp ρ s n r
  | (.timeout, _) => Survives (layout prog) inp ρ s n st.clock

/-- the EVM state {name}`s` is the Yul state {name}`st` at a statement in the context
{name}`ctx` -/
structure Pre (ctx : Ctx) (fs : Funs) (st : State) (s : EVM.State) (n : Nat) (rest : List Word) :
    Prop where
  funs : FunsOK prog fs ctx.funs
  names : ctx.vars = names st.vars
  loop : ∀ l lc d, ctx.loop = some (l, lc, d) →
    d ≤ st.vars.length ∧ (∃ p, At prog p [.label l]) ∧ ∃ p, At prog p [.label lc]
  leave : ∀ l d, ctx.leave = some (l, d) → d ≤ st.vars.length ∧ ∃ p, At prog p [.label l]
  stack : s.stack = vals st.vars ++ rest
  mem : s.mem = st.mem
  reads : n = st.reads

/-! ## The motives

One for each function of the interpreter, with its arguments. An expression has the number of
values that the proof of well-formedness gives. -/

def M1 (fs : Funs) (st : State) (Γ : Scope) (s : Statement) (h : s.WellFormed EVM.dialect N Γ)
    (hI : Agrees N fs st.vars Γ) : Prop :=
  ∀ ctx q code vars', compileStmt ctx q s = .ok (code, vars') → ∀ p, At prog p code →
    ∀ s0 n rest, s0.pc = p → Pre prog ctx fs st s0 n rest →
      StmtPost prog inp ρ ctx s0 n st (p + size code) rest
        ((exec inp ρ N fs st Γ s h hI).val, (exec inp ρ N fs st Γ s h hI).st) ∧
      ((exec inp ρ N fs st Γ s h hI).val = .normal →
        vars' = names (exec inp ρ N fs st Γ s h hI).st.vars)

def M2 (fs : Funs) (st : State) (Γ : Scope) (c : Expression) (post body : Block)
    (hc : c.WellFormed EVM.dialect N Γ 1)
    (hb : body.WellFormed EVM.dialect N { Γ with inLoopBody := true })
    (hp : post.WellFormed EVM.dialect N Γ) (hl : Γ.inLoopBody = false)
    (hI : Agrees N fs st.vars Γ) : Prop :=
  ∀ ctx q cc cb cp, ctx.loop = none → compileExpr ctx (q ++ [1]) 0 c = .ok cc →
    compileBlock { ctx with loop := some ((q, 2), (q, 1), ctx.vars.length) } (q ++ [2]) body =
      .ok cb →
    compileBlock ctx (q ++ [3]) post = .ok cp → ∀ p, At prog p (loopCode q cc cb cp) →
    ∀ s0 n rest, s0.pc = p → Pre prog ctx fs st s0 n rest →
      StmtPost prog inp ρ ctx s0 n st (p + size (loopCode q cc cb cp)) rest
        ((loop inp ρ N fs st Γ c post body hc hb hp hl hI).val,
          (loop inp ρ N fs st Γ c post body hc hb hp hl hI).st)

def M3 (fs : Funs) (st : State) (Γ : Scope) (b : Block) (h : b.WellFormed EVM.dialect N Γ)
    (hI : Agrees N fs st.vars Γ) : Prop :=
  ∀ ctx q code, compileBlock ctx q b = .ok code → ∀ p, At prog p code →
    ∀ s0 n rest, s0.pc = p → Pre prog ctx fs st s0 n rest →
      StmtPost prog inp ρ ctx s0 n st (p + size code) rest
        ((execBlock inp ρ N fs st Γ b h hI).val, (execBlock inp ρ N fs st Γ b h hI).st)

def M4 (fs : Funs) (st : State) (Γ : Scope) (ss : List Statement)
    (h : statementsWellFormed EVM.dialect N Γ ss) (hI : Agrees N fs st.vars Γ) : Prop :=
  ∀ ctx q j code vars', compileStmts ctx q j ss = .ok (code, vars') → ∀ p, At prog p code →
    ∀ s0 n rest, s0.pc = p → Pre prog ctx fs st s0 n rest →
      StmtPost prog inp ρ ctx s0 n st (p + size code) rest
        ((execs inp ρ N fs st Γ ss h hI).val, (execs inp ρ N fs st Γ ss h hI).st) ∧
      ((execs inp ρ N fs st Γ ss h hI).val = .normal →
        vars' = names (execs inp ρ N fs st Γ ss h hI).st.vars)

def M5 (fs : Funs) (st : State) (Γ : Scope) (e : Expression) (k : Nat)
    (h : e.WellFormed EVM.dialect N Γ k) (hI : Agrees N fs st.vars Γ) : Prop :=
  ∀ ctx q d code, compileExpr ctx q d e = .ok code → ∀ p, At prog p code →
    FunsOK prog fs ctx.funs → ctx.vars = names st.vars →
    ∀ s0 n T rest, T.length = d → s0.pc = p → s0.stack = T ++ vals st.vars ++ rest →
      s0.mem = st.mem → n = st.reads →
      EvalPost prog inp ρ s0 n st k (p + size code)
        ((eval inp ρ N fs st Γ e k h hI).val, (eval inp ρ N fs st Γ e k h hI).st)

def M6 (fs : Funs) (st : State) (Γ : Scope) (es : List Expression)
    (h : argsWellFormed EVM.dialect N Γ es) (hI : Agrees N fs st.vars Γ) : Prop :=
  ∀ ctx q d code, compileArgs ctx q d es = .ok code → ∀ p, At prog p code →
    FunsOK prog fs ctx.funs → ctx.vars = names st.vars →
    ∀ s0 n T rest, T.length = d → s0.pc = p → s0.stack = T ++ vals st.vars ++ rest →
      s0.mem = st.mem → n = st.reads →
      EvalPost prog inp ρ s0 n st es.length (p + size code)
        ((evals inp ρ N fs st Γ es h hI).val, (evals inp ρ N fs st Γ es h hI).st)

end

variable {prog : Code} {inp : Input} {ρ : Readings} {N : List String}

/-! ## Runs that go to a state -/

theorem Goes.pre (h : Steps (layout prog) inp ρ s n j s1 n1)
    (h' : Goes prog inp ρ s1 n1 c st' pc stack) : Goes prog inp ρ s n c st' pc stack := by
  obtain ⟨j', s', h', hs, hc⟩ := h'
  exact ⟨j + j', s', h.trans h', hs, by omega⟩

theorem Goes.bind (h : Goes prog inp ρ s n c st1 pc1 stk1)
    (h' : ∀ s1, Is s1 pc1 stk1 st1.mem → Goes prog inp ρ s1 st1.reads st1.clock st2 pc2 stk2) :
    Goes prog inp ρ s n c st2 pc2 stk2 := by
  obtain ⟨j, s1, h, hs, hc⟩ := h
  obtain ⟨j', s2, h', hs', hc'⟩ := h' s1 hs
  exact ⟨j + j', s2, h.trans h', hs', by omega⟩

theorem Goes.survives (h : Goes prog inp ρ s n c st1 pc1 stk1)
    (h' : ∀ s1, Is s1 pc1 stk1 st1.mem → Survives (layout prog) inp ρ s1 st1.reads st1.clock) :
    Survives (layout prog) inp ρ s n c := by
  obtain ⟨j, s1, h, hs, hc⟩ := h
  exact Survives.of_steps h (h' s1 hs) hc

theorem Goes.halts (h : Goes prog inp ρ s n c st1 pc1 stk1)
    (h' : ∀ s1, Is s1 pc1 stk1 st1.mem → Halts (layout prog) inp ρ s1 st1.reads r) :
    Halts (layout prog) inp ρ s n r := by
  obtain ⟨j, s1, h, hs, hc⟩ := h
  exact Halts.of_steps h (h' s1 hs)

theorem Goes.mono (h : Goes prog inp ρ s n c st' pc stack) (hc : c' ≤ c) :
    Goes prog inp ρ s n c' st' pc stack := by
  obtain ⟨j, s', h, hs, hc'⟩ := h
  exact ⟨j, s', h, hs, by omega⟩

theorem Goes.refl (hs : Is s pc stack st.mem) (hn : n = st.reads) (hc : c ≤ st.clock) :
    Goes prog inp ρ s n c st pc stack := ⟨0, s, hn ▸ .refl, hs, by omega⟩

theorem Survives.pre (h : Steps (layout prog) inp ρ s n j s1 n1)
    (h' : Survives (layout prog) inp ρ s1 n1 c) (hc : m ≤ j + c) :
    Survives (layout prog) inp ρ s n m := Survives.of_steps h h' hc

theorem Survives.zero : Survives (layout prog) inp ρ s n 0 := ⟨s, n, .refl⟩

theorem Halts.pre (h : Steps (layout prog) inp ρ s n j s1 n1)
    (h' : Halts (layout prog) inp ρ s1 n1 r) : Halts (layout prog) inp ρ s n r :=
  Halts.of_steps h h'

theorem At.at {s : EVM.State} (h : At prog p c) (e : s.pc = p) : At prog s.pc c := e ▸ h

/-! ## Functions in scope -/

theorem Match.lookup (h : Match P l cl) (hf : cl.lookup f = some info) :
    ∃ fn, l.lookup f = some fn ∧ P fn info := by
  induction l generalizing cl with
  | nil => cases cl <;> simp_all [Match]
  | cons a l ih =>
    obtain ⟨g, fn⟩ := a
    cases cl with
    | nil => simp [Match] at h
    | cons b cl =>
      obtain ⟨g', info'⟩ := b
      obtain ⟨rfl, hP, hM⟩ := h
      by_cases hfg : f = g
      · subst hfg; simp [List.lookup] at hf; subst hf; exact ⟨fn, by simp [List.lookup], hP⟩
      · have hb : (f == g) = false := by simpa using hfg
        simp [List.lookup, hb] at hf ⊢
        exact ih hM hf

theorem Match.lookup_none (h : Match P l cl) (hf : cl.lookup f = none) : l.lookup f = none := by
  induction l generalizing cl with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨g, fn⟩ := a
    cases cl with
    | nil => simp [Match] at h
    | cons b cl =>
      obtain ⟨g', info'⟩ := b
      obtain ⟨rfl, hP, hM⟩ := h
      by_cases hfg : f = g
      · subst hfg; simp [List.lookup] at hf
      · have hb : (f == g) = false := by simpa using hfg
        simp only [List.lookup, hb] at hf ⊢
        exact ih hM hf

theorem FunsOK.find (h : FunsOK prog fs cfs) (hf : cfs.find? f = some (info, cfs')) :
    ∃ fn fs', Funs.find? f fs = some (fn, fs') ∧ FunAt prog cfs' fn info ∧
      FunsOK prog fs' cfs' := by
  induction fs generalizing cfs with
  | nil => cases cfs <;> simp_all [FunsOK, CFuns.find?]
  | cons l ls ih =>
    cases cfs with
    | nil => simp [FunsOK] at h
    | cons cl cls =>
      have h' := h
      obtain ⟨hM, hR⟩ := h
      simp only [CFuns.find?] at hf
      split at hf
      · next info' hl =>
        cases hf
        obtain ⟨fn, hfn, hP⟩ := hM.lookup hl
        exact ⟨fn, l :: ls, by simp [Funs.find?, hfn], hP, h'⟩
      · next hl =>
        obtain ⟨fn, fs', h1, h2, h3⟩ := ih hR hf
        exact ⟨fn, fs', by simp [Funs.find?, hM.lookup_none hl, h1], h2, h3⟩

/-! ## Variables -/

theorem get_of_idx {l : Vars} (h : (names l).idxOf? x = some j) (hx : x ∈ names l) :
    (vals l)[j]? = some (Vars.get l x hx) := by
  induction l generalizing j with
  | nil => simp at h
  | cons a l ih =>
    obtain ⟨y, w⟩ := a
    by_cases hy : y = x
    · subst hy; simp [List.idxOf?_cons] at h; subst h; simp [Vars.get]
    · simp [List.idxOf?_cons, hy] at h
      obtain ⟨j', hj, rfl⟩ := h
      have := ih hj (mem_names_tail hx hy)
      simpa [Vars.get, hy] using this

theorem vals_set {l : Vars} (h : (names l).idxOf? x = some j) (hx : x ∈ names l) :
    vals (Vars.set l x hx v) = (vals l).set j v := by
  induction l generalizing j with
  | nil => simp at h
  | cons a l ih =>
    obtain ⟨y, w⟩ := a
    by_cases hy : y = x
    · subst hy; simp [List.idxOf?_cons] at h; subst h; simp [Vars.set]
    · simp [List.idxOf?_cons, hy] at h
      obtain ⟨j', hj, rfl⟩ := h
      simp [Vars.set, hy, ih hj (mem_names_tail hx hy)]

theorem vals_append {a b : Vars} : vals (a ++ b) = vals a ++ vals b := List.map_append

theorem vals_bind {h : vs.length = xs.length} : vals (bind xs vs h) = vs := by
  induction xs generalizing vs with
  | nil => cases vs with
    | nil => rfl
    | cons => simp at h
  | cons x xs ih => cases vs with
    | nil => simp at h
    | cons v vs => simp only [Clocked.bind, List.map_cons, ih]

/-! ## The compiled code -/

theorem compileStmts_cons (h : compileStmts ctx q j (s :: ss) = .ok (code, vars')) :
    ∃ c vars cs, compileStmt ctx (q ++ [j]) s = .ok (c, vars) ∧
      compileStmts { ctx with vars } q (j + 1) ss = .ok (cs, vars') ∧ code = c ++ cs := by
  simp only [compileStmts, except_bind_ok] at h
  obtain ⟨⟨c, vars⟩, h1, ⟨cs, vars''⟩, h2, h3⟩ := h
  cases h3
  exact ⟨c, vars, cs, h1, h2, rfl⟩

theorem compileFunDef (h : compileStmt ctx q (.FunctionDefinition f ps rs body) = .ok (code, vars')) :
    ∃ cb c, compileBlock (funCtx ctx.funs q ps rs) (q ++ [0]) body = .ok cb ∧
      funCode q ps.length rs.length cb = .ok c ∧
      code = [.push (q, 1), .op .Jump] ++ c ++ [.label (q, 1)] ∧ vars' = ctx.vars := by
  rw [compileStmt] at h
  inv h
  obtain ⟨cb, hb, c, hc, rfl, rfl⟩ := h
  exact ⟨cb, c, hb, hc, rfl, rfl⟩

theorem match_defs (h : compileStmts ctx q j ss = .ok (code, vars')) (hA : At prog p code) :
    Match (FunAt prog ctx.funs) (defs ss) (cdefs q j ss) := by
  induction ss generalizing ctx j p code vars' with
  | nil => simp [defs, cdefs, Match]
  | cons s ss ih =>
    obtain ⟨c, vars, cs, h1, h2, rfl⟩ := compileStmts_cons h
    have ih' := ih h2 hA.right
    cases s with
    | FunctionDefinition f ps rs body =>
      obtain ⟨cb, c', hb, hc, rfl, rfl⟩ := compileFunDef h1
      refine ⟨rfl, ⟨rfl, rfl, q ++ [j], rfl, cb, c', hb, hc,
        p + size [Item.push (q ++ [j], 1), .op .Jump], ?_⟩, ih'⟩
      have := hA.left
      exact (At.left (a := [Item.push (q ++ [j], 1), .op .Jump] ++ c') this).right
    | _ => exact ih'

theorem funsOK_scope (hF : FunsOK prog fs ctx.funs)
    (h : compileStmts (scope ctx q ss) q 0 ss = .ok (code, vars')) (hA : At prog p code) :
    FunsOK prog (defs ss :: fs) (scope ctx q ss).funs :=
  ⟨match_defs h hA, hF⟩

/-! ## Chains of steps -/

theorem Goes.thenS (h : ∃ s', Steps (layout prog) inp ρ s n j s' n' ∧ Is s' pc' stk' m')
    (k : ∀ s', Is s' pc' stk' m' → Goes prog inp ρ s' n' c st pc stk) :
    Goes prog inp ρ s n c st pc stk := by
  obtain ⟨s', h, hs⟩ := h
  exact Goes.pre h (k s' hs)

theorem Survives.thenS (h : ∃ s', Steps (layout prog) inp ρ s n j s' n' ∧ Is s' pc' stk' m')
    (k : ∀ s', Is s' pc' stk' m' → Survives (layout prog) inp ρ s' n' c) (hc : m ≤ j + c) :
    Survives (layout prog) inp ρ s n m := by
  obtain ⟨s', h, hs⟩ := h
  exact Survives.pre h (k s' hs) hc

theorem Halts.thenS (h : ∃ s', Steps (layout prog) inp ρ s n j s' n' ∧ Is s' pc' stk' m')
    (k : ∀ s', Is s' pc' stk' m' → Halts (layout prog) inp ρ s' n' r) :
    Halts (layout prog) inp ρ s n r := by
  obtain ⟨s', h, hs⟩ := h
  exact Halts.pre h (k s' hs)

theorem Goes.done (h : ∃ s', Steps (layout prog) inp ρ s n j s' n' ∧ Is s' pc' stk' m)
    (hpc : pc' = pc) (hstk : stk' = stk) (hm : m = st.mem) (hn : n' = st.reads)
    (hc : c ≤ j + st.clock) : Goes prog inp ρ s n c st pc stk := by
  obtain ⟨s', h, hs⟩ := h
  subst hpc hstk hm hn
  exact ⟨j, s', h, hs, hc⟩

theorem Goes.preC (h : Steps (layout prog) inp ρ s n j s1 n1)
    (h' : Goes prog inp ρ s1 n1 c' st' pc stack) (hc : c ≤ j + c') :
    Goes prog inp ρ s n c st' pc stack := by
  obtain ⟨j', s', h', hs, hc'⟩ := h'
  exact ⟨j + j', s', h.trans h', hs, by omega⟩

theorem Goes.cast (h : Goes prog inp ρ s n c st pc stk) (hpc : pc = pc') (hstk : stk = stk') :
    Goes prog inp ρ s n c st pc' stk' := hpc ▸ hstk ▸ h

theorem Halts.one (h : EVM.step (EVM.abstract ρ) (layout prog) inp s n = .halt r n') :
    Halts (layout prog) inp ρ s n r := ⟨0, s, n, n', .refl, h⟩

theorem Is.at (h : Is s pc stk m) (hA : At prog pc c) : At prog s.pc c := h.1 ▸ hA

theorem toNat_ofNat_pos (h : v < 2 ^ 16) : (BitVec.ofNat 256 (v % 2 ^ 16)).toNat = v := by
  rw [Nat.mod_eq_of_lt h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-! ## Outcomes of statements -/

/-- a run to a state, then the outcome of a statement from there -/
theorem StmtPost.pre (g : Goes prog inp ρ s n st.clock st1 pc1 stk1)
    (h : ∀ s1, Is s1 pc1 stk1 st1.mem → StmtPost prog inp ρ ctx s1 st1.reads st1 pc rest r) :
    StmtPost prog inp ρ ctx s n st pc rest r := by
  obtain ⟨o, st'⟩ := r
  obtain ⟨j, s1, h1, hs1, hc⟩ := g
  have h' := h s1 hs1
  cases o with
  | normal => exact Goes.preC h1 h' hc
  | brk => obtain ⟨l, lc, d, hl, g'⟩ := h'; exact ⟨l, lc, d, hl, Goes.preC h1 g' hc⟩
  | cont => obtain ⟨l, lc, d, hl, g'⟩ := h'; exact ⟨l, lc, d, hl, Goes.preC h1 g' hc⟩
  | leave => obtain ⟨l, d, hl, g'⟩ := h'; exact ⟨l, d, hl, Goes.preC h1 g' hc⟩
  | halt r => exact Halts.pre h1 h'
  | timeout => exact Survives.pre h1 h' hc

/-- steps without a change of the Yul state, then the outcome of a statement -/
theorem StmtPost.steps (h : Steps (layout prog) inp ρ s n j s1 n)
    (h' : StmtPost prog inp ρ ctx s1 n st pc rest r) : StmtPost prog inp ρ ctx s n st pc rest r := by
  obtain ⟨o, st'⟩ := r
  cases o with
  | normal => exact Goes.preC h h' (by omega)
  | brk => obtain ⟨l, lc, d, hl, g'⟩ := h'; exact ⟨l, lc, d, hl, Goes.preC h g' (by omega)⟩
  | cont => obtain ⟨l, lc, d, hl, g'⟩ := h'; exact ⟨l, lc, d, hl, Goes.preC h g' (by omega)⟩
  | leave => obtain ⟨l, d, hl, g'⟩ := h'; exact ⟨l, d, hl, Goes.preC h g' (by omega)⟩
  | halt r => exact Halts.pre h h'
  | timeout => exact Survives.pre h h' (by omega)

theorem StmtPost.cast_pc (h : StmtPost prog inp ρ ctx s n st pc rest r) (e : pc = pc') :
    StmtPost prog inp ρ ctx s n st pc' rest r := e ▸ h

/-- a {lit}`JUMPDEST` after the code -/
theorem StmtPost.label (h : StmtPost prog inp ρ ctx s n st pc rest r) (hL : At prog pc [.label l]) :
    StmtPost prog inp ρ ctx s n st (pc + 1) rest r := by
  obtain ⟨o, st'⟩ := r
  cases o with
  | normal =>
    exact Goes.bind h fun s1 hs1 => Goes.done (st_label (n := st'.reads) (ρ := ρ) (inp := inp)
      (hL.at hs1.1)) (by rw [hs1.1]) hs1.2.1 hs1.2.2 rfl (by omega)
  | _ => exact h

/-- the pc after the code matters only for the outcome {lit}`normal` -/
theorem StmtPost.anyPc (h : StmtPost prog inp ρ ctx s n st pc rest (o, st')) (ho : o ≠ .normal) :
    StmtPost prog inp ρ ctx s n st pc' rest (o, st') := by
  cases o with
  | normal => exact absurd rfl ho
  | _ => exact h

/-- the outcome of an expression that halts or times out -/
theorem StmtPost.of_eval (h : EvalPost prog inp ρ s n st k pc' (v, st1))
    (hv : ∀ vs, v = .ok vs → False) :
    StmtPost prog inp ρ ctx s n st pc rest (v.outcome, st1) := by
  cases v with
  | ok vs => exact absurd rfl (hv vs)
  | halt r => exact h
  | timeout => exact h

/-- {lit}`break`, {lit}`continue` and {lit}`leave`: remove the variables above the first
{name}`d`, and jump -/
theorem st_jumpOut (hg : Good prog) (hA : At prog s.pc (jumpOut vars d l))
    (hL : At prog pl [.label l]) (hs : s.stack = vals V ++ rest) (hlen : vars.length = V.length) :
    ∃ s', Steps (layout prog) inp ρ s n (V.length - d + 2) s' n ∧
      Is s' (pos prog l) (vals (V.drop (V.length - d)) ++ rest) s.mem := by
  rw [jumpOut, hlen] at hA
  obtain ⟨s1, h1, hp1, hs1, hm1⟩ := st_pops (n := n) (ρ := ρ) (inp := inp) hA
    (l := (vals V).take (V.length - d)) (st := (vals V).drop (V.length - d) ++ rest)
    (by rw [hs, ← List.append_assoc, List.take_append_drop]) (by simp <;> omega)
  have hA1 : At prog s1.pc (.push l :: [.op .Jump]) := by
    rw [hp1]; have := hA.right (a := pops (V.length - d))
    simpa [pops, Item.size, EVM.Instr.encode, EVM.Instr.immediate] using this
  obtain ⟨s2, h2, hp2, hs2, hm2⟩ := st_pushLabel (n := n) (ρ := ρ) (inp := inp) hA1
  have hA2 : At prog s2.pc [.op .Jump] := by
    rw [hp2]; simpa [Item.size] using hA1.tail
  have hlt : pos prog l < 2 ^ 16 := pos_lt hg (a := []) (by simpa using hL)
  have hpl : pos prog l = pl := by simpa using pos_at hg (a := []) hL
  obtain ⟨s3, h3, hp3, hs3, hm3⟩ := st_jump (n := n) (ρ := ρ) (inp := inp) hA2 hs2
    (by rw [toNat_ofNat_pos hlt, hpl]; exact jumpdest_at hL)
  refine ⟨s3, by simpa [Nat.add_assoc] using (h1.trans h2).trans h3, ?_, ?_, ?_⟩
  · rw [hp3, toNat_ofNat_pos hlt]
  · simp [hs3, hs1, List.map_drop]
  · rw [hm3, hm2, hm1]

end Compiler
