import YulSemnaticsZoo.Compiler.Lemmas.SimExpr

set_option doc.verso true

/-!
# Compiler: the simulation of calls

The cases of {lit}`sim` for a call of a builtin and of a Yul function. {lit}`callee_builtin` and
{lit}`callee_fn` give the facts about the call that the compiler uses: the builtin of the
dialect, or the function in scope.
-/

namespace Compiler
open Semantics Yul Yul.Clocked

variable {prog : Code} {inp : Input} {ρ : Readings} {N : List String}

/-! ## The callee -/

theorem callee_builtin {h : (Expression.FunctionCall f args).WellFormed EVM.dialect N Γ n}
    {hI : Agrees N fs vars Γ} (hc : callee h hI = .builtin b es hw hl hn hs) :
    ∃ kinds mk, EVM.dialect.builtin f = some (kinds, mk) ∧ mk (literalArgs kinds args) = some b ∧
      es = exprArgs kinds args := by
  unfold callee at hc
  split at hc
  · next kinds mk hb =>
    split at hc
    · next b' hm => cases hc; exact ⟨kinds, mk, hb, hm, rfl⟩
    · next hm => exact (wf_builtin_none h hb hm).elim
  · next hb =>
    split at hc
    · cases hc
    · next hf => exact (wf_call_none h hb hI hf).elim

theorem callee_fn {h : (Expression.FunctionCall f args).WellFormed EVM.dialect N Γ n}
    {hI : Agrees N fs vars Γ} (hc : callee h hI = .fn fn fs' hw hl hn hfs hb) :
    EVM.dialect.builtin f = none ∧ Funs.find? f fs = some (fn, fs') := by
  unfold callee at hc
  split at hc
  · next kinds mk hb =>
    split at hc
    · cases hc
    · next hm => exact (wf_builtin_none h hb hm).elim
  · next hb =>
    split at hc
    · next hf => cases hc; exact ⟨hb, hf⟩
    · next hf => exact (wf_call_none h hb hI hf).elim

/-- the 8 builtins of the clocked semantics have no literal arguments -/
theorem kinds_of_op (hb : Yul.EVM.builtin f = some (kinds, mk)) (hm : mk ls = some b)
    (hop : builtinOp b = some i) : kinds = List.replicate kinds.length .Expression := by
  unfold Yul.EVM.builtin at hb
  split at hb <;> simp only [Yul.EVM.plain, Option.some.injEq, Prod.mk.injEq,
    Option.map_eq_some_iff] at hb
  all_goals first
    | (obtain ⟨rfl, rfl⟩ := hb; simp; done)
    | (obtain ⟨rfl, rfl⟩ := hb; simp only [Option.map_eq_some_iff] at hm
       obtain ⟨_, -, rfl⟩ := hm; simp [builtinOp] at hop)
    | (obtain ⟨⟨_, _⟩, -, hb⟩ := hb; simp only at hb; obtain ⟨rfl, rfl⟩ := hb
       simp only [Option.map_eq_some_iff] at hm; obtain ⟨_, -, rfl⟩ := hm
       simp [builtinOp] at hop)

theorem exprArgs_replicate (h : es.length = k) : exprArgs (List.replicate k .Expression) es = es := by
  induction es generalizing k with
  | nil => cases k <;> rfl
  | cons e es ih => cases k with
    | zero => simp at h
    | succ k => simp [List.replicate_succ, exprArgs, ih (by simpa using h)]

theorem builtinArgsWellFormed_length {d : Dialect} {Γ : Scope}
    (h : builtinArgsWellFormed d N Γ ks es) : es.length = ks.length := by
  induction es generalizing ks with
  | nil => rcases ks with _ | ⟨_ | _, _⟩ <;> simp_all [builtinArgsWellFormed]
  | cons e es ih =>
    rcases ks with _ | ⟨_ | _, ks⟩
    · simp [builtinArgsWellFormed] at h
    · simpa using ih h.2
    · simpa using ih h.2


/-! ## Builtins -/

theorem compileBuiltin (hb : Yul.EVM.dialect.builtin f = some (kinds, mk))
    (hc : compileExpr ctx q d (.FunctionCall f args) = .ok code) :
    ∃ (b : Yul.EVM.Builtin) (i : EVM.Instr) (ca : Code),
      mk (literalArgs kinds args) = some b ∧ builtinOp b = some i ∧
      compileArgs ctx q d args = .ok ca ∧ code = ca ++ [.op i] := by
  rw [compileExpr] at hc
  have hb' : Yul.EVM.builtin f = some (kinds, mk) := hb
  simp only [hb'] at hc
  split at hc
  · next i hop =>
    inv hc
    obtain ⟨ca, hca, rfl⟩ := hc
    obtain ⟨b, hmk, hop⟩ := Option.bind_eq_some_iff.mp hop
    exact ⟨b, i, ca, hmk, hop, hca, rfl⟩
  · inv hc

theorem size_op1 (h : i ∈ [EVM.Instr.Add, .Lt, .Eq, .Calldataload, .Mload, .Mstore, .Gas, .Return]) :
    size [Item.op i] = 1 := by
  simp at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- the code of a call of a builtin: the code of its arguments, then the instruction -/
theorem builtin_code {h : (Expression.FunctionCall f args).WellFormed EVM.dialect N Γ k}
    {hI : Agrees N fs vars Γ} (hcl : callee h hI = .builtin b es hw hl hn hs)
    (hc : compileExpr ctx q d (.FunctionCall f args) = .ok code) :
    ∃ i ca, builtinOp b = some i ∧ compileArgs ctx q d es = .ok ca ∧ code = ca ++ [.op i] := by
  obtain ⟨kinds, mk, hb, hmk, rfl⟩ := callee_builtin hcl
  obtain ⟨b', i, ca, hmk', hop, hca, rfl⟩ := compileBuiltin hb hc
  rw [hmk] at hmk'
  cases hmk'
  have hkinds := kinds_of_op hb hmk hop
  have hlen : args.length = kinds.length := by
    have h' := h
    rw [Expression.WellFormed, hb] at h'
    exact builtinArgsWellFormed_length h'.1
  have hex : exprArgs kinds args = args := by rw [hkinds]; exact exprArgs_replicate (by simp [hlen])
  exact ⟨i, ca, hop, by rw [hex]; exact hca, rfl⟩

theorem sim_builtin {h : (Expression.FunctionCall f args).WellFormed EVM.dialect N Γ k}
    {hI : Agrees N fs st.vars Γ} (hcl : callee h hI = .builtin b es hw hl hn hs)
    (he : evals inp ρ N fs st Γ es hw hI = ⟨.ok vs, st1, h1, p1⟩)
    (ih : M6 prog inp ρ N fs st Γ es hw hI) :
    M5 prog inp ρ N fs st Γ (.FunctionCall f args) k h hI := by
  intro ctx q d code hc p hA hF hN s0 n T rest hT hp hs hm hn'
  obtain ⟨i, ca, hop, hca, rfl⟩ := builtin_code hcl hc
  have r1 := ih ctx q d ca hca p hA.left hF hN s0 n T rest hT hp hs hm hn'
  rw [he] at r1
  obtain ⟨hl', hv, g⟩ := r1
  dsimp only at hv g
  have hr : eval inp ρ N fs st Γ (.FunctionCall f args) k h hI =
      (builtin inp ρ b vs (p1.count.trans hl) st1).up h1
        fun _ _ q => ⟨q.vars.trans p1.vars, hn ▸ q.count⟩ := by
    rw [eval]
    simp only [hcl]
    rw [he]
  rw [hr]
  have hA2 := hA.right
  have hargs : vs.length = Yul.EVM.ins b := p1.count.trans hl
  subst hn
  cases b <;> simp only [builtinOp, reduceCtorEq, Option.some.injEq] at hop <;> subst hop
  all_goals (rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨_, _⟩⟩⟩ <;> simp [Yul.EVM.ins] at hargs)
  · refine ⟨rfl, hv, g.bind fun s1 hs1 => Goes.done (st_add (hA2.at hs1.1) hs1.2.1) ?_ rfl
      hs1.2.2 rfl (by simp [builtin])⟩
    simp [hs1.1, Item.size, EVM.Instr.encode, EVM.Instr.immediate]; omega
  · refine ⟨rfl, hv, g.bind fun s1 hs1 => Goes.done (st_lt (hA2.at hs1.1) hs1.2.1) ?_ rfl
      hs1.2.2 rfl (by simp [builtin])⟩
    simp [hs1.1, Item.size, EVM.Instr.encode, EVM.Instr.immediate]; omega
  · refine ⟨rfl, hv, g.bind fun s1 hs1 => Goes.done (st_eq (hA2.at hs1.1) hs1.2.1) ?_ rfl
      hs1.2.2 rfl (by simp [builtin])⟩
    simp [hs1.1, Item.size, EVM.Instr.encode, EVM.Instr.immediate]; omega
  · refine ⟨rfl, hv, g.bind fun s1 hs1 => Goes.done (st_calldataload (hA2.at hs1.1) hs1.2.1) ?_
      rfl hs1.2.2 rfl (by simp [builtin])⟩
    simp [hs1.1, Item.size, EVM.Instr.encode, EVM.Instr.immediate]; omega
  · refine ⟨rfl, hv, g.bind fun s1 hs1 => Goes.done (st_mload (hA2.at hs1.1) hs1.2.1) ?_
      (by rw [hs1.2.2]; rfl) hs1.2.2 rfl (by simp [builtin])⟩
    simp [hs1.1, Item.size, EVM.Instr.encode, EVM.Instr.immediate]; omega
  · refine ⟨rfl, hv, g.bind fun s1 hs1 => Goes.done (st_mstore (hA2.at hs1.1) hs1.2.1) ?_
      rfl (by rw [hs1.2.2]; rfl) rfl (by simp [builtin])⟩
    simp [hs1.1, Item.size, EVM.Instr.encode, EVM.Instr.immediate]; omega
  · refine ⟨rfl, hv, g.bind fun s1 hs1 => Goes.done (st_gas (hA2.at hs1.1)) ?_
      (by rw [hs1.2.1]; rfl) hs1.2.2 rfl (by simp [builtin])⟩
    simp [hs1.1, Item.size, EVM.Instr.encode, EVM.Instr.immediate]; omega
  · exact g.halts fun s1 hs1 => by
      have := st_return (n := st1.reads) (ρ := ρ) (inp := inp) (hA2.at hs1.1) hs1.2.1
      rw [hs1.2.2] at this
      exact Halts.one this

/-! ## Calls of Yul functions -/

theorem compileCall (hb : Yul.EVM.dialect.builtin f = none)
    (hc : compileExpr ctx q d (.FunctionCall f args) = .ok code) :
    ∃ info scope ca, ctx.funs.find? f = some (info, scope) ∧
      compileArgs ctx q (d + 1 + info.rets) args = .ok ca ∧
      code = [.push (q, 0)] ++ List.replicate info.rets push0 ++ ca ++
        [.push info.label, .op .Jump, .label (q, 0)] := by
  rw [compileExpr] at hc
  have hb' : Yul.EVM.builtin f = none := hb
  simp only [hb'] at hc
  split at hc
  · next info scope hf =>
    inv hc
    obtain ⟨ca, hca, rfl⟩ := hc
    exact ⟨info, scope, ca, hf, hca, by simp⟩
  · inv hc

theorem funCode_ok (h : funCode q n m body = .ok c) :
    ∃ rc, rotate m = .ok rc ∧
      c = [.label (q, 0)] ++ body ++ [.label (q, 2)] ++ pops n ++ rc ++ [.op .Jump] := by
  unfold funCode at h
  inv h
  obtain ⟨rc, hr, rfl⟩ := h
  exact ⟨rc, hr, rfl⟩

/-- the return label and the zeros of the return variables -/
theorem call_prefix (hA : At prog p ([.push (q, 0)] ++ List.replicate m push0 ++ c))
    (hp : s0.pc = p) :
    ∃ s2, Steps (layout prog) inp ρ s0 n (1 + m) s2 n ∧
      Is s2 (p + 3 + m)
        (List.replicate m 0 ++ BitVec.ofNat 256 (pos prog (q, 0) % 2 ^ 16) :: s0.stack) s0.mem := by
  have hA1 : At prog s0.pc (.push (q, 0) :: (List.replicate m push0 ++ c)) := by
    rw [hp]; simpa using hA
  obtain ⟨s1, h1, hp1, hs1, hm1⟩ := st_pushLabel (n := n) (ρ := ρ) (inp := inp) hA1
  have hA2 : At prog s1.pc (List.replicate m push0 ++ c) := by
    rw [hp1]; have := hA1.tail; simpa [Item.size] using this
  obtain ⟨s2, h2, hp2, hs2, hm2⟩ := st_push0s (n := n) (ρ := ρ) (inp := inp) hA2
  refine ⟨s2, by simpa [Nat.add_comm] using h1.trans h2, ⟨?_, ?_, ?_⟩⟩
  · rw [hp2, hp1, hp]
  · rw [hs2, hs1]
  · rw [hm2, hm1]

/-- the facts about a function that the compiler finds -/
structure Callee (prog : Code) (sco : CFuns) (fn : Fun) (info : FunInfo) where
  q : List Nat
  cb : Code
  rc : Code
  pf : Nat
  label : info.label = (q, 0)
  params : info.params = fn.params.length
  rets : info.rets = fn.rets.length
  body : compileBlock (funCtx sco q fn.params fn.rets) (q ++ [0]) fn.body = .ok cb
  rot : rotate fn.rets.length = .ok rc
  hat : At prog pf ([.label (q, 0)] ++ cb ++ [.label (q, 2)] ++ pops fn.params.length ++ rc ++
    [.op .Jump])

theorem FunAt.callee (h : FunAt prog sco fn info) : Nonempty (Callee prog sco fn info) := by
  obtain ⟨hp, hr, q, hl, cb, c, hb, hc, pf, hA⟩ := h
  obtain ⟨rc, hrc, rfl⟩ := funCode_ok hc
  exact ⟨⟨q, cb, rc, pf, hl, hp, hr, hb, hrc, hA⟩⟩

/-- the jump into the function: {lit}`PUSH2 label`, {lit}`JUMP` and its {lit}`JUMPDEST` -/
theorem call_enter (hg : Good prog) (cl : Callee prog sco fn info)
    (hA : At prog s.pc ([.push info.label, .op .Jump] ++ c)) :
    ∃ s', Steps (layout prog) inp ρ s n 3 s' n ∧ Is s' (cl.pf + 1) s.stack s.mem := by
  have hpos : pos prog info.label = cl.pf := by
    rw [cl.label]; simpa using pos_at hg (a := []) cl.hat
  have hlt : pos prog info.label < 2 ^ 16 := by
    rw [cl.label]; exact pos_lt hg (a := []) (by simpa using cl.hat)
  obtain ⟨s1, h1, hp1, hs1, hm1⟩ := st_pushLabel (n := n) (ρ := ρ) (inp := inp)
    (by simpa using hA : At prog s.pc (.push info.label :: (.op .Jump :: c)))
  have hA1 : At prog s1.pc (.op .Jump :: c) := by
    rw [hp1]; have := (by simpa using hA : At prog s.pc (.push info.label :: (.op .Jump :: c))).tail
    simpa [Item.size] using this
  have hd : (BitVec.ofNat 256 (pos prog info.label % 2 ^ 16)).toNat ∈ EVM.jumpdests (layout prog) := by
    rw [toNat_ofNat_pos hlt, hpos]; exact jumpdest_at (by simpa using cl.hat)
  obtain ⟨s2, h2, hp2, hs2, hm2⟩ := st_jump (n := n) (ρ := ρ) (inp := inp) hA1 hs1 hd
  have hA2 : At prog s2.pc (.label (cl.q, 0) :: (cl.cb ++ [.label (cl.q, 2)] ++
      pops fn.params.length ++ cl.rc ++ [.op .Jump])) := by
    rw [hp2, toNat_ofNat_pos hlt, hpos]; simpa using cl.hat
  obtain ⟨s3, h3, hp3, hs3, hm3⟩ := st_label (n := n) (ρ := ρ) (inp := inp) hA2
  refine ⟨s3, (h1.trans h2).trans h3, ?_, ?_, ?_⟩
  · rw [hp3, hp2, toNat_ofNat_pos hlt, hpos]
  · rw [hs3, hs2]
  · rw [hm3, hm2, hm1]

theorem Callee.pos_exit (hg : Good prog) (cl : Callee prog sco fn info) :
    pos prog (cl.q, 2) = cl.pf + 1 + size cl.cb := by
  have := pos_at hg (a := [.label (cl.q, 0)] ++ cl.cb)
    (b := pops fn.params.length ++ cl.rc ++ [.op .Jump]) (by simpa using cl.hat)
  simpa [Item.size, Nat.add_assoc] using this

theorem Callee.at_body (cl : Callee prog sco fn info) : At prog (cl.pf + 1) cl.cb := by
  have := (At.left (a := [.label (cl.q, 0)] ++ cl.cb) (by simpa using cl.hat)).right
  simpa [Item.size, Nat.add_assoc] using this

theorem Callee.at_exit (cl : Callee prog sco fn info) :
    At prog (cl.pf + 1 + size cl.cb)
      ([.label (cl.q, 2)] ++ (pops fn.params.length ++ cl.rc ++ [.op .Jump])) := by
  have := (At.right (a := [.label (cl.q, 0)] ++ cl.cb) (by simpa using cl.hat))
  simpa [Item.size, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this

/-- the end of the function: its {lit}`JUMPDEST`, {lit}`POP` for each parameter, the return
label above the return values, the jump back, and the {lit}`JUMPDEST` there -/
theorem call_exit (hg : Good prog) (cl : Callee prog sco fn info) (hAr : At prog pr [.label (q, 0)])
    (hp : s.pc = pos prog (cl.q, 2))
    (hs : s.stack = l ++ BitVec.ofNat 256 (pos prog (q, 0) % 2 ^ 16) :: S)
    (hl : l.length = fn.params.length + fn.rets.length) :
    ∃ s', Steps (layout prog) inp ρ s n (1 + fn.params.length + fn.rets.length + 1 + 1) s' n ∧
      Is s' (pr + 1) (l.drop fn.params.length ++ S) s.mem := by
  have hA : At prog (cl.pf + 1 + size cl.cb)
      ([.label (cl.q, 2)] ++ pops fn.params.length ++ cl.rc ++ [.op .Jump]) := by
    have := (At.right (a := [.label (cl.q, 0)] ++ cl.cb) (by simpa using cl.hat))
    simpa [Item.size, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  rw [cl.pos_exit hg] at hp
  obtain ⟨s1, h1, hp1, hs1, hm1⟩ := st_label (n := n) (ρ := ρ) (inp := inp)
    (by rw [hp]; simpa using hA : At prog s.pc (.label (cl.q, 2) :: _))
  have hA1 : At prog s1.pc (pops fn.params.length ++ (cl.rc ++ [.op .Jump])) := by
    rw [hp1, hp]; have := hA.right (a := [.label (cl.q, 2)]); simpa [Item.size] using this
  obtain ⟨s2, h2, hp2, hs2, hm2⟩ := st_pops (n := n) (ρ := ρ) (inp := inp) hA1
    (l := l.take fn.params.length) (st := l.drop fn.params.length ++ _ :: S)
    (by rw [hs1, hs, ← List.append_assoc, List.take_append_drop]) (by simp [hl])
  have hA2 : At prog s2.pc (cl.rc ++ [.op .Jump]) := by
    rw [hp2]; have := hA1.right (a := pops fn.params.length)
    simpa [pops, Item.size, EVM.Instr.encode, EVM.Instr.immediate] using this
  obtain ⟨s3, h3, hp3, hs3, hm3⟩ := st_rotate (n := n) (ρ := ρ) (inp := inp) cl.rot hA2 hs2
    (by simp [hl])
  have hlt : pos prog (q, 0) < 2 ^ 16 := pos_lt hg (a := []) (by simpa using hAr)
  have hpr : pos prog (q, 0) = pr := by simpa using pos_at hg (a := []) hAr
  have hA3 : At prog s3.pc [.op .Jump] := by
    rw [hp3, ← rotate_size cl.rot]; have := hA2.right (a := cl.rc)
    simpa [Item.size, EVM.Instr.encode, EVM.Instr.immediate, Nat.add_assoc] using this
  obtain ⟨s4, h4, hp4, hs4, hm4⟩ := st_jump (n := n) (ρ := ρ) (inp := inp) hA3 hs3
    (by rw [toNat_ofNat_pos hlt, hpr]; exact jumpdest_at hAr)
  obtain ⟨s5, h5, hp5, hs5, hm5⟩ := st_label (n := n) (ρ := ρ) (inp := inp)
    (by rw [hp4, toNat_ofNat_pos hlt, hpr]; exact hAr : At prog s4.pc [.label (q, 0)])
  refine ⟨s5, (((h1.trans h2).trans h3).trans h4).trans h5, ?_, ?_, ?_⟩
  · rw [hp5, hp4, toNat_ofNat_pos hlt, hpr]
  · rw [hs5, hs4]; rfl
  · rw [hm5, hm4, hm3, hm2, hm1]

theorem length_bind {h : vs.length = xs.length} : (Clocked.bind xs vs h).length = xs.length := by
  have := congrArg List.length (names_bind (xs := xs) (vs := vs) (h := h)); rwa [List.length_map] at this

/-- a call of a Yul function after its arguments, for each outcome of its body -/
theorem sim_call {h : (Expression.FunctionCall f args).WellFormed EVM.dialect N Γ k}
    {hI : Agrees N fs st.vars Γ} (hg : Good prog) (hcl : callee h hI = .fn fn fs' hw hl hn hfs hbody)
    (he : evals inp ρ N fs st Γ args hw hI = ⟨.ok vs, st1, h1, p1⟩) (h0 : ¬st1.clock = 0)
    (hbe : execBlock inp ρ N fs'
      { st1 with
        vars := Clocked.bind fn.params vs hp ++
          Clocked.bind fn.rets (List.replicate fn.rets.length 0) hz
        clock := st1.clock - 1 } (fn.scope fs') fn.body hbody hIb = ⟨o, st2, h2, pb⟩)
    (ih : M6 prog inp ρ N fs st Γ args hw hI)
    (ihb : M3 prog inp ρ N fs'
      { st1 with
        vars := Clocked.bind fn.params vs hp ++
          Clocked.bind fn.rets (List.replicate fn.rets.length 0) hz
        clock := st1.clock - 1 } (fn.scope fs') fn.body hbody hIb) :
    M5 prog inp ρ N fs st Γ (.FunctionCall f args) k h hI := by
  intro ctx q d code hc p hA hF hN s0 n T rest hT hp' hs hm hn'
  obtain ⟨hb, hf⟩ := callee_fn hcl
  obtain ⟨info, sco, ca, hfc, hca, rfl⟩ := compileCall hb hc
  obtain ⟨fn', fs'', hf', hfa, hFs⟩ := hF.find hfc
  rw [hf] at hf'
  cases hf'
  obtain ⟨cl⟩ := hfa.callee
  -- the return label and the zeros, then the arguments
  obtain ⟨s2, h02, hp2, hs2, hm2⟩ := call_prefix (n := n) (ρ := ρ) (inp := inp) (m := info.rets)
    (c := ca ++ [.push info.label, .op .Jump, .label (q, 0)]) (by simpa using hA) hp'
  have hAa : At prog (p + 3 + info.rets) ca := by
    have := (At.left (a := [Item.push (q, 0)] ++ List.replicate info.rets push0 ++ ca)
      (by simpa using hA)).right
    simpa [Item.size, push0, pushNat_encode_length, Nat.add_assoc] using this
  have r1 := ih ctx q (d + 1 + info.rets) ca hca (p + 3 + info.rets) hAa hF hN s2 n
    (List.replicate info.rets 0 ++ BitVec.ofNat 256 (pos prog (q, 0) % 2 ^ 16) :: T) rest
    (by simp [hT]; omega) hp2 (by rw [hs2, hs]; simp) (hm2.trans hm) hn'
  rw [he] at r1
  obtain ⟨hlv, hv, g⟩ := r1
  dsimp only at hv g
  have hAc : At prog (p + 3 + info.rets + size ca)
      ([.push info.label, .op .Jump] ++ [.label (q, 0)]) := by
    have := (At.right (a := [Item.push (q, 0)] ++ List.replicate info.rets push0 ++ ca)
      (by simpa using hA))
    simpa [Item.size, push0, pushNat_encode_length, Nat.add_assoc] using this
  have hAr : At prog (p + 3 + info.rets + size ca + 4) [.label (q, 0)] := by
    have := hAc.right (a := [.push info.label, .op .Jump])
    simpa [Item.size, EVM.Instr.encode, EVM.Instr.immediate, Nat.add_assoc] using this
  rw [eval]
  simp only [hcl]
  rw [he]
  dsimp only
  simp only [h0, dite_false]
  rw [hbe]
  dsimp only
  -- the body
  have r2 := fun s4 (hs4 : Is s4 (cl.pf + 1) (vs ++ s2.stack) st1.mem) =>
    ihb (funCtx sco cl.q fn.params fn.rets) (cl.q ++ [0]) cl.cb cl.body (cl.pf + 1) cl.at_body
      s4 st1.reads (BitVec.ofNat 256 (pos prog (q, 0) % 2 ^ 16) :: s0.stack) hs4.1
      { funs := hFs
        names := by simp [funCtx]
        loop := by simp [funCtx]
        leave := by
          intro l d h; simp [funCtx] at h; obtain ⟨rfl, rfl⟩ := h
          exact ⟨by simp [length_bind], _, cl.at_exit.left⟩
        stack := by rw [hs4.2.1, hs2, vals_append, vals_bind, vals_bind, cl.rets]; simp
        mem := hs4.2.2
        reads := rfl }
  rw [hbe] at r2
  dsimp only at r2
  have hnm : names st2.vars = fn.params ++ fn.rets := pb.vars
  have enter := fun s3 (hs3 : Is s3 (p + 3 + info.rets + size ca) (vs ++ s2.stack) st1.mem) =>
    call_enter (n := st1.reads) (ρ := ρ) (inp := inp) hg cl (hAc.at hs3.1)
  -- the end of the function, for `normal` and `leave`
  have fin : ∀ s5, Is s5 (pos prog (cl.q, 2))
      (vals st2.vars ++ BitVec.ofNat 256 (pos prog (q, 0) % 2 ^ 16) :: s0.stack) st2.mem →
      Goes prog inp ρ s5 st2.reads st2.clock ⟨st1.vars, st2.mem, st2.reads, st2.clock⟩
        (p + size ([.push (q, 0)] ++ List.replicate info.rets push0 ++ ca ++
          [.push info.label, .op .Jump, .label (q, 0)]))
        ((st2.vars.drop fn.params.length).map Prod.snd ++ s0.stack) := fun s5 hs5 => by
    have hlen : (vals st2.vars).length = fn.params.length + fn.rets.length := by
      have := congrArg List.length hnm; simpa using this
    refine Goes.done (call_exit hg cl hAr hs5.1 hs5.2.1 hlen) ?_ ?_ hs5.2.2 rfl (by dsimp only; omega)
    · simp [Item.size, push0, pushNat, toBytes, EVM.Instr.encode, EVM.Instr.immediate]
      omega
    · simp [List.map_drop]
  have hcount : ((st2.vars.drop fn.params.length).map Prod.snd).length = k :=
    (rets_count hnm).trans hn.symm
  cases o with
  | halt r =>
    exact Halts.pre h02 (g.halts fun s3 hs3 => Halts.thenS (enter s3 hs3) fun s4 hs4 =>
      r2 s4 ⟨hs4.1, hs4.2.1.trans hs3.2.1, hs4.2.2.trans hs3.2.2⟩)
  | timeout =>
    exact Survives.pre h02 (g.survives fun s3 hs3 => Survives.thenS (enter s3 hs3)
      (fun s4 hs4 => r2 s4 ⟨hs4.1, hs4.2.1.trans hs3.2.1, hs4.2.2.trans hs3.2.2⟩)
      (by dsimp only; omega)) (by omega)
  | brk => exact absurd pb.fits (by simp [Outcome.Fits, Fun.scope])
  | cont => exact absurd pb.fits (by simp [Outcome.Fits, Fun.scope])
  | normal =>
    refine ⟨hcount, hv, Goes.pre h02 (g.bind fun s3 hs3 => ?_)⟩
    obtain ⟨s4, h34, hs4⟩ := enter s3 hs3
    exact Goes.preC h34 ((r2 s4 ⟨hs4.1, hs4.2.1.trans hs3.2.1, hs4.2.2.trans hs3.2.2⟩).bind
      fun s5 hs5 => fin s5 ⟨hs5.1.trans (cl.pos_exit hg).symm, hs5.2.1, hs5.2.2⟩)
      (by dsimp only; omega)
  | leave =>
    refine ⟨hcount, hv, Goes.pre h02 (g.bind fun s3 hs3 => ?_)⟩
    obtain ⟨s4, h34, hs4⟩ := enter s3 hs3
    obtain ⟨l, d', hld, g2⟩ := r2 s4 ⟨hs4.1, hs4.2.1.trans hs3.2.1, hs4.2.2.trans hs3.2.2⟩
    simp only [funCtx, Option.some.injEq, Prod.mk.injEq] at hld
    obtain ⟨rfl, rfl⟩ := hld
    have hlen : st2.vars.length = fn.params.length + fn.rets.length := by
      have := congrArg List.length hnm; simpa using this
    rw [hlen, Nat.sub_self, List.drop_zero] at g2
    exact Goes.preC h34 (g2.bind fun s5 hs5 => fin s5 hs5) (by dsimp only; omega)

/-- the clock is 0 at the call -/
theorem sim_call_zero {h : (Expression.FunctionCall f args).WellFormed EVM.dialect N Γ k}
    {hI : Agrees N fs st.vars Γ} (hcl : callee h hI = .fn fn fs' hw hl hn hfs hbody)
    (he : evals inp ρ N fs st Γ args hw hI = ⟨.ok vs, st1, h1, p1⟩) (h0 : st1.clock = 0)
    (ih : M6 prog inp ρ N fs st Γ args hw hI) :
    M5 prog inp ρ N fs st Γ (.FunctionCall f args) k h hI := by
  intro ctx q d code hc p hA hF hN s0 n T rest hT hp' hs hm hn'
  obtain ⟨hb, hf⟩ := callee_fn hcl
  obtain ⟨info, sco, ca, hfc, hca, rfl⟩ := compileCall hb hc
  obtain ⟨s2, h02, hp2, hs2, hm2⟩ := call_prefix (n := n) (ρ := ρ) (inp := inp) (m := info.rets)
    (c := ca ++ [.push info.label, .op .Jump, .label (q, 0)]) (by simpa using hA) hp'
  have hAa : At prog (p + 3 + info.rets) ca := by
    have := (At.left (a := [Item.push (q, 0)] ++ List.replicate info.rets push0 ++ ca)
      (by simpa using hA)).right
    simpa [Item.size, push0, pushNat_encode_length, Nat.add_assoc] using this
  have r1 := ih ctx q (d + 1 + info.rets) ca hca (p + 3 + info.rets) hAa hF hN s2 n
    (List.replicate info.rets 0 ++ BitVec.ofNat 256 (pos prog (q, 0) % 2 ^ 16) :: T) rest
    (by simp [hT]; omega) hp2 (by rw [hs2, hs]; simp) (hm2.trans hm) hn'
  rw [he] at r1
  obtain ⟨-, -, g⟩ := r1
  rw [eval]
  simp only [hcl]
  rw [he]
  dsimp only
  simp only [h0, dite_true]
  exact Survives.pre h02 (g.survives fun _ _ => by rw [h0]; exact Survives.zero) (by omega)

/-- the arguments of a call of a builtin halt or time out -/
theorem sim_builtin_args {h : (Expression.FunctionCall f args).WellFormed EVM.dialect N Γ k}
    {hI : Agrees N fs st.vars Γ} (hcl : callee h hI = .builtin b es hw hl hn hs)
    (he : evals inp ρ N fs st Γ es hw hI = ⟨v, st1, h1, p1⟩)
    (hv : ∀ vs, v = .ok vs → False) (ih : M6 prog inp ρ N fs st Γ es hw hI) :
    M5 prog inp ρ N fs st Γ (.FunctionCall f args) k h hI := by
  intro ctx q d code hc p hA hF hN s0 n T rest hT hp hs hm hn'
  obtain ⟨i, ca, -, hca, rfl⟩ := builtin_code hcl hc
  have r1 := ih ctx q d ca hca p hA.left hF hN s0 n T rest hT hp hs hm hn'
  rw [he] at r1
  rw [eval]
  simp only [hcl]
  rw [he]
  cases v with
  | ok vs => exact absurd rfl (hv vs)
  | halt r => exact r1
  | timeout => exact r1

/-- the arguments of a call of a Yul function halt or time out -/
theorem sim_call_args {h : (Expression.FunctionCall f args).WellFormed EVM.dialect N Γ k}
    {hI : Agrees N fs st.vars Γ} (hcl : callee h hI = .fn fn fs' hw hl hn hfs hbody)
    (he : evals inp ρ N fs st Γ args hw hI = ⟨v, st1, h1, p1⟩)
    (hv : ∀ vs, v = .ok vs → False) (ih : M6 prog inp ρ N fs st Γ args hw hI) :
    M5 prog inp ρ N fs st Γ (.FunctionCall f args) k h hI := by
  intro ctx q d code hc p hA hF hN s0 n T rest hT hp' hs hm hn'
  obtain ⟨hb, -⟩ := callee_fn hcl
  obtain ⟨info, sco, ca, hfc, hca, rfl⟩ := compileCall hb hc
  obtain ⟨s2, h02, hp2, hs2, hm2⟩ := call_prefix (n := n) (ρ := ρ) (inp := inp) (m := info.rets)
    (c := ca ++ [.push info.label, .op .Jump, .label (q, 0)]) (by simpa using hA) hp'
  have hAa : At prog (p + 3 + info.rets) ca := by
    have := (At.left (a := [Item.push (q, 0)] ++ List.replicate info.rets push0 ++ ca)
      (by simpa using hA)).right
    simpa [Item.size, push0, pushNat_encode_length, Nat.add_assoc] using this
  have r1 := ih ctx q (d + 1 + info.rets) ca hca (p + 3 + info.rets) hAa hF hN s2 n
    (List.replicate info.rets 0 ++ BitVec.ofNat 256 (pos prog (q, 0) % 2 ^ 16) :: T) rest
    (by simp [hT]; omega) hp2 (by rw [hs2, hs]; simp) (hm2.trans hm) hn'
  rw [he] at r1
  rw [eval]
  simp only [hcl]
  rw [he]
  cases v with
  | ok vs => exact absurd rfl (hv vs)
  | halt r => exact Halts.pre h02 r1
  | timeout => exact Survives.pre h02 r1 (by omega)

end Compiler
