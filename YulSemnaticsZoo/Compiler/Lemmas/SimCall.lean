import YulSemnaticsZoo.Compiler.Lemmas.SimExpr

set_option doc.verso true

/-!
# Compiler: the simulation of calls

The cases of {lit}`sim` for a call of a builtin and of a Yul function.
-/

namespace Compiler
open Semantics Yul Yul.Clocked

variable {prog : Code} {inp : Input} {ρ : Readings}

/-! ## Builtins -/

theorem compileBuiltin (hb : Yul.EVM.dialect.builtin f = some (kinds, mk))
    (hc : compileExpr ctx q d (.FunctionCall f args) k = .ok code) :
    ∃ (b : Yul.EVM.Builtin) (i : EVM.Instr) (nargs outs : Nat) (ca : Code),
      mk (literalArgs kinds args) = some b ∧ builtinOp b = some (i, nargs, outs) ∧
      args.length = nargs ∧ k = outs ∧ compileArgs ctx q d args = .ok ca ∧
      code = ca ++ [.op i] := by
  rw [compileExpr] at hc
  have hb' : Yul.EVM.builtin f = some (kinds, mk) := hb
  simp only [hb'] at hc
  split at hc
  · next b hmk =>
    split at hc
    · next i nargs outs hop =>
      inv hc
      obtain ⟨⟨h1, rfl⟩, ca, hca, rfl⟩ := hc
      exact ⟨b, i, nargs, _, ca, hmk, hop, h1, rfl, hca, rfl⟩
    · inv hc
  · inv hc

theorem size_op1 (h : i ∈ [EVM.Instr.Add, .Lt, .Eq, .Calldataload, .Mload, .Mstore, .Gas, .Return]) :
    size [Item.op i] = 1 := by
  simp at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem sim_builtin (hb : Yul.EVM.dialect.builtin f = some (kinds, mk))
    (he : evals inp ρ fs st args = ⟨.ok vs, st1, h1⟩) (ih : M6 prog inp ρ fs st args) :
    M5 prog inp ρ fs st (.FunctionCall f args) := by
  intro ctx q d k code hc p hA hF hN s0 n T rest hT hp hs hm hn
  obtain ⟨b, i, nargs, outs, ca, hmk, hop, hargs, rfl, hca, rfl⟩ := compileBuiltin hb hc
  have r1 := ih ctx q d ca hca p hA.left hF hN s0 n T rest hT hp hs hm hn
  rw [he] at r1
  obtain ⟨hl, hv, g⟩ := r1
  dsimp only at hv g
  have hr : eval inp ρ fs st (.FunctionCall f args) = (builtin inp ρ (some b) vs st1).up h1 := by
    rw [eval, he]
    have hb' : Yul.EVM.builtin f = some (kinds, mk) := hb
    simp only [hb', hmk]
  rw [hr]
  have hA2 := hA.right
  rw [← hl] at hargs
  cases b <;> simp only [builtinOp, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hop <;>
    obtain ⟨rfl, rfl, rfl⟩ := hop
  all_goals (rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨_, _⟩⟩⟩ <;> simp at hargs)
  · refine ⟨rfl, hv, g.bind fun s1 hs1 => Goes.done (st_add (hA2.at hs1.1) hs1.2.1) ?_ rfl
      hs1.2.2 rfl (by simp [Res.up, builtin])⟩
    simp [hs1.1, Item.size, EVM.Instr.encode, EVM.Instr.immediate]; omega
  · refine ⟨rfl, hv, g.bind fun s1 hs1 => Goes.done (st_lt (hA2.at hs1.1) hs1.2.1) ?_ rfl
      hs1.2.2 rfl (by simp [Res.up, builtin])⟩
    simp [hs1.1, Item.size, EVM.Instr.encode, EVM.Instr.immediate]; omega
  · refine ⟨rfl, hv, g.bind fun s1 hs1 => Goes.done (st_eq (hA2.at hs1.1) hs1.2.1) ?_ rfl
      hs1.2.2 rfl (by simp [Res.up, builtin])⟩
    simp [hs1.1, Item.size, EVM.Instr.encode, EVM.Instr.immediate]; omega
  · refine ⟨rfl, hv, g.bind fun s1 hs1 => Goes.done (st_calldataload (hA2.at hs1.1) hs1.2.1) ?_
      rfl hs1.2.2 rfl (by simp [Res.up, builtin])⟩
    simp [hs1.1, Item.size, EVM.Instr.encode, EVM.Instr.immediate]; omega
  · refine ⟨rfl, hv, g.bind fun s1 hs1 => Goes.done (st_mload (hA2.at hs1.1) hs1.2.1) ?_
      (by rw [hs1.2.2]; rfl) hs1.2.2 rfl (by simp [Res.up, builtin])⟩
    simp [hs1.1, Item.size, EVM.Instr.encode, EVM.Instr.immediate]; omega
  · refine ⟨rfl, hv, g.bind fun s1 hs1 => Goes.done (st_mstore (hA2.at hs1.1) hs1.2.1) ?_
      rfl (by rw [hs1.2.2]; rfl) rfl (by simp [Res.up, builtin])⟩
    simp [hs1.1, Item.size, EVM.Instr.encode, EVM.Instr.immediate]; omega
  · refine ⟨rfl, hv, g.bind fun s1 hs1 => Goes.done (st_gas (hA2.at hs1.1)) ?_
      (by rw [hs1.2.1]; rfl) hs1.2.2 rfl (by simp [Res.up, builtin])⟩
    simp [hs1.1, Item.size, EVM.Instr.encode, EVM.Instr.immediate]; omega
  · exact g.halts fun s1 hs1 => by
      have := st_return (n := st1.reads) (ρ := ρ) (inp := inp) (hA2.at hs1.1) hs1.2.1
      rw [hs1.2.2] at this
      exact Halts.one this

/-! ## Calls of Yul functions -/

theorem compileCall (hb : Yul.EVM.dialect.builtin f = none)
    (hc : compileExpr ctx q d (.FunctionCall f args) k = .ok code) :
    ∃ info scope ca, ctx.funs.find? f = some (info, scope) ∧ args.length = info.params ∧
      k = info.rets ∧ compileArgs ctx q (d + 1 + info.rets) args = .ok ca ∧
      code = [.push (q, 0)] ++ List.replicate info.rets push0 ++ ca ++
        [.push info.label, .op .Jump, .label (q, 0)] := by
  rw [compileExpr] at hc
  have hb' : Yul.EVM.builtin f = none := hb
  simp only [hb'] at hc
  split at hc
  · next info scope hf =>
    inv hc
    obtain ⟨⟨h1, rfl⟩, ca, hca, rfl⟩ := hc
    exact ⟨info, scope, ca, hf, h1, rfl, hca, by simp⟩
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
  nodup : (fn.params ++ fn.rets).Nodup
  body : compileBlock (funCtx sco q fn.params fn.rets) (q ++ [0]) fn.body = .ok cb
  rot : rotate fn.rets.length = .ok rc
  hat : At prog pf ([.label (q, 0)] ++ cb ++ [.label (q, 2)] ++ pops fn.params.length ++ rc ++
    [.op .Jump])

theorem FunAt.callee (h : FunAt prog sco fn info) : Nonempty (Callee prog sco fn info) := by
  obtain ⟨hp, hr, q, hl, hn, cb, c, hb, hc, pf, hA⟩ := h
  obtain ⟨rc, hrc, rfl⟩ := funCode_ok hc
  exact ⟨⟨q, cb, rc, pf, hl, hp, hr, hn, hb, hrc, hA⟩⟩

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

theorem length_bind : (Clocked.bind xs vs).length = xs.length := by simp [Clocked.bind]

/-- a call of a Yul function after its arguments: the cases of the clock, and of the outcome of
the body -/
theorem sim_call (hg : Good prog) (hb : Yul.EVM.dialect.builtin f = none)
    (hf : Funs.find? f fs = some (fn, fs'))
    (he : evals inp ρ fs st args = ⟨.ok vs, st1, h1⟩) (ih : M6 prog inp ρ fs st args)
    (ihb : st1.clock ≠ 0 → M3 prog inp ρ fs'
      ⟨Clocked.bind fn.params vs ++ Clocked.bind fn.rets [], st1.mem, st1.reads, st1.clock - 1⟩
      fn.body) :
    M5 prog inp ρ fs st (.FunctionCall f args) := by
  intro ctx q d k code hc p hA hF hN s0 n T rest hT hp hs hm hn
  obtain ⟨info, sco, ca, hfc, hpar, rfl, hca, rfl⟩ := compileCall hb hc
  obtain ⟨fn', fs'', hf', hfa, hFs⟩ := hF.find hfc
  rw [hf] at hf'
  cases hf'
  obtain ⟨cl⟩ := hfa.callee
  have hb' : Yul.EVM.builtin f = none := hb
  -- the return label and the zeros, then the arguments
  obtain ⟨s2, h02, hp2, hs2, hm2⟩ := call_prefix (n := n) (ρ := ρ) (inp := inp) (m := info.rets)
    (c := ca ++ [.push info.label, .op .Jump, .label (q, 0)]) (by simpa using hA) hp
  have hAa : At prog (p + 3 + info.rets) ca := by
    have := (At.left (a := [Item.push (q, 0)] ++ List.replicate info.rets push0 ++ ca)
      (by simpa using hA)).right
    simpa [Item.size, push0, pushNat_encode_length, Nat.add_assoc] using this
  have r1 := ih ctx q (d + 1 + info.rets) ca hca (p + 3 + info.rets) hAa hF hN s2 n
    (List.replicate info.rets 0 ++ BitVec.ofNat 256 (pos prog (q, 0) % 2 ^ 16) :: T) rest
    (by simp [hT]; omega) hp2 (by rw [hs2, hs]; simp) (hm2.trans hm) hn
  rw [he] at r1
  obtain ⟨hl, hv, g⟩ := r1
  dsimp only at hv g
  have hAc : At prog (p + 3 + info.rets + size ca)
      ([.push info.label, .op .Jump] ++ [.label (q, 0)]) := by
    have := (At.right (a := [Item.push (q, 0)] ++ List.replicate info.rets push0 ++ ca)
      (by simpa using hA))
    simpa [Item.size, push0, pushNat_encode_length, Nat.add_assoc] using this
  have hAr : At prog (p + 3 + info.rets + size ca + 4) [.label (q, 0)] := by
    have := hAc.right (a := [.push info.label, .op .Jump])
    simpa [Item.size, EVM.Instr.encode, EVM.Instr.immediate, Nat.add_assoc] using this
  rw [eval, he]
  simp only [hb', hf]
  by_cases h0 : st1.clock = 0
  · simp only [h0, dite_true]
    exact Survives.pre h02 (g.survives fun _ _ => by rw [h0]; exact Survives.zero) (by omega)
  simp only [h0, dite_false]
  -- the body
  have r2 := fun s4 (hs4 : Is s4 (cl.pf + 1) (vs ++ s2.stack) st1.mem) =>
    ihb h0 (funCtx sco cl.q fn.params fn.rets) (cl.q ++ [0]) cl.cb cl.body (cl.pf + 1) cl.at_body
      s4 st1.reads (BitVec.ofNat 256 (pos prog (q, 0) % 2 ^ 16) :: s0.stack) hs4.1
      { funs := hFs
        names := by simp [funCtx]
        loop := by simp [funCtx]
        leave := by
          intro l d h; simp [funCtx] at h; obtain ⟨rfl, rfl⟩ := h
          exact ⟨by simp [length_bind], _, cl.at_exit.left⟩
        stack := by
          rw [hs4.2.1, hs2, vals_append, vals_bind (by rw [hl, hpar, cl.params]), vals_bind_nil,
            cl.rets]; simp
        mem := hs4.2.2
        reads := rfl }
  have hnm := (names_mono inp ρ).2.2.1 fs'
    ⟨Clocked.bind fn.params vs ++ Clocked.bind fn.rets [], st1.mem, st1.reads, st1.clock - 1⟩ fn.body
  generalize execBlock inp ρ fs'
    ⟨Clocked.bind fn.params vs ++ Clocked.bind fn.rets [], st1.mem, st1.reads, st1.clock - 1⟩
    fn.body = Rb at r2 hnm ⊢
  obtain ⟨o, st2, h2⟩ := Rb
  dsimp only at r2 hnm ⊢
  simp only [names_append, names_bind] at hnm
  have enter := fun s3 (hs3 : Is s3 (p + 3 + info.rets + size ca) (vs ++ s2.stack) st1.mem) =>
    call_enter (n := st1.reads) (ρ := ρ) (inp := inp) hg cl (hAc.at hs3.1)
  -- the end of the function, for `normal` and `leave`
  have fin : ∀ s5, Is s5 (pos prog (cl.q, 2))
      (vals st2.vars ++ BitVec.ofNat 256 (pos prog (q, 0) % 2 ^ 16) :: s0.stack) st2.mem →
      Goes prog inp ρ s5 st2.reads st2.clock ⟨st1.vars, st2.mem, st2.reads, st2.clock⟩
        (p + size ([.push (q, 0)] ++ List.replicate info.rets push0 ++ ca ++
          [.push info.label, .op .Jump, .label (q, 0)]))
        (fn.rets.map (Vars.get st2.vars) ++ s0.stack) := fun s5 hs5 => by
    have hlen : (vals st2.vars).length = fn.params.length + fn.rets.length := by
      have := congrArg List.length hnm; simpa using this
    refine Goes.done (call_exit hg cl hAr hs5.1 hs5.2.1 hlen) ?_ ?_ hs5.2.2 rfl (by dsimp only; omega)
    · simp [Item.size, push0, pushNat, toBytes, EVM.Instr.encode, EVM.Instr.immediate]
      omega
    · rw [rets_get hnm cl.nodup]
  cases o with
  | halt r =>
    exact Halts.pre h02 (g.halts fun s3 hs3 => Halts.thenS (enter s3 hs3) fun s4 hs4 =>
      r2 s4 ⟨hs4.1, hs4.2.1.trans hs3.2.1, hs4.2.2.trans hs3.2.2⟩)
  | timeout =>
    exact Survives.pre h02 (g.survives fun s3 hs3 => Survives.thenS (enter s3 hs3)
      (fun s4 hs4 => r2 s4 ⟨hs4.1, hs4.2.1.trans hs3.2.1, hs4.2.2.trans hs3.2.2⟩)
      (by dsimp only; omega)) (by omega)
  | brk =>
    obtain ⟨l, lc, d, h, -⟩ := r2 ⟨cl.pf + 1, vs ++ s2.stack, st1.mem, 0⟩ ⟨rfl, rfl, rfl⟩
    simp [funCtx] at h
  | cont =>
    obtain ⟨l, lc, d, h, -⟩ := r2 ⟨cl.pf + 1, vs ++ s2.stack, st1.mem, 0⟩ ⟨rfl, rfl, rfl⟩
    simp [funCtx] at h
  | normal =>
    refine ⟨by simp [cl.rets], hv, Goes.pre h02 (g.bind fun s3 hs3 => ?_)⟩
    obtain ⟨s4, h34, hs4⟩ := enter s3 hs3
    exact Goes.preC h34 ((r2 s4 ⟨hs4.1, hs4.2.1.trans hs3.2.1, hs4.2.2.trans hs3.2.2⟩).bind
      fun s5 hs5 => fin s5 ⟨hs5.1.trans (cl.pos_exit hg).symm, hs5.2.1, hs5.2.2⟩)
      (by dsimp only; omega)
  | leave =>
    refine ⟨by simp [cl.rets], hv, Goes.pre h02 (g.bind fun s3 hs3 => ?_)⟩
    obtain ⟨s4, h34, hs4⟩ := enter s3 hs3
    obtain ⟨l, d', hld, g2⟩ := r2 s4 ⟨hs4.1, hs4.2.1.trans hs3.2.1, hs4.2.2.trans hs3.2.2⟩
    simp only [funCtx, Option.some.injEq, Prod.mk.injEq] at hld
    obtain ⟨rfl, rfl⟩ := hld
    have hlen : st2.vars.length = fn.params.length + fn.rets.length := by
      have := congrArg List.length hnm; simpa using this
    rw [hlen, Nat.sub_self, List.drop_zero] at g2
    exact Goes.preC h34 (g2.bind fun s5 hs5 => fin s5 hs5) (by dsimp only; omega)

/-- a call of a name that is neither a builtin nor a function in scope does not compile -/
theorem sim_call_unbound (hb : Yul.EVM.dialect.builtin f = none) (hf : Funs.find? f fs = none) :
    M5 prog inp ρ fs st (.FunctionCall f args) := by
  intro ctx q d k code hc p hA hF hN s0 n T rest hT hp hs hm hn
  obtain ⟨info, sco, ca, hfc, -⟩ := compileCall hb hc
  obtain ⟨fn', fs'', hf', -⟩ := hF.find hfc
  simp [hf] at hf'

/-- the arguments of a call halt or time out -/
theorem sim_call_args (he : evals inp ρ fs st args = ⟨v, st1, h1⟩)
    (hv : ∀ vs, v = .ok vs → False) (ih : M6 prog inp ρ fs st args) :
    M5 prog inp ρ fs st (.FunctionCall f args) := by
  intro ctx q d k code hc p hA hF hN s0 n T rest hT hp hs hm hn
  have hr : ((eval inp ρ fs st (.FunctionCall f args)).val,
      (eval inp ρ fs st (.FunctionCall f args)).st) = (v, st1) := by
    rw [eval, he]
    cases v with
    | ok vs => exact absurd rfl (hv vs)
    | halt r => rfl
    | timeout => rfl
  rw [hr]
  cases hb : Yul.EVM.dialect.builtin f with
  | some b =>
    obtain ⟨kinds, mk⟩ := b
    obtain ⟨b, i, nargs, outs, ca, -, -, -, -, hca, rfl⟩ := compileBuiltin hb hc
    have r1 := ih ctx q d ca hca p hA.left hF hN s0 n T rest hT hp hs hm hn
    rw [he] at r1
    cases v with
    | ok vs => exact absurd rfl (hv vs)
    | halt r => exact r1
    | timeout => exact r1
  | none =>
    obtain ⟨info, sco, ca, hfc, hpar, rfl, hca, rfl⟩ := compileCall hb hc
    obtain ⟨s2, h02, hp2, hs2, hm2⟩ := call_prefix (n := n) (ρ := ρ) (inp := inp) (m := info.rets)
      (c := ca ++ [.push info.label, .op .Jump, .label (q, 0)]) (by simpa using hA) hp
    have hAa : At prog (p + 3 + info.rets) ca := by
      have := (At.left (a := [Item.push (q, 0)] ++ List.replicate info.rets push0 ++ ca)
        (by simpa using hA)).right
      simpa [Item.size, push0, pushNat_encode_length, Nat.add_assoc] using this
    have r1 := ih ctx q (d + 1 + info.rets) ca hca (p + 3 + info.rets) hAa hF hN s2 n
      (List.replicate info.rets 0 ++ BitVec.ofNat 256 (pos prog (q, 0) % 2 ^ 16) :: T) rest
      (by simp [hT]; omega) hp2 (by rw [hs2, hs]; simp) (hm2.trans hm) hn
    rw [he] at r1
    cases v with
    | ok vs => exact absurd rfl (hv vs)
    | halt r => exact Halts.pre h02 r1
    | timeout => exact Survives.pre h02 r1 (by omega)

end Compiler
