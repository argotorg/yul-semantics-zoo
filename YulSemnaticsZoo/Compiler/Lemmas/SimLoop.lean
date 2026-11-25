import YulSemnaticsZoo.Compiler.Lemmas.SimStmt

set_option doc.verso true

/-!
# Compiler: the simulation of loops

The cases of {lit}`sim` for {lit}`loop` and for the {lit}`for` statement. One lemma
({lit}`sim_loop`) does each iteration: the cases of the functional induction only give it the
induction hypotheses.
-/

namespace Compiler
open Semantics Yul Yul.Clocked

variable {prog : Code} {inp : Input} {ρ : Readings}

/-- the parts of the code of a loop -/
structure LoopAt (prog : Code) (p : Nat) (q : List Nat) (cc cb cp : Code) : Prop where
  head : At prog p [.label (q, 0)]
  cond : At prog (p + 1) cc
  test : At prog (p + 1 + size cc) ([push0, .op .Eq, .push (q, 2), .op .Jumpi] ++ [])
  body : At prog (p + 7 + size cc) cb
  cont : At prog (p + 7 + size cc + size cb) [.label (q, 1)]
  post : At prog (p + 8 + size cc + size cb) cp
  back : At prog (p + 8 + size cc + size cb + size cp) [.push (q, 0), .op .Jump]
  exit : At prog (p + 12 + size cc + size cb + size cp) [.label (q, 2)]

theorem size_loopCode : size (loopCode q cc cb cp) = 13 + size cc + size cb + size cp := by
  simp [loopCode, EVM.Instr.immediate]; omega

theorem loopCode_at (hA : At prog p (loopCode q cc cb cp)) : LoopAt prog p q cc cb cp where
  head := by
    have := At.left (a := [.label (q, 0)]) (b := cc ++ _) (by simpa [loopCode] using hA)
    exact this
  cond := by
    have := At.mid (a := [.label (q, 0)]) (b := cc) (by simpa [loopCode] using hA)
    exact this.shift (by simp)
  test := by
    have := At.mid (a := [.label (q, 0)] ++ cc) (b := [push0, .op .Eq, .push (q, 2), .op .Jumpi])
      (by simpa [loopCode] using hA)
    have e : p + size ([.label (q, 0)] ++ cc) = p + 1 + size cc := by simp; omega
    simpa using this.shift e
  body := by
    have := At.mid (a := [.label (q, 0)] ++ cc ++ [push0, .op .Eq, .push (q, 2), .op .Jumpi])
      (b := cb) (by simpa [loopCode] using hA)
    exact this.shift (by simp [EVM.Instr.immediate]; omega)
  cont := by
    have := At.mid (a := [.label (q, 0)] ++ cc ++ [push0, .op .Eq, .push (q, 2), .op .Jumpi] ++ cb)
      (b := [.label (q, 1)]) (by simpa [loopCode] using hA)
    exact this.shift (by simp [EVM.Instr.immediate]; omega)
  post := by
    have := At.mid (a := [.label (q, 0)] ++ cc ++ [push0, .op .Eq, .push (q, 2), .op .Jumpi] ++ cb ++
      [.label (q, 1)]) (b := cp) (by simpa [loopCode] using hA)
    exact this.shift (by simp [EVM.Instr.immediate]; omega)
  back := by
    have := At.mid (a := [.label (q, 0)] ++ cc ++ [push0, .op .Eq, .push (q, 2), .op .Jumpi] ++ cb ++
      [.label (q, 1)] ++ cp) (b := [.push (q, 0), .op .Jump]) (by simpa [loopCode] using hA)
    exact this.shift (by simp [EVM.Instr.immediate]; omega)
  exit := by
    have := At.mid (a := [.label (q, 0)] ++ cc ++ [push0, .op .Eq, .push (q, 2), .op .Jumpi] ++ cb ++
      [.label (q, 1)] ++ cp ++ [.push (q, 0), .op .Jump]) (b := [.label (q, 2)]) (c := [])
      (by simpa [loopCode] using hA)
    exact this.shift (by simp [EVM.Instr.immediate]; omega)

theorem Goes.label (g : Goes prog inp ρ s n c st pc stk) (hL : At prog pc [.label l]) :
    Goes prog inp ρ s n c st (pc + 1) stk :=
  g.bind fun s1 hs1 => Goes.done (st_label (n := st.reads) (ρ := ρ) (inp := inp) (hL.at hs1.1))
    (by rw [hs1.1]) hs1.2.1 hs1.2.2 rfl (by omega)

/-- the jump back to the start of the loop: {lit}`PUSH2 head JUMP` -/
theorem st_back (hg : Good prog) (L : LoopAt prog p q cc cb cp)
    (hs : s.pc = p + 8 + size cc + size cb + size cp) :
    ∃ s', Steps (layout prog) inp ρ s n 2 s' n ∧ Is s' p s.stack s.mem := by
  have hA : At prog s.pc (.push (q, 0) :: [.op .Jump]) := by rw [hs]; exact L.back
  obtain ⟨s1, h1, hp1, hs1, hm1⟩ := st_pushLabel (n := n) (ρ := ρ) (inp := inp) hA
  have hlt : pos prog (q, 0) < 2 ^ 16 := pos_lt hg (a := []) (by simpa using L.head)
  have hpl : pos prog (q, 0) = p := by simpa using pos_at hg (a := []) L.head
  obtain ⟨s2, h2, hp2, hs2, hm2⟩ := st_jump (n := n) (ρ := ρ) (inp := inp)
    (by rw [hp1]; simpa using hA.tail : At prog s1.pc [.op .Jump]) hs1
    (by rw [toNat_ofNat_pos hlt, hpl]; exact jumpdest_at L.head)
  exact ⟨s2, h1.trans h2, by rw [hp2, toNat_ofNat_pos hlt, hpl], hs2, by rw [hm2, hm1]⟩

/-- the context of the body of a loop -/
theorem Pre.body (hP : Pre prog ctx fs st s0 n rest) (L : LoopAt prog p q cc cb cp)
    (hv : st1.vars = st.vars) (hs : Is s1 pc (vals st.vars ++ rest) st1.mem) :
    Pre prog { ctx with loop := some ((q, 2), (q, 1), ctx.vars.length) } fs st1 s1 st1.reads
      rest where
  funs := hP.funs
  names := by rw [hP.names, hv]
  loop := fun l lc d h => by
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨by rw [hP.names, hv]; simp, ⟨_, L.exit⟩, ⟨_, L.cont⟩⟩
  leave := by rw [hv]; exact hP.leave
  stack := by rw [hs.2.1, hv]
  mem := hs.2.2
  reads := rfl

/-- the context at a state with the same names of variables -/
theorem Pre.of (hP : Pre prog ctx fs st s0 n rest)
    (hn : Clocked.names st1.vars = Clocked.names st.vars)
    (hs : Is s1 pc (vals st1.vars ++ rest) st1.mem) : Pre prog ctx fs st1 s1 st1.reads rest where
  funs := hP.funs
  names := by rw [hP.names, hn]
  loop := fun l lc d h => by
    have hl : st1.vars.length = st.vars.length := by
      have := congrArg List.length hn; simpa using this
    rw [hl]; exact hP.loop l lc d h
  leave := fun l d h => by
    have hl : st1.vars.length = st.vars.length := by
      have := congrArg List.length hn; simpa using this
    rw [hl]; exact hP.leave l d h
  stack := hs.2.1
  mem := hs.2.2
  reads := rfl

theorem sim_loop_zero (h0 : st.clock = 0) : M2 prog inp ρ fs st c post body := by
  intro ctx q cc cb cp hnone hcc hcb hcp p hA s0 n rest hp hP
  rw [loop]
  simp only [h0, dite_true]
  show Survives (layout prog) inp ρ s0 n st.clock
  rw [h0]; exact Survives.zero

/-- one iteration of a loop, and the rest of the loop -/
theorem sim_loop (hg : Good prog) (h0 : ¬st.clock = 0) {h1 : st1.clock ≤ st.clock - 1}
    (he : eval inp ρ fs ⟨st.vars, st.mem, st.reads, st.clock - 1⟩ c = ⟨v, st1, h1⟩)
    (ihc : M5 prog inp ρ fs ⟨st.vars, st.mem, st.reads, st.clock - 1⟩ c)
    (ihb : ∀ vs, v = .ok vs → ¬vs.headD 0 = 0 → M3 prog inp ρ fs st1 body)
    (ihp : ∀ vs, v = .ok vs → ¬vs.headD 0 = 0 →
      (execBlock inp ρ fs st1 body).val = .normal ∨ (execBlock inp ρ fs st1 body).val = .cont →
      M3 prog inp ρ fs (execBlock inp ρ fs st1 body).st post)
    (ihl : ∀ vs, v = .ok vs → ¬vs.headD 0 = 0 →
      (execBlock inp ρ fs st1 body).val = .normal ∨ (execBlock inp ρ fs st1 body).val = .cont →
      (execBlock inp ρ fs (execBlock inp ρ fs st1 body).st post).val = .normal →
      M2 prog inp ρ fs (execBlock inp ρ fs (execBlock inp ρ fs st1 body).st post).st c post body) :
    M2 prog inp ρ fs st c post body := by
  intro ctx q cc cb cp hnone hcc hcb hcp p hA s0 n rest hp hP
  have L := loopCode_at hA
  rw [size_loopCode]
  -- the start of the iteration, and the condition
  obtain ⟨s1, h01, hp1, hs1, hm1⟩ := st_label (n := n) (ρ := ρ) (inp := inp) (L.head.at hp)
  have r := ihc ctx (q ++ [1]) 0 1 cc hcc (p + 1) L.cond hP.funs hP.names s1 n [] rest rfl
    (by rw [hp1, hp]) (by rw [hs1, hP.stack]; rfl) (hm1.trans hP.mem) hP.reads
  rw [he] at r
  rw [loop]
  simp only [h0, dite_false]
  rw [he]
  cases v with
  | halt r' => exact Halts.pre h01 r
  | timeout => exact Survives.pre h01 r (by dsimp only; omega)
  | ok vs =>
  obtain ⟨hl, hv, g⟩ := r
  dsimp only at hv g
  obtain ⟨x, rfl⟩ : ∃ x, vs = [x] := by
    match vs, hl with | [x], _ => exact ⟨x, rfl⟩
  have hexit : pos prog (q, 2) = p + 12 + size cc + size cb + size cp := by
    simpa using pos_at hg (a := []) L.exit
  have hcont : pos prog (q, 1) = p + 7 + size cc + size cb := by
    simpa using pos_at hg (a := []) L.cont
  dsimp only
  simp only [List.headD_cons]
  by_cases hx : x = 0
  · -- the condition is false: the end of the loop
    subst hx
    simp only [ite_true]
    refine Goes.preC h01 (g.bind fun s2 hs2 => ?_) (by omega)
    obtain ⟨s3, h3, hs3⟩ := st_test (n := st1.reads) (ρ := ρ) (inp := inp) hg (L.test.at hs2.1)
      L.exit hs2.2.1
    simp only [ite_true] at hs3
    have := Goes.label (Goes.done (st := st1) (c := st1.clock) ⟨s3, h3, hs3⟩ (by rw [hexit]) rfl hs2.2.2 rfl
      (by omega))
      (L.exit.shift hexit.symm)
    refine this.cast (by rw [hexit]; try omega) ?_
    simp [hs1, hP.stack, hv]
  simp only [hx, ite_false]
  -- the body
  have hb := ihb [x] rfl (by simpa using hx)
  have hp' := ihp [x] rfl (by simpa using hx)
  have hl' := ihl [x] rfl (by simpa using hx)
  have hnb := (names_mono inp ρ).2.2.1 fs st1 body
  have gb : Goes prog inp ρ s0 n st.clock st1 (p + 7 + size cc) (vals st.vars ++ rest) := by
    refine Goes.preC h01 (g.bind fun s2 hs2 => ?_) (by omega)
    obtain ⟨s3, h3, hs3⟩ := st_test (n := st1.reads) (ρ := ρ) (inp := inp) hg (L.test.at hs2.1)
      L.exit hs2.2.1
    simp only [hx, ite_false] at hs3
    exact Goes.done ⟨s3, h3, hs3⟩ (by rw [hs2.1]; omega) (by rw [hs1, hP.stack]; rfl) hs2.2.2 rfl
      (by omega)
  have rb := fun s3 (hs3 : Is s3 (p + 7 + size cc) (vals st.vars ++ rest) st1.mem) =>
    hb _ (q ++ [2]) cb hcb (p + 7 + size cc) L.body s3 st1.reads rest hs3.1 (hP.body L hv hs3)
  generalize execBlock inp ρ fs st1 body = Rb at rb hp' hl' hnb ⊢
  obtain ⟨ob, st2, h2⟩ := Rb
  dsimp only at rb hp' hl' hnb ⊢
  have hlen2 : st2.vars.length = ctx.vars.length := by
    have := congrArg List.length hnb; rw [hP.names, ← hv]; simpa using this
  have hn2 : names st2.vars = names st.vars := by rw [hnb, hv]
  refine StmtPost.pre gb fun s3 hs3 => ?_
  have r3 := rb s3 hs3
  -- after the body (normal or `continue`): at the post block
  have g2 : ob = .normal ∨ ob = .cont →
      Goes prog inp ρ s3 st1.reads st1.clock st2 (p + 8 + size cc + size cb) (vals st2.vars ++ rest) := by
    intro ho
    rcases ho with rfl | rfl
    · exact (Goes.label r3 L.cont).cast (by omega) rfl
    · obtain ⟨l, lc, d, hld, g'⟩ := r3
      simp only [Option.some.injEq, Prod.mk.injEq] at hld
      obtain ⟨rfl, rfl, rfl⟩ := hld
      rw [hlen2, Nat.sub_self, List.drop_zero, hcont] at g'
      exact (Goes.label g' L.cont).cast (by omega) rfl
  cases ob
  case brk =>
    obtain ⟨l, lc, d, hld, g'⟩ := r3
    simp only [Option.some.injEq, Prod.mk.injEq] at hld
    obtain ⟨rfl, rfl, rfl⟩ := hld
    rw [hlen2, Nat.sub_self, List.drop_zero] at g'
    exact (Goes.label g' (L.exit.shift hexit.symm)).cast (by rw [hexit]; omega) rfl
  case leave => exact r3
  case halt => exact r3
  case timeout => exact r3
  all_goals
    have g2' := g2 (by simp)
    have hp'' := hp' (by simp)
    have hl'' := hl' (by simp)
    have rp := fun s4 (hs4 : Is s4 (p + 8 + size cc + size cb) (vals st2.vars ++ rest) st2.mem) =>
      hp'' ctx (q ++ [3]) cp hcp (p + 8 + size cc + size cb) L.post s4 st2.reads rest hs4.1
        (hP.of hn2 hs4)
    have hnp := (names_mono inp ρ).2.2.1 fs st2 post
    simp only at rp hl'' ⊢
    generalize execBlock inp ρ fs st2 post = Rp at rp hl'' hnp ⊢
    obtain ⟨op, st3, h3⟩ := Rp
    dsimp only at rp hl'' hnp ⊢
    refine StmtPost.pre g2' fun s4 hs4 => ?_
    have r4 := rp s4 hs4
    cases op
    case normal =>
      refine StmtPost.pre r4 fun s5 hs5 => ?_
      obtain ⟨s6, h6, hs6⟩ := st_back (n := st3.reads) (ρ := ρ) (inp := inp) hg L hs5.1
      refine StmtPost.steps h6 ?_
      have := hl'' rfl ctx q cc cb cp hnone hcc hcb hcp p hA s6 st3.reads rest hs6.1
        (hP.of (by rw [hnp, hn2]) ⟨hs6.1, hs6.2.1.trans hs5.2.1, hs6.2.2.trans hs5.2.2⟩)
      rw [size_loopCode] at this
      simpa [Res.up] using this
    case brk => obtain ⟨l, lc, d, hld, -⟩ := r4; simp [hnone] at hld
    case cont => obtain ⟨l, lc, d, hld, -⟩ := r4; simp [hnone] at hld
    all_goals exact r4

/-! ## The {lit}`for` statement -/

theorem compileFor (hc : compileStmt ctx q (.ForLoop ⟨init⟩ c post body) = .ok (code, vars')) :
    ∃ ctxi ci vars cc cb cp, scope { ctx with loop := none } (q ++ [0]) init = .ok ctxi ∧
      compileStmts ctxi (q ++ [0]) 0 init = .ok (ci, vars) ∧
      compileExpr { ctxi with vars } (q ++ [1]) 0 c 1 = .ok cc ∧
      compileBlock { { ctxi with vars } with loop := some ((q, 2), (q, 1), vars.length) } (q ++ [2])
        body = .ok cb ∧
      compileBlock { ctxi with vars } (q ++ [3]) post = .ok cp ∧
      code = ci ++ loopCode q cc cb cp ++ pops (vars.length - ctx.vars.length) ∧
      vars' = ctx.vars := by
  rw [compileStmt] at hc
  inv hc
  obtain ⟨ctxi, hs, ⟨ci, vars⟩, hci, cc, hcc, cb, hcb, cp, hcp, rfl, rfl⟩ := hc
  exact ⟨ctxi, ci, vars, cc, cb, cp, hs, hci, hcc, hcb, hcp, rfl, rfl⟩

/-- the context of the init block of a loop -/
theorem Pre.init (hP : Pre prog ctx fs st s0 n rest) (hs : scope { ctx with loop := none } q ss = .ok ctxi)
    (hci : compileStmts ctxi q 0 ss = .ok (ci, vars)) (hA : At prog p ci) :
    Pre prog ctxi (defs ss :: fs) st s0 n rest := by
  have hctx := scope_ok hs
  exact
    { funs := funsOK_scope (ctx := { ctx with loop := none }) hP.funs hs hci hA
      names := by rw [hctx]; exact hP.names
      loop := by rw [hctx]; simp
      leave := by rw [hctx]; exact hP.leave
      stack := hP.stack
      mem := hP.mem
      reads := hP.reads }

theorem sim_for (he : execs inp ρ (defs init :: fs) st init = ⟨.normal, st2, h2⟩)
    (hl : loop inp ρ (defs init :: fs) st2 c post body = ⟨o, st3, h3⟩)
    (ih1 : M4 prog inp ρ (defs init :: fs) st init)
    (ih2 : M2 prog inp ρ (defs init :: fs) st2 c post body) :
    M1 prog inp ρ fs st (.ForLoop ⟨init⟩ c post body) := by
  intro ctx q code vars' hc p hA s0 n rest hp hP
  obtain ⟨ctxi, ci, vars, cc, cb, cp, hsc, hci, hcc, hcb, hcp, rfl, rfl⟩ := compileFor hc
  have hctx := scope_ok hsc
  have hAi : At prog p ci := hA.left.left
  have hAl : At prog (p + size ci) (loopCode q cc cb cp) := hA.left.right
  have r1 := ih1 ctxi (q ++ [0]) 0 ci vars hci p hAi s0 n rest hp (hP.init hsc hci hAi)
  have hsuf := (names_mono inp ρ).2.2.2.1 (defs init :: fs) st init
  have hnl := (names_mono inp ρ).2.1 (defs init :: fs) st2 c post body
  rw [he] at r1 hsuf
  rw [hl] at hnl
  dsimp only at hsuf hnl
  obtain ⟨g1, hvn⟩ := r1
  have hvn := hvn rfl
  dsimp only at hvn g1
  have hlen : st.vars.length ≤ st3.vars.length := by
    rw [← (by have := congrArg List.length hnl; simpa using this.symm : st2.vars.length = st3.vars.length)]
    exact length_le_of_suffix hsuf
  have hsuf3 : names st.vars <:+ names st3.vars := by rw [hnl]; exact hsuf
  rw [exec, he]
  dsimp only
  rw [hl]
  dsimp only
  refine ⟨StmtPost.pre g1 fun s1 hs1 => ?_, fun _ => by rw [names_restrict' hsuf3, hP.names]⟩
  have rl := ih2 { ctxi with vars } q cc cb cp (by rw [hctx]) hcc hcb hcp (p + size ci) hAl s1
    st2.reads rest hs1.1
    { funs := (hP.init hsc hci hAi).funs
      names := hvn
      loop := by rw [hctx]; simp
      leave := fun l d h => by
        rw [hctx] at h; obtain ⟨hd, h'⟩ := hP.leave l d h
        exact ⟨by have := length_le_of_suffix hsuf; omega, h'⟩
      stack := hs1.2.1
      mem := hs1.2.2
      reads := rfl }
  rw [hl] at rl
  cases o with
  | normal =>
    refine Goes.bind rl fun s2 hs2 => ?_
    have hk : vars.length - ctx.vars.length = st3.vars.length - st.vars.length := by
      rw [hvn, hP.names, ← hnl]; simp
    obtain ⟨s4, h4, hp4, hs4, hm4⟩ := st_pops (n := st3.reads) (ρ := ρ) (inp := inp) (c := [])
      (by rw [hs2.1]; simpa [size_loopCode, Nat.add_assoc] using hA.right)
      (l := (vals st3.vars).take (st3.vars.length - st.vars.length))
      (st := (vals st3.vars).drop (st3.vars.length - st.vars.length) ++ rest)
      (by rw [hs2.2.1, ← List.append_assoc, List.take_append_drop]) (by simp [hk])
    refine Goes.done ⟨s4, h4, hp4, hs4, hm4⟩
      (by rw [hs2.1, hk]; simp [pops, EVM.Instr.immediate, size_loopCode]; omega) ?_ hs2.2.2 rfl
      (by simp [restrict])
    simp [restrict, List.map_drop]
  | brk => obtain ⟨l, lc, d, h, -⟩ := rl; rw [hctx] at h; simp at h
  | cont => obtain ⟨l, lc, d, h, -⟩ := rl; rw [hctx] at h; simp at h
  | leave =>
    obtain ⟨l, d, hld, g⟩ := rl
    have hd := (hP.leave l d (by rw [hctx] at hld; exact hld)).1
    exact ⟨l, d, by rw [hctx] at hld; exact hld, g.cast rfl (by rw [drop_restrict hlen hd])⟩
  | halt r => exact rl
  | timeout => exact rl

theorem sim_for_init (he : execs inp ρ (defs init :: fs) st init = ⟨o, st2, h2⟩)
    (ho : o ≠ .normal) (ih1 : M4 prog inp ρ (defs init :: fs) st init) :
    M1 prog inp ρ fs st (.ForLoop ⟨init⟩ c post body) := by
  intro ctx q code vars' hc p hA s0 n rest hp hP
  obtain ⟨ctxi, ci, vars, cc, cb, cp, hsc, hci, hcc, hcb, hcp, rfl, rfl⟩ := compileFor hc
  have hctx := scope_ok hsc
  have hAi : At prog p ci := hA.left.left
  have r1 := ih1 ctxi (q ++ [0]) 0 ci vars hci p hAi s0 n rest hp (hP.init hsc hci hAi)
  have hsuf := (names_mono inp ρ).2.2.2.1 (defs init :: fs) st init
  rw [he] at r1 hsuf
  dsimp only at hsuf
  have hlen := length_le_of_suffix hsuf
  have hr : exec inp ρ fs st (.ForLoop ⟨init⟩ c post body) = ⟨o, restrict st st2, h2⟩ := by
    rw [exec, he]
    cases o <;> first | exact absurd rfl ho | rfl
  rw [hr]
  refine ⟨?_, fun h => absurd h ho⟩
  obtain ⟨r1, -⟩ := r1
  cases o with
  | normal => exact absurd rfl ho
  | brk => obtain ⟨l, lc, d, h, -⟩ := r1; rw [hctx] at h; simp at h
  | cont => obtain ⟨l, lc, d, h, -⟩ := r1; rw [hctx] at h; simp at h
  | leave =>
    obtain ⟨l, d, hld, g⟩ := r1
    have hd := (hP.leave l d (by rw [hctx] at hld; exact hld)).1
    exact ⟨l, d, by rw [hctx] at hld; exact hld, g.cast rfl (by rw [drop_restrict hlen hd])⟩
  | halt r => exact r1
  | timeout => exact r1

end Compiler
