import YulSemnaticsZoo.Compiler.Lemmas.SimStmt

set_option doc.verso true

/-!
# Compiler: the simulation of loops

The cases of {lit}`sim` for {lit}`loop` and for the {lit}`for` statement. There is one lemma for
each shape of an iteration: the condition is 0 or halts; the body ends with {lit}`break`, or it
stops the loop; the post block stops the loop, or the next iteration starts. {lit}`loop_cond`,
{lit}`loop_body` and {lit}`loop_post` are the parts that these lemmas share.
-/

namespace Compiler
open Semantics Yul Yul.Clocked

variable {prog : Code} {inp : Input} {ρ : Readings} {N : List String}

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

theorem sim_loop_zero (h0 : st.clock = 0) :
    M2 prog inp ρ N fs st Γ c post body hc hb hp hl hI := by
  intro ctx q cc cb cp hnone hcc hcb hcp p hA s0 n rest hps hP
  rw [loop, dite_eq_left h0]
  show Survives (layout prog) inp ρ s0 n st.clock
  rw [h0]; exact Survives.zero

/-- the start of an iteration: its {lit}`JUMPDEST`, the condition with one value, and
the test; then the end of the loop for the value 0, else the body -/
theorem loop_cond (hg : Good prog) (L : LoopAt prog p q cc cb cp) (hps : s0.pc = p)
    (hP : Pre prog ctx fs st s0 n rest) (_h0 : ¬st.clock = 0)
    (hcc : compileExpr ctx (q ++ [1]) 0 c = .ok cc)
    (he : eval inp ρ N fs { st with clock := st.clock - 1 } Γ c 1 hc hI' = ⟨.ok vs, st1, h1, p1⟩)
    (ihc : M5 prog inp ρ N fs { st with clock := st.clock - 1 } Γ c 1 hc hI') :
    ∃ x, vs = [x] ∧ st1.vars = st.vars ∧
      Goes prog inp ρ s0 n st.clock st1 (if x = 0 then pos prog (q, 2) else p + 7 + size cc)
        (vals st.vars ++ rest) := by
  obtain ⟨s1, h01, hp1, hs1, hm1⟩ := st_label (n := n) (ρ := ρ) (inp := inp) (L.head.at hps)
  have r := ihc ctx (q ++ [1]) 0 cc hcc (p + 1) L.cond hP.funs hP.names s1 n [] rest rfl
    (by rw [hp1, hps]) (by rw [hs1, hP.stack]; rfl) (hm1.trans hP.mem) hP.reads
  rw [he] at r
  obtain ⟨hl', hv, g⟩ := r
  try dsimp only at g
  obtain ⟨x, rfl⟩ : ∃ x, vs = [x] := by
    match vs, hl' with | [x], _ => exact ⟨x, rfl⟩
  refine ⟨x, rfl, hv, Goes.preC h01 (g.bind fun s2 hs2 => ?_) (by omega)⟩
  obtain ⟨s3, h3, hs3⟩ := st_test (n := st1.reads) (ρ := ρ) (inp := inp) hg (L.test.at hs2.1)
    L.exit hs2.2.1
  refine Goes.done ⟨s3, h3, hs3⟩ ?_ (by rw [hs1, hP.stack]; rfl) hs2.2.2 rfl (by omega)
  rw [hs2.1]; congr 1; omega

theorem sim_loop_false (hg : Good prog) (h0 : ¬st.clock = 0)
    (he : eval inp ρ N fs { st with clock := st.clock - 1 } Γ c 1 hc hI' = ⟨.ok vs, st1, h1, p1⟩)
    (hz : vs.head hne = 0) (ihc : M5 prog inp ρ N fs { st with clock := st.clock - 1 } Γ c 1 hc hI') :
    M2 prog inp ρ N fs st Γ c post body hc hb hp hl hI := by
  intro ctx q cc cb cp hnone hcc hcb hcp p hA s0 n rest hps hP
  have L := loopCode_at hA
  obtain ⟨x, rfl, hv, g⟩ := loop_cond hg L hps hP h0 hcc he ihc
  rw [size_loopCode, loop, dite_eq_right h0, he]
  dsimp only
  rw [ite_eq_left hz]
  simp only [List.head_cons] at hz
  subst hz
  have hexit : pos prog (q, 2) = p + 12 + size cc + size cb + size cp := by
    simpa using pos_at hg (a := []) L.exit
  simp only [ite_true] at g
  refine (Goes.label g (L.exit.shift hexit.symm)).cast (by rw [hexit]; omega) ?_
  rw [hv]

theorem sim_loop_cond_err (h0 : ¬st.clock = 0)
    (he : eval inp ρ N fs { st with clock := st.clock - 1 } Γ c 1 hc hI' = ⟨v, st1, h1, p1⟩)
    (hv : ∀ vs, v = .ok vs → False)
    (ihc : M5 prog inp ρ N fs { st with clock := st.clock - 1 } Γ c 1 hc hI') :
    M2 prog inp ρ N fs st Γ c post body hc hb hp hl hI := by
  intro ctx q cc cb cp hnone hcc hcb hcp p hA s0 n rest hps hP
  have L := loopCode_at hA
  obtain ⟨s1, h01, hp1, hs1, hm1⟩ := st_label (n := n) (ρ := ρ) (inp := inp) (L.head.at hps)
  have r := ihc ctx (q ++ [1]) 0 cc hcc (p + 1) L.cond hP.funs hP.names s1 n [] rest rfl
    (by rw [hp1, hps]) (by rw [hs1, hP.stack]; rfl) (hm1.trans hP.mem) hP.reads
  rw [he] at r
  rw [loop, dite_eq_right h0, he]
  cases v with
  | ok vs => exact absurd rfl (hv vs)
  | halt r' => exact Halts.pre h01 r
  | timeout => exact Survives.pre h01 r (by dsimp only; omega)

/-- the body of the loop: from its start, the outcome of the body -/
theorem loop_body (hg : Good prog) (h0 : ¬st.clock = 0) (L : LoopAt prog p q cc cb cp)
    (hps : s0.pc = p) (hP : Pre prog ctx fs st s0 n rest)
    (hcc : compileExpr ctx (q ++ [1]) 0 c = .ok cc)
    (hcb : compileBlock { ctx with loop := some ((q, 2), (q, 1), ctx.vars.length) } (q ++ [2])
      body = .ok cb)
    (he : eval inp ρ N fs { st with clock := st.clock - 1 } Γ c 1 hc hI' = ⟨.ok vs, st1, h1, p1⟩)
    (hz : ¬vs.head hne = 0) (ihc : M5 prog inp ρ N fs { st with clock := st.clock - 1 } Γ c 1 hc hI')
    (hbe : execBlock inp ρ N fs st1 Γb body hb' hIb = ⟨ob, st2, h2, pb⟩)
    (ihb : M3 prog inp ρ N fs st1 Γb body hb' hIb) :
    st1.vars = st.vars ∧ names st2.vars = names st.vars ∧
      Goes prog inp ρ s0 n st.clock st1 (p + 7 + size cc) (vals st.vars ++ rest) ∧
      ∀ s3, Is s3 (p + 7 + size cc) (vals st.vars ++ rest) st1.mem →
        StmtPost prog inp ρ { ctx with loop := some ((q, 2), (q, 1), ctx.vars.length) } s3
          st1.reads st1 (p + 7 + size cc + size cb) rest (ob, st2) := by
  obtain ⟨x, rfl, hv, g⟩ := loop_cond hg L hps hP h0 hcc he ihc
  simp only [List.head_cons] at hz
  simp only [hz, ite_false] at g
  have hnb : names (execBlock inp ρ N fs st1 Γb body hb' hIb).st.vars = names st1.vars :=
    names_execBlock
  rw [hbe] at hnb
  refine ⟨hv, by rw [hnb, hv], g, fun s3 hs3 => ?_⟩
  have := ihb _ (q ++ [2]) cb hcb (p + 7 + size cc) L.body s3 st1.reads rest hs3.1 (hP.body L hv hs3)
  rwa [hbe] at this

/-- the body ends with {lit}`break`: the end of the loop -/
theorem sim_loop_brk (hg : Good prog) (h0 : ¬st.clock = 0)
    (he : eval inp ρ N fs { st with clock := st.clock - 1 } Γ c 1 hc hI' = ⟨.ok vs, st1, h1, p1⟩)
    (hz : ¬vs.head hne = 0) (ihc : M5 prog inp ρ N fs { st with clock := st.clock - 1 } Γ c 1 hc hI')
    (hbe : execBlock inp ρ N fs st1 { Γ with inLoopBody := true } body hb hIb = ⟨.brk, st2, h2, pb⟩)
    (ihb : M3 prog inp ρ N fs st1 { Γ with inLoopBody := true } body hb hIb) :
    M2 prog inp ρ N fs st Γ c post body hc hb hp hl hI := by
  intro ctx q cc cb cp hnone hcc hcb hcp p hA s0 n rest hps hP
  have L := loopCode_at hA
  obtain ⟨hv, hn2, gb, rb⟩ := loop_body hg h0 L hps hP hcc hcb he hz ihc hbe ihb
  have hexit : pos prog (q, 2) = p + 12 + size cc + size cb + size cp := by
    simpa using pos_at hg (a := []) L.exit
  have hlen2 : st2.vars.length = ctx.vars.length := by
    have := congrArg List.length hn2; rw [hP.names]; simpa using this
  rw [size_loopCode, loop, dite_eq_right h0, he]
  dsimp only
  rw [ite_eq_right hz, hbe]
  dsimp only
  refine StmtPost.pre gb fun s3 hs3 => ?_
  obtain ⟨l, lc, d, hld, g'⟩ := rb s3 hs3
  simp only [Option.some.injEq, Prod.mk.injEq] at hld
  obtain ⟨rfl, rfl, rfl⟩ := hld
  rw [hlen2, Nat.sub_self, List.drop_zero] at g'
  exact (Goes.label g' (L.exit.shift hexit.symm)).cast (by rw [hexit]; omega) rfl

/-- the body ends with {lit}`leave`, a halt or a timeout: the loop ends with it -/
theorem sim_loop_stop (hg : Good prog) (h0 : ¬st.clock = 0)
    (he : eval inp ρ N fs { st with clock := st.clock - 1 } Γ c 1 hc hI' = ⟨.ok vs, st1, h1, p1⟩)
    (hz : ¬vs.head hne = 0) (ihc : M5 prog inp ρ N fs { st with clock := st.clock - 1 } Γ c 1 hc hI')
    (hbe : execBlock inp ρ N fs st1 { Γ with inLoopBody := true } body hb hIb = ⟨ob, st2, h2, pb⟩)
    (ho : ob ≠ .normal ∧ ob ≠ .brk ∧ ob ≠ .cont)
    (ihb : M3 prog inp ρ N fs st1 { Γ with inLoopBody := true } body hb hIb) :
    M2 prog inp ρ N fs st Γ c post body hc hb hp hl hI := by
  intro ctx q cc cb cp hnone hcc hcb hcp p hA s0 n rest hps hP
  have L := loopCode_at hA
  obtain ⟨hv, hn2, gb, rb⟩ := loop_body hg h0 L hps hP hcc hcb he hz ihc hbe ihb
  rw [size_loopCode, loop, dite_eq_right h0, he]
  dsimp only
  rw [ite_eq_right hz, hbe]
  refine StmtPost.pre gb fun s3 hs3 => ?_
  have r3 := rb s3 hs3
  obtain ⟨h1', h2', h3'⟩ := ho
  cases ob with
  | normal => exact absurd rfl h1'
  | brk => exact absurd rfl h2'
  | cont => exact absurd rfl h3'
  | leave => exact r3
  | halt r => exact r3
  | timeout => exact r3

/-- after the body (normal or {lit}`continue`): at the start of the post block -/
theorem loop_post (L : LoopAt prog p q cc cb cp) (hP : Pre prog ctx fs st s0 n rest)
    (hpos : pos prog (q, 1) = p + 7 + size cc + size cb)
    (hn2 : names st2.vars = names st.vars) (ho : ob = .normal ∨ ob = .cont)
    (r3 : StmtPost prog inp ρ { ctx with loop := some ((q, 2), (q, 1), ctx.vars.length) } s3
      st1.reads st1 (p + 7 + size cc + size cb) rest (ob, st2)) :
    Goes prog inp ρ s3 st1.reads st1.clock st2 (p + 8 + size cc + size cb)
      (vals st2.vars ++ rest) := by
  have hlen2 : st2.vars.length = ctx.vars.length := by
    have := congrArg List.length hn2; rw [hP.names]; simpa using this
  rcases ho with rfl | rfl
  · exact (Goes.label r3 L.cont).cast (by omega) rfl
  · obtain ⟨l, lc, d, hld, g'⟩ := r3
    simp only [Option.some.injEq, Prod.mk.injEq] at hld
    obtain ⟨rfl, rfl, rfl⟩ := hld
    rw [hlen2, Nat.sub_self, List.drop_zero, hpos] at g'
    exact (Goes.label g' L.cont).cast (by omega) rfl

/-- the post block ends with {lit}`leave`, a halt or a timeout: the loop ends with it -/
theorem sim_loop_post_stop (hg : Good prog) (h0 : ¬st.clock = 0)
    (he : eval inp ρ N fs { st with clock := st.clock - 1 } Γ c 1 hc hI' = ⟨.ok vs, st1, h1, p1⟩)
    (hz : ¬vs.head hne = 0) (ihc : M5 prog inp ρ N fs { st with clock := st.clock - 1 } Γ c 1 hc hI')
    (hbe : execBlock inp ρ N fs st1 { Γ with inLoopBody := true } body hb hIb =
      ⟨ob, st2, h2, f2, n2⟩)
    (hob : ob = .normal ∨ ob = .cont)
    (ihb : M3 prog inp ρ N fs st1 { Γ with inLoopBody := true } body hb hIb)
    (hpe : execBlock inp ρ N fs st2 Γ post hp hI2 = ⟨op, st3, h3, pp⟩)
    (hop : op ≠ .normal ∧ op ≠ .brk ∧ op ≠ .cont)
    (ihp : M3 prog inp ρ N fs st2 Γ post hp hI2) :
    M2 prog inp ρ N fs st Γ c post body hc hb hp hl hI := by
  intro ctx q cc cb cp hnone hcc hcb hcp p hA s0 n rest hps hP
  have L := loopCode_at hA
  obtain ⟨hv, hn2, gb, rb⟩ := loop_body hg h0 L hps hP hcc hcb he hz ihc hbe ihb
  have hcont : pos prog (q, 1) = p + 7 + size cc + size cb := by
    simpa using pos_at hg (a := []) L.cont
  rw [size_loopCode, loop, dite_eq_right h0, he]
  dsimp only
  rw [ite_eq_right hz, hbe]
  refine StmtPost.pre gb fun s3 hs3 => ?_
  have g2 := loop_post L hP hcont hn2 hob (rb s3 hs3)
  have rp := fun s4 (hs4 : Is s4 (p + 8 + size cc + size cb) (vals st2.vars ++ rest) st2.mem) =>
    ihp ctx (q ++ [3]) cp hcp (p + 8 + size cc + size cb) L.post s4 st2.reads rest hs4.1
      (hP.of hn2 hs4)
  rw [hpe] at rp
  refine StmtPost.pre g2 fun s4 hs4 => ?_
  have r4 := rp s4 hs4
  obtain ⟨h1', h2', h3'⟩ := hop
  rcases hob with rfl | rfl <;> dsimp only <;> rw [hpe] <;> dsimp only
  all_goals
    cases op with
    | normal => exact absurd rfl h1'
    | brk => exact absurd rfl h2'
    | cont => exact absurd rfl h3'
    | leave => exact r4
    | halt r => exact r4
    | timeout => exact r4

/-- the post block ends normally: the next iteration -/
theorem sim_loop_next (hg : Good prog) (h0 : ¬st.clock = 0)
    (he : eval inp ρ N fs { st with clock := st.clock - 1 } Γ c 1 hc hI' = ⟨.ok vs, st1, h1, p1⟩)
    (hz : ¬vs.head hne = 0) (ihc : M5 prog inp ρ N fs { st with clock := st.clock - 1 } Γ c 1 hc hI')
    (hbe : execBlock inp ρ N fs st1 { Γ with inLoopBody := true } body hb hIb =
      ⟨ob, st2, h2, f2, n2⟩)
    (hob : ob = .normal ∨ ob = .cont)
    (ihb : M3 prog inp ρ N fs st1 { Γ with inLoopBody := true } body hb hIb)
    (hpe : execBlock inp ρ N fs st2 Γ post hp hI2 = ⟨.normal, st3, h3, pp⟩)
    (ihp : M3 prog inp ρ N fs st2 Γ post hp hI2)
    (ihl : M2 prog inp ρ N fs st3 Γ c post body hc hb hp hl hI3) :
    M2 prog inp ρ N fs st Γ c post body hc hb hp hl hI := by
  intro ctx q cc cb cp hnone hcc hcb hcp p hA s0 n rest hps hP
  have L := loopCode_at hA
  obtain ⟨hv, hn2, gb, rb⟩ := loop_body hg h0 L hps hP hcc hcb he hz ihc hbe ihb
  have hcont : pos prog (q, 1) = p + 7 + size cc + size cb := by
    simpa using pos_at hg (a := []) L.cont
  have hnp : names (execBlock inp ρ N fs st2 Γ post hp hI2).st.vars = names st2.vars :=
    names_execBlock
  rw [hpe] at hnp
  rw [size_loopCode, loop, dite_eq_right h0, he]
  dsimp only
  rw [ite_eq_right hz, hbe]
  refine StmtPost.pre gb fun s3 hs3 => ?_
  have g2 := loop_post L hP hcont hn2 hob (rb s3 hs3)
  have rp := fun s4 (hs4 : Is s4 (p + 8 + size cc + size cb) (vals st2.vars ++ rest) st2.mem) =>
    ihp ctx (q ++ [3]) cp hcp (p + 8 + size cc + size cb) L.post s4 st2.reads rest hs4.1
      (hP.of hn2 hs4)
  rw [hpe] at rp
  refine StmtPost.pre g2 fun s4 hs4 => ?_
  have r4 := rp s4 hs4
  have rl : ∀ s5, Is s5 (p + 8 + size cc + size cb + size cp) (vals st3.vars ++ rest) st3.mem →
      StmtPost prog inp ρ ctx s5 st3.reads st3 (p + (13 + size cc + size cb + size cp)) rest
        ((loop inp ρ N fs st3 Γ c post body hc hb hp hl hI3).val,
          (loop inp ρ N fs st3 Γ c post body hc hb hp hl hI3).st) := fun s5 hs5 => by
    obtain ⟨s6, h6, hs6⟩ := st_back (n := st3.reads) (ρ := ρ) (inp := inp) hg L hs5.1
    refine StmtPost.steps h6 ?_
    have := ihl ctx q cc cb cp hnone hcc hcb hcp p hA s6 st3.reads rest hs6.1
      (hP.of (by rw [hnp, hn2]) ⟨hs6.1, hs6.2.1.trans hs5.2.1, hs6.2.2.trans hs5.2.2⟩)
    rwa [size_loopCode] at this
  rcases hob with rfl | rfl <;> dsimp only <;> rw [hpe] <;> dsimp only
  all_goals exact StmtPost.pre r4 fun s5 hs5 => rl s5 hs5

/-! ## The {lit}`for` statement -/

theorem compileFor (hc : compileStmt ctx q (.ForLoop ⟨init⟩ c post body) = .ok (code, vars')) :
    ∃ ci vars cc cb cp, compileStmts { ctx with loop := none } (q ++ [0]) 0 init = .ok (ci, vars) ∧
      compileExpr { ctx with loop := none, vars } (q ++ [1]) 0 c = .ok cc ∧
      compileBlock { ctx with loop := some ((q, 2), (q, 1), vars.length), vars } (q ++ [2])
        body = .ok cb ∧
      compileBlock { ctx with loop := none, vars } (q ++ [3]) post = .ok cp ∧
      code = ci ++ loopCode q cc cb cp ++ pops (vars.length - ctx.vars.length) ∧
      vars' = ctx.vars := by
  rw [compileStmt] at hc
  inv hc
  obtain ⟨⟨ci, vars⟩, hci, cc, hcc, cb, hcb, cp, hcp, rfl, rfl⟩ := hc
  exact ⟨ci, vars, cc, cb, cp, hci, hcc, hcb, hcp, rfl, rfl⟩

/-- the context of the init block of a loop -/
theorem Pre.init (hP : Pre prog ctx fs st s0 n rest) :
    Pre prog { ctx with loop := none } fs st s0 n rest where
  funs := hP.funs
  names := hP.names
  loop := by simp
  leave := hP.leave
  stack := hP.stack
  mem := hP.mem
  reads := hP.reads

theorem sim_for
    (he : execs inp ρ N fs st { Γ with inLoopBody := false, inInit := true } init hi hIi =
      ⟨o, st2, h2, p2⟩)
    (ho : o = .normal)
    (hl : loop inp ρ N fs st2
      { init.foldl Scope.after { Γ with inLoopBody := false, inInit := true } with inInit := Γ.inInit }
      c post body hc hb hp hlb hI2 = ⟨o3, st3, h3, p3⟩)
    (ih1 : M4 prog inp ρ N fs st { Γ with inLoopBody := false, inInit := true } init hi hIi)
    (ih2 : M2 prog inp ρ N fs st2
      { init.foldl Scope.after { Γ with inLoopBody := false, inInit := true } with inInit := Γ.inInit }
      c post body hc hb hp hlb hI2) :
    M1 prog inp ρ N fs st Γ (.ForLoop ⟨init⟩ c post body) h hI := by
  subst ho
  intro ctx q code vars' hcd p hA s0 n rest hps hP
  obtain ⟨ci, vars, cc, cb, cp, hci, hcc, hcb, hcp, rfl, rfl⟩ := compileFor hcd
  have hAi : At prog p ci := hA.left.left
  have hAl : At prog (p + size ci) (loopCode q cc cb cp) := hA.left.right
  have r1 := ih1 { ctx with loop := none } (q ++ [0]) 0 ci vars hci p hAi s0 n rest hps hP.init
  have hsuf : names st.vars <:+ names (execs inp ρ N fs st
      { Γ with inLoopBody := false, inInit := true } init hi hIi).st.vars := names_execs
  have hnl : names (loop inp ρ N fs st2
      { init.foldl Scope.after { Γ with inLoopBody := false, inInit := true } with inInit := Γ.inInit }
      c post body hc hb hp hlb hI2).st.vars =
      names st2.vars := names_loop
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
  rw [dite_eq_left rfl]
  dsimp only
  rw [hl]
  dsimp only
  refine ⟨StmtPost.pre g1 fun s1 hs1 => ?_, fun _ => by rw [names_restrict' hsuf3, hP.names]⟩
  have rl := ih2 { ctx with loop := none, vars } q cc cb cp rfl hcc hcb hcp (p + size ci) hAl s1
    st2.reads rest hs1.1
    { funs := hP.funs
      names := hvn
      loop := by simp
      leave := fun l d h => by
        obtain ⟨hd, h'⟩ := hP.leave l d h
        exact ⟨by have := length_le_of_suffix hsuf; omega, h'⟩
      stack := hs1.2.1
      mem := hs1.2.2
      reads := rfl }
  rw [hl] at rl
  cases o3 with
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
  | brk => obtain ⟨l, lc, d, h, -⟩ := rl; simp at h
  | cont => obtain ⟨l, lc, d, h, -⟩ := rl; simp at h
  | leave =>
    obtain ⟨l, d, hld, g⟩ := rl
    have hd := (hP.leave l d hld).1
    exact ⟨l, d, hld, g.cast rfl (by rw [drop_restrict hlen hd])⟩
  | halt r => exact rl
  | timeout => exact rl

theorem sim_for_init
    (he : execs inp ρ N fs st { Γ with inLoopBody := false, inInit := true } init hi hIi =
      ⟨o, st2, h2, p2⟩)
    (ho : ¬o = .normal)
    (ih1 : M4 prog inp ρ N fs st { Γ with inLoopBody := false, inInit := true } init hi hIi) :
    M1 prog inp ρ N fs st Γ (.ForLoop ⟨init⟩ c post body) h hI := by
  intro ctx q code vars' hcd p hA s0 n rest hps hP
  obtain ⟨ci, vars, cc, cb, cp, hci, hcc, hcb, hcp, rfl, rfl⟩ := compileFor hcd
  have hAi : At prog p ci := hA.left.left
  have r1 := ih1 { ctx with loop := none } (q ++ [0]) 0 ci vars hci p hAi s0 n rest hps hP.init
  have hsuf : names st.vars <:+ names (execs inp ρ N fs st
      { Γ with inLoopBody := false, inInit := true } init hi hIi).st.vars := names_execs
  rw [he] at r1 hsuf
  dsimp only at hsuf
  have hlen := length_le_of_suffix hsuf
  rw [exec, he]
  dsimp only
  rw [dite_eq_right ho]
  refine ⟨?_, fun h => absurd h ho⟩
  obtain ⟨r1, -⟩ := r1
  cases o with
  | normal => exact absurd rfl ho
  | brk => obtain ⟨l, lc, d, h, -⟩ := r1; simp at h
  | cont => obtain ⟨l, lc, d, h, -⟩ := r1; simp at h
  | leave =>
    obtain ⟨l, d, hld, g⟩ := r1
    have hd := (hP.leave l d hld).1
    exact ⟨l, d, hld, g.cast rfl (by rw [drop_restrict hlen hd])⟩
  | halt r => exact r1
  | timeout => exact r1

end Compiler
