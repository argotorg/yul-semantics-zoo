import YulSemnaticsZoo.Compiler.Lemmas.SimCall

set_option doc.verso true

/-!
# Compiler: the simulation of statements

The cases of {lit}`sim` for {lit}`exec` (but {lit}`for`), {lit}`execBlock` and {lit}`execs`.
-/

namespace Compiler
open Semantics Yul Yul.Clocked

variable {prog : Code} {inp : Input} {ρ : Readings} {N : List String}

/-! ## Assignments -/

theorem assign_cons (h : assign vars (x :: xs) = .ok ac) :
    ∃ j it ac', vars.idxOf? x = some j ∧ swap (xs.length + 1 + j) = .ok it ∧
      assign vars xs = .ok ac' ∧ ac = [it, .op .Pop] ++ ac' := by
  rw [assign] at h
  split at h
  · next j hj =>
    inv h
    obtain ⟨it, hit, ac', hac, rfl⟩ := h
    exact ⟨j, it, ac', hj, hit, hac, rfl⟩
  · inv h

theorem st_assign (h : assign vars xs = .ok ac) (hA : At prog s.pc (ac ++ c))
    (hN : vars = names V) (hs : s.stack = vs ++ vals V ++ rest) (hx : ∀ x ∈ xs, x ∈ names V)
    (hl : vs.length = xs.length) :
    ∃ s', Steps (layout prog) inp ρ s n (2 * xs.length) s' n ∧
      Is s' (s.pc + size ac) (vals (Vars.assign V xs vs hx hl) ++ rest) s.mem := by
  induction xs generalizing V vs s ac with
  | nil =>
    rw [assign] at h; cases h
    obtain rfl := List.eq_nil_of_length_eq_zero hl
    exact ⟨s, .refl, by simp [Is, hs, Vars.assign]⟩
  | cons x xs ih =>
    obtain ⟨j, it, ac', hj, hit, hac, rfl⟩ := assign_cons h
    obtain ⟨hk, rfl⟩ := swap_ok hit
    obtain ⟨v, vs', rfl⟩ : ∃ v vs', vs = v :: vs' := by
      cases vs with
      | nil => simp at hl
      | cons v vs' => exact ⟨v, vs', rfl⟩
    have hl' : vs'.length = xs.length := by simpa using hl
    have hj' : (names V).idxOf? x = some j := hN ▸ hj
    have hjl : j < (vals V).length := by
      have := (List.idxOf?_eq_some_iff.mp hj').1; simpa using this
    have hxV : x ∈ names V := hx x (by simp)
    have hv : (vs' ++ vals V ++ rest)[xs.length + 1 + j - 1]? = some (Vars.get V x hxV) := by
      rw [show xs.length + 1 + j - 1 = vs'.length + j by omega, List.append_assoc,
        List.getElem?_append_right (by omega), show vs'.length + j - vs'.length = j by omega,
        List.getElem?_append_left hjl]
      exact get_of_idx hj' hxV
    have hA1 : At prog s.pc (.op (.Swap (xs.length + 1 + j) hk) :: (.op .Pop :: (ac' ++ c))) := by
      simpa using hA
    obtain ⟨s1, h1, hp1, hs1, hm1⟩ := st_swap (n := n) (ρ := ρ) (inp := inp) hA1
      (by rw [hs]; rfl) hv
    have hA2 : At prog s1.pc (.op .Pop :: (ac' ++ c)) := by
      rw [hp1]; simpa [Item.size, EVM.Instr.encode, EVM.Instr.immediate] using hA1.tail
    obtain ⟨s2, h2, hp2, hs2, hm2⟩ := st_pop (n := n) (ρ := ρ) (inp := inp) hA2 hs1
    have hA3 : At prog s2.pc (ac' ++ c) := by
      rw [hp2]; simpa [Item.size, EVM.Instr.encode, EVM.Instr.immediate] using hA2.tail
    have hs2' : s2.stack = vs' ++ vals (Vars.set V x hxV v) ++ rest := by
      rw [hs2, vals_set hj', show xs.length + 1 + j - 1 = vs'.length + j by omega,
        List.append_assoc, List.set_append_right _ _ (by omega),
        show vs'.length + j - vs'.length = j by omega, List.set_append_left _ _ hjl,
        List.append_assoc]
    obtain ⟨s3, h3, hp3, hs3, hm3⟩ := ih hac hA3 (by rw [names_set]; exact hN) hs2'
      (fun y hy => by rw [names_set]; exact hx y (by simp [hy])) hl'
    refine ⟨s3, by simpa [Nat.mul_add, Nat.add_comm] using (h1.trans h2).trans h3, ?_, ?_, ?_⟩
    · rw [hp3, hp2, hp1]; simp [Item.size, EVM.Instr.encode, EVM.Instr.immediate]; omega
    · rw [hs3]; rfl
    · rw [hm3, hm2, hm1]

/-! ## Statements -/

theorem sim_block (ih : M3 prog inp ρ N fs st Γ b h' hI) :
    M1 prog inp ρ N fs st Γ (.Block b) h hI := by
  intro ctx q code vars' hc p hA s0 n rest hp hP
  rw [compileStmt] at hc
  inv hc
  obtain ⟨c, hc, rfl, rfl⟩ := hc
  rw [exec]
  refine ⟨ih ctx q c hc p hA s0 n rest hp hP, fun _ => ?_⟩
  rw [hP.names]
  exact names_execBlock.symm

theorem sim_fundef (hg : Good prog) :
    M1 prog inp ρ N fs st Γ (.FunctionDefinition f ps rs body) h hI := by
  intro ctx q code vars' hc p hA s0 n rest hp hP
  obtain ⟨cb, c, -, -, rfl, rfl⟩ := compileFunDef hc
  rw [exec]
  refine ⟨?_, fun _ => hP.names⟩
  have hA1 : At prog s0.pc (.push (q, 1) :: (.op .Jump :: (c ++ [.label (q, 1)]))) := by
    rw [hp]; simpa using hA
  obtain ⟨s1, h1, hp1, hs1, hm1⟩ := st_pushLabel (n := n) (ρ := ρ) (inp := inp) hA1
  have hL : At prog (p + 4 + size c) [.label (q, 1)] := by
    have := hA.right (a := [.push (q, 1), .op .Jump] ++ c)
    rw [show p + 4 + size c = p + (3 + (1 + size c)) by omega]
    simpa [Item.size, EVM.Instr.encode, EVM.Instr.immediate, Nat.add_assoc] using this
  have hlt : pos prog (q, 1) < 2 ^ 16 := pos_lt hg (a := []) (by simpa using hL)
  have hpl : pos prog (q, 1) = p + 4 + size c := by simpa using pos_at hg (a := []) hL
  have hA2 : At prog s1.pc (.op .Jump :: (c ++ [.label (q, 1)])) := by
    rw [hp1]; simpa [Item.size] using hA1.tail
  obtain ⟨s2, h2, hp2, hs2, hm2⟩ := st_jump (n := n) (ρ := ρ) (inp := inp) hA2 hs1
    (by rw [toNat_ofNat_pos hlt, hpl]; exact jumpdest_at hL)
  obtain ⟨s3, h3, hp3, hs3, hm3⟩ := st_label (n := n) (ρ := ρ) (inp := inp)
    (by rw [hp2, toNat_ofNat_pos hlt, hpl]; exact hL : At prog s2.pc [.label (q, 1)])
  refine Goes.done ⟨s3, (h1.trans h2).trans h3, hp3, hs3, hm3⟩ ?_ ?_ ?_ hP.reads
    (by dsimp only; omega)
  · rw [hp2, toNat_ofNat_pos hlt, hpl]
    simp [Item.size, EVM.Instr.encode, EVM.Instr.immediate]; omega
  · rw [hs2, hP.stack]
  · rw [hm2, hm1, hP.mem]

theorem sim_let_none : M1 prog inp ρ N fs st Γ (.VariableDeclaration xs none) h hI := by
  intro ctx q code vars' hc p hA s0 n rest hp hP
  rw [compileStmt] at hc
  inv hc
  obtain ⟨rfl, rfl⟩ := hc
  rw [exec]
  refine ⟨?_, fun _ => by simp [hP.names]⟩
  obtain ⟨s1, h1, hp1, hs1, hm1⟩ := st_push0s (n := n) (ρ := ρ) (inp := inp) (k := xs.length)
    (c := []) (by rw [hp]; simpa using hA)
  refine Goes.done ⟨s1, h1, hp1, hs1, hm1⟩ ?_ ?_ hP.mem hP.reads (by dsimp only; omega)
  · rw [hp]; simp [Item.size, push0, pushNat, toBytes, EVM.Instr.encode, EVM.Instr.immediate]
  · rw [hP.stack]; simp [vals_bind]

theorem sim_let {he1 : e.WellFormed EVM.dialect N Γ xs.length}
    {p1 : AfterExpr st.vars xs.length (.ok vs) st1.vars}
    (he : eval inp ρ N fs st Γ e xs.length he1 hI = ⟨.ok vs, st1, h1, p1⟩)
    (ih : M5 prog inp ρ N fs st Γ e xs.length he1 hI) :
    M1 prog inp ρ N fs st Γ (.VariableDeclaration xs (some e)) h hI := by
  intro ctx q code vars' hc p hA s0 n rest hp hP
  rw [compileStmt] at hc
  inv hc
  obtain ⟨c, hc, rfl, rfl⟩ := hc
  have r := ih ctx q 0 c hc p hA hP.funs hP.names s0 n [] rest rfl hp
    (by simp [hP.stack]) hP.mem hP.reads
  rw [he] at r
  obtain ⟨hl, hv, g⟩ := r
  dsimp only at hv g
  rw [exec, he]
  refine ⟨?_, fun _ => by simp [hP.names, hv]⟩
  refine g.cast rfl ?_
  rw [hP.stack, vals_append, vals_bind, hv]; simp

theorem sim_let_err {he1 : e.WellFormed EVM.dialect N Γ xs.length}
    {p1 : AfterExpr st.vars xs.length v st1.vars}
    (he : eval inp ρ N fs st Γ e xs.length he1 hI = ⟨v, st1, h1, p1⟩)
    (hv : ∀ vs, v = .ok vs → False) (ih : M5 prog inp ρ N fs st Γ e xs.length he1 hI) :
    M1 prog inp ρ N fs st Γ (.VariableDeclaration xs (some e)) h hI := by
  intro ctx q code vars' hc p hA s0 n rest hp hP
  rw [compileStmt] at hc
  inv hc
  obtain ⟨c, hc, rfl, rfl⟩ := hc
  have r := ih ctx q 0 c hc p hA hP.funs hP.names s0 n [] rest rfl hp
    (by simp [hP.stack]) hP.mem hP.reads
  rw [he] at r
  rw [exec, he]
  cases v with
  | ok vs => exact absurd rfl (hv vs)
  | halt r' => exact ⟨r, fun h => by cases h⟩
  | timeout => exact ⟨r, fun h => by cases h⟩

theorem sim_assign {he1 : e.WellFormed EVM.dialect N Γ xs.length}
    {p1 : AfterExpr st.vars xs.length (.ok vs) st1.vars}
    (he : eval inp ρ N fs st Γ e xs.length he1 hI = ⟨.ok vs, st1, h1, p1⟩)
    (ih : M5 prog inp ρ N fs st Γ e xs.length he1 hI) :
    M1 prog inp ρ N fs st Γ (.Assignment xs e) h hI := by
  intro ctx q code vars' hc p hA s0 n rest hp hP
  rw [compileStmt] at hc
  inv hc
  obtain ⟨c, hc, ac, hac, rfl, rfl⟩ := hc
  have r := ih ctx q 0 c hc p hA.left hP.funs hP.names s0 n [] rest rfl hp
    (by simp [hP.stack]) hP.mem hP.reads
  rw [he] at r
  obtain ⟨hl, hv, g⟩ := r
  dsimp only at hv g
  rw [exec, he]
  refine ⟨g.bind fun s1 hs1 => ?_, fun _ => by simp [hP.names, hv]⟩
  obtain ⟨s2, h2, hp2, hs2, hm2⟩ := st_assign (n := st1.reads) (ρ := ρ) (inp := inp) (c := [])
    hac (by rw [hs1.1]; simpa using hA.right) (V := st1.vars) (by rw [hP.names, hv])
    (vs := vs) (rest := rest) (by rw [hs1.2.1, hP.stack, hv]; simp) _ hl
  exact Goes.done ⟨s2, h2, hp2, hs2, hm2⟩ (by rw [hs1.1]; simp [Nat.add_assoc]) rfl hs1.2.2 rfl
    (by dsimp only; omega)

theorem sim_assign_err {he1 : e.WellFormed EVM.dialect N Γ xs.length}
    {p1 : AfterExpr st.vars xs.length v st1.vars}
    (he : eval inp ρ N fs st Γ e xs.length he1 hI = ⟨v, st1, h1, p1⟩)
    (hv : ∀ vs, v = .ok vs → False) (ih : M5 prog inp ρ N fs st Γ e xs.length he1 hI) :
    M1 prog inp ρ N fs st Γ (.Assignment xs e) h hI := by
  intro ctx q code vars' hc p hA s0 n rest hp hP
  rw [compileStmt] at hc
  inv hc
  obtain ⟨c, hc, ac, hac, rfl, rfl⟩ := hc
  have r := ih ctx q 0 c hc p hA.left hP.funs hP.names s0 n [] rest rfl hp
    (by simp [hP.stack]) hP.mem hP.reads
  rw [he] at r
  rw [exec, he]
  cases v with
  | ok vs => exact absurd rfl (hv vs)
  | halt r' => exact ⟨r, fun h => by cases h⟩
  | timeout => exact ⟨r, fun h => by cases h⟩

theorem sim_expr {h : (Statement.Expression e).WellFormed EVM.dialect N Γ}
    (he : eval inp ρ N fs st Γ e 0 h hI = ⟨v, st1, h1, p1⟩)
    (ih : M5 prog inp ρ N fs st Γ e 0 h hI) :
    M1 prog inp ρ N fs st Γ (.Expression e) h hI := by
  intro ctx q code vars' hc p hA s0 n rest hp hP
  rw [compileStmt] at hc
  inv hc
  obtain ⟨c, hc, rfl, rfl⟩ := hc
  have r := ih ctx q 0 c hc p hA hP.funs hP.names s0 n [] rest rfl hp
    (by simp [hP.stack]) hP.mem hP.reads
  rw [he] at r
  rw [exec, he]
  dsimp only
  cases v with
  | ok vs =>
    obtain ⟨hl, hv, g⟩ := r
    obtain rfl := List.eq_nil_of_length_eq_zero hl
    dsimp only at hv g
    refine ⟨g.cast rfl ?_, fun _ => by simp [hP.names, hv]⟩
    rw [hP.stack, hv]; simp
  | halt r' => exact ⟨r, fun h => by cases h⟩
  | timeout => exact ⟨r, fun h => by cases h⟩

/-- the code of an {lit}`if` -/
theorem compileIf (hc : compileStmt ctx q (.If c b) = .ok (code, vars')) :
    ∃ cc cb, compileExpr ctx (q ++ [0]) 0 c = .ok cc ∧ compileBlock ctx (q ++ [1]) b = .ok cb ∧
      code = cc ++ [push0, .op .Eq, .push (q, 0), .op .Jumpi] ++ cb ++ [.label (q, 0)] ∧
      vars' = ctx.vars := by
  rw [compileStmt] at hc
  inv hc
  obtain ⟨cc, hcc, cb, hcb, rfl, rfl⟩ := hc
  exact ⟨cc, cb, hcc, hcb, rfl, rfl⟩

/-- the test of an {lit}`if` or of a loop: {lit}`PUSH0 EQ PUSH2 l JUMPI` -/
theorem st_test (hg : Good prog) (hA : At prog s.pc ([push0, .op .Eq, .push l, .op .Jumpi] ++ c))
    (hL : At prog pl [.label l]) (hs : s.stack = v :: S) :
    ∃ s', Steps (layout prog) inp ρ s n 4 s' n ∧
      Is s' (if v = 0 then pos prog l else s.pc + 6) S s.mem := by
  have hA1 : At prog s.pc (push0 :: (.op .Eq :: (.push l :: (.op .Jumpi :: c)))) := by
    simpa using hA
  obtain ⟨s1, h1, hp1, hs1, hm1⟩ := st_push0 (n := n) (ρ := ρ) (inp := inp) hA1
  have hA2 : At prog s1.pc (.op .Eq :: (.push l :: (.op .Jumpi :: c))) := by
    rw [hp1]; simpa [push0, Item.size, pushNat_encode_length] using hA1.tail
  obtain ⟨s2, h2, hp2, hs2, hm2⟩ := st_eq (n := n) (ρ := ρ) (inp := inp) hA2
    (by rw [hs1, hs])
  have hA3 : At prog s2.pc (.push l :: (.op .Jumpi :: c)) := by
    rw [hp2]; simpa [Item.size, EVM.Instr.encode, EVM.Instr.immediate] using hA2.tail
  obtain ⟨s3, h3, hp3, hs3, hm3⟩ := st_pushLabel (n := n) (ρ := ρ) (inp := inp) hA3
  have hA4 : At prog s3.pc (.op .Jumpi :: c) := by
    rw [hp3]; simpa [Item.size] using hA3.tail
  have hlt : pos prog l < 2 ^ 16 := pos_lt hg (a := []) (by simpa using hL)
  have hpl : pos prog l = pl := by simpa using pos_at hg (a := []) hL
  by_cases hv : v = 0
  · subst hv
    obtain ⟨s4, h4, hp4, hs4, hm4⟩ := st_jumpi_ne (n := n) (ρ := ρ) (inp := inp) hA4
      (v := Semantics.eq 0 0) (by rw [hs3, hs2]) (by simp [Semantics.eq])
      (by rw [toNat_ofNat_pos hlt, hpl]; exact jumpdest_at hL)
    refine ⟨s4, ((h1.trans h2).trans h3).trans h4, ?_, hs4, by rw [hm4, hm3, hm2, hm1]⟩
    rw [hp4, toNat_ofNat_pos hlt]; simp
  · obtain ⟨s4, h4, hp4, hs4, hm4⟩ := st_jumpi_zero (n := n) (ρ := ρ) (inp := inp) hA4
      (by rw [hs3, hs2, show Semantics.eq 0 v = 0 by simp [Semantics.eq]; exact fun h => hv h.symm])
    refine ⟨s4, ((h1.trans h2).trans h3).trans h4, ?_, hs4, by rw [hm4, hm3, hm2, hm1]⟩
    rw [ite_eq_right_of_eq_false _ _ (eq_false hv), hp4, hp3, hp2, hp1]

theorem size_test : size [push0, .op .Eq, .push l, .op .Jumpi] = 6 := by
  simp [Item.size, push0, pushNat, toBytes, EVM.Instr.encode, EVM.Instr.immediate]

/-- the parts of the code of an {lit}`if` -/
theorem ifCode_at
    (hA : At prog p (cc ++ [push0, .op .Eq, .push (q, 0), .op .Jumpi] ++ cb ++ [.label (q, 0)])) :
    At prog p cc ∧
      At prog (p + size cc) ([push0, .op .Eq, .push (q, 0), .op .Jumpi] ++ (cb ++ [.label (q, 0)])) ∧
      At prog (p + size cc + 6) cb ∧ At prog (p + size cc + 6 + size cb) [.label (q, 0)] := by
  have h1 : At prog p (cc ++ ([push0, .op .Eq, .push (q, 0), .op .Jumpi] ++ (cb ++ [.label (q, 0)]))) := by
    simpa using hA
  refine ⟨h1.left, h1.right, ?_, ?_⟩
  · have := (At.left (a := [push0, .op .Eq, .push (q, 0), .op .Jumpi] ++ cb) (by simpa using h1.right)).right
    exact this.shift (by rw [size_test])
  · have := hA.right
    exact this.shift (by simp [EVM.Instr.immediate]; omega)

theorem sim_if_zero (hg : Good prog) (he : eval inp ρ N fs st Γ c 1 hc1 hI = ⟨.ok vs, st1, h1, p1⟩)
    (hz : vs.head hne = 0) (ih : M5 prog inp ρ N fs st Γ c 1 hc1 hI) :
    M1 prog inp ρ N fs st Γ (.If c b) h hI := by
  intro ctx q code vars' hc p hA s0 n rest hp hP
  obtain ⟨cc, cb, hcc, hcb, rfl, rfl⟩ := compileIf hc
  have r := ih ctx (q ++ [0]) 0 cc hcc p (hA.left.left.left) hP.funs hP.names s0 n [] rest rfl hp
    (by simp [hP.stack]) hP.mem hP.reads
  rw [he] at r
  obtain ⟨hl, hv, g⟩ := r
  dsimp only at hv g
  rw [exec, he]
  dsimp only
  obtain ⟨v, rfl⟩ : ∃ v, vs = [v] := by
    match vs, hl with | [v], _ => exact ⟨v, rfl⟩
  simp only [List.head_cons] at hz
  subst hz
  simp only [List.head_cons, ite_true]
  refine ⟨g.bind fun s1 hs1 => ?_, fun _ => by simp [hP.names, hv]⟩
  obtain ⟨-, hAt, -, hL⟩ := ifCode_at hA
  obtain ⟨s2, h2, hs2⟩ := st_test (n := st1.reads) (ρ := ρ) (inp := inp) hg (hAt.at hs1.1) hL
    hs1.2.1
  simp only [ite_true] at hs2
  have hpl : pos prog (q, 0) = p + size cc + 6 + size cb := by simpa using pos_at hg (a := []) hL
  obtain ⟨s3, h3, hp3, hs3, hm3⟩ := st_label (n := st1.reads) (ρ := ρ) (inp := inp)
    (by rw [hs2.1, hpl]; exact hL : At prog s2.pc [.label (q, 0)])
  refine Goes.done ⟨s3, h2.trans h3, hp3, hs3, hm3⟩ ?_ ?_ (by rw [hs2.2.2, hs1.2.2]) rfl
    (by omega)
  · rw [hs2.1, hpl]
    simp [EVM.Instr.immediate]; omega
  · rw [hs2.2.1, hP.stack, hv]; simp

/-- the context at a state with the same names of variables -/
theorem Pre.same (hP : Pre prog ctx fs st s0 n rest) (hv : st1.vars = st.vars)
    (hs : Is s1 pc (vals st.vars ++ rest) st1.mem) : Pre prog ctx fs st1 s1 st1.reads rest where
  funs := hP.funs
  names := by rw [hP.names, hv]
  loop := by rw [hv]; exact hP.loop
  leave := by rw [hv]; exact hP.leave
  stack := by rw [hs.2.1, hv]
  mem := hs.2.2
  reads := rfl

theorem sim_if_ne (hg : Good prog) (he : eval inp ρ N fs st Γ c 1 hc1 hI = ⟨.ok vs, st1, h1, p1⟩)
    (hz : ¬vs.head hne = 0) (ih : M5 prog inp ρ N fs st Γ c 1 hc1 hI)
    (ihb : M3 prog inp ρ N fs st1 Γ b hb hI1) :
    M1 prog inp ρ N fs st Γ (.If c b) h hI := by
  intro ctx q code vars' hc p hA s0 n rest hp hP
  obtain ⟨cc, cb, hcc, hcb, rfl, rfl⟩ := compileIf hc
  obtain ⟨hAc, hAt, hAb, hL⟩ := ifCode_at hA
  have r := ih ctx (q ++ [0]) 0 cc hcc p hAc hP.funs hP.names s0 n [] rest rfl hp
    (by simp [hP.stack]) hP.mem hP.reads
  rw [he] at r
  obtain ⟨hl, hv, g⟩ := r
  dsimp only at hv g
  rw [exec, he]
  dsimp only
  obtain ⟨v, rfl⟩ : ∃ v, vs = [v] := by
    match vs, hl with | [v], _ => exact ⟨v, rfl⟩
  simp only [List.head_cons] at hz
  simp only [List.head_cons, hz, ite_false]
  have hnm : names (execBlock inp ρ N fs st1 Γ b hb hI1).st.vars = names st1.vars := names_execBlock
  refine ⟨StmtPost.pre g fun s1 hs1 => ?_, fun _ => by rw [hnm, hP.names, hv]⟩
  obtain ⟨s2, h2, hs2⟩ := st_test (n := st1.reads) (ρ := ρ) (inp := inp) hg (hAt.at hs1.1) hL
    hs1.2.1
  simp only [hz, ite_false] at hs2
  have hb' := ihb ctx (q ++ [1]) cb hcb (p + size cc + 6) hAb s2 st1.reads rest
    (by rw [hs2.1, hs1.1])
    (hP.same hv ⟨hs2.1, by rw [hs2.2.1, hP.stack]; rfl, hs2.2.2.trans hs1.2.2⟩)
  have := (StmtPost.steps h2 hb').label hL
  exact this.cast_pc (by simp [EVM.Instr.immediate]; omega)

theorem sim_if_err (he : eval inp ρ N fs st Γ c 1 hc1 hI = ⟨v, st1, h1, p1⟩)
    (hv : ∀ vs, v = .ok vs → False) (ih : M5 prog inp ρ N fs st Γ c 1 hc1 hI) :
    M1 prog inp ρ N fs st Γ (.If c b) h hI := by
  intro ctx q code vars' hc p hA s0 n rest hp hP
  obtain ⟨cc, cb, hcc, hcb, rfl, rfl⟩ := compileIf hc
  obtain ⟨hAc, -, -, -⟩ := ifCode_at hA
  have r := ih ctx (q ++ [0]) 0 cc hcc p hAc hP.funs hP.names s0 n [] rest rfl hp
    (by simp [hP.stack]) hP.mem hP.reads
  rw [he] at r
  rw [exec, he]
  cases v with
  | ok vs => exact absurd rfl (hv vs)
  | halt r' => exact ⟨r, fun h => by cases h⟩
  | timeout => exact ⟨r, fun h => by cases h⟩

theorem sim_break (hg : Good prog) : M1 prog inp ρ N fs st Γ .Break h hI := by
  intro ctx q code vars' hc p hA s0 n rest hp hP
  rw [compileStmt] at hc
  split at hc
  · next l lc d hl =>
    cases hc
    rw [exec]
    obtain ⟨-, ⟨pl, hL⟩, -⟩ := hP.loop l lc d hl
    refine ⟨⟨l, lc, d, hl, Goes.done (st_jumpOut (n := n) (ρ := ρ) (inp := inp) hg (hA.at hp) hL
      hP.stack (by rw [hP.names]; simp)) rfl rfl hP.mem hP.reads (by simp)⟩, fun h => by cases h⟩
  · cases hc

theorem sim_continue (hg : Good prog) : M1 prog inp ρ N fs st Γ .Continue h hI := by
  intro ctx q code vars' hc p hA s0 n rest hp hP
  rw [compileStmt] at hc
  split at hc
  · next l lc d hl =>
    cases hc
    rw [exec]
    obtain ⟨-, -, ⟨pl, hL⟩⟩ := hP.loop l lc d hl
    refine ⟨⟨l, lc, d, hl, Goes.done (st_jumpOut (n := n) (ρ := ρ) (inp := inp) hg (hA.at hp) hL
      hP.stack (by rw [hP.names]; simp)) rfl rfl hP.mem hP.reads (by simp)⟩, fun h => by cases h⟩
  · cases hc

theorem sim_leave (hg : Good prog) : M1 prog inp ρ N fs st Γ .Leave h hI := by
  intro ctx q code vars' hc p hA s0 n rest hp hP
  rw [compileStmt] at hc
  split at hc
  · next l d hl =>
    cases hc
    rw [exec]
    obtain ⟨-, ⟨pl, hL⟩⟩ := hP.leave l d hl
    refine ⟨⟨l, d, hl, Goes.done (st_jumpOut (n := n) (ρ := ρ) (inp := inp) hg (hA.at hp) hL
      hP.stack (by rw [hP.names]; simp)) rfl rfl hP.mem hP.reads (by simp)⟩, fun h => by cases h⟩
  · cases hc

/-! ## Blocks and lists of statements -/

theorem compileBlock_ok (h : compileBlock ctx q ⟨ss⟩ = .ok code) :
    ∃ c vars, compileStmts (scope ctx q ss) q 0 ss = .ok (c, vars) ∧
      code = c ++ pops (vars.length - ctx.vars.length) := by
  rw [compileBlock] at h
  inv h
  obtain ⟨⟨c, vars⟩, hc, rfl⟩ := h
  exact ⟨c, vars, hc, rfl⟩

theorem length_le_of_suffix {a b : Vars} (h : names a <:+ names b) : a.length ≤ b.length := by
  have := h.length_le; simpa using this

/-- the values of the variables of a loop or function after the {lit}`restrict` of a block -/
theorem drop_restrict {st st1 : State} (hl : st.vars.length ≤ st1.vars.length)
    (hd : d ≤ st.vars.length) :
    (restrict st st1).vars.drop ((restrict st st1).vars.length - d) =
      st1.vars.drop (st1.vars.length - d) := by
  simp only [restrict, List.drop_drop, List.length_drop]
  congr 1; omega

theorem sim_execBlock
    (he : execs inp ρ N (defs ss :: fs) st { Γ with funs := functions ss ++ Γ.funs } ss hss hI' =
      ⟨o, st1, h1, p1⟩)
    (ih : M4 prog inp ρ N (defs ss :: fs) st { Γ with funs := functions ss ++ Γ.funs } ss hss hI') :
    M3 prog inp ρ N fs st Γ ⟨ss⟩ h hI := by
  intro ctx q code hc p hA s0 n rest hp hP
  obtain ⟨c, vars, hcs, rfl⟩ := compileBlock_ok hc
  have hP' : Pre prog (scope ctx q ss) (defs ss :: fs) st s0 n rest :=
    { funs := funsOK_scope hP.funs hcs hA.left
      names := hP.names
      loop := hP.loop
      leave := hP.leave
      stack := hP.stack
      mem := hP.mem
      reads := hP.reads }
  have r := ih (scope ctx q ss) q 0 c vars hcs p hA.left s0 n rest hp hP'
  have hsuf : names st.vars <:+
      names (execs inp ρ N (defs ss :: fs) st { Γ with funs := functions ss ++ Γ.funs } ss hss hI').st.vars :=
    names_execs
  rw [he] at r hsuf
  obtain ⟨r, hnm⟩ := r
  dsimp only at hsuf
  have hl := length_le_of_suffix hsuf
  rw [execBlock, he]
  dsimp only
  have hloop : (scope ctx q ss).loop = ctx.loop := rfl
  have hleave : (scope ctx q ss).leave = ctx.leave := rfl
  cases o with
  | normal =>
    refine Goes.bind r fun s1 hs1 => ?_
    have hk : vars.length - ctx.vars.length = st1.vars.length - st.vars.length := by
      rw [hnm rfl, hP.names]; simp
    obtain ⟨s2, h2, hp2, hs2, hm2⟩ := st_pops (n := st1.reads) (ρ := ρ) (inp := inp) (c := [])
      (by rw [hs1.1]; simpa using hA.right)
      (l := (vals st1.vars).take (st1.vars.length - st.vars.length))
      (st := (vals st1.vars).drop (st1.vars.length - st.vars.length) ++ rest)
      (by rw [hs1.2.1, ← List.append_assoc, List.take_append_drop]) (by simp [hk])
    refine Goes.done ⟨s2, h2, hp2, hs2, hm2⟩
      (by rw [hs1.1, hk]; simp [pops, EVM.Instr.immediate, Nat.add_assoc]) ?_ hs1.2.2 rfl
      (by simp [restrict])
    simp [restrict, List.map_drop]
  | brk =>
    obtain ⟨l, lc, d, hld, g⟩ := r
    have hd := (hP.loop l lc d (hloop ▸ hld)).1
    exact ⟨l, lc, d, hloop ▸ hld, g.cast rfl (by rw [drop_restrict hl hd])⟩
  | cont =>
    obtain ⟨l, lc, d, hld, g⟩ := r
    have hd := (hP.loop l lc d (hloop ▸ hld)).1
    exact ⟨l, lc, d, hloop ▸ hld, g.cast rfl (by rw [drop_restrict hl hd])⟩
  | leave =>
    obtain ⟨l, d, hld, g⟩ := r
    have hd := (hP.leave l d (hleave ▸ hld)).1
    exact ⟨l, d, hleave ▸ hld, g.cast rfl (by rw [drop_restrict hl hd])⟩
  | halt r' => exact r
  | timeout => exact r

theorem sim_execs_nil : M4 prog inp ρ N fs st Γ [] h hI := by
  intro ctx q j code vars' hc p hA s0 n rest hp hP
  rw [compileStmts] at hc
  cases hc
  rw [execs]
  exact ⟨Goes.refl ⟨by simp [hp], hP.stack, hP.mem⟩ hP.reads (Nat.le_refl _),
    fun _ => hP.names⟩

theorem sim_execs_cons (he : exec inp ρ N fs st Γ s hs hI = ⟨o, st2, h2, p2⟩)
    (ho : o = .normal) (ih1 : M1 prog inp ρ N fs st Γ s hs hI)
    (ih2 : M4 prog inp ρ N fs st2 (Scope.after Γ s) ss hss hI2) :
    M4 prog inp ρ N fs st Γ (s :: ss) h hI := by
  subst ho
  intro ctx q j code vars' hc p hA s0 n rest hp hP
  obtain ⟨c, vars, cs, h1, h2', rfl⟩ := compileStmts_cons hc
  have r1 := ih1 ctx (q ++ [j]) c vars h1 p hA.left s0 n rest hp hP
  have hsuf : names st.vars <:+ names (exec inp ρ N fs st Γ s hs hI).st.vars := names_exec
  rw [he] at r1 hsuf
  obtain ⟨g, hn⟩ := r1
  dsimp only at hsuf g
  have hl := length_le_of_suffix hsuf
  have hP2 : ∀ s1, Is s1 (p + size c) (vals st2.vars ++ rest) st2.mem →
      Pre prog { ctx with vars } fs st2 s1 st2.reads rest := fun s1 hs1 =>
    { funs := hP.funs
      names := hn rfl
      loop := fun l lc d h => by
        obtain ⟨hd, h'⟩ := hP.loop l lc d h; exact ⟨by omega, h'⟩
      leave := fun l d h => by
        obtain ⟨hd, h'⟩ := hP.leave l d h; exact ⟨by omega, h'⟩
      stack := hs1.2.1
      mem := hs1.2.2
      reads := rfl }
  have r2 := fun s1 hs1 => ih2 { ctx with vars } q (j + 1) cs vars' h2' (p + size c) hA.right s1
    st2.reads rest hs1.1 (hP2 s1 hs1)
  rw [execs, he]
  dsimp only
  rw [dite_eq_left rfl]
  obtain ⟨_, s1, -, hs1, -⟩ := id g
  refine ⟨StmtPost.pre g fun s1 hs1 => (r2 s1 hs1).1.cast_pc (by simp [Nat.add_assoc]),
    fun h => ?_⟩
  exact (r2 s1 hs1).2 h

theorem sim_execs_stop (he : exec inp ρ N fs st Γ s hs hI = ⟨o, st2, h2, p2⟩)
    (ho : ¬o = .normal) (ih1 : M1 prog inp ρ N fs st Γ s hs hI) :
    M4 prog inp ρ N fs st Γ (s :: ss) h hI := by
  intro ctx q j code vars' hc p hA s0 n rest hp hP
  obtain ⟨c, vars, cs, h1, h2', rfl⟩ := compileStmts_cons hc
  have r1 := ih1 ctx (q ++ [j]) c vars h1 p hA.left s0 n rest hp hP
  rw [he] at r1
  rw [execs, he]
  dsimp only
  rw [dite_eq_right ho]
  exact ⟨r1.1.anyPc ho, fun h => absurd h ho⟩

end Compiler
