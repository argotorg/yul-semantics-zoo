import YulSemnaticsZoo.Yul.Syntax.EVM
import YulSemnaticsZoo.Yul.Syntax.WellFormed
import YulSemnaticsZoo.Semantics

set_option doc.verso true

/-!
# Yul: a clocked semantics

Reference: [the formal specification of Yul](https://docs.soliditylang.org/en/v0.8.38/yul.html#formal-specification)

A big-step interpreter for Yul in the EVM dialect ({lit}`Yul.EVM.dialect`). It is a total
function. The clock is part of the state. It decreases by 1 at each loop iteration (before the
condition) and at each call of a Yul function. When the clock is 0 at one of these points, the
outcome is {lit}`timeout`. Nothing else uses the clock.

The semantics defines 8 builtins: {lit}`add`, {lit}`lt`, {lit}`eq`, {lit}`calldataload`,
{lit}`mload`, {lit}`mstore`, {lit}`gas` and {lit}`return`. A call of each other builtin of the
dialect halts the run with {lit}`unsupported`, as the EVM semantics does for an instruction that it
does not define. The halt comes after the arguments, as for the 8 builtins: the arguments can read
gas, halt or time out before it.

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

## ASTs that are not well-formed

The semantics is total, and for an AST that is not well-formed it does the simplest thing:
* An unbound variable gives 0. An assignment to an unbound variable has no effect.
* A call of a name that is not a builtin and not a function in scope gives no values. A builtin
  name is always the builtin.
* A call of a builtin outside the 8 halts the run with {lit}`unsupported`, also if its literal
  arguments are not valid. (Only builtins outside the 8 have literal arguments.)
* A missing value (an argument, or a value for a variable) is 0. An extra value has no effect.
* A literal number is taken modulo 2^256, and a literal string has its first 32 bytes.
* {lit}`break`, {lit}`continue` and {lit}`leave` stop the statements of each block until a loop or a
  function call takes them. A function call takes each of them as {lit}`leave`. A loop body takes
  {lit}`break` and {lit}`continue`, the post block takes them as normal, and the loop iteration
  continues. A loop does not take them from its init block: the loop stops with that outcome. At
  the end of the code, each of them is the end of the run.
* A function in the init block of a loop is in scope in all of the loop.
-/

namespace Yul.Clocked
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

/-- the value of {name}`x`, or 0 -/
def Vars.get (vs : Vars) (x : Identifier) : Word := (vs.lookup x).getD 0

/-- the variables with a new value for the first variable with a name -/
def Vars.set : Vars → Identifier → Word → Vars
  | [], _, _ => []
  | (y, w) :: vs, x, v => if y = x then (y, v) :: vs else (y, w) :: Vars.set vs x v

/-- the variables after an assignment of values to variables in order -/
def Vars.assign (vars : Vars) : List Identifier → List Word → Vars
  | [], _ => vars
  | x :: xs, vs => Vars.assign (Vars.set vars x (vs.headD 0)) xs vs.tail

/-- new variables {name}`xs` with the values {name}`vs` in order -/
def bind (xs : List Identifier) (vs : List Word) : Vars := xs.mapIdx fun k x => (x, vs.getD k 0)

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

/-- the value of a literal; a string is left-aligned, as in solc -/
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

/-- a result and the state after it, with a clock that is not more than {name}`c` -/
structure Res (c : Nat) (α : Type) where
  val : α
  st : State
  le : st.clock ≤ c

def Res.up (h : c ≤ c') (r : Res c α) : Res c' α := ⟨r.val, r.st, Nat.le_trans r.le h⟩

/-- the measure of the recursion decreases: the clock decreases, or the clock does not increase and
the AST is smaller -/
theorem lex_lt {a a' b b' : Nat} (h : a' < a ∨ a' ≤ a ∧ b' < b) :
    Prod.Lex (· < ·) (· < ·) (a', b') (a, b) := by
  rcases h with h | ⟨h, hb⟩
  · exact .left _ _ h
  · rcases Nat.lt_or_eq_of_le h with h | rfl
    · exact .left _ _ h
    · exact .right _ hb

/-- the proof that the measure decreases at a recursive call -/
macro "decreasing_clock" : tactic =>
  `(tactic| ((try apply lex_lt) <;> simp_all <;> omega))

section

variable (i : Input) (ρ : Readings)

/-- a builtin with the arguments {name}`args`, or {name}`none` for literal arguments that the
dialect does not accept. Each builtin outside the 8 halts with {name}`Result.unsupported`. -/
def builtin (b : Option EVM.Builtin) (args : List Word) (st : State) : Res st.clock Values :=
  let x := args.getD 0 0
  let y := args.getD 1 0
  match b with
  | some .Add => ⟨.ok [x + y], st, Nat.le_refl _⟩
  | some .Lt => ⟨.ok [lt x y], st, Nat.le_refl _⟩
  | some .Eq => ⟨.ok [eq x y], st, Nat.le_refl _⟩
  | some .Calldataload => ⟨.ok [calldataload i x], st, Nat.le_refl _⟩
  | some .Mload => ⟨.ok [mload st.mem x], st, Nat.le_refl _⟩
  | some .Mstore => ⟨.ok [], { st with mem := mstore st.mem x y }, Nat.le_refl _⟩
  | some .Gas => ⟨.ok [ρ st.reads], { st with reads := st.reads + 1 }, Nat.le_refl _⟩
  | some .Return => ⟨.halt (.ret (read st.mem x y)), st, Nat.le_refl _⟩
  | _ => ⟨.halt .unsupported, st, Nat.le_refl _⟩

mutual

/-- a statement -/
def exec (fs : Funs) (st : State) : Statement → Res st.clock Outcome
  | .Block b => execBlock fs st b
  | .FunctionDefinition .. => ⟨.normal, st, Nat.le_refl _⟩
  | .VariableDeclaration xs none =>
    ⟨.normal, { st with vars := bind xs [] ++ st.vars }, Nat.le_refl _⟩
  | .VariableDeclaration xs (some e) =>
    let ⟨v, st1, h1⟩ := eval fs st e
    match v with
    | .ok vs => ⟨.normal, { st1 with vars := bind xs vs ++ st1.vars }, h1⟩
    | v => ⟨v.outcome, st1, h1⟩
  | .Assignment xs e =>
    let ⟨v, st1, h1⟩ := eval fs st e
    match v with
    | .ok vs => ⟨.normal, { st1 with vars := st1.vars.assign xs vs }, h1⟩
    | v => ⟨v.outcome, st1, h1⟩
  | .If c b =>
    let ⟨v, st1, h1⟩ := eval fs st c
    match v with
    | .ok vs => if vs.headD 0 = 0 then ⟨.normal, st1, h1⟩ else (execBlock fs st1 b).up h1
    | v => ⟨v.outcome, st1, h1⟩
  | .Expression e =>
    let ⟨v, st1, h1⟩ := eval fs st e
    ⟨v.outcome, st1, h1⟩
  -- the init block is in the scope of the loop
  | .ForLoop ⟨init⟩ c post body =>
    let ⟨o, st1, h1⟩ := execs (defs init :: fs) st init
    match o with
    | .normal =>
      let ⟨o, st2, h2⟩ := loop (defs init :: fs) st1 c post body
      ⟨o, restrict st st2, Nat.le_trans h2 h1⟩
    | o => ⟨o, restrict st st1, h1⟩
  | .Break => ⟨.brk, st, Nat.le_refl _⟩
  | .Continue => ⟨.cont, st, Nat.le_refl _⟩
  | .Leave => ⟨.leave, st, Nat.le_refl _⟩
termination_by s => (st.clock, sizeOf s)
decreasing_by all_goals decreasing_clock

/-- a block: its functions are in scope in all of it, and its variables only in it -/
def execBlock (fs : Funs) (st : State) : Block → Res st.clock Outcome
  | ⟨ss⟩ =>
    let ⟨o, st1, h1⟩ := execs (defs ss :: fs) st ss
    ⟨o, restrict st st1, h1⟩
termination_by b => (st.clock, sizeOf b)
decreasing_by all_goals decreasing_clock

/-- statements in order, until one has an outcome that is not normal -/
def execs (fs : Funs) (st : State) : List Statement → Res st.clock Outcome
  | [] => ⟨.normal, st, Nat.le_refl _⟩
  | s :: ss =>
    let ⟨o, st1, h1⟩ := exec fs st s
    match o with
    | .normal => (execs fs st1 ss).up h1
    | o => ⟨o, st1, h1⟩
termination_by ss => (st.clock, sizeOf ss)
decreasing_by all_goals decreasing_clock

/-- the iterations of a loop -/
def loop (fs : Funs) (st : State) (c : Expression) (post body : Block) : Res st.clock Outcome :=
  if _h0 : st.clock = 0 then ⟨.timeout, st, Nat.le_refl _⟩ else
  let ⟨v, st1, h1⟩ := eval fs { st with clock := st.clock - 1 } c
  have hc : st1.clock ≤ st.clock := Nat.le_trans h1 (Nat.sub_le _ _)
  match v with
  | .ok vs =>
    if vs.headD 0 = 0 then ⟨.normal, st1, hc⟩ else
    let ⟨o, st2, h2⟩ := execBlock fs st1 body
    match o with
    | .brk => ⟨.normal, st2, Nat.le_trans h2 hc⟩
    | .normal | .cont =>
      let ⟨o, st3, h3⟩ := execBlock fs st2 post
      match o with
      | .normal | .brk | .cont => (loop fs st3 c post body).up (Nat.le_trans h3 (Nat.le_trans h2 hc))
      | o => ⟨o, st3, Nat.le_trans h3 (Nat.le_trans h2 hc)⟩
    | o => ⟨o, st2, Nat.le_trans h2 hc⟩
  | v => ⟨v.outcome, st1, hc⟩
termination_by (st.clock, 0)
decreasing_by all_goals decreasing_clock

/-- an expression -/
def eval (fs : Funs) (st : State) : Expression → Res st.clock Values
  | .Literal l => ⟨.ok [literalValue l], st, Nat.le_refl _⟩
  | .Identifier x => ⟨.ok [st.vars.get x], st, Nat.le_refl _⟩
  | .FunctionCall f args =>
    let ⟨v, st1, h1⟩ := evals fs st args
    match v with
    | .ok vs =>
      match EVM.dialect.builtin f, fs.find? f with
      | some (kinds, mk), _ => (builtin i ρ (mk (literalArgs kinds args)) vs st1).up h1
      | none, none => ⟨.ok [], st1, h1⟩
      | none, some (fn, fs') =>
        if _h0 : st1.clock = 0 then ⟨.timeout, st1, h1⟩ else
        let callee : State :=
          { st1 with vars := bind fn.params vs ++ bind fn.rets [], clock := st1.clock - 1 }
        let ⟨o, st2, h2⟩ := execBlock fs' callee fn.body
        have h : st2.clock ≤ st.clock := Nat.le_trans h2 (Nat.le_trans (Nat.sub_le _ _) h1)
        match o with
        | .halt r => ⟨.halt r, { st2 with vars := st1.vars }, h⟩
        | .timeout => ⟨.timeout, { st2 with vars := st1.vars }, h⟩
        | _ => ⟨.ok (fn.rets.map st2.vars.get), { st2 with vars := st1.vars }, h⟩
    | v => ⟨v, st1, h1⟩
termination_by e => (st.clock, sizeOf e)
decreasing_by all_goals decreasing_clock

/-- arguments, from the last to the first, as in Yul; each gives one value -/
def evals (fs : Funs) (st : State) : List Expression → Res st.clock Values
  | [] => ⟨.ok [], st, Nat.le_refl _⟩
  | e :: es =>
    let ⟨v, st1, h1⟩ := evals fs st es
    match v with
    | .ok vs =>
      let ⟨v, st2, h2⟩ := eval fs st1 e
      match v with
      | .ok v => ⟨.ok (v.headD 0 :: vs), st2, Nat.le_trans h2 h1⟩
      | v => ⟨v, st2, Nat.le_trans h2 h1⟩
    | v => ⟨v, st1, h1⟩
termination_by es => (st.clock, sizeOf es)
decreasing_by all_goals decreasing_clock

end

end

/-- the outcome and the state at the end of the code of {name}`P` with clock {name}`k` -/
def top (P : Object) (i : Input) (ρ : Readings) (k : Nat) : Outcome × State :=
  let r := execBlock i ρ [] (start k) P.code
  (r.val, r.st)

/-- the result of a run with this outcome at the end of the code, or {name}`none` at a timeout.
The end of the code is a halt with no data. -/
def Outcome.result : Outcome → Option Result
  | .halt r => some r
  | .timeout => none
  | .normal | .brk | .cont | .leave => some (.ret [])

/-- the result of the code of {name}`P` with clock {name}`k`, or {name}`none` at a timeout -/
def run (P : Object) (i : Input) (ρ : Readings) (k : Nat) : Option Result := (top P i ρ k).1.result

/-! ## Behaviours

As in the clocked interpreter row of the table in {lit}`doc/gas-equivalence.md`: a run ends with
{lit}`r` if some clock gives {lit}`r`, and it diverges if each clock gives a timeout.
-/

/-- {lit}`⟪P, i, ρ⟫ ⇝ b`: the run of the code of {name}`P` with input {name}`i` and readings
{name}`ρ` has the behaviour {lit}`b` -/
def Behaves (P : Object) (i : Input) (ρ : Readings) : Beh → Prop
  | .ends r => ∃ k, run P i ρ k = some r
  | .diverges => ∀ k, run P i ρ k = none

@[inherit_doc] scoped notation:50 "⟪" P ", " i ", " ρ "⟫" " ⇝ " b:50 => Behaves P i ρ b

open Classical in
/-- the behaviour of the run: the result of a clock that gives one, else divergence.
The theorem {lit}`beh_eq` shows that it is the only behaviour. -/
noncomputable def beh (P : Object) (i : Input) (ρ : Readings) : Beh :=
  if h : ∃ r k, run P i ρ k = some r then .ends h.choose else .diverges

end Yul.Clocked
