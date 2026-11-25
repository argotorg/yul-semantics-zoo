import YulSemnaticsZoo.EVM.Syntax
import YulSemnaticsZoo.Semantics

set_option doc.verso true

/-!
# EVM: semantics

A clocked interpreter. One step function {lit}`step` executes one instruction. It has a gas model
as a parameter: the gas model charges the cost of each instruction, gives the value that
{lit}`GAS` pushes, and has the stack limit. {lit}`run` repeats {lit}`step`, and its clock
decreases by 1 at each instruction.

There are two gas models:

- The abstract model (this module) has no gas counter and no stack limit. The n-th {lit}`GAS`
  pushes {lit}`ρ n`. It has no resource failure. The relation {lit}`⟪code, i, ρ⟫ ⇝ b` of
  {lit}`doc/gas-equivalence.md` uses it.
- The concrete model ({lit}`EVM.Gas`) has a gas counter, the real gas costs and the stack limit
  of 1024 words. Out of gas and a stack overflow are resource failures.
-/

namespace EVM
open Semantics

/-- the state of a run, without the gas -/
structure State where
  pc : Nat
  /-- the stack; the top is the first item -/
  stack : List Word
  mem : Memory
  /-- the size of the memory in words of 32 bytes; only the gas cost uses it -/
  words : Nat

/-- the state at the start of a run -/
def State.init : State := ⟨0, [], Memory.empty, 0⟩

/-- the resources of a run: it charges each instruction, gives the value that {lit}`GAS` pushes,
and limits the stack -/
structure GasModel (S : Type) where
  /-- the gas state after the cost of the instruction in the state, or {name}`none` if the gas
  is not sufficient. The state is the state before the memory expansion of the instruction. -/
  charge : Instr → State → S → Option S
  /-- the value that {lit}`GAS` pushes, and the gas state after it -/
  gas : S → Word × S
  /-- the largest number of words on the stack, or {name}`none` for no limit -/
  stackLimit : Option Nat

/-- a resource failure: the run needs more gas or more stack than the model has. The real EVM
takes it as an exceptional halt that uses all the gas. -/
inductive Failure where
  | outOfGas
  | stackOverflow
  deriving DecidableEq, Repr

/-- the result of one step -/
inductive Step (S : Type) where
  | next (s : State) (g : S)
  | halt (r : Result) (g : S)
  /-- a resource failure -/
  | fail (f : Failure)

/-- the positions of the {lit}`JUMPDEST`s of {name}`code`. A byte in the data of a push is not a
{lit}`JUMPDEST`. -/
def jumpdests (code : List UInt8) : List Nat := go 0 code
where
  go (pc : Nat) : List UInt8 → List Nat
    | [] => []
    | b :: rest =>
      -- the number of data bytes of a push
      let n := if 0x60 ≤ b.toNat ∧ b.toNat < 0x80 then b.toNat - 0x5f else 0
      (if b = 0x5b then [pc] else []) ++ go (pc + 1 + n) (rest.drop n)
  termination_by l => l.length
  decreasing_by simp; omega

namespace Instr

/-- the number of words that the instruction takes from the stack, and the number that it puts
on the stack -/
def arity : Instr → Nat × Nat
  | Stop | Jumpdest => (0, 0)
  | Add | Lt | Eq => (2, 1)
  | Calldataload | Mload => (1, 1)
  | Pop | Jump => (1, 0)
  | Mstore | Jumpi | Return => (2, 0)
  | Gas | Push _ _ => (0, 1)
  | Dup n _ => (n, n + 1)
  | Swap n _ => (n + 1, n + 1)
  | Codecopy => (3, 0)
  | Extcodecopy => (4, 0)
  | Create => (3, 1)
  | Call => (7, 1)

/-- the instructions that the semantics do not define -/
def unsupported : Instr → Bool
  | Codecopy | Extcodecopy | Create | Call => true
  | _ => false

/-- the size in words that the memory must have for the instruction, or 0 -/
def memWords : Instr → List Word → Nat
  | Mload, off :: _ | Mstore, off :: _ => (off.toNat + 32 + 31) / 32
  | Return, off :: size :: _ => if size = 0 then 0 else (off.toNat + size.toNat + 31) / 32
  | _, _ => 0

end Instr

/-- The opcodes of the real EVM: the bytes that {lit}`evm run` of geth 1.17.10 does not reject
with an {lit}`invalid opcode` error. {lit}`0xfe` ({lit}`INVALID`) is not in the set. {lit}`lake
test` checks the set against geth for each byte. -/
def defined (b : UInt8) : Bool :=
  let n := b.toNat
  n ≤ 0x0b || (0x10 ≤ n && n ≤ 0x1e) || n == 0x20 || (0x30 ≤ n && n ≤ 0x4b) ||
    (0x50 ≤ n && n ≤ 0xa4) || (0xe6 ≤ n && n ≤ 0xe8) || (0xf0 ≤ n && n ≤ 0xf5) ||
    n == 0xfa || n == 0xfd || n == 0xff

/-- The instruction at {name}`pc`, or the result of a halt there: {name}`Result.unsupported` for
an opcode of the real EVM that the semantics do not define, and {name}`Result.exception` for a
byte that is not an opcode of the real EVM. After the end of the code, the instruction is
{lit}`STOP`. -/
def fetch (code : List UInt8) (pc : Nat) : Except Result Instr :=
  match code.drop pc with
  | [] => .ok .Stop
  | b :: rest =>
    match decode b rest with
    | some (i, _) => if i.unsupported then .error .unsupported else .ok i
    | none => .error (if defined b then .unsupported else .exception)

/-- the effect of an instruction -/
inductive Exec where
  | next (s : State)
  | halt (r : Result)
  /-- {lit}`GAS`: the next state for the value that it pushes -/
  | gas (k : Word → State)

/-- a jump to {name}`dest` -/
def jump (code : List UInt8) (dest : Word) (s : State) : Exec :=
  if dest.toNat ∈ jumpdests code then .next { s with pc := dest.toNat } else .halt .exception

/-- the effect of the instruction {name}`i` in the state {name}`s`, without gas. The size of the
memory is already expanded. -/
def exec (code : List UInt8) (input : Input) (i : Instr) (s : State) : Exec :=
  let pc := s.pc + 1 + i.immediate.length
  let next (stack : List Word) : Exec := .next { s with pc := pc, stack := stack }
  match i, s.stack with
  | .Stop, _ => .halt (.ret [])
  | .Add, a :: b :: st => next ((a + b) :: st)
  | .Lt, a :: b :: st => next (lt a b :: st)
  | .Eq, a :: b :: st => next (eq a b :: st)
  | .Calldataload, a :: st => next (calldataload input a :: st)
  | .Pop, _ :: st => next st
  | .Mload, a :: st => next (mload s.mem a :: st)
  | .Mstore, a :: v :: st => .next { s with pc := pc, stack := st, mem := mstore s.mem a v }
  | .Jump, d :: st => jump code d { s with stack := st }
  | .Jumpi, d :: c :: st => if c = 0 then next st else jump code d { s with stack := st }
  | .Gas, st => .gas fun v => { s with pc := pc, stack := v :: st }
  | .Jumpdest, st => next st
  | .Push _ imm, st => next (ofBytes imm.toList :: st)
  | .Dup n _, st =>
    match st[n - 1]? with
    | some v => next (v :: st)
    | none => .halt .exception
  | .Swap n _, a :: st =>
    match st[n - 1]? with
    | some b => next (b :: st.set (n - 1) a)
    | none => .halt .exception
  | .Return, off :: size :: _ => .halt (.ret (read s.mem off size))
  | .Codecopy, _ | .Extcodecopy, _ | .Create, _ | .Call, _ => .halt .unsupported
  -- a stack underflow; `step` finds it before `exec`
  | _, _ => .halt .exception

/-- One instruction: the instruction at the {lit}`pc` (or a halt for an unsupported or undefined
opcode), then the stack checks (underflow, then the stack limit of the model), then the gas, then
the effect. This is the order of geth: a stack error comes before out of gas, and a bad jump after
it. -/
def step (m : GasModel S) (code : List UInt8) (input : Input) (s : State) (g : S) : Step S :=
  match fetch code s.pc with
  | .error r => .halt r g
  | .ok i =>
    if s.stack.length < i.arity.1 then .halt .exception g
    else if m.stackLimit.any (· < s.stack.length - i.arity.1 + i.arity.2) then
      .fail .stackOverflow
    else
      match m.charge i s g with
      | none => .fail .outOfGas
      | some g =>
        match exec code input i { s with words := max s.words (i.memWords s.stack) } with
        | .next s => .next s g
        | .halt r => .halt r g
        | .gas k => let (v, g) := m.gas g; .next (k v) g

/-- the result of a run -/
inductive Outcome (S : Type) where
  /-- a halt, with the gas state at the halt -/
  | halt (r : Result) (g : S)
  /-- a resource failure, with the gas state before the instruction that fails -/
  | fail (f : Failure) (g : S)
  /-- the clock is 0 -/
  | timeout
  deriving DecidableEq, Repr

/-- {name}`step` until a halt, a resource failure, or the end of the clock {lit}`k`: each instruction
uses 1 of the clock -/
def run (m : GasModel S) (code : List UInt8) (input : Input) : Nat → State → S → Outcome S
  | 0, _, _ => .timeout
  | k + 1, s, g =>
    match step m code input s g with
    | .next s g => run m code input k s g
    | .halt r g => .halt r g
    | .fail f => .fail f g

/-- (Mono): if the clock {name}`k` gives an outcome that is not a timeout, then each larger clock
gives the same outcome -/
theorem run_mono {m : GasModel S} {k k' : Nat} {s : State} {g : S}
    (h : run m code input k s g ≠ .timeout) (hk : k ≤ k') :
    run m code input k' s g = run m code input k s g := by
  induction k generalizing k' s g with
  | zero => simp [run] at h
  | succ k ih =>
    obtain ⟨k', rfl⟩ : ∃ j, k' = j + 1 := ⟨k' - 1, by omega⟩
    simp only [run] at h ⊢
    split
    · next hs => rw [hs] at h; exact ih h (by omega)
    · rfl
    · rfl

/-- The abstract gas model: the gas state is the number of reads. Each charge succeeds, the n-th
{lit}`GAS` pushes {lit}`ρ n`, and the stack has no limit. -/
def abstract (ρ : Readings) : GasModel Nat where
  charge _ _ n := some n
  gas n := (ρ n, n + 1)
  stackLimit := none

/-- the abstract run of {name}`code` with input {name}`i`, readings {name}`ρ` and clock
{name}`k` -/
def runA (code : List UInt8) (i : Input) (ρ : Readings) (k : Nat) : Outcome Nat :=
  run (abstract ρ) code i k .init 0

/-- {lit}`⟪code, i, ρ⟫ ⇝ b`: the abstract run has the behaviour {lit}`b`. It ends with {lit}`r` if
a clock gives {lit}`r`, and it diverges if each clock gives a timeout. -/
def Runs (code : List UInt8) (i : Input) (ρ : Readings) : Beh → Prop
  | .ends r => ∃ k n, runA code i ρ k = .halt r n
  | .diverges => ∀ k, runA code i ρ k = .timeout

@[inherit_doc] scoped notation:50 "⟪" c ", " i ", " ρ "⟫" " ⇝ " b:50 => Runs c i ρ b

/-- an abstract step has no resource failure: each charge succeeds, and the stack has no limit -/
theorem step_abstract_ne_fail : step (abstract ρ) code i s n ≠ .fail f := by
  simp only [step, abstract, Option.any, Bool.false_eq_true, ite_false]
  split
  · simp
  · split
    · simp
    · cases exec code i _ _ <;> simp

/-- the abstract model has no resource failure -/
theorem run_abstract_ne_fail : run (abstract ρ) code i k s n ≠ .fail f n' := by
  induction k generalizing s n with
  | zero => simp [run]
  | succ k ih =>
    simp only [run]
    split
    · exact ih
    · simp
    · next hs => exact absurd hs step_abstract_ne_fail

/-- (Det): a run has at most one behaviour -/
theorem Runs.det (h : ⟪code, i, ρ⟫ ⇝ b) (h' : ⟪code, i, ρ⟫ ⇝ b') : b = b' := by
  cases b <;> cases b' <;> simp only [Runs] at h h'
  · obtain ⟨k, n, hk⟩ := h
    obtain ⟨k', n', hk'⟩ := h'
    have ne {k r n} (e : runA code i ρ k = .halt r n) : runA code i ρ k ≠ .timeout := by simp [e]
    have a := (run_mono (ne hk) (Nat.le_max_left k k')).trans hk
    have b := (run_mono (ne hk') (Nat.le_max_right k k')).trans hk'
    rw [a] at b
    simp at b
    rw [b.1]
  · obtain ⟨k, n, hk⟩ := h; simp [h' k] at hk
  · obtain ⟨k, n, hk⟩ := h'; simp [h k] at hk
  · rfl

/-- (Total): a run has a behaviour -/
theorem Runs.total : ∃ b, ⟪code, i, ρ⟫ ⇝ b := by
  by_cases h : ∀ k, runA code i ρ k = .timeout
  · exact ⟨.diverges, h⟩
  · obtain ⟨k, hk⟩ := Classical.not_forall.mp h
    cases e : runA code i ρ k with
    | halt r n => exact ⟨.ends r, k, n, e⟩
    | fail f n => exact absurd e run_abstract_ne_fail
    | timeout => exact absurd e hk

end EVM
