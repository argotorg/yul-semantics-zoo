import YulSemnaticsZoo.EVM.Semantics

set_option doc.verso true

/-!
# EVM: concrete gas

The concrete gas model: a gas counter with the real gas costs. The costs are the costs of
{lit}`evm run` of geth 1.17.10 with its default chain configuration (all forks to Osaka, and the
next fork, that has {lit}`DUPN`, {lit}`SWAPN` and {lit}`EXCHANGE`). {lit}`lake test` fuzzes them
against geth. The memory of {lit}`w` words costs {lit}`3 * w + w * w / 512`, and an instruction
that expands the memory pays the difference.

{lit}`GAS` pushes the remaining gas after the cost of {lit}`GAS`. Each instruction that does not
halt costs at least 1 gas, thus the concrete run with gas {lit}`g` ends before the clock
{lit}`g + 1` ends ({lit}`runC_ne_timeout`).

The gas counter is a natural number without a limit. geth has a limit of {lit}`2 ^ 64 - 1` and
it halts with an error if a memory size is larger than {lit}`0x1FFFFFFFE0` bytes. That memory
costs more than {lit}`2 ^ 55` gas, thus for a start gas less than {lit}`2 ^ 55` the two agree.
-/

namespace EVM
open Semantics

namespace Instr

/-- the gas cost of the instruction without the memory expansion. An unsupported instruction
halts before its charge, thus its cost here is 0. -/
def baseCost : Instr → Nat
  | Stop | Return => 0
  | Jumpdest => 1
  | Pop | Gas | Push 0 _ => 2
  | Add | Lt | Eq | Calldataload | Mload | Mstore | Push _ _ | Dup _ _ | Swap _ _ => 3
  | Jump => 8
  | Jumpi => 10
  | Codecopy | Extcodecopy | Create | Call => 0

end Instr

/-- the cost of a memory of {name}`w` words -/
def memCost (w : Nat) : Nat := 3 * w + w * w / 512

/-- the gas cost of the instruction {name}`i` in the state {name}`s`: the base cost, and the cost
of the memory expansion -/
def cost (i : Instr) (s : State) : Nat :=
  i.baseCost + (memCost (max s.words (i.memWords s.stack)) - memCost s.words)

/-- the gas state of the concrete model -/
structure Meter where
  /-- the remaining gas -/
  gas : Nat
  /-- the values that the {lit}`GAS` instructions pushed, the first read first -/
  reads : List Word
  deriving DecidableEq, Repr

/-- the concrete gas model: the remaining gas, and a record of the reads -/
def concrete : GasModel Meter where
  charge i s m := if cost i s ≤ m.gas then some { m with gas := m.gas - cost i s } else none
  gas m :=
    let v := BitVec.ofNat 256 m.gas
    (v, { m with reads := m.reads ++ [v] })

/-- the concrete run of {name}`code` with input {name}`i` and gas {name}`g` -/
def runC (code : List UInt8) (i : Input) (g : Nat) : Outcome Meter :=
  run concrete code i (g + 1) .init ⟨g, []⟩

/-- the result of the concrete run, or {name}`none` if it goes out of gas -/
def result_C (code : List UInt8) (i : Input) (g : Nat) : Option Result :=
  match runC code i g with
  | .halt r _ => some r
  | _ => none

/-- the readings of the concrete run: the value of the n-th {lit}`GAS`, or 0 after the last
read -/
def reads (code : List UInt8) (i : Input) (g : Nat) : Readings :=
  let l := match runC code i g with
    | .halt _ m | .oog m => m.reads
    | .timeout => []
  fun n => l.getD n 0

/-- only {lit}`STOP`, {lit}`RETURN` and the unsupported instructions have a base cost of 0 -/
theorem Instr.one_le_baseCost {i : Instr} (h : i.unsupported = false) (hs : i ≠ .Stop)
    (hr : i ≠ .Return) : 1 ≤ i.baseCost := by
  cases i <;> simp_all [baseCost, unsupported]
  next n _ => match n with | 0 => simp | ⟨n + 1, _⟩ => simp

/-- {lit}`STOP` and {lit}`RETURN` halt -/
theorem exec_stop_return (h : i = .Stop ∨ i = .Return) : ∃ r, exec code input i s = .halt r := by
  rcases h with rfl | rfl
  · exact ⟨_, rfl⟩
  · rcases hs : s.stack with _ | ⟨a, _ | ⟨b, st⟩⟩ <;> simp [exec, hs]

/-- an instruction that {name}`fetch` gives is not unsupported -/
theorem fetch_supported (h : fetch code pc = .ok i) : i.unsupported = false := by
  unfold fetch at h
  split at h
  · cases h; rfl
  · split at h
    · split at h
      · cases h
      · next hn => cases h; simpa using hn
    · cases h

/-- a concrete step that does not halt uses at least 1 gas -/
theorem step_concrete_gas (h : step concrete code input s m = .next s' m') : m'.gas < m.gas := by
  simp only [step] at h
  split at h
  · simp at h
  · next i hf =>
    have hu := fetch_supported hf
    · split at h
      · simp at h
      · simp only [concrete] at h
        split at h
        · simp at h
        · next m₁ hc =>
          split at hc
          · next hle =>
            simp only [Option.some.injEq] at hc
            subst hc
            have hb : 1 ≤ cost i s := by
              by_cases hsr : i = .Stop ∨ i = .Return
              · obtain ⟨r, hr⟩ := exec_stop_return (code := code) (input := input)
                  (s := { s with words := max s.words (i.memWords s.stack) }) hsr
                rw [hr] at h
                simp at h
              · simp only [not_or] at hsr
                have := Instr.one_le_baseCost (by simpa using hu) hsr.1 hsr.2
                simp only [cost]; omega
            split at h <;> simp at h <;> obtain ⟨-, rfl⟩ := h <;> simp <;> omega
          · simp at hc

/-- with a clock larger than the gas, the concrete run does not time out -/
theorem run_concrete_ne_timeout (h : m.gas < k) : run concrete code input k s m ≠ .timeout := by
  induction k generalizing s m with
  | zero => omega
  | succ k ih =>
    simp only [run]
    split
    · next hs => exact ih (by have := step_concrete_gas hs; omega)
    · simp
    · simp

/-- the concrete run with gas {name}`g` and clock {lit}`g + 1` does not time out: thus
{name}`result_C` and {name}`reads` see the end of the run -/
theorem runC_ne_timeout : runC code i g ≠ .timeout :=
  run_concrete_ne_timeout (by simp)

end EVM
