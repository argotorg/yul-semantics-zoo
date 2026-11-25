import Fuzz.Gen
import YulSemnaticsZoo.EVM.Syntax.Syntax

/-!
# Random bytecode for the semantics fuzzers

Most programs are valid code of the tiny EVM: jumps go to JUMPDESTs, and memory offsets are
small. Some programs have a bad jump, a stack error, a large offset, a loop that overflows the
stack, an unsupported instruction, or any byte as an opcode.
-/

namespace Fuzz.Bytecode
open EVM Instr

/-- a part of a program -/
inductive Item where
  | instr (i : Instr)
  /-- {lit}`PUSH2` of the position of a JUMPDEST: the k-th, modulo their number -/
  | label (k : Nat)
  /-- bytes that are not decoded when the program is made -/
  | raw (bytes : List UInt8)
  /-- {lit}`JUMPDEST PUSH0 PUSH2 <this JUMPDEST> JUMP`: each iteration pushes 1 word -/
  | grow

/-- {lit}`PUSHn` of the low {name}`n` bytes of {name}`v` -/
def push (n : Nat) (v : Nat) : Instr :=
  if h : n < 33 then
    Push ⟨n, h⟩ (takeImmediate n ((List.range n).reverse.map fun k => (v >>> (8 * k)).toUInt8))
  else Stop

def Item.size : Item → Nat
  | .instr i => i.encode.length
  | .label _ => 3
  | .raw bytes => bytes.length
  | .grow => 6

/-- the bytes of the items; a label becomes the position of its JUMPDEST -/
def layout (items : List Item) : List UInt8 :=
  let pos := (items.foldl (fun (p, ps) it => (p + it.size, ps ++ [p])) (0, [])).2
  let dests := (items.zip pos).filterMap fun
    | (.instr .Jumpdest, p) | (.grow, p) => some p
    | _ => none
  (items.zip pos).flatMap fun
    | (.instr i, _) => i.encode
    -- without JUMPDESTs, `k % 0 = k` and the jump goes to `k`
    | (.label k, _) => (push 2 (dests.getD (k % dests.length) k)).encode
    | (.raw bytes, _) => bytes
    | (.grow, p) => [0x5b, 0x5f] ++ (push 2 p).encode ++ [0x56]

/-- a generator from the list, with the weights -/
def weighted (xs : List (Nat × Gen α)) (d : Gen α) : Gen α := do
  let r ← nat 0 ((xs.map (·.1)).sum - 1)
  let rec go : List (Nat × Gen α) → Nat → Gen α
    | [], _ => d
    | (w, x) :: xs, r => if r < w then x else go xs (r - w)
  go xs r

/-- {lit}`PUSH0`, or {lit}`PUSH1` of a small value: an offset or a size -/
def pushSmall : Gen Instr := do
  if (← nat 0 3) == 0 then return push 0 0 else return push 1 (← nat 0 96)

/-- a push of any width and value -/
def pushAny : Gen Instr := do
  let n ← nat 1 32
  return push n (← nat 0 (2 ^ (8 * n) - 1))

/-- {lit}`DUPn` or {lit}`SWAPn`, mostly with a small {lit}`n` -/
def dupSwap : Gen Instr := do
  let n ← if ← coin then nat 1 3 else nat 1 16
  let dup ← coin
  return if h : 0 < n ∧ n ≤ 16 then (if dup then Dup n h else Swap n h) else Stop

def item : Gen (List Item) :=
  weighted [
    (12, return [.instr (← pushSmall)]),
    (3, return [.instr (← pushAny)]),
    -- a medium offset: the memory cost has its quadratic part
    (2, return [.instr (push 2 (← nat 0 0x1400))]),
    (4, return [.instr (← pick [Add, Lt, Eq] Add)]),
    (6, return [.instr (← pick [Calldataload, Mload, Mstore, Pop] Pop)]),
    (6, return [.instr (← dupSwap)]),
    (5, return [.instr Jumpdest]),
    (6, return [.label (← nat 0 7), .instr (← pick [Jump, Jumpi] Jump)]),
    (3, return [.instr Gas]),
    -- a branch on the gas: jump if `GAS < x`
    (2, return [.instr (push 2 (← nat 0 3000)), .instr Gas, .instr Lt, .label (← nat 0 7),
                .instr Jumpi]),
    (2, return [.instr (← pushSmall), .instr (← pushSmall), .instr Return]),
    (1, return [.instr Stop]),
    -- a jump that may go to a byte that is not a JUMPDEST
    (1, return [.instr (push 1 (← nat 0 64)), .instr (← pick [Jump, Jumpi] Jump)]),
    -- any byte: an opcode of the tiny EVM, an opcode of the real EVM that the tiny EVM does not
    -- define (the run is skipped), or a byte that geth rejects
    (2, return [.raw [← byte]]),
    (1, return [.grow])]
    (return [])

/-- a program: some pushes, so that the stack has words for the next instructions, then items,
then sometimes an unsupported instruction, then some bytes, for example a push without its data -/
def program : Gen (List UInt8) := do
  let pushes ← list (← nat 0 8) do return Item.instr (← pushSmall)
  let items := pushes ++ (← list (← nat 0 30) item).flatten
  let k ← nat 0 items.length
  let unsupported ← pick [Codecopy, Extcodecopy, Create, Call] Call
  let items := if (← nat 0 9) == 0 then items.take k ++ [.instr unsupported] ++ items.drop k
    else items
  return layout items ++ (← list (← nat 0 2) byte)

/-- calldata -/
def input : Gen (List UInt8) := do list (← nat 0 70) byte

end Fuzz.Bytecode
