import YulSemnaticsZoo.EVM.Semantics.Clocked.Gas
import Fuzz.Bytecode

namespace EVM.Test
open EVM Semantics Fuzz

/-- Obligation 3 of {lit}`doc/gas-equivalence.md` for random code, input and gas: if the concrete
run ends with {lit}`r`, then the abstract run with the readings of the concrete run ends with
{lit}`r`, and the clock {lit}`g + 1` is sufficient. {lit}`none` for a resource failure of the
concrete run (out of gas or a stack overflow). -/
def refines : Gen (Option Bool) := do
  let code ← Bytecode.program
  let i ← Bytecode.input
  let g ← nat 0 5000
  return (result_C code i g).map fun r =>
    match runA code i (reads code i g) (g + 1) with
    | .halt r' _ => r' == r
    | _ => false

-- the property holds, and at least 300 of the 1000 cases end
#guard
  let rs := ((list 1000 refines).run' (mkStdGen 0)).filterMap id
  rs.all id && 300 ≤ rs.length

/-- {name}`n` times {lit}`PUSH0`, then the end of the code -/
def pushes (n : Nat) : List UInt8 := List.replicate n 0x5f

-- the boundary of the stack limit: the concrete run can have 1024 words on the stack, and a
-- stack overflow is a resource failure. The abstract run has no stack limit.
#guard result_C (pushes 1024) [] 5000 == some (.ret [])
#guard result_C (pushes 1025) [] 5000 == none
#guard runC (pushes 1025) [] 5000 == .fail .stackOverflow ⟨5000 - 2048, []⟩
#guard runA (pushes 1025) [] (fun _ => 0) 1026 == .halt (.ret []) 0

end EVM.Test
