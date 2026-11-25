import YulSemnaticsZoo.EVM.Semantics.Clocked.Gas

namespace EVM.Test
open EVM Semantics

/-- {name}`n` times {lit}`PUSH0`, then the end of the code -/
def pushes (n : Nat) : List UInt8 := List.replicate n 0x5f

-- the boundary of the stack limit: the concrete run can have 1024 words on the stack, and a
-- stack overflow is a resource failure. The abstract run has no stack limit.
#guard result_C (pushes 1024) [] 5000 == some (.ret [])
#guard result_C (pushes 1025) [] 5000 == none
#guard runC (pushes 1025) [] 5000 == .fail .stackOverflow ⟨5000 - 2048, []⟩
#guard runA (pushes 1025) [] (fun _ => 0) 1026 == .halt (.ret []) 0

end EVM.Test
