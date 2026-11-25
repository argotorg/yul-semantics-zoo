import YulSemnaticsZoo.EVM.Gas
import Fuzz.Bytecode

namespace EVM.Test
open EVM Semantics Fuzz

/-- Obligation 3 of {lit}`doc/gas-equivalence.md` for random code, input and gas: if the concrete
run ends with {lit}`r`, then the abstract run with the readings of the concrete run ends with
{lit}`r`, and the clock {lit}`g + 1` is sufficient. {lit}`none` if the concrete run goes out of
gas. -/
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

end EVM.Test
