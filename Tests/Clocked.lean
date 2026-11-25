import YulSemnaticsZoo.Yul.Clocked
import YulSemnaticsZoo.Yul.Quote

/-! `lake test` fuzzes the clocked semantics against solc and geth (`Fuzz.Clocked`), and
`Yul.Clocked.run_mono` proves (Mono). This test is for the boundary of the clock, which the
fuzzer does not check: it gives each run sufficient clock. -/

namespace Yul.Clocked.Test
open Yul Yul.Clocked

-- one call and a loop with 2 iterations: the clock decreases at the call and at each of the 3
-- tests of the condition
def P : Object :=
  [yul| object "O" { code {
    function f() { for { let k := 0 } lt(k, 2) { k := add(k, 1) } { } }
    f()
  } } |]

#guard run P [] (fun _ => 0) 3 == none
#guard run P [] (fun _ => 0) 4 == some (.ret [])

end Yul.Clocked.Test
