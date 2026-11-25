import YulSemnaticsZoo.Yul.Semantics.Clocked.Interp
import YulSemnaticsZoo.Yul.Syntax.Quote

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

-- a builtin of the EVM dialect that the semantics does not define halts the run with
-- `unsupported`, after its arguments: the `gas()` in the arguments of `call` reads a value
def callP : Object :=
  [yul| object "O" { code { let x := call(gas(), 0, 0, 0, 0, 0, 0) return(0, 0) } } |]

#guard run callP [] (fun _ => 0) 0 == some .unsupported
#guard (top callP [] (fun _ => 0) 0).2.reads == 1

-- also a builtin with a literal argument
def datasizeP : Object :=
  [yul| object "O" { code { mstore(0, datasize("D")) return(0, 32) } data "D" hex"00" } |]

#guard run datasizeP [] (fun _ => 0) 0 == some .unsupported

def verbatimP : Object := [yul| object "O" { code { verbatim_0i_0o("a") return(0, 0) } } |]

#guard run verbatimP [] (fun _ => 0) 0 == some .unsupported

-- a run that does not reach the builtin is not affected
def unreachedP : Object :=
  [yul| object "O" { code { if lt(1, 0) { verbatim_0i_0o("a") } mstore(0, 7) return(31, 1) } } |]

#guard run unreachedP [] (fun _ => 0) 0 == some (.ret [7])

end Yul.Clocked.Test
