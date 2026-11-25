import YulSemnaticsZoo.Yul.Semantics.Clocked.Interp
import YulSemnaticsZoo.Yul.Syntax.Quote

/-! `lake test` fuzzes the clocked semantics against solc and geth (`Fuzz.Clocked`), and
`Yul.Clocked.run_mono` proves (Mono). These tests are for the boundary of the clock, which the
fuzzer does not check (it gives each run sufficient clock), and for the type of the interpreter:
it runs only well-formed objects. -/

namespace Yul.Clocked.Test
open Yul Yul.Clocked

/-- the object with the proof that it is well-formed in the EVM dialect, or `none` -/
def wf (P : Object) : Option WFObject := P.checkWellFormed EVM.dialect

-- the interpreter takes only well-formed objects: an `Object` is not a `WFObject`
#guard_msgs (drop info) in
#check_failure (run ([yul| object "O" { code { } } |] : Object) [] (fun _ => 0) 0)

-- one call and a loop with 2 iterations: the clock decreases at the call and at each of the 3
-- tests of the condition
def P : Object :=
  [yul| object "O" { code {
    function f() { for { let k := 0 } lt(k, 2) { k := add(k, 1) } { } }
    f()
  } } |]

#guard (wf P).map (run · [] (fun _ => 0) 3) == some none
#guard (wf P).map (run · [] (fun _ => 0) 4) == some (some (.ret []))

-- a builtin of the EVM dialect that the semantics does not define halts the run with
-- `unsupported`, after its arguments: the `gas()` in the arguments of `call` reads a value
def callP : Object :=
  [yul| object "O" { code { let x := call(gas(), 0, 0, 0, 0, 0, 0) return(0, 0) } } |]

#guard (wf callP).map (run · [] (fun _ => 0) 0) == some (some .unsupported)
#guard (wf callP).map (fun P => (top P [] (fun _ => 0) 0).st.reads) == some 1

-- also a builtin with a literal argument
def datasizeP : Object :=
  [yul| object "O" { code { mstore(0, datasize("D")) return(0, 32) } data "D" hex"00" } |]

#guard (wf datasizeP).map (run · [] (fun _ => 0) 0) == some (some .unsupported)

def verbatimP : Object := [yul| object "O" { code { verbatim_0i_0o("a") return(0, 0) } } |]

#guard (wf verbatimP).map (run · [] (fun _ => 0) 0) == some (some .unsupported)

-- a run that does not reach the builtin is not affected
def unreachedP : Object :=
  [yul| object "O" { code { if lt(1, 0) { verbatim_0i_0o("a") } mstore(0, 7) return(31, 1) } } |]

#guard (wf unreachedP).map (run · [] (fun _ => 0) 0) == some (some (.ret [7]))

end Yul.Clocked.Test
