import YulSemnaticsZoo.Compiler.Compile
import YulSemnaticsZoo.EVM.Semantics.Clocked.Step
import YulSemnaticsZoo.Yul.Syntax.Quote

/-! `lake test` fuzzes the compiler (`Fuzz.Compiler`), and `Compiler.compile_correct` proves it.
These tests are for boundaries that the fuzzer seldom gives: the clock at a timeout, and the
limits of the stack; and for the type of the compiler: it compiles only well-formed objects. -/

namespace Compiler.Test
open Yul Compiler

/-- the object with the proof that it is well-formed in the EVM dialect, or `none` -/
def wf (P : Object) : Option WFObject := P.checkWellFormed EVM.dialect

/-- for a well-formed object: the reason why the compiler gives no code, or `none` -/
def reason (P : Object) : Option (Option Error) :=
  (wf P).map fun P =>
    match compileE P with
    | .error e => some e
    | .ok _ => none

-- the compiler takes only well-formed objects: an `Object` is not a `WFObject`
#guard_msgs (drop info) in
#check_failure compile ([yul| object "O" { code { } } |] : Object)

-- one call and a loop with 2 iterations: the Yul run needs clock 4 (`Tests/Clocked.lean`). With
-- clock 3 the EVM run also times out (Fwd-Timeout at the boundary), and it ends with more clock.
def P : Object :=
  [yul| object "O" { code {
    function f() { for { let k := 0 } lt(k, 2) { k := add(k, 1) } { } }
    f()
  } } |]

#guard (wf P).map (Clocked.run · [] (fun _ => 0) 3) == some none
#guard ((wf P).bind compile).map (EVM.runA · [] (fun _ => 0) 3) == some .timeout
#guard ((wf P).bind compile).map (EVM.runA · [] (fun _ => 0) 1000) == some (.halt (.ret []) 0)

-- a builtin that the semantics does not define
def callP : Object := [yul| object "O" { code { let x := call(gas(), 0, 0, 0, 0, 0, 0) } } |]

#guard reason callP == some (some .unsupported)

-- 16 return variables fit (SWAP16), 17 do not
def rets16 : Object := [yul| object "O" { code {
    function f() -> a, b, c, d, e, g, h, i, j, k, l, m, n, o, p, r { }
    let a, b, c, d, e, g, h, i, j, k, l, m, n, o, p, r := f()
  } } |]

def rets17 : Object := [yul| object "O" { code {
    function f() -> a, b, c, d, e, g, h, i, j, k, l, m, n, o, p, r, s { }
  } } |]

#guard reason rets16 == some none
#guard reason rets17 == some (some .stackTooDeep)

end Compiler.Test
