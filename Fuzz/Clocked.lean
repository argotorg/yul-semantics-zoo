import Lean.Data.Json
import Fuzz.YulGen
import YulSemnaticsZoo.Yul.Semantics.Clocked.Interp
import YulSemnaticsZoo.EVM.Syntax.Printer

/-!
# Fuzzing the clocked Yul semantics against solc and geth

For a random object `o` that is well-formed in the EVM dialect and calls only the 8 builtins
that the clocked semantics defines (`Fuzz.Yul.subsetObject`), and random calldata:
- solc compiles `o` without optimization steps (`solc`);
- `evm run` (geth) runs the bytecode with the calldata and `gasLimit` gas; a second run with a
  trace gives the value that each `GAS` pushes (`geth`);
- `Yul.Clocked.top` with these values as the readings and the clock `gasLimit` gives the result of
  geth, and reads as many values as geth runs `GAS` instructions (`check`).

The clock `gasLimit` is sufficient: each loop iteration and each function call in the bytecode
runs a jump, which costs more than 1 gas.

The settings of solc keep each `gas()`. With only `"optimizer": {"enabled": false}`, solc 0.8.38
removes a `gas()` whose value is not used, at two places: the stack allocation of the Yul code
generator (on by default; `stackAllocation: false` needs `yul: true`, here with no steps `":"`),
and the peephole optimizer of the assembly (it removes `GAS POP`). Then the later reads get other
values. Thus the fuzzer turns both off.

Cases where solc fails (for example, stack too deep) are skipped and counted. Cases where geth
goes out of gas or past its stack limit of 1024 words are also skipped and counted: these are
resource failures, {lit}`EVM.result_C` gives {lit}`none` for them, and the spec gives no statement
about them. Yul has no limit on the depth of calls, thus a deep recursion in Yul can end or
diverge where the bytecode has a stack overflow.
-/

namespace Fuzz.Clocked
open Lean _root_.Yul Semantics

/-- the gas for geth, and the clock for the interpreter -/
def gasLimit : Nat := 10000000

def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- the number in hex digits, with or without `0x` -/
def parseHexNat (s : String) : Option Nat :=
  let cs := s.toList
  let cs := if cs.take 2 == ['0', 'x'] then cs.drop 2 else cs
  cs.foldlM (fun n c => (hexVal c).map (n * 16 + ·)) 0

/-- the bytes in hex digits, with or without `0x` -/
def parseHexBytes (s : String) : Option (List UInt8) :=
  let cs := s.toList
  let cs := if cs.take 2 == ['0', 'x'] then cs.drop 2 else cs
  go cs
where
  go : List Char → Option (List UInt8)
    | [] => some []
    | a :: b :: cs => do
      let hi ← hexVal a
      let lo ← hexVal b
      return (hi * 16 + lo).toUInt8 :: (← go cs)
    | [_] => none

/-- the bytecode of `text` from solc, or the errors; the settings keep each `gas()` (see above) -/
def solc (text : String) : IO (Except String String) := do
  let input := Json.mkObj [
    ("language", "Yul"),
    ("sources", Json.mkObj [("s.yul", Json.mkObj [("content", text)])]),
    ("settings", Json.mkObj [
      ("optimizer", Json.mkObj [("enabled", false), ("details", Json.mkObj [("peephole", false),
        ("yul", true),
        ("yulDetails", Json.mkObj [("optimizerSteps", ":"), ("stackAllocation", false)])])]),
      ("outputSelection", Json.mkObj [("*", Json.mkObj [("*", Json.arr #["evm.bytecode.object"])])])])]
  let (h, path) ← IO.FS.createTempFile
  h.putStr input.compress
  h.flush
  let out ← IO.Process.output { cmd := "solc", args := #["--standard-json", path.toString] }
  IO.FS.removeFile path
  let .ok json := Json.parse out.stdout | return .error s!"{out.stdout}{out.stderr}"
  let errors := ((json.getObjValD "errors").getArr?.toOption.getD #[]).toList.filter fun e =>
    e.getObjValD "severity" == Json.str "error"
  if !errors.isEmpty then return .error (", ".intercalate (errors.map (·.compress)))
  let code := (((((json.getObjValD "contracts").getObjValD "s.yul").getObjValD "O").getObjValD
    "evm").getObjValD "bytecode").getObjValD "object"
  match code.getStr? with
  | .ok c => return .ok c
  | .error _ => return .error s!"no bytecode in {json.compress}"

/-- what geth does with a run -/
inductive Geth where
  /-- the run halts with no error: the return data, and the value of each `GAS` -/
  | ok (data : List UInt8) (gas : List Nat)
  /-- the run halts with an error -/
  | error (message : String)

/-- the values that the `GAS` instructions push: the top of the stack after each of them -/
def gasValues (trace : String) : Option (List Nat) := do
  let steps ← (trace.splitOn "\n").filter (· ≠ "") |>.mapM (Json.parse · |>.toOption)
  let after := steps.zip (steps.drop 1)
  (after.filter fun (s, _) => s.getObjValD "opName" == Json.str "GAS").mapM fun (_, next) => do
    let stack ← (next.getObjValD "stack").getArr?.toOption
    parseHexNat (← (← stack.back?).getStr?.toOption)

/-- geth on `code` with `calldata`: a run without a trace, and if it has no error, a run with a
trace for the values of `GAS` -/
def geth (code : String) (calldata : List UInt8) : IO (Except String Geth) := do
  let args := #["run", "--gas", toString gasLimit, "--input", "0x" ++ EVM.hex calldata, code]
  let out ← IO.Process.output { cmd := "evm", args }
  let text := out.stdout.trimAscii.toString
  if (text.splitOn "error:").length > 1 then return .ok (.error text)
  let some data := parseHexBytes text | return .error s!"geth output\n{out.stdout}{out.stderr}"
  let traced ← IO.Process.output { cmd := "evm", args := #["run", "--trace"] ++ args.drop 1 }
  let some gas := gasValues traced.stderr | return .error s!"geth trace\n{traced.stderr}"
  return .ok (.ok data gas)

/-- the result of a case -/
inductive Case where
  /-- the same result; the number of gas reads and of clock ticks -/
  | same (reads ticks : Nat)
  | solcFailed
  | outOfGas
  | stackLimit

/-- a difference between geth and the interpreter on `o` and `calldata` -/
def check (o : Object) (calldata : List UInt8) : IO (Except String Case) := do
  let text := o.print
  if !decide (o.WellFormed EVM.dialect) then
    return .error s!"the object is not well-formed in the EVM dialect\n{text}"
  let .ok code ← solc text | return .ok .solcFailed
  match ← geth code calldata with
  | .error e => return .error e
  | .ok (.error e) =>
    -- a memory offset or size with a cost that does not fit in 64 bits
    if ["out of gas", "gas uint64 overflow"].any fun s => (e.splitOn s).length > 1 then
      return .ok .outOfGas
    -- a stack overflow: a resource failure, as out of gas
    if (e.splitOn "stack limit").length > 1 then return .ok .stackLimit
    return .error s!"geth fails: {e}\n{text}\ncalldata {EVM.hex calldata}"
  | .ok (.ok data gas) =>
    let ρ : Readings := fun n => BitVec.ofNat 256 (gas.getD n 0)
    let (outcome, st) := Clocked.top o calldata ρ gasLimit
    let ours := outcome.result
    let info := s!"{text}\ncalldata {EVM.hex calldata}\ngas {gas}"
    if ours != some (.ret data) then
      return .error s!"geth returns {EVM.hex data}, we give {repr ours}\n{info}"
    if st.reads != gas.length then
      return .error s!"geth runs {gas.length} GAS, we read {st.reads} values\n{info}"
    return .ok (.same st.reads (gasLimit - st.clock))

structure Counts where
  same : Nat := 0
  -- the compared cases with a gas read, and with a loop iteration or a function call
  reads : Nat := 0
  ticks : Nat := 0
  solcFailed : Nat := 0
  outOfGas : Nat := 0
  stackLimit : Nat := 0

def Counts.add (c : Counts) : Case → Counts
  | .same r t =>
    { c with same := c.same + 1, reads := c.reads + min r 1, ticks := c.ticks + min t 1 }
  | .solcFailed => { c with solcFailed := c.solcFailed + 1 }
  | .outOfGas => { c with outOfGas := c.outOfGas + 1 }
  | .stackLimit => { c with stackLimit := c.stackLimit + 1 }

/-- check `k` cases from `g`: the first difference and the number of its case, or the counts -/
def run (g : StdGen) (i : Nat) (c : Counts) : Nat → IO (Except (Nat × String) Counts)
  | 0 => return .ok c
  | k + 1 => do
    let ((o, calldata), g) := Id.run do
      let ((o, _), g) := (Yul.subsetObject |>.run 0).run g
      let (calldata, g) := (do list (← nat 0 64) byte : Gen _).run g
      return ((o, calldata), g)
    match ← check o calldata with
    | .error err => return .error (i, err)
    | .ok r => run g (i + 1) (c.add r) k

/-- `[cases] [seed]`: check `cases` cases (100 if not given) from `seed` (the clock if not
given); 0 if there are no differences -/
def fuzz (args : List String) : IO UInt32 := do
  let cases := (args[0]? >>= String.toNat?).getD 100
  let seed ← match args[1]? >>= String.toNat? with
    | some s => pure s
    | none => pure ((← IO.monoNanosNow) % 2 ^ 32)
  IO.println s!"clocked yul fuzz seed {seed}: {cases} cases"
  (← IO.getStdout).flush
  match ← run (mkStdGen seed) 0 {} cases with
  | .error (i, err) => IO.eprintln s!"case {i}: {err}"; return 1
  | .ok c =>
    IO.println s!"no differences ({c.same} compared, {c.reads} with gas reads, {c.ticks} with \
      loop iterations or calls; skipped: {c.solcFailed} solc failed, \
      {c.outOfGas} out of gas, {c.stackLimit} stack limit)"
    return 0

end Fuzz.Clocked
