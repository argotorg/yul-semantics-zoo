import Lean.Data.Json
import Fuzz.Bytecode
import YulSemnaticsZoo.EVM.Semantics.Clocked.Gas
import YulSemnaticsZoo.EVM.Syntax.Printer

/-!
# Fuzzing the concrete EVM semantics against geth

Runs random bytecode (`Fuzz.Bytecode`) with random calldata and gas in `EVM.runC` and in
`evm run --json` of geth, and compares the end of the run (the return data, an exception, or a
resource failure: out of gas or a stack overflow), the value that each `GAS` pushes, and for a halt
without error the remaining gas. `evm` must be on the path.

The semantics stops at an unsupported instruction (`CODECOPY`, `EXTCODECOPY`, `CREATE`, `CALL`,
or an opcode of the real EVM that the tiny EVM does not have), and geth executes it. Thus a case
that ends with `Result.unsupported` is skipped and counted. Before the cases, the fuzzer checks
`EVM.defined` against geth for each byte: geth must reject exactly the bytes that are not
defined.
-/

namespace Fuzz.Geth
open EVM Semantics Lean

/-- the end of a run: a result, or a resource failure -/
inductive End where
  | result (r : Result)
  | fail (f : Failure)
  deriving DecidableEq, Repr

/-- a run as geth or the semantics gives it -/
structure Run where
  result : End
  reads : List Nat
  /-- the remaining gas, only for a halt without error -/
  left : Option Nat
  deriving DecidableEq, Repr

def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

/-- the digits without a {lit}`0x` prefix -/
def digits (s : String) : List Char :=
  match s.toList with
  | '0' :: 'x' :: cs => cs
  | cs => cs

def natOfHex (s : String) : Option Nat :=
  (digits s).foldlM (fun v c => (16 * v + ·) <$> hexDigit c) 0

def bytesOfHex (s : String) : Option (List UInt8) :=
  let rec go : List Char → Option (List UInt8)
    | [] => some []
    | a :: b :: cs => do
      let byte := 16 * (← hexDigit a) + (← hexDigit b)
      return byte.toUInt8 :: (← go cs)
    | [_] => none
  go (digits s)

/-- the result of geth for the error of the run -/
def classify : Option String → List UInt8 → Except String End
  | none, out => .ok (.result (.ret out))
  | some e, _ =>
    if e.startsWith "out of gas" || e == "gas uint64 overflow" then .ok (.fail .outOfGas)
    else if e.startsWith "stack limit reached" then .ok (.fail .stackOverflow)
    else if ["stack underflow", "invalid jump destination", "invalid opcode"].any (e.startsWith ·)
    then .ok (.result .exception)
    else .error s!"unknown error of geth: {e}"

def str (j : Json) (k : String) : Except String String := j.getObjValAs? String k

/-- the run in the JSON trace of {lit}`evm run --json` with gas {name}`g` -/
def parse (g : Nat) (trace : String) : Except String Run := do
  let lines ← ((trace.splitOn "\n").filter (· ≠ "")).mapM Json.parse
  let some last := lines.getLast? | throw "no output"
  let steps := lines.dropLast
  let err := (str last "error").toOption
  let some out := bytesOfHex (← str last "output") | throw "bad output"
  let some used := natOfHex (← str last "gasUsed") | throw "bad gasUsed"
  -- the value of a `GAS` is the top of the stack at the next step
  let reads ← (steps.zip steps.tail).filterMapM fun (s, t) => do
    if (str s "opName").toOption == some "GAS" && (str s "error").toOption.isNone then
      let stack ← t.getObjValAs? (List String) "stack"
      let some v := stack.getLast? >>= natOfHex | throw "bad stack after GAS"
      return some v
    else return none
  let result ← classify err out
  return ⟨result, reads, if err.isNone then some (g - used) else none⟩

/-- the run of the semantics; {lit}`none` if it ends with {name}`Result.unsupported` -/
def ours (code : List UInt8) (i : Input) (g : Nat) : Except String (Option Run) :=
  let reads (m : Meter) := m.reads.map (·.toNat)
  match runC code i g with
  | .halt .unsupported _ => .ok none
  | .halt (.ret out) m => .ok (some ⟨.result (.ret out), reads m, some m.gas⟩)
  | .halt r m => .ok (some ⟨.result r, reads m, none⟩)
  | .fail f m => .ok (some ⟨.fail f, reads m, none⟩)
  | .timeout => .error "timeout"

/-- the run of geth -/
def geth (code : List UInt8) (i : Input) (g : Nat) : IO (Except String Run) := do
  let input := if i.isEmpty then #[] else #["--input", "0x" ++ hex i]
  let out ← IO.Process.output
    { cmd := "evm", args := #["run", "--json", "--gas", toString g] ++ input ++ #[hex code] }
  if out.exitCode != 0 then return .error s!"evm fails: {out.stdout}{out.stderr}"
  return parse g out.stderr

/-- geth rejects the code {lit}`b` with an {lit}`invalid opcode` error -/
def rejects (b : UInt8) : IO (Except String Bool) := do
  let out ← IO.Process.output
    { cmd := "evm", args := #["run", "--json", "--nostack", "--gas", "100", hex [b]] }
  let some last := ((out.stderr.splitOn "\n").filter (· ≠ "")).getLast? | return .error "no output"
  return (Json.parse last).map fun j =>
    ((str j "error").toOption.map (·.startsWith "invalid opcode")).getD false

/-- the first byte where geth and {name}`EVM.defined` differ: geth must reject exactly the bytes
that are not defined -/
def checkOpcodes : IO (Option String) := do
  for b in List.range 256 do
    match ← rejects b.toUInt8 with
    | .error e => return some s!"byte {b}: {e}"
    | .ok r =>
      let d := defined b.toUInt8
      if r == d then return some s!"byte 0x{hex [b.toUInt8]}: geth rejects: {r}, defined: {d}"
  return none

/-- the gas: small (out of gas is frequent), medium, or sufficient for a stack overflow. geth
takes gas 0 as no limit, so the gas is at least 1. -/
def gas : Gen Nat :=
  Bytecode.weighted [(3, nat 1 60), (4, nat 60 3000), (3, nat 3000 40000)] (return 1)

/-- a case without a difference -/
inductive Outcome where
  | same (r : Run)
  | skip

/-- the outcome of a case, or the difference -/
def check (code : List UInt8) (i : Input) (g : Nat) : IO (Except String Outcome) := do
  let case := s!"evm run --json --gas {g} --input 0x{hex i} {hex code}"
  match ours code i g, ← geth code i g with
  -- geth executes the unsupported instruction, and can then give any error
  | .ok none, _ => return .ok .skip
  | .error e, _ | _, .error e => return .error s!"{e}\n {case}"
  | .ok (some a), .ok b =>
    return if a = b then .ok (.same a)
      else .error s!"{case}\n ours: {repr a}\n geth: {repr b}"

/-- the counts of the cases with each kind of result -/
structure Counts where
  ret := 0
  exception := 0
  oog := 0
  stackOverflow := 0
  skipped := 0
  /-- the number of compared {lit}`GAS` values -/
  reads := 0

def Counts.add (c : Counts) : Outcome → Counts
  | .same r =>
    let c := { c with reads := c.reads + r.reads.length }
    match r.result with
    | .result (.ret _) => { c with ret := c.ret + 1 }
    | .result _ => { c with exception := c.exception + 1 }
    | .fail .outOfGas => { c with oog := c.oog + 1 }
    | .fail .stackOverflow => { c with stackOverflow := c.stackOverflow + 1 }
  | .skip => { c with skipped := c.skipped + 1 }

/-- check {name}`k` cases from {name}`g`: the counts, or the first difference and the number of
its case -/
def run (g : StdGen) (i : Nat) (c : Counts) : Nat → IO (Except (Nat × String) Counts)
  | 0 => return .ok c
  | k + 1 => do
    let ((code, input, gas), g) :=
      Id.run ((do return (← Bytecode.program, ← Bytecode.input, ← gas)).run g)
    match ← check code input gas with
    | .error e => return .error (i, e)
    | .ok o => run g (i + 1) (c.add o) k

/-- {lit}`[cases] [seed]`: check {lit}`cases` cases (200 if not given) from {lit}`seed` (the
clock if not given); 0 if there are no differences -/
def fuzz (args : List String) : IO UInt32 := do
  let cases := (args[0]? >>= String.toNat?).getD 200
  let seed ← match args[1]? >>= String.toNat? with
    | some s => pure s
    | none => pure ((← IO.monoNanosNow) % 2 ^ 32)
  IO.println s!"geth opcodes: 256 bytes"
  (← IO.getStdout).flush
  let opcodes ← checkOpcodes
  match opcodes with
  | some e => IO.eprintln e
  | none => IO.println "no differences"
  IO.println s!"geth fuzz seed {seed}: {cases} cases"
  (← IO.getStdout).flush
  match ← run (mkStdGen seed) 0 {} cases with
  | .error (i, err) => IO.eprintln s!"case {i}: {err}"; return 1
  | .ok c =>
    IO.println s!"no differences ({c.ret} return, {c.exception} exception, {c.oog} out of gas, \
      {c.stackOverflow} stack overflow, {c.skipped} skipped: unsupported; {c.reads} GAS values)"
    return if opcodes.isSome then 1 else 0

end Fuzz.Geth
