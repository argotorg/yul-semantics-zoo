import Fuzz.Clocked
import YulSemnaticsZoo.Compiler.Compile
import YulSemnaticsZoo.EVM.Semantics.Clocked.Step

/-!
# Fuzzing the compiler against the Yul semantics, the abstract EVM and geth

For a random object `P` of the subset (`Fuzz.Yul.subsetObject`) that is well-formed, random
calldata `i`, random readings `ρ` and a random clock `k`: if `Compiler.compile P = some B`, then

- (abstract) if `Yul.Clocked.run P i ρ k = some r`, then `EVM.runA B i ρ k'` halts with `r` for a
  large clock `k'`, after as many `GAS` instructions as the Yul run reads values; if the Yul run
  times out at `k`, then `EVM.runA B i ρ k` times out (the same clock);
- (geth) `evm run` of geth runs `B` with the calldata `i`, and the Yul run with the values of the
  `GAS` instructions of geth as readings gives the result of geth, with as many reads.

The first check is the statement of `Compiler.compile_correct` for one `i`, `ρ` and `k`. The
second check also tests the concrete EVM: geth uses real gas. A run where geth goes out of gas or
past its stack limit of 1024 words is a resource failure, and is skipped and counted. 1 case in
10 is a changed subset object (`Fuzz.Yul.mutateObject`), and 1 in 10 an object with all builtins
of the EVM dialect (`Fuzz.Yul.object`). The compiler takes only well-formed objects: the fuzzer
skips and counts each object that is not well-formed. Each compile failure is counted by its
reason.

The abstract runs have no gas. Thus the size of each `return` that is not a literal becomes
`lt(size, 64)` if it is not a number less than 1024 (`boundBlock`): a random reading, calldata
word or string literal as a size would make the run
build a list of up to `2 ^ 256` bytes. The large clock is 2000: a loop that does not end then
stops after 2000 iterations.
-/

namespace Fuzz.Compiler
open _root_.Yul Semantics _root_.Compiler

/-- a clock for the EVM run that is large for the subset programs -/
def bigClock : Nat := 10000000

/-- a word near 0, near 2 ^ 256, or any word -/
def word : Gen Word := do
  match ← nat 0 2 with
  | 0 => return BitVec.ofNat 256 (← nat 0 64)
  | 1 => return BitVec.ofNat 256 (2 ^ 256 - 1 - (← nat 0 64))
  | _ => return BitVec.ofNat 256 (← nat 0 (2 ^ 256 - 1))

mutual

/-- the expression with the size of each `return` less than 1024: a size that is not a number
literal less than 1024 becomes `lt(size, 64)`. The size is still evaluated, thus the reads stay
the same. The abstract runs have no gas, and a random reading, calldata word or string literal
as a size makes `Semantics.read` build a list of up to `2 ^ 256` bytes. -/
partial def boundExpr : Expression → Expression
  | .FunctionCall "return" [off, size] =>
    let size := match size with
      | .Literal (.NumberLiteral n) => if n < 1024 then size else lt size
      | e => lt (boundExpr e)
    .FunctionCall "return" [boundExpr off, size]
  | .FunctionCall f args => .FunctionCall f (args.map boundExpr)
  | e => e
where
  lt (e : Expression) : Expression := .FunctionCall "lt" [e, .Literal (.NumberLiteral 64)]

partial def boundBlock : Block → Block
  | ⟨ss⟩ => ⟨ss.map boundStmt⟩

partial def boundStmt : Statement → Statement
  | .Block b => .Block (boundBlock b)
  | .FunctionDefinition f ps rs b => .FunctionDefinition f ps rs (boundBlock b)
  | .VariableDeclaration xs e => .VariableDeclaration xs (e.map boundExpr)
  | .Assignment xs e => .Assignment xs (boundExpr e)
  | .If c b => .If (boundExpr c) (boundBlock b)
  | .Expression e => .Expression (boundExpr e)
  | .ForLoop i c p b => .ForLoop (boundBlock i) (boundExpr c) (boundBlock p) (boundBlock b)
  | s => s

end

/-- the readings that repeat the words -/
def cycle (ws : List Word) : Readings := fun n => ws.getD (n % ws.length) 0

/-- the result of a case that agrees -/
inductive Case where
  /-- the object is not well-formed: the compiler does not take it -/
  | notWellFormed
  | failed (e : Error)
  /-- the Yul run ends (`true`) or times out; the number of reads and ticks; the geth case -/
  | same (ends : Bool) (reads ticks : Nat) (geth : Fuzz.Clocked.Case)

/-- the abstract check for `P` and its code `B` -/
def abstract (P : WFObject) (B : List UInt8) (i : Input) (ws : List Word) (k : Nat) :
    Except String (Bool × Nat × Nat) :=
  let ρ := cycle ws
  let r := Clocked.top P i ρ k
  let st := r.st
  let info := s!"{P.1.print}\ncode {EVM.hex B}\ncalldata {EVM.hex i}\nreadings {ws.map (·.toNat)}\nclock {k}"
  match r.result with
  | some r =>
    match EVM.runA B i ρ bigClock with
    | .halt r' n =>
      if r' != r then .error s!"Yul gives {repr r}, the EVM gives {repr r'}\n{info}"
      else if n != st.reads then .error s!"Yul reads {st.reads} values, the EVM {n}\n{info}"
      else .ok (true, st.reads, k - st.clock)
    | e => .error s!"Yul gives {repr r}, the EVM gives {repr e}\n{info}"
  | none =>
    match EVM.runA B i ρ k with
    | .timeout => .ok (false, st.reads, k)
    | e => .error s!"Yul times out, the EVM with the same clock gives {repr e}\n{info}"

/-- the geth check for `P` and its code `B`, as in `Fuzz.Clocked.check` -/
def geth (P : WFObject) (B : List UInt8) (i : Input) : IO (Except String Fuzz.Clocked.Case) := do
  let info := s!"{P.1.print}\ncode {EVM.hex B}\ncalldata {EVM.hex i}"
  match ← Fuzz.Clocked.geth (EVM.hex B) i with
  | .error e => return .error e
  | .ok (.error e) =>
    if ["out of gas", "gas uint64 overflow"].any fun s => (e.splitOn s).length > 1 then
      return .ok .outOfGas
    if (e.splitOn "stack limit").length > 1 then return .ok .stackLimit
    return .error s!"geth fails: {e}\n{info}"
  | .ok (.ok data gas) =>
    let ρ : Readings := fun n => BitVec.ofNat 256 (gas.getD n 0)
    let r := Clocked.top P i ρ Fuzz.Clocked.gasLimit
    let st := r.st
    if r.result != some (.ret data) then
      return .error s!"geth returns {EVM.hex data}, Yul gives {repr r.result}\n{info}\ngas {gas}"
    if st.reads != gas.length then
      return .error s!"geth runs {gas.length} GAS, Yul reads {st.reads} values\n{info}"
    return .ok (.same st.reads (Fuzz.Clocked.gasLimit - st.clock))

def check (P : Object) (i : Input) (ws : List Word) (k : Nat) : IO (Except String Case) := do
  let some P := P.checkWellFormed EVM.dialect | return .ok .notWellFormed
  match compileE P with
  | .error e => return .ok (.failed e)
  | .ok B =>
    match abstract P B i ws k with
    | .error e => return .error e
    | .ok (ends, reads, ticks) =>
      match ← geth P B i with
      | .error e => return .error e
      | .ok g => return .ok (.same ends reads ticks g)

structure Counts where
  compiled : Nat := 0
  ends : Nat := 0
  timeouts : Nat := 0
  /-- the compiled cases with a gas read, and with a loop iteration or a function call -/
  reads : Nat := 0
  ticks : Nat := 0
  gethSame : Nat := 0
  gethOutOfGas : Nat := 0
  gethStackLimit : Nat := 0
  /-- the objects that are not well-formed, and the compile failures with each reason -/
  notWellFormed : Nat := 0
  failed : List (Error × Nat) := []

def Counts.add (c : Counts) : Case → Counts
  | .notWellFormed => { c with notWellFormed := c.notWellFormed + 1 }
  | .failed e =>
    { c with failed := match c.failed.lookup e with
      | some n => c.failed.map fun (e', m) => (e', if e' = e then n + 1 else m)
      | none => c.failed ++ [(e, 1)] }
  | .same ends r t g =>
    let c := { c with
      compiled := c.compiled + 1
      reads := c.reads + min r 1
      ticks := c.ticks + min t 1 }
    let c := if ends then { c with ends := c.ends + 1 } else { c with timeouts := c.timeouts + 1 }
    match g with
    | .same .. => { c with gethSame := c.gethSame + 1 }
    | .outOfGas => { c with gethOutOfGas := c.gethOutOfGas + 1 }
    | .stackLimit => { c with gethStackLimit := c.gethStackLimit + 1 }
    | .solcFailed => c

/-- a clock: often small, to test the boundary of the clock, else large -/
def clock : Gen Nat := do if ← coin then nat 0 30 else return 2000

/-- check `k` cases from `g`: the first difference and the number of its case, or the counts -/
def run (g : StdGen) (n : Nat) (c : Counts) : Nat → IO (Except (Nat × String) Counts)
  | 0 => return .ok c
  | k + 1 => do
    let gen : Gen (List UInt8 × List Word × Nat) := do
      return (← list (← nat 0 64) byte, ← list (← nat 1 4) word, ← clock)
    let ((P, i, ws, clk), g) := Id.run do
      -- 1 case in 10 is a changed object (it is often not well-formed: then it is skipped and
      -- counted), and 1 in 10 an object
      -- with all builtins of the EVM dialect: the compiler must reject the builtins outside the 8
      let obj : Fuzz.Yul.YGen Object := do
        match ← (nat 0 9 : Gen Nat) with
        | 0 => Fuzz.Yul.mutateObject (← Fuzz.Yul.subsetObject)
        | 1 => Fuzz.Yul.object 1
        | _ => Fuzz.Yul.subsetObject
      let ((P, _), g) := (obj.run 0).run g
      let (rest, g) := gen.run g
      return (({ P with code := boundBlock P.code }, rest), g)
    match ← check P i ws clk with
    | .error err => return .error (n, err)
    | .ok r => run g (n + 1) (c.add r) k

/-- `[cases] [seed]`: check `cases` cases (100 if not given) from `seed` (the clock if not
given); 0 if there are no differences -/
def fuzz (args : List String) : IO UInt32 := do
  let cases := (args[0]? >>= String.toNat?).getD 100
  let seed ← match args[1]? >>= String.toNat? with
    | some s => pure s
    | none => pure ((← IO.monoNanosNow) % 2 ^ 32)
  IO.println s!"compiler fuzz seed {seed}: {cases} cases"
  (← IO.getStdout).flush
  match ← run (mkStdGen seed) 0 {} cases with
  | .error (i, err) => IO.eprintln s!"case {i}: {err}"; return 1
  | .ok c =>
    let failed := c.failed.map fun (e, n) => s!"{n} {repr e}"
    IO.println s!"no differences ({c.compiled} compiled: {c.ends} end, {c.timeouts} time out, \
      {c.reads} with gas reads, {c.ticks} with loop iterations or calls; geth: {c.gethSame} same, \
      {c.gethOutOfGas} out of gas, {c.gethStackLimit} stack limit; not well-formed: \
      {c.notWellFormed}; compile failures: \
      {if failed.isEmpty then "none" else ", ".intercalate failed})"
    return 0

end Fuzz.Compiler
