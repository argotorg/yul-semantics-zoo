import Fuzz.Solc

/-!
# Fuzzing the EVM encoding against solc

Generates random instructions and bytes, and checks `EVM.Instr.encode` and `EVM.decode` on
them against `solc` (see `Fuzz.Solc`). `solc` must be on the path.
-/

namespace Fuzz
open EVM Instr

abbrev Gen := StateM StdGen

def nat (lo hi : Nat) : Gen Nat := modifyGet fun g => randNat g lo hi

def byte : Gen UInt8 := return (← nat 0 255).toUInt8

def list (k : Nat) (x : Gen α) : Gen (List α) := (List.range k).mapM fun _ => x

/-- a random byte that is not in `eofImmediate` -/
def dataByte : Gen UInt8 := do
  let bytes := (List.range 256).filter (!eofImmediate.contains ·)
  return (bytes.getD (← nat 0 (bytes.length - 1)) 0).toUInt8

def simple : List Instr :=
  [.Stop, .Add, .Eq, .Codecopy, .Extcodecopy, .Pop, .Mload, .Mstore, .Jump, .Jumpi, .Gas,
   .Jumpdest, .Create, .Call, .Return]

/-- a random instruction; a push has its minimal width -/
def instr : Gen Instr := do
  match ← nat 0 3 with
  | 0 => return simple.getD (← nat 0 (simple.length - 1)) .Stop
  | 1 =>
    let n ← nat 0 32
    let imm := (← nat 1 255).toUInt8 :: (← list (n - 1) byte)
    return if h : n < 33 then .Push ⟨n, h⟩ (takeImmediate n imm) else .Stop
  | 2 => let n ← nat 1 16; return if h : 0 < n ∧ n ≤ 16 then .Dup n h else .Stop
  | _ => let n ← nat 1 16; return if h : 0 < n ∧ n ≤ 16 then .Swap n h else .Stop

/-- instructions, and bytes after them -/
def case : Gen (List Instr × List UInt8) :=
  return (← list (← nat 0 20) instr, ← list (← nat 0 32) dataByte)

/-- the bytes and the disassembly that solc gives for asm JSON -/
def solc (json : String) : IO (Except String (String × String)) := do
  let (h, path) ← IO.FS.createTempFile
  h.putStr json
  h.flush
  let out ← IO.Process.output
    { cmd := "solc", args := #["--import-asm-json", "--bin", "--opcodes", path.toString] }
  IO.FS.removeFile path
  let lines := out.stdout.splitOn "\n"
  let after (header : String) := ((lines.dropWhile (· != header)).drop 1).head?
  return match out.exitCode, after "Binary:", after "Opcodes:" with
    | 0, some bin, some ops => .ok (bin, ops)
    | _, _, _ => .error (out.stdout ++ out.stderr)

/-- a difference between solc and us on a case -/
def check (instrs : List Instr) (data : List UInt8) : IO (Option String) := do
  let json := asmJson instrs data
  let bytes := instrs.flatMap encode ++ data
  let ours := " ".intercalate ((disassemble bytes).map fun i => (i.map mnemonic).getD "?")
  return match ← solc json with
    | .error e => some s!"solc fails on {json}\n{e}"
    | .ok (bin, ops) =>
      if bin.trimAscii.toString != hex bytes then
        some s!"encode\n json: {json}\n ours: {hex bytes}\n solc: {bin}"
      else if !agrees (disassemble bytes) ops then
        some s!"decode\n bytes: {hex bytes}\n ours: {ours}\n solc: {ops}"
      else none

/-- check `k` cases from `g`: the first difference, and the number of its case -/
def run (g : StdGen) (i : Nat) : Nat → IO (Option (Nat × String))
  | 0 => return none
  | k + 1 => do
    let ((instrs, data), g) := Id.run (case.run g)
    match ← check instrs data with
    | some err => return some (i, err)
    | none => run g (i + 1) k

/-- `[cases] [seed]`: check `cases` cases (200 if not given) from `seed` (the clock if not
given); 0 if there are no differences -/
def fuzz (args : List String) : IO UInt32 := do
  let cases := (args[0]? >>= String.toNat?).getD 200
  let seed ← match args[1]? >>= String.toNat? with
    | some s => pure s
    | none => pure ((← IO.monoNanosNow) % 2 ^ 32)
  IO.println s!"fuzz seed {seed}: {cases} cases"
  (← IO.getStdout).flush
  match ← run (mkStdGen seed) 0 cases with
  | some (i, err) => IO.eprintln s!"case {i}: {err}"; return 1
  | none => IO.println "no differences"; return 0

end Fuzz
