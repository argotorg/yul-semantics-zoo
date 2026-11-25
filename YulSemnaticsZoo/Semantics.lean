set_option doc.verso true

/-!
# Semantics: shared definitions

The definitions that the Yul semantics and the EVM semantics both use: words, the input, memory,
the gas readings, and the results and behaviours of a run. {lit}`doc/gas-equivalence.md` defines
the equivalence that uses them.
-/

namespace Semantics

/-- a value on the stack, in a variable or in memory -/
abbrev Word := BitVec 256

/-- the calldata of a run -/
abbrev Input := List UInt8

/-- the value of {name}`bytes` in big-endian order: the first byte is the most significant -/
def ofBytes (bytes : List UInt8) : Word :=
  bytes.foldl (fun w b => w <<< 8 ||| b.toBitVec.setWidth 256) 0

/-- byte {name}`k` of {name}`w` in big-endian order: byte 0 is the most significant -/
def byte (w : Word) (k : Fin 32) : UInt8 := UInt8.ofBitVec (w.extractLsb' (8 * (31 - k.val)) 8)

/-- memory: a byte at each address. The addresses are not limited to words, so an access at an
address near 2 ^ 256 does not wrap. -/
abbrev Memory := Nat → UInt8

/-- the memory at the start of a run: each byte is 0 -/
def Memory.empty : Memory := fun _ => 0

/-- the {name}`size` bytes at {name}`off` -/
def read (m : Memory) (off size : Word) : List UInt8 :=
  (List.range size.toNat).map fun k => m (off.toNat + k)

/-- the word at {name}`off`: 32 bytes in big-endian order -/
def mload (m : Memory) (off : Word) : Word := ofBytes (read m off 32)

/-- the memory with {name}`v` at {name}`off`: 32 bytes in big-endian order -/
def mstore (m : Memory) (off v : Word) : Memory := fun a =>
  if h : off.toNat ≤ a ∧ a - off.toNat < 32 then byte v ⟨a - off.toNat, h.2⟩ else m a

/-- the 32 bytes of {name}`i` at {name}`off` in big-endian order; each byte after the end of
{name}`i` is 0 -/
def calldataload (i : Input) (off : Word) : Word := mload (fun a => i.getD a 0) off

/-- the gas readings: {lit}`ρ n` is the value of the n-th gas read, and the count starts at 0 -/
abbrev Readings := Nat → Word

/-- 1 if {name}`a` is less than {name}`b` as unsigned numbers, else 0 -/
def lt (a b : Word) : Word := if a < b then 1 else 0

/-- 1 if {name}`a` and {name}`b` are equal, else 0 -/
def eq (a b : Word) : Word := if a = b then 1 else 0

/-- the result of a run that ends. It contains no gas value. -/
inductive Result where
  /-- a halt with no error ({lit}`STOP`, {lit}`RETURN`, or the end of the code), with the return
  data; {lit}`STOP` gives no data -/
  | ret (data : List UInt8)
  /-- an exceptional halt of the EVM: a bad jump, a stack underflow or overflow, or an undefined
  opcode -/
  | exception
  /-- an instruction or builtin that the semantics do not define: {lit}`CODECOPY`,
  {lit}`EXTCODECOPY`, {lit}`CREATE` or {lit}`CALL` -/
  | unsupported
  deriving DecidableEq, Repr

/-- the behaviour of a run: it ends with a result, or it does not end -/
inductive Beh where
  | ends (r : Result)
  | diverges
  deriving DecidableEq, Repr

end Semantics
