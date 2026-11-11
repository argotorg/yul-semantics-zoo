import YulSemnaticsZoo.Yul.Dialect

set_option doc.verso true

/-!
# Yul: the EVM dialect

Builtins for the opcodes of the tiny EVM (see `EVM.Instr`), and the solc object builtins. The
names, and the arguments that must be literals, are as in solc ({lit}`libyul/backends/evm`).
-/

namespace Yul.EVM

inductive Builtin where
  | Add
  | Eq
  | Codecopy
  | Extcodecopy
  | Mload
  | Mstore
  | Gas
  -- `create(value, offset, size)`
  | Create
  -- `call(gas, addr, value, argsOffset, argsSize, retOffset, retSize)`
  | Call
  -- `return(offset, size)`
  | Return
  -- `dataoffset("name")`: the offset of a sub-object or data in the code
  | Dataoffset (name : String)
  -- `datasize("name")`: the size of a sub-object or data
  | Datasize (name : String)
  -- `datacopy(to, offset, size)`
  | Datacopy
  -- `setimmutable(offset, "name", value)`: write `value` to memory at `offset` at each place where
  -- the runtime code at `offset` reads immutable `name`
  | Setimmutable (name : String)
  -- `loadimmutable("name")`
  | Loadimmutable (name : String)
  -- `linkersymbol("id")`: the address of library `id`, set by the linker
  | Linkersymbol (id : String)
  -- `memoryguard(size)`
  | Memoryguard (size : BitVec 256)
  -- `verbatim_<ins>i_<outs>o("code", args)`: the bytes `code` in the output
  | Verbatim (ins outs : Nat) (code : List UInt8)
  deriving DecidableEq, Repr

def outs : Builtin → Nat
  | .Add | .Eq | .Mload | .Gas | .Create | .Call
  | .Dataoffset _ | .Datasize _ | .Loadimmutable _ | .Linkersymbol _ | .Memoryguard _ => 1
  | .Codecopy | .Extcodecopy | .Mstore | .Return | .Datacopy | .Setimmutable _ => 0
  | .Verbatim _ o _ => o

/-- the name of the sub-object or data that a builtin refers to -/
def dataName : Builtin → Option String
  | .Dataoffset name | .Datasize name => some name
  | _ => none

/-- the instructions of the EVM in solc 0.8.38, without the ones that are only in EOF -/
def instructions : List String :=
  ["stop", "add", "sub", "mul", "div", "sdiv", "mod", "smod", "exp", "not", "lt", "gt", "slt",
   "sgt", "eq", "iszero", "and", "or", "xor", "byte", "shl", "shr", "sar", "clz", "addmod",
   "mulmod", "signextend", "keccak256", "address", "balance", "origin", "caller", "callvalue",
   "calldataload", "calldatasize", "calldatacopy", "codesize", "codecopy", "gasprice",
   "extcodesize", "extcodecopy", "returndatasize", "returndatacopy", "mcopy", "extcodehash",
   "blockhash", "blobhash", "coinbase", "timestamp", "number", "difficulty", "prevrandao",
   "gaslimit", "chainid", "selfbalance", "basefee", "blobbasefee", "pop", "mload", "mstore",
   "mstore8", "sload", "sstore", "tload", "tstore", "jump", "jumpi", "pc", "msize", "gas",
   "jumpdest", "log0", "log1", "log2", "log3", "log4", "create", "call", "callcode",
   "staticcall", "return", "delegatecall", "create2", "revert", "invalid", "selfdestruct"] ++
  (List.range 33).map (s!"push{·}") ++ (List.range 16).map (s!"dup{· + 1}") ++
  (List.range 16).map (s!"swap{· + 1}")

/-- the names that solc 0.8.38 does not let a declaration use: the instructions, the object
builtins, and each name that starts with {lit}`verbatim` -/
def reserved (x : Identifier) : Bool :=
  x.startsWith "verbatim" || instructions.contains x ||
    ["linkersymbol", "datasize", "dataoffset", "datacopy", "setimmutable", "loadimmutable",
     "memoryguard"].contains x

/-- a builtin with {name}`k` arguments, none of them literals -/
def plain (k : Nat) (b : Builtin) : Option (List Arg × (List Literal → Option Builtin)) :=
  some (List.replicate k .Expression, fun _ => some b)

/-- the name in a string literal -/
def name? : List Literal → Option String
  | [.StringLiteral s] => String.fromUTF8? ⟨s.toArray⟩
  | _ => none

/-- the size in a number literal that fits in a word -/
def size? : List Literal → Option (BitVec 256)
  | [.NumberLiteral k] => if k < 2 ^ 256 then some (BitVec.ofNat 256 k) else none
  | _ => none

/-- the code in a string literal, which is not empty (as in solc) -/
def code? : List Literal → Option (List UInt8)
  | [.StringLiteral s@(_ :: _)] => some s
  | _ => none

/-- a decimal number of verbatim slots: `[1-9]?[0-9]` in solc -/
def slots? (s : String) : Option Nat :=
  s.toNat?.filter fun k => k < 100 && toString k == s

/-- the number of arguments and returns in the name `verbatim_<ins>i_<outs>o` -/
def verbatim? (f : Identifier) : Option (Nat × Nat) :=
  match f.splitOn "_" with
  | ["verbatim", i, o] =>
    match i.toList.reverse, o.toList.reverse with
    | 'i' :: i', 'o' :: o' => do
      some (← slots? (String.ofList i'.reverse), ← slots? (String.ofList o'.reverse))
    | _, _ => none
  | _ => none

def builtin : Identifier → Option (List Arg × (List Literal → Option Builtin))
  | "add" => plain 2 .Add
  | "eq" => plain 2 .Eq
  | "codecopy" => plain 3 .Codecopy
  | "extcodecopy" => plain 4 .Extcodecopy
  | "mload" => plain 1 .Mload
  | "mstore" => plain 2 .Mstore
  | "gas" => plain 0 .Gas
  | "create" => plain 3 .Create
  | "call" => plain 7 .Call
  | "return" => plain 2 .Return
  | "datacopy" => plain 3 .Datacopy
  | "dataoffset" => some ([.Literal], fun ls => (name? ls).map .Dataoffset)
  | "datasize" => some ([.Literal], fun ls => (name? ls).map .Datasize)
  | "setimmutable" =>
    some ([.Expression, .Literal, .Expression], fun ls => (name? ls).map .Setimmutable)
  | "loadimmutable" => some ([.Literal], fun ls => (name? ls).map .Loadimmutable)
  | "linkersymbol" => some ([.Literal], fun ls => (name? ls).map .Linkersymbol)
  | "memoryguard" => some ([.Literal], fun ls => (size? ls).map .Memoryguard)
  | f => (verbatim? f).map fun (i, o) =>
    (.Literal :: List.replicate i .Expression, fun ls => (code? ls).map (.Verbatim i o))

def dialect : Dialect where
  Builtin := Builtin
  outs := outs
  builtin := builtin
  dataName := dataName
  reserved := reserved

end Yul.EVM
