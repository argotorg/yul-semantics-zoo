import YulSemnaticsZoo.Yul.EVM

set_option doc.verso true

/-!
# Yul: the subset dialect

The dialect of the clocked semantics: the 8 builtins {lit}`add`, {lit}`lt`, {lit}`eq`,
{lit}`calldataload`, {lit}`mload`, {lit}`mstore`, {lit}`gas` and {lit}`return`. They have the
names, arguments and results of the EVM dialect, and no literal arguments. A call of another
builtin of the EVM dialect is not well-formed in this dialect. A declaration cannot use the names
that the EVM dialect reserves, as in solc.
-/

namespace Yul.Subset

inductive Builtin where
  | Add
  | Lt
  | Eq
  | Calldataload
  | Mload
  | Mstore
  | Gas
  -- `return(offset, size)`
  | Return
  deriving DecidableEq, Repr

/-- the builtin with a name -/
def builtin? : Identifier → Option Builtin
  | "add" => some .Add
  | "lt" => some .Lt
  | "eq" => some .Eq
  | "calldataload" => some .Calldataload
  | "mload" => some .Mload
  | "mstore" => some .Mstore
  | "gas" => some .Gas
  | "return" => some .Return
  | _ => none

/-- the number of arguments -/
def ins : Builtin → Nat
  | .Gas => 0
  | .Calldataload | .Mload => 1
  | .Add | .Lt | .Eq | .Mstore | .Return => 2

/-- the number of results -/
def outs : Builtin → Nat
  | .Add | .Lt | .Eq | .Calldataload | .Mload | .Gas => 1
  | .Mstore | .Return => 0

def dialect : Dialect where
  Builtin := Builtin
  outs := outs
  builtin f := (builtin? f).map fun b => (List.replicate (ins b) .Expression, fun _ => some b)
  dataName _ := none
  reserved := EVM.reserved

end Yul.Subset
