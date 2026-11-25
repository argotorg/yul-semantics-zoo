import YulSemnaticsZoo.Yul.Semantics.Clocked.Interp
import YulSemnaticsZoo.Yul.Semantics.Clocked.Theorems

set_option doc.verso true

/-!
# Yul: semantics

The pages under *Semantics*, *Clocked*:

- *Clocked semantics*: a big-step interpreter with a clock for the objects that are well-formed
  in the EVM dialect ({lit}`WFObject`), and the behaviours of a run. It defines the 8 builtins
  {lit}`add`, {lit}`lt`, {lit}`eq`, {lit}`calldataload`, {lit}`mload`, {lit}`mstore`, {lit}`gas`
  and {lit}`return`; each other builtin halts the run with {lit}`unsupported`. {lit}`lake test`
  fuzzes the interpreter against solc and geth.
- *Clocked theorems*: (Mono), (Det) and (Total).
-/
