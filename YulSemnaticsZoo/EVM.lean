import YulSemnaticsZoo.EVM.Syntax.Syntax
import YulSemnaticsZoo.EVM.Syntax.Printer
import YulSemnaticsZoo.EVM.Syntax.Theorems
import YulSemnaticsZoo.EVM.Semantics.Clocked.Step
import YulSemnaticsZoo.EVM.Semantics.Clocked.Gas
import YulSemnaticsZoo.EVM.Semantics.Clocked.Refinement

set_option doc.verso true

/-!
# EVM

The pages under *Syntax*:

- *Syntax*: code is bytes, since programs read and create code; an instruction is decoded from
  the bytes. Each instruction is a real EVM instruction, with the same opcode and stack arguments.
- *Printer*: instructions as {lit}`solc --opcodes` prints them. {lit}`lake test` fuzzes the encoding
  against the assembler of solc.
- *Theorems*: decoding an encoded program gives it back, and encoding a decoded instruction gives
  back its bytes.

The pages under *Semantics*, *Clocked*:

- *Semantics*: a clocked interpreter with one step function and a gas model as a parameter, the
  abstract gas model, and the relation {lit}`⟪code, i, ρ⟫ ⇝ b`.
- *Concrete gas*: the real gas costs. {lit}`lake test` fuzzes them against {lit}`evm run` of geth.
- *Refinement*: obligation 3 of {lit}`doc/gas-equivalence.md`. If the concrete run halts with a
  result, then the abstract run with the readings of the concrete run halts with the same result.
-/
