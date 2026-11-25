import YulSemnaticsZoo.EVM.Syntax
import YulSemnaticsZoo.EVM.Printer
import YulSemnaticsZoo.EVM.Theorems
import YulSemnaticsZoo.EVM.Semantics
import YulSemnaticsZoo.EVM.Gas

set_option doc.verso true

/-!
# EVM

- *Syntax*: code is bytes, since programs read and create code; an instruction is decoded from
  the bytes. Each instruction is a real EVM instruction, with the same opcode and stack arguments.
- *Printer*: instructions as {lit}`solc --opcodes` prints them. {lit}`lake test` fuzzes the encoding
  against the assembler of solc.
- *Theorems*: decoding an encoded program gives it back, and encoding a decoded instruction gives
  back its bytes.
- *Semantics*: a clocked interpreter with one step function and a gas model as a parameter, the
  abstract gas model, and the relation {lit}`(code, i, ρ) ⇝ b`.
- *Concrete gas*: the real gas costs. {lit}`lake test` fuzzes them against {lit}`evm run` of geth.
-/
