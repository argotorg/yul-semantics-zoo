import YulSemnaticsZoo.EVM.Syntax
import YulSemnaticsZoo.EVM.Printer
import YulSemnaticsZoo.EVM.Theorems

/-!
# EVM

- *Syntax*: code is bytes, since programs read and create code; an instruction is decoded from
  the bytes. Each instruction is a real EVM instruction, with the same opcode and stack arguments.
- *Printer*: instructions as `solc --opcodes` prints them. `lake test` fuzzes the encoding against
  the assembler of solc.
- *Theorems*: decoding an encoded program gives it back, and encoding a decoded instruction gives
  back its bytes.
-/
