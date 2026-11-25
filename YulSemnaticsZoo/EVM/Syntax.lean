import YulSemnaticsZoo.EVM.Syntax.Syntax
import YulSemnaticsZoo.EVM.Syntax.Printer
import YulSemnaticsZoo.EVM.Syntax.Theorems

set_option doc.verso true

/-!
# EVM: syntax

The pages under *Syntax*:

- *Syntax*: code is bytes, since programs read and create code; an instruction is decoded from
  the bytes. Each instruction is a real EVM instruction, with the same opcode and stack arguments.
- *Printer*: instructions as {lit}`solc --opcodes` prints them. {lit}`lake test` fuzzes the encoding
  against the assembler of solc.
- *Theorems*: decoding an encoded program gives it back, and encoding a decoded instruction gives
  back its bytes.
-/
