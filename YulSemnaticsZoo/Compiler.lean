import YulSemnaticsZoo.Compiler.Compile
import YulSemnaticsZoo.Compiler.Correct

set_option doc.verso true

/-!
# Compiler

The pages:

- *Compile*: {lit}`compile : Yul.Object → Option (List UInt8)`, a compiler from the code of a
  Yul object in the EVM dialect to EVM bytecode. Variables are on the stack, functions are code
  with a return label on the stack, and labels get their positions in one layout pass. It gives
  {lit}`none` for an object that is not well-formed, for a builtin outside the 8 builtins of the
  clocked semantics, and for code that it cannot make (stack too deep, code too large).
- *Correctness*: {lit}`compile_correct`: if {lit}`compile P = some B`, then {lit}`B` and
  {lit}`P` have the same behaviour for each input and each readings. {lit}`compile_congr` and
  {lit}`compile_concrete` follow from it.

The proof is in {lit}`YulSemnaticsZoo/Compiler/Lemmas`: a forward simulation for each function of
the Yul interpreter, by its functional induction. {lit}`lake test` fuzzes the compiler against
the Yul interpreter, the abstract EVM and geth ({lit}`Fuzz/Compiler.lean`).
-/
