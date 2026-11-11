import YulSemnaticsZoo.Yul.Syntax
import YulSemnaticsZoo.Yul.Dialect
import YulSemnaticsZoo.Yul.EVM
import YulSemnaticsZoo.Yul.Lexer
import YulSemnaticsZoo.Yul.Printer
import YulSemnaticsZoo.Yul.Parser
import YulSemnaticsZoo.Yul.Valid
import YulSemnaticsZoo.Yul.Theorems
import YulSemnaticsZoo.Yul.Quote

/-!
# Yul

- *Syntax*: the abstract syntax, with the names of the grammar in the Solidity docs. A *dialect*
  gives the builtins; the *EVM dialect* has the builtins of the small EVM and the builtins of
  solc for objects.
- *Lexer*, *Printer* and *Parser*: between text and ASTs. Where the grammar in the docs and solc
  0.8.33 differ, the parser follows solc. `lake test` fuzzes the parser against the parser of
  solc.
- *Valid* and *Theorems*: parsing printed text gives the AST, for each AST that the grammar can
  express.
- *Quote*: `[yul| … |]` is Yul text in Lean, parsed when Lean elaborates it.
-/
