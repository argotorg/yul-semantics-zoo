import YulSemnaticsZoo.Yul.Syntax
import YulSemnaticsZoo.Yul.Dialect
import YulSemnaticsZoo.Yul.EVM
import YulSemnaticsZoo.Yul.Lexer
import YulSemnaticsZoo.Yul.Printer
import YulSemnaticsZoo.Yul.Parser
import YulSemnaticsZoo.Yul.Valid
import YulSemnaticsZoo.Yul.WellFormed
import YulSemnaticsZoo.Yul.Theorems
import YulSemnaticsZoo.Yul.Quote
import YulSemnaticsZoo.Yul.Subset
import YulSemnaticsZoo.Yul.Clocked
import YulSemnaticsZoo.Yul.ClockedTheorems

set_option doc.verso true

/-!
# Yul

- *Syntax*: the abstract syntax, with the names of the grammar in the Solidity docs. A *dialect*
  gives the builtins; the *EVM dialect* has the builtins of the small EVM and the builtins of
  solc for objects.
- *Lexer*, *Printer* and *Parser*: between text and ASTs. Where the grammar in the docs and solc
  0.8.38 differ, the parser follows solc, but it rejects object names that are not UTF-8 (the
  *Parser* page lists the differences). {lit}`lake test` fuzzes the parser against the parser
  of solc.
- *Valid* and *Theorems*: parsing printed text gives the AST, for each AST that the grammar can
  express.
- *WellFormed*: the restrictions on the grammar and the scoping rules, for a dialect. The
  parser {lit}`Object.parseWellFormed` gives only well-formed objects. {lit}`lake test` fuzzes
  {lit}`Object.WellFormed` in the EVM dialect against the analysis of solc.
- *Quote*: {lit}`[yul| … |]` is Yul text in Lean, parsed when Lean elaborates it.
- *Subset dialect*: the 8 builtins {lit}`add`, {lit}`lt`, {lit}`eq`, {lit}`calldataload`,
  {lit}`mload`, {lit}`mstore`, {lit}`gas` and {lit}`return`.
- *Clocked semantics*: a big-step interpreter for the subset dialect with a clock, and the
  behaviours of a run. *Clocked theorems*: (Mono), (Det) and (Total). {lit}`lake test` fuzzes
  the interpreter against solc and geth.
-/
