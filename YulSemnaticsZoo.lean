import YulSemnaticsZoo.Yul
import YulSemnaticsZoo.EVM

/-!
# Yul semantics zoo

This document defines a small Yul and a small EVM, and semantics for them in different styles.
The goal is to find which style of semantics is best for a compiler correctness theorem from Yul
to the EVM. The design priorities are:

1. completeness: the compiler can compile most existing Solidity code;
2. auditability: the trusted semantics and the correctness statement are simple to read and to
   check;
3. proof efficiency: proofs about compiler passes are local and modular, so passes can be added,
   removed and reordered without changes to other proofs.

The two languages have only the parts of Yul and the EVM that make semantics or a correctness
statement hard: `gas()`, infinite loops and recursion, contract creation, calls to other code,
reads of the own code and of other code, immutables, `datacopy`, data and its offsets,
`memoryguard`, `verbatim`, and library linking. Each program of the small languages is a program of
the real ones.

The document has two parts, *Yul* and *EVM*: each defines the syntax of the language, how it
is read and printed, and theorems about these.

## Semantics

The semantics of Yul and of the EVM, in each style, are parts of this document still to come.
-/
