import YulSemnaticsZoo.Yul
import YulSemnaticsZoo.EVM

set_option doc.verso true

/-!
# Yul semantics zoo

This repository defines syntax and semantics for two cut down versions of both yul and the evm. The
goal is to explore which semantic styles are best suited for a compiler correctness theorem between
yul and the evm.

The defined syntax is for only the parts of the yul / evm execution model that are quirky or make
defining a compiler correctness statement tricky.

This means that in addition to the core basic control flow ops and data regions we define:

- calls to the `gas()` opcode
- divergence (infinite loops + recursion)
- contract creation
- calls to external code
- code reads (both self and external)
- load / set immutable
- datacopy
- data objects and data offsets
- memoryguard
- verbatim
- library linking

## Design Goals

The intention here is to gather evidence to support a choice of semantic style for yul and the evm
that support the construction of a verified compiler. The design priorities are:

1. completeness: we should be able to support compilation of the vast majority of existing solidity code
2. auditability: the core trusted semantics and compiler correctness statement should simple and easy to audit and understand
3. proof efficiency: the define semantics should support efficient and modular proofs about
   compiler passes, reasoning should be local, and vertical modularity is of critical importance
   (i.e. we should be able to insert, drop and reorder compiler passes without having to change our proofs).

## What Does Compiler Correctness Mean

When we compile a yul program to EVM we wish to preserve some of the semantics (e.g. control flow,
variable assignment, return values, storage updates), while allowing modifications to others to
allow for optimization (e.g. instruction order, gas costs, memory layouts, ...).

At a very high level we generally wish to preserve most externally observable effects (modulo gas
costs), while giving the compiler freedom to make changes to the program semantics that can only be
observed from within a call.

## Contents

So far the repo contains syntax for the Yul and EVM subsets we are interested
in specifying here. Round trip theorems are proved for the printer / parser
pairs for both Yul and the EVM. Both parsers are fuzzed against solc.

The Yul syntax additionally defines a {lean}`Yul.Object.WellFormed` relation that encodes
the additional non structural restrictions on the grammar. The Yul parser is
proved to only ever produce well formed Yul.
-/
