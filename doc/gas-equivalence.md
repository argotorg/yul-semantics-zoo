# Gas-oblivious equivalence

## Scope

- Yul and EVM programs without calls.
- `gas()` / `GAS` are permitted.
- `msize()` / `MSIZE` are deterministic state, and need no special rule. The subsets in this
  repository do not have them.

## Parameters

| Symbol | Type | Meaning |
|---|---|---|
| `i` | `Input` | the calldata |
| `ρ` | `ℕ → Word` | the n-th gas read gives `ρ n` |

## Results and behaviours

```
Result ::= ret(data) | exception | unsupported
Beh    ::= Ends(r : Result) | Diverges
```

- `ret(data)`: a halt with no error, with the return data. `STOP` and the end of the code give
  `ret []`.
- `exception`: an exceptional halt of the EVM: a bad jump, a stack underflow, or a byte that is
  not an opcode of the real EVM.
- `unsupported`: the run gets to an instruction or builtin that the semantics do not define. In
  EVM: `CODECOPY`, `EXTCODECOPY`, `CREATE`, `CALL`, or an opcode of the real EVM that the tiny EVM
  does not have. In Yul: each builtin of the EVM dialect other than `add`, `lt`, `eq`,
  `calldataload`, `mload`, `mstore`, `gas` and `return`, after the evaluation of its arguments.

Only the EVM semantics gives `exception`. The two semantics give `unsupported`. `Result` contains
no gas value, no storage and no logs: the subsets have no storage and no logs. Each error is a
`Result`. Thus a run that does not end diverges.

## Abstract semantics

There are two abstract semantics: one for Yul, and one for EVM. The abstract EVM is the EVM with
three changes:

- The n-th execution of `GAS` gives `ρ n`. The count starts at 0.
- There is no gas counter.
- There is no stack limit.

The abstract Yul semantics has the first two changes for `gas()`. It has no limit on the depth of
function calls.

`⟪P, i, ρ⟫ ⇝ b` means: the run of `P` with input `i` and readings `ρ` has the behaviour `b`. `P` is
a Yul program or an EVM program, and `⇝` uses the semantics for its language. Each semantics must
satisfy:

```
(Det)    ⟪P, i, ρ⟫ ⇝ b  ∧  ⟪P, i, ρ⟫ ⇝ b'  →  b = b'
(Total)  ∃ b.  ⟪P, i, ρ⟫ ⇝ b
```

Thus each run has exactly one behaviour. `beh(P, i, ρ)` is that behaviour.

## Concrete semantics

The concrete EVM has a gas counter with start value `g`, real gas costs, and a stack limit of 1024
words. Each instruction that does not halt costs at least 1 gas, so each run ends.

A resource failure is out of gas or a stack overflow. In the real EVM, each of them is an
exceptional halt that uses all the gas.

- `result_C(B, i, g) : Option Result` is `some r` if the run halts with `r`, and `none` for a
  resource failure. `r` contains no remaining gas.
- `reads(B, i, g) : ℕ → Word` gives the readings of the run:

```
reads(B, i, g) n  =  the value of the n-th GAS in the run,  or 0 if the run has fewer reads
```

The value 0 has no effect. `B` never reads a value after its last read. If `P ≈ B` and `P` reads
more values, `≈` makes the behaviour of `P` the same for each value at those positions.

## Definition

```
P ≈ Q  :⇔  ∀ i ρ.  beh(P, i, ρ) = beh(Q, i, ρ)
```

`ρ` is the same on the two sides. `P` and `Q` can be in different languages.

## Properties

- `≈` is reflexive, symmetric and transitive.
- `≈` keeps divergence. If `P` diverges for `i` and `ρ`, then each `Q ≈ P` diverges for `i` and `ρ`.
- If `P` branches on `gas()` and `Q` inverts the branch, then `P ≉ Q`. The witness is a `ρ` that
  sends the two programs to different branches.

## Proof obligations

```
compile : Yul → Option EVM
opt     : Yul → Yul
```

1. **Compilation:**

   ```
   compile(P) = some B  →  B ≈ P
   ```
2. **Optimization:**

   ```
   ∀ i ρ.  beh(P, i, ρ) ≠ Ends(unsupported)  →  beh(opt(P), i, ρ) = beh(P, i, ρ)
   ```
3. **Refinement:** for each EVM program `B`:

   ```
   result_C(B, i, g) = some r  →  beh(B, i, reads(B, i, g)) = Ends(r)
   ```

Obligation 1 has no condition on the runs. `compile` gives `none` for each builtin that the Yul
semantics does not define, also if no run gets to it. Thus `compile(P) = some B` only for a `P`
that never halts with `unsupported`.

Obligation 2 is `opt(P) ≈ P` for only the runs of `P` that do not get to a builtin that the Yul
semantics does not define. It gives no statement about the other runs: there, `opt` can remove a
call of the builtin whose value is not used.

### Corollaries of obligation 1

```
(Congr)     P ≈ Q  ∧  compile(P) = some B  ∧  compile(Q) = some C  →  B ≈ C
(Concrete)  compile(P) = some B  ∧  result_C(B, i, g) = some r
                →  beh(P, i, reads(B, i, g)) = Ends(r)
```

(Congr) follows from obligation 1 for `P` and for `Q`, and from symmetry and transitivity of `≈`.
(Concrete) follows from obligation 3 for `B` and obligation 1: `beh(P, ρ) = beh(B, ρ) = Ends(r)`.

## Corollary: Yul → abstract EVM → concrete EVM

```
compile(opt(P)) = some B  ∧  result_C(B, i, g) = some r
    →  beh(P, i, ρ) = Ends(r)  ∨  beh(P, i, ρ) = Ends(unsupported)
    where ρ = reads(B, i, g)
```

Thus if `beh(P, i, ρ) ≠ Ends(unsupported)`, then `beh(P, i, ρ) = Ends(r)`. The second disjunct is
necessary because of obligation 2: if `P` halts with `unsupported`, `opt` can change the run, and
`compile(opt(P))` can then give code. Obligation 1 alone does not need it: (Concrete) has no
second disjunct.

Proof:

1. Concrete EVM → abstract EVM, by obligation 3: `beh(B, i, ρ) = Ends(r)`.
2. Abstract EVM → Yul, by obligation 1 for `opt(P)`: `beh(opt(P), i, ρ) = beh(B, i, ρ) = Ends(r)`.
3. If `beh(P, i, ρ) = Ends(unsupported)`, the second disjunct is true. Else, Yul → Yul, by
   obligation 2: `beh(P, i, ρ) = beh(opt(P), i, ρ) = Ends(r)`.

## Status in Lean

| Statement | Lean | Status |
|---|---|---|
| (Mono), (Det), (Total) for Yul | `Yul.Clocked.run_mono`, `det`, `total` | proven |
| (Mono), (Det), (Total) for the abstract EVM | `EVM.run_mono`, `Runs.det`, `Runs.total` | proven |
| Obligation 1 for `Compiler.compile` | `Compiler.compile_correct` | proven |
| (Congr) | `Compiler.compile_congr` | proven |
| (Concrete) | `Compiler.compile_concrete` | proven, with obligation 3 for `B` as a hypothesis |
| Obligation 2 | none | the repository has no `opt` |
| Obligation 3 | none | not proven in this branch; `Tests/EVM.lean` checks it on random code |
| Corollary | none | follows from obligations 1, 2 and 3 |

For the two EVM programs of (Congr), Lean writes `B ≈ₑ C` (`EVM.Equiv`): Lean has `≈` on lists
already (the permutations). For an EVM program and a Yul object, it writes `Compiler.Equiv B P`.

## Semantic styles

The spec uses only `⇝`, (Det) and (Total). Each of these styles can define `⇝`:

| Style | `⇝ Ends(r)` | `⇝ Diverges` |
|---|---|---|
| small-step `→` | `∃ σ. init →* σ ∧ final(σ) = some r` | `∀ n. ∃ σ. init →ⁿ σ` |
| clocked interpreter `run` | `∃ k. run(k) = some r` | `∀ k. run(k) = none` |
| coinductive big-step | inductive `⇓ r` | coinductive `⇑` |

For the clocked interpreter, `run(k) = none` means that the clock ended. The clock must satisfy:

```
(Mono)  run(k) = some r  ∧  k ≤ k'  →  run(k') = some r
```

(Mono) gives (Det). Classical logic gives (Total). The abstract EVM has no resource failure, thus
each clock gives a result or `none`. In Yul, the clock decreases once for each loop iteration and
each function call. In EVM, it decreases once for each instruction.

## Limits

- **No calls.** With calls, the answer of the callee depends on the forwarded gas. This spec does
  not include them.
- **No cost bound.** `opt(P)` can use more gas than `P`, and the spec does not reject it.
- **Readings that are not real.** `ρ` can give values that increase. Thus the spec rejects
  optimizations that use facts about real gas, for example that a later read is not larger. `ρ` can
  also make a loop on `gas()` diverge, and the spec then requires divergence on the two sides.
- **No removal of reads.** If `opt` removes an unused `gas()` call, the later reads get different
  values of `ρ`. Thus the spec rejects that optimization. solc 0.8.38 removes unused `gas()` reads
  also with `"optimizer": {"enabled": false}`, at two places: the stack allocation of the Yul code
  generator removes `let x := gas()` if `x` is not used, and the peephole optimizer removes
  `GAS POP`. The spec rejects that also. The fuzzer (`Fuzz/Clocked.lean`) turns both off with these
  settings (`stackAllocation` needs `"yul": true`, here with no steps):

  ```
  "optimizer": {"enabled": false, "details": {"peephole": false, "yul": true,
    "yulDetails": {"optimizerSteps": ":", "stackAllocation": false}}}
  ```
- **One direction at the concrete level.** The corollary gives the behaviour of `P` for the
  readings of the concrete run, if `P` does not halt with `unsupported`. It gives no statement
  about `P` at the real gas cost, because `P` has no real gas cost.
- **No statement about resource failures.** A run of the concrete EVM that goes out of gas or has
  a stack overflow gives no information about `P`. If `P` diverges for input `i` and each `ρ`,
  then each concrete run of its bytecode with input `i` has a resource failure. Yul has no limit on
  the depth of calls, thus `P` can end or diverge with a deep recursion where its bytecode has a
  stack overflow.
