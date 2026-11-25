# Gas-oblivious equivalence

## Scope

- Yul and EVM programs without calls.
- `gas()` / `GAS` are permitted.
- `msize()` / `MSIZE` are deterministic state, and need no special rule.

## Parameters

| Symbol | Type | Meaning |
|---|---|---|
| `i` | `Input` | calldata and start storage |
| `ρ` | `ℕ → Word` | the n-th gas read gives `ρ n` |

## Results and behaviours

```
Result ::= Halt(status, returndata, storage, logs)
Beh    ::= Ends(r : Result) | Diverges
```

`Result` contains no gas value. Each error, for example a stack underflow, is a `Halt` with a
status. Thus a run that does not end diverges.

## Abstract semantics

There are two abstract semantics: one for Yul, and one for EVM. The abstract EVM is the EVM with
two changes:

- The n-th execution of `GAS` gives `ρ n`. The count starts at 0.
- There is no gas counter.

The abstract Yul semantics has the same two changes for `gas()`.

`P, i, ρ ⇝ b` means: the run of `P` with input `i` and readings `ρ` has the behaviour `b`. `P` is a
Yul program or an EVM program, and `⇝` uses the semantics for its language. Each semantics must
satisfy:

```
(Det)    P, i, ρ ⇝ b  ∧  P, i, ρ ⇝ b'  →  b = b'
(Total)  ∃ b.  P, i, ρ ⇝ b
```

Thus each run has exactly one behaviour. `beh(P, i, ρ)` is that behaviour.

## Concrete semantics

The concrete EVM has a gas counter with start value `g`, and real gas costs. Each non-terminal
instruction costs at least 1 gas, so each run ends.

- `result_C(B, i, g) : Option Result` is `some r` if the run halts with `r`, and `none` if it goes
  out of gas. `r` contains no remaining gas.
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
compile : Yul → EVM
opt     : Yul → Yul
```

1. **Compilation:** `compile(P) ≈ P`.
2. **Optimization:** `opt(P) ≈ P`.
3. **Refinement:** for each EVM program `B`:

   ```
   result_C(B, i, g) = some r  →  beh(B, i, reads(B, i, g)) = Ends(r)
   ```

## Corollary: Yul → abstract EVM → concrete EVM

```
result_C(compile(opt(P)), i, g) = some r  →  beh(P, i, ρ) = Ends(r)
    where ρ = reads(compile(opt(P)), i, g)
```

Proof:

1. Concrete EVM → abstract EVM, by obligation 3: `beh(compile(opt(P)), i, ρ) = Ends(r)`.
2. Abstract EVM → Yul, by obligation 1: `beh(opt(P), i, ρ) = Ends(r)`.
3. Yul → Yul, by obligation 2: `beh(P, i, ρ) = Ends(r)`.

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

(Mono) gives (Det). Classical logic gives (Total). In Yul, the clock decreases once for each loop
iteration and each function call. In EVM, it decreases once for each instruction.

## Limits

- **No calls.** With calls, the answer of the callee depends on the forwarded gas. This spec does
  not include them.
- **No cost bound.** `opt(P)` can use more gas than `P`, and the spec does not reject it.
- **Readings that are not real.** `ρ` can give values that increase. Thus the spec rejects
  optimizations that use facts about real gas, for example that a later read is not larger. `ρ` can
  also make a loop on `gas()` diverge, and the spec then requires divergence on the two sides.
- **No removal of reads.** If `opt` removes an unused `gas()` call, the later reads get different
  values of `ρ`. Thus the spec rejects that optimization.
- **One direction at the concrete level.** The corollary gives the behaviour of `P` for the
  readings of the concrete run. It gives no statement about `P` at the real gas cost, because `P`
  has no real gas cost.
- **No statement about OOG.** An `OOG` run of the concrete EVM gives no information about `P`. If
  `P` diverges, each concrete run of its bytecode goes `OOG`.
