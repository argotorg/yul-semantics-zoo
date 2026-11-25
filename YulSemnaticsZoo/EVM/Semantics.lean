import YulSemnaticsZoo.EVM.Semantics.Clocked.Step
import YulSemnaticsZoo.EVM.Semantics.Clocked.Gas
import YulSemnaticsZoo.EVM.Semantics.Clocked.Refinement

set_option doc.verso true

/-!
# EVM: semantics

The pages under *Semantics*, *Clocked*:

- *Semantics*: a clocked interpreter with one step function and a gas model as a parameter, the
  abstract gas model, and the relation {lit}`⟪code, i, ρ⟫ ⇝ b`.
- *Concrete gas*: the real gas costs. {lit}`lake test` fuzzes them against {lit}`evm run` of geth.
- *Refinement*: obligation 3 of {lit}`doc/gas-equivalence.md`, proven as {lit}`EVM.refines`. If
  the concrete run halts with a result, then the abstract run with the readings of the concrete
  run halts with the same result.
-/
