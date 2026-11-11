# yul-semnatics-zoo

This repository defines syntax and semantics for two cut down versions of both yul and the evm. The
goal is to explore which semantic styles are best suited for a compiler correctness theorem between
yul and the evm.

It is defined as a literate [verso](https://verso.lean-lang.org/) document. The `main` branch is
published at https://argotorg.github.io/yul-semantics-zoo.

## Developing

The tools come from the nix devshell: run `nix develop`, or `direnv allow` to use the `.envrc`. It
has `elan` (and so Lean and Lake), `solc`, `geth` and `serve-docs`.

- `lake build`: build the library and check its proofs.
- `lake test`: check the proofs and tests, then fuzz the EVM encoding and the Yul parser against
  `solc`. `lake test -- 1000 42` runs 1000 fuzz cases from seed 42. CI runs `lake --wfail test`,
  which also fails on warnings.
- `serve-docs`: build the literate document, serve it at http://localhost:8000, and rebuild and
  reload it when a source changes. `lake query :literateHtml` only builds it and prints its path.
