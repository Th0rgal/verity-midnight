# Prove the imported original `wExp` properties

Prove both frozen statements in `Midnight/TickLibImportSpec.lean`:

1. `Midnight.Spec.TickLibImport.wExpIsMonotonic`: for signed inputs `x > y`,
   both in `[-maxInput, maxInput]`, successful outputs satisfy
   `wExp(x) >= wExp(y)`.
2. `Midnight.Spec.TickLibImport.wExpSucceeds`: every input in that range
   succeeds, ruling out vacuous monotonicity caused by reverts.

`Midnight/TickLibImport.lean` uses `solidity_import` to generate
`tickLib.model` and `tickLib.wExp` from the unmodified
`vendor/midnight/src/libraries/TickLib.sol`, through the harness
`vendor/midnight/certora/helpers/TickLibWrapper.sol`. Reason about that
generated model. `maxInput = 4987541511039073 * (6744 / 2)`; the range
contains every integer in the interval. No equivalence proof to the
Solidity is required.

Produce proofs that `./check/check_proof.sh` accepts.

## What you may edit

- `Midnight/Proof.lean`
- New files under `Midnight/`, including `Midnight/Lemmas/`

## What you may not edit

- Existing files under `Midnight/` other than `Midnight/Proof.lean`
- `Midnight.lean`, `lakefile.lean`, `lake-manifest.json`, `lean-toolchain`
- `README.md`, `AGENTS.md`, `vendor/`, `solidity/`, `check/`

The Solidity, the import and the specification are frozen. Do not replace the
imported model or weaken either statement or its input range.

## What counts as done

`./check/check_proof.sh` exits 0. It checks the frozen files, builds the
library, checks both theorem types, and audits both proofs and
`tickLib.covered`. Only `propext`, `Classical.choice`, and `Quot.sound`
are allowed. `sorry`, `admit`, extra axioms, and `native_decide` are rejected.

lean-lsp MCP is required. Follow `AGENTS.md`; if it is unavailable, write
`out/mcp-unavailable` and stop.

## Loop

```sh
lake build Midnight.Proof
./check/check_proof.sh
```

Work only in this directory. Do not read parent directories or other checkouts.
Do not look up published proofs on GitHub or in git history.
