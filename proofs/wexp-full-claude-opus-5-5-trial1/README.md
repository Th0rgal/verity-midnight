# `wexp-full` trial 1: Claude Opus 5.5

Agent-produced proof of `Midnight.Spec.TickLibImport.wExpIsMonotonic` and
`Midnight.Spec.TickLibImport.wExpSucceeds` for the original signed
`TickLib.wExp(int256)`, imported unmodified via `solidity_import`.

| | |
|---|---|
| Model | `claude-opus-5-5`, effort `high` |
| Proof phase (agent wall time, `end - start`) | 13,091 s (3 h 38 min) |
| Lean/`lake build` iterations | ~55, plus 1 `check_proof.sh` run |
| lean-lsp MCP | installed but not registered; shell-only `lake env lean` |
| Machine load during trial | load average ~25 on 8 cores (shared) |
| Axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Independent re-check | `check/check_proof.sh` exit 0 on a fresh task copy |
| Re-check cost of the proof files | ~50 s cumulative elaboration on a loaded machine |

Not run inside the Docker/egress-proxy harness (no Docker access on the trial
host). The agent was instructed not to read git history or search the web;
its transcript was not audited with `scripts/audit_transcripts.py`.

## Proof structure

1. `Lemmas/Body.lean`, `Exec.lean`, `Reduce.lean`: the imported body, shown
   equal to the model by `rfl`, executed statement by statement.
2. `Lemmas/Bridge.lean`: 256-bit word operations ↔ integers on the input range.
3. `Lemmas/Math.lean`: the cubic Taylor polynomial is non-decreasing within a
   segment; segment boundaries are discharged by `decide`.
4. `Lemmas/Final.lean`: closed form `wExp x = posI x` (x ≥ 0) and
   `1e36 / posI (-x)` (x < 0); monotonicity by sign cases, success because
   `posI ≥ 1e18 > 0` and every intermediate stays in range.
