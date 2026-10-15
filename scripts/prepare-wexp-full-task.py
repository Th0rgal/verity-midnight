#!/usr/bin/env python3
"""Select an imported original-TickLib task in a fresh experiment run.

`wexp-full` (default): monotonicity and success of the original signed
`TickLib.wExp(int256)` imported through Verity. `ticktoprice`: monotonicity and
success of the original `TickLib.tickToPrice(uint256)` from the same import.
"""

import hashlib
from pathlib import Path
import re
import runpy
import sys

COMMON_RULES = """Produce proofs that `./check/check_proof.sh` accepts.

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
"""

TASKS = {
    "wexp-full": {
        "theorems": ["wExpIsMonotonic", "wExpSucceeds"],
        "readme": """# Prove the imported original `wExp` properties

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

""",
    },
    "ticktoprice": {
        "theorems": ["tickToPriceIsMonotonic", "tickToPriceSucceeds"],
        "readme": """# Prove the imported original `tickToPrice` properties

Prove both frozen statements in `Midnight/TickLibImportSpec.lean`:

1. `Midnight.Spec.TickLibImport.tickToPriceIsMonotonic`: for ticks
   `tick1 < tick2 <= MAX_TICK`, successful outputs satisfy
   `tickToPrice(tick1) <= tickToPrice(tick2)`.
2. `Midnight.Spec.TickLibImport.tickToPriceSucceeds`: every tick
   `<= MAX_TICK` succeeds, ruling out vacuous monotonicity caused by reverts.

`Midnight/TickLibImport.lean` uses `solidity_import` to generate
`tickLib.model` and `tickLib.tickToPrice` from the unmodified
`vendor/midnight/src/libraries/TickLib.sol`, through the harness
`vendor/midnight/certora/helpers/TickLibWrapper.sol`. Reason about that
generated model. `MAX_TICK = 6744`. No equivalence proof to the Solidity is
required.

""",
    },
}


def prepare(root: Path, task: str = "wexp-full") -> None:
    spec = TASKS[task]
    base = runpy.run_path(str(Path(__file__).with_name("prepare-wexp-task.py")))
    base["prepare"](root)
    names = spec["theorems"]
    proof = "import Midnight.TickLibImportSpec\n\nnamespace Midnight.TickLibImport\n\n"
    for name in names:
        proof += f"theorem {name} : Spec.TickLibImport.{name} := by\n  sorry\n\n"
    proof += "end Midnight.TickLibImport\n"
    goal = "import Midnight\n\n-- Both claims must be proved about the exact imported model.\n"
    for name in names:
        goal += (f"example : Midnight.Spec.TickLibImport.{name} :=\n"
                 f"  Midnight.TickLibImport.{name}\n")
    goal += "\n"
    for name in names:
        goal += f"#print axioms Midnight.TickLibImport.{name}\n"
    goal += "#print axioms tickLib.covered\n"
    overrides = {
        "Midnight/Proof.lean": proof,
        "Midnight.lean": "import Midnight.TickLibImportSpec\nimport Midnight.Proof\n",
        "check/Goal.lean": goal,
        "README.md": spec["readme"] + COMMON_RULES,
    }
    for rel, contents in overrides.items():
        (root / rel).write_text(contents)

    axioms = root / "check/check_axioms.py"
    expected = "".join(f'"Midnight.TickLibImport.{name}",\n    ' for name in names)
    contents = axioms.read_text().replace(
        '"Midnight.wExpIsMonotonic",',
        expected + '"tickLib.covered",',
    )
    axioms.write_text(contents)
    smoke = root / "scripts/check-lean-mcp.py"
    smoke.write_text(smoke.read_text().replace(
        '"file_path": "Midnight/TickLibSpec.lean"',
        '"file_path": "Midnight/TickLibImportSpec.lean"',
    ))

    checker = root / "check/check_frozen.py"
    contents = checker.read_text()
    for rel in [*overrides, "check/check_axioms.py", "scripts/check-lean-mcp.py"]:
        digest = hashlib.sha256((root / rel).read_bytes()).hexdigest()
        pattern = rf"('{re.escape(rel)}': ')[0-9a-f]{{64}}(')"
        contents, count = re.subn(pattern, rf"\g<1>{digest}\g<2>", contents)
        if count != 1:
            raise RuntimeError(f"Expected one digest for {rel}, got {count}")
    checker.write_text(contents)


if __name__ == "__main__":
    prepare(Path(sys.argv[1]).resolve(), sys.argv[2] if len(sys.argv) > 2 else "wexp-full")
