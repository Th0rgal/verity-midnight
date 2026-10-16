import Compiler.SolidityImport.Import

/-!
Import the original signed `TickLib.wExp(int256)` and `TickLib.tickToPrice(uint256)`
from `vendor/midnight/src/libraries/TickLib.sol`, unmodified.

`solidity_import` imports external functions of a contract, so the entry point is
Morpho's own Certora harness `vendor/midnight/certora/helpers/TickLibWrapper.sol`,
whose `wExp` and `tickToPrice` are one-line external wrappers forwarding to the
internal library functions. The compiler settings match
`vendor/midnight/certora/confs/TickToPrice.conf` (solc 0.8.34, via-IR, osaka) and
the main import in `Midnight/Import.lean`.

The importer creates `tickLib.model`, `tickLib.covered`, `tickLib.sourceDigest`,
`tickLib.wExp : DenoteOracle → ContractState → Int256 → Option Uint256` and
`tickLib.tickToPrice : DenoteOracle → ContractState → Uint256 → Option Uint256`.
There is no handwritten Lean implementation of the exponential here.
-/

solidity_import tickLib from "vendor/midnight" entry "certora/helpers/TickLibWrapper.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract TickLibWrapper
  function wExp(int256)
  function tickToPrice(uint256)
