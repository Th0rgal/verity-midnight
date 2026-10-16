import Lake
open Lake DSL

package «morpho-midnight-verity» where
  version := v!"0.1.0"

require verity from git "https://github.com/lfglabs-dev/verity" @ "10f697bbb52dd9273591490137fe20593db56dde"

/-- The Solidity read by `solidity_import`: editing it rebuilds the import. -/
input_dir midnightSol where
  path := "vendor/midnight/src"
  filter := .extension "sol"
  text := true

/-- Morpho's Certora harness exposing the original `TickLib` functions. -/
input_dir midnightHarnessSol where
  path := "vendor/midnight/certora/helpers"
  filter := .extension "sol"
  text := true

/-- The standalone positive exponential read by `solidity_import`. -/
input_dir positiveTickSol where
  path := "solidity"
  filter := .extension "sol"
  text := true

@[default_target]
lean_lib «Midnight» where
  globs := #[.andSubmodules `Midnight]
  needs := #[midnightSol, midnightHarnessSol, positiveTickSol]
