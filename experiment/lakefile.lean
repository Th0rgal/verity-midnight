import Lake
open Lake DSL

package «morpho-midnight-verity» where
  version := v!"0.1.0"

require verity from git "https://github.com/lfglabs-dev/verity" @ "9b472a8a48a9990337845f1720a20f374fa1e9cd"

/-- The Solidity read by `solidity_import`: editing it rebuilds the import. -/
input_dir midnightSol where
  path := "vendor/midnight/src"
  filter := .extension "sol"
  text := true

/-- The standalone positive exponential read by `solidity_import`. -/
input_dir positiveTickSol where
  path := "solidity"
  filter := .extension "sol"
  text := true

/-- Generic lemmas for symbolic execution of `solidity_import` models. -/
lean_lib «ProofKit» where
  globs := #[.andSubmodules `ProofKit]

@[default_target]
lean_lib «Midnight» where
  globs := #[.andSubmodules `Midnight]
  needs := #[midnightSol, positiveTickSol]
