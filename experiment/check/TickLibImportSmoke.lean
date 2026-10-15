import Midnight.TickLibImportSpec

open Compiler.CompilationModel.Denote
open Verity.Core

private def oracle : DenoteOracle where
  mappingSlot _ _ := 0
  keccakMemorySlice _ _ _ := 0

/-! Exercise the generated functions, not a separate Lean implementation.
Expected values are EVM results of `TickLibWrapper` compiled with solc 0.8.34
(via-IR, osaka, 466 optimizer runs) and executed by `forge test`. -/

private def wExpSamples : List (Int × Nat) :=
  [(-16817989975223754156, 49665761238),
   (-693147180559945309, 500000000000000000),
   (-1, 999999999999999999),
   (0, 1000000000000000000),
   (1, 1000000000000000001),
   (370535965570485438, 1447663323139670138),
   (370535965570485439, 1447663323139670138),
   (1063683146130430747, 2895326646279340276),
   (1063683146130430748, 2895326646279340276),
   (693147180559945309, 2000000000000000000),
   (1000000000000000000, 2717495241040366476),
   (16817989975223754156, 20134595243400876315901952)]

private def tickToPriceSamples : List (Nat × Nat) :=
  [(0, 0), (1, 0), (3371, 498753100000000000), (3372, 500000000000000000),
   (3373, 501246900000000000), (6743, 1000000000000000000),
   (6744, 1000000000000000000)]

private def checkSamples : IO Unit := do
  for (input, expected) in wExpSamples do
    let actual := tickLib.wExp oracle Verity.defaultState (Int256.ofInt input)
    unless actual.map (·.val) == some expected do
      throw (IO.userError s!"Imported wExp({input}) returned {repr actual}; expected {expected}")
  for (tick, expected) in tickToPriceSamples do
    let actual := tickLib.tickToPrice oracle Verity.defaultState (Uint256.ofNat tick)
    unless actual.map (·.val) == some expected do
      throw (IO.userError s!"Imported tickToPrice({tick}) returned {repr actual}; expected {expected}")
  -- Both revert in the EVM: unbounded recursion at int256.min, TickOutOfRange above MAX_TICK.
  unless (tickLib.wExp oracle Verity.defaultState (Int256.ofInt (-2 ^ 255))).isNone do
    throw (IO.userError "Imported wExp(type(int256).min) did not revert")
  unless (tickLib.tickToPrice oracle Verity.defaultState (Uint256.ofNat 6745)).isNone do
    throw (IO.userError "Imported tickToPrice(6745) did not revert")
  IO.println "Imported TickLib smoke tests passed (wExp: negative, zero, positive, segment boundaries, range ends; tickToPrice: ends, midpoint; reverts)"

#eval checkSamples

#print axioms tickLib.covered
