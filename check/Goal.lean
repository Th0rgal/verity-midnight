import Midnight

-- Both claims must be proved about the exact imported model.
example : Midnight.Spec.TickLibImport.tickToPriceIsMonotonic :=
  Midnight.TickLibImport.tickToPriceIsMonotonic
example : Midnight.Spec.TickLibImport.tickToPriceSucceeds :=
  Midnight.TickLibImport.tickToPriceSucceeds

#print axioms Midnight.TickLibImport.tickToPriceIsMonotonic
#print axioms Midnight.TickLibImport.tickToPriceSucceeds
#print axioms tickLib.covered
