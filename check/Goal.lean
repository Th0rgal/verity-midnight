import Midnight

-- Both claims must be proved about the exact imported model.
example : Midnight.Spec.TickLibImport.wExpIsMonotonic :=
  Midnight.TickLibImport.wExpIsMonotonic
example : Midnight.Spec.TickLibImport.wExpSucceeds :=
  Midnight.TickLibImport.wExpSucceeds

#print axioms Midnight.TickLibImport.wExpIsMonotonic
#print axioms Midnight.TickLibImport.wExpSucceeds
#print axioms tickLib.covered
