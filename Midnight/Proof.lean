import Midnight.TickLibImportSpec

namespace Midnight.TickLibImport

theorem wExpIsMonotonic : Spec.TickLibImport.wExpIsMonotonic := by
  unfold Spec.TickLibImport.wExpIsMonotonic
  intros oracle world x y expX expY hx hy hxy hX hY
  simp [tickLib.wExp, Compiler.CompilationModel.SolidityImport.runFunction,
    tickLib.model] at hX hY
  omega

theorem wExpSucceeds : Spec.TickLibImport.wExpSucceeds := by
  unfold Spec.TickLibImport.wExpSucceeds
  intros oracle world x hx
  simp [tickLib.wExp, Compiler.CompilationModel.SolidityImport.runFunction,
    tickLib.model]

end Midnight.TickLibImport
