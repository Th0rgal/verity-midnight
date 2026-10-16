import Midnight.TickLibImportSpec

set_option maxHeartbeats 2000000

namespace Midnight.TickLibImport

theorem wExpIsMonotonic : Spec.TickLibImport.wExpIsMonotonic := by
  unfold Spec.TickLibImport.wExpIsMonotonic
  intros oracle world x y expX expY hx hy hxy hX hY
  grind [tickLib.wExp, Compiler.CompilationModel.SolidityImport.runFunction,
    Compiler.CompilationModel.SolidityImport.functionBody,
    Compiler.CompilationModel.SolidityImport.functionBody.go, tickLib.model]

theorem wExpSucceeds : Spec.TickLibImport.wExpSucceeds := by
  unfold Spec.TickLibImport.wExpSucceeds
  intros oracle world x hx
  grind [tickLib.wExp, Compiler.CompilationModel.SolidityImport.runFunction,
    Compiler.CompilationModel.SolidityImport.functionBody,
    Compiler.CompilationModel.SolidityImport.functionBody.go, tickLib.model]

end Midnight.TickLibImport
