import Midnight.Lemmas.TickCore

open Compiler.CompilationModel.Denote

namespace Midnight.TickLibImport.Core

theorem chunk32 (o : DenoteOracle) (w : Verity.ContractState) :
    monoFrom o w 101 3200 0 = true := by kernel_rfl

end Midnight.TickLibImport.Core
