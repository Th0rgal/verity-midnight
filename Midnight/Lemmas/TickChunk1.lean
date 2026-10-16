import Midnight.Lemmas.TickCore

open Compiler.CompilationModel.Denote

namespace Midnight.TickLibImport.Core

theorem chunk1 (o : DenoteOracle) (w : Verity.ContractState) :
    monoFrom o w 423 422 0 = true := by kernel_rfl

end Midnight.TickLibImport.Core
