import Midnight.Lemmas.TickCore

open Compiler.CompilationModel.Denote

namespace Midnight.TickLibImport.Core

theorem chunk2 (o : DenoteOracle) (w : Verity.ContractState) :
    monoFrom o w 423 844 0 = true := by kernel_rfl

end Midnight.TickLibImport.Core
