import Midnight.Lemmas.TickCore

open Compiler.CompilationModel.Denote

namespace Midnight.TickLibImport.Core

theorem chunk24 (o : DenoteOracle) (w : Verity.ContractState) :
    monoFrom o w 101 2400 0 = true := by kernel_rfl

end Midnight.TickLibImport.Core
