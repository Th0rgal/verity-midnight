import Midnight.TickLibImportSpec

/-! The body of the imported `wExp`, restated to drive symbolic execution. -/

open Compiler.CompilationModel Compiler.CompilationModel.Denote Compiler.CompilationModel.SolidityImport
open Verity.Core

namespace Midnight.TickLibImport

def wExpBody : List Stmt :=
  [Stmt.letVar
     "_verity_slice_tmp_0"
     (Expr.slt
       (Expr.param "x")
       (Expr.literal 0)),
   Stmt.letVar "_verity_slice_tmp_22" (Expr.literal 0),
   Stmt.ite
     (Expr.localVar "_verity_slice_tmp_0")
     [Stmt.letVar
        "_verity_slice_tmp_1"
        (Expr.sub
          (Expr.literal 0)
          (Expr.param "x")),
      Stmt.ite
        (Expr.slt
          (Expr.localVar "_verity_slice_tmp_1")
          (Expr.literal 0))
        [Stmt.revertReturndata]
        [],
      Stmt.letVar "ln2" (Expr.literal 693147180559945309),
      Stmt.letVar "offset" (Expr.literal 322611214989459870),
      Stmt.letVar
        "_verity_slice_tmp_2"
        (Expr.add
          (Expr.localVar "_verity_slice_tmp_1")
          (Expr.localVar "offset")),
      Stmt.letVar "_verity_slice_tmp_3" (Expr.literal 0),
      Stmt.ite
        (Expr.eq
          (Expr.localVar "ln2")
          (Expr.literal 0))
        [Stmt.panic (PanicCode.divisionByZero)]
        [Stmt.assignVar
           "_verity_slice_tmp_3"
           (Expr.sdiv
             (Expr.localVar "_verity_slice_tmp_2")
             (Expr.localVar "ln2"))],
      Stmt.letVar "q" (Expr.localVar "_verity_slice_tmp_3"),
      Stmt.letVar
        "_verity_slice_tmp_4"
        (Expr.mul
          (Expr.localVar "q")
          (Expr.localVar "ln2")),
      Stmt.letVar
        "r"
        (Expr.sub
          (Expr.localVar "_verity_slice_tmp_1")
          (Expr.localVar "_verity_slice_tmp_4")),
      Stmt.letVar
        "_verity_slice_tmp_5"
        (Expr.mul
          (Expr.localVar "r")
          (Expr.localVar "r")),
      Stmt.letVar "_verity_slice_tmp_6" (Expr.literal 0),
      Stmt.ite
        (Expr.eq
          (Expr.literal 2000000000000000000)
          (Expr.literal 0))
        [Stmt.panic (PanicCode.divisionByZero)]
        [Stmt.assignVar
           "_verity_slice_tmp_6"
           (Expr.sdiv
             (Expr.localVar "_verity_slice_tmp_5")
             (Expr.literal 2000000000000000000))],
      Stmt.letVar "secondTerm" (Expr.localVar "_verity_slice_tmp_6"),
      Stmt.letVar
        "_verity_slice_tmp_7"
        (Expr.mul
          (Expr.localVar "secondTerm")
          (Expr.localVar "r")),
      Stmt.letVar "_verity_slice_tmp_8" (Expr.literal 0),
      Stmt.ite
        (Expr.eq
          (Expr.literal 3000000000000000000)
          (Expr.literal 0))
        [Stmt.panic (PanicCode.divisionByZero)]
        [Stmt.assignVar
           "_verity_slice_tmp_8"
           (Expr.sdiv
             (Expr.localVar "_verity_slice_tmp_7")
             (Expr.literal 3000000000000000000))],
      Stmt.letVar "thirdTerm" (Expr.localVar "_verity_slice_tmp_8"),
      Stmt.letVar
        "_verity_slice_tmp_9"
        (Expr.add
          (Expr.literal 1000000000000000000)
          (Expr.localVar "r")),
      Stmt.letVar
        "_verity_slice_tmp_10"
        (Expr.add
          (Expr.localVar "_verity_slice_tmp_9")
          (Expr.localVar "secondTerm")),
      Stmt.letVar
        "expR"
        (Expr.add
          (Expr.localVar "_verity_slice_tmp_10")
          (Expr.localVar "thirdTerm")),
      Stmt.letVar
        "_verity_slice_tmp_11"
        (Expr.shl
          (Expr.localVar "q")
          (Expr.localVar "expR")),
      Stmt.letVar "_verity_slice_tmp_12" (Expr.literal 0),
      Stmt.ite
        (Expr.eq
          (Expr.localVar "_verity_slice_tmp_11")
          (Expr.literal 0))
        [Stmt.panic (PanicCode.divisionByZero)]
        [Stmt.assignVar
           "_verity_slice_tmp_12"
           (Expr.div
             (Expr.literal 1000000000000000000000000000000000000)
             (Expr.localVar "_verity_slice_tmp_11"))],
      Stmt.assignVar
        "_verity_slice_tmp_22"
        (Expr.localVar "_verity_slice_tmp_12")]
     [Stmt.letVar "ln2_1" (Expr.literal 693147180559945309),
      Stmt.letVar "offset_1" (Expr.literal 322611214989459870),
      Stmt.letVar
        "_verity_slice_tmp_13"
        (Expr.add
          (Expr.param "x")
          (Expr.localVar "offset_1")),
      Stmt.letVar "_verity_slice_tmp_14" (Expr.literal 0),
      Stmt.ite
        (Expr.eq
          (Expr.localVar "ln2_1")
          (Expr.literal 0))
        [Stmt.panic (PanicCode.divisionByZero)]
        [Stmt.assignVar
           "_verity_slice_tmp_14"
           (Expr.sdiv
             (Expr.localVar "_verity_slice_tmp_13")
             (Expr.localVar "ln2_1"))],
      Stmt.letVar "q_1" (Expr.localVar "_verity_slice_tmp_14"),
      Stmt.letVar
        "_verity_slice_tmp_15"
        (Expr.mul
          (Expr.localVar "q_1")
          (Expr.localVar "ln2_1")),
      Stmt.letVar
        "r_1"
        (Expr.sub
          (Expr.param "x")
          (Expr.localVar "_verity_slice_tmp_15")),
      Stmt.letVar
        "_verity_slice_tmp_16"
        (Expr.mul
          (Expr.localVar "r_1")
          (Expr.localVar "r_1")),
      Stmt.letVar "_verity_slice_tmp_17" (Expr.literal 0),
      Stmt.ite
        (Expr.eq
          (Expr.literal 2000000000000000000)
          (Expr.literal 0))
        [Stmt.panic (PanicCode.divisionByZero)]
        [Stmt.assignVar
           "_verity_slice_tmp_17"
           (Expr.sdiv
             (Expr.localVar "_verity_slice_tmp_16")
             (Expr.literal 2000000000000000000))],
      Stmt.letVar
        "secondTerm_1"
        (Expr.localVar "_verity_slice_tmp_17"),
      Stmt.letVar
        "_verity_slice_tmp_18"
        (Expr.mul
          (Expr.localVar "secondTerm_1")
          (Expr.localVar "r_1")),
      Stmt.letVar "_verity_slice_tmp_19" (Expr.literal 0),
      Stmt.ite
        (Expr.eq
          (Expr.literal 3000000000000000000)
          (Expr.literal 0))
        [Stmt.panic (PanicCode.divisionByZero)]
        [Stmt.assignVar
           "_verity_slice_tmp_19"
           (Expr.sdiv
             (Expr.localVar "_verity_slice_tmp_18")
             (Expr.literal 3000000000000000000))],
      Stmt.letVar
        "thirdTerm_1"
        (Expr.localVar "_verity_slice_tmp_19"),
      Stmt.letVar
        "_verity_slice_tmp_20"
        (Expr.add
          (Expr.literal 1000000000000000000)
          (Expr.localVar "r_1")),
      Stmt.letVar
        "_verity_slice_tmp_21"
        (Expr.add
          (Expr.localVar "_verity_slice_tmp_20")
          (Expr.localVar "secondTerm_1")),
      Stmt.letVar
        "expR_1"
        (Expr.add
          (Expr.localVar "_verity_slice_tmp_21")
          (Expr.localVar "thirdTerm_1")),
      Stmt.assignVar
        "_verity_slice_tmp_22"
        (Expr.shl
          (Expr.localVar "q_1")
          (Expr.localVar "expR_1"))],
   Stmt.letVar
     "_verity_slice_tmp_23"
     (Expr.localVar "_verity_slice_tmp_22"),
   Stmt.returnValues [Expr.localVar "_verity_slice_tmp_23"]]

theorem functionBody_wExp : functionBody tickLib.model "wExp" = wExpBody := by
  rfl

end Midnight.TickLibImport
