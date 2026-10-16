import Midnight.Lemmas.Exec

/-! Symbolic execution of the imported `wExp` body. -/
open Compiler.CompilationModel Compiler.CompilationModel.Denote Compiler.CompilationModel.SolidityImport
open Verity.Core
namespace Midnight.TickLibImport

def posW (X : Nat) : Nat :=
  let q := sdivW (addW X 322611214989459870) 693147180559945309
  let r := subW X (mulW q 693147180559945309)
  let s := sdivW (mulW r r) 2000000000000000000
  let t := sdivW (mulW s r) 3000000000000000000
  shlW q (addW (addW (addW 1000000000000000000 r) s) t)

scoped macro "norm" : tactic => `(tactic| simp only [eval_param, eval_localVar, eval_literal, eval_add, eval_sub,
    eval_mul, eval_div, eval_sdiv, eval_shl, eval_slt, eval_eq, lookup_bind, lookup_single,
    bind_some', getD_some', isSome_some', String.reduceEq, ↓reduceIte,
    wordNormalize_lit, Nat.reducePow, Nat.reduceLT, Nat.reduceEqDiff, decide_true, decide_false, boolWord_true', boolWord_false',
    cons_append', nil_append', toWord_int256'])

scoped macro "stepl" : tactic => `(tactic| first
  | (rw [exec_let]; rotate_left; norm; norm)
  | (rw [exec_assign]; rotate_left; norm; norm))

scoped macro "stepi" : tactic => `(tactic| (rw [exec_ite_zero]; rotate_left; norm; norm))

scoped macro "step" : tactic => `(tactic| first | stepl | stepi)

theorem wExp_nonneg (o : DenoteOracle) (w : Verity.ContractState) (x : Int256)
    (hx : ¬ sltW x.toUint256.val 0) :
    tickLib.wExp o w x = some (Uint256.ofNat (posW x.toUint256.val)) := by
  simp only [tickLib.wExp, runFunction, functionBody_wExp, wExpBody]
  step; step
  rw [exec_ite_zero]
  rotate_left
  · norm; rw [boolWord_decide_false hx]
  norm
  repeat step
  rw [exec_ret]; rotate_left; norm
  norm
  simp only [ofWord_uint256', ofNat_wordNormalize]
  rfl

theorem wExp_neg (o : DenoteOracle) (w : Verity.ContractState) (x : Int256)
    (hx : sltW x.toUint256.val 0) (h1 : ¬ sltW (subW 0 x.toUint256.val) 0)
    (h2 : posW (subW 0 x.toUint256.val) ≠ 0) :
    tickLib.wExp o w x =
      some (Uint256.ofNat (divW 1000000000000000000000000000000000000 (posW (subW 0 x.toUint256.val)))) := by
  simp only [tickLib.wExp, runFunction, functionBody_wExp, wExpBody]
  step; step
  rw [exec_ite_ne _ _ _ _ _ _ _ 1]
  rotate_left
  · norm; rw [boolWord_decide_true hx]
  · decide
  norm
  stepl
  rw [exec_ite_zero]
  rotate_left
  · norm; rw [boolWord_decide_false h1]
  norm
  repeat step
  rw [exec_ite_zero]
  rotate_left
  · norm; exact some_boolWord_decide_eq_zero h2
  norm
  repeat step
  rw [exec_ret]; rotate_left; norm
  norm
  simp only [ofWord_uint256', ofNat_wordNormalize]
  rfl

end Midnight.TickLibImport
