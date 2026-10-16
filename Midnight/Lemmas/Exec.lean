import Midnight.Lemmas.Body

/-! Step lemmas for symbolically executing straight-line imported code. -/

open Compiler.CompilationModel Compiler.CompilationModel.Denote Compiler.CompilationModel.SolidityImport
open Verity.Core

namespace Midnight.TickLibImport

def addW (a b : Nat) : Nat := (Uint256.ofNat a + Uint256.ofNat b).val
def subW (a b : Nat) : Nat := (Uint256.ofNat a - Uint256.ofNat b).val
def mulW (a b : Nat) : Nat := (Uint256.ofNat a * Uint256.ofNat b).val
def sdivW (a b : Nat) : Nat :=
  (Int256.div (Int256.ofUint256 (Uint256.ofNat a)) (Int256.ofUint256 (Uint256.ofNat b))).toUint256.val
def shlW (s v : Nat) : Nat := (Uint256.shl (Uint256.ofNat s) (Uint256.ofNat v)).val
def divW (a b : Nat) : Nat := (Uint256.ofNat a / Uint256.ofNat b).val
def sltW (a b : Nat) : Prop :=
  (Int256.ofUint256 (Uint256.ofNat a)).toInt < (Int256.ofUint256 (Uint256.ofNat b)).toInt

instance (a b : Nat) : Decidable (sltW a b) := by unfold sltW; infer_instance

theorem exec_let (o : DenoteOracle) (f : List Field) (s : DenoteState) (n : String) (e : Expr)
    (rest : List Stmt) (h : (evalExpr o f s e).isSome) :
    execStmtList o f s (.letVar n e :: rest) =
      execStmtList o f { s with bindings := bindValue s.bindings n ((evalExpr o f s e).getD 0) } rest := by
  cases h' : evalExpr o f s e <;> simp_all [execStmtList, execStmt]

theorem exec_assign (o : DenoteOracle) (f : List Field) (s : DenoteState) (n : String) (e : Expr)
    (rest : List Stmt) (h : (evalExpr o f s e).isSome) :
    execStmtList o f s (.assignVar n e :: rest) =
      execStmtList o f { s with bindings := bindValue s.bindings n ((evalExpr o f s e).getD 0) } rest := by
  cases h' : evalExpr o f s e <;> simp_all [execStmtList, execStmt]

theorem exec_append (o : DenoteOracle) (f : List Field) (s : DenoteState) (a b : List Stmt) :
    execStmtList o f s (a ++ b) =
      match execStmtList o f s a with
      | .continue next => execStmtList o f next b
      | .stop next => .stop next
      | .return value next => .return value next
      | .revert => .revert
      | .revertWithData data => .revertWithData data := by
  induction a generalizing s with
  | nil => simp [execStmtList]
  | cons x a ih =>
    simp only [List.cons_append, execStmtList]
    cases execStmt o f s x <;> simp [ih]

theorem exec_ite_zero (o : DenoteOracle) (f : List Field) (s : DenoteState) (c : Expr)
    (t e rest : List Stmt) (h : evalExpr o f s c = some 0) :
    execStmtList o f s (.ite c t e :: rest) = execStmtList o f s (e ++ rest) := by
  rw [exec_append]
  simp only [execStmtList, execStmt, h]
  cases execStmtList o f s e <;> rfl

theorem exec_ite_ne (o : DenoteOracle) (f : List Field) (s : DenoteState) (c : Expr)
    (t e rest : List Stmt) (v : Nat) (h : evalExpr o f s c = some v) (hv : v ≠ 0) :
    execStmtList o f s (.ite c t e :: rest) = execStmtList o f s (t ++ rest) := by
  rw [exec_append]
  have hv' : (v != 0) = true := by simpa using hv
  simp only [execStmtList, execStmt, h, hv', if_true]
  cases execStmtList o f s t <;> rfl

theorem exec_ret (o : DenoteOracle) (f : List Field) (s : DenoteState) (e : Expr) (rest : List Stmt)
    (h : (evalExpr o f s e).isSome) :
    execStmtList o f s (.returnValues [e] :: rest) =
      .stop { s with observedReturnWords := some [wordNormalize ((evalExpr o f s e).getD 0)],
                     observedStop := false } := by
  cases h' : evalExpr o f s e <;> simp_all [execStmtList, execStmt, evalExprList]

theorem exec_ret_nil (o : DenoteOracle) (f : List Field) (s : DenoteState) :
    execStmtList o f s [] = .continue s := by simp [execStmtList]

theorem lookup_bind (B : Env) (n m : String) (v : Nat) :
    lookupValue (bindValue B n v) m = if n = m then v else lookupValue B m := by
  unfold lookupValue bindValue
  by_cases h : n = m
  · subst h; simp
  · have hb : (n == m) = false := by simpa using h
    simp only [List.find?, hb, h, if_false]
    congr 1
    induction B with
    | nil => rfl
    | cons a B ih =>
      by_cases ha : a.1 = n
      · have ham : (a.1 == m) = false := by simpa [ha] using h
        have han : (a.1 != n) = false := by simpa using ha
        simp only [List.filter, han, List.find?, ham]
        exact ih
      · have han : (a.1 != n) = true := by simpa using ha
        simp only [List.filter, han, List.find?]
        cases a.1 == m
        · exact ih
        · rfl

theorem lookup_single (n m : String) (v : Nat) :
    lookupValue [(n, v)] m = if n = m then v else 0 := by
  unfold lookupValue
  by_cases h : n = m
  · subst h; simp
  · have hb : (n == m) = false := by simpa using h
    simp [List.find?, hb, h]

theorem wordNormalize_eq (n : Nat) : wordNormalize n = n % Uint256.modulus := rfl
theorem sltW_def (a b : Nat) :
    ((Int256.ofUint256 (Uint256.ofNat a)).toInt < (Int256.ofUint256 (Uint256.ofNat b)).toInt) =
      sltW a b := rfl
theorem addW_def (a b : Nat) : (Uint256.ofNat a + Uint256.ofNat b).val = addW a b := rfl
theorem subW_def (a b : Nat) : (Uint256.ofNat a - Uint256.ofNat b).val = subW a b := rfl
theorem mulW_def (a b : Nat) : (Uint256.ofNat a * Uint256.ofNat b).val = mulW a b := rfl
theorem divW_def (a b : Nat) : (Uint256.ofNat a / Uint256.ofNat b).val = divW a b := rfl
theorem shlW_def (a b : Nat) : (Uint256.shl (Uint256.ofNat a) (Uint256.ofNat b)).val = shlW a b := rfl
theorem sdivW_def (a b : Nat) :
    (Int256.div (Int256.ofUint256 (Uint256.ofNat a)) (Int256.ofUint256 (Uint256.ofNat b))).toUint256.val =
      sdivW a b := rfl

theorem boolWord_true : boolWord true = 1 := rfl
theorem boolWord_false : boolWord false = 0 := rfl

end Midnight.TickLibImport

namespace Midnight.TickLibImport
theorem boolWord_decide_false {p : Prop} {_ : Decidable p} (h : ¬p) : boolWord (decide p) = 0 := by
  simp [boolWord, h]
theorem boolWord_decide_true {p : Prop} {_ : Decidable p} (h : p) : boolWord (decide p) = 1 := by
  simp [boolWord, h]
section
variable (o : DenoteOracle) (f : List Field) (s : DenoteState)
theorem eval_param (n : String) : evalExpr o f s (.param n) = some (lookupValue s.bindings n) := by simp [evalExpr]
theorem eval_localVar (n : String) : evalExpr o f s (.localVar n) = some (lookupValue s.bindings n) := by simp [evalExpr]
theorem eval_literal (n : Nat) : evalExpr o f s (.literal n) = some (wordNormalize n) := by simp [evalExpr]
theorem eval_add (a b : Expr) : evalExpr o f s (.add a b) =
    (evalExpr o f s a).bind fun x => (evalExpr o f s b).bind fun y => some (addW x y) := by
  simp [evalExpr]; rfl
theorem eval_sub (a b : Expr) : evalExpr o f s (.sub a b) =
    (evalExpr o f s a).bind fun x => (evalExpr o f s b).bind fun y => some (subW x y) := by
  simp [evalExpr]; rfl
theorem eval_mul (a b : Expr) : evalExpr o f s (.mul a b) =
    (evalExpr o f s a).bind fun x => (evalExpr o f s b).bind fun y => some (mulW x y) := by
  simp [evalExpr]; rfl
theorem eval_div (a b : Expr) : evalExpr o f s (.div a b) =
    (evalExpr o f s a).bind fun x => (evalExpr o f s b).bind fun y => some (divW x y) := by
  simp [evalExpr]; rfl
theorem eval_sdiv (a b : Expr) : evalExpr o f s (.sdiv a b) =
    (evalExpr o f s a).bind fun x => (evalExpr o f s b).bind fun y => some (sdivW x y) := by
  simp [evalExpr]; rfl
theorem eval_shl (a b : Expr) : evalExpr o f s (.shl a b) =
    (evalExpr o f s a).bind fun x => (evalExpr o f s b).bind fun y => some (shlW x y) := by
  simp [evalExpr]; rfl
theorem eval_slt (a b : Expr) : evalExpr o f s (.slt a b) =
    (evalExpr o f s a).bind fun x => (evalExpr o f s b).bind fun y => some (boolWord (decide (sltW x y))) := by
  simp [evalExpr]; rfl
theorem eval_eq (a b : Expr) : evalExpr o f s (.eq a b) =
    (evalExpr o f s a).bind fun x => (evalExpr o f s b).bind fun y => some (boolWord (decide (x = y))) := by
  simp [evalExpr]
end

/-! Non-`rfl` simp lemmas: `dsimp` steps would leave definitional checks with large
literals to the kernel, which can be very slow. -/

theorem bind_some' {α β : Type} (a : α) (f : α → Option β) : (some a).bind f = f a := by simp
theorem getD_some' {α : Type} (a d : α) : (some a).getD d = a := by simp
theorem isSome_some' {α : Type} (a : α) : (some a).isSome = true := by simp
theorem wordNormalize_lit (n : Nat) (h : n < 2 ^ 256) : wordNormalize n = n := by
  simp only [wordNormalize_eq]; exact Nat.mod_eq_of_lt h
theorem boolWord_true' : boolWord true = 1 := by simp [boolWord]
theorem boolWord_false' : boolWord false = 0 := by simp [boolWord]

end Midnight.TickLibImport

namespace Midnight.TickLibImport
theorem ofNat_wordNormalize (n : Nat) : Uint256.ofNat (wordNormalize n) = Uint256.ofNat n := by
  apply Uint256.ext; simp [wordNormalize_eq, Uint256.val_ofNat]
theorem ofWord_uint256' (n : Nat) : (Word.ofWord n : Uint256) = Uint256.ofNat n := by simp
end Midnight.TickLibImport

namespace Midnight.TickLibImport
theorem cons_append' {α : Type} (a : α) (l r : List α) : (a :: l) ++ r = a :: (l ++ r) := by simp
theorem nil_append' {α : Type} (r : List α) : [] ++ r = r := by simp
theorem toWord_int256' (x : Int256) : Word.toWord x = x.toUint256.val := by simp
end Midnight.TickLibImport

namespace Midnight.TickLibImport
theorem some_boolWord_decide_eq_zero {a : Nat} {_ : Decidable (a = 0)} (h : a ≠ 0) :
    some (boolWord (decide (a = 0))) = some 0 := by
  simp [boolWord, h]
end Midnight.TickLibImport
