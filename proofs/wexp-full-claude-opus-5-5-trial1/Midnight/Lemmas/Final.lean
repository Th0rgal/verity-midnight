import Midnight.Lemmas.Bridge
import Midnight.TickLibImportSpec

/-! The imported `wExp` on the specification range, as an integer function. -/

open Compiler.CompilationModel.Denote
open Verity.Core

namespace Midnight.TickLibImport

/-- Value of the imported `wExp` on in-range inputs. -/
def wExpF (x : Int) : Nat :=
  if x < 0 then 1000000000000000000000000000000000000 / (posI (-x)).toNat else (posI x).toNat

theorem maxInput_eq : Spec.TickLibImport.maxInput = 16817989975223754156 := by
  unfold Spec.TickLibImport.maxInput Spec.TickLibImport.lnOnePlusDelta Spec.TickLibImport.maxTick
  norm_num

theorem posI_zero : posI 0 = 1000000000000000000 := by
  unfold posI rF qF eF tF sF; decide

theorem posI_bounds {x : Int} (h0 : 0 ≤ x) (h1 : x ≤ 16817989975223754156) :
    1000000000000000000 ≤ posI x ∧ posI x < 2 ^ 200 := by
  constructor
  · rw [← posI_zero]; exact posI_mono (le_refl 0) h0
  · obtain ⟨r1, r2⟩ := rF_bounds h0
    obtain ⟨s1, s2⟩ := sF_bounds r1 r2
    obtain ⟨t1, t2⟩ := tF_bounds r1 r2
    have q1 : qF x ≤ 24 := qF_max ▸ qF_mono h0 h1
    have q0 := qF_nonneg h0
    have epos := eF_pos r1
    have hp : (2 : Int) ^ (qF x).toNat ≤ 2 ^ 24 := pow_le_pow_right₀ (by norm_num) (by omega)
    have he : eF (rF x) ≤ 2000000000000000000 := by unfold eF; omega
    unfold posI
    calc eF (rF x) * 2 ^ (qF x).toNat ≤ 2000000000000000000 * 2 ^ 24 :=
          mul_le_mul he hp (by positivity) (by norm_num)
      _ < 2 ^ 200 := by norm_num

theorem enc_zero : (0 : Nat) = enc 0 := by unfold enc; norm_num

theorem wExp_eq (o : DenoteOracle) (w : Verity.ContractState) (x : Int256)
    (hx : Spec.TickLibImport.inWExpRange x) :
    tickLib.wExp o w x = some (Uint256.ofNat (wExpF x.toInt)) := by
  unfold Spec.TickLibImport.inWExpRange at hx
  rw [maxInput_eq] at hx
  obtain ⟨hx1, hx2⟩ := hx
  have hX := val_enc x
  unfold wExpF
  by_cases hneg : x.toInt < 0
  · have hs : sltW x.toUint256.val 0 := by
      rw [hX, enc_zero, sltW_enc (by omega) (by omega) (by norm_num) (by norm_num)]; exact hneg
    have hsub : subW 0 x.toUint256.val = enc (-x.toInt) := by
      rw [hX, enc_zero, subW_enc]; congr 1; ring
    obtain ⟨b1, b2⟩ := posI_bounds (x := -x.toInt) (by omega) (by omega)
    have hp : posW (subW 0 x.toUint256.val) = (posI (-x.toInt)).toNat := by
      rw [hsub, posW_enc (by omega) (by omega), enc_nonneg (by omega) (by omega)]
    have h1 : ¬ sltW (subW 0 x.toUint256.val) 0 := by
      rw [hsub, enc_zero, sltW_enc (by omega) (by omega) (by norm_num) (by norm_num)]; omega
    have h2 : posW (subW 0 x.toUint256.val) ≠ 0 := by rw [hp]; omega
    rw [wExp_neg o w x hs h1 h2, hp, if_pos hneg,
      divW_nat (by norm_num) (by omega) (by omega)]
  · have hs : ¬ sltW x.toUint256.val 0 := by
      rw [hX, enc_zero, sltW_enc (by omega) (by omega) (by norm_num) (by norm_num)]; exact hneg
    obtain ⟨b1, b2⟩ := posI_bounds (x := x.toInt) (by omega) (by omega)
    rw [wExp_nonneg o w x hs, hX, posW_enc (by omega) (by omega), if_neg hneg,
      enc_nonneg (by omega) (by omega)]

theorem wExpF_mono {a b : Int} (ha1 : -16817989975223754156 ≤ a) (hb2 : b ≤ 16817989975223754156)
    (hab : a ≤ b) : wExpF a ≤ wExpF b := by
  unfold wExpF
  by_cases ha : a < 0 <;> by_cases hb : b < 0
  · rw [if_pos ha, if_pos hb]
    obtain ⟨b1, _⟩ := posI_bounds (x := -b) (by omega) (by omega)
    have hm := posI_mono (x := -b) (y := -a) (by omega) (by omega)
    apply Nat.div_le_div_left (by omega) (by omega)
  · rw [if_pos ha, if_neg hb]
    have hm1 := posI_mono (x := 0) (y := -a) (le_refl 0) (by omega)
    have hm2 := posI_mono (x := 0) (y := b) (le_refl 0) (by omega)
    rw [posI_zero] at hm1 hm2
    calc 1000000000000000000000000000000000000 / (posI (-a)).toNat
        ≤ 1000000000000000000000000000000000000 / 1000000000000000000 :=
          Nat.div_le_div_left (by omega) (by norm_num)
      _ = 1000000000000000000 := by norm_num
      _ ≤ (posI b).toNat := by omega
  · omega
  · rw [if_neg ha, if_neg hb]
    have := posI_mono (x := a) (y := b) (by omega) hab
    omega

theorem wExpF_lt {a : Int} (ha1 : -16817989975223754156 ≤ a) (ha2 : a ≤ 16817989975223754156) :
    wExpF a < 2 ^ 256 := by
  unfold wExpF
  split_ifs with h
  · exact lt_of_le_of_lt (Nat.div_le_self _ _) (by norm_num)
  · obtain ⟨_, b2⟩ := posI_bounds (x := a) (by omega) ha2
    have : (2 : Int) ^ 200 < 2 ^ 256 := by norm_num
    omega

end Midnight.TickLibImport
