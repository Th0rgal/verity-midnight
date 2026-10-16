import Midnight.Lemmas.Reduce
import Midnight.Lemmas.Math

/-! Words versus integers: the word operations of the model on encoded integers. -/

open Compiler.CompilationModel.Denote
open Verity.Core

namespace Midnight.TickLibImport

def enc (i : Int) : Nat := (i % 2 ^ 256).toNat

theorem cast_enc (i : Int) : ((enc i : Nat) : Int) = i % 2 ^ 256 := by
  unfold enc; rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]

theorem enc_lt (i : Int) : enc i < 2 ^ 256 := by
  have h := cast_enc i
  have h2 := Int.emod_lt_of_pos i (b := 2 ^ 256) (by norm_num)
  omega

theorem enc_inj {a b : Nat} (h : (a : Int) = (b : Int)) : a = b := by exact_mod_cast h

theorem val_ofNat' (n : Nat) : (Uint256.ofNat n).val = n % 2 ^ 256 := by
  simp [Uint256.val_ofNat, Uint256.modulus, UINT256_MODULUS]

theorem addW_nat (a b : Nat) : addW a b = (a % 2 ^ 256 + b % 2 ^ 256) % 2 ^ 256 := rfl
theorem mulW_nat (a b : Nat) : mulW a b = (a % 2 ^ 256 * (b % 2 ^ 256)) % 2 ^ 256 := rfl

theorem M_eq : (2 : Int) ^ 256 =
    115792089237316195423570985008687907853269984665640564039457584007913129639936 := by norm_num

theorem enc_mod (i : Int) : enc i % 2 ^ 256 = enc i := Nat.mod_eq_of_lt (enc_lt i)

theorem addW_enc (i j : Int) : addW (enc i) (enc j) = enc (i + j) := by
  apply enc_inj
  rw [addW_nat, enc_mod, enc_mod]
  push_cast
  rw [cast_enc, cast_enc, cast_enc, M_eq, ← Int.add_emod]

theorem mulW_enc (i j : Int) : mulW (enc i) (enc j) = enc (i * j) := by
  apply enc_inj
  rw [mulW_nat, enc_mod, enc_mod]
  push_cast
  rw [cast_enc, cast_enc, cast_enc, M_eq, ← Int.mul_emod]

theorem modulus_eq : Uint256.modulus =
    115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
  simp [Uint256.modulus, UINT256_MODULUS]

theorem subW_cast (a b : Nat) (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) :
    (subW a b : Int) = ((a : Int) - b) % 2 ^ 256 := by
  have e : subW a b = (Uint256.sub (Uint256.ofNat a) (Uint256.ofNat b)).val := rfl
  rw [e]
  unfold Uint256.sub
  simp only [Uint256.val_ofNat, modulus_eq] at *
  rw [M_eq]
  norm_num at ha hb
  split_ifs <;> simp only [Uint256.val_ofNat, modulus_eq] <;> omega

theorem subW_enc (i j : Int) : subW (enc i) (enc j) = enc (i - j) := by
  apply enc_inj
  rw [subW_cast _ _ (enc_lt i) (enc_lt j), cast_enc, cast_enc, cast_enc, M_eq]
  omega

theorem ofInt_val (v : Int) : (Int256.ofInt v).toUint256.val = enc v := by
  apply enc_inj
  rw [cast_enc, M_eq]
  by_cases hv : v < 0
  · rw [Int256.ofInt_neg v hv]
    simp only [Uint256.val_ofNat, modulus_eq, Int256.modulus]
    have h1 : ((v.natAbs : Nat) : Int) = -v := by omega
    push_cast
    omega
  · rw [Int256.ofInt_nonneg v hv]
    simp only [Uint256.val_ofNat, modulus_eq]
    push_cast
    omega

theorem sw_enc {i : Int} (h1 : -2 ^ 255 ≤ i) (h2 : i < 2 ^ 255) :
    (Int256.ofUint256 (Uint256.ofNat (enc i))).toInt = i := by
  have hc := cast_enc i
  have hl := enc_lt i
  rw [M_eq] at hc
  unfold Int256.toInt
  simp only [Int256.ofUint256, Uint256.val_ofNat, modulus_eq, Int256.signBit, Int256.modulus]
  norm_num at *
  split_ifs <;> omega

theorem sltW_enc {i j : Int} (hi1 : -2 ^ 255 ≤ i) (hi2 : i < 2 ^ 255) (hj1 : -2 ^ 255 ≤ j)
    (hj2 : j < 2 ^ 255) : sltW (enc i) (enc j) ↔ i < j := by
  unfold sltW; rw [sw_enc hi1 hi2, sw_enc hj1 hj2]

theorem tdiv_natCast (i : Int) (n : Nat) :
    Int.tdiv i n = if i < 0 then -((i.natAbs / n : Nat) : Int) else ((i.natAbs / n : Nat) : Int) := by
  cases i with
  | ofNat m => simp [Int.tdiv]
  | negSucc m =>
    simp only [Int.tdiv, Int.negSucc_lt_zero, if_true, Int.natAbs_negSucc]
    rfl

theorem sdivW_enc {i c : Int} (hi1 : -2 ^ 255 ≤ i) (hi2 : i < 2 ^ 255) (hc1 : 0 < c)
    (hc2 : c < 2 ^ 255) : sdivW (enc i) (enc c) = enc (Int.tdiv i c) := by
  unfold sdivW Int256.div
  rw [sw_enc hi1 hi2, sw_enc (by omega) hc2]
  obtain ⟨n, rfl⟩ : ∃ n : Nat, c = n := ⟨c.toNat, by omega⟩
  rw [tdiv_natCast]
  simp only [Int256.signedAbsNat, Int.natAbs_natCast]
  have hn : n ≠ 0 := by omega
  have hn' : ((n : Int) < 0) = False := by simp
  by_cases hneg : i < 0 <;> simp [hn, hn', hneg] <;> rw [ofInt_val]

theorem enc_nonneg {i : Int} (h1 : 0 ≤ i) (h2 : i < 2 ^ 256) : enc i = i.toNat := by
  apply enc_inj; rw [cast_enc, Int.emod_eq_of_lt h1 h2]; omega

theorem shlW_enc {q e : Int} (hq : 0 ≤ q) (hq2 : q < 2 ^ 256) (he : 0 ≤ e) (he2 : e < 2 ^ 256) :
    shlW (enc q) (enc e) = enc (e * 2 ^ q.toNat) := by
  have e1 : shlW (enc q) (enc e) = ((enc e % 2 ^ 256) <<< (enc q % 2 ^ 256)) % 2 ^ 256 := rfl
  rw [e1, enc_mod, enc_mod, enc_nonneg hq hq2, enc_nonneg he he2, Nat.shiftLeft_eq]
  apply enc_inj
  rw [cast_enc]
  push_cast
  rw [Int.toNat_of_nonneg he]

theorem divW_nat {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) (hb0 : b ≠ 0) :
    divW a b = a / b := by
  have e1 : divW a b = (Uint256.div (Uint256.ofNat a) (Uint256.ofNat b)).val := rfl
  rw [e1]
  unfold Uint256.div
  simp only [Uint256.val_ofNat, modulus_eq] at *
  norm_num at ha hb
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, if_neg hb0]
  simp only [Uint256.val_ofNat, modulus_eq]
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) ha)

theorem val_enc (x : Int256) : x.toUint256.val = enc x.toInt := by
  apply enc_inj
  rw [cast_enc, M_eq]
  have hl := x.word.isLt
  simp only [UINT256_MODULUS] at hl
  norm_num at hl
  unfold Int256.toInt
  simp only [Int256.signBit, Int256.modulus, Uint256.modulus, UINT256_MODULUS]
  show ((x.word.val : Nat) : Int) = _
  norm_num
  split_ifs <;> omega

theorem e_off : (322611214989459870 : Nat) = enc 322611214989459870 := by unfold enc; norm_num; rfl
theorem e_ln2 : (693147180559945309 : Nat) = enc 693147180559945309 := by unfold enc; norm_num; rfl
theorem e_two : (2000000000000000000 : Nat) = enc 2000000000000000000 := by unfold enc; norm_num; rfl
theorem e_three : (3000000000000000000 : Nat) = enc 3000000000000000000 := by unfold enc; norm_num; rfl
theorem e_one : (1000000000000000000 : Nat) = enc 1000000000000000000 := by unfold enc; norm_num; rfl

theorem qF_max : qF 16817989975223754156 = 24 := by unfold qF; decide

theorem sF_bounds {r : Int} (h1 : -322611214989459870 ≤ r) (h2 : r ≤ 370535965570485438) :
    0 ≤ sF r ∧ sF r ≤ 100000000000000000 := by
  refine ⟨sF_nonneg r, ?_⟩
  rw [sF_eq]
  have := Int.ediv_mul_le (r * r) (b := 2000000000000000000) (by norm_num)
  nlinarith

theorem tF_bounds {r : Int} (h1 : -322611214989459870 ≤ r) (h2 : r ≤ 370535965570485438) :
    -100000000000000000 ≤ tF r ∧ tF r ≤ 100000000000000000 := by
  obtain ⟨s1, s2⟩ := sF_bounds h1 h2
  unfold tF
  constructor
  · have := tdiv_mono (d := 3000000000000000000) (by norm_num)
      (show -100000000000000000000000000000000000 ≤ sF r * r by nlinarith)
    have h : Int.tdiv (-100000000000000000000000000000000000) 3000000000000000000 =
      -33333333333333333 := by decide
    omega
  · have := tdiv_mono (d := 3000000000000000000) (by norm_num)
      (show sF r * r ≤ 100000000000000000000000000000000000 by nlinarith)
    have h : Int.tdiv (100000000000000000000000000000000000) 3000000000000000000 =
      33333333333333333 := by decide
    omega

theorem posW_enc {x : Int} (h0 : 0 ≤ x) (h1 : x ≤ 16817989975223754156) :
    posW (enc x) = enc (posI x) := by
  obtain ⟨r1, r2⟩ := rF_bounds h0
  have q0 := qF_nonneg h0
  have q1 : qF x ≤ 24 := qF_max ▸ qF_mono h0 h1
  obtain ⟨s1, s2⟩ := sF_bounds r1 r2
  obtain ⟨t1, t2⟩ := tF_bounds r1 r2
  have hq : sdivW (addW (enc x) 322611214989459870) 693147180559945309 = enc (qF x) := by
    rw [e_off, e_ln2, addW_enc, sdivW_enc (by omega) (by omega) (by norm_num) (by norm_num)]; rfl
  have hr : subW (enc x) (mulW (enc (qF x)) 693147180559945309) = enc (rF x) := by
    rw [e_ln2, mulW_enc, subW_enc]; rfl
  have hs : sdivW (mulW (enc (rF x)) (enc (rF x))) 2000000000000000000 = enc (sF (rF x)) := by
    rw [e_two, mulW_enc, sdivW_enc (by nlinarith) (by nlinarith) (by norm_num) (by norm_num)]; rfl
  have ht : sdivW (mulW (enc (sF (rF x))) (enc (rF x))) 3000000000000000000 = enc (tF (rF x)) := by
    rw [e_three, mulW_enc, sdivW_enc (by nlinarith) (by nlinarith) (by norm_num) (by norm_num)]; rfl
  have he : addW (addW (addW 1000000000000000000 (enc (rF x))) (enc (sF (rF x)))) (enc (tF (rF x))) =
      enc (eF (rF x)) := by
    rw [e_one, addW_enc, addW_enc, addW_enc]; rfl
  have epos := eF_pos r1
  have hsh : shlW (enc (qF x)) (enc (eF (rF x))) = enc (posI x) := by
    rw [shlW_enc q0 (by omega) epos.le (by unfold eF; omega)]; rfl
  unfold posW
  simp only [hq, hr, hs, ht, he, hsh]

end Midnight.TickLibImport
