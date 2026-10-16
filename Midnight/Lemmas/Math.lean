import Midnight.Lemmas.Word

/-! The integer function computed by the imported `wExp`, and its monotonicity. -/

namespace Midnight.TickLibImport.Math
open Midnight.TickLibImport.Word

def qOf (y : Int) : Int := sdivI (y + 322611214989459870) 693147180559945309
def rOf (y : Int) : Int := y - qOf y * 693147180559945309
def sOf (y : Int) : Int := sdivI (rOf y * rOf y) 2000000000000000000
def tOf (y : Int) : Int := sdivI (sOf y * rOf y) 3000000000000000000
def eOf (y : Int) : Int := 1000000000000000000 + rOf y + sOf y + tOf y
def posW (y : Int) : Int := eOf y * 2 ^ (qOf y).toNat

/-- Largest input magnitude. -/
def M : Int := 16817989975223754156

theorem q_eq {y : Int} (hy : 0 ≤ y) : qOf y = (y + 322611214989459870) / 693147180559945309 :=
  sdivI_nonneg (by omega) (by norm_num)

theorem q_bounds {y : Int} (hy0 : 0 ≤ y) (hy : y ≤ M) : 0 ≤ qOf y ∧ qOf y ≤ 24 := by
  rw [q_eq hy0]; unfold M at hy; omega

theorem r_bounds {y : Int} (hy0 : 0 ≤ y) :
    -322611214989459870 ≤ rOf y ∧ rOf y ≤ 370535965570485438 := by
  unfold rOf; rw [q_eq hy0]; omega

/-- The polynomial part, as a function of the residual. -/
def sR (r : Int) : Int := sdivI (r * r) 2000000000000000000
def tR (r : Int) : Int := sdivI (sR r * r) 3000000000000000000
def eR (r : Int) : Int := 1000000000000000000 + r + sR r + tR r

theorem eOf_eq (y : Int) : eOf y = eR (rOf y) := rfl

theorem sR_eq (r : Int) : sR r = r * r / 2000000000000000000 :=
  sdivI_nonneg (mul_self_nonneg r) (by norm_num)

theorem tR_pos {r : Int} (hr : 0 ≤ r) : tR r = sR r * r / 3000000000000000000 := by
  have : 0 ≤ sR r := by rw [sR_eq]; exact Int.ediv_nonneg (mul_self_nonneg r) (by norm_num)
  exact sdivI_nonneg (mul_nonneg this hr) (by norm_num)

theorem tR_neg {r : Int} (hr : r < 0) : tR r = -((sR r * (-r)) / 3000000000000000000) := by
  have h0 : 0 ≤ sR r := by rw [sR_eq]; exact Int.ediv_nonneg (mul_self_nonneg r) (by norm_num)
  unfold tR
  rcases h0.lt_or_eq with h | h
  · rw [sdivI_neg (by nlinarith) (by norm_num)]; ring_nf
  · rw [← h]; simp [sdivI]

theorem sR_nonneg (r : Int) : 0 ≤ sR r := by
  rw [sR_eq]; exact Int.ediv_nonneg (mul_self_nonneg r) (by norm_num)

theorem sR_mul_le (r : Int) : sR r * 2000000000000000000 ≤ r * r := by
  rw [sR_eq]; exact Int.ediv_mul_le _ (by norm_num)

theorem sR_lt (r : Int) : r * r < (sR r + 1) * 2000000000000000000 := by
  rw [sR_eq]; have := Int.lt_ediv_add_one_mul_self (r * r) (show (0 : Int) < 2000000000000000000 by norm_num)
  linarith

theorem sR_mono {a b : Int} (h : a * a ≤ b * b) : sR a ≤ sR b := by
  rw [sR_eq, sR_eq]; exact Int.ediv_le_ediv (by norm_num) h

theorem eR_mono {r1 r2 : Int} (h1 : -322611214989459870 ≤ r1) (h12 : r1 ≤ r2)
    (h2 : r2 ≤ 370535965570485438) : eR r1 ≤ eR r2 := by
  unfold eR
  rcases le_or_gt 0 r1 with p1 | n1
  · have hs : sR r1 ≤ sR r2 := sR_mono (by nlinarith)
    have hs0 := sR_nonneg r1
    rw [tR_pos p1, tR_pos (by omega)]
    have : sR r1 * r1 / 3000000000000000000 ≤ sR r2 * r2 / 3000000000000000000 :=
      Int.ediv_le_ediv (by norm_num) (by nlinarith)
    omega
  rcases le_or_gt 0 r2 with p2 | n2
  · rw [tR_neg n1, tR_pos p2]
    have hs1 := sR_mul_le r1
    have hs0 := sR_nonneg r1
    have hlt : sR r1 ≤ -r1 := by nlinarith
    have : 0 ≤ sR r1 * -r1 / 3000000000000000000 := Int.ediv_nonneg (by nlinarith) (by norm_num)
    have : 0 ≤ sR r2 * r2 / 3000000000000000000 := Int.ediv_nonneg (mul_nonneg (sR_nonneg r2) p2) (by norm_num)
    have := sR_nonneg r2
    omega
  · rw [tR_neg n1, tR_neg n2]
    have hs1 := sR_mul_le r1
    have hs2 := sR_lt r2
    have hsm : sR r2 ≤ sR r1 := sR_mono (by nlinarith)
    have hd : sR r1 - sR r2 ≤ r2 - r1 := by
      by_contra hc
      push Not at hc
      nlinarith
    have : sR r2 * -r2 / 3000000000000000000 ≤ sR r1 * -r1 / 3000000000000000000 :=
      Int.ediv_le_ediv (by norm_num) (by nlinarith [sR_nonneg r2])
    omega

theorem eR_top : eR 370535965570485438 = 1447663323139670138 := by
  rw [eR, tR_pos (by norm_num), sR_eq]; norm_num

theorem eR_bot : eR (-322611214989459870) = 723831661569835069 := by
  rw [eR, tR_neg (by norm_num), sR_eq]; norm_num

theorem posW_eq (y : Int) : posW y = eR (rOf y) * 2 ^ (qOf y).toNat := rfl

theorem posW_mono {y1 y2 : Int} (h0 : 0 ≤ y1) (h12 : y1 ≤ y2) (h2 : y2 ≤ M) :
    posW y1 ≤ posW y2 := by
  have hq1 := q_bounds h0 (by omega)
  have hq2 := q_bounds (by omega : 0 ≤ y2) h2
  have hr1 := r_bounds h0
  have hr2 := r_bounds (by omega : 0 ≤ y2)
  have hqm : qOf y1 ≤ qOf y2 := by
    rw [q_eq h0, q_eq (by omega)]; exact Int.ediv_le_ediv (by norm_num) (by omega)
  rw [posW_eq, posW_eq]
  rcases hqm.lt_or_eq with hlt | heq
  · have e1 : eR (rOf y1) ≤ eR 370535965570485438 := eR_mono hr1.1 hr1.2 (le_refl _)
    have e2 : eR (-322611214989459870) ≤ eR (rOf y2) := eR_mono (le_refl _) hr2.1 hr2.2
    rw [eR_top] at e1; rw [eR_bot] at e2
    have hn : (qOf y1).toNat + 1 ≤ (qOf y2).toNat := by omega
    have hp : (2 : Int) ^ ((qOf y1).toNat + 1) ≤ 2 ^ (qOf y2).toNat :=
      pow_le_pow_right₀ (by norm_num) hn
    have hpos : (0 : Int) < 2 ^ (qOf y1).toNat := by positivity
    rw [pow_succ] at hp
    calc eR (rOf y1) * 2 ^ (qOf y1).toNat ≤ 1447663323139670138 * 2 ^ (qOf y1).toNat :=
          mul_le_mul_of_nonneg_right e1 hpos.le
      _ = 723831661569835069 * (2 ^ (qOf y1).toNat * 2) := by ring
      _ ≤ 723831661569835069 * 2 ^ (qOf y2).toNat := mul_le_mul_of_nonneg_left hp (by norm_num)
      _ ≤ eR (rOf y2) * 2 ^ (qOf y2).toNat := mul_le_mul_of_nonneg_right e2 (by positivity)
  · rw [heq]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply eR_mono hr1.1 _ hr2.2
    unfold rOf; rw [heq]; omega

end Midnight.TickLibImport.Math
