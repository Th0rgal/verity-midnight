import Mathlib.Tactic

/-! Integer model of the positive branch of `wExp` and its monotonicity. -/

namespace Midnight.TickLibImport

def sF (r : Int) : Int := Int.tdiv (r * r) 2000000000000000000
def tF (r : Int) : Int := Int.tdiv (sF r * r) 3000000000000000000
def eF (r : Int) : Int := 1000000000000000000 + r + sF r + tF r

theorem tdiv_mono {a b d : Int} (hd : 0 < d) (h : a ≤ b) : Int.tdiv a d ≤ Int.tdiv b d :=
  Int.tdiv_le_tdiv hd h

theorem sF_eq (r : Int) : sF r = r * r / 2000000000000000000 := by
  unfold sF; rw [Int.tdiv_eq_ediv_of_nonneg (mul_self_nonneg r)]

theorem sF_nonneg (r : Int) : 0 ≤ sF r := by
  rw [sF_eq]; exact Int.ediv_nonneg (mul_self_nonneg r) (by norm_num)

theorem eF_step (r : Int) (hr : -1000000000000000000 < r) : eF r ≤ eF (r + 1) := by
  unfold eF tF
  rcases le_or_gt 0 r with h0 | h0
  · have hs : sF r ≤ sF (r + 1) := tdiv_mono (by norm_num) (by nlinarith)
    have hs0 := sF_nonneg r
    have ht : Int.tdiv (sF r * r) 3000000000000000000 ≤ Int.tdiv (sF (r + 1) * (r + 1)) 3000000000000000000 :=
      tdiv_mono (by norm_num) (by nlinarith)
    linarith
  · have hs1 : sF (r + 1) ≤ sF r := tdiv_mono (by norm_num) (by nlinarith)
    have hs2 : sF r ≤ sF (r + 1) + 1 := by
      rw [sF_eq, sF_eq]
      have : r * r / 2000000000000000000 ≤ ((r + 1) * (r + 1) + 1 * 2000000000000000000) / 2000000000000000000 :=
        Int.ediv_le_ediv (by norm_num) (by nlinarith)
      rw [Int.add_mul_ediv_right _ _ (by norm_num)] at this
      exact this
    have hs0 := sF_nonneg (r + 1)
    have ht : Int.tdiv (sF r * r) 3000000000000000000 ≤ Int.tdiv (sF (r + 1) * (r + 1)) 3000000000000000000 :=
      tdiv_mono (by norm_num) (by nlinarith)
    linarith

theorem eF_mono (a b : Int) (ha : -1000000000000000000 < a) (hab : a ≤ b) : eF a ≤ eF b := by
  obtain ⟨n, rfl⟩ : ∃ n : Nat, b = a + n := ⟨(b - a).toNat, by omega⟩
  induction n with
  | zero => simp
  | succ n ih =>
    have := eF_step (a + n) (by omega)
    have h2 : a + ((n + 1 : Nat) : Int) = a + n + 1 := by push_cast; ring
    rw [h2]
    exact le_trans (ih (by omega)) this



theorem eF_key : eF 370535965570485438 ≤ 2 * eF (-322611214989459870) := by
  unfold eF tF sF; decide

theorem eF_low_pos : 0 < eF (-322611214989459870) := by
  unfold eF tF sF; decide

def qF (x : Int) : Int := Int.tdiv (x + 322611214989459870) 693147180559945309
def rF (x : Int) : Int := x - qF x * 693147180559945309
def posI (x : Int) : Int := eF (rF x) * 2 ^ (qF x).toNat

theorem qF_eq {x : Int} (hx : 0 ≤ x) : qF x = (x + 322611214989459870) / 693147180559945309 := by
  unfold qF; rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]

theorem qF_nonneg {x : Int} (hx : 0 ≤ x) : 0 ≤ qF x := by
  rw [qF_eq hx]; exact Int.ediv_nonneg (by omega) (by norm_num)

theorem rF_bounds {x : Int} (hx : 0 ≤ x) :
    -322611214989459870 ≤ rF x ∧ rF x ≤ 370535965570485438 := by
  unfold rF; rw [qF_eq hx]
  have h1 := Int.emod_add_mul_ediv (x + 322611214989459870) 693147180559945309
  have h2 := Int.emod_nonneg (x + 322611214989459870) (b := 693147180559945309) (by norm_num)
  have h3 := Int.emod_lt_of_pos (x + 322611214989459870) (b := 693147180559945309) (by norm_num)
  constructor <;> linarith

theorem qF_mono {x y : Int} (hx : 0 ≤ x) (hxy : x ≤ y) : qF x ≤ qF y := by
  rw [qF_eq hx, qF_eq (by omega)]; exact Int.ediv_le_ediv (by norm_num) (by omega)

theorem eF_pos {r : Int} (hr : -322611214989459870 ≤ r) : 0 < eF r :=
  lt_of_lt_of_le eF_low_pos (eF_mono _ _ (by norm_num) hr)

theorem posI_mono {x y : Int} (hx : 0 ≤ x) (hxy : x ≤ y) : posI x ≤ posI y := by
  have hy : 0 ≤ y := by omega
  have hq := qF_mono hx hxy
  have hqx := qF_nonneg hx
  obtain ⟨hrx1, hrx2⟩ := rF_bounds hx
  obtain ⟨hry1, hry2⟩ := rF_bounds hy
  unfold posI
  rcases eq_or_lt_of_le hq with he | hlt
  · rw [he]
    have hr : rF x ≤ rF y := by unfold rF; rw [he]; omega
    have := eF_mono _ _ (by omega) hr
    exact mul_le_mul_of_nonneg_right this (by positivity)
  · have e1 : eF (rF x) ≤ eF 370535965570485438 := eF_mono _ _ (by omega) hrx2
    have e2 : eF (-322611214989459870) ≤ eF (rF y) := eF_mono _ _ (by norm_num) hry1
    have e0 := eF_low_pos
    have hp : (2 : Int) ^ (qF x).toNat * 2 ≤ 2 ^ (qF y).toNat := by
      rw [← pow_succ]; exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hpx : (0 : Int) < 2 ^ (qF x).toNat := by positivity
    calc eF (rF x) * 2 ^ (qF x).toNat ≤ eF 370535965570485438 * 2 ^ (qF x).toNat :=
          mul_le_mul_of_nonneg_right e1 hpx.le
      _ ≤ (2 * eF (-322611214989459870)) * 2 ^ (qF x).toNat :=
          mul_le_mul_of_nonneg_right eF_key hpx.le
      _ = eF (-322611214989459870) * (2 ^ (qF x).toNat * 2) := by ring
      _ ≤ eF (-322611214989459870) * 2 ^ (qF y).toNat := mul_le_mul_of_nonneg_left hp e0.le
      _ ≤ eF (rF y) * 2 ^ (qF y).toNat := mul_le_mul_of_nonneg_right e2 (by positivity)

end Midnight.TickLibImport
