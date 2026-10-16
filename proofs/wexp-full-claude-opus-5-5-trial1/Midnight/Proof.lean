import Midnight.TickLibImportSpec
import Midnight.Lemmas.Final

namespace Midnight.TickLibImport

open Verity.Core

private theorem range_bounds {x : Int256} (hx : Spec.TickLibImport.inWExpRange x) :
    -16817989975223754156 ≤ x.toInt ∧ x.toInt ≤ 16817989975223754156 := by
  unfold Spec.TickLibImport.inWExpRange at hx
  rw [maxInput_eq] at hx
  exact hx

theorem wExpIsMonotonic : Spec.TickLibImport.wExpIsMonotonic := by
  intro oracle world x y expX expY hx hy hxy hX hY
  rw [wExp_eq oracle world x hx] at hX
  rw [wExp_eq oracle world y hy] at hY
  cases hX
  cases hY
  obtain ⟨x1, x2⟩ := range_bounds hx
  obtain ⟨y1, y2⟩ := range_bounds hy
  have hlt : y.toInt < x.toInt := hxy
  show (Uint256.ofNat (wExpF y.toInt)).val ≤ (Uint256.ofNat (wExpF x.toInt)).val
  rw [val_ofNat', val_ofNat', Nat.mod_eq_of_lt (wExpF_lt x1 x2), Nat.mod_eq_of_lt (wExpF_lt y1 y2)]
  exact wExpF_mono y1 x2 hlt.le

theorem wExpSucceeds : Spec.TickLibImport.wExpSucceeds := by
  intro oracle world x hx
  exact ⟨_, wExp_eq oracle world x hx⟩

end Midnight.TickLibImport
