import Midnight.Lemmas.TickChunk0
import Midnight.Lemmas.TickChunk1
import Midnight.Lemmas.TickChunk2
import Midnight.Lemmas.TickChunk3
import Midnight.Lemmas.TickChunk4
import Midnight.Lemmas.TickChunk5
import Midnight.Lemmas.TickChunk6
import Midnight.Lemmas.TickChunk7
import Midnight.Lemmas.TickChunk8
import Midnight.Lemmas.TickChunk9
import Midnight.Lemmas.TickChunk10
import Midnight.Lemmas.TickChunk11
import Midnight.Lemmas.TickChunk12
import Midnight.Lemmas.TickChunk13
import Midnight.Lemmas.TickChunk14
import Midnight.Lemmas.TickChunk15
import Midnight.Lemmas.TickChunk16
import Midnight.Lemmas.TickChunk17
import Midnight.Lemmas.TickChunk18
import Midnight.Lemmas.TickChunk19
import Midnight.Lemmas.TickChunk20
import Midnight.Lemmas.TickChunk21
import Midnight.Lemmas.TickChunk22
import Midnight.Lemmas.TickChunk23
import Midnight.Lemmas.TickChunk24
import Midnight.Lemmas.TickChunk25
import Midnight.Lemmas.TickChunk26
import Midnight.Lemmas.TickChunk27
import Midnight.Lemmas.TickChunk28
import Midnight.Lemmas.TickChunk29
import Midnight.Lemmas.TickChunk30
import Midnight.Lemmas.TickChunk31
import Midnight.Lemmas.TickChunk32
import Midnight.Lemmas.TickChunk33
import Midnight.Lemmas.TickChunk34
import Midnight.Lemmas.TickChunk35
import Midnight.Lemmas.TickChunk36
import Midnight.Lemmas.TickChunk37
import Midnight.Lemmas.TickChunk38
import Midnight.Lemmas.TickChunk39
import Midnight.Lemmas.TickChunk40
import Midnight.Lemmas.TickChunk41
import Midnight.Lemmas.TickChunk42
import Midnight.Lemmas.TickChunk43
import Midnight.Lemmas.TickChunk44
import Midnight.Lemmas.TickChunk45
import Midnight.Lemmas.TickChunk46
import Midnight.Lemmas.TickChunk47
import Midnight.Lemmas.TickChunk48
import Midnight.Lemmas.TickChunk49
import Midnight.Lemmas.TickChunk50
import Midnight.Lemmas.TickChunk51
import Midnight.Lemmas.TickChunk52
import Midnight.Lemmas.TickChunk53
import Midnight.Lemmas.TickChunk54
import Midnight.Lemmas.TickChunk55
import Midnight.Lemmas.TickChunk56
import Midnight.Lemmas.TickChunk57
import Midnight.Lemmas.TickChunk58
import Midnight.Lemmas.TickChunk59
import Midnight.Lemmas.TickChunk60
import Midnight.Lemmas.TickChunk61
import Midnight.Lemmas.TickChunk62
import Midnight.Lemmas.TickChunk63
import Midnight.Lemmas.TickChunk64
import Midnight.Lemmas.TickChunk65
import Midnight.Lemmas.TickChunk66
import Midnight.Lemmas.TickChunk67

open Compiler.CompilationModel.Denote
open Midnight.TickLibImport.Core

namespace Midnight.TickLibImport

set_option maxRecDepth 100000 in
theorem step (o : DenoteOracle) (w : Verity.ContractState) (t : Nat) (ht : t < 6744) :
    ∃ a b, f o w t = some a ∧ f o w (t+1) = some b ∧ a ≤ b := by
  if h0 : t < 100 then
    have := step_of_monoFrom 100 0 0 (chunk0 o w) (t - 0) (by omega)
    rw [show 0 + (t - 0) = t by omega] at this
    exact this
  else
  if h1 : t < 200 then
    have := step_of_monoFrom 100 100 0 (chunk1 o w) (t - 100) (by omega)
    rw [show 100 + (t - 100) = t by omega] at this
    exact this
  else
  if h2 : t < 300 then
    have := step_of_monoFrom 100 200 0 (chunk2 o w) (t - 200) (by omega)
    rw [show 200 + (t - 200) = t by omega] at this
    exact this
  else
  if h3 : t < 400 then
    have := step_of_monoFrom 100 300 0 (chunk3 o w) (t - 300) (by omega)
    rw [show 300 + (t - 300) = t by omega] at this
    exact this
  else
  if h4 : t < 500 then
    have := step_of_monoFrom 100 400 0 (chunk4 o w) (t - 400) (by omega)
    rw [show 400 + (t - 400) = t by omega] at this
    exact this
  else
  if h5 : t < 600 then
    have := step_of_monoFrom 100 500 0 (chunk5 o w) (t - 500) (by omega)
    rw [show 500 + (t - 500) = t by omega] at this
    exact this
  else
  if h6 : t < 700 then
    have := step_of_monoFrom 100 600 0 (chunk6 o w) (t - 600) (by omega)
    rw [show 600 + (t - 600) = t by omega] at this
    exact this
  else
  if h7 : t < 800 then
    have := step_of_monoFrom 100 700 0 (chunk7 o w) (t - 700) (by omega)
    rw [show 700 + (t - 700) = t by omega] at this
    exact this
  else
  if h8 : t < 900 then
    have := step_of_monoFrom 100 800 0 (chunk8 o w) (t - 800) (by omega)
    rw [show 800 + (t - 800) = t by omega] at this
    exact this
  else
  if h9 : t < 1000 then
    have := step_of_monoFrom 100 900 0 (chunk9 o w) (t - 900) (by omega)
    rw [show 900 + (t - 900) = t by omega] at this
    exact this
  else
  if h10 : t < 1100 then
    have := step_of_monoFrom 100 1000 0 (chunk10 o w) (t - 1000) (by omega)
    rw [show 1000 + (t - 1000) = t by omega] at this
    exact this
  else
  if h11 : t < 1200 then
    have := step_of_monoFrom 100 1100 0 (chunk11 o w) (t - 1100) (by omega)
    rw [show 1100 + (t - 1100) = t by omega] at this
    exact this
  else
  if h12 : t < 1300 then
    have := step_of_monoFrom 100 1200 0 (chunk12 o w) (t - 1200) (by omega)
    rw [show 1200 + (t - 1200) = t by omega] at this
    exact this
  else
  if h13 : t < 1400 then
    have := step_of_monoFrom 100 1300 0 (chunk13 o w) (t - 1300) (by omega)
    rw [show 1300 + (t - 1300) = t by omega] at this
    exact this
  else
  if h14 : t < 1500 then
    have := step_of_monoFrom 100 1400 0 (chunk14 o w) (t - 1400) (by omega)
    rw [show 1400 + (t - 1400) = t by omega] at this
    exact this
  else
  if h15 : t < 1600 then
    have := step_of_monoFrom 100 1500 0 (chunk15 o w) (t - 1500) (by omega)
    rw [show 1500 + (t - 1500) = t by omega] at this
    exact this
  else
  if h16 : t < 1700 then
    have := step_of_monoFrom 100 1600 0 (chunk16 o w) (t - 1600) (by omega)
    rw [show 1600 + (t - 1600) = t by omega] at this
    exact this
  else
  if h17 : t < 1800 then
    have := step_of_monoFrom 100 1700 0 (chunk17 o w) (t - 1700) (by omega)
    rw [show 1700 + (t - 1700) = t by omega] at this
    exact this
  else
  if h18 : t < 1900 then
    have := step_of_monoFrom 100 1800 0 (chunk18 o w) (t - 1800) (by omega)
    rw [show 1800 + (t - 1800) = t by omega] at this
    exact this
  else
  if h19 : t < 2000 then
    have := step_of_monoFrom 100 1900 0 (chunk19 o w) (t - 1900) (by omega)
    rw [show 1900 + (t - 1900) = t by omega] at this
    exact this
  else
  if h20 : t < 2100 then
    have := step_of_monoFrom 100 2000 0 (chunk20 o w) (t - 2000) (by omega)
    rw [show 2000 + (t - 2000) = t by omega] at this
    exact this
  else
  if h21 : t < 2200 then
    have := step_of_monoFrom 100 2100 0 (chunk21 o w) (t - 2100) (by omega)
    rw [show 2100 + (t - 2100) = t by omega] at this
    exact this
  else
  if h22 : t < 2300 then
    have := step_of_monoFrom 100 2200 0 (chunk22 o w) (t - 2200) (by omega)
    rw [show 2200 + (t - 2200) = t by omega] at this
    exact this
  else
  if h23 : t < 2400 then
    have := step_of_monoFrom 100 2300 0 (chunk23 o w) (t - 2300) (by omega)
    rw [show 2300 + (t - 2300) = t by omega] at this
    exact this
  else
  if h24 : t < 2500 then
    have := step_of_monoFrom 100 2400 0 (chunk24 o w) (t - 2400) (by omega)
    rw [show 2400 + (t - 2400) = t by omega] at this
    exact this
  else
  if h25 : t < 2600 then
    have := step_of_monoFrom 100 2500 0 (chunk25 o w) (t - 2500) (by omega)
    rw [show 2500 + (t - 2500) = t by omega] at this
    exact this
  else
  if h26 : t < 2700 then
    have := step_of_monoFrom 100 2600 0 (chunk26 o w) (t - 2600) (by omega)
    rw [show 2600 + (t - 2600) = t by omega] at this
    exact this
  else
  if h27 : t < 2800 then
    have := step_of_monoFrom 100 2700 0 (chunk27 o w) (t - 2700) (by omega)
    rw [show 2700 + (t - 2700) = t by omega] at this
    exact this
  else
  if h28 : t < 2900 then
    have := step_of_monoFrom 100 2800 0 (chunk28 o w) (t - 2800) (by omega)
    rw [show 2800 + (t - 2800) = t by omega] at this
    exact this
  else
  if h29 : t < 3000 then
    have := step_of_monoFrom 100 2900 0 (chunk29 o w) (t - 2900) (by omega)
    rw [show 2900 + (t - 2900) = t by omega] at this
    exact this
  else
  if h30 : t < 3100 then
    have := step_of_monoFrom 100 3000 0 (chunk30 o w) (t - 3000) (by omega)
    rw [show 3000 + (t - 3000) = t by omega] at this
    exact this
  else
  if h31 : t < 3200 then
    have := step_of_monoFrom 100 3100 0 (chunk31 o w) (t - 3100) (by omega)
    rw [show 3100 + (t - 3100) = t by omega] at this
    exact this
  else
  if h32 : t < 3300 then
    have := step_of_monoFrom 100 3200 0 (chunk32 o w) (t - 3200) (by omega)
    rw [show 3200 + (t - 3200) = t by omega] at this
    exact this
  else
  if h33 : t < 3400 then
    have := step_of_monoFrom 100 3300 0 (chunk33 o w) (t - 3300) (by omega)
    rw [show 3300 + (t - 3300) = t by omega] at this
    exact this
  else
  if h34 : t < 3500 then
    have := step_of_monoFrom 100 3400 0 (chunk34 o w) (t - 3400) (by omega)
    rw [show 3400 + (t - 3400) = t by omega] at this
    exact this
  else
  if h35 : t < 3600 then
    have := step_of_monoFrom 100 3500 0 (chunk35 o w) (t - 3500) (by omega)
    rw [show 3500 + (t - 3500) = t by omega] at this
    exact this
  else
  if h36 : t < 3700 then
    have := step_of_monoFrom 100 3600 0 (chunk36 o w) (t - 3600) (by omega)
    rw [show 3600 + (t - 3600) = t by omega] at this
    exact this
  else
  if h37 : t < 3800 then
    have := step_of_monoFrom 100 3700 0 (chunk37 o w) (t - 3700) (by omega)
    rw [show 3700 + (t - 3700) = t by omega] at this
    exact this
  else
  if h38 : t < 3900 then
    have := step_of_monoFrom 100 3800 0 (chunk38 o w) (t - 3800) (by omega)
    rw [show 3800 + (t - 3800) = t by omega] at this
    exact this
  else
  if h39 : t < 4000 then
    have := step_of_monoFrom 100 3900 0 (chunk39 o w) (t - 3900) (by omega)
    rw [show 3900 + (t - 3900) = t by omega] at this
    exact this
  else
  if h40 : t < 4100 then
    have := step_of_monoFrom 100 4000 0 (chunk40 o w) (t - 4000) (by omega)
    rw [show 4000 + (t - 4000) = t by omega] at this
    exact this
  else
  if h41 : t < 4200 then
    have := step_of_monoFrom 100 4100 0 (chunk41 o w) (t - 4100) (by omega)
    rw [show 4100 + (t - 4100) = t by omega] at this
    exact this
  else
  if h42 : t < 4300 then
    have := step_of_monoFrom 100 4200 0 (chunk42 o w) (t - 4200) (by omega)
    rw [show 4200 + (t - 4200) = t by omega] at this
    exact this
  else
  if h43 : t < 4400 then
    have := step_of_monoFrom 100 4300 0 (chunk43 o w) (t - 4300) (by omega)
    rw [show 4300 + (t - 4300) = t by omega] at this
    exact this
  else
  if h44 : t < 4500 then
    have := step_of_monoFrom 100 4400 0 (chunk44 o w) (t - 4400) (by omega)
    rw [show 4400 + (t - 4400) = t by omega] at this
    exact this
  else
  if h45 : t < 4600 then
    have := step_of_monoFrom 100 4500 0 (chunk45 o w) (t - 4500) (by omega)
    rw [show 4500 + (t - 4500) = t by omega] at this
    exact this
  else
  if h46 : t < 4700 then
    have := step_of_monoFrom 100 4600 0 (chunk46 o w) (t - 4600) (by omega)
    rw [show 4600 + (t - 4600) = t by omega] at this
    exact this
  else
  if h47 : t < 4800 then
    have := step_of_monoFrom 100 4700 0 (chunk47 o w) (t - 4700) (by omega)
    rw [show 4700 + (t - 4700) = t by omega] at this
    exact this
  else
  if h48 : t < 4900 then
    have := step_of_monoFrom 100 4800 0 (chunk48 o w) (t - 4800) (by omega)
    rw [show 4800 + (t - 4800) = t by omega] at this
    exact this
  else
  if h49 : t < 5000 then
    have := step_of_monoFrom 100 4900 0 (chunk49 o w) (t - 4900) (by omega)
    rw [show 4900 + (t - 4900) = t by omega] at this
    exact this
  else
  if h50 : t < 5100 then
    have := step_of_monoFrom 100 5000 0 (chunk50 o w) (t - 5000) (by omega)
    rw [show 5000 + (t - 5000) = t by omega] at this
    exact this
  else
  if h51 : t < 5200 then
    have := step_of_monoFrom 100 5100 0 (chunk51 o w) (t - 5100) (by omega)
    rw [show 5100 + (t - 5100) = t by omega] at this
    exact this
  else
  if h52 : t < 5300 then
    have := step_of_monoFrom 100 5200 0 (chunk52 o w) (t - 5200) (by omega)
    rw [show 5200 + (t - 5200) = t by omega] at this
    exact this
  else
  if h53 : t < 5400 then
    have := step_of_monoFrom 100 5300 0 (chunk53 o w) (t - 5300) (by omega)
    rw [show 5300 + (t - 5300) = t by omega] at this
    exact this
  else
  if h54 : t < 5500 then
    have := step_of_monoFrom 100 5400 0 (chunk54 o w) (t - 5400) (by omega)
    rw [show 5400 + (t - 5400) = t by omega] at this
    exact this
  else
  if h55 : t < 5600 then
    have := step_of_monoFrom 100 5500 0 (chunk55 o w) (t - 5500) (by omega)
    rw [show 5500 + (t - 5500) = t by omega] at this
    exact this
  else
  if h56 : t < 5700 then
    have := step_of_monoFrom 100 5600 0 (chunk56 o w) (t - 5600) (by omega)
    rw [show 5600 + (t - 5600) = t by omega] at this
    exact this
  else
  if h57 : t < 5800 then
    have := step_of_monoFrom 100 5700 0 (chunk57 o w) (t - 5700) (by omega)
    rw [show 5700 + (t - 5700) = t by omega] at this
    exact this
  else
  if h58 : t < 5900 then
    have := step_of_monoFrom 100 5800 0 (chunk58 o w) (t - 5800) (by omega)
    rw [show 5800 + (t - 5800) = t by omega] at this
    exact this
  else
  if h59 : t < 6000 then
    have := step_of_monoFrom 100 5900 0 (chunk59 o w) (t - 5900) (by omega)
    rw [show 5900 + (t - 5900) = t by omega] at this
    exact this
  else
  if h60 : t < 6100 then
    have := step_of_monoFrom 100 6000 0 (chunk60 o w) (t - 6000) (by omega)
    rw [show 6000 + (t - 6000) = t by omega] at this
    exact this
  else
  if h61 : t < 6200 then
    have := step_of_monoFrom 100 6100 0 (chunk61 o w) (t - 6100) (by omega)
    rw [show 6100 + (t - 6100) = t by omega] at this
    exact this
  else
  if h62 : t < 6300 then
    have := step_of_monoFrom 100 6200 0 (chunk62 o w) (t - 6200) (by omega)
    rw [show 6200 + (t - 6200) = t by omega] at this
    exact this
  else
  if h63 : t < 6400 then
    have := step_of_monoFrom 100 6300 0 (chunk63 o w) (t - 6300) (by omega)
    rw [show 6300 + (t - 6300) = t by omega] at this
    exact this
  else
  if h64 : t < 6500 then
    have := step_of_monoFrom 100 6400 0 (chunk64 o w) (t - 6400) (by omega)
    rw [show 6400 + (t - 6400) = t by omega] at this
    exact this
  else
  if h65 : t < 6600 then
    have := step_of_monoFrom 100 6500 0 (chunk65 o w) (t - 6500) (by omega)
    rw [show 6500 + (t - 6500) = t by omega] at this
    exact this
  else
  if h66 : t < 6700 then
    have := step_of_monoFrom 100 6600 0 (chunk66 o w) (t - 6600) (by omega)
    rw [show 6600 + (t - 6600) = t by omega] at this
    exact this
  else
  if h67 : t < 6744 then
    have := step_of_monoFrom 44 6700 0 (chunk67 o w) (t - 6700) (by omega)
    rw [show 6700 + (t - 6700) = t by omega] at this
    exact this
  else
  omega

theorem f_isSome (o : DenoteOracle) (w : Verity.ContractState) (t : Nat) (ht : t ≤ 6744) :
    ∃ a, f o w t = some a := by
  cases t with
  | zero => obtain ⟨a, _, h, _, _⟩ := step o w 0 (by omega); exact ⟨a, h⟩
  | succ t => obtain ⟨_, b, _, h, _⟩ := step o w t (by omega); exact ⟨b, h⟩

theorem f_mono (o : DenoteOracle) (w : Verity.ContractState) :
    ∀ (d t : Nat), t + d ≤ 6744 → ∀ a b, f o w t = some a → f o w (t + d) = some b → a ≤ b
  | 0, t, _, a, b, ha, hb => by
    rw [Nat.add_zero, ha] at hb; cases hb; exact Nat.le_refl _
  | d+1, t, hd, a, b, ha, hb => by
    obtain ⟨a', c, ha', hc, hac⟩ := step o w t (by omega)
    rw [ha] at ha'; cases ha'
    have := f_mono o w d (t+1) (by omega) c b hc (by rw [show t + 1 + d = t + (d+1) by omega]; exact hb)
    omega

theorem ofNat_val (x : Verity.Core.Uint256) : Verity.Core.Uint256.ofNat x.val = x := by
  apply Verity.Core.Uint256.ext
  exact Nat.mod_eq_of_lt x.isLt

theorem f_val (o : DenoteOracle) (w : Verity.ContractState) (x : Verity.Core.Uint256) :
    f o w x.val = (tickLib.tickToPrice o w x).map (·.val) := by
  simp only [f, ofNat_val]

theorem tickToPriceIsMonotonic : Spec.TickLibImport.tickToPriceIsMonotonic := by
  intro o w t1 t2 p1 p2 h2 hlt h1 hp2
  have hlt' : t1.val < t2.val := hlt
  have e1 := f_val o w t1
  have e2 := f_val o w t2
  rw [h1] at e1; rw [hp2] at e2
  have := f_mono o w (t2.val - t1.val) t1.val
    (by simp only [Spec.TickLibImport.maxTick] at h2; omega) p1.val p2.val e1
    (by rw [show t1.val + (t2.val - t1.val) = t2.val by omega]; exact e2)
  exact this

theorem tickToPriceSucceeds : Spec.TickLibImport.tickToPriceSucceeds := by
  intro o w t ht
  obtain ⟨a, ha⟩ := f_isSome o w t.val (by simpa [Spec.TickLibImport.maxTick] using ht)
  rw [f_val] at ha
  cases h : tickLib.tickToPrice o w t with
  | none => rw [h] at ha; cases ha
  | some p => exact ⟨p, rfl⟩

end Midnight.TickLibImport
