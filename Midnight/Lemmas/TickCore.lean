import Midnight.TickLibImportSpec

/-!
Kernel-checked evaluation of the imported `tickToPrice` on concrete ticks.

`kernel_rfl` closes `lhs = rhs` with `Eq.refl lhs` without an elaborator
defeq check; the kernel checks the resulting declaration.
-/

open Compiler.CompilationModel.Denote

namespace Midnight.TickLibImport.Core

open Lean Elab Tactic Meta in
elab "kernel_rfl" : tactic => do
  let g ← getMainGoal
  let t ← whnfR (← g.getType)
  let some (α, lhs, _) := t.eq? | throwError "kernel_rfl: goal is not an equality"
  let u ← getLevel α
  g.assign (mkApp2 (mkConst ``Eq.refl [u]) α lhs)

/-- `tickToPrice` on a natural-number tick, read as a natural number. -/
def f (o : DenoteOracle) (w : Verity.ContractState) (t : Nat) : Option Nat :=
  (tickLib.tickToPrice o w (Verity.Core.Uint256.ofNat t)).map (·.val)

/-- `n` consecutive ticks from `t` succeed and are non-decreasing, starting
at least at `prev`. -/
def monoFrom (o : DenoteOracle) (w : Verity.ContractState) : Nat → Nat → Nat → Bool
  | 0, _, _ => true
  | k+1, t, prev => match f o w t with
    | some a => decide (prev ≤ a) && monoFrom o w k (t+1) a
    | none => false

theorem monoFrom_succ {o w} {n s prev : Nat} (h : monoFrom o w (n+1) s prev = true) :
    ∃ a, f o w s = some a ∧ prev ≤ a ∧ monoFrom o w n (s+1) a = true := by
  simp only [monoFrom] at h
  split at h
  · rename_i a ha
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨a, ha, h.1, h.2⟩
  · exact absurd h (by simp)

theorem step_of_monoFrom {o w} : ∀ (n s prev : Nat), monoFrom o w (n+1) s prev = true →
    ∀ i, i < n → ∃ a b, f o w (s+i) = some a ∧ f o w (s+i+1) = some b ∧ a ≤ b
  | 0, _, _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | n+1, s, prev, h, i, hi => by
    obtain ⟨a, ha, _, h'⟩ := monoFrom_succ h
    cases i with
    | zero =>
      obtain ⟨b, hb, hab, _⟩ := monoFrom_succ h'
      exact ⟨a, b, by simpa using ha, by simpa using hb, hab⟩
    | succ i =>
      obtain ⟨a', b', h1, h2, h3⟩ := step_of_monoFrom n (s+1) a h' i (by omega)
      refine ⟨a', b', ?_, ?_, h3⟩
      · rw [show s + (i+1) = s + 1 + i by omega]; exact h1
      · rw [show s + (i+1) + 1 = s + 1 + i + 1 by omega]; exact h2

end Midnight.TickLibImport.Core
