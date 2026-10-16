import ProofKit.Words

/-!
# Signed words as `Int`

`ofI a` is the two's-complement word of `a : Int` (`a` modulo `2^256`). The word
operations of the `Denote` interpreter commute with it, so a symbolic run of
signed (`int256`) code can be stated, and reasoned about, in `Int`:

* `wadd_ofI`, `wsub_ofI`, `wmul_ofI`: wrapping arithmetic is `Int` arithmetic
  modulo `2^256`.
* `toInt_ofI`, `word_eq_ofI`, `ofInt_val`: moving between `ofI`, `Int256`
  values and their words.
* `sdiv_ofI`: signed division of in-range words is `Int.tdiv` (rounds toward
  zero).
* `shl_ofI`: a left shift of a small value is multiplication by a power of two.
* `wordNormalize_eq`: literals (`eval_literal`) as `ofI`.

Comparisons (`eval_slt`, `eval_sgt`) read words through
`Int256.toInt (Int256.ofUint256 (Uint256.ofNat w))`; rewrite those with
`toInt_ofI`. Keep `2 ^ 256` unevaluated: once it becomes a 78-digit literal,
`Int.emod` rewrites stop matching.
-/

open Compiler.CompilationModel Compiler.CompilationModel.Denote
open Verity.Core

namespace ProofKit

/-- The word holding `a` modulo `2^256`. -/
def ofI (a : Int) : Nat := (a % 2 ^ 256).toNat

theorem ofI_cast (a : Int) : ((ofI a : Nat) : Int) = a % 2 ^ 256 := by
  unfold ofI
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))

theorem ofI_lt (a : Int) : ofI a < 2 ^ 256 := by
  have h := ofI_cast a
  have h2 : a % 2 ^ 256 < 2 ^ 256 := Int.emod_lt_of_pos _ (by omega)
  omega

theorem ofI_eq_iff (a b : Int) : ofI a = ofI b ↔ a % 2 ^ 256 = b % 2 ^ 256 := by
  constructor
  · intro h; rw [← ofI_cast, ← ofI_cast, h]
  · intro h; unfold ofI; rw [h]

theorem ofI_natCast (n : Nat) (h : n < 2 ^ 256) : ofI (n : Int) = n := by
  have h1 := ofI_cast n
  have h2 : (n : Int) % 2 ^ 256 = n := Int.emod_eq_of_lt (by omega) (by exact_mod_cast h)
  omega

theorem ofI_of_nonneg (a : Int) (h0 : 0 ≤ a) (h : a < 2 ^ 256) : ofI a = a.toNat := by
  unfold ofI; rw [Int.emod_eq_of_lt h0 h]

theorem cast_two_pow_256 : ((2 ^ 256 : Nat) : Int) = 2 ^ 256 := by
  rw [Int.natCast_pow]; rfl

theorem natCast_ofI (n : Nat) : ofI (n : Int) = n % 2 ^ 256 := by
  have h1 := ofI_cast n
  have h2 : ((n % 2 ^ 256 : Nat) : Int) = (n : Int) % 2 ^ 256 := by
    rw [Int.natCast_emod, cast_two_pow_256]
  omega

theorem wordNormalize_eq (n : Nat) : wordNormalize n = ofI (n : Int) := by
  rw [natCast_ofI]; rfl

theorem wadd_ofI (a b : Int) : wadd (ofI a) (ofI b) = ofI (a + b) := by
  show (ofI a % 2 ^ 256 + ofI b % 2 ^ 256) % 2 ^ 256 = ofI (a + b)
  rw [Nat.mod_eq_of_lt (ofI_lt a), Nat.mod_eq_of_lt (ofI_lt b)]
  have h1 := ofI_cast a
  have h2 := ofI_cast b
  have h3 := ofI_cast (a + b)
  have : (((ofI a + ofI b) % 2 ^ 256 : Nat) : Int) = ((ofI (a + b) : Nat) : Int) := by
    rw [Int.natCast_emod, Int.natCast_add, h1, h2, h3, cast_two_pow_256, ← Int.add_emod]
  exact_mod_cast this

theorem wmul_ofI (a b : Int) : wmul (ofI a) (ofI b) = ofI (a * b) := by
  show (ofI a % 2 ^ 256 * (ofI b % 2 ^ 256)) % 2 ^ 256 = ofI (a * b)
  rw [Nat.mod_eq_of_lt (ofI_lt a), Nat.mod_eq_of_lt (ofI_lt b)]
  have h1 := ofI_cast a
  have h2 := ofI_cast b
  have h3 := ofI_cast (a * b)
  have : (((ofI a * ofI b) % 2 ^ 256 : Nat) : Int) = ((ofI (a * b) : Nat) : Int) := by
    rw [Int.natCast_emod, Int.natCast_mul, h1, h2, h3, cast_two_pow_256, ← Int.mul_emod]
  exact_mod_cast this

theorem wsub_ofI (a b : Int) : wsub (ofI a) (ofI b) = ofI (a - b) := by
  show (Uint256.sub (Uint256.ofNat (ofI a)) (Uint256.ofNat (ofI b))).val = ofI (a - b)
  unfold Uint256.sub
  have ha := ofI_lt a
  have hb := ofI_lt b
  have h1 := ofI_cast a
  have h2 := ofI_cast b
  have h3 := ofI_cast (a - b)
  have hsub : (a - b) % 2 ^ 256 = (a % 2 ^ 256 - b % 2 ^ 256) % 2 ^ 256 := Int.sub_emod _ _ _
  simp only [Uint256.val_ofNat, Uint256.modulus, UINT256_MODULUS, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt hb]
  split
  · rename_i h
    show (ofI a - ofI b) % 2 ^ 256 = ofI (a - b)
    rw [Nat.mod_eq_of_lt (by omega)]
    have : (a % 2 ^ 256 - b % 2 ^ 256) % 2 ^ 256 = a % 2 ^ 256 - b % 2 ^ 256 :=
      Int.emod_eq_of_lt (by omega) (by omega)
    omega
  · rename_i h
    show (2 ^ 256 - (ofI b - ofI a)) % 2 ^ 256 = ofI (a - b)
    rw [Nat.mod_eq_of_lt (by omega)]
    have : (a % 2 ^ 256 - b % 2 ^ 256) % 2 ^ 256 = a % 2 ^ 256 - b % 2 ^ 256 + 2 ^ 256 := by
      omega
    omega

/-- A word read as `int256`. -/
theorem toInt_ofI (a : Int) (h1 : -2 ^ 255 ≤ a) (h2 : a < 2 ^ 255) :
    Int256.toInt (Int256.ofUint256 (Uint256.ofNat (ofI a))) = a := by
  have hc := ofI_cast a
  have hl := ofI_lt a
  unfold Int256.toInt
  simp only [Int256.ofUint256, Uint256.val_ofNat, Uint256.modulus, UINT256_MODULUS,
    Nat.mod_eq_of_lt hl, Int256.signBit, Int256.modulus, Int.ofNat_eq_natCast]
  by_cases ha : 0 ≤ a
  · have : a % 2 ^ 256 = a := Int.emod_eq_of_lt ha (by omega)
    rw [if_pos (by omega)]; omega
  · have : a % 2 ^ 256 = a + 2 ^ 256 := by
      omega
    rw [if_neg (by omega)]; rw [Int.natCast_pow]; omega

theorem word_eq_ofI (x : Int256) : x.toUint256.val = ofI x.toInt := by
  have hl : x.word.val < 2 ^ 256 := x.word.isLt
  have hc := ofI_cast x.toInt
  have ht : x.toInt = (x.word.val : Int) ∨ x.toInt = (x.word.val : Int) - 2 ^ 256 := by
    unfold Int256.toInt
    simp only [Int256.signBit, Int256.modulus, Uint256.modulus, UINT256_MODULUS,
      Int.ofNat_eq_natCast]
    split
    · left; rfl
    · right; rw [Int.natCast_pow]; rfl
  show x.word.val = _
  rcases ht with h | h <;> omega

theorem ofInt_val (a : Int) (h1 : -2 ^ 255 ≤ a) (h2 : a < 2 ^ 255) :
    (Int256.ofInt a).toUint256.val = ofI a := by
  have hc := ofI_cast a
  unfold Int256.ofInt
  split
  · rename_i h
    simp only [Int256.toUint256_ofUint256, Uint256.val_ofNat, Uint256.modulus, UINT256_MODULUS,
      Int256.modulus]
    have : a % 2 ^ 256 = a + 2 ^ 256 := by
      omega
    have hn : a.natAbs % 2 ^ 256 = a.natAbs := Nat.mod_eq_of_lt (by omega)
    rw [hn, Nat.mod_eq_of_lt (by omega)]
    omega
  · rename_i h
    simp only [Int256.toUint256_ofUint256, Uint256.val_ofNat, Uint256.modulus, UINT256_MODULUS]
    have : a % 2 ^ 256 = a := Int.emod_eq_of_lt (by omega) (by omega)
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-- Signed division of two in-range words truncates toward zero. -/
theorem sdiv_ofI (a b : Int) (ha1 : -2 ^ 255 < a) (ha2 : a < 2 ^ 255)
    (hb1 : -2 ^ 255 < b) (hb2 : b < 2 ^ 255) (hb : b ≠ 0) :
    (Int256.div (Int256.ofUint256 (Uint256.ofNat (ofI a)))
      (Int256.ofUint256 (Uint256.ofNat (ofI b)))).toUint256.val = ofI (a.tdiv b) := by
  unfold Int256.div
  simp only [toInt_ofI a (by omega) ha2, toInt_ofI b (by omega) hb2, if_neg hb,
    Int256.signedAbsNat]
  have hn : (a.tdiv b).natAbs = a.natAbs / b.natAbs := Int.natAbs_tdiv a b
  have hq : (a.natAbs / b.natAbs : Nat) ≤ a.natAbs := Nat.div_le_self _ _
  have hle : (a.tdiv b).natAbs ≤ a.natAbs := by omega
  split
  · rename_i hs
    have heq : ((a.natAbs / b.natAbs : Nat) : Int) = a.tdiv b := by
      rw [← hn]
      have : 0 ≤ a.tdiv b := by
        simp only [beq_iff_eq, decide_eq_decide] at hs
        rcases Int.lt_or_le a 0 with h | h <;> rcases Int.lt_or_le b 0 with h' | h'
        · exact Int.tdiv_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
        · exact absurd (hs.mp h) (by omega)
        · exact absurd (hs.mpr h') (by omega)
        · exact Int.tdiv_nonneg h h'
      omega
    rw [Int.ofNat_eq_natCast, heq, ofInt_val _ (by omega) (by omega)]
  · rename_i hs
    have heq : -((a.natAbs / b.natAbs : Nat) : Int) = a.tdiv b := by
      rw [← hn]
      have : a.tdiv b ≤ 0 := by
        simp only [beq_iff_eq, decide_eq_decide] at hs
        rcases Int.lt_or_le a 0 with h | h <;> rcases Int.lt_or_le b 0 with h' | h'
        · exact absurd ⟨fun _ => h', fun _ => h⟩ hs
        · have h2 : 0 ≤ (-a).tdiv b := Int.tdiv_nonneg (by omega) h'
          rw [Int.neg_tdiv] at h2; omega
        · exact Int.tdiv_nonpos_of_nonneg_of_nonpos h (by omega)
        · exact absurd ⟨fun h1 => absurd h1 (by omega), fun h1 => absurd h1 (by omega)⟩ hs
      omega
    rw [Int.ofNat_eq_natCast, heq, ofInt_val _ (by omega) (by omega)]

/-- `shl` of a small nonnegative value by a small shift. -/
theorem shl_ofI (q e : Int) (hq0 : 0 ≤ q) (hq : q < 256) (he0 : 0 ≤ e) (he : e < 2 ^ 256) :
    (Uint256.shl (Uint256.ofNat (ofI q)) (Uint256.ofNat (ofI e))).val =
      (e.toNat * 2 ^ q.toNat) % 2 ^ 256 := by
  rw [ofI_of_nonneg q hq0 (by omega), ofI_of_nonneg e he0 he]
  unfold Uint256.shl
  simp only [Uint256.val_ofNat, Uint256.modulus, UINT256_MODULUS, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (a := q.toNat) (by omega), Nat.mod_eq_of_lt (a := e.toNat) (by omega)]

end ProofKit
