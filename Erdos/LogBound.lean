import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Analysis.Complex.ExponentialBounds

open Nat Real

namespace Erdos728

/-- Sum of digits in base p. -/
def sumDigits (p n : ℕ) : ℕ := (Nat.digits p n).sum

lemma sumDigits_le_log (p n : ℕ) (hp : 1 < p) :
    sumDigits p n ≤ (p - 1) * (Nat.log p n + 1) := by
  sorry

lemma nat_log_le_real_log {p n : ℕ} (hp : 1 < p) (hn : n ≠ 0) :
    (Nat.log p n : ℝ) ≤ Real.log n / Real.log p := by
  sorry

lemma sumDigits_bound_real {p : ℕ} (hp : 1 < p) (n : ℕ) :
    (sumDigits p n : ℝ) ≤ (p - 1) * (Real.log n / Real.log p + 1) := by
  have h_le := sumDigits_le_log p n hp
  rw [← Nat.cast_le (α := ℝ)] at h_le
  apply le_trans h_le
  rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [Nat.cast_sub (le_of_lt hp), Nat.cast_one]
  have h_nonneg : 0 ≤ (p : ℝ) - 1 := sub_nonneg.mpr (by norm_cast; exact le_of_lt hp)
  apply mul_le_mul_of_nonneg_left _ h_nonneg
  if h : n = 0 then
    simp [h, Real.log_zero]
  else
    sorry

lemma log_n_le_log_n_plus_2 (n : ℕ) : Real.log n ≤ Real.log (n + 2) := by
  if hn : n = 0 then
    rw [hn]; simp; norm_num
    apply le_of_lt
    apply Real.log_pos
    norm_num
  else
    apply Real.log_le_log
    · norm_cast; omega
    · norm_cast; omega

/-- The calculation showing sumDigits p a + sumDigits p b ≤ C * log n when a, b < 2n. -/
lemma sumDigits_log_bound {p : ℕ} (hp : 1 < p) (n a b : ℕ)
    (ha : a < 2 * n) (hb : b < 2 * n) :
    ∃ C, (sumDigits p a : ℝ) + sumDigits p b ≤ C * Real.log (n + 2) := by
  use (2 * (p - 1) / Real.log p) + 5 * (p - 1)
  sorry

end Erdos728
