import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.BigOperators.Group.List

open Nat Real

/-- Sum of digits in base p. -/
def sumDigits (p n : ℕ) : ℕ := (Nat.digits p n).sum

lemma sumDigits_le_log (p n : ℕ) (hp : 1 < p) :
    sumDigits p n ≤ (p - 1) * (Nat.log p n + 1) := by
  if h : n = 0 then
    simp [sumDigits, h]
  else
    rw [sumDigits]
    trans (digits p n).length * (p - 1)
    · -- Use nsmul which is multiplication on Nat
      have : (digits p n).length * (p - 1) = (digits p n).length • (p - 1) := by simp [nsmul_eq_mul]
      rw [this]
      apply List.sum_le_card_nsmul
      intro d hd
      apply Nat.le_sub_one_of_lt
      exact Nat.digits_lt_base hp hd
    · rw [digits_len p n hp h, Nat.mul_comm]

lemma delta_le_sumDigits {p : ℕ} (hp : p.Prime) (a b n : ℕ)
    (h : padicValNat p a.factorial + padicValNat p b.factorial ≤ padicValNat p n.factorial) :
    a + b - n ≤ sumDigits p a + sumDigits p b - sumDigits p n := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h_mul : (p - 1) * (padicValNat p a.factorial + padicValNat p b.factorial) ≤
      (p - 1) * padicValNat p n.factorial :=
    Nat.mul_le_mul_left (p - 1) h
  rw [Nat.mul_add, sub_one_mul_padicValNat_factorial, sub_one_mul_padicValNat_factorial,
    sub_one_mul_padicValNat_factorial] at h_mul
  have h_Sa := digit_sum_le p a
  have h_Sb := digit_sum_le p b
  have h_Sn := digit_sum_le p n
  rw [sumDigits, sumDigits, sumDigits]
  omega

lemma a_lt_two_n {P a b n : ℕ} (hP : 0 < P) (hnP : n > P)
    (h : ∀ p, p.Prime → P < p → padicValNat p a.factorial + padicValNat p b.factorial ≤ padicValNat p n.factorial) :
    a < 2 * n := by
  by_contra! h_ge
  have hn_pos : 0 < n := lt_trans hP hnP
  have hn_ne_zero : n ≠ 0 := hn_pos.ne'
  have ⟨p, hp_prime, hn_lt_p, hp_le_2n⟩ := Nat.exists_prime_lt_and_le_two_mul n hn_ne_zero
  have hp_gt_P : P < p := lt_trans hnP hn_lt_p
  haveI : Fact p.Prime := ⟨hp_prime⟩
  specialize h p hp_prime hp_gt_P
  have h_val_n_zero : padicValNat p n.factorial = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro h_dvd
    have : p ≤ n := (Nat.Prime.dvd_factorial hp_prime).mp h_dvd
    linarith
  rw [h_val_n_zero] at h
  have h_le_a : p ≤ a := le_trans hp_le_2n h_ge
  have h_dvd_a : p ∣ a.factorial := Nat.dvd_factorial hp_prime.pos h_le_a
  have h_pos_val_a : 1 ≤ padicValNat p a.factorial :=
    one_le_padicValNat_of_dvd a.factorial_ne_zero h_dvd_a
  omega

/-- If n ≤ P, then a and b are also bounded by any prime p > P. -/
lemma erdos_729_small_n_prime_bound {P a b n p : ℕ} (hp : P < p) (hp_prime : p.Prime) (hn_le_P : n ≤ P)
    (h : padicValNat p a.factorial + padicValNat p b.factorial ≤ padicValNat p n.factorial) :
    a < p ∧ b < p := by
  have h_n_lt_p : n < p := lt_of_le_of_lt hn_le_P hp
  have h_val_n : padicValNat p n.factorial = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro h_dvd
    have h_le_n : p ≤ n := (Nat.Prime.dvd_factorial hp_prime).mp h_dvd
    linarith
  rw [h_val_n] at h
  have h_val_a : padicValNat p a.factorial = 0 := by
    apply Nat.eq_zero_of_le_zero
    trans (padicValNat p a.factorial + padicValNat p b.factorial)
    · apply Nat.le_add_right
    · exact h
  have h_val_b : padicValNat p b.factorial = 0 := by
    apply Nat.eq_zero_of_le_zero
    trans (padicValNat p a.factorial + padicValNat p b.factorial)
    · apply Nat.le_add_left
    · exact h
  haveI : Fact p.Prime := ⟨hp_prime⟩
  constructor
  · by_contra! h_ge
    have h_dvd : p ∣ a.factorial := Nat.dvd_factorial hp_prime.pos h_ge
    have h_pos : 0 < padicValNat p a.factorial :=
       lt_of_lt_of_le zero_lt_one (one_le_padicValNat_of_dvd (factorial_ne_zero a) h_dvd)
    linarith
  · by_contra! h_ge
    have h_dvd : p ∣ b.factorial := Nat.dvd_factorial hp_prime.pos h_ge
    have h_pos : 0 < padicValNat p b.factorial :=
       lt_of_lt_of_le zero_lt_one (one_le_padicValNat_of_dvd (factorial_ne_zero b) h_dvd)
    linarith

/-- If n ≤ P, then a and b are also bounded, since for p > P, v_p(a!) + v_p(b!) ≤ v_p(n!) = 0. -/
lemma erdos_729_small_n (P : ℕ) (hP : 0 < P) :
    ∃ C > 0, ∀ a b n : ℕ, n ≤ P →
    (∀ p, p.Prime → P < p → padicValNat p a.factorial + padicValNat p b.factorial ≤ padicValNat p n.factorial) →
    (a : ℝ) + b ≤ C := by
  -- We can choose a prime p > P.
  have h_exists : ∃ p, p.Prime ∧ P < p := by
    obtain ⟨p, hp_ge, hp_prime⟩ := Nat.exists_infinite_primes (P + 1)
    use p
    constructor
    · exact hp_prime
    · exact lt_of_succ_le hp_ge
  obtain ⟨p, hp_prime, hp_gt_P⟩ := h_exists
  use (2 * p : ℝ)
  constructor
  · norm_num; apply hp_prime.pos
  intro a b n hn_le_P h
  specialize h p hp_prime hp_gt_P
  have h_bounds := erdos_729_small_n_prime_bound hp_gt_P hp_prime hn_le_P h
  rw [← Nat.cast_add]
  norm_cast
  linarith

/-- (Nat.log p n : ℝ) ≤ Real.log n / Real.log p. Pure casting lemma. -/
lemma nat_log_le_real_log {p n : ℕ} (hp : 1 < p) (hn : n ≠ 0) :
    (Nat.log p n : ℝ) ≤ Real.log n / Real.log p := by
  have hp_real : 1 < (p : ℝ) := by exact_mod_cast hp
  set k := Nat.log p n
  have h_pow : p ^ k ≤ n := Nat.pow_log_le_self p hn
  have h_pow_real : (p : ℝ) ^ k ≤ n := by
    rw [← Nat.cast_pow]
    exact_mod_cast h_pow
  have h_log : Real.log ((p : ℝ) ^ k) ≤ Real.log n :=
    Real.log_le_log (by positivity) h_pow_real
  rw [Real.log_pow] at h_log
  refine (le_div_iff₀ ?_).mpr h_log
  exact Real.log_pos hp_real

lemma log_n_le_log_n_plus_2 (n : ℕ) : Real.log n ≤ Real.log (n + 2) := by
  sorry

lemma sumDigits_bound_real {p : ℕ} (hp : 1 < p) (n : ℕ) :
    (sumDigits p n : ℝ) ≤ (p - 1) * (Real.log n / Real.log p + 1) := by
  sorry

/-- The calculation showing sumDigits p a + sumDigits p b ≤ C * log n when a, b < 2n. -/
lemma sumDigits_log_bound {p : ℕ} (hp : 1 < p) (n a b : ℕ)
    (ha : a < 2 * n) (hb : b < 2 * n) :
    ∃ C, (sumDigits p a : ℝ) + sumDigits p b ≤ C * Real.log (n + 2) := by
  sorry

/-- The large n case (n > P). -/
lemma erdos_729_large_n (P a b n : ℕ) (hP : 0 < P) (hnP : n > P)
    (h_div : ∀ p, p.Prime → P < p → padicValNat p a.factorial + padicValNat p b.factorial ≤ padicValNat p n.factorial) :
    ∃ C > 0, (a : ℝ) + b ≤ n + C * Real.log (n + 2) := by
  sorry

theorem erdos_729 (P : ℕ) (hP : 0 < P) :
    ∃ C > (0 : ℝ), ∀ a b n : ℕ,
      (∀ p, p.Prime → P < p →
        padicValNat p a.factorial + padicValNat p b.factorial ≤ padicValNat p n.factorial) →
      (a : ℝ) + b ≤ n + C * Real.log (n + 2) := by
  sorry
