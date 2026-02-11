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
    · rw [digits_len p n hp h, mul_comm]

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

lemma nat_log_le_real_log {p n : ℕ} (hp : 1 < p) (hn : n ≠ 0) :
    (Nat.log p n : ℝ) ≤ Real.log n / Real.log p := by
  have h_p_gt_1 : 1 < (p : ℝ) := by norm_cast; exact hp
  have h_log_p_pos : 0 < Real.log p := Real.log_pos h_p_gt_1
  rw [le_div_iff₀ h_log_p_pos]
  -- Nat.log p n is the greatest k such that p^k ≤ n
  -- So p^(Nat.log p n) ≤ n
  -- Taking log: Nat.log p n * log p ≤ log n
  have h_pow_nat : p ^ (Nat.log p n) ≤ n := Nat.pow_log_le_self p hn
  have h_pow_real : (p : ℝ) ^ (Nat.log p n) ≤ n := by
    rw [← Nat.cast_pow]
    norm_cast
    exact h_pow_nat
  rw [Real.log_pow] at *
  apply Real.log_le_log _ _ h_pow_real
  · apply pow_pos; exact lt_trans zero_lt_one h_p_gt_1
  · exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)

lemma sumDigits_bound_real {p : ℕ} (hp : 1 < p) (n : ℕ) :
    (sumDigits p n : ℝ) ≤ (p - 1) * (Real.log n / Real.log p + 1) := by
  have h_le := sumDigits_le_log p n hp
  rw [← Nat.cast_le (α := ℝ)] at h_le
  apply le_trans h_le
  rw [Nat.cast_mul, Nat.cast_sub (le_of_lt hp), Nat.cast_one, Nat.cast_add, Nat.cast_one]
  have h_nonneg : 0 ≤ (p : ℝ) - 1 := sub_nonneg.mpr (by norm_cast; exact le_of_lt hp)
  apply mul_le_mul_of_nonneg_left _ h_nonneg
  if h : n = 0 then
    simp [h]
    rw [Real.log_zero]
    linarith
  else
    apply _root_.add_le_add (nat_log_le_real_log hp h) (le_refl 1)

/-- The calculation showing sumDigits p a + sumDigits p b ≤ C * log n when a, b < 2n. -/
lemma sumDigits_log_bound {p : ℕ} (hp : 1 < p) (n a b : ℕ)
    (ha : a < 2 * n) (hb : b < 2 * n) :
    ∃ C, (sumDigits p a : ℝ) + sumDigits p b ≤ C * Real.log (n + 2) := by
  use (2 * (p - 1) / Real.log p) + 5 * (p - 1)
  have h_p_gt_1 : 1 < (p : ℝ) := by norm_cast; exact hp
  have h_log_p_pos : 0 < Real.log p := Real.log_pos h_p_gt_1
  have h_nonneg_p : 0 ≤ (p : ℝ) - 1 := sub_nonneg.mpr (by norm_cast; exact le_of_lt hp)
  have h_p_minus_1_pos : 0 < (p : ℝ) - 1 := sub_pos.mpr (by norm_cast; exact hp)
  
  -- Case n = 0
  if hn : n = 0 then
    rw [hn] at ha hb
    have : a = 0 := Nat.eq_zero_of_le_zero (le_of_lt ha)
    have : b = 0 := Nat.eq_zero_of_le_zero (le_of_lt hb)
    simp [sumDigits, *]
    -- 0 <= C * log 2
    apply mul_nonneg
    · apply add_nonneg
      · apply div_nonneg
        · apply mul_nonneg; norm_num; exact h_nonneg_p
        · apply Real.log_nonneg; exact le_of_lt h_p_gt_1
      · apply mul_nonneg; norm_num; exact h_nonneg_p
    · apply Real.log_nonneg; norm_num
  else
    have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    have h_bound_a := sumDigits_bound_real hp a
    have h_bound_b := sumDigits_bound_real hp b
    have h_log_a : Real.log a ≤ Real.log (2 * n) := by
      if ha0 : a = 0 then
        rw [ha0, Nat.cast_zero, Real.log_zero]
        apply le_of_lt
        apply Real.log_pos
        norm_cast
        linarith
      else
        apply Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero ha0))
        norm_cast
        exact le_of_lt ha
    have h_log_b : Real.log b ≤ Real.log (2 * n) := by
      if hb0 : b = 0 then
        rw [hb0, Nat.cast_zero, Real.log_zero]
        apply le_of_lt
        apply Real.log_pos
        norm_cast
        linarith
      else
        apply Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hb0))
        norm_cast
        exact le_of_lt hb
    apply le_trans (add_le_add h_bound_a h_bound_b)
    
    have h_calc : (p - 1 : ℝ) * (Real.log a / Real.log p + 1) + (p - 1) * (Real.log b / Real.log p + 1) ≤
         (2 * (p - 1) / Real.log p) * Real.log (2 * n) + 2 * (p - 1) := by
       rw [mul_add, mul_add]
       have h1 : (p - 1 : ℝ) * (Real.log a / Real.log p) = (p - 1) / Real.log p * Real.log a := by field_simp
       have h2 : (p - 1 : ℝ) * (Real.log b / Real.log p) = (p - 1) / Real.log p * Real.log b := by field_simp
       rw [h1, h2]
       rw [add_add_add_comm]
       rw [← mul_add, ← two_mul]
       apply add_le_add_right
       rw [div_mul_eq_mul_div, div_le_div_iff₀ h_log_p_pos h_log_p_pos]
       rw [mul_assoc, mul_assoc, mul_le_mul_left h_p_minus_1_pos]
       apply add_le_add h_log_a h_log_b
    
    apply le_trans h_calc
    
    have h_log_n_le : Real.log n ≤ Real.log (n + 2) := by
      apply Real.log_le_log
      · norm_cast; linarith
      · norm_cast; linarith
    have h_log_3_le : Real.log 3 ≤ Real.log (n + 2) := by
      apply Real.log_le_log (by norm_num)
      norm_cast; linarith
    
    have h_one_le_log : 1 ≤ Real.log (n + 2) := by
      apply le_trans _ h_log_3_le
      rw [← Real.log_exp 1]
      apply Real.log_le_log (Real.exp_pos 1)
      have : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
      linarith

    rw [Real.log_mul (by norm_num) (by norm_cast; linarith)]
    rw [mul_add]
    rw [add_comm (2 * (p - 1) / Real.log p * Real.log 2)]
    rw [add_assoc]
    refine _root_.add_le_add ?_ ?_
    · -- Log n term
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left h_log_n_le
      apply mul_nonneg
      · apply div_nonneg; apply mul_nonneg; norm_num; exact h_nonneg_p; exact le_of_lt h_log_p_pos
      · norm_num
    · -- Constant term
      rw [← mul_assoc, mul_comm (2 * (p-1) : ℝ), mul_assoc, mul_comm (1/Real.log p), ← div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_left _ h_nonneg_p
      trans 4
      · rw [add_comm]
        apply _root_.add_le_add (le_refl 2)
        rw [div_le_iff₀ (h_log_p_pos)]
        nth_rewrite 2 [← mul_one (Real.log p)]
        apply mul_le_mul_of_nonneg_right _ (le_of_lt h_log_p_pos)
        trans Real.log 2
        · linarith
        · apply Real.log_le_log (by norm_num)
          norm_cast; exact le_of_lt hp
      · trans 5
        · norm_num
        · nth_rewrite 1 [← mul_one 5]
          apply mul_le_mul_of_nonneg_left h_one_le_log (by norm_num)

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
