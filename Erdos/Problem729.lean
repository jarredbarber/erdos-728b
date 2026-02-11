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

open Nat Real

/-- Sum of digits in base p. -/
def sumDigits (p n : ℕ) : ℕ := (Nat.digits p n).sum

private lemma list_sum_le_length_mul (l : List ℕ) (b : ℕ) (h : ∀ x ∈ l, x ≤ b) : l.sum ≤ l.length * b := by
  induction l with
  | nil => simp
  | cons head tail ih =>
    simp only [List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    rw [Nat.add_comm (tail.length * b) b]
    apply Nat.add_le_add
    · apply h; apply List.mem_cons_self
    · apply ih
      intro x hx
      apply h; apply List.mem_cons_of_mem _ hx

lemma sumDigits_le_log (p n : ℕ) (hp : 1 < p) :
    sumDigits p n ≤ (p - 1) * (Nat.log p n + 1) := by
  if h : n = 0 then
    simp [sumDigits, h]
  else
    rw [sumDigits]
    trans (digits p n).length * (p - 1)
    · apply list_sum_le_length_mul
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

theorem erdos_729 (P : ℕ) (hP : 0 < P) :
    ∃ C > (0 : ℝ), ∀ a b n : ℕ,
      (∀ p, p.Prime → P < p →
        padicValNat p a.factorial + padicValNat p b.factorial ≤ padicValNat p n.factorial) →
      (a : ℝ) + b ≤ n + C * Real.log (n + 2) := by
  obtain ⟨p, h_le_p, hp_prime⟩ := Nat.exists_infinite_primes (P + 1)
  have hPp : P < p := lt_of_lt_of_le (lt_add_one P) h_le_p
  have hp_gt_1 : 1 < p := hp_prime.one_lt
  have hp_pos : 0 < (p : ℝ) := Nat.cast_pos.mpr hp_prime.pos
  have hlogp_pos : 0 < Real.log p := Real.log_pos (Nat.one_lt_cast.mpr hp_gt_1)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

  -- Define C generously to cover all cases
  let K1 := 2 * (p : ℝ) / Real.log p
  let K2 := 2 * (p : ℝ) * (Real.log 2 / Real.log p + 1)
  let C := max (4 * (p : ℝ)) (K1 + K2)

  use C
  constructor
  · apply lt_of_lt_of_le _ (le_max_left _ _)
    apply lt_trans hp_pos
    have : 1 < (4 : ℝ) := by norm_num
    exact lt_mul_of_one_lt_left hp_pos this

  intro a b n h_div
  by_cases hn_le_P : n ≤ P
  · -- Case 1: n ≤ P
    have h_small : ∀ x, padicValNat p x.factorial = 0 → x < p := by
      intro x h_val
      haveI : Fact p.Prime := ⟨hp_prime⟩
      by_contra! h_ge
      have h_dvd : p ∣ x.factorial := (Nat.Prime.dvd_factorial hp_prime).mpr h_ge
      have h_val_pos : 1 ≤ padicValNat p x.factorial := by
        apply Nat.succ_le_of_lt
        apply Nat.pos_of_ne_zero
        intro h0
        rw [padicValNat.eq_zero_iff] at h0
        have : p ≠ 1 := Ne.symm (ne_of_lt hp_gt_1)
        simp [this, Nat.factorial_ne_zero] at h0
        exact h0 h_dvd
      rw [h_val] at h_val_pos
      linarith
    
    have h_val_n : padicValNat p n.factorial = 0 := by
      apply padicValNat.eq_zero_of_not_dvd
      intro h_dvd
      have h_le : p ≤ n := (Nat.Prime.dvd_factorial hp_prime).mp h_dvd
      linarith [hPp, hn_le_P]

    specialize h_div p hp_prime hPp
    rw [h_val_n] at h_div
    have h_val_a : padicValNat p a.factorial = 0 := by linarith
    have h_val_b : padicValNat p b.factorial = 0 := by linarith
    
    have ha_lt : a < p := h_small a h_val_a
    have hb_lt : b < p := h_small b h_val_b
    
    calc (a : ℝ) + b ≤ p + p := by norm_cast; linarith
      _ = 2 * p := by ring
      _ ≤ 4 * p * Real.log 2 := by
          -- 4 * log 2 ≈ 2.77 > 2.
          rw [mul_assoc, mul_comm (p : ℝ)]
          apply mul_le_mul_of_nonneg_right _ hp_pos.le
          linarith [hlog2_pos] 
      _ ≤ C * Real.log 2 := by
          apply mul_le_mul_of_nonneg_right (le_max_left _ _) hlog2_pos.le
      _ ≤ n + C * Real.log (n + 2) := by
          apply le_add_of_nonneg_of_le (Nat.cast_nonneg n)
          apply mul_le_mul_of_nonneg_left _ (le_trans (lt_of_lt_of_le hp_pos (le_max_left _ _)).le (le_refl _))
          apply Real.log_le_log (by norm_num) (by norm_num)

  · -- Case 2: n > P
    push_neg at hn_le_P
    have hn_gt_P : P < n := hn_le_P
    have hn_pos : 0 < n := lt_trans hP hn_gt_P
    
    have ha_lt_2n : a < 2 * n := a_lt_two_n hP hn_gt_P h_div
    have hb_lt_2n : b < 2 * n := by
      apply a_lt_two_n hP hn_gt_P
      intro q hq_prime hq_gt
      rw [add_comm]
      exact h_div q hq_prime hq_gt

    have h_delta_nat : a + b - n ≤ sumDigits p a + sumDigits p b - sumDigits p n :=
      delta_le_sumDigits hp_prime a b n (h_div p hp_prime hPp)
      
    have h_le_sum : (a : ℝ) + b - n ≤ sumDigits p a + sumDigits p b := by
       by_cases h_sum : n ≤ a + b
       · have : a + b - n ≤ sumDigits p a + sumDigits p b :=
           le_trans h_delta_nat tsub_le_self
         rw [← Nat.cast_sub h_sum] at this
         norm_cast at this ⊢
         exact this
       · -- a + b < n
         have : (a : ℝ) + b - n < 0 := by norm_cast; linarith [not_le.mp h_sum]
         have : 0 ≤ (sumDigits p a : ℝ) + sumDigits p b := by apply add_nonneg <;> apply Nat.cast_nonneg
         linarith
        
    have h_sum_a : sumDigits p a ≤ (p - 1) * (Nat.log p a + 1) :=
      sumDigits_le_log p a hp_gt_1
    have h_sum_b : sumDigits p b ≤ (p - 1) * (Nat.log p b + 1) :=
      sumDigits_le_log p b hp_gt_1
    
    have h_log_bound (x : ℕ) (hx : x < 2 * n) : (Nat.log p x : ℝ) ≤ (Real.log 2 + Real.log n) / Real.log p := by
      if hx_zero : x = 0 then
        simp [hx_zero]
        apply div_nonneg
        · apply add_nonneg hlog2_pos.le (Real.log_nonneg (Nat.one_le_cast.mpr hn_pos))
        · exact hlogp_pos.le
      else
        calc (Nat.log p x : ℝ) ≤ Real.log x / Real.log p := by
               rw [div_eq_mul_inv]
               apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hlogp_pos.le)
               rw [← Real.log_rpow (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hx_zero))]
               apply Real.log_le_log (by norm_num)
               norm_cast
               exact Nat.pow_log_le_self p (Nat.pos_of_ne_zero hx_zero).ne'
             _ ≤ Real.log (2 * n) / Real.log p := by
               apply div_le_div_of_nonneg_right _ hlogp_pos.le
               apply Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hx_zero))
               norm_cast; exact le_of_lt hx
             _ = (Real.log 2 + Real.log n) / Real.log p := by
               rw [Nat.cast_mul, Real.log_mul (by norm_num) (Nat.cast_pos.mpr hn_pos)]
               norm_num

    have h_sum_a_r : (sumDigits p a : ℝ) ≤ (↑p - 1) * (Nat.log p a + 1) := by 
      rw [← Nat.cast_le (α := ℝ), Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hp_gt_1.le, Nat.cast_one]
      exact h_sum_a
    have h_sum_b_r : (sumDigits p b : ℝ) ≤ (↑p - 1) * (Nat.log p b + 1) := by 
      rw [← Nat.cast_le (α := ℝ), Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hp_gt_1.le, Nat.cast_one]
      exact h_sum_b

    have h_comb : (a : ℝ) + b - n ≤ 2 * (↑p - 1) * ((Real.log 2 + Real.log n) / Real.log p + 1) := by
      calc (a : ℝ) + b - n ≤ (sumDigits p a : ℝ) + sumDigits p b := h_le_sum
        _ ≤ (↑(p - 1) : ℝ) * (Nat.log p a + 1) + (↑(p - 1) : ℝ) * (Nat.log p b + 1) := by
          apply _root_.add_le_add h_sum_a_r h_sum_b_r
        _ = (↑p - 1) * (Nat.log p a + Nat.log p b + 2) := by 
          rw [Nat.cast_sub hp_gt_1.le, Nat.cast_one]
          ring
        _ ≤ (↑p - 1) * ((Real.log 2 + Real.log n) / Real.log p + (Real.log 2 + Real.log n) / Real.log p + 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by nlinarith [hp_gt_1])
          have h_la : (Nat.log p a : ℝ) ≤ (Real.log 2 + Real.log n) / Real.log p := h_log_bound a ha_lt_2n
          have h_lb : (Nat.log p b : ℝ) ≤ (Real.log 2 + Real.log n) / Real.log p := h_log_bound b hb_lt_2n
          linarith
        _ = 2 * (↑p - 1) * ((Real.log 2 + Real.log n) / Real.log p + 1) := by ring

    have h_final : (a : ℝ) + b - n ≤ C * Real.log (n + 2) := by
      calc (a : ℝ) + b - n ≤ 2 * (↑p - 1) * ((Real.log 2 + Real.log n) / Real.log p + 1) := h_comb
        _ ≤ 2 * p * ((Real.log 2 + Real.log n) / Real.log p + 1) := by
          apply mul_le_mul_of_nonneg_right 
          · exact mul_le_mul_of_nonneg_left (sub_le_self _ zero_le_one) (by norm_num)
          · apply add_nonneg
            · apply div_nonneg
              · apply add_nonneg hlog2_pos.le (Real.log_nonneg (Nat.one_le_cast.mpr hn_pos))
              · exact hlogp_pos.le
            · exact zero_le_one
        _ = K1 * Real.log n + K2 := by 
          dsimp [K1, K2]
          field_simp [hlogp_pos.ne']
          ring
        _ ≤ K1 * Real.log (n + 2) + K2 * Real.log (n + 2) := by
           apply _root_.add_le_add
           · apply mul_le_mul_of_nonneg_left
             · apply Real.log_le_log (Nat.cast_pos.mpr hn_pos)
               norm_cast; linarith
             · apply le_of_lt (div_pos (mul_pos (by norm_num) hp_pos) hlogp_pos)
           · conv_lhs => rw [← mul_one K2]
             apply mul_le_mul_of_nonneg_left
             · rw [← Real.log_exp 1]
               apply Real.log_le_log (Real.exp_pos 1)
               have h_exp : Real.exp 1 < 3 := Real.exp_one_lt_three
               have h_n_ge_3 : 3 ≤ n + 2 := by linarith [hn_pos]
               have h_n_ge_3_r : (3 : ℝ) ≤ n + 2 := by norm_cast; exact h_n_ge_3
               exact le_trans h_exp.le h_n_ge_3_r
             · dsimp [K2]
               refine mul_nonneg ?_ ?_
               · exact mul_nonneg (by norm_num) hp_pos.le
               · refine add_nonneg (div_nonneg hlog2_pos.le hlogp_pos.le) zero_le_one
        _ = (K1 + K2) * Real.log (n + 2) := by ring
        _ ≤ C * Real.log (n + 2) := by
            apply mul_le_mul_of_nonneg_right (le_max_right _ _)
            apply Real.log_nonneg; norm_cast; linarith [hn_pos]

    linarith
