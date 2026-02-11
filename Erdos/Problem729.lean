import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Nat.Prime.Factorial

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
  sorry
