import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic

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

theorem erdos_729 (P : ℕ) (hP : 0 < P) :
    ∃ C > (0 : ℝ), ∀ a b n : ℕ,
      (∀ p, p.Prime → P < p →
        padicValNat p a.factorial + padicValNat p b.factorial ≤ padicValNat p n.factorial) →
      (a : ℝ) + b ≤ n + C * Real.log (n + 2) := by
  sorry

lemma delta_le_sumDigits {p : ℕ} (hp : p.Prime) (a b n : ℕ)
    (h : padicValNat p a.factorial + padicValNat p b.factorial ≤ padicValNat p n.factorial) :
    a + b - n ≤ (digits p a).sum + (digits p b).sum - (digits p n).sum := by
  sorry

lemma a_lt_two_n {P a b n : ℕ} (hP : 0 < P) (hnP : n > P)
    (h : ∀ p, p.Prime → P < p → padicValNat p a.factorial + padicValNat p b.factorial ≤ padicValNat p n.factorial) :
    a < 2 * n := by
  sorry
