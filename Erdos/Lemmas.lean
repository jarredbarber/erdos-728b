import Mathlib

open Nat

namespace Erdos728

/-!
# Reduction Lemma (Lemma 1)

This file formalizes the reduction from factorial divisibility to binomial
coefficient divisibility. The key result is:

  `(m+k).choose k ∣ (2m).choose m  ↔  m! * (m+k)! ∣ (2m)! * k!`

Under the substitution a = m, b = m + k, n = 2m (so k = a + b − n), the
original problem's divisibility condition a!b! | n!k! becomes equivalent
to testing whether choose(m+k, k) divides the central binomial coefficient
choose(2m, m).
-/

/-- The key identity relating the two forms of the divisibility condition.

Both sides equal `(2m)! * (m+k)! / m!`. Expanding the binomial coefficients:
- `choose(2m, m) * m! * m! = (2m)!`
- `choose(m+k, k) * k! * m! = (m+k)!`

Substituting and simplifying yields the identity. -/
lemma choose_centralBinom_factorial_identity (m k : ℕ) :
    (2*m).choose m * m.factorial * (m+k).factorial =
    (m+k).choose k * ((2*m).factorial * k.factorial) := by
  have h1 : (2*m).choose m * m.factorial * (2*m - m).factorial = (2*m).factorial :=
    choose_mul_factorial_mul_factorial (Nat.le_mul_of_pos_left m (by omega))
  have h2 : (m+k).choose k * k.factorial * ((m+k) - k).factorial = (m+k).factorial :=
    choose_mul_factorial_mul_factorial (Nat.le_add_left k m)
  have hsimp1 : 2 * m - m = m := by omega
  have hsimp2 : m + k - k = m := by omega
  rw [hsimp1] at h1; rw [hsimp2] at h2
  rw [← h2, ← h1]; ring

/-- **Reduction Lemma (Lemma 1).**

For natural numbers m and k, the divisibility of binomial coefficients
`choose(m+k, k) | choose(2m, m)` is equivalent to the factorial divisibility
`m! * (m+k)! | (2m)! * k!`.

Under the substitution a = m, b = m + k, n = 2m, the latter is exactly
`a! * b! | n! * (a + b − n)!`, which is the divisibility condition in
Erdős Problem 728. -/
lemma reduction_lemma (m k : ℕ) :
    (m+k).choose k ∣ (2*m).choose m ↔
    m.factorial * (m+k).factorial ∣ (2*m).factorial * k.factorial := by
  have hid := choose_centralBinom_factorial_identity m k
  have hpos : (m.factorial * (m+k).factorial) ≠ 0 :=
    Nat.ne_of_gt (Nat.mul_pos (factorial_pos m) (factorial_pos (m+k)))
  have hck_pos : (m+k).choose k ≠ 0 :=
    Nat.ne_of_gt (choose_pos (Nat.le_add_left k m))
  constructor
  · -- Forward: choose(m+k,k) | choose(2m,m)  →  m!(m+k)! | (2m)!k!
    intro ⟨q, hq⟩
    use q
    have step : (m+k).choose k * (q * (m.factorial * (m+k).factorial)) =
                (m+k).choose k * ((2*m).factorial * k.factorial) := by
      have : (m+k).choose k * q * m.factorial * (m+k).factorial =
             (m+k).choose k * ((2*m).factorial * k.factorial) := by
        calc (m+k).choose k * q * m.factorial * (m+k).factorial
            = ((m+k).choose k * q) * m.factorial * (m+k).factorial := by ring
          _ = (2*m).choose m * m.factorial * (m+k).factorial := by rw [← hq]
          _ = (m+k).choose k * ((2*m).factorial * k.factorial) := hid
      nlinarith
    have := mul_left_cancel₀ hck_pos step
    linarith
  · -- Backward: m!(m+k)! | (2m)!k!  →  choose(m+k,k) | choose(2m,m)
    intro ⟨q, hq⟩
    use q
    have step : (2*m).choose m * (m.factorial * (m+k).factorial) =
                (m+k).choose k * q * (m.factorial * (m+k).factorial) := by
      calc (2*m).choose m * (m.factorial * (m+k).factorial)
          = (2*m).choose m * m.factorial * (m+k).factorial := by ring
        _ = (m+k).choose k * ((2*m).factorial * k.factorial) := hid
        _ = (m+k).choose k * (m.factorial * (m+k).factorial * q) := by rw [hq]
        _ = (m+k).choose k * q * (m.factorial * (m+k).factorial) := by ring
    exact mul_right_cancel₀ hpos step

end Erdos728
