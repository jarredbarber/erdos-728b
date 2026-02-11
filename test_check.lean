import Erdos.Problem729
open Nat Real
example {p : ℕ} (hp : 1 < p) (n : ℕ) : (sumDigits p n : ℝ) ≤ (p - 1) * (Real.log n / Real.log p + 1) := by
  apply sumDigits_bound_real hp n
