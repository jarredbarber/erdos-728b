import Mathlib.Data.Nat.Basic
example (n : ℕ) : n / 2 + (n + 1) / 2 = n := by exact Nat.div_add_div_plus_one_div_two_eq_self n
