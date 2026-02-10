import Mathlib.Data.Nat.Digits

open Nat

example (m p i : ℕ) : m % (p * p ^ i) = (m / p ^ i % p) * p ^ i + m % p ^ i := by
  exact?
