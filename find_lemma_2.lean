import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.ModEq

open Nat

example (m p i : ℕ) : m % p ^ (i + 1) = (m / p ^ i % p) * p ^ i + m % p ^ i := by
  exact?
