import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Log

open Nat

example (p n : ℕ) (hp : 1 < p) (hn : n ≠ 0) : (digits p n).length = log p n + 1 := by
  rw [digits_len p n hp hn]
  -- digits_len says: (digits p n).length = log p n + 1
  -- Let's check if digits_len is the exact name.
