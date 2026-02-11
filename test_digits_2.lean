import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Log

open Nat

example (p n : ℕ) (hp : 1 < p) (hn : n ≠ 0) : (digits p n).length = log p n + 1 := by
  exact digits_len p n hp hn
