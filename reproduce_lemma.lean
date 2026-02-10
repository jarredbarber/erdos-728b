import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Interval
import Mathlib.Algebra.BigOperators.Basic

open Finset Nat

variable (a b n r : ℕ)
variable (h : a ≤ b)
variable (n_pos : n > 0)
variable (r_lt : r < n)

example : ((Ico a b).filter (fun m => m % n = r)).card ≤ (b - a) / n + 1 := by
  sorry
