import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic
-- import Mathlib.Data.Nat.Interval -- removed
-- import Mathlib.Algebra.BigOperators.Basic -- removed
import Mathlib.Algebra.BigOperators.Group.Finset -- Let's try this
import Mathlib.Data.Finset.LocallyFinite -- For Ico

open Finset Nat

variable (a b : ℕ)
#check (Ico a b).card
