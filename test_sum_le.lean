import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Digits.Lemmas

open Nat

example (l : List ℕ) (b : ℕ) (h : ∀ x ∈ l, x ≤ b) : l.sum ≤ l.length * b := by
  induction l with
  | nil => simp
  | cons head tail ih =>
    simp
    have h_head : head ≤ b := h head (List.mem_cons_self _ _)
    have h_tail : ∀ x ∈ tail, x ≤ b := fun x hx => h x (List.mem_cons_of_mem _ hx)
    exact add_le_add h_head (ih h_tail)
