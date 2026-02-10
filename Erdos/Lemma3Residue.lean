import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Interval
import Mathlib.Algebra.BigOperators.Basic

open Finset Nat

lemma residue_count_interval {p D : ℕ} (hp : p > 0) {R : Finset ℕ} (hR : ∀ r ∈ R, r < p^D) (a b : ℕ) (h_ba : a ≤ b) :
    ((Ico a b).filter (fun m => m % p^D ∈ R)).card ≤ R.card * ((b - a) / p^D + 1) := by
  let M := b - a
  let q := M / p^D
  let r := M % p^D
  -- We can cover [a, b) by q+1 intervals of length p^D (the last one might be partial or full, but we can extend it)
  -- Actually, let's use the fact that m % p^D takes each value at most (q + 1) times.
  let f : ℕ → ℕ := fun m => m % p^D
  let S := (Ico a b).filter (fun m => f m ∈ R)
  -- We want to bound S.card.
  -- S.card = ∑ r in R, ((Ico a b).filter (fun m => m % p^D = r)).card
  rw [filter_mem_eq_inter, ← biUnion_filter_eq_of_maps_to (fun _ _ => mem_univ _)]
  -- Wait, the sum formula is easier.
  have h_disjoint : (R.image (fun r => (Ico a b).filter (fun m => m % p^D = r))).PairwiseDisjoint id := by
    intro s1 hs1 s2 hs2 h_neq
    rw [Function.onFun, disjoint_left]
    intro x hx1 hx2
    simp at hx1 hx2
    apply h_neq
    rw [← hx1.2, hx2.2]
  -- It's easier to just show that for any fixed r < p^D, count {m ∈ [a, b) | m % p^D = r} ≤ q + 1.
  have count_le : ∀ r < p^D, ((Ico a b).filter (fun m => m % p^D = r)).card ≤ q + 1 := by
    intro r hr
    -- The elements are a + k, etc.
    -- m ≡ r (mod p^D) means m = k * p^D + r.
    -- We are counting k such that a ≤ k * p^D + r < b.
    -- This is equivalent to (a - r) / p^D ≤ k < (b - r) / p^D (roughly).
    -- More precisely, the number of such k is at most ⌈(b-a)/p^D⌉.
    -- Let's use a known bound or prove it.
    let count := ((Ico a b).filter (fun m => m % p^D = r)).card
    -- We can map these m to m / p^D.
    -- Since m % p^D = r is fixed, m / p^D determines m.
    let g : ℕ → ℕ := fun m => m / p^D
    have inj : Set.InjOn g {m | m % p^D = r} := by
      intro x hx y hy h_eq
      apply Nat.div_mod_unique h_eq
      simp at hx hy; rw [hx, hy]
    -- The image of the filter under g is contained in an interval of length q + 1.
    -- m ∈ [a, b) => m/p^D ∈ [a/p^D, b/p^D] approx.
    -- Actually, simpler: in any interval of length p^D, there is exactly one solution.
    -- [a, b) is covered by union of [a, a+p^D), [a+p^D, a+2p^D), ...
    -- There are q full intervals and one partial.
    -- In a full interval [x, x + p^D), there is exactly 1 solution.
    -- In a partial interval, there is at most 1 solution.
    -- Total ≤ q + 1.
    sorry
  
  calc S.card = ∑ x in S, 1 := by simp
       _ = ∑ r in R, ((Ico a b).filter (fun m => m % p^D = r)).card := by
         -- This step requires mapping sum over R.
         -- S = ⋃_{r ∈ R} {m ∈ [a, b) | m % p^D = r}
         rw [card_eq_sum_card_fiberwise (fun m => m % p^D) R]
         intro m hm
         simp at hm
         exact hm.2
       _ ≤ ∑ r in R, (q + 1) := by
         apply sum_le_sum
         intro r hr
         apply count_le r (hR r hr)
       _ = R.card * (q + 1) := by simp [mul_comm]
