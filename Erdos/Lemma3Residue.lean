import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Periodic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith

open Finset Nat Function
open scoped BigOperators

lemma residue_count_interval {p D : ℕ} (hp : p > 0) {R : Finset ℕ} (hR : ∀ r ∈ R, r < p^D) (a b : ℕ) (h_ba : a ≤ b) :
    ((Ico a b).filter (fun m => m % p^D ∈ R)).card ≤ R.card * ((b - a) / p^D + 1) := by
  let M := b - a
  let q := M / p^D
  let r := M % p^D
  let f : ℕ → ℕ := fun m => m % p^D
  let S := (Ico a b).filter (fun m => f m ∈ R)

  have count_le : ∀ r < p^D, ((Ico a b).filter (fun m => m % p^D = r)).card ≤ q + 1 := by
    intro r hr
    let k := p^D
    have k_pos : k > 0 := pow_pos hp D
    let P := fun m => m % k = r
    have per : Periodic P k := fun x => by simp [P, Nat.add_mod_right]
    
    have card_interval : ∀ n, ((Ico n (n + k)).filter P).card = 1 := by
      intro n
      rw [filter_Ico_card_eq_of_periodic n k P per]
      rw [count_eq_card_filter_range]
      have : ((range k).filter P) = {r} := by
        ext x
        simp only [mem_filter, mem_range, P]
        constructor
        · intro h; rw [mem_singleton]; rw [← h.2]; exact (mod_eq_of_lt h.1).symm
        · intro h; rw [mem_singleton] at h; rw [h]; exact ⟨hr, mod_eq_of_lt hr⟩
      rw [this, card_singleton]

    let q' := (b - a) / k
    
    have h_split : Ico a b = (Ico a (a + q' * k)) ∪ (Ico (a + q' * k) b) := by
      rw [Ico_union_Ico_eq_Ico]
      · exact Nat.le_add_right _ _
      · rw [← Nat.add_sub_of_le h_ba]
        apply Nat.add_le_add_left
        exact Nat.div_mul_le_self _ _

    have count_blocks : ((Ico a (a + q' * k)).filter P).card = q' := by
      induction q' with
      | zero => simp
      | succ n ih =>
        let mid := a + n * k
        let end_ := a + (n + 1) * k
        have h_union : Ico a end_ = Ico a mid ∪ Ico mid end_ := by
          rw [Ico_union_Ico_eq_Ico]
          · exact Nat.le_add_right _ _
          · apply Nat.add_le_add_left
            rw [Nat.add_mul, one_mul]; exact Nat.le_add_right _ _
        rw [h_union, filter_union, card_union_of_disjoint]
        · rw [ih]; congr 1
          have : end_ = mid + k := by dsimp [end_, mid]; rw [Nat.add_mul, one_mul, Nat.add_assoc]
          rw [this, card_interval]
        · apply disjoint_of_subset_left (filter_subset _ _)
          apply disjoint_of_subset_right (filter_subset _ _)
          rw [disjoint_left]; intro x h1 h2
          rw [mem_Ico] at h1 h2
          linarith [h1.2, h2.1]
    
    rw [h_split, filter_union, card_union_of_disjoint]
    · rw [count_blocks]
      apply Nat.add_le_add_left
      -- Bound remainder
      let b' := a + q' * k
      let len := b - b'
      have len_lt : len < k := by
        have : b - a - q' * k = (b - a) % k := by
          rw [Nat.sub_eq_iff_eq_add (Nat.div_mul_le_self _ _)]
          rw [Nat.mul_comm ((b-a)/k) k]
          exact (Nat.mod_add_div _ _).symm
        calc b - b' = b - (a + q' * k) := rfl
             _ = b - a - q' * k := (Nat.sub_sub b a (q' * k)).symm
             _ = (b - a) % k := this
             _ < k := Nat.mod_lt _ k_pos

      let S_rem := (Ico b' b).filter P
      by_contra h_contra
      have h_ge_2 : S_rem.card ≥ 2 := Nat.lt_of_not_le h_contra
      rcases Finset.one_lt_card_iff.mp h_ge_2 with ⟨x, y, hx_mem, hy_mem, hne⟩
      rw [mem_filter, mem_Ico] at hx_mem hy_mem
      dsimp [P] at hx_mem hy_mem
      
      have h_dist_lt : (if x < y then y - x else x - y) < k := by
        split_ifs with h_lt
        · calc y - x < b - x := Nat.sub_lt_sub_right (Nat.le_of_lt h_lt) hy_mem.1.2
             _ ≤ b - b' := Nat.sub_le_sub_left hx_mem.1.1 _
             _ = len := rfl
             _ < k := len_lt
        · calc x - y < b - y := Nat.sub_lt_sub_right (Nat.le_of_not_lt h_lt) hx_mem.1.2
             _ ≤ b - b' := Nat.sub_le_sub_left hy_mem.1.1 _
             _ = len := rfl
             _ < k := len_lt

      have h_div : k ∣ (if x < y then y - x else x - y) := by
        rw [Nat.dvd_iff_mod_eq_zero]
        split_ifs with h_lt
        · rw [Nat.sub_mod_eq_zero_of_mod_eq (hy_mem.2.trans hx_mem.2.symm)]
        · rw [Nat.sub_mod_eq_zero_of_mod_eq (hx_mem.2.trans hy_mem.2.symm)]

      have h_pos : (if x < y then y - x else x - y) > 0 := by
        split_ifs with h_lt
        · exact Nat.sub_pos_of_lt h_lt
        · exact Nat.sub_pos_of_lt (Nat.lt_of_le_of_ne (Nat.le_of_not_lt h_lt) hne.symm)

      have h_le : k ≤ (if x < y then y - x else x - y) := Nat.le_of_dvd h_pos h_div
      exact Nat.lt_le_asymm h_dist_lt h_le

    · apply disjoint_of_subset_left (filter_subset _ _)
      apply disjoint_of_subset_right (filter_subset _ _)
      rw [disjoint_left]; intro x h1 h2
      rw [mem_Ico] at h1 h2
      linarith [h1.2, h2.1]

  calc S.card = Finset.sum R (fun r => ((Ico a b).filter (fun m => m % p^D = r)).card) := by
         rw [card_eq_sum_card_fiberwise (f := f) (s := S) (t := R) (H := fun m hm => let h : m ∈ Ico a b ∧ f m ∈ R := (by simpa [S] using hm); h.2)]
         dsimp [S, f]
         apply sum_congr rfl
         intro r hr
         congr 1
         ext m
         simp only [mem_filter, mem_Ico]
         constructor
         · rintro ⟨⟨hm_ico, hm_R⟩, hm_eq⟩; exact ⟨hm_ico, hm_eq⟩
         · rintro ⟨hm_ico, hm_eq⟩; exact ⟨⟨hm_ico, hm_eq.symm ▸ hr⟩, hm_eq⟩
       _ ≤ Finset.sum R (fun r => (q + 1)) := by
         apply sum_le_sum
         intro r hr
         apply count_le r (hR r hr)
       _ = R.card * (q + 1) := by simp
