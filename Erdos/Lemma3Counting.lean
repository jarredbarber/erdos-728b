import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Erdos.Digits
import Erdos.Lemma3Common
import Erdos.Chernoff

open Nat BigOperators Finset Real

namespace Erdos728

section Common

variable {p : ℕ} (hp : p.Prime) (D : ℕ)

def toDigitSpace (m : Fin (p^D)) : DigitSpace D p := fun i => ⟨digit p m i, Nat.mod_lt _ hp.pos⟩

lemma toDigitSpace_bijective : Function.Bijective (toDigitSpace hp D) := sorry

lemma count_digits_fixed {T : ℕ} (indices : Fin T → Fin D) (values : Fin T → Fin p)
    (h_inj : Function.Injective indices) :
    ((range (p^D)).filter (fun m => ∀ k : Fin T, digit p m (indices k) = values k)).card = p ^ (D - T) := sorry

end Common

section Cascade

variable {p : ℕ} (hp : p.Prime) (k : ℕ) (D : ℕ)

def cascade_length (m : ℕ) : ℕ :=
  let s := log p k
  let limit := D - (s + 1)
  (List.range limit).takeWhile (fun i => digit p m (s + 1 + i) = p - 1) |>.length

def carry_cond (p k m i : ℕ) : Prop := p ^ i ≤ k % p ^ i + m % p ^ i

lemma carry_propagate (m i : ℕ) (hi : i > log p k + 1) (h_carry : carry_cond p k m i) (hk : k ≥ 1) :
    digit p m (i - 1) = p - 1 ∧ carry_cond p k m (i - 1) := sorry

lemma valuation_le_cascade (hp : p.Prime) (m : ℕ) (hk : k ≥ 1) (hm : m < p ^ D) :
    padicValNat p ((m + k).choose k) ≤ (log p k + 1) + cascade_length (p:=p) k D m := sorry

lemma count_large_cascade (hp : p.Prime) (T : ℕ) (hT : T ≤ D - (log p k + 1)) :
    ((range (p^D)).filter (fun m => cascade_length (p:=p) k D m ≥ T)).card ≤ p ^ (D - T) := sorry

end Cascade

section HighDigits
variable {p : ℕ} (hp : p.Prime) (D : ℕ)

lemma valuation_ge_high_digits (hp : p.Prime) (m : ℕ) (h_log : log p (2*m) < D + 1) :
    padicValNat p ((2*m).choose m) ≥ count_high_digits p m D := sorry

lemma highDigitCount_eq (m : Fin (p^D)) :
    highDigitCount (toDigitSpace hp D m) = count_high_digits p m D := by
  simp only [highDigitCount, count_high_digits, high_digits_finset, isHigh, is_high_digit, toDigitSpace]
  apply Finset.card_bij (fun (i : Fin D) _ => i.val)
  · intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    constructor
    · exact mem_range.mpr i.isLt
    · exact hi
  · intro i j _ _ h
    exact Fin.eq_of_val_eq h
  · intro b hb
    simp only [mem_filter, mem_range] at hb
    refine ⟨⟨b, hb.1⟩, ?_, rfl⟩
    simp only [mem_filter, mem_univ, true_and]
    exact hb.2

lemma count_few_high_digits_bound (hp : p.Prime) (t : ℝ) (ht : t < (D * probHigh p)) :
    (Finset.univ.filter (fun m : DigitSpace D p => (highDigitCount m : ℝ) ≤ t)).card ≤
    p ^ D * exp (-2 * ((D * probHigh p) - t)^2 / D) := by
  have : NeZero p := ⟨Nat.Prime.ne_zero hp⟩
  apply count_few_high_digits_bound_chernoff t ht

lemma count_few_high_digits (hp : p.Prime) (t : ℕ) (ht : t ≤ D/6) (hp_ge_3 : p ≥ 3) :
    ((range (p^D)).filter (fun m => count_high_digits p m D < t)).card ≤ p^D / 2^(D/36) := sorry

end HighDigits

section SinglePrime
variable {p : ℕ} (hp : p.Prime) (k : ℕ) (D : ℕ)

lemma count_bad_single_prime (hD : D ≥ 12 * (log p k + 1) + 6) (hp : p.Prime) (hp_ge_3 : p ≥ 3) (hk : k ≥ 1) :
    ((range (p^D)).filter (fun m => padicValNat p ((m + k).choose k) > padicValNat p ((2 * m).choose m))).card
    ≤ (p^D) / p^(D/6 - log p k) + (p^D) / 2^(D/36) := by
  let s := log p k
  let T_val := D/6
  let T_casc := T_val - s
  let Bad1 := (range (p^D)).filter (fun m => padicValNat p ((m + k).choose k) > T_val)
  let Bad2 := (range (p^D)).filter (fun m => padicValNat p ((2 * m).choose m) < T_val)

  have h_T_val : 2 * s + 3 ≤ T_val := sorry

  have h_subset : (range (p^D)).filter (fun m => padicValNat p ((m + k).choose k) > padicValNat p ((2 * m).choose m)) ⊆ Bad1 ∪ Bad2 := by
    intro m hm
    simp at hm ⊢
    by_contra h_not
    push_neg at h_not
    have h1 : padicValNat p ((m + k).choose k) ≤ T_val := by
      have : m ∈ Bad1 ↔ padicValNat p ((m + k).choose k) > T_val := by
        simp [Bad1, hm.1]
      rw [this] at h_not
      linarith [h_not.1]
    have h2 : T_val ≤ padicValNat p ((2 * m).choose m) := by
      have : m ∈ Bad2 ↔ padicValNat p ((2 * m).choose m) < T_val := by
        simp [Bad2, hm.1]
      rw [this] at h_not
      linarith [h_not.2]
    linarith [hm.2]

  apply le_trans (card_le_card h_subset)
  apply le_trans (card_union_le Bad1 Bad2)
  apply Nat.add_le_add

  -- Bound Bad1
  · sorry

  -- Bound Bad2
  · sorry

end SinglePrime

section ResidueCounting

variable {p : ℕ} (hp : p.Prime) (D : ℕ) (k : ℕ)

lemma count_congruent_le (a b K r : ℕ) (hK : K > 0) :
    ((Ico a b).filter (fun m => m % K = r)).card ≤ (b - a) / K + 1 := sorry

lemma residue_count_interval {R : Finset ℕ} (hR : ∀ r ∈ R, r < p^D) (a b : ℕ) (h_ba : a ≤ b) :
    ((Ico a b).filter (fun m => m % p^D ∈ R)).card ≤ R.card * ((b - a) / p^D + 1) := sorry

lemma bad_residue_sets (hp : p.Prime) (hD : D ≥ 16 * (log p (k + 1)) + 16) :
    (∀ m, padicValNat p ((m + k).choose k) > D/6 → 
      m % p^D ∈ (range (p^D)).filter (fun r => cascade_length (p:=p) k D r ≥ D/6 - log p k)) ∧
    (∀ m, padicValNat p ((2 * m).choose m) < D/6 → 
      m % p^D ∈ (range (p^D)).filter (fun r => count_high_digits p r D < D/6)) := sorry

lemma count_bad_interval (m0 : ℕ) (hm0 : m0 ≥ p^D) (hD : D ≥ 16 * (log p (k + 1)) + 16)
    (hp : p.Prime) (hp_ge_3 : p ≥ 3) (hk : k ≥ 1) :
    ((Ico m0 (2 * m0)).filter (fun m => padicValNat p ((m + k).choose k) > padicValNat p ((2 * m).choose m))).card
    ≤ (2 * m0) / 2 ^ (D / 36) + (2 * p^D) / 2 ^ (D / 36) := by
  let Bad := (Ico m0 (2 * m0)).filter (fun m => padicValNat p ((m + k).choose k) > padicValNat p ((2 * m).choose m))
  
  -- Define bad residues
  let R1 := (range (p^D)).filter (fun r => cascade_length (p:=p) k D r ≥ D/6 - log p k)
  let R2 := (range (p^D)).filter (fun r => count_high_digits p r D < D/6)
  
  have h_bad_subset : Bad ⊆ (Ico m0 (2 * m0)).filter (fun m => m % p^D ∈ R1 ∪ R2) := by
    intro m hm
    simp only [Bad, mem_filter, mem_Ico] at hm
    simp only [mem_filter, mem_Ico, mem_union]
    constructor
    · exact hm.1
    · have h_or : padicValNat p ((m + k).choose k) > D/6 ∨ padicValNat p ((2 * m).choose m) < D/6 := by
         by_contra h_not; push_neg at h_not; linarith [hm.2]
      rcases h_or with h1 | h2
      · left; exact (bad_residue_sets D k hp hD).1 m h1
      · right; exact (bad_residue_sets D k hp hD).2 m h2
      
  apply le_trans (card_le_card h_bad_subset)
  apply le_trans (residue_count_interval (R:=R1 ∪ R2) (hR:=by intro r hr; rw [mem_union] at hr; rcases hr with h|h <;> exact mem_range.mp (mem_filter.mp h).1) (a:=m0) (b:=2*m0) (h_ba:=Nat.le_mul_of_pos_left m0 (by norm_num)))
  · -- Bound |R1 U R2|
    have hR1 : R1.card ≤ p^D / 2^(D/36) := by
      -- Use count_large_cascade
      -- Need to verify D/6 - log p k <= D - (log p k + 1)
      have hR1 : R1.card ≤ p^D / 2^(D/36) := sorry
    
    have hR2 : R2.card ≤ p^D / 2^(D/36) := sorry
    
    sorry
  · intro r hr; simp at hr; apply Nat.mod_lt _ (pow_pos hp.pos D)

end ResidueCounting

end Erdos728
