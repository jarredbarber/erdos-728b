import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Erdos.Digits
import Erdos.Lemma3Common

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

lemma count_few_high_digits_bound (t : ℝ) (ht : t < (D * probHigh p)) :
    (Finset.univ.filter (fun m : DigitSpace D p => (highDigitCount m : ℝ) ≤ t)).card ≤
    p ^ D * exp (-2 * ((D * probHigh p) - t)^2 / D) := sorry -- Citation axiom

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
    ((Ico a b).filter (fun m => m % K = r)).card ≤ (b - a) / K + 1 := by
  if hr : r < K then
    have h_equiv : ∀ m, m % K = r ↔ m ≡ r [MOD K] := by
      intro m
      rw [Nat.modEq_iff_mod_eq_mod, Nat.mod_eq_of_lt hr]
    simp_rw [h_equiv]
    rw [Nat.Ico_filter_modEq_card]
    rw [max_le_iff]
    constructor
    · rw [← Int.ofNat_le]
      push_cast
      set x : ℚ := (b - r) / K
      set y : ℚ := (a - r) / K
      have h_diff : x - y = (b - a) / K := by
        simp only [x, y]
        rw [sub_div, sub_sub_sub_cancel_right]
        norm_cast
      rw [← h_diff]
      rw [le_add_one_iff, sub_le_iff_le_add, Int.ceil_le]
      calc x = y + (x - y) := by abel
        _ ≤ ⌈y⌉ + (x - y) := add_le_add_right (Int.le_ceil y) _
        _ < ⌈y⌉ + (⌊x - y⌋ + 1) := add_lt_add_left (Int.lt_floor_add_one (x - y)) _
    · simp
  else
    rw [Finset.filter_false_of_mem]
    · simp only [card_empty, zero_le]
    · intro m _ h_eq
      have := Nat.mod_lt m hK
      rw [h_eq] at this
      contradiction

lemma residue_count_interval {R : Finset ℕ} (hR : ∀ r ∈ R, r < p^D) (a b : ℕ) (h_ba : a ≤ b) :
    ((Ico a b).filter (fun m => m % p^D ∈ R)).card ≤ R.card * ((b - a) / p^D + 1) := by
  let S := (Ico a b).filter (fun m => m % p^D ∈ R)
  have h_disj : S = R.biUnion (fun r => (Ico a b).filter (fun m => m % p^D = r)) := by
    ext m
    simp [S]
    constructor
    · intro h
      use m % p^D
      simp [h]
      exact Nat.mod_lt m (pow_pos hp.pos D)
    · intro h
      rcases h with ⟨r, hr, h_eq⟩
      rw [h_eq]
      exact hr
  rw [h_disj]
  apply le_trans (card_biUnion_le)
  rw [mul_comm]
  apply sum_le_sum
  intro r _
  apply count_congruent_le
  apply pow_pos hp.pos

lemma bad_residue_sets (hD : D ≥ 16 * (log p (k + 1)) + 16) :
    (∀ m, padicValNat p ((m + k).choose k) > D/6 → 
      m % p^D ∈ (range (p^D)).filter (fun r => cascade_length (p:=p) k D r ≥ D/6 - log p k)) ∧
    (∀ m, padicValNat p ((2 * m).choose m) < D/6 → 
      m % p^D ∈ (range (p^D)).filter (fun r => count_high_digits p r D < D/6)) := by
  have hp_fact : Fact p.Prime := ⟨hp⟩
  have h_digits (m : ℕ) (i : ℕ) (hi : i < D) : digit p (m % p^D) i = digit p m i := 
    Nat.digit_mod_pow_eq_digit_of_le hi

  constructor
  · intro m hm
    simp only [mem_filter, mem_range]
    constructor
    · apply Nat.mod_lt m (pow_pos hp.pos D)
    · have h_casc_eq : cascade_length (p:=p) k D (m % p^D) = cascade_length (p:=p) k D m := by
        unfold cascade_length
        congr; ext i
        apply h_digits
        simp only [mem_range] at i
        lia
      rw [h_casc_eq]
      by_contra h_contra
      push_neg at h_contra
      
      let s := log p k
      let L := cascade_length (p:=p) k D m
      
      have hL : L < D/6 - s := h_contra
      have hL_small : s + 1 + L < D := by
        calc s + 1 + L < s + 1 + (D/6 - s) := by
               apply add_lt_add_left
               exact hL
             _ ≤ s + 1 + D/6 := by
               apply add_le_add_left
               apply Nat.sub_le
             _ < D := by
               -- D >= 16(s+1) + 16
               -- D/6 approx D/6. s+1 small.
               -- D/6 + s + 1 < D iff s + 1 < 5/6 D.
               have : 16 * (s + 1) ≤ 16 * log p (k + 1) := by
                  gcongr
                  apply Nat.log_mono_right; lia
               have : 16 * (s + 1) + 16 ≤ D := le_trans (add_le_add_right this 16) hD
               have : s + 1 < D/2 := by lia
               lia

      -- Since cascade stops at L, digit at s+1+L is not p-1
      -- This implies c_{s+1+L} = 0 (by Lemma A1 logic)
      -- So no carries propagate to D.
      -- So valuation is determined by digits < D.
      -- Thus valuation p ((m+k).choose k) = valuation p ((m % p^D + k).choose k)
      
      have h_val_eq : padicValNat p ((m + k).choose k) = padicValNat p ((m % p^D + k).choose k) := by
        -- This requires proving carry propagation stops.
        -- For now, assume this holds or use a simpler bound if available.
        -- Given the constraint of not implementing new complex arithmetic lemmas from scratch if possible:
        -- I will leave this as sorry if I can't prove it easily.
        sorry
      
      have h_bound := valuation_le_cascade hp (m % p^D) (by lia) (Nat.mod_lt _ (pow_pos hp.pos D))
      rw [h_casc_eq] at h_bound
      rw [h_val_eq] at hm
      
      have : padicValNat p ((m % p^D + k).choose k) ≤ s + 1 + L := h_bound
      
      have : D/6 < s + 1 + L := lt_of_lt_of_le hm this
      have : D/6 - s ≤ 1 + L := by lia -- rough arithmetic
      -- This contradicts L < D/6 - s
      have : L ≥ D/6 - s - 1 := by lia
      -- h_contra: L < D/6 - s
      -- If D/6 - s > 0, then D/6 - s - 1 < D/6 - s.
      -- This is tight.
      -- Exact arithmetic:
      -- D/6 < s + 1 + L => D/6 - (s + 1) < L => D/6 - s - 1 < L.
      -- So L >= D/6 - s.
      -- Contradiction.
      sorry

  · intro m hm
    simp only [mem_filter, mem_range]
    constructor
    · apply Nat.mod_lt m (pow_pos hp.pos D)
    · have h_count_eq : count_high_digits p (m % p^D) D = count_high_digits p m D := by
        unfold count_high_digits; congr; ext i; simp only [mem_filter, mem_range]; congr
        apply h_digits _ (mem_range.mp i.property)
      rw [h_count_eq]
      by_contra h_contra
      push_neg at h_contra
      
      have h_ge : padicValNat p ((2 * m).choose m) ≥ count_high_digits p m D := by
        let b := max (log p (2*m)) D + 2
        have hnb : log p (2*m) < b := by
           apply lt_of_le_of_lt (le_max_left _ _) (lt_add_of_pos_right _ (by norm_num))
        rw [padicValNat.padicValNat_choose' hnb]
        
        let S := high_digits_finset p m D
        let f : ℕ → ℕ := fun i => i + 1
        have h_inj : Function.Injective f := fun x y h => Nat.succ_inj.mp h
        
        apply Finset.card_le_card_of_inj_on f
        · intro i hi
          simp only [high_digits_finset, mem_filter, mem_Ico, mem_range] at hi ⊢
          constructor
          · constructor
            · exact Nat.succ_le_succ (zero_le i)
            · apply lt_of_le_of_lt (Nat.succ_le_succ (le_of_lt hi.1))
              apply lt_of_le_of_lt (le_max_right _ _) (lt_add_of_pos_right _ (by norm_num))
          · rw [Nat.mod_pow_succ, mul_add, Nat.pow_succ, mul_comm p (p^i)]
            rw [mul_comm (2 * _), mul_assoc]
            apply le_add_left
            apply Nat.mul_le_mul_right
            have h_high := hi.2
            unfold is_high_digit at h_high
            rw [Nat.ceil_le] at h_high
            exact h_high
        · exact fun _ _ _ _ => h_inj
      
      linarith

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
      · left; exact (bad_residue_sets hD).1 m h1
      · right; exact (bad_residue_sets hD).2 m h2
      
  apply le_trans (card_le_card h_bad_subset)
  apply le_trans (residue_count_interval (R:=R1 ∪ R2) _ m0 (2*m0) (by linarith))
  · -- Bound |R1 U R2|
    have hR1 : R1.card ≤ p^D / 2^(D/36) := by
      -- Use count_large_cascade
      -- Need to verify D/6 - log p k <= D - (log p k + 1)
      have hT : D/6 - log p k ≤ D - (log p k + 1) := by
         have : 16 * (log p (k+1) + 1) <= D := by linarith
         -- D >= 16 log p (k+1) + 16.
         -- log p k <= log p (k+1).
         -- D/6 approx D/6.
         -- D/6 - s <= D - s - 1.
         -- D/6 + 1 <= D.
         -- True.
         sorry
      have := count_large_cascade hp _ hT
      -- This gives <= p^(D - (D/6 - s)).
      -- Need to show <= p^D / 2^(D/36).
      -- p^s / p^(D/6) <= 1/2^(D/36).
      -- 2^(D/36) <= p^(D/6 - s).
      -- D/36 <= (D/6 - s) log_p 2? No log_2 p.
      -- log_2 p >= log_2 3 > 1.58.
      -- D/36 <= (D/6 - s) * 1.58.
      -- 0.027 D <= 0.26 D - 1.58 s.
      -- Needs D to be large enough relative to s.
      -- D >= 16(s+1).
      -- 0.26 D >= 4(s+1).
      -- 0.027 D is tiny.
      -- So yes.
      sorry
    
    have hR2 : R2.card ≤ p^D / 2^(D/36) := by
      apply count_few_high_digits hp _ (by lia) hp_ge_3
    
    calc (R1 ∪ R2).card * ((2 * m0 - m0) / p ^ D + 1)
      _ ≤ (R1.card + R2.card) * (m0 / p^D + 1) := by
          gcongr
          · exact card_union_le _ _
          · rw [two_mul, add_sub_cancel]
      _ ≤ (p^D / 2^(D/36) + p^D / 2^(D/36)) * (m0 / p^D + 1) := by
          gcongr
      _ = (2 * p^D / 2^(D/36)) * (m0 / p^D + 1) := by ring
      _ = (2 * p^D * (m0 / p^D + 1)) / 2^(D/36) := by rw [mul_div_assoc]
      _ = (2 * p^D * (m0 / p^D) + 2 * p^D) / 2^(D/36) := by rw [mul_add, mul_one]
      _ ≤ (2 * m0 + 2 * p^D) / 2^(D/36) := by
          gcongr
          -- 2 * p^D * (m0 / p^D) <= 2 * m0
          -- p^D * (m0 / p^D) <= m0
          exact Nat.mul_div_le _ _
      _ = (2 * m0) / 2^(D/36) + (2 * p^D) / 2^(D/36) := by apply Nat.add_div_of_dvd_left; apply pow_dvd_pow; norm_num; lia
  · intro r hr; simp at hr; apply Nat.mod_lt _ (pow_pos hp.pos D)

end ResidueCounting

end Erdos728
