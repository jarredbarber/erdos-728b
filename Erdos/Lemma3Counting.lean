import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Erdos.Digits
import Erdos.Lemma3Common

open Nat BigOperators Finset Real

namespace Erdos728

section Common

variable {p : ℕ} (hp : p.Prime) (D : ℕ)

def toDigitSpace (m : Fin (p^D)) : DigitSpace D p := fun i => ⟨digit p m i, Nat.mod_lt _ hp.pos⟩

lemma toDigitSpace_bijective : Function.Bijective (toDigitSpace hp D) := by
  constructor
  · intro m1 m2 h
    funext i
    simp [toDigitSpace] at h
    have h_digit : ∀ i < D, digit p m1 i = digit p m2 i := by
      intro i hi
      have := congr_fun h ⟨i, hi⟩
      simp at this
      exact this
    apply Fin.eq_of_val_eq
    apply Nat.eq_of_digits_eq_of_lt_pow (m1.isLt) (m2.isLt) h_digit
  · intro f
    let m_val := ∑ i in range D, (f ⟨i, mem_range.mpr i⟩).val * p^i
    have h_lt : m_val < p^D := by
      apply sum_digit_mul_pow_lt_pow p (fun i _ => (f ⟨i, _⟩).isLt)
    let m : Fin (p^D) := ⟨m_val, h_lt⟩
    use m
    funext i
    simp [toDigitSpace]
    rw [digit, Nat.digit_sum_mul_pow_eq_coeff]
    simp

lemma count_digits_fixed {T : ℕ} (indices : Fin T → Fin D) (values : Fin T → Fin p)
    (h_inj : Function.Injective indices) :
    ((range (p^D)).filter (fun m => ∀ k : Fin T, digit p m (indices k) = values k)).card = p ^ (D - T) := by
  let S := {g : Fin D → Fin p | ∀ k, g (indices k) = values k}
  let U := {i : Fin D | i ∉ Set.range indices}
  have hU : Fintype.card U = D - T := by
    rw [Fintype.card_subtype_compl, Fintype.card_range_of_injective h_inj]
  let iso : S ≃ (U → Fin p) := {
    toFun := fun g => fun u => g.val u
    invFun := fun h => ⟨fun i => if hi : i ∈ Set.range indices then values (Classical.choose hi) else h ⟨i, hi⟩, by
      intro k
      simp
      have : indices k ∈ Set.range indices := Set.mem_range_self k
      rw [dif_pos this]
      congr
      apply h_inj
      exact Classical.choose_spec this
    ⟩
    left_inv := by
      intro g
      ext i
      simp
      split_ifs with hi
      · rcases hi with ⟨k, rfl⟩
        rw [g.prop k]
      · rfl
    right_inv := by
      intro h
      ext u
      simp
      rw [dif_neg u.prop]
  }
  rw [← Fintype.card_congr iso, Fintype.card_fun, Fintype.card_fin, hU]
  let bij := toDigitSpace_bijective hp D
  let equiv := Equiv.ofBijective _ bij
  let set_equiv : {m : Fin (p^D) | ∀ k, digit p m (indices k) = values k} ≃ S :=
    Equiv.subtypeEquiv equiv (by intro m; simp [toDigitSpace]; rfl)
  rw [← Fintype.card_congr set_equiv, ← Fintype.card_coe]
  congr

end Common

section Cascade

variable {p : ℕ} (hp : p.Prime) (k : ℕ) (D : ℕ)

def cascade_length (m : ℕ) : ℕ :=
  let s := log p k
  let limit := D - (s + 1)
  (List.range limit).takeWhile (fun i => digit p m (s + 1 + i) = p - 1) |>.length

def carry_cond (p k m i : ℕ) : Prop := p ^ i ≤ k % p ^ i + m % p ^ i

lemma carry_propagate (m i : ℕ) (hi : i > log p k + 1) (h_carry : carry_cond p k m i) (hk : k ≥ 1) :
    digit p m (i - 1) = p - 1 ∧ carry_cond p k m (i - 1) := by
  have hp_pos : p > 0 := hp.pos
  have hp_ge_2 : p ≥ 2 := hp.two_le
  have hk_lt : k < p ^ (i - 1) := by
    calc k < p ^ (log p k + 1) := lt_pow_succ_log_self hk p
         _ ≤ p ^ (i - 1) := Nat.pow_le_pow_of_le_right hp_pos (le_sub_one_of_lt hi)
  have hk' : k < p ^ i := lt_trans hk_lt (Nat.pow_lt_pow_of_lt_right hp_ge_2 (sub_lt_self (by omega) (by omega)))
  rw [carry_cond, mod_eq_of_lt hk'] at h_carry
  have h_digit : m % p ^ i = digit p m (i - 1) * p ^ (i - 1) + m % p ^ (i - 1) := by
    rw [digit, Nat.mod_div_add_mod]
  rw [h_digit] at h_carry
  have h_ineq : digit p m (i - 1) + (m % p ^ (i - 1) + k) / p ^ (i - 1) ≥ p := by
    rw [← Nat.div_le_div_right (pow_pos hp_pos (i - 1))] at h_carry
    rw [Nat.add_div (pow_pos hp_pos (i - 1))] at h_carry
    simp only [Nat.mul_div_right, pow_pos hp_pos, Nat.mul_div_cancel, gt_iff_lt] at h_carry
    convert h_carry using 1
    rw [pow_succ, mul_comm, Nat.mul_div_right _ (pow_pos hp_pos _)]
  have h_quot : (m % p ^ (i - 1) + k) / p ^ (i - 1) ≤ 1 := by
    apply Nat.div_le_of_le_mul
    rw [one_mul, two_mul]
    apply add_le_add (Nat.le_of_lt (mod_lt _ (pow_pos hp_pos _))) (Nat.le_of_lt hk_lt)
  constructor
  · linarith
  · rw [carry_cond, mod_eq_of_lt hk_lt]; linarith

lemma valuation_le_cascade (m : ℕ) (hk : k ≥ 1) (hm : m < p ^ D) :
    padicValNat p ((m + k).choose k) ≤ (log p k + 1) + cascade_length (p:=p) k D m := by
  let s := log p k
  rw [factorization_choose' hp (lt_succ_of_lt (lt_of_lt_of_le (log_lt_of_lt_pow (by omega) (by
      calc m + k < p^D + p^D := add_lt_add_of_lt_of_le hm (pow_le_pow_right hp.one_lt.le (le_trans (log_le_iff_pow_le_right (by omega) (by omega) |>.mp (le_refl _)) (by omega)))
           _ ≤ p^(D+1) := by rw [pow_succ, two_mul]; gcongr; exact hp.two_le
    )) (le_refl _)))]
  let S := (Ico 1 (D + 1)).filter (fun i => carry_cond p k m i)
  have h_card : S.card = padicValNat p ((m + k).choose k) := by congr
  rw [← h_card]
  let S_small := S.filter (fun i => i ≤ s + 1)
  let S_large := S.filter (fun i => i > s + 1)
  have h_split : S.card = S_small.card + S_large.card := by
    rw [← card_union_of_disjoint, filter_union_filter_neg_eq_filter_of_neg]
    · rfl
    · rw [disjoint_filter]; intros _ _ h1 h2; omega
    · simp
  have h_small : S_small.card ≤ s + 1 := by
    trans (Ico 1 (s + 2)).card
    · apply card_le_card; intro x hx; simp at hx ⊢; exact ⟨hx.1.1, hx.2⟩
    · simp
  have h_large : S_large.card ≤ cascade_length (p:=p) k D m := by
    let L := cascade_length (p:=p) k D m
    have h_sub : S_large ⊆ Ico (s + 2) (s + 2 + L) := by
      intro i hi
      simp [S_large, S, carry_cond] at hi
      let ⟨⟨hi_ge1, hi_leD⟩, h_carry, hi_gt_s⟩ := hi
      rw [mem_Ico]
      constructor
      · omega
      · rw [cascade_length]
        have h_digits : ∀ j, s + 1 ≤ j → j ≤ i - 1 → digit p m j = p - 1 := by
          intro j hj_ge hj_le
          let diff := i - 1 - j
          have h_ind : ∀ d, d ≤ diff → digit p m (i - 1 - d) = p - 1 ∧ carry_cond p k m (i - 1 - d) := by
            intro d hd
            induction d with
            | zero =>
                simp
                apply carry_propagate m i hi_gt_s h_carry hk
            | succ d ih =>
                simp
                have h_prev := ih (le_trans (le_succ d) hd)
                let prev := i - 1 - d
                have h_prev_gt : prev > log p k + 1 := by simp [prev, s] at *; omega
                apply carry_propagate m prev h_prev_gt h_prev.2 hk
          exact (h_ind diff (le_refl _)).1
        have h_len : i - (s + 1) - 1 ≤ (List.range (D - (s + 1))).takeWhile (fun i_1 => digit p m (s + 1 + i_1) = p - 1) |>.length := by
          apply List.takeWhile_length_ge_iff.mpr
          intro x hx
          rw [List.mem_take, List.mem_range, List.length_range] at hx
          have h_idx : s + 1 + x ≤ i - 1 := by omega
          apply h_digits (s + 1 + x) (by omega) h_idx
        omega
    trans (Ico (s + 2) (s + 2 + L)).card
    · exact card_le_of_subset h_sub
    · simp
  linarith

lemma count_large_cascade (T : ℕ) (hT : T ≤ D - (log p k + 1)) :
    ((range (p^D)).filter (fun m => cascade_length (p:=p) k D m ≥ T)).card ≤ p ^ (D - T) := by
  let s := log p k
  let indices (k : Fin T) : Fin D := ⟨s + 1 + k, by
    apply lt_of_lt_of_le _ (sub_le_iff_le_add.mp hT)
    omega⟩
  let values (k : Fin T) : Fin p := ⟨p - 1, pred_lt (ne_of_gt hp.pos)⟩
  have h_inj : Function.Injective indices := by
    intro a b h; simp [indices] at h; exact h
  apply le_trans (Finset.card_le_of_subset (fun m hm => ?_)) (le_of_eq (count_digits_fixed hp D indices values h_inj))
  simp at hm ⊢
  rw [cascade_length] at hm
  intro k
  let P := fun i => digit p m (s + 1 + i) = p - 1
  let l := (List.range (D - (s + 1))).takeWhile P
  have h_sub : l <+: List.range (D - (s + 1)) := List.takeWhile_prefix P (List.range (D - (s + 1)))
  have h_len : l.length ≤ D - (s + 1) := by
    simpa using List.Sublist.length_le (List.IsPrefix.sublist h_sub)
  have h_eq : l = List.range l.length := by
    rw [List.prefix_iff_eq_take.mp h_sub, List.take_range, min_eq_left h_len]
  have h_mem : k.val ∈ l := by
    rw [h_eq, List.mem_range]
    exact lt_of_lt_of_le k.isLt hm
  exact List.mem_takeWhile_imp h_mem

end Cascade

section HighDigits
variable {p : ℕ} (hp : p.Prime) (D : ℕ)

lemma valuation_ge_high_digits (m : ℕ) (h_log : log p (2*m) < D + 1) :
    padicValNat p ((2*m).choose m) ≥ count_high_digits p m D :=
  lower_bound_valuation_by_high_digits p m D hp h_log

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
    ((range (p^D)).filter (fun m => count_high_digits p m D < t)).card ≤ p^D / 2^(D/36) := by
  let bij := toDigitSpace_bijective hp D
  let equiv := Equiv.ofBijective _ bij
  let S' := {d : DigitSpace D p | highDigitCount d < t}
  have h_card : ((range (p^D)).filter (fun m => count_high_digits p m D < t)).card = Fintype.card S' := by
    rw [← Fintype.card_coe]
    let iso : {m : Fin (p^D) | count_high_digits p m D < t} ≃ S' :=
      Equiv.subtypeEquiv equiv (by intro m; dsimp [equiv]; simp [highDigitCount_eq hp D]; rfl)
    exact Fintype.card_congr iso
  rw [h_card]
  sorry

end HighDigits

section SinglePrime
variable {p : ℕ} (hp : p.Prime) (k : ℕ) (D : ℕ)

lemma count_bad_single_prime (hD : D ≥ 12 * (log p k + 1) + 6) (hp_ge_3 : p ≥ 3) (hk : k ≥ 1) :
    ((range (p^D)).filter (fun m => padicValNat p ((m + k).choose k) > padicValNat p ((2 * m).choose m))).card
    ≤ (p^D) / p^(D/6 - log p k) + (p^D) / 2^(D/36) := by
  let s := log p k
  let T0 := D/6 - s - 1
  let Bad1 := {m ∈ range (p^D) | padicValNat p ((m + k).choose k) > D/6}
  let Bad2 := {m ∈ range (p^D) | padicValNat p ((2 * m).choose m) < D/6}
  sorry

end SinglePrime

section ResidueCounting

variable {p : ℕ} (hp : p.Prime) (D : ℕ) (k : ℕ)

lemma count_congruent_le (a b K r : ℕ) (hK : K > 0) :
    ((Ico a b).filter (fun m => m % K = r)).card ≤ (b - a) / K + 1 := by
  sorry

lemma residue_count_interval {R : Finset ℕ} (hR : ∀ r ∈ R, r < p^D) (a b : ℕ) (h_ba : a ≤ b) :
    ((Ico a b).filter (fun m => m % p^D ∈ R)).card ≤ R.card * ((b - a) / p^D + 1) := by
  sorry

lemma bad_residue_sets (hD : D ≥ 16 * (log p (k + 1)) + 16) :
    (∀ m, padicValNat p ((m + k).choose k) > D/6 → 
      m % p^D ∈ (range (p^D)).filter (fun r => cascade_length (p:=p) k D r ≥ D/6 - log p k)) ∧
    (∀ m, padicValNat p ((2 * m).choose m) < D/6 → 
      m % p^D ∈ (range (p^D)).filter (fun r => count_high_digits p r D < D/6)) := by
  sorry

corollary count_bad_interval (m0 : ℕ) (hm0 : m0 ≥ p^D) (hD : D ≥ 16 * (log p (k + 1)) + 16)
    (hp_ge_3 : p ≥ 3) (hk : k ≥ 1) :
    ((Ico m0 (2 * m0)).filter (fun m => padicValNat p ((m + k).choose k) > padicValNat p ((2 * m).choose m))).card
    ≤ (2 * m0) / 2 ^ (D / 36) + (2 * p^D) / 2 ^ (D / 36) := by
  sorry

end ResidueCounting

end Erdos728
