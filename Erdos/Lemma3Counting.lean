import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Set.Card
import Erdos.Digits
import Erdos.Lemma3Common
import Erdos.Chernoff
import Erdos.Lemma3Residue

open Nat BigOperators Finset Real

namespace Erdos728

section Common

variable {p : ℕ} (hp : p.Prime) (D : ℕ)

def toDigitSpace (m : Fin (p^D)) : DigitSpace D p := fun i => ⟨digit p m i, Nat.mod_lt _ hp.pos⟩

/-- Two naturals with the same base-p digits at positions 0..D-1 are congruent mod p^D.
    Proved by induction using Nat.mod_pow_succ. -/
private lemma mod_pow_eq_of_digits_eq (a b : ℕ)
    (h : ∀ i, i < D → digit p a i = digit p b i) : a % p ^ D = b % p ^ D := by
  induction D with
  | zero => simp [pow_zero, Nat.mod_one]
  | succ D ih =>
    rw [Nat.mod_pow_succ, Nat.mod_pow_succ]
    have h_prev : ∀ i, i < D → digit p a i = digit p b i :=
      fun i hi => h i (Nat.lt_succ_of_lt hi)
    have h_D : digit p a D = digit p b D := h D (Nat.lt_succ_iff.mpr le_rfl)
    unfold digit at h_D
    rw [ih h_prev, h_D]

lemma toDigitSpace_bijective : Function.Bijective (toDigitSpace hp D) := by
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · -- Injectivity: if digits agree, then the underlying naturals agree
    intro ⟨a, ha⟩ ⟨b, hb⟩ h_eq
    ext
    have h_digits : ∀ i, i < D → digit p a i = digit p b i := by
      intro i hi
      have h_fi := congr_fun h_eq ⟨i, hi⟩
      simp only [toDigitSpace, Fin.mk.injEq] at h_fi
      exact h_fi
    have := mod_pow_eq_of_digits_eq D a b h_digits
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  · -- Cardinality: |Fin(p^D)| = |Fin D → Fin p| = p^D
    simp [Fintype.card_fin]

/-- Equiv between digit-space functions constrained at T injective positions
    and unconstrained functions on the D-T remaining positions. -/
private noncomputable def digitConstraintEquiv {T : ℕ} (indices : Fin T → Fin D)
    (values : Fin T → Fin p) (h_inj : Function.Injective indices) :
    {f : DigitSpace D p // ∀ k, f (indices k) = values k} ≃
    ({i : Fin D // i ∉ Set.range indices} → Fin p) where
  toFun f := fun ⟨i, _⟩ => f.val i
  invFun g :=
    ⟨fun i =>
      if h : i ∈ Set.range indices then values h.choose
      else g ⟨i, h⟩,
    fun k => by
      have hmem : indices k ∈ Set.range indices := ⟨k, rfl⟩
      simp only [dif_pos hmem]
      congr 1
      exact h_inj hmem.choose_spec⟩
  left_inv := by
    intro ⟨f, hf⟩; apply Subtype.ext; funext i; simp only
    split
    · rename_i h; rw [← hf h.choose, h.choose_spec]
    · rfl
  right_inv := by
    intro g; funext ⟨i, hi⟩; simp only [dif_neg hi]

include hp in
lemma count_digits_fixed {T : ℕ} (indices : Fin T → Fin D) (values : Fin T → Fin p)
    (h_inj : Function.Injective indices) :
    ((range (p^D)).filter (fun m => ∀ k : Fin T,
      digit p m (indices k) = values k)).card = p ^ (D - T) := by
  -- Step 1: Transfer from range(p^D) to Finset.univ (Fin(p^D))
  have h1 :
      ((range (p ^ D)).filter (fun m =>
        ∀ k, digit p m (indices k) = (values k : ℕ))).card =
      ((univ : Finset (Fin (p ^ D))).filter (fun m : Fin (p ^ D) =>
        ∀ k, digit p m.val (indices k) = (values k : ℕ))).card := by
    apply card_bij (fun m hm =>
      ⟨m, mem_range.mp (mem_filter.mp hm).1⟩)
    · intro m hm
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hm).2⟩
    · intro a _ b _ h; simp at h; exact h
    · intro ⟨b, hb⟩ hmem
      exact ⟨b, mem_filter.mpr
        ⟨mem_range.mpr hb, (mem_filter.mp hmem).2⟩, rfl⟩
  -- Step 2: Transfer Fin(p^D) → DigitSpace via toDigitSpace
  have hbij := toDigitSpace_bijective hp D
  have h2 :
      ((univ : Finset (Fin (p ^ D))).filter (fun m : Fin (p ^ D) =>
        ∀ k, digit p m.val (indices k) = (values k : ℕ))).card =
      ((univ : Finset (DigitSpace D p)).filter (fun f : DigitSpace D p =>
        ∀ k, f (indices k) = values k)).card := by
    apply card_bij (fun m _ => toDigitSpace hp D m)
    · intro m hm; rw [mem_filter] at hm ⊢
      exact ⟨mem_univ _, fun k =>
        Fin.ext (by simp [toDigitSpace]; exact hm.2 k)⟩
    · intro a _ b _ h; exact hbij.1 h
    · intro f hf; obtain ⟨a, ha⟩ := hbij.2 f
      exact ⟨a, mem_filter.mpr ⟨mem_univ _, fun k => by
        have := congrArg Fin.val ((mem_filter.mp hf).2 k)
        rw [← ha] at this
        simp [toDigitSpace] at this
        exact this⟩, ha⟩
  -- Step 3: Constrained DigitSpace = p^(D-T) via Equiv
  have h3 :
      ((univ : Finset (DigitSpace D p)).filter (fun f : DigitSpace D p =>
        ∀ k, f (indices k) = values k)).card = p ^ (D - T) := by
    rw [← Fintype.card_subtype]
    rw [Fintype.card_congr
      (digitConstraintEquiv D indices values h_inj)]
    simp only [Fintype.card_fun, Fintype.card_fin,
      Fintype.card_subtype_compl,
      Set.card_range_of_injective h_inj]
  linarith

end Common

section Cascade

variable {p : ℕ} (hp : p.Prime) (k : ℕ) (D : ℕ)

def cascade_length (m : ℕ) : ℕ :=
  let s := log p k
  let limit := D - (s + 1)
  (List.range limit).takeWhile (fun i => digit p m (s + 1 + i) = p - 1) |>.length

def carry_cond (p k m i : ℕ) : Prop := p ^ i ≤ k % p ^ i + m % p ^ i

lemma carry_propagate (hp : p.Prime) (m i : ℕ) (hi : i > log p k + 1) (h_carry : carry_cond p k m i) (hk : k ≥ 1) :
    digit p m (i - 1) = p - 1 ∧ carry_cond p k m (i - 1) := by
  -- Rewrite i as (i-1)+1 to use Nat.mod_pow_succ without subtraction issues
  set j := i - 1 with hj_def
  have hj_eq : i = j + 1 := by omega
  have hj_ge : j ≥ Nat.log p k + 1 := by omega
  rw [hj_eq] at h_carry
  unfold carry_cond at *
  -- Key facts about p
  have hp2 : p ≥ 2 := Nat.Prime.two_le hp
  have hp_pos : p > 0 := by omega
  have hpj_pos : p ^ j > 0 := Nat.pos_of_ne_zero (by positivity)
  -- Since j ≥ log_p(k) + 1, we have k < p^j (all digits of k above position s are 0)
  have hk_lt_pj : k < p ^ j :=
    lt_of_lt_of_le (Nat.lt_pow_succ_log_self (by omega) k) (Nat.pow_le_pow_right hp_pos hj_ge)
  -- So k % p^j = k and k % p^(j+1) = k
  have hk_mod_j : k % p ^ j = k := Nat.mod_eq_of_lt hk_lt_pj
  have hk_mod_j1 : k % p ^ (j + 1) = k :=
    Nat.mod_eq_of_lt (lt_of_lt_of_le hk_lt_pj (Nat.pow_le_pow_right hp_pos (by omega)))
  -- Decompose m % p^(j+1) = m % p^j + p^j * digit(p, m, j)
  have h_decomp : m % p ^ (j + 1) = m % p ^ j + p ^ j * (m / p ^ j % p) :=
    Nat.mod_pow_succ
  set d := m / p ^ j % p with hd_def
  rw [hk_mod_j1, h_decomp] at h_carry
  -- h_carry : p^(j+1) ≤ k + (m%p^j + p^j * d)
  have hm_mod_lt : m % p ^ j < p ^ j := Nat.mod_lt _ hpj_pos
  have hd_lt : d < p := Nat.mod_lt _ hp_pos
  -- Part 1: d must be p-1 (otherwise the sum is too small)
  have hd_eq : d = p - 1 := by
    by_contra h_ne
    have hd_le : d ≤ p - 2 := by omega
    have : p ^ j * d ≤ p ^ j * (p - 2) := Nat.mul_le_mul_left _ hd_le
    -- Total ≤ (p^j-1) + (p^j-1) + p^j*(p-2) = p^j*p - 2 < p^(j+1)
    have h_sum : k + (m % p ^ j + p ^ j * d) < p ^ j + (p ^ j + p ^ j * (p - 2)) := by omega
    have h_rw : p ^ j + (p ^ j + p ^ j * (p - 2)) = p ^ j * p := by
      have : p ^ j * (p - 2) + p ^ j + p ^ j = p ^ j * p := by
        rw [← Nat.mul_succ, ← Nat.mul_succ]; congr 1; omega
      omega
    rw [pow_succ] at h_carry; omega
  constructor
  · -- digit p m j = p - 1
    exact hd_eq
  · -- carry_cond at j: p^j ≤ k + m%p^j
    rw [hk_mod_j]
    rw [hd_eq] at h_carry; rw [pow_succ] at h_carry
    -- h_carry: p^j*p ≤ k + (m%p^j + p^j*(p-1))
    -- Since p^j*(p-1) + p^j = p^j*p, we get p^j ≤ k + m%p^j
    have : p ^ j * (p - 1) + p ^ j = p ^ j * p := by
      rw [← Nat.mul_succ]; congr 1; omega
    omega

lemma valuation_le_cascade (hp : p.Prime) (m : ℕ) (hk : k ≥ 1) (hm : m < p ^ D) :
    padicValNat p ((m + k).choose k) ≤ (log p k + 1) + cascade_length (p:=p) k D m := sorry

lemma count_large_cascade (hp : p.Prime) (T : ℕ) (hT : T ≤ D - (log p k + 1)) :
    ((range (p^D)).filter (fun m => cascade_length (p:=p) k D m ≥ T)).card ≤ p ^ (D - T) := sorry

end Cascade

section HighDigits
variable {p : ℕ} (hp : p.Prime) (D : ℕ)

lemma valuation_ge_high_digits (hp : p.Prime) (m : ℕ) (h_log : log p (2*m) < D + 1) :
    padicValNat p ((2*m).choose m) ≥ count_high_digits p m D := by
  have h := lower_bound_valuation_by_high_digits p m D hp h_log
  rw [Nat.factorization_def _ hp] at h
  exact h

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
    ((range (p^D)).filter (fun m => count_high_digits p m D < t)).card ≤
    p^D / 2^(D/36) := by
  -- Handle trivial case t = 0 (empty filter)
  by_cases ht0 : t = 0
  · simp [ht0]
  have ht_pos : t ≥ 1 := Nat.pos_of_ne_zero ht0
  have hD_ge_6 : D ≥ 6 := by omega
  have hD_pos : D > 0 := by omega
  -- Step 1: Relate range(p^D) filter to DigitSpace filter via bijection
  have h_card_eq_fin :
      ((range (p^D)).filter (fun m => count_high_digits p m D < t)).card =
      ((Finset.univ : Finset (Fin (p^D))).filter
        (fun m : Fin (p^D) =>
          count_high_digits p m.val D < t)).card := by
    apply Finset.card_bij
      (fun m hm => ⟨m, by rw [mem_filter] at hm; exact mem_range.mp hm.1⟩)
    · intro m hm; rw [mem_filter] at hm ⊢; exact ⟨mem_univ _, hm.2⟩
    · intro a _ b _ h; simp at h; exact h
    · intro b hb; refine ⟨b.val, ?_, Fin.ext rfl⟩
      rw [mem_filter]
      exact ⟨mem_range.mpr b.isLt, (mem_filter.mp hb).2⟩
  have h_card_eq_ds :
      ((Finset.univ : Finset (Fin (p^D))).filter
        (fun m : Fin (p^D) =>
          count_high_digits p m.val D < t)).card =
      ((Finset.univ : Finset (DigitSpace D p)).filter
        (fun m : DigitSpace D p => highDigitCount m < t)).card := by
    have hbij := toDigitSpace_bijective hp D
    apply Finset.card_bij (fun m _ => toDigitSpace hp D m)
    · intro m hm; rw [mem_filter] at hm ⊢
      exact ⟨mem_univ _,
        by rw [highDigitCount_eq hp D m]; exact hm.2⟩
    · intro a _ b _ h; exact hbij.1 h
    · intro b hb; obtain ⟨a, ha⟩ := hbij.2 b
      refine ⟨a, ?_, ha⟩; rw [mem_filter]
      exact ⟨mem_univ _, by
        rw [← highDigitCount_eq hp D a, ha]
        exact (mem_filter.mp hb).2⟩
  -- Step 2: Filter subset (< t implies ≤ (t : ℝ))
  have h_subset :
      (Finset.univ.filter
        (fun m : DigitSpace D p => highDigitCount m < t)) ⊆
      (Finset.univ.filter
        (fun m : DigitSpace D p =>
          (highDigitCount m : ℝ) ≤ ↑t)) := by
    intro m; simp only [mem_filter, mem_univ, true_and]
    exact fun h => by exact_mod_cast le_of_lt h
  -- Step 3: probHigh p ≥ 1/3 and t < D * probHigh p
  have h_prob_ge : probHigh p ≥ 1/3 := by
    unfold probHigh
    rw [ge_iff_le, div_le_div_iff₀
      (by norm_num : (0:ℝ) < 3) (by positivity : (0:ℝ) < p)]
    have : (↑(p / 2 * 3) : ℝ) ≥ (↑p : ℝ) := by
      exact_mod_cast (show p / 2 * 3 ≥ p by omega)
    push_cast at this; linarith
  have h_t_le_D6 : (↑t : ℝ) ≤ ↑D / 6 := by
    have : (↑(t * 6) : ℝ) ≤ (↑D : ℝ) := by
      exact_mod_cast (show t * 6 ≤ D by omega)
    push_cast at this; linarith
  have h_t_lt : (t : ℝ) < ↑D * probHigh p := by
    have : (↑D : ℝ) / 6 < ↑D / 3 := by
      apply div_lt_div_of_pos_left
        (by exact_mod_cast hD_pos : (0:ℝ) < ↑D)
        (by norm_num) (by norm_num)
    nlinarith [show (D:ℝ) ≥ 0 from by positivity]
  -- Step 4: Apply Chernoff bound from Erdos/Chernoff.lean
  have hne : NeZero p := ⟨Nat.Prime.ne_zero hp⟩
  have h_chernoff :=
    @count_few_high_digits_bound_chernoff D p hne (↑t) h_t_lt
  -- Step 5: Bound exp(-2*(gap)^2/D) ≤ (2^(D/36))⁻¹
  -- Gap ≥ D/6, so exponent ≤ -D/18, and exp(-D/18) ≤ 2^(-D/36)
  -- since ln 2 ≤ 1 ≤ 2 and (D/36 : ℕ) ≤ D/18.
  have h_exp_bound :
      exp (-2 * ((↑D * probHigh p - ↑t)^2) / (↑D : ℝ)) ≤
      ((2 : ℝ)^(D/36))⁻¹ := by
    have h_gap : ↑D * probHigh p - ↑t ≥ ↑D / 6 := by
      nlinarith [show (D:ℝ) ≥ 0 from by positivity]
    have hD_r : (↑D : ℝ) > 0 := by exact_mod_cast hD_pos
    have h_exp_le :
        -2 * ((↑D * probHigh p - ↑t)^2) / (↑D : ℝ) ≤
        -(↑D : ℝ) / 18 := by
      calc -2 * (↑D * probHigh p - ↑t)^2 / ↑D
          ≤ -2 * ((↑D : ℝ) / 6)^2 / ↑D := by
            apply div_le_div_of_nonneg_right _ (le_of_lt hD_r)
            nlinarith [sq_le_sq'
              (by linarith) h_gap]
        _ = -(↑D : ℝ) / 18 := by field_simp; ring
    calc exp (-2 * ((↑D * probHigh p - ↑t)^2) / ↑D)
        ≤ exp (-(↑D : ℝ) / 18) := by
          rw [exp_le_exp]; exact h_exp_le
      _ ≤ ((2 : ℝ)^(D/36))⁻¹ := by
          rw [show ((2 : ℝ)^(D/36))⁻¹ =
              exp (-(↑(D/36) * Real.log 2)) from by
            rw [exp_neg]; congr 1
            rw [← rpow_natCast,
              rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
            ring_nf]
          rw [exp_le_exp]
          nlinarith [
            show Real.log 2 ≤ 1 from by
              rw [← Real.log_exp 1]
              exact Real.log_le_log (by norm_num)
                (by linarith [add_one_le_exp 1]),
            show (↑(D/36) : ℝ) ≤ (D : ℝ) / 18 from by
              have : (↑(D/36) : ℝ) ≤ (D : ℝ) / 36 := by
                rw [le_div_iff₀
                  (by norm_num : (0:ℝ) < 36)]
                exact_mod_cast Nat.div_mul_le_self D 36
              linarith [show (D:ℝ) / 36 ≤ (D:ℝ) / 18
                from by
                  apply div_le_div_of_nonneg_left _
                    (by norm_num) (by norm_num)
                  exact_mod_cast Nat.zero_le D],
            show (↑(D/36) : ℝ) ≥ 0 from by
              exact_mod_cast Nat.zero_le _]
  -- Step 6: Combine bounds to get ℕ inequality
  rw [h_card_eq_fin, h_card_eq_ds]
  have h2_pos : (2 : ℕ)^(D/36) > 0 := by positivity
  rw [Nat.le_div_iff_mul_le h2_pos]
  have h_card_le := card_le_card h_subset
  suffices h : ((((Finset.univ.filter
      (fun m : DigitSpace D p => highDigitCount m < t)).card
      * 2^(D/36) : ℕ) : ℝ) ≤ ↑(p^D)) from by
    exact_mod_cast h
  push_cast
  calc ↑((Finset.univ.filter
        (fun m : DigitSpace D p =>
          highDigitCount m < t)).card) *
        (2:ℝ)^(D/36)
      ≤ ↑((Finset.univ.filter
        (fun m : DigitSpace D p =>
          (highDigitCount m : ℝ) ≤ ↑t)).card) *
        (2:ℝ)^(D/36) := by
        apply mul_le_mul_of_nonneg_right
          (by exact_mod_cast h_card_le) (by positivity)
    _ ≤ (↑p ^ D *
        exp (-2 * ((↑D * probHigh p - ↑t)^2) / ↑D)) *
        (2:ℝ)^(D/36) := by
        apply mul_le_mul_of_nonneg_right h_chernoff
          (by positivity)
    _ ≤ (↑p ^ D * ((2 : ℝ)^(D/36))⁻¹) *
        (2:ℝ)^(D/36) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left h_exp_bound
          (by positivity)
    _ = ↑p ^ D := by
        rw [mul_assoc,
          inv_mul_cancel₀
            (by positivity : (2:ℝ)^(D/36) ≠ 0),
          mul_one]

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

  have h_T_val : 2 * s + 3 ≤ T_val := by omega

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
  by_cases hab : a ≤ b
  swap
  · push_neg at hab; rw [Ico_eq_empty (by omega)]; simp
  rw [← card_range ((b - a) / K + 1)]
  apply card_le_card_of_injOn (fun m => (m - a) / K)
  · intro m hm
    rw [mem_coe, mem_filter, mem_Ico] at hm
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (by omega)))
  · intro x hx y hy hxy
    rw [mem_coe, mem_filter, mem_Ico] at hx hy
    by_contra h_ne
    have hmod : x % K = y % K := hx.2.trans hy.2.symm
    -- If x ≠ y, then K | |x - y| (same residue), so quotients (· - a)/K differ
    have hdvd_ne : ∀ {u v : ℕ}, a ≤ u → u < v → K ∣ (v - u) →
        (u - a) / K ≠ (v - a) / K := by
      intro u v hu hlt hdvd h_eq
      have h1 : v - a = (u - a) + (v - u) := by omega
      have : (u - a) / K < (v - a) / K := by
        rw [h1]
        calc (u - a) / K < (u - a) / K + 1 := Nat.lt_succ_self _
          _ ≤ ((u - a) + K) / K := by rw [Nat.add_div_right _ hK]
          _ ≤ ((u - a) + (v - u)) / K :=
              Nat.div_le_div_right (by exact Nat.add_le_add_left (Nat.le_of_dvd (by omega) hdvd) _)
      omega
    rcases Nat.lt_or_gt_of_ne h_ne with hlt | hlt
    · exact absurd hxy (hdvd_ne hx.1.1 hlt
        (Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hmod.symm)))
    · exact absurd hxy.symm (hdvd_ne hy.1.1 hlt
        (Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hmod)))

lemma residue_count_interval (hp : p.Prime)
    {R : Finset ℕ} (hR : ∀ r ∈ R, r < p^D) (a b : ℕ) (h_ba : a ≤ b) :
    ((Ico a b).filter (fun m => m % p^D ∈ R)).card ≤ R.card * ((b - a) / p^D + 1) :=
  _root_.residue_count_interval hp.pos hR a b h_ba

/-- digit p (m % p^D) i = digit p m i for i < D.
    The i-th digit depends only on (m / p^i) % p, and reducing m mod p^D
    doesn't affect quotients at positions below D. -/
private lemma digit_mod_pow_eq (p m D i : ℕ) (hp : p > 0) (hi : i < D) :
    digit p (m % p ^ D) i = digit p m i := by
  unfold digit
  have hD_split : p ^ D = p ^ i * p ^ (D - i) := by
    rw [← pow_add]; congr 1; omega
  rw [hD_split, Nat.mod_mul_right_div_self]
  apply Nat.mod_mod_of_dvd
  exact dvd_pow_self p (by omega : D - i ≠ 0)

/-- Helper: extensionality for List.takeWhile when the predicate agrees on all elements. -/
private lemma takeWhile_congr' {l : List ℕ} {p q : ℕ → Bool}
    (h : ∀ x, x ∈ l → p x = q x) : l.takeWhile p = l.takeWhile q := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.takeWhile_cons]
    rw [h a List.mem_cons_self]
    split
    · congr 1; exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    · rfl

/-- cascade_length depends only on digits at positions s+1..D-1, hence only on m mod p^D. -/
private lemma cascade_length_mod_eq (k D m : ℕ) (hp : p > 0) :
    cascade_length (p := p) k D (m % p ^ D) = cascade_length (p := p) k D m := by
  unfold cascade_length
  simp only
  congr 1
  apply takeWhile_congr'
  intro i hi
  rw [List.mem_range] at hi
  simp only [decide_eq_decide]
  rw [digit_mod_pow_eq p m D (log p k + 1 + i) hp (by omega)]

/-- count_high_digits depends only on digits at positions 0..D-1, hence only on m mod p^D. -/
private lemma count_high_digits_mod_eq (p m D : ℕ) (hp : p > 0) :
    count_high_digits p (m % p ^ D) D = count_high_digits p m D := by
  unfold count_high_digits high_digits_finset is_high_digit
  congr 1
  ext i
  simp only [mem_filter, mem_range]
  constructor
  · intro ⟨hi, hd⟩; exact ⟨hi, by rw [digit_mod_pow_eq p m D i hp hi] at hd; exact hd⟩
  · intro ⟨hi, hd⟩; exact ⟨hi, by rw [digit_mod_pow_eq p m D i hp hi]; exact hd⟩

/-- If `takeWhile` has length `L < l.length`, then `l[L]` does NOT satisfy the predicate. -/
private lemma not_pred_at_takeWhile_length {α : Type*} {p : α → Bool} :
    ∀ (l : List α) (h : (l.takeWhile p).length < l.length),
    p l[(l.takeWhile p).length] = false := by
  intro l; induction l with
  | nil => intro h; simp at h
  | cons a t ih =>
    intro h; by_cases ha : p a = true
    · have htw_len : (List.takeWhile p (a :: t)).length =
          (List.takeWhile p t).length + 1 := by simp [ha]
      have h' : (List.takeWhile p t).length < t.length := by
        simp [List.length_cons] at h; omega
      have h_idx : (a :: t)[(List.takeWhile p (a :: t)).length] =
          t[(List.takeWhile p t).length] := by
        simp only [htw_len, List.getElem_cons_succ]
      simp only [h_idx]; exact ih h'
    · have htw_len : (List.takeWhile p (a :: t)).length = 0 := by
        simp [Bool.eq_false_iff.mpr ha]
      have h_idx : (a :: t)[(List.takeWhile p (a :: t)).length] = a := by
        simp only [htw_len, List.getElem_cons_zero]
      simp only [h_idx]; exact Bool.eq_false_iff.mpr ha

/-- If `cascade_length = L < D - (s+1)`, the digit at position `s+1+L` is NOT `p-1`.
    This is because `takeWhile` stopped at position `L` in the range. -/
private lemma cascade_digit_neq (k D m : ℕ)
    (hL_lt : cascade_length (p := p) k D m < D - (log p k + 1)) :
    digit p m (log p k + 1 + cascade_length (p := p) k D m) ≠ p - 1 := by
  unfold cascade_length; simp only
  set s := log p k; set limit := D - (s + 1)
  set pred := fun i => decide (digit p m (s + 1 + i) = p - 1)
  set tw := (List.range limit).takeWhile pred
  have h_tw_lt : tw.length < (List.range limit).length := by
    simp [List.length_range]; exact hL_lt
  have h_not := not_pred_at_takeWhile_length (List.range limit) h_tw_lt
  have h_range_eq : (List.range limit)[tw.length] = tw.length := by
    simp [List.getElem_range]
  rw [h_range_eq] at h_not
  simp only [pred, decide_eq_false_iff_not] at h_not; exact h_not

/-- No carry exists at any position beyond the cascade boundary.
    If `digit p m j ≠ p-1` and `j ≥ s+1`, then `carry_cond` is false at all
    positions `> j`, by descending induction using `carry_propagate`. -/
private lemma no_carry_beyond (hp : p.Prime) (k m j : ℕ)
    (hk : k ≥ 1) (hj : j ≥ log p k + 1) (h_digit : digit p m j ≠ p - 1)
    (i : ℕ) (hi : i > j) (h_carry : carry_cond p k m i) : False := by
  obtain ⟨d, rfl⟩ : ∃ d, i = j + 1 + d := ⟨i - (j + 1), by omega⟩
  clear hi; induction d with
  | zero =>
    have : j + 1 > log p k + 1 := by omega
    obtain ⟨h_dig, _⟩ := carry_propagate k hp m (j + 1) this h_carry hk
    simp at h_dig; exact h_digit h_dig
  | succ d ih =>
    have h_pos : j + 1 + (d + 1) > log p k + 1 := by omega
    obtain ⟨_, h_carry_prev⟩ :=
      carry_propagate k hp m (j + 1 + (d + 1)) h_pos h_carry hk
    have h_sub : j + 1 + (d + 1) - 1 = j + 1 + d := by omega
    rw [h_sub] at h_carry_prev; exact ih h_carry_prev

/-- For arbitrary m, v_p(C(m+k,k)) > D/6 implies the cascade within D digits
    is at least D/6 - log p k.
    Proof (contrapositive): if cascade_length L < D/6 - s, then the cascade
    terminates within D (since D/6 - s < D - s - 1 for D ≥ 16). The digit at
    position s+1+L ≠ p-1, so no carry propagates beyond s+1+L. By Kummer's
    theorem (factorization_choose'), v_p = #{carry positions} ⊆ Ico 1 (s+2+L),
    giving v_p ≤ s+1+L ≤ D/6. -/
private lemma valuation_gt_implies_cascade (hp : p.Prime) (k D m : ℕ)
    (hk : k ≥ 1) (hD : D ≥ 16 * (log p (k + 1)) + 16) :
    padicValNat p ((m + k).choose k) > D / 6 →
    cascade_length (p := p) k D m ≥ D / 6 - log p k := by
  intro hv; by_contra h_lt; push_neg at h_lt
  set s := log p k; set L := cascade_length (p := p) k D m
  -- L < D - (s+1): from L < D/6 - s and D ≥ 16
  have hD_ge16 : D ≥ 16 := by omega
  have hL_lt_limit : L < D - (s + 1) := by
    have : D / 6 ≤ D - 1 := by omega
    omega
  -- digit at s+1+L ≠ p-1 (cascade boundary)
  have h_digit := cascade_digit_neq k D m hL_lt_limit
  -- Express v_p using factorization_choose'
  set b := max (D + 1) (log p (m + k) + 1) with hb_def
  have hb : log p (m + k) < b := by show _ < max _ _; omega
  rw [← Nat.factorization_def _ hp,
    Nat.factorization_choose' hp hb] at hv
  -- All carry positions are ≤ s+1+L (no carry beyond the cascade)
  set boundary := s + 1 + L
  have h_subset :
      (Ico 1 b).filter (fun i => p ^ i ≤ k % p ^ i + m % p ^ i) ⊆
        Ico 1 (boundary + 1) := by
    intro i hi; rw [mem_filter, mem_Ico] at hi; rw [mem_Ico]
    refine ⟨hi.1.1, ?_⟩
    by_contra h_not; push_neg at h_not
    exact no_carry_beyond hp k m (s + 1 + L) hk
      (by omega) h_digit i (by omega) hi.2
  have h_card_bound :
      ((Ico 1 b).filter
        (fun i => p ^ i ≤ k % p ^ i + m % p ^ i)).card ≤
        boundary := by
    calc ((Ico 1 b).filter _).card
        ≤ (Ico 1 (boundary + 1)).card := card_le_card h_subset
      _ = boundary := by simp [Nat.card_Ico]
  -- boundary = s + 1 + L ≤ D/6 (from L < D/6 - s)
  have h_boundary_le : boundary ≤ D / 6 := by omega
  omega

/-- For arbitrary m, count_high_digits p m D ≤ v_p(C(2m,m)).
    Each high digit at position i < D forces a carry at position i+1 in m+m
    (by high_digit_forces_carry). These carries are at distinct positions 1..D,
    each contributing 1 to v_p via Kummer's theorem. -/
private lemma count_high_le_valuation (hp : p.Prime) (m D : ℕ) :
    count_high_digits p m D ≤ padicValNat p ((2 * m).choose m) := by
  classical
  by_cases hm : m = 0
  · subst hm
    unfold count_high_digits high_digits_finset is_high_digit digit
    simp only [Nat.zero_div, Nat.zero_mod]
    rw [Finset.filter_false_of_mem]
    · simp
    · intro i _; simp only [not_le]; have := hp.two_le; omega
  have hm_pos : m ≥ 1 := Nat.pos_of_ne_zero hm
  let b := max (D + 1) (log p (2 * m) + 1)
  have hb : log p (2 * m) < b := by
    show log p (2 * m) < max (D + 1) (log p (2 * m) + 1); omega
  have hb_gt_D : D < b := by
    show D < max (D + 1) (log p (2 * m) + 1); omega
  have hle : m ≤ 2 * m := Nat.le_mul_of_pos_left m (by omega)
  have h2m_sub : 2 * m - m = m := by omega
  rw [← Nat.factorization_def _ hp, Nat.factorization_choose hp hle hb, h2m_sub]
  apply card_le_card_of_injOn (fun j => j + 1)
  · intro j hj
    rw [mem_coe] at hj
    rw [high_digits_finset, mem_filter, mem_range] at hj
    rw [mem_coe, mem_filter, mem_Ico]
    refine ⟨⟨Nat.succ_le_succ (Nat.zero_le j),
      Nat.lt_of_lt_of_le (Nat.succ_lt_succ hj.1) (by omega)⟩,
      high_digit_forces_carry p m j hj.2⟩
  · intro x hx y hy hxy
    rw [mem_coe] at hx hy
    exact Nat.succ_injective hxy

lemma bad_residue_sets (hp : p.Prime) (hD : D ≥ 16 * (log p (k + 1)) + 16) :
    (∀ m, padicValNat p ((m + k).choose k) > D/6 → 
      m % p^D ∈ (range (p^D)).filter (fun r => cascade_length (p:=p) k D r ≥ D/6 - log p k)) ∧
    (∀ m, padicValNat p ((2 * m).choose m) < D/6 → 
      m % p^D ∈ (range (p^D)).filter (fun r => count_high_digits p r D < D/6)) := by
  have hp_pos : p > 0 := Nat.Prime.pos hp
  have hpD_pos : p ^ D > 0 := Nat.pos_of_ne_zero (by positivity)
  constructor
  · -- Conjunct 1: high valuation on C(m+k,k) → m % p^D has large cascade
    intro m hv
    rw [mem_filter]
    constructor
    · exact mem_range.mpr (Nat.mod_lt m hpD_pos)
    · rw [cascade_length_mod_eq k D m hp_pos]
      have hk : k ≥ 1 := by
        by_contra hk_lt
        push_neg at hk_lt
        interval_cases k
        simp at hv
      exact valuation_gt_implies_cascade hp k D m hk hD hv
  · -- Conjunct 2: low valuation on C(2m,m) → m % p^D has few high digits
    intro m hv
    rw [mem_filter]
    constructor
    · exact mem_range.mpr (Nat.mod_lt m hpD_pos)
    · rw [count_high_digits_mod_eq p m D hp_pos]
      exact Nat.lt_of_le_of_lt (count_high_le_valuation hp m D) hv

lemma count_bad_interval (m0 : ℕ) (hm0 : m0 ≥ p^D) (hD : D ≥ 16 * (log p (k + 1)) + 16)
    (hp : p.Prime) (hp_ge_3 : p ≥ 3) (hk : k ≥ 1) :
    ((Ico m0 (2 * m0)).filter (fun m => padicValNat p ((m + k).choose k) > padicValNat p ((2 * m).choose m))).card
    ≤ (2 * m0) / 2 ^ (D / 36) + (2 * p^D) / 2 ^ (D / 36) := by
  sorry

end ResidueCounting

section UnionBound

/-! ### Union bound over small primes

For each fixed k ≥ 1, there exists M₀(k) such that for m₀ ≥ M₀(k),
at most m₀/4 values of m ∈ [m₀, 2m₀) are "bad" for any prime p ≤ 2k.
The threshold M₀(k) is quasi-polynomial in k.

When k ≤ C_log · log(2m₀), this threshold is subpolynomial in m₀,
so a single M₀ works for all valid k.
-/

/-- The threshold function M₀(k) for the union bound.
    For each k ≥ 1, the union bound argument works for m₀ ≥ this threshold.
    Defined as (2k)^{72·(⌊log₂(16k)⌋+1) + 72}. -/
noncomputable def union_bound_threshold (k : ℕ) : ℕ :=
  (2 * k) ^ (72 * (Nat.log 2 (16 * k) + 1) + 72)

/-- For fixed k ≥ 1 and m₀ ≥ union_bound_threshold k, the union bound shows
    that a good m ∈ [m₀, 2m₀) exists: for all primes p ≤ 2k,
    v_p(C(m+k,k)) ≤ v_p(C(2m,m)).

    Proof outline (Part E of proofs/lemma3-counting.md):
    1. For each prime p ≤ 2k, define D_p with:
       - D_p ≥ 16·log_p(k+1) + 16 (cascade threshold)
       - p^{D_p} ≤ m₀ (interval tiling)
       - 2^{D_p/36} ≥ 32k (per-prime decay)
    2. Apply count_bad_interval for each prime: |bad_p| ≤ m₀/(8k)
    3. Union bound: total bad ≤ π(2k) · m₀/(8k) ≤ 2k · m₀/(8k) = m₀/4
    4. Since m₀/4 < m₀ = |[m₀, 2m₀)|, a good m exists

    Blocked on: count_bad_interval (sorry'd),
    D_p parameter verification, summation arithmetic. -/
lemma exists_m_for_fixed_k (k : ℕ) (hk : k ≥ 1)
    (m₀ : ℕ) (hm₀ : union_bound_threshold k ≤ m₀) :
    ∃ m : ℕ, m₀ ≤ m ∧ m < 2 * m₀ ∧
      ∀ p : ℕ, p.Prime → p ≤ 2 * k →
        padicValNat p ((m + k).choose k) ≤
          padicValNat p ((2 * m).choose m) := by
  sorry

/-- For any C_log, there exists N such that for m₀ ≥ N and all k with
    1 ≤ k ≤ C_log · log(2m₀), the union bound threshold is at most m₀.

    This holds because union_bound_threshold k = (2k)^{O(log k)}, and
    when k ≤ C_log · log(2m₀), this is 2^{O(log²(log m₀))},
    which grows slower than any power of m₀.

    Blocked on: growth rate comparison between
    (2·C_log·log(2m₀))^{O(log(log m₀))} and m₀. -/
lemma threshold_subpolynomial (C_log : ℝ) :
    ∃ N : ℕ, ∀ m₀ : ℕ, N ≤ m₀ → ∀ k : ℕ, 1 ≤ k →
      (k : ℝ) ≤ C_log * Real.log (2 * m₀) →
      union_bound_threshold k ≤ m₀ := by
  sorry

end UnionBound

end Erdos728
