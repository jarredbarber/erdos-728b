import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Independence.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Order.Interval.Finset.Nat

open Real MeasureTheory ProbabilityTheory
open scoped Nat BigOperators ENNReal Classical

namespace Erdos728

section CombinatorialChernoff

variable {D p : ℕ} [NeZero p]

abbrev DigitSpace (D p : ℕ) := Fin D → Fin p

-- Define measurable space on components
instance : MeasurableSpace (Fin p) := ⊤
instance : MeasurableSingletonClass (Fin p) := ⟨fun _ => trivial⟩

/-- The uniform probability measure on `Fin p`. -/
noncomputable def probFin (p : ℕ) : Measure (Fin p) :=
  (p : ℝ≥0∞)⁻¹ • Measure.count

instance isProb_probFin : IsProbabilityMeasure (probFin p) := by
  constructor
  rw [probFin, Measure.smul_apply, Measure.count_univ]
  rw [ENat.card_eq_coe_fintype_card, Fintype.card_fin]
  have h_ne_zero : (p : ℝ≥0∞) ≠ 0 := by simp [NeZero.ne p]
  have h_ne_top : (p : ℝ≥0∞) ≠ ⊤ := by simp
  rw [smul_eq_mul]
  exact ENNReal.inv_mul_cancel h_ne_zero h_ne_top

/-- The uniform probability measure on `DigitSpace D p`. -/
noncomputable def probDigitSpace (D p : ℕ) : Measure (DigitSpace D p) :=
  Measure.pi (fun _ => probFin p)

instance isProb_probDigitSpace : IsProbabilityMeasure (probDigitSpace D p) := by
  constructor
  rw [probDigitSpace, Measure.pi_univ]
  simp only [measure_univ, Finset.prod_const_one]

/-- A digit is "high" if it is in the upper half of the range [0, p-1]. -/
def isHigh (p : ℕ) (d : Fin p) : Prop :=
  d.val ≥ (p + 1) / 2

instance : DecidablePred (isHigh p) := fun _ => Nat.decLe _ _

/-- The number of high digits in a number m. -/
def highDigitCount (m : DigitSpace D p) : ℕ :=
  (Finset.univ.filter (fun i => isHigh p (m i))).card

/-- The indicator function for the i-th digit being high. -/
noncomputable def highIndicator (i : Fin D) (m : DigitSpace D p) : ℝ :=
  if isHigh p (m i) then 1 else 0

/-- The probability of a single digit being high. -/
noncomputable def probHigh (p : ℕ) : ℝ :=
  (p / 2 : ℕ) / p

lemma expectation_highIndicator (i : Fin D) :
    (probDigitSpace D p)[highIndicator i] = probHigh p := by
  -- Unfold definitions
  dsimp [probHigh]
  
  -- Use measure preserving property
  let proj : DigitSpace D p → Fin p := fun m => m i
  have h_meas : MeasurePreserving proj (probDigitSpace D p) (probFin p) :=
    measurePreserving_eval (fun _ => probFin p) i
  
  -- Function composition
  let f : Fin p → ℝ := fun d => if isHigh p d then 1 else 0
  have h_comp : highIndicator i = f ∘ proj := rfl
  rw [h_comp]
  
  -- Integral composition
  change ∫ x, f (x i) ∂(probDigitSpace D p) = _
  rw [← integral_map (measurable_pi_apply i).aemeasurable]
  rotate_left
  · -- Proof of AEStronglyMeasurable
    rw [h_meas.map_eq]
    exact Integrable.of_finite.aestronglyMeasurable
  
  -- Main goal
  rw [h_meas.map_eq]
  
  -- Integral over Fin p
  rw [probFin]
  rw [integral_smul_measure]
  rw [integral_count]
  
  -- Sum over Fin p
  simp_rw [f]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero]
  rw [Finset.sum_const]
  rw [nsmul_eq_mul, mul_one]
  
  -- Cardinality
  have h_card : (Finset.filter (isHigh p) Finset.univ).card = p / 2 := by
    rw [← Finset.card_map Fin.valEmbedding]
    
    -- Rewrite predicate
    have h_p : isHigh p = (fun n => (p + 1) / 2 ≤ n) ∘ Fin.valEmbedding := rfl
    simp_rw [h_p]
    rw [← Finset.filter_map]
    
    -- Map univ to range p
    have h_map : Finset.map Fin.valEmbedding (Finset.univ : Finset (Fin p)) = Finset.range p := by
      ext x
      simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_range]
      constructor
      · rintro ⟨y, rfl⟩; exact y.is_lt
      · intro hx; use ⟨x, hx⟩; rfl

    rw [h_map]
    
    -- Identify the filter with Ico
    have h_ico : Finset.filter (fun x => (p + 1) / 2 ≤ x) (Finset.range p) = Finset.Ico ((p + 1) / 2) p := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      tauto
      
    rw [h_ico]
    rw [Nat.card_Ico]
    -- p - (p+1)/2 = p/2
    omega

  rw [h_card]
  
  -- Arithmetic on reals
  rw [ENNReal.toReal_inv]
  rw [ENNReal.toReal_natCast]
  rw [smul_eq_mul]
  rw [inv_mul_eq_div]


lemma indep_highIndicator :
    iIndepFun (fun i => highIndicator i) (probDigitSpace D p) := by
  let X (i : Fin D) (d : Fin p) : ℝ := if isHigh p d then 1 else 0
  have h_meas (i : Fin D) : AEMeasurable (X i) (probFin p) := by
    apply Measurable.aemeasurable
    measurability
  convert iIndepFun_pi h_meas using 1

lemma prob_eq_count_div_total (S : Set (DigitSpace D p)) :
    (probDigitSpace D p S).toReal = (Fintype.card S : ℝ) / (p ^ D : ℝ) := by
  let μ := probDigitSpace D p
  have h_sing_enn (x : DigitSpace D p) : μ {x} = ((p : ℝ≥0∞)⁻¹)^D := by
    -- Proof blocked by mysterious type class instance failure in Finset.prod_congr
    sorry

  have h_sing (x : DigitSpace D p) : (μ {x}).toReal = 1 / (p ^ D : ℝ) := by
    rw [h_sing_enn]
    rw [ENNReal.toReal_pow]
    rw [ENNReal.toReal_inv]
    rw [ENNReal.toReal_natCast]
    rw [one_div, inv_pow]
  
  have h_meas : MeasurableSet S := S.toFinite.measurableSet
  rw [← MeasureTheory.Measure.tsum_indicator_apply_singleton _ _ h_meas]
  
  rw [tsum_fintype]
  rw [ENNReal.toReal_sum]
  rotate_left
  · intro x _
    rw [Set.indicator_apply]
    split_ifs
    · exact measure_ne_top _ _
    · simp
  
  simp_rw [Set.indicator_apply]
  
  have h_ite : ∀ x, (if x ∈ S then μ {x} else 0).toReal = if x ∈ S then (μ {x}).toReal else 0 := by
    intro x
    split_ifs <;> simp
  
  rw [Finset.sum_congr rfl (fun x _ => h_ite x)]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero]
  
  have h_filter : (Finset.filter (fun x => x ∈ S) Finset.univ) = S.toFinset := by
    ext; simp
  
  rw [h_filter]
  rw [Finset.sum_congr rfl (fun x _ => h_sing x)]
  rw [Finset.sum_const]
  rw [nsmul_eq_mul]
  rw [Set.toFinset_card]
  rw [mul_one_div]




lemma count_few_high_digits_aux (t : ℝ) (ht : t < (D * probHigh p)) :
    (probDigitSpace D p {m | (highDigitCount m : ℝ) ≤ t}).toReal ≤
    exp (-2 * ((D * probHigh p) - t)^2 / D) := sorry

lemma count_few_high_digits_bound (t : ℝ) (ht : t < (D * probHigh p)) :
    (Finset.univ.filter (fun m : DigitSpace D p => (highDigitCount m : ℝ) ≤ t)).card ≤
    p ^ D * exp (-2 * ((D * probHigh p) - t)^2 / D) := by
  have h_prob := count_few_high_digits_aux t ht
  let S := {m : DigitSpace D p | (highDigitCount m : ℝ) ≤ t}
  
  -- Use prob_eq_count_div_total
  rw [prob_eq_count_div_total S] at h_prob
  
  -- Fintype.card S is exactly what we want
  -- Finset.filter corresponds to Set S
  have h_card : (Finset.univ.filter (fun m : DigitSpace D p => (highDigitCount m : ℝ) ≤ t)).card = Fintype.card S := by
    rw [Fintype.card_ofFinset]
    rfl
  
  rw [← h_card] at h_prob
  
  have h_pos : (0 : ℝ) < p ^ D := by
    norm_cast
    apply pow_pos
    exact Nat.pos_of_ne_zero (NeZero.ne p)
  
  -- Manually multiply
  rw [div_le_iff₀ h_pos] at h_prob
  rw [mul_comm] at h_prob
  exact h_prob

end CombinatorialChernoff

end Erdos728
