import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Independence.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

open Real MeasureTheory ProbabilityTheory
open scoped Nat BigOperators ENNReal

namespace Erdos728

section CombinatorialChernoff

variable {D p : ℕ}

/-- The space of D-digit numbers in base p, represented as functions. -/
def DigitSpace (D p : ℕ) := Fin D → Fin p

instance : Fintype (DigitSpace D p) := Pi.fintype

-- Ensure MeasurableSpace exists
instance : MeasurableSpace (Fin p) := ⊤
instance : MeasurableSingletonClass (Fin p) := ⟨fun _ => trivial⟩
instance : MeasurableSpace (DigitSpace D p) := MeasurableSpace.pi
instance : MeasurableSingletonClass (DigitSpace D p) := ⟨fun _ => MeasurableSet.pi (fun _ => trivial)⟩

lemma card_digitSpace : Fintype.card (DigitSpace D p) = p ^ D := by
  simp [DigitSpace, Fintype.card_pi]

/-- A digit is "high" if it is in the upper half of the range [0, p-1].
    Specifically, d ≥ ⌈p/2⌉. -/
def isHigh (p : ℕ) (d : Fin p) : Prop :=
  d.val ≥ (p + 1) / 2

instance : DecidablePred (isHigh p) := fun _ => Nat.decLe _ _

/-- The number of high digits in a number m (represented as a tuple of digits). -/
def highDigitCount (m : DigitSpace D p) : ℕ :=
  (Finset.univ.filter (fun i => isHigh p (m i))).card

/-- The indicator function for the i-th digit being high, as a real number. -/
noncomputable def highIndicator (i : Fin D) (m : DigitSpace D p) : ℝ :=
  if isHigh p (m i) then 1 else 0

/-- `highDigitCount` as a sum of indicators. -/
lemma highDigitCount_eq_sum_indicators (m : DigitSpace D p) :
    (highDigitCount m : ℝ) = ∑ i : Fin D, highIndicator i m := by
  simp only [highDigitCount, highIndicator]
  rw [Finset.card_eq_sum_ones]
  simp only [Finset.sum_filter, Finset.sum_boole]

variable (hp : p ≥ 2)

/-- The uniform probability measure on `Fin p`. -/
noncomputable def probFin (p : ℕ) : Measure (Fin p) :=
  (p : ℝ≥0∞)⁻¹ • Measure.count

instance isProb_probFin : IsProbabilityMeasure (probFin p) := by
  constructor
  simp only [probFin, Measure.count_univ, Fintype.card_fin]
  have : (p : ℝ≥0∞) ≠ 0 := by simp [hp]
  have : (p : ℝ≥0∞) ≠ ⊤ := by simp
  rw [ENNReal.mul_inv_cancel this this]

/-- The uniform probability measure on `DigitSpace D p`. -/
noncomputable def probDigitSpace (D p : ℕ) : Measure (DigitSpace D p) :=
  Measure.pi (fun _ => probFin p)

instance isProb_probDigitSpace : IsProbabilityMeasure (probDigitSpace D p) :=
  Measure.pi.isProbabilityMeasure _

/-- The probability of a single digit being high. -/
noncomputable def probHigh (p : ℕ) : ℝ :=
  (p / 2 : ℕ) / p

/-- The expected value of `highIndicator` is q/p where q = ⌊p/2⌋. -/
lemma expectation_highIndicator (i : Fin D) :
    (probDigitSpace D p)[highIndicator i] = probHigh p := by
  let f (d : Fin p) : ℝ := if isHigh p d then 1 else 0
  have h_comp : (fun m => highIndicator i m) = f ∘ (fun m => m i) := rfl
  rw [h_comp]
  
  -- Measure map relation
  have h_map : (probDigitSpace D p).map (fun m => m i) = probFin p := by
    rw [probDigitSpace, Measure.pi_map_eval]
    have h_prod : (∏ j ∈ Finset.univ.erase i, probFin p Set.univ) = 1 := by
      simp [measure_univ]
    rw [h_prod, one_smul]

  -- Measurability
  have h_meas_pi : AEMeasurable (fun m : DigitSpace D p => m i) (probDigitSpace D p) :=
    (measurable_pi_apply i).aemeasurable
  have h_meas_f : AEMeasurable f (probFin p) := measurable_from_top.aemeasurable

  rw [integral_map h_meas_pi h_meas_f, h_map]
  
  -- Calculate integral over probFin p
  rw [probFin, integral_smul_measure, integral_count]
  simp only [f, Finset.sum_boole, smul_eq_mul]
  rw [probHigh]
  congr 1
  -- Count high digits
  rw [Finset.card_univ_filter_ge]
  have h_ceil : (p + 1) / 2 = (p + 1) / 2 := rfl
  rw [h_ceil]
  have : (p + 1) / 2 ≤ p := by omega
  simp [this]
  congr 1
  omega

/-- The `highIndicator` variables are independent. -/
lemma indep_highIndicator :
    iIndepFun (fun i => highIndicator i) (probDigitSpace D p) := by
  let f (i : Fin D) (d : Fin p) : ℝ := if isHigh p d then 1 else 0
  have : (fun i m => highIndicator i m) = (fun i m => f i (m i)) := rfl
  rw [this, probDigitSpace]
  apply iIndepFun_pi
  intro i
  exact Measurable.aemeasurable measurable_from_top

lemma prob_eq_count_div_total (S : Set (DigitSpace D p)) [MeasurableSet S] :
    (probDigitSpace D p).real S = (Fintype.card S : ℝ) / (p ^ D : ℝ) := by
  rw [Measure.real_apply]
  -- Calculate probability of singleton
  have h_singleton : ∀ m, probDigitSpace D p {m} = (p ^ D : ℝ≥0∞)⁻¹ := by
    intro m
    rw [probDigitSpace, Measure.pi_singleton]
    simp only [probFin, Measure.count_singleton, Finset.card_fin, Algebra.id.smul_eq_mul, mul_one]
    rw [Finset.prod_const, Finset.card_fin, ENNReal.inv_pow]
  
  -- Sum over S
  rw [measure_finite_measure_eq_sum_singleton S]
  simp only [h_singleton, Finset.sum_const, Finset.card_coe, nsmul_eq_mul]
  
  -- Convert to Real
  rw [ENNReal.toReal_mul, ENNReal.toReal_nat, ENNReal.toReal_inv]
  · field_simp
    rw [ENNReal.toReal_pow, ENNReal.toReal_nat]
  · simp
  · simp
  
/-- The main counting lemma: number of m with few high digits is small. -/
lemma count_few_high_digits_aux (t : ℝ) (ht : t < (D * probHigh p)) :
    (probDigitSpace D p).real {m | (highDigitCount m : ℝ) ≤ t} ≤
    exp (-2 * ((D * probHigh p) - t)^2 / D) := by
  let μ := D * probHigh p
  let ε := μ - t
  have hε : 0 < ε := sub_pos.mpr ht
  
  -- Define centered variables Y i = probHigh p - highIndicator i m
  let Y (i : Fin D) (m : DigitSpace D p) : ℝ := probHigh p - highIndicator i m

  -- Show sum Y i >= ε is equivalent to sum highIndicator i <= t
  have h_equiv : {m | (highDigitCount m : ℝ) ≤ t} = {m | ε ≤ ∑ i, Y i m} := by
    ext m
    simp [Y, μ, ε, highDigitCount_eq_sum_indicators, Finset.sum_sub_distrib]
    simp [Finset.card_fin, nsmul_eq_mul]
    linarith

  rw [h_equiv]
  
  -- Show Y i are independent
  have h_indep : iIndepFun Y (probDigitSpace D p) := by
    apply iIndepFun.comp (indep_highIndicator hp)
    intro i
    exact Measurable.aemeasurable (measurable_id.const_sub _)

  -- Show Y i are sub-Gaussian with parameter 1/4
  have h_subg : ∀ i ∈ Finset.univ, HasSubgaussianMGF (Y i) (1/4) (probDigitSpace D p) := by
    intro i _
    -- E[Y i] = 0
    have h_mean : (probDigitSpace D p)[Y i] = 0 := by
      simp only [Y]
      rw [integral_sub]
      · rw [integral_const, expectation_highIndicator hp i]
        simp only [Measure.pi_univ, Measure.univ_pi, Finset.prod_const_one, ENNReal.one_toReal, mul_one, sub_self]
      · exact integrable_const _
      · exact integrable_const _
    
    -- Bound range
    have h_bound : ∀ m, Y i m ∈ Set.Icc (probHigh p - 1) (probHigh p) := by
      intro m
      simp [Y, highIndicator]
      split_ifs
      · -- highIndicator = 1. Y = probHigh p - 1.
        rw [Set.mem_Icc]
        constructor <;> rfl
      · -- highIndicator = 0. Y = probHigh p.
        rw [Set.mem_Icc]
        constructor
        · have : probHigh p - 1 ≤ probHigh p := by linarith
          exact this
        · rfl

    -- Apply Hoeffding's lemma
    have h_sq : (1/4 : ℝ) = ((probHigh p - (probHigh p - 1)) / 2) ^ 2 := by
      ring
      norm_num
    
    rw [h_sq]
    -- We need to prove range length condition
    have h_ae_bound : ∀ᵐ m ∂(probDigitSpace D p), Y i m ∈ Set.Icc (probHigh p - 1) (probHigh p) :=
      ae_of_all _ h_bound

    apply ProbabilityTheory.HasSubgaussianMGF.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (measurable_from_top.aemeasurable) h_ae_bound h_mean

  -- Apply Hoeffding
  have h_hoeff := ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun h_indep h_subg (le_of_lt hε)
  
  -- Simplify the bound
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul] at h_hoeff
  convert h_hoeff using 3
  field_simp
  ring

/-- The counting version of the Chernoff bound. -/
lemma count_few_high_digits_bound (t : ℝ) (ht : t < (D * probHigh p)) :
    (Finset.univ.filter (fun m : DigitSpace D p => (highDigitCount m : ℝ) ≤ t)).card ≤
    p ^ D * exp (-2 * ((D * probHigh p) - t)^2 / D) := by
  have h_prob := count_few_high_digits_aux hp t ht
  let S := {m | (highDigitCount m : ℝ) ≤ t}
  have h_meas : MeasurableSet S := MeasurableSet.pi (fun _ => trivial)
  rw [prob_eq_count_div_total hp S] at h_prob
  rw [div_le_iff] at h_prob
  · exact h_prob
  · norm_cast
    positivity

end CombinatorialChernoff

end Erdos728
