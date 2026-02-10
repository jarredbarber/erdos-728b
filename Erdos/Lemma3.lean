import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Independence.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Algebra.Order.Field.Basic

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
    (probDigitSpace D p)[highIndicator i] = probHigh p := sorry

lemma indep_highIndicator :
    iIndepFun (fun i => highIndicator i) (probDigitSpace D p) := sorry

lemma prob_eq_count_div_total (S : Set (DigitSpace D p)) :
    (probDigitSpace D p S).toReal = (Fintype.card S : ℝ) / (p ^ D : ℝ) := sorry

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
