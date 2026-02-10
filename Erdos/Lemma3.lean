import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Independence.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
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
instance : MeasurableSingletonClass (DigitSpace D p) := ⟨fun _ => MeasurableSet.pi Set.to_countable (fun _ => trivial)⟩

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

variable (hp : p ≥ 2)

/-- The uniform probability measure on `Fin p`. -/
noncomputable def probFin (p : ℕ) : Measure (Fin p) :=
  (p : ℝ≥0∞)⁻¹ • Measure.count

instance isProb_probFin : IsProbabilityMeasure (probFin p) := sorry

/-- The uniform probability measure on `DigitSpace D p`. -/
noncomputable def probDigitSpace (D p : ℕ) : Measure (DigitSpace D p) :=
  Measure.pi (fun _ => probFin p)

instance isProb_probDigitSpace : IsProbabilityMeasure (probDigitSpace D p) := sorry

/-- The probability of a single digit being high. -/
noncomputable def probHigh (p : ℕ) : ℝ :=
  (p / 2 : ℕ) / p

lemma expectation_highIndicator (i : Fin D) :
    (probDigitSpace D p)[highIndicator i] = probHigh p := sorry

lemma indep_highIndicator :
    iIndepFun (fun i => highIndicator i) (probDigitSpace D p) := sorry

lemma prob_eq_count_div_total (S : Set (DigitSpace D p)) [MeasurableSet S] :
    (probDigitSpace D p).real S = (Fintype.card S : ℝ) / (p ^ D : ℝ) := sorry

lemma count_few_high_digits_aux (t : ℝ) (ht : t < (D * probHigh p)) :
    (probDigitSpace D p).real {m | (highDigitCount m : ℝ) ≤ t} ≤
    exp (-2 * ((D * probHigh p) - t)^2 / D) := sorry

lemma count_few_high_digits_bound (t : ℝ) (ht : t < (D * probHigh p)) :
    (Finset.univ.filter (fun m : DigitSpace D p => (highDigitCount m : ℝ) ≤ t)).card ≤
    p ^ D * exp (-2 * ((D * probHigh p) - t)^2 / D) := sorry

end CombinatorialChernoff

end Erdos728
