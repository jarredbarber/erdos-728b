import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Basic

namespace Erdos728

section CommonDefinitions

variable {D p : ℕ}

/-- The space of D-digit numbers in base p. -/
abbrev DigitSpace (D p : ℕ) := Fin D → Fin p

def isHigh (p : ℕ) (d : Fin p) : Prop :=
  d.val ≥ (p + 1) / 2

instance : DecidablePred (isHigh p) := fun _ => Nat.decLe _ _

def highDigitCount (m : DigitSpace D p) : ℕ :=
  (Finset.univ.filter (fun i => isHigh p (m i))).card

noncomputable def probHigh (p : ℕ) : ℝ :=
  (p / 2 : ℕ) / (p : ℝ)

end CommonDefinitions

end Erdos728
