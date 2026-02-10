import Mathlib

open Real
open scoped Nat Topology

namespace Erdos728

/--
Erdős Problem #728: For sufficiently small ε > 0 and any 0 < C < C',
there exist a, b, n with a, b > εn such that a!b! | n!(a+b-n)!
and C log n < a+b-n < C' log n.
-/
theorem erdos_728 :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ C > (0 : ℝ), ∀ C' > C,
      ∃ a b n : ℕ,
        0 < n ∧
        ε * n < a ∧
        ε * n < b ∧
        a ! * b ! ∣ n ! * (a + b - n)! ∧
        a + b > n + C * Real.log n ∧
        a + b < n + C' * Real.log n := by
  sorry

end Erdos728
