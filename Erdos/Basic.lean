import Mathlib
import Erdos.Lemmas

open Real Nat
open scoped Nat Topology

namespace Erdos728

/-!
## Supporting lemmas for the main theorem

The proof of Erdős 728 uses the substitution a = m, b = m+k, n = 2m.
Under this substitution:
- The divisibility a!b! | n!(a+b-n)! becomes C(m+k,k) | C(2m,m) (Lemma 1 / reduction_lemma)
- For primes p > 2k, v_p(C(m+k,k)) ≤ v_p(C(2m,m)) automatically (Lemma 2 / carry_dominance)
- For primes p ≤ 2k, a counting/union bound argument shows that for m₀ large,
  at least one m ∈ [m₀, 2m₀] gives v_p(C(m+k,k)) ≤ v_p(C(2m,m)) for all such p (Lemma 3)

The main theorem then follows by choosing k ≈ (C+C')/2 · log(2m₀) and verifying
the size and gap constraints.
-/

/-- **Core existence lemma**: For any k ≥ 1 and all sufficiently large m₀,
there exists m ∈ [m₀, 2m₀] such that C(m+k, k) | C(2m, m).

This combines carry dominance for large primes with a counting argument
for small primes. The key steps:
1. For p > 2k: carry_dominance gives v_p(C(m+k,k)) ≤ v_p(C(2m,m)) for ALL m.
2. For p ≤ 2k: Among m ∈ [m₀, 2m₀], the fraction of "bad" m for prime p
   (where v_p(C(m+k,k)) > v_p(C(2m,m))) is ≤ 2/2^{D_p/36} where D_p = log_p(m₀)/2.
3. Union bound: total bad fraction ≤ Σ_{p≤2k} 2/2^{D_p/36} + O(√m₀/m₀) < 1
   for m₀ sufficiently large relative to k. -/
lemma exists_m_choose_dvd (k : ℕ) (hk : 1 ≤ k) :
    ∃ M₀ : ℕ, ∀ m₀ : ℕ, M₀ ≤ m₀ →
      ∃ m : ℕ, m₀ ≤ m ∧ m ≤ 2 * m₀ ∧ (m + k).choose k ∣ (2 * m).choose m := by
  sorry

/-- **Log gap selection**: For 0 < C < C', the choice k = ⌊(C+C')/2 · log(2m₀)⌋₊
gives k ≥ 1 and C·log(2m) < k < C'·log(2m) for all m ∈ [m₀, 2m₀],
provided m₀ is large enough.

The proof uses:
- log(2m)/log(2m₀) → 1 as m₀ → ∞ (for m ∈ [m₀, 2m₀])
- (C+C')/2 is strictly between C and C'
- Floor doesn't lose more than 1, which is absorbed by the margin -/
lemma log_gap_bounds (C C' : ℝ) (hC : 0 < C) (hCC' : C < C') :
    ∃ M₀ : ℕ, ∀ m₀ : ℕ, M₀ ≤ m₀ →
      let k := ⌊(C + C') / 2 * Real.log (2 * ↑m₀)⌋₊
      1 ≤ k ∧
      ∀ m : ℕ, m₀ ≤ m → m ≤ 2 * m₀ →
        C * Real.log (2 * ↑m) < ↑k ∧
        (↑k : ℝ) < C' * Real.log (2 * ↑m) := by
  sorry

/-- **Combined existence**: For 0 < C < C' and m₀ sufficiently large,
there exist m ∈ [m₀, 2m₀] and k ≥ 1 with C(m+k,k) | C(2m,m) and
C·log(2m) < k < C'·log(2m).

This combines `exists_m_choose_dvd` and `log_gap_bounds`. The key observation
is that k = O(log m₀) grows much slower than m₀, so the threshold M₀(k) from
`exists_m_choose_dvd` is eventually dominated by m₀. -/
lemma exists_good_m (C C' : ℝ) (hC : 0 < C) (hCC' : C < C') :
    ∃ M₀ : ℕ, ∀ m₀ : ℕ, M₀ ≤ m₀ →
      ∃ m k : ℕ,
        m₀ ≤ m ∧ m ≤ 2 * m₀ ∧
        1 ≤ k ∧
        (m + k).choose k ∣ (2 * m).choose m ∧
        C * Real.log (2 * ↑m) < ↑k ∧
        (↑k : ℝ) < C' * Real.log (2 * ↑m) := by
  sorry

/--
**Erdős Problem #728**: For sufficiently small ε > 0 and any 0 < C < C',
there exist a, b, n with a, b > εn such that a!b! | n!(a+b-n)!
and C log n < a+b-n < C' log n.

**Proof**: Use the substitution a = m, b = m+k, n = 2m where k = a+b-n.
By the reduction lemma, the divisibility condition becomes C(m+k,k) | C(2m,m).
The combined existence lemma provides m and k satisfying all constraints.
Taking ε < 1/4 ensures ε·n = 2εm < m = a and ε·n < m+k = b.
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
  -- It suffices to prove for ε ∈ (0, 1/4)
  rw [eventually_nhdsWithin_iff, Filter.eventually_iff_exists_mem]
  refine ⟨Set.Ioo (-1) (1/4), Ioo_mem_nhds (by norm_num) (by norm_num), ?_⟩
  intro ε hε _ C hC C' hCC'
  -- Step 1: Get m, k from the combined existence lemma
  obtain ⟨M₀, hM₀⟩ := exists_good_m C C' hC hCC'
  set m₀ := max M₀ 1 with m₀_def
  obtain ⟨m, k, hm_lb, hm_ub, hk, hdvd, hk_lb, hk_ub⟩ := hM₀ m₀ (le_max_left _ _)
  -- Step 2: Set a = m, b = m + k, n = 2 * m
  refine ⟨m, m + k, 2 * m, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- n > 0: since m ≥ m₀ ≥ 1
    omega
  · -- ε * n < a: since ε < 1/4, ε * (2m) < m/2 < m
    have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast show 0 < m by omega
    push_cast; nlinarith [hε.2]
  · -- ε * n < b: since ε * (2m) < m ≤ m + k
    have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast show 0 < m by omega
    push_cast; nlinarith [hε.2, show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k]
  · -- a! * b! ∣ n! * (a + b - n)!
    -- By reduction_lemma: C(m+k,k) | C(2m,m) ↔ m!(m+k)! | (2m)!k!
    rw [show m + (m + k) - 2 * m = k from by omega]
    exact (reduction_lemma m k).mp hdvd
  · -- a + b > n + C * log n: follows from k > C * log(2m)
    push_cast; linarith
  · -- a + b < n + C' * log n: follows from k < C' * log(2m)
    push_cast; linarith

end Erdos728
