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

/-- **Core existence lemma (uniform version)**: For all sufficiently large m₀,
for every k with 1 ≤ k ≤ m₀, there exists m ∈ [m₀, 2m₀] such that
C(m+k, k) | C(2m, m).

This combines carry dominance for large primes with a counting argument
for small primes:
1. For p > 2k: carry_dominance gives v_p(C(m+k,k)) ≤ v_p(C(2m,m)) for ALL m.
2. For p ≤ 2k: Among m ∈ [m₀, 2m₀], the fraction of "bad" m for prime p
   (where v_p(C(m+k,k)) > v_p(C(2m,m))) decays exponentially in log_p(m₀).
3. Union bound: total bad fraction < 1 for m₀ sufficiently large.

The threshold M₀ is independent of k (as long as k ≤ m₀), because the
per-prime failure probability decreases as m₀ grows regardless of k. -/
lemma exists_m_choose_dvd_uniform :
    ∃ M₀ : ℕ, ∀ m₀ : ℕ, M₀ ≤ m₀ → ∀ k : ℕ, 1 ≤ k → k ≤ m₀ →
      ∃ m : ℕ, m₀ ≤ m ∧ m ≤ 2 * m₀ ∧ (m + k).choose k ∣ (2 * m).choose m := by
  sorry

/-- **Log gap selection**: For 0 < C < C', the choice k = ⌊(C+C')/2 · log(2m₀)⌋₊
gives 1 ≤ k ≤ m₀ and C·log(2m) < k < C'·log(2m) for all m ∈ [m₀, 2m₀],
provided m₀ is large enough.

The proof uses:
- log(2m)/log(2m₀) ∈ [1, 1 + log(2)/log(2m₀)] for m ∈ [m₀, 2m₀]
- (C+C')/2 is strictly between C and C'
- Floor loses at most 1, which is absorbed by the margin for large m₀
- k = O(log m₀) ≤ m₀ for large m₀ -/
lemma log_gap_bounds (C C' : ℝ) (hC : 0 < C) (hCC' : C < C') :
    ∃ M₀ : ℕ, ∀ m₀ : ℕ, M₀ ≤ m₀ →
      let k := ⌊(C + C') / 2 * Real.log (2 * ↑m₀)⌋₊
      1 ≤ k ∧ k ≤ m₀ ∧
      ∀ m : ℕ, m₀ ≤ m → m ≤ 2 * m₀ →
        C * Real.log (2 * ↑m) < ↑k ∧
        (↑k : ℝ) < C' * Real.log (2 * ↑m) := by
  sorry

/-- **Combined existence**: For 0 < C < C' and m₀ sufficiently large,
there exist m ∈ [m₀, 2m₀] and k ≥ 1 with C(m+k,k) | C(2m,m) and
C·log(2m) < k < C'·log(2m).

Proved by combining `exists_m_choose_dvd_uniform` and `log_gap_bounds`. -/
lemma exists_good_m (C C' : ℝ) (hC : 0 < C) (hCC' : C < C') :
    ∃ M₀ : ℕ, ∀ m₀ : ℕ, M₀ ≤ m₀ →
      ∃ m k : ℕ,
        m₀ ≤ m ∧ m ≤ 2 * m₀ ∧
        1 ≤ k ∧
        (m + k).choose k ∣ (2 * m).choose m ∧
        C * Real.log (2 * ↑m) < ↑k ∧
        (↑k : ℝ) < C' * Real.log (2 * ↑m) := by
  obtain ⟨M₁, hM₁⟩ := log_gap_bounds C C' hC hCC'
  obtain ⟨M₂, hM₂⟩ := exists_m_choose_dvd_uniform
  refine ⟨max M₁ M₂, fun m₀ hm₀ => ?_⟩
  have hm₀₁ : M₁ ≤ m₀ := le_of_max_le_left hm₀
  have hm₀₂ : M₂ ≤ m₀ := le_of_max_le_right hm₀
  obtain ⟨hk, hk_le, hgap⟩ := hM₁ m₀ hm₀₁
  set k := ⌊(C + C') / 2 * Real.log (2 * ↑m₀)⌋₊
  obtain ⟨m, hm_lb, hm_ub, hdvd⟩ := hM₂ m₀ hm₀₂ k hk hk_le
  exact ⟨m, k, hm_lb, hm_ub, hk, hdvd, (hgap m hm_lb hm_ub).1, (hgap m hm_lb hm_ub).2⟩

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
