import Mathlib
import Erdos.Lemmas
import Erdos.Lemma3Counting

open Real Nat Filter Asymptotics
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

/-- If for all primes p, padicValNat p a ≤ padicValNat p b, then a ∣ b.
    Converts pointwise p-adic valuation comparisons into divisibility. -/
private lemma dvd_of_padicValNat_le {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ p : ℕ, p.Prime → padicValNat p a ≤ padicValNat p b) : a ∣ b := by
  rw [← Nat.factorization_le_iff_dvd ha hb]
  intro p
  by_cases hp : p.Prime
  · rw [Nat.factorization_def a hp, Nat.factorization_def b hp]; exact h p hp
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- **Union bound over small primes (uniform in k)**: For any C_log and m₀
    sufficiently large, for every k with 1 ≤ k ≤ C_log * log(2m₀), there exists
    m ∈ [m₀, 2m₀) such that for ALL primes p ≤ 2k,
    v_p(C(m+k,k)) ≤ v_p(C(2m,m)).

    This combines:
    - Theorem E2 from proofs/lemma3-counting.md (per-k union bound)
    - The observation that M₀(k) = (2k)^{O(log k)} is subpolynomial in m₀
      when k ≤ C_log * log(2m₀), so a single M₀ suffices for all k.

    The proof structure:
    1. For each prime p ≤ 2k, choose D_p = 36⌈log₂(16k)⌉ + 36⌊log_p(k+1)⌋ + 36
    2. Apply count_bad_interval for each such prime (from Lemma3Counting.lean)
    3. Each prime contributes ≤ m₀/(8k) bad m values
    4. Union bound: total bad ≤ π(2k) · m₀/(8k) ≤ 2k · m₀/(8k) = m₀/4 < m₀
    5. Since |bad| < |[m₀, 2m₀)| = m₀, a good m exists

    SORRY: The union bound arithmetic is verified in the NL proof
    (proofs/lemma3-counting.md, Part E) but requires substantial formalization:
    - Explicit D_p computation and hypothesis verification
    - Summation over primes with Finset arithmetic
    - The M₀(k) ≤ m₀ bound when k = O(log m₀) -/
private lemma exists_m_small_primes_good_uniform (C_log : ℝ) :
    ∃ M₀ : ℕ, ∀ m₀ : ℕ, M₀ ≤ m₀ → ∀ k : ℕ, 1 ≤ k →
      (k : ℝ) ≤ C_log * Real.log (2 * m₀) →
      ∃ m : ℕ, m₀ ≤ m ∧ m < 2 * m₀ ∧
        ∀ p : ℕ, p.Prime → p ≤ 2 * k →
          padicValNat p ((m + k).choose k) ≤ padicValNat p ((2 * m).choose m) := by
  sorry

/-- **Core existence lemma**: For any constant C > 0 and all sufficiently large m₀,
for every k with 1 ≤ k ≤ C * log(2m₀), there exists m ∈ [m₀, 2m₀] such that
C(m+k, k) | C(2m, m). -/
lemma exists_m_choose_dvd_uniform (C_log : ℝ) :
    ∃ M₀ : ℕ, ∀ m₀ : ℕ, M₀ ≤ m₀ → ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ C_log * Real.log (2 * m₀) →
      ∃ m : ℕ, m₀ ≤ m ∧ m ≤ 2 * m₀ ∧ (m + k).choose k ∣ (2 * m).choose m := by
  -- Get the M₀ that handles all small primes uniformly
  obtain ⟨M₀, hM₀⟩ := exists_m_small_primes_good_uniform C_log
  refine ⟨max M₀ 1, fun m₀ hm₀ k hk hk_bound => ?_⟩
  have hm₀_M₀ : M₀ ≤ m₀ := le_of_max_le_left hm₀
  have hm₀_pos : 0 < m₀ := by omega
  -- Get m ∈ [m₀, 2m₀) good for all small primes
  obtain ⟨m, hm_lb, hm_ub_strict, hsmall⟩ := hM₀ m₀ hm₀_M₀ k hk hk_bound
  refine ⟨m, hm_lb, by omega, ?_⟩
  -- Prove C(m+k,k) | C(2m,m) by comparing all prime valuations
  apply dvd_of_padicValNat_le
  · exact Nat.ne_of_gt (Nat.choose_pos (Nat.le_add_left k m))
  · exact Nat.ne_of_gt (Nat.choose_pos (Nat.le_mul_of_pos_left m (by omega)))
  intro p hp
  by_cases hpk : 2 * k < p
  · -- Large prime (p > 2k): carry_dominance handles it unconditionally
    exact carry_dominance_padicValNat p m k hp hpk
  · -- Small prime (p ≤ 2k): the counting/union bound argument handles it
    push_neg at hpk
    exact hsmall p hp hpk

-- Helper lemmas for log_gap_bounds

private lemma log_le_sub_one {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ x - 1 := by
  calc Real.log x ≤ Real.log (Real.exp (x - 1)) := by
        apply Real.log_le_log (by linarith : 0 < x)
        linarith [Real.add_one_le_exp (x - 1)]
      _ = x - 1 := Real.log_exp (x - 1)

/-- A * log(2n) → ∞ as n → ∞ -/
private lemma tendsto_const_mul_log {A : ℝ} (hA : 0 < A) :
    Filter.Tendsto (fun n : ℕ => A * Real.log (2 * (n : ℝ))) Filter.atTop Filter.atTop :=
  Filter.Tendsto.const_mul_atTop hA
    (Real.tendsto_log_atTop.comp
      (Filter.Tendsto.const_mul_atTop (by norm_num : (0:ℝ) < 2) tendsto_natCast_atTop_atTop))

/-- A * log(2n) ≤ n eventually -/
private lemma eventually_log_le_id {A : ℝ} (hA : 0 < A) :
    ∀ᶠ n : ℕ in Filter.atTop, A * Real.log (2 * (n : ℝ)) ≤ (n : ℝ) := by
  rw [Filter.eventually_atTop]
  refine ⟨⌈8 * A ^ 2⌉₊ + 2, fun n hn => ?_⟩
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast show 0 < n by omega
  have h2n_nn : (0 : ℝ) ≤ 2 * (n : ℝ) := by linarith
  have h2n_ge1 : (1 : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast show 1 ≤ 2 * n by omega
  have hlog_bound : Real.log (2 * ↑n) ≤ 2 * Real.sqrt (2 * ↑n) := by
    have hsx : 1 ≤ Real.sqrt (2 * ↑n) := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt h2n_ge1
    calc Real.log (2 * ↑n) 
        = Real.log (Real.sqrt (2 * ↑n) ^ 2) := by rw [Real.sq_sqrt h2n_nn]
      _ = 2 * Real.log (Real.sqrt (2 * ↑n)) := by rw [Real.log_pow]; ring
      _ ≤ 2 * (Real.sqrt (2 * ↑n) - 1) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
          calc Real.log (Real.sqrt (2 * ↑n))
              ≤ Real.log (Real.exp (Real.sqrt (2 * ↑n) - 1)) := by
                apply Real.log_le_log (by positivity)
                linarith [Real.add_one_le_exp (Real.sqrt (2 * ↑n) - 1)]
            _ = Real.sqrt (2 * ↑n) - 1 := Real.log_exp _
      _ ≤ 2 * Real.sqrt (2 * ↑n) := by linarith
  have hsqrt_bound : 2 * A * Real.sqrt (2 * ↑n) ≤ (n : ℝ) := by
    have h_sq : (2 * A * Real.sqrt (2 * ↑n)) ^ 2 ≤ (n : ℝ) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt h2n_nn]
      have : 8 * A ^ 2 ≤ (n : ℝ) := by
        calc 8 * A ^ 2 ≤ ↑(⌈8 * A ^ 2⌉₊ + 2) := by push_cast; linarith [Nat.le_ceil (8 * A ^ 2)]
          _ ≤ ↑n := (Nat.cast_le (α := ℝ)).mpr hn
      nlinarith
    nlinarith [sq_abs (2 * A * Real.sqrt (2 * ↑n)), sq_abs (n : ℝ),
               abs_of_nonneg (show 0 ≤ 2 * A * Real.sqrt (2 * ↑n) from by positivity),
               abs_of_nonneg (show 0 ≤ (n : ℝ) from by linarith)]
  calc A * Real.log (2 * ↑n)
      ≤ A * (2 * Real.sqrt (2 * ↑n)) := mul_le_mul_of_nonneg_left hlog_bound (le_of_lt hA)
    _ = 2 * A * Real.sqrt (2 * ↑n) := by ring
    _ ≤ ↑n := hsqrt_bound

/-- **Log gap selection**: For 0 < C < C', the choice k = ⌊(C+C')/2 · log(2m₀)⌋₊
gives 1 ≤ k ≤ m₀ and C·log(2m) < k < C'·log(2m) for all m ∈ [m₀, 2m₀],
provided m₀ is large enough. -/
lemma log_gap_bounds (C C' : ℝ) (hC : 0 < C) (hCC' : C < C') :
    ∃ M₀ : ℕ, ∀ m₀ : ℕ, M₀ ≤ m₀ →
      let k := ⌊(C + C') / 2 * Real.log (2 * ↑m₀)⌋₊
      1 ≤ k ∧ k ≤ m₀ ∧
      ∀ m : ℕ, m₀ ≤ m → m ≤ 2 * m₀ →
        C * Real.log (2 * ↑m) < ↑k ∧
        (↑k : ℝ) < C' * Real.log (2 * ↑m) := by
  set avg := (C + C') / 2 with avg_def
  have hC_avg : C < avg := by linarith
  have havg_C' : avg < C' := by linarith
  have havg_pos : 0 < avg := by linarith
  have hgap : 0 < avg - C := by linarith
  -- Three eventually-true conditions
  have cond1 : ∀ᶠ m₀ : ℕ in Filter.atTop, 1 ≤ avg * Real.log (2 * ↑m₀) :=
    (tendsto_const_mul_log havg_pos).eventually_ge_atTop 1
  have cond2 : ∀ᶠ m₀ : ℕ in Filter.atTop,
      2 + C * Real.log 2 ≤ (avg - C) * Real.log (2 * ↑m₀) :=
    (tendsto_const_mul_log hgap).eventually_ge_atTop _
  have cond3 : ∀ᶠ m₀ : ℕ in Filter.atTop, avg * Real.log (2 * ↑m₀) ≤ ↑m₀ :=
    eventually_log_le_id havg_pos
  have cond4 : ∀ᶠ m₀ : ℕ in Filter.atTop, (1 : ℕ) ≤ m₀ :=
    Filter.eventually_atTop.mpr ⟨1, fun _ h => h⟩
  -- Combine
  rw [Filter.eventually_atTop] at cond1 cond2 cond3 cond4
  obtain ⟨N₁, hN₁⟩ := cond1; obtain ⟨N₂, hN₂⟩ := cond2
  obtain ⟨N₃, hN₃⟩ := cond3; obtain ⟨N₄, hN₄⟩ := cond4
  refine ⟨max (max N₁ N₂) (max N₃ N₄), fun m₀ hm₀ => ?_⟩
  have h1 := hN₁ m₀ (by omega); have h2 := hN₂ m₀ (by omega)
  have h3 := hN₃ m₀ (by omega); have h4 := hN₄ m₀ (by omega)
  set k := ⌊avg * Real.log (2 * ↑m₀)⌋₊ with k_def
  have hm₀_pos : (0 : ℝ) < (m₀ : ℝ) := by exact_mod_cast show 0 < m₀ by omega
  have h2m₀_pos : (0 : ℝ) < 2 * (m₀ : ℝ) := by linarith
  have hlog_pos : 0 < Real.log (2 * ↑m₀) := Real.log_pos (by linarith)
  have hk_le : (k : ℝ) ≤ avg * Real.log (2 * ↑m₀) := Nat.floor_le (by 
    have : 0 ≤ avg := by linarith
    have : 0 ≤ Real.log (2 * m₀) := by 
      apply Real.log_nonneg; linarith
    positivity)
  have hk_lb : avg * Real.log (2 * ↑m₀) - 1 < (k : ℝ) := Nat.sub_one_lt_floor _
  refine ⟨?_, ?_, ?_⟩
  · rwa [Nat.one_le_floor_iff]
  · rw [← Nat.cast_le (α := ℝ)]; linarith
  · intro m hm_lb hm_ub
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast show 0 < m by omega
    have h2m_pos : (0 : ℝ) < 2 * (m : ℝ) := by linarith
    have hlog_mono : Real.log (2 * ↑m₀) ≤ Real.log (2 * ↑m) :=
      Real.log_le_log h2m₀_pos (by linarith [(Nat.cast_le (α := ℝ)).mpr hm_lb])
    have hlog_2m_pos : 0 < Real.log (2 * ↑m) := lt_of_lt_of_le hlog_pos hlog_mono
    have hlog_ub : Real.log (2 * ↑m) ≤ Real.log (4 * ↑m₀) := by
      apply Real.log_le_log h2m_pos
      have : (m : ℝ) ≤ 2 * m₀ := by exact_mod_cast hm_ub
      linarith
    have hlog_split : Real.log (4 * (m₀ : ℝ)) = Real.log 2 + Real.log (2 * ↑m₀) := by
      rw [show (4 : ℝ) * ↑m₀ = 2 * (2 * ↑m₀) from by ring]
      rw [Real.log_mul (by norm_num) (by linarith)]
    constructor
    · -- C * log(2m) < k
      calc C * Real.log (2 * ↑m)
          ≤ C * Real.log (4 * ↑m₀) := mul_le_mul_of_nonneg_left hlog_ub (le_of_lt hC)
        _ = C * (Real.log 2 + Real.log (2 * ↑m₀)) := by rw [hlog_split]
        _ = C * Real.log (2 * ↑m₀) + C * Real.log 2 := by ring
        _ < avg * Real.log (2 * ↑m₀) - 1 := by nlinarith
        _ < ↑k := hk_lb
    · -- k < C' * log(2m)
      calc (k : ℝ) ≤ avg * Real.log (2 * ↑m₀) := hk_le
        _ ≤ avg * Real.log (2 * ↑m) := mul_le_mul_of_nonneg_left hlog_mono (le_of_lt havg_pos)
        _ < C' * Real.log (2 * ↑m) := mul_lt_mul_of_pos_right havg_C' hlog_2m_pos

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
  obtain ⟨M₂, hM₂⟩ := exists_m_choose_dvd_uniform (C' + 1)
  refine ⟨max M₁ M₂, fun m₀ hm₀ => ?_⟩
  have hm₀₁ : M₁ ≤ m₀ := le_of_max_le_left hm₀
  have hm₀₂ : M₂ ≤ m₀ := le_of_max_le_right hm₀
  obtain ⟨hk, hk_le_m₀, hgap⟩ := hM₁ m₀ hm₀₁
  set k := ⌊(C + C') / 2 * Real.log (2 * ↑m₀)⌋₊
  have hm₀_ge_1 : 1 ≤ m₀ := by omega
  have h2m₀_ge_1 : (1 : ℝ) ≤ 2 * (m₀ : ℝ) := by
    exact_mod_cast show 1 ≤ 2 * m₀ by omega
  have hlog_nn : (0 : ℝ) ≤ Real.log (2 * m₀) := Real.log_nonneg h2m₀_ge_1
  have hk_le_log : (k : ℝ) ≤ (C' + 1) * Real.log (2 * m₀) := by
    calc (k : ℝ) ≤ (C + C') / 2 * Real.log (2 * m₀) := Nat.floor_le (by
          exact mul_nonneg (by linarith) hlog_nn)
      _ ≤ C' * Real.log (2 * m₀) := by
          apply mul_le_mul_of_nonneg_right _ hlog_nn; linarith
      _ ≤ (C' + 1) * Real.log (2 * m₀) := by
          apply mul_le_mul_of_nonneg_right _ hlog_nn; linarith
  obtain ⟨m, hm_lb, hm_ub, hdvd⟩ := hM₂ m₀ hm₀₂ k hk hk_le_log
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
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
    have : ε < 1 / 4 := hε.2
    push_cast; nlinarith
  · -- ε * n < b: since ε * (2m) < m ≤ m + k
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
    have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have : ε < 1 / 4 := hε.2
    push_cast; nlinarith
  · -- a! * b! ∣ n! * (a + b - n)!
    -- By reduction_lemma: C(m+k,k) | C(2m,m) ↔ m!(m+k)! | (2m)!k!
    rw [show m + (m + k) - 2 * m = k from by omega]
    exact (reduction_lemma m k).mp hdvd
  · -- a + b > n + C * log n: follows from k > C * log(2m)
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
    push_cast; linarith
  · -- a + b < n + C' * log n: follows from k < C' * log(2m)
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
    push_cast; linarith

end Erdos728
