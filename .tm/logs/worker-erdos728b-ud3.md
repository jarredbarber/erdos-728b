# timtam Task: Formalize Main Theorem (existence via union bound) (erdos728b-ud3)

Role: formalize
Agent: formalize (google-antigravity/claude-opus-4-6-thinking)
Start Time: 2026-02-10T16:41:35.900Z

## Agent Interaction



> **Thinking:**
> Let me start by understanding the current state of the project - reading the main theorem file, any existing lemmas, and the relevant proof files.


🛠️ **Executing tool: read**

🛠️ **Executing tool: read**

```bash
$ ls /home/jarred/code/erdos-728b/proofs/
```

```bash
$ ls /home/jarred/code/erdos-728b/proofs/ && cat /home/jarred/code/erdos-728b/proofs/erdos728_v2.md
```

```bash
$ cat /home/jarred/code/erdos-728b/proofs/erdos728.md
```
Now let me read the other proof files and check the current state of the project:
```bash
$ cat /home/jarred/code/erdos-728b/proofs/lemma3-counting.md
```

```bash
$ cat /home/jarred/code/erdos-728b/proofs/sieve-lemma.md
```

```bash
$ ls /home/jarred/code/erdos-728b/artifacts/
```

```bash
$ cat /home/jarred/code/erdos-728b/artifacts/mathlib-coverage.md
```

```bash
$ cd /home/jarred/code/erdos-728b && lake build 2>&1 | tail -20
```
Good. The project compiles with just the one `sorry` in the main theorem. Now let me understand the full picture and update my progress:
```bash
$ cd /home/jarred/code/erdos-728b && tm update erdos728b-ud3 --status "Reading NL proofs and understanding the formalization approach. Current state: one sorry in erdos_728 theorem." 2>/dev/null || true
```
Let me now think about the formalization strategy. The NL proof is a probabilistic/counting existence argument. The main theorem statement uses `∀ᶠ ε : ℝ in 𝓝[>] 0` (eventually for small ε) and existential quantifiers. This is a very deep proof to formalize end-to-end. Let me explore what Mathlib tools are available and plan the decomposition.
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_filter.lean << 'EOF'
import Mathlib

#check Filter.Eventually
#check nhdsWithin
#check Filter.eventually_nhdsWithin_iff
#check Nat.choose_dvd_choose_iff
#check Nat.factorization_le_iff_pow_dvd_of_ne_zero
#check Nat.factorization_le_iff_dvd
EOF
lake env lean /tmp/test_filter.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test2.lean << 'EOF'
import Mathlib

-- Check how to work with nhdsWithin
#check nhdsWithin_Ioi_eq_nhdsWithin
#check eventually_nhdsWithin_iff  
#check Filter.Eventually.mono
#check Finsupp.le_iff
#check Nat.factorization_le_iff_dvd
-- Check Kummer's theorem availability
#check Nat.factorization_choose_le
EOF
lake env lean /tmp/test2.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test3.lean << 'EOF'
import Mathlib

-- Explore how to construct the "eventually" proof
example : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0), ε < 1/4 := by
  rw [eventually_nhdsWithin_iff]
  apply Filter.eventually_of_forall
  intro x hx
  simp at hx
  linarith

-- Try a simpler version
example : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0), ε < 1 := by
  rw [eventually_nhdsWithin_iff]
  rw [Filter.eventually_iff_exists_mem]
  exact ⟨Set.Ioo (-1) 1, Ioo_mem_nhds (by norm_num) (by norm_num), fun x hx _ => hx.2⟩

-- Check nhds > notation  
#check nhdsWithin (0 : ℝ) (Set.Ioi 0)
#print nhds
EOF
lake env lean /tmp/test3.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test4.lean << 'EOF'
import Mathlib

-- Let's see what 𝓝[>] 0 is
#check @nhdsWithin ℝ _ (0 : ℝ) (Set.Ioi 0)
-- That's the same as 𝓝[>] 0

-- Let's try to produce a simple "eventually" fact
example : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < 1 := by
  apply Filter.eventually_of_mem (Ioo_mem_nhdsWithin_Ioi (by norm_num : (0:ℝ) ≤ 0))
  intro x hx
  exact hx.2

-- Check eventuality helpers
#check Ioo_mem_nhdsWithin_Ioi
#check Ico_mem_nhdsWithin_Ioi
EOF
lake env lean /tmp/test4.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && grep -r "nhdsWithin_Ioi" .lake/packages/mathlib/Mathlib/ --include="*.lean" -l | head -5
```

```bash
$ cd /home/jarred/code/erdos-728b && grep "mem_nhdsWithin_Ioi" .lake/packages/mathlib/Mathlib/Topology/Order/DenselyOrdered.lean | head -20
```

```bash
$ cd /home/jarred/code/erdos-728b && grep -r "mem_nhdsWithin_Ioi" .lake/packages/mathlib/Mathlib/ --include="*.lean" | head -10
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test5.lean << 'EOF'
import Mathlib

-- Let's try the notation
example : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < 1 := by
  rw [eventually_nhdsWithin_iff]
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨Set.Ioo (-1) 1, Ioo_mem_nhds (by norm_num) (by norm_num), ?_⟩
  intro x hx _
  exact hx.2
EOF
lake env lean /tmp/test5.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && grep "scoped notation" .lake/packages/mathlib/Mathlib/Topology/Basic.lean | head -10
```

```bash
$ cd /home/jarred/code/erdos-728b && grep -rn "𝓝\[>" .lake/packages/mathlib/Mathlib/ --include="*.lean" | head -5
```

```bash
$ cd /home/jarred/code/erdos-728b && grep -rn "notation.*𝓝\[" .lake/packages/mathlib/Mathlib/ --include="*.lean" | head -10
```
So `𝓝[>]` is `notation3` — I need to use the right syntax. Let me look at how the theorem itself uses it:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test6.lean << 'EOF'
import Mathlib
open scoped Topology

-- The theorem uses 𝓝[>] 0 which is nhdsWithin 0 (Set.Ioi 0)
example : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < 1 := by
  rw [eventually_nhdsWithin_iff]
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨Set.Ioo (-1) 1, Ioo_mem_nhds (by norm_num) (by norm_num), ?_⟩
  intro x hx _
  exact hx.2
EOF
lake env lean /tmp/test6.lean 2>&1
```
Good, that works. Now let me think about the overall strategy. The proof is extremely complex — it involves:

1. Carry dominance (Lemma 2 — already formalized)
2. Reduction to binomial coefficients (Lemma 1 — already formalized)
3. Probabilistic/counting argument for small primes (Lemma 3 — not formalized)
4. Union bound combining everything

This is a massive formalization effort. The task says to "combine Lemmas 1, 2, 3 to prove the main theorem." Given the complexity, the best approach is to:
- State the key intermediate results as `sorry`d lemmas
- Use them to prove the main theorem structure
- Leave the individual lemma proofs for separate tasks

Let me plan the proof structure:
```bash
$ cd /home/jarred/code/erdos-728b && tm update erdos728b-ud3 --status "Planning proof structure. Will decompose into helper lemmas with sorry, then wire them together." 2>/dev/null || true
```
Let me first explore what API is available for key concepts:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_api.lean << 'EOF'
import Mathlib
open Nat

-- Key facts we need:
-- 1. Factorization characterizes divisibility
#check Nat.factorization_le_iff_dvd
-- 2. Choose is nonzero
#check Nat.choose_pos
-- 3. Factorial positivity
#check Nat.factorial_pos
-- 4. Log properties
#check Real.log_pos
#check Real.log_lt_log_of_lt
-- 5. Nat.Prime and primes
#check Nat.Prime
-- 6. Finset operations
#check Finset.filter
#check Finset.card_pos
-- 7. Exists from card_pos
#check Finset.Nonempty.exists_eq

-- Let's see what we can do with choose divisibility
-- We need: if for all primes p, v_p(a) ≤ v_p(b), then a ∣ b
-- That's exactly factorization_le_iff_dvd
example (d n : ℕ) (hd : d ≠ 0) (hn : n ≠ 0) 
    (h : ∀ p, d.factorization p ≤ n.factorization p) : d ∣ n := by
  rwa [← Nat.factorization_le_iff_dvd hd hn]
  exact Finsupp.le_iff.mpr (fun p _ => h p)
EOF
lake env lean /tmp/test_api.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_api2.lean << 'EOF'
import Mathlib
open Nat

-- Test factorization_le_iff_dvd usage
example (d n : ℕ) (hd : d ≠ 0) (hn : n ≠ 0) 
    (h : ∀ p, d.factorization p ≤ n.factorization p) : d ∣ n := by
  rw [← Nat.factorization_le_iff_dvd hd hn]
  exact fun p => h p

-- Good! Now let's check how factorization interacts with choose
-- We need: factorization of choose(m+k, k)
#check Nat.factorization_choose
EOF
lake env lean /tmp/test_api2.lean 2>&1
```
Good. Now let me think about the big picture. The main theorem proof goes like this:

1. Fix any `C > 0` and `C' > C`. Choose `ε = 1/8` (or any small constant < 1/4).
2. For sufficiently large `m₀`, set `k = ⌊(C+C')/2 · log(2m₀)⌋`.
3. Find `m ∈ [m₀, 2m₀]` such that `C(m+k,k) | C(2m,m)`.
4. Set `a = m, b = m+k, n = 2m` and verify all conditions.

Step 3 is the hard part — it requires the counting/probabilistic argument. The cleanest approach for formalization is to state the existence result as a sorry'd lemma and build the main theorem around it.

Let me write the formalization:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_structure.lean << 'EOF'
import Mathlib

open Real Nat
open scoped Nat Topology

namespace Erdos728

-- Check key operations
#check Nat.choose
#check Nat.log  -- this is floor(log_b(n))
#check Real.log  -- natural log

-- Check how to express "for all p prime, v_p(a) ≤ v_p(b)"
-- implies a ∣ b
example (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ p : ℕ, Nat.Prime p → a.factorization p ≤ b.factorization p) : a ∣ b := by
  rw [← Nat.factorization_le_iff_dvd ha hb]
  intro p
  by_cases hp : Nat.Prime p
  · exact h p hp
  · simp [Nat.factorization_eq_zero_of_non_prime _ hp]

end Erdos728
EOF
lake env lean /tmp/test_structure.lean 2>&1
```
Good. Now let me design the helper lemmas and the main proof:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_main.lean << 'EOF'
import Mathlib
import Erdos.Lemmas

open Real Nat
open scoped Nat Topology

namespace Erdos728

/-! 
## Key existence lemma (the heart of the proof)

For any k ≥ 1, for m₀ sufficiently large, there exists m ∈ [m₀, 2m₀] 
such that C(m+k, k) ∣ C(2m, m).

This combines:
- Carry dominance (Lemma 2): for primes p > 2k, v_p(C(m+k,k)) ≤ v_p(C(2m,m)) always.
- Counting argument (Lemma 3): for primes p ≤ 2k, the set of "bad" m in any 
  large interval has density < 1, so a "good" m exists.
-/

/-- For any k ≥ 1, for all sufficiently large m₀, there exists m in [m₀, 2m₀]
such that choose(m+k, k) divides choose(2m, m). -/
lemma exists_m_choose_dvd (k : ℕ) (hk : 1 ≤ k) :
    ∃ M₀ : ℕ, ∀ m₀ : ℕ, M₀ ≤ m₀ →
      ∃ m : ℕ, m₀ ≤ m ∧ m ≤ 2 * m₀ ∧ (m + k).choose k ∣ (2 * m).choose m := by
  sorry

/-- The main theorem using the substitution a = m, b = m + k, n = 2m. -/
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
EOF
lake env lean /tmp/test_main.lean 2>&1
```
Good, it compiles. Now let me think carefully about how to connect the pieces. The key steps are:

1. We need to show `∀ᶠ ε in 𝓝[>] 0, ...` — we can take any ε < 1/4
2. Given C, C' with 0 < C < C', we choose k appropriately
3. We find m using `exists_m_choose_dvd` 
4. We verify the conditions

The trickiest parts are:
- Converting between `choose` divisibility and factorial divisibility (using `reduction_lemma`)
- The logarithmic bounds on k = a + b - n

Let me work on the main theorem proof, assuming `exists_m_choose_dvd`:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_main2.lean << 'EOF'
import Mathlib
import Erdos.Lemmas

open Real Nat
open scoped Nat Topology

namespace Erdos728

-- Let me check what the reduction lemma gives us
-- reduction_lemma (m k : ℕ) :
--     (m+k).choose k ∣ (2*m).choose m ↔
--     m.factorial * (m+k).factorial ∣ (2*m).factorial * k.factorial

-- The theorem needs: a ! * b ! ∣ n ! * (a + b - n)!
-- With a = m, b = m + k, n = 2m:
-- m ! * (m + k) ! ∣ (2m) ! * k !
-- and a + b - n = m + (m + k) - 2m = k
-- but in ℕ: a + b - n = m + (m + k) - 2*m = k (when m + (m+k) ≥ 2m, which is always true since k ≥ 0)

-- Let's verify the natural number arithmetic
example (m k : ℕ) : m + (m + k) - 2 * m = k := by omega
-- Good!

-- And check: a + b > n means m + (m + k) > 2m, i.e., k > 0
-- a + b - n = k when a + b ≥ n

-- The gap condition: a + b > n + C * log n means k > C * log(2m)
-- and a + b < n + C' * log n means k < C' * log(2m)

-- So we need: C * log(2m) < k < C' * log(2m)
-- If we choose k = ⌊(C + C')/2 * log(2m₀)⌋, we need m large enough that
-- this k satisfies both bounds for m ∈ [m₀, 2m₀]

-- Check floor
#check Nat.floor
#check Int.toNat
EOF
lake env lean /tmp/test_main2.lean 2>&1
```
Now let me think about the approach more carefully. The main theorem is very involved to prove end-to-end. The task says to "combine Lemmas 1, 2, 3" and use the union bound. The cleanest approach is:

1. State `exists_m_choose_dvd` as the core existence lemma (sorry'd)
2. State a helper lemma about the logarithmic gap bounds (sorry'd)
3. Wire them together for the main theorem

Let me write this step by step:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_main3.lean << 'EOF'
import Mathlib
import Erdos.Lemmas

open Real Nat
open scoped Nat Topology

namespace Erdos728

/-- For any k ≥ 1 and sufficiently large m₀, there exists m in [m₀, 2m₀]
such that choose(m+k, k) divides choose(2m, m).

This is the core existence result, combining:
- Carry dominance for primes p > 2k (Lemma 2, already formalized)
- Counting argument for primes p ≤ 2k (Lemma 3)
- Union bound showing total failure probability < 1 -/
lemma exists_m_choose_dvd (k : ℕ) (hk : 1 ≤ k) :
    ∃ M₀ : ℕ, ∀ m₀ : ℕ, M₀ ≤ m₀ →
      ∃ m : ℕ, m₀ ≤ m ∧ m ≤ 2 * m₀ ∧ (m + k).choose k ∣ (2 * m).choose m := by
  sorry

/-- Auxiliary: For m ≥ 1, the reduction lemma gives us the factorial divisibility
from choose divisibility. We restate in terms of a, b, n. -/
lemma factorial_dvd_of_choose_dvd (m k : ℕ) (hm : 1 ≤ m) 
    (hdvd : (m + k).choose k ∣ (2 * m).choose m) :
    m ! * (m + k) ! ∣ (2 * m) ! * k ! :=
  (reduction_lemma m k).mp hdvd

/-- The key logarithmic bound: for C, C' with 0 < C < C', for m₀ large enough,
    if k = ⌊(C+C')/2 * log(2m₀)⌋ and m ∈ [m₀, 2m₀], then
    C * log(2m) < k and k < C' * log(2m). -/
lemma log_gap_bounds (C C' : ℝ) (hC : 0 < C) (hCC' : C < C') :
    ∃ M₀ : ℕ, ∀ m₀ : ℕ, M₀ ≤ m₀ →
      let k := ⌊(C + C') / 2 * Real.log (2 * m₀)⌋₊
      1 ≤ k ∧ 
      ∀ m : ℕ, m₀ ≤ m → m ≤ 2 * m₀ →
        C * Real.log (2 * ↑m) < ↑k ∧ 
        (↑k : ℝ) < C' * Real.log (2 * ↑m) := by
  sorry

end Erdos728
EOF
lake env lean /tmp/test_main3.lean 2>&1
```
Good, the structure compiles. Now let me build the actual main theorem proof using these helpers:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_main4.lean << 'EOF'
import Mathlib
import Erdos.Lemmas

open Real Nat
open scoped Nat Topology

namespace Erdos728

-- Helper lemmas (sorry'd - will be proved separately)

lemma exists_m_choose_dvd (k : ℕ) (hk : 1 ≤ k) :
    ∃ M₀ : ℕ, ∀ m₀ : ℕ, M₀ ≤ m₀ →
      ∃ m : ℕ, m₀ ≤ m ∧ m ≤ 2 * m₀ ∧ (m + k).choose k ∣ (2 * m).choose m := by
  sorry

lemma log_gap_bounds (C C' : ℝ) (hC : 0 < C) (hCC' : C < C') :
    ∃ M₀ : ℕ, ∀ m₀ : ℕ, M₀ ≤ m₀ →
      let k := ⌊(C + C') / 2 * Real.log (2 * m₀)⌋₊
      1 ≤ k ∧ 
      ∀ m : ℕ, m₀ ≤ m → m ≤ 2 * m₀ →
        C * Real.log (2 * ↑m) < ↑k ∧ 
        (↑k : ℝ) < C' * Real.log (2 * ↑m) := by
  sorry

-- Now the main theorem
-- We need to produce: ∀ᶠ ε in 𝓝[>] 0, ∀ C > 0, ∀ C' > C, ∃ a b n, ...
-- Key: for any ε < 1/4, the result holds

-- Let's first check what n = 2*m gives us for the size bounds
-- a = m, b = m + k, n = 2*m
-- ε * n = 2*ε*m < m = a when ε < 1/2 (always true for ε < 1/4)
-- ε * n = 2*ε*m < m + k = b when ε < 1/2 (since k ≥ 0)

-- Let's also check: a + b - n = m + (m+k) - 2*m = k in ℕ
-- a + b > n ↔ k > 0 (which we ensure)
-- a + b = 2*m + k, n = 2*m, so a + b > n + C * log n ↔ k > C * log(2m)

-- The condition a + b > n + C * log n is:
-- (2*m + k : ℕ) > (2*m : ℕ) + C * log(2*m)
-- But the RHS has C * log(2*m) which is a real number added to a nat
-- In the theorem statement, it's (a + b : ℕ) > (n : ℕ) + C * Real.log ↑n
-- Wait, let me re-read the theorem statement carefully

-- a + b > n + C * Real.log n
-- Here a + b and n are ℕ, but the inequality is in ℝ (implicit coercion)
-- So it's: (↑(a + b) : ℝ) > (↑n : ℝ) + C * Real.log (↑n)

-- Similarly: a + b < n + C' * Real.log n is
-- (↑(a + b) : ℝ) < (↑n : ℝ) + C' * Real.log (↑n)

-- With a = m, b = m+k, n = 2*m:
-- a + b = m + (m + k) = 2*m + k
-- ↑(2*m + k) > ↑(2*m) + C * log(↑(2*m))
-- ↔ ↑k > C * log(↑(2*m))
-- since ↑(2*m + k) - ↑(2*m) = ↑k

-- Similarly: ↑(2*m + k) < ↑(2*m) + C' * log(↑(2*m))
-- ↔ ↑k < C' * log(↑(2*m))

-- Great! So the log_gap_bounds lemma gives exactly what we need.

-- Now let me also check: ε * n < a means ε * ↑(2*m) < ↑m
-- ↔ 2*ε*↑m < ↑m ↔ 2*ε < 1 ↔ ε < 1/2

-- And n > 0 means 2*m > 0, i.e., m > 0, which holds since m ≥ m₀ ≥ 1

-- Now let me try to write the proof:
theorem erdos_728 :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ C > (0 : ℝ), ∀ C' > C,
      ∃ a b n : ℕ,
        0 < n ∧
        ε * n < a ∧
        ε * n < b ∧
        a ! * b ! ∣ n ! * (a + b - n)! ∧
        a + b > n + C * Real.log n ∧
        a + b < n + C' * Real.log n := by
  -- It suffices to show this for all ε ∈ (0, 1/4)
  rw [eventually_nhdsWithin_iff]
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨Set.Ioo 0 (1/4), Ioo_mem_nhds (by norm_num) (by norm_num), ?_⟩
  intro ε hε hε_pos
  simp only [Set.mem_Ioi] at hε_pos
  obtain ⟨hε_lb, hε_ub⟩ := hε  -- 0 < ε and ε < 1/4
  intro C hC C' hCC'
  -- Get the log gap bounds
  obtain ⟨M₁, hM₁⟩ := log_gap_bounds C C' hC hCC'
  -- Get the existence result
  -- We need k first, then get the existence for that k
  -- But k depends on m₀... We need to pick m₀ large enough for both
  sorry

end Erdos728
EOF
lake env lean /tmp/test_main4.lean 2>&1
```
The issue is that `hε` from `Set.Ioo` doesn't unpack correctly with `hε_pos` being separate. Let me fix:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_main5.lean << 'EOF'
import Mathlib
import Erdos.Lemmas

open Real Nat
open scoped Nat Topology

namespace Erdos728

lemma exists_m_choose_dvd (k : ℕ) (hk : 1 ≤ k) :
    ∃ M₀ : ℕ, ∀ m₀ : ℕ, M₀ ≤ m₀ →
      ∃ m : ℕ, m₀ ≤ m ∧ m ≤ 2 * m₀ ∧ (m + k).choose k ∣ (2 * m).choose m := by
  sorry

lemma log_gap_bounds (C C' : ℝ) (hC : 0 < C) (hCC' : C < C') :
    ∃ M₀ : ℕ, ∀ m₀ : ℕ, M₀ ≤ m₀ →
      let k := ⌊(C + C') / 2 * Real.log (2 * m₀)⌋₊
      1 ≤ k ∧ 
      ∀ m : ℕ, m₀ ≤ m → m ≤ 2 * m₀ →
        C * Real.log (2 * ↑m) < ↑k ∧ 
        (↑k : ℝ) < C' * Real.log (2 * ↑m) := by
  sorry

-- The theorem
theorem erdos_728 :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ C > (0 : ℝ), ∀ C' > C,
      ∃ a b n : ℕ,
        0 < n ∧
        ε * n < a ∧
        ε * n < b ∧
        a ! * b ! ∣ n ! * (a + b - n)! ∧
        a + b > n + C * Real.log n ∧
        a + b < n + C' * Real.log n := by
  rw [eventually_nhdsWithin_iff]
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨Set.Ioo 0 (1/4), Ioo_mem_nhds (by norm_num) (by norm_num), ?_⟩
  intro ε ⟨hε_pos, hε_lt⟩ _
  intro C hC C' hCC'
  -- Step 1: Get log gap bounds for this C, C'
  obtain ⟨M₁, hM₁⟩ := log_gap_bounds C C' hC hCC'
  -- Step 2: We need to choose m₀ large enough, then get k, then get m
  -- Choose m₀ = max(M₁, something large enough for size bounds)
  -- k = ⌊(C + C') / 2 * log(2 * m₀)⌋₊
  -- Then exists_m_choose_dvd gives us M₀_k for this k
  -- Then we need m₀ ≥ max(M₁, M₀_k)
  -- But k depends on m₀... this is circular!
  -- 
  -- The fix: k grows as O(log m₀), so for ANY k, exists_m_choose_dvd
  -- gives a threshold M₀_k. We just need m₀ large enough that:
  -- (a) m₀ ≥ M₁ (for log gap bounds)  
  -- (b) m₀ ≥ M₀_k where k = ⌊(C+C')/2 * log(2*m₀)⌋₊
  -- Since M₀_k is some fixed number depending on k, and k grows as log m₀,
  -- such m₀ exists.
  --
  -- Alternative simpler approach: pick a specific large m₀ and compute.
  -- Let's take a different route: use a combined helper.
  sorry

end Erdos728
EOF
lake env lean /tmp/test_main5.lean 2>&1
```
The `_` at the end doesn't match. Let me look at what the `hε_pos` argument actually is:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_main6.lean << 'EOF'
import Mathlib
import Erdos.Lemmas

open Real Nat
open scoped Nat Topology

namespace Erdos728

-- Let me check what the filter constraint looks like
-- 𝓝[>] 0 = nhdsWithin 0 (Set.Ioi 0)
-- eventually_nhdsWithin_iff says:
-- (∀ᶠ x in nhdsWithin a s, p x) ↔ ∀ᶠ x in nhds a, x ∈ s → p x
-- So after rewriting, we get: ∀ᶠ ε in 𝓝 0, ε ∈ Set.Ioi 0 → ∀ C > 0, ...
-- i.e., ∀ᶠ ε in 𝓝 0, ε > 0 → ∀ C > 0, ...

-- When we use Ioo_mem_nhds + intro, we get:
-- ε : ℝ, hε : ε ∈ Set.Ioo 0 (1/4), hε_mem : ε ∈ Set.Ioi 0

example : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < 1/4 := by
  rw [eventually_nhdsWithin_iff]
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨Set.Ioo 0 (1/4), Ioo_mem_nhds (by norm_num) (by norm_num), ?_⟩
  intro ε hε hε_pos
  -- hε : ε ∈ Set.Ioo 0 (1/4)
  -- hε_pos : ε ∈ Set.Ioi 0
  exact hε.2

end Erdos728
EOF
lake env lean /tmp/test_main6.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_main6b.lean << 'EOF'
import Mathlib
open scoped Topology

-- Let me just look at what the eventually_nhdsWithin_iff gives us
example : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < 1/4 := by
  rw [eventually_nhdsWithin_iff]
  -- Goal: ∀ᶠ (x : ℝ) in nhds 0, x ∈ Set.Ioi 0 → x < 1 / 4
  rw [Filter.eventually_iff_exists_mem]
  -- Goal: ∃ t ∈ 𝓝 0, ∀ x ∈ t, x ∈ Set.Ioi 0 → x < 1/4
  refine ⟨Set.Ioo (-1) (1/4), Ioo_mem_nhds (by norm_num) (by norm_num), ?_⟩
  intro x hx _
  exact hx.2
EOF
lake env lean /tmp/test_main6b.lean 2>&1
```
Good — the `_` is the `x ∈ Set.Ioi 0` hypothesis. Now let me build the full proof:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_main7.lean << 'EOF'
import Mathlib
import Erdos.Lemmas

open Real Nat
open scoped Nat Topology

namespace Erdos728

/-- Combined existence lemma: given C, C' with 0 < C < C', for all sufficiently
large m₀, there exists m ∈ [m₀, 2m₀] and k with:
  1. C(m+k, k) | C(2m, m)
  2. C * log(2m) < k < C' * log(2m)
  3. k ≥ 1

This combines the log gap selection with the existence of good m. -/
lemma exists_good_m (C C' : ℝ) (hC : 0 < C) (hCC' : C < C') :
    ∃ M₀ : ℕ, ∀ m₀ : ℕ, M₀ ≤ m₀ →
      ∃ m k : ℕ, 
        m₀ ≤ m ∧ m ≤ 2 * m₀ ∧ 
        1 ≤ k ∧
        (m + k).choose k ∣ (2 * m).choose m ∧
        C * Real.log (2 * ↑m) < ↑k ∧ 
        (↑k : ℝ) < C' * Real.log (2 * ↑m) := by
  sorry

theorem erdos_728 :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ C > (0 : ℝ), ∀ C' > C,
      ∃ a b n : ℕ,
        0 < n ∧
        ε * n < a ∧
        ε * n < b ∧
        a ! * b ! ∣ n ! * (a + b - n)! ∧
        a + b > n + C * Real.log n ∧
        a + b < n + C' * Real.log n := by
  rw [eventually_nhdsWithin_iff]
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨Set.Ioo (-1) (1/4), Ioo_mem_nhds (by norm_num) (by norm_num), ?_⟩
  intro ε hε hε_pos
  simp only [Set.mem_Ioi] at hε_pos
  intro C hC C' hCC'
  -- Get a good m and k
  obtain ⟨M₀, hM₀⟩ := exists_good_m C C' hC hCC'
  -- Pick m₀ large enough: m₀ ≥ M₀ and m₀ ≥ 1
  set m₀ := max M₀ 1
  obtain ⟨m, k, hm_lb, hm_ub, hk, hdvd, hk_lb, hk_ub⟩ := hM₀ m₀ (le_max_left _ _)
  -- Set a = m, b = m + k, n = 2 * m
  refine ⟨m, m + k, 2 * m, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- 0 < n = 2 * m 
    have : 1 ≤ m₀ := le_max_right M₀ 1
    omega
  · -- ε * n < a, i.e., ε * (2 * m) < m
    -- Since ε < 1/4, we have ε * (2 * m) < (1/4) * (2 * m) = m/2 < m
    have hm_pos : (0 : ℝ) < m := by
      have : 1 ≤ m₀ := le_max_right M₀ 1; exact_mod_cast show 0 < m by omega
    push_cast
    calc ε * (2 * ↑m) < (1/4) * (2 * ↑m) := by nlinarith [hε.2]
    _ = ↑m / 2 := by ring
    _ < ↑m := by linarith
  · -- ε * n < b = m + k
    -- Since ε * (2m) < m ≤ m + k
    have hm_pos : (0 : ℝ) < m := by
      have : 1 ≤ m₀ := le_max_right M₀ 1; exact_mod_cast show 0 < m by omega
    push_cast
    calc ε * (2 * ↑m) < (1/4) * (2 * ↑m) := by nlinarith [hε.2]
    _ = ↑m / 2 := by ring
    _ < ↑m := by linarith
    _ ≤ ↑m + ↑k := by linarith [show (0 : ℝ) ≤ ↑k from Nat.cast_nonneg k]
  · -- a ! * b ! ∣ n ! * (a + b - n)!
    -- i.e., m ! * (m + k) ! ∣ (2 * m) ! * k !
    -- a + b - n = m + (m + k) - 2 * m = k
    have hab_ge_n : 2 * m ≤ m + (m + k) := by omega
    rw [show m + (m + k) - 2 * m = k from by omega]
    exact (reduction_lemma m k).mp hdvd
  · -- a + b > n + C * log n
    -- i.e., (m + (m + k) : ℝ) > (2 * m : ℝ) + C * log(2 * m)
    push_cast
    linarith [hk_lb]
  · -- a + b < n + C' * log n
    -- i.e., (m + (m + k) : ℝ) < (2 * m : ℝ) + C' * log(2 * m)
    push_cast
    linarith [hk_ub]

end Erdos728
EOF
lake env lean /tmp/test_main7.lean 2>&1
```
Excellent! The main theorem proof compiles with only `exists_good_m` as a sorry! Let me verify the whole structure more carefully and clean it up:
```bash
$ cd /home/jarred/code/erdos-728b && tm update erdos728b-ud3 --status "Main theorem proof structure works! Only depends on exists_good_m (sorry'd). Now refining and decomposing exists_good_m." 2>/dev/null || true
```
Now let me further decompose `exists_good_m` into two parts: the log gap bounds and the choose divisibility existence:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_decompose.lean << 'EOF'
import Mathlib
import Erdos.Lemmas

open Real Nat
open scoped Nat Topology

namespace Erdos728

/-- For any k ≥ 1, for all sufficiently large m₀, there exists m ∈ [m₀, 2m₀]
such that C(m+k, k) | C(2m, m). 

Proof sketch: 
- For primes p > 2k: v_p(C(m+k,k)) ≤ v_p(C(2m,m)) by carry dominance (for ALL m).
- For primes p ≤ 2k: A counting argument shows that for m uniform in [m₀, 2m₀],
  the probability that v_p(C(m+k,k)) > v_p(C(2m,m)) is ≤ 1/p^{D/40} where 
  D = log_p(m₀). By union bound over π(2k) primes, the total failure probability 
  is < 1 for m₀ sufficiently large. -/
lemma exists_m_choose_dvd (k : ℕ) (hk : 1 ≤ k) :
    ∃ M₀ : ℕ, ∀ m₀ : ℕ, M₀ ≤ m₀ →
      ∃ m : ℕ, m₀ ≤ m ∧ m ≤ 2 * m₀ ∧ (m + k).choose k ∣ (2 * m).choose m := by
  sorry

/-- For C, C' with 0 < C < C', for m₀ large enough,
k = ⌊(C+C')/2 * log(2m₀)⌋₊ satisfies: k ≥ 1, and for all m ∈ [m₀, 2m₀],
C * log(2m) < k < C' * log(2m). -/
lemma log_gap_bounds (C C' : ℝ) (hC : 0 < C) (hCC' : C < C') :
    ∃ M₀ : ℕ, ∀ m₀ : ℕ, M₀ ≤ m₀ →
      let k := ⌊(C + C') / 2 * Real.log (2 * ↑m₀)⌋₊
      1 ≤ k ∧ 
      ∀ m : ℕ, m₀ ≤ m → m ≤ 2 * m₀ →
        C * Real.log (2 * ↑m) < ↑k ∧ 
        (↑k : ℝ) < C' * Real.log (2 * ↑m) := by
  sorry

/-- Combined existence lemma. -/
lemma exists_good_m (C C' : ℝ) (hC : 0 < C) (hCC' : C < C') :
    ∃ M₀ : ℕ, ∀ m₀ : ℕ, M₀ ≤ m₀ →
      ∃ m k : ℕ, 
        m₀ ≤ m ∧ m ≤ 2 * m₀ ∧ 
        1 ≤ k ∧
        (m + k).choose k ∣ (2 * m).choose m ∧
        C * Real.log (2 * ↑m) < ↑k ∧ 
        (↑k : ℝ) < C' * Real.log (2 * ↑m) := by
  -- Get thresholds from both lemmas
  obtain ⟨M₁, hM₁⟩ := log_gap_bounds C C' hC hCC'
  -- For each m₀ ≥ M₁, we get k = ⌊(C+C')/2 * log(2m₀)⌋₊
  -- Then exists_m_choose_dvd gives a threshold M₂(k) for this k
  -- We need m₀ ≥ max(M₁, M₂(k)) — but k depends on m₀!
  -- 
  -- Fix: We can use a two-step argument.
  -- First pick m₀ ≥ M₁ to get k. Then get M₂ for this k.
  -- Then pick m₀' = max(m₀, M₂) and observe that k doesn't decrease.
  -- But k might change when we change m₀!
  --
  -- Actually, the cleanest approach: for any fixed k ≥ 1, we can find m.
  -- And for m₀ large enough, the k computed from m₀ satisfies the log bounds.
  -- The key insight: once m₀ ≥ M₁ (fixing k), and m₀ ≥ M₂(k), we're done.
  -- Since both M₁ and M₂(k) are finite, we can take m₀ = max(M₁, M₂(k))
  -- for any specific m₀ that determines k.
  --
  -- Let me try a cleaner formulation:
  -- Pick some m₀₀ ≥ M₁. This determines k₀ = ⌊...⌋₊. 
  -- Get M₂ from exists_m_choose_dvd k₀.
  -- Set M₀ = max(m₀₀, M₂).
  -- For any m₀ ≥ M₀, we have m₀ ≥ m₀₀ ≥ M₁, so the k computed from m₀ 
  -- might differ from k₀. But we want to use k₀ (the k from m₀₀).
  -- Hmm, but then the log bounds are stated for k = ⌊(C+C')/2 * log(2*m₀)⌋₊,
  -- not k = k₀.
  --
  -- Actually, we should NOT fix k across different m₀. The statement says
  -- "for all m₀ large enough, ∃ m, k". The k can depend on m₀.
  -- But to get M₀ independent of m₀, we need a uniform bound.
  --
  -- The solution: we don't need to find M₀ independent of k!
  -- exists_m_choose_dvd gives, for EACH k, a threshold M₀(k).
  -- log_gap_bounds gives M₁ for k to be ≥ 1 and in the right range.
  -- The combined threshold is: m₀ should be ≥ M₁ AND ≥ M₀(k(m₀)).
  -- Since k(m₀) = O(log m₀) and M₀(k) is some function of k,
  -- for m₀ large enough both hold.
  --
  -- For Lean, the cleanest approach: define a function that,
  -- given m₀, picks k and checks if both conditions are met.
  -- Then show that for m₀ large enough, it works.
  -- But this requires showing that M₀(k) grows slower than m₀,
  -- which is a real analysis argument.
  --
  -- Alternative: reformulate exists_m_choose_dvd to take k as a function of m₀
  -- and have a SINGLE threshold. Or, use the bound from the task description:
  -- m₀ > (π(2k))^40. Since k = O(log m₀), π(2k) = O(log m₀ / log log m₀),
  -- so (π(2k))^40 = o(m₀). Hence for m₀ large enough, this holds.
  --
  -- For now, let me sorry this and focus on getting the overall structure right.
  sorry

theorem erdos_728 :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ C > (0 : ℝ), ∀ C' > C,
      ∃ a b n : ℕ,
        0 < n ∧
        ε * n < a ∧
        ε * n < b ∧
        a ! * b ! ∣ n ! * (a + b - n)! ∧
        a + b > n + C * Real.log n ∧
        a + b < n + C' * Real.log n := by
  rw [eventually_nhdsWithin_iff]
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨Set.Ioo (-1) (1/4), Ioo_mem_nhds (by norm_num) (by norm_num), ?_⟩
  intro ε hε _
  intro C hC C' hCC'
  obtain ⟨M₀, hM₀⟩ := exists_good_m C C' hC hCC'
  set m₀ := max M₀ 1
  obtain ⟨m, k, hm_lb, hm_ub, hk, hdvd, hk_lb, hk_ub⟩ := hM₀ m₀ (le_max_left _ _)
  refine ⟨m, m + k, 2 * m, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- 0 < 2 * m 
    have : 1 ≤ m₀ := le_max_right M₀ 1; omega
  · -- ε * (2 * m) < m
    have hm_pos : (0 : ℝ) < m := by
      have : 1 ≤ m₀ := le_max_right M₀ 1; exact_mod_cast show 0 < m by omega
    push_cast; nlinarith [hε.2]
  · -- ε * (2 * m) < m + k
    have hm_pos : (0 : ℝ) < m := by
      have : 1 ≤ m₀ := le_max_right M₀ 1; exact_mod_cast show 0 < m by omega
    push_cast; nlinarith [hε.2, show (0 : ℝ) ≤ ↑k from Nat.cast_nonneg k]
  · -- m ! * (m + k) ! ∣ (2 * m) ! * k !
    rw [show m + (m + k) - 2 * m = k from by omega]
    exact (reduction_lemma m k).mp hdvd
  · -- (m + (m + k) : ℝ) > (2 * m : ℝ) + C * log(2 * m)
    push_cast; linarith [hk_lb]
  · -- (m + (m + k) : ℝ) < (2 * m : ℝ) + C' * log(2 * m)
    push_cast; linarith [hk_ub]

end Erdos728
EOF
lake env lean /tmp/test_decompose.lean 2>&1
```
The whole thing compiles. Now let me write the final version for `Basic.lean`, integrating the sorry'd helper lemmas cleanly:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_final.lean << 'EOF'
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
EOF
lake env lean /tmp/test_final.lean 2>&1
```
The proof compiles cleanly with only `sorry` warnings (no errors). The main theorem `erdos_728` is fully proven, modulo three helper lemmas that are sorry'd. Now let me write this to the actual file:
🛠️ **Executing tool: read**

🛠️ **Executing tool: write**

```bash
$ cd /home/jarred/code/erdos-728b && lake build 2>&1 | tail -20
```
Build succeeds. Let me verify the sorry count — previously there was 1 sorry (the whole theorem), now there are 3 (three helper lemmas), but the main theorem itself is fully proven:
```bash
$ cd /home/jarred/code/erdos-728b && grep -n "sorry" Erdos/Basic.lean Erdos/Lemmas.lean
```
3 sorry holes, all in helper lemmas. The main theorem `erdos_728` is fully proved (no sorry). Let me commit this:
```bash
$ cd /home/jarred/code/erdos-728b && git add -A && git commit -m "Prove erdos_728 main theorem modulo three helper lemmas

The main theorem is fully proved by:
1. Choosing ε < 1/4 (via nhdsWithin filter)
2. Using exists_good_m to get m, k with C(m+k,k) | C(2m,m) and log bounds
3. Setting a=m, b=m+k, n=2m and verifying all six conditions

Three sorry'd helper lemmas remain:
- exists_m_choose_dvd: core existence via carry dominance + counting/union bound
- log_gap_bounds: k = floor((C+C')/2 * log(2m₀)) satisfies gap constraints
- exists_good_m: combines the above two (needs threshold compatibility argument)

The reduction_lemma and carry_dominance from Lemmas.lean are used directly."
```
Now let me update the task status:
```bash
$ cd /home/jarred/code/erdos-728b && tm update erdos728b-ud3 --status "Main theorem proven! 3 sorry'd helper lemmas remain: exists_m_choose_dvd, log_gap_bounds, exists_good_m. Building succeeds." 2>/dev/null || true
```
Now let me try to close some of the sorry holes. The `exists_good_m` lemma should be provable from the other two, so let me try that next:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_good_m.lean << 'EOF'
import Mathlib
import Erdos.Lemmas

open Real Nat
open scoped Nat Topology

namespace Erdos728

-- Sorry'd dependencies
lemma exists_m_choose_dvd (k : ℕ) (hk : 1 ≤ k) :
    ∃ M₀ : ℕ, ∀ m₀ : ℕ, M₀ ≤ m₀ →
      ∃ m : ℕ, m₀ ≤ m ∧ m ≤ 2 * m₀ ∧ (m + k).choose k ∣ (2 * m).choose m := by
  sorry

lemma log_gap_bounds (C C' : ℝ) (hC : 0 < C) (hCC' : C < C') :
    ∃ M₀ : ℕ, ∀ m₀ : ℕ, M₀ ≤ m₀ →
      let k := ⌊(C + C') / 2 * Real.log (2 * ↑m₀)⌋₊
      1 ≤ k ∧
      ∀ m : ℕ, m₀ ≤ m → m ≤ 2 * m₀ →
        C * Real.log (2 * ↑m) < ↑k ∧
        (↑k : ℝ) < C' * Real.log (2 * ↑m) := by
  sorry

-- Now try to prove exists_good_m from the two above
-- The challenge: k depends on m₀, and exists_m_choose_dvd gives a threshold 
-- that depends on k.
-- 
-- Strategy: 
-- 1. Pick m₀_init ≥ M₁ (from log_gap_bounds). This gives k₀.
-- 2. Get M₂ from exists_m_choose_dvd k₀.
-- 3. Set M₀ = max(m₀_init, M₂).
-- 4. For any m₀ ≥ M₀:
--    - m₀ ≥ m₀_init ≥ M₁, so the k for m₀ is valid
--    - But k for m₀ might differ from k₀!
--    - However, k is monotone in m₀ (since log is monotone)
--    - So k(m₀) ≥ k₀ for m₀ ≥ m₀_init
--    - exists_m_choose_dvd needs to work for k(m₀), not just k₀
--
-- This approach doesn't work directly because exists_m_choose_dvd 
-- gives a separate threshold for each k.
--
-- Better approach: don't try to wire them together. Instead, 
-- prove exists_good_m directly using a combined argument.
-- OR, use a quantifier swap.
--
-- Cleanest Lean approach: For a given (C, C'), we can pick a SPECIFIC
-- large m₀ and show everything works. The ∃ M₀ statement just needs
-- us to exhibit one such threshold.
--
-- Let me try: obtain the M₁ from log_gap_bounds, pick m₀ = M₁,
-- get k from this, then get M₂ from exists_m_choose_dvd k,
-- then set M₀ = max(M₁, M₂).
-- For any m₀ ≥ M₀: we compute k' = ⌊...⌋₊ using m₀.
-- But we want to use the SAME k as we got for M₁.
-- Actually no — we want k to depend on m₀. That's the whole point.
--
-- The real issue: the lemma exists_m_choose_dvd works for a FIXED k,
-- but in the combined statement k varies with m₀.
--
-- The RIGHT approach: strengthen exists_m_choose_dvd to work for all k
-- simultaneously, or reformulate.
--
-- Actually, the simplest fix: exists_m_choose_dvd says for EACH k ≥ 1,
-- ∃ M₀(k), ∀ m₀ ≥ M₀(k), ... . The NL proof says M₀(k) grows 
-- polynomially in k (roughly k^40 or (π(2k))^40). Since k = O(log m₀),
-- M₀(k) = O((log m₀)^40) = o(m₀). So for m₀ large enough, m₀ ≥ M₀(k(m₀)).
--
-- This is a real analysis argument. Let me formalize it with a sorry on 
-- the growth rate, or find a simpler path.
--
-- Actually, here's the key insight: we DON'T need to use exists_m_choose_dvd
-- with varying k. We can use it with a FIXED k, and then observe that
-- log_gap_bounds works for that same fixed k if m₀ is in the right range.
--
-- Wait, but k = ⌊(C+C')/2 * log(2*m₀)⌋₊ changes with m₀. Unless we
-- fix k and then find the range of m₀ for which the log bounds hold for
-- that k... This is more natural!
--
-- New approach: Fix k ≥ 1. Then:
-- (a) exists_m_choose_dvd gives M₀(k): for m₀ ≥ M₀(k), ∃ m with divisibility.
-- (b) The log gap C * log(2m) < k < C' * log(2m) for m ∈ [m₀, 2m₀] 
--     is equivalent to roughly e^{k/C'} / 2 < m₀ < e^{k/C} / 2.
--     So for each k, there's a range of m₀ that works.
-- (c) If we can find k such that the range in (b) contains some m₀ ≥ M₀(k),
--     we're done.
--
-- Since the range in (b) grows exponentially in k while M₀(k) grows 
-- polynomially, this works for large k.
--
-- For the ∃ M₀ statement: we need to show ∀ m₀ ≥ M₀, ... . So we need
-- a single M₀ that works for ALL large m₀.
--
-- Hmm, this is getting circular again. Let me try a different formulation.

-- Alternative: Let me try to prove it directly using the sorry'd lemmas,
-- accepting that we need to handle the threshold compatibility manually.

-- The trick: exists_m_choose_dvd gives ∃ M₀, ∀ m₀ ≥ M₀, ... for EACH k.
-- We can compose by first getting k from m₀, then applying exists_m_choose_dvd.
-- But the ∃ M₀ in the conclusion must be independent of m₀.
-- 
-- Key realization: We need a UNIFORM version of exists_m_choose_dvd.
-- Something like: ∃ M₀, ∀ m₀ ≥ M₀, ∀ k with 1 ≤ k ≤ C' * log(2m₀),
-- ∃ m ∈ [m₀, 2m₀] with C(m+k,k) | C(2m,m).
--
-- This is actually what the NL proof proves! The threshold M₀ can be taken
-- independent of k (as long as k ≤ C' * log(2m₀)).

-- For now, let me sorry exists_good_m and focus on the other helpers.

end Erdos728
EOF
echo "Analysis complete"
```
The analysis shows that `exists_good_m` requires careful threshold management. Let me reformulate `exists_m_choose_dvd` to be more directly usable, and then try to close `exists_good_m`:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_good_m2.lean << 'EOF'
import Mathlib
import Erdos.Lemmas

open Real Nat
open scoped Nat Topology

namespace Erdos728

-- Let me try a cleaner version of exists_m_choose_dvd that's easier to compose
-- The key: the threshold M₀ can be taken as (2k+1)^40 or similar polynomial in k.

/-- Uniform existence: for all sufficiently large m₀, for ALL k with 
    1 ≤ k ≤ m₀, there exists m ∈ [m₀, 2m₀] with C(m+k,k) | C(2m,m). 
    
    The threshold is independent of k (as long as k ≤ m₀). -/
lemma exists_m_choose_dvd_uniform :
    ∃ M₀ : ℕ, ∀ m₀ : ℕ, M₀ ≤ m₀ → ∀ k : ℕ, 1 ≤ k → k ≤ m₀ →
      ∃ m : ℕ, m₀ ≤ m ∧ m ≤ 2 * m₀ ∧ (m + k).choose k ∣ (2 * m).choose m := by
  sorry

lemma log_gap_bounds (C C' : ℝ) (hC : 0 < C) (hCC' : C < C') :
    ∃ M₀ : ℕ, ∀ m₀ : ℕ, M₀ ≤ m₀ →
      let k := ⌊(C + C') / 2 * Real.log (2 * ↑m₀)⌋₊
      1 ≤ k ∧ k ≤ m₀ ∧
      ∀ m : ℕ, m₀ ≤ m → m ≤ 2 * m₀ →
        C * Real.log (2 * ↑m) < ↑k ∧
        (↑k : ℝ) < C' * Real.log (2 * ↑m) := by
  sorry

-- Now exists_good_m follows easily!
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

end Erdos728
EOF
lake env lean /tmp/test_good_m2.lean 2>&1
```
`exists_good_m` is now fully proven (no sorry) from the two helper lemmas! Let me update the main file with this improved decomposition:
🛠️ **Executing tool: write**

```bash
$ cd /home/jarred/code/erdos-728b && lake build 2>&1 | tail -10
```
Now we're down to **2 sorry holes** (from 3 before). The `exists_good_m` is fully proved. Let me commit:
```bash
$ cd /home/jarred/code/erdos-728b && git add -A && git commit -m "Reduce to 2 sorry holes: prove exists_good_m from uniform existence + log gap

Restructured the decomposition:
- exists_m_choose_dvd_uniform: uniform version (threshold independent of k)
- log_gap_bounds: k selection gives gap bounds and k ≤ m₀
- exists_good_m: now FULLY PROVEN from the above two (was sorry'd before)
- erdos_728: main theorem fully proven from exists_good_m

Remaining sorrys:
1. exists_m_choose_dvd_uniform (carry dominance + counting/union bound)
2. log_gap_bounds (real analysis: log monotonicity + floor bounds)"
```
Now let me try to tackle `log_gap_bounds`, which is the real analysis lemma. This should be more tractable:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_log.lean << 'EOF'
import Mathlib

open Real

-- Key facts about Real.log and Nat.floor
#check Real.log_le_log_of_le
#check Real.log_lt_log
#check Real.log_pos
#check Nat.floor_le
#check Nat.lt_floor_add_one
#check Nat.le_floor
#check Nat.sub_one_lt_floor
-- How does ⌊·⌋₊ work?
#check Nat.floor_eq_zero
#check Nat.one_le_floor_iff  -- probably doesn't exist
EOF
lake env lean /tmp/test_log.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_log2.lean << 'EOF'
import Mathlib

open Real

-- We need log_gap_bounds:
-- For 0 < C < C', for m₀ large enough,
-- let k = ⌊(C + C') / 2 * log(2 * m₀)⌋₊
-- Then: 1 ≤ k, k ≤ m₀, and for all m ∈ [m₀, 2m₀],
-- C * log(2m) < k < C' * log(2m).

-- Key facts:
-- 1. k ≥ 1: Need (C+C')/2 * log(2m₀) ≥ 1, i.e., m₀ ≥ exp(2/(C+C'))/2
-- 2. k ≤ m₀: Need (C+C')/2 * log(2m₀) ≤ m₀, which holds for large m₀
-- 3. Upper bound: k < C' * log(2m) for m ≥ m₀
--    k ≤ (C+C')/2 * log(2m₀) ≤ (C+C')/2 * log(2m) < C' * log(2m)
--    since (C+C')/2 < C' (as C < C')
-- 4. Lower bound: k > C * log(2m) for m ≤ 2m₀
--    k ≥ (C+C')/2 * log(2m₀) - 1
--    We need this > C * log(2*2m₀) = C * log(4m₀)
--    = C * (log(2m₀) + log 2)
--    So need ((C+C')/2 - C) * log(2m₀) > 1 + C * log 2
--    i.e., (C'-C)/2 * log(2m₀) > 1 + C * log 2
--    which holds for large m₀.

-- Let me try to prove this step by step.

-- First, some basic facts
#check Real.log_le_log
#check Real.log_le_log_of_le  -- doesn't exist
#check Real.log_lt_log
#check Real.log_le_log
-- #check Real.log_nonneg -- check if this exists
#check Real.log_natCast_nonneg  -- probably doesn't exist

-- What about monotonicity?
example (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) : Real.log x ≤ Real.log y := by
  exact Real.log_le_log hx hxy

-- Nat.floor properties
-- ⌊a⌋₊ ≤ a  (for a ≥ 0)
-- a < ⌊a⌋₊ + 1
-- n ≤ ⌊a⌋₊ ↔ (n : ℝ) ≤ a  (for a ∈ something)
-- a - 1 < ⌊a⌋₊

example (a : ℝ) (ha : 1 ≤ a) : 1 ≤ ⌊a⌋₊ := by
  rwa [Nat.one_le_floor_iff]

-- Good. Now let me try the upper bound:
-- k = ⌊(C+C')/2 * log(2*m₀)⌋₊
-- k ≤ (C+C')/2 * log(2*m₀)  (by Nat.floor_le)
-- For m ≥ m₀: log(2*m) ≥ log(2*m₀)  (by monotonicity)
-- So (C+C')/2 * log(2*m₀) ≤ (C+C')/2 * log(2*m)
-- And (C+C')/2 < C'
-- So k ≤ (C+C')/2 * log(2*m) < C' * log(2*m)

-- For the lower bound:
-- k ≥ (C+C')/2 * log(2*m₀) - 1  (by Nat.sub_one_lt_floor)
-- For m ≤ 2*m₀: log(2*m) ≤ log(4*m₀) = log(2*m₀) + log(2)
-- We need k > C * log(2*m)
-- k ≥ (C+C')/2 * log(2*m₀) - 1
-- C * log(2*m) ≤ C * (log(2*m₀) + log 2)
-- Need: (C+C')/2 * log(2*m₀) - 1 > C * log(2*m₀) + C * log 2
-- ↔ ((C+C')/2 - C) * log(2*m₀) > 1 + C * log 2
-- ↔ (C'-C)/2 * log(2*m₀) > 1 + C * log 2
-- This holds when log(2*m₀) > 2*(1 + C*log 2)/(C'-C)
-- i.e., m₀ > exp(2*(1 + C*log 2)/(C'-C))/2

-- Great! Let me try to formalize this.

-- But wait, we also need k ≤ m₀
-- k ≤ (C+C')/2 * log(2*m₀)
-- We need log(2*m₀) ≤ 2*m₀/(C+C'), i.e., (C+C')/2 * log(2*m₀) ≤ m₀
-- Since log grows slower than linear, this holds for m₀ large enough.

-- This requires showing log(x) ≤ x eventually.
#check Real.add_one_le_exp
#check Real.log_le_sub_one_of_le

-- Let me try a concrete approach
example (x : ℝ) (hx : 1 ≤ x) : Real.log x ≤ x := by
  have h1 : Real.log x ≤ x - 1 := by
    rw [← Real.log_exp (x - 1)]
    apply Real.log_le_log (exp_pos _).le
    linarith [Real.add_one_le_exp (x - 1)]
  linarith

EOF
lake env lean /tmp/test_log2.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_log3.lean << 'EOF'
import Mathlib

open Real

-- log x ≤ x for x ≥ 1
lemma log_le_self {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ x := by
  have h1 : Real.log x ≤ x - 1 := by
    have hx0 : 0 < x := by linarith
    calc Real.log x = Real.log x := rfl
    _ ≤ x - 1 := by
        rw [← Real.log_exp (x - 1)]
        exact Real.log_le_log (exp_pos _) (by linarith [Real.add_one_le_exp (x - 1)])
  linarith

-- log(2x) ≤ 2x for x ≥ 1
lemma log_two_mul_le {x : ℝ} (hx : 1 ≤ x) : Real.log (2 * x) ≤ 2 * x := by
  have : 1 ≤ 2 * x := by linarith
  calc Real.log (2 * x) ≤ 2 * x := log_le_self this

-- Now test: for large m₀, (C+C')/2 * log(2*m₀) ≤ m₀
-- Equivalently, log(2*m₀) ≤ 2*m₀/(C+C')
-- Since log(2*m₀) ≤ 2*m₀ (by above), we need 2*m₀ ≤ 2*m₀/(C+C') only when C+C' ≤ 1
-- In general we need a sharper bound. Let's use: for any A > 0, log(x) ≤ x/A for x ≥ e^A.

-- Actually, we just need: (C+C')/2 * log(2m₀) ≤ m₀
-- This is: log(2m₀) ≤ 2m₀/(C+C')  
-- For A = (C+C'): log(x) ≤ x/A when x ≥ something
-- Since log(x)/x → 0, this holds eventually.

-- Let me use Filter.Eventually and tendsto to handle "for large m₀"

-- Actually for Lean, the cleanest approach might be to use Nat.find or 
-- just show existence of a suitable M₀.

-- Let me try a more direct approach using Filter.Tendsto

-- The key: we need to show that for m₀ sufficiently large, several 
-- conditions hold simultaneously. Each condition has the form "f(m₀) ≥ g(m₀)"
-- where f grows faster than g.

-- Actually, let me try to use the "eventually" filter for ℕ.

#check Filter.atTop
#check Filter.Eventually
#check Filter.eventually_atTop

-- For m₀ → ∞ in ℕ:
-- (1) (C+C')/2 * log(2*m₀) ≥ 1 — eventually (log → ∞)
-- (2) (C'-C)/2 * log(2*m₀) > 1 + C * log 2 — eventually  
-- (3) (C+C')/2 * log(2*m₀) ≤ m₀ — eventually (log/x → 0)

-- Each of these is provable using Filter.Tendsto and properties of log.

-- Strategy: prove each condition is eventually true, then take the max of thresholds.

-- Let me try condition (1): (C+C')/2 * log(2 * m₀) ≥ 1
-- This is: log(2 * m₀) ≥ 2/(C+C')
-- Since log is unbounded, this holds for m₀ large.

#check Filter.Tendsto.eventually_ge_atTop  
-- Hmm, probably doesn't exist. Let me check what's available.

-- The cleanest approach for "eventually" on ℕ is Filter.eventually_atTop:
-- (∀ᶠ n in atTop, P n) ↔ ∃ N, ∀ n ≥ N, P n

-- And we can show things like: ∀ᶠ n in atTop, Real.log n ≥ c
-- using the fact that log is monotone and unbounded.

-- For a concrete bound, we can use Nat.ceil
-- e.g., M₀ = ⌈exp(2/(C+C'))/2⌉₊ + 1 works for condition (1)

-- This is getting quite involved. Let me try to write the full proof.
EOF
lake env lean /tmp/test_log3.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_log4.lean << 'EOF'
import Mathlib
open Real

-- Fix the log_le_self proof
lemma log_le_self {x : ℝ} (hx : 1 ≤ x) : log x ≤ x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have h1 : log x ≤ x - 1 := by
    have := Real.add_one_le_exp (x - 1)
    -- exp(x-1) ≥ x, so log(x) ≤ log(exp(x-1)) = x-1... wait
    -- Actually log x ≤ x - 1 is equivalent to exp(log x) ≤ exp(x-1)
    -- i.e., x ≤ exp(x-1), which follows from add_one_le_exp with x-1
    -- since (x-1) + 1 ≤ exp(x-1), i.e., x ≤ exp(x-1)
    calc log x ≤ log (exp (x - 1)) := by
          apply log_le_log hx0
          linarith
        _ = x - 1 := log_exp (x - 1)
  linarith

-- Now let me try the full log_gap_bounds

-- We need:
-- Given C, C' with 0 < C < C', find M₀ such that for m₀ ≥ M₀,
-- k := ⌊(C+C')/2 * log(2*m₀)⌋₊ satisfies:
-- (a) 1 ≤ k
-- (b) k ≤ m₀  
-- (c) For m ∈ [m₀, 2m₀]: C * log(2m) < k
-- (d) For m ∈ [m₀, 2m₀]: k < C' * log(2m)

-- Let me prove each condition separately and then combine.

-- Helper: log(2*n) is monotone in n for n ≥ 1
lemma log_two_mul_nat_mono {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    log (2 * (a : ℝ)) ≤ log (2 * (b : ℝ)) := by
  apply log_le_log
  · positivity
  · exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hab) (by norm_num)

-- (d) is the easiest: k ≤ (C+C')/2 * log(2m₀) ≤ (C+C')/2 * log(2m) < C' * log(2m)
-- since (C+C')/2 < C' and log(2m) ≥ log(2m₀) > 0

-- (c) is: k ≥ (C+C')/2 * log(2m₀) - 1 > C * log(2m)
-- For m ≤ 2m₀: log(2m) ≤ log(4m₀)
-- Need: (C+C')/2 * log(2m₀) - 1 > C * log(4m₀)
-- = C * (log(2m₀) + log 2)
-- = C * log(2m₀) + C * log 2
-- So: ((C+C')/2 - C) * log(2m₀) > 1 + C * log 2
-- i.e., (C'-C)/2 * log(2m₀) > 1 + C * log 2

-- Let me try to prove (d) and (c) together
-- For m ∈ [m₀, 2m₀] with m₀ large:

-- Let avg := (C + C') / 2
-- k := ⌊avg * log(2m₀)⌋₊
-- Then: avg * log(2m₀) - 1 < k ≤ avg * log(2m₀)

-- (d): k ≤ avg * log(2m₀) ≤ avg * log(2m) < C' * log(2m)
-- since avg < C' and log(2m) > 0 (for m ≥ 1)

-- (c): k > avg * log(2m₀) - 1
-- Need: avg * log(2m₀) - 1 ≥ C * log(2m)
-- For m ≤ 2m₀: log(2m) ≤ log(4m₀) = log(2m₀) + log(2)
-- So: C * log(2m) ≤ C * log(2m₀) + C * log(2)
-- Need: avg * log(2m₀) - 1 ≥ C * log(2m₀) + C * log(2)
-- i.e., (avg - C) * log(2m₀) ≥ 1 + C * log(2)
-- i.e., (C'-C)/2 * log(2m₀) ≥ 1 + C * log(2)
-- i.e., log(2m₀) ≥ 2*(1 + C*log 2)/(C'-C)

-- Let me try proving it

EOF
lake env lean /tmp/test_log4.lean 2>&1
```
Good, the helper lemmas compile. Now let me write the full `log_gap_bounds` proof:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_lgb.lean << 'EOF'
import Mathlib
import Erdos.Lemmas

open Real Nat
open scoped Nat Topology

namespace Erdos728

/-- log x ≤ x for x ≥ 1 -/
private lemma log_le_self' {x : ℝ} (hx : 1 ≤ x) : log x ≤ x := by
  have hx0 : (0 : ℝ) < x := by linarith
  calc log x ≤ log (exp (x - 1)) := by
        apply log_le_log hx0; linarith [Real.add_one_le_exp (x - 1)]
      _ = x - 1 := log_exp (x - 1)
      _ ≤ x := by linarith

/-- For m₀ sufficiently large, (C+C')/2 * log(2m₀) ≤ m₀ -/
private lemma log_bound_le_linear (C C' : ℝ) (hC : 0 < C) (hCC' : C < C') :
    ∃ M₀ : ℕ, ∀ m₀ : ℕ, M₀ ≤ m₀ →
      (C + C') / 2 * log (2 * ↑m₀) ≤ ↑m₀ := by
  -- For m₀ ≥ 1: log(2*m₀) ≤ 2*m₀ (by log_le_self')
  -- So (C+C')/2 * log(2*m₀) ≤ (C+C')/2 * 2*m₀ = (C+C') * m₀
  -- We need this ≤ m₀, which requires (C+C') ≤ 1. That's NOT always true!
  -- 
  -- Better: use log(x) ≤ x/A for x large enough (depending on A).
  -- Or: for any A > 0, ∃ N, ∀ x ≥ N, A * log(x) ≤ x.
  -- This follows from lim_{x→∞} log(x)/x = 0.
  --
  -- In Lean, use Filter.Tendsto
  sorry

lemma log_gap_bounds (C C' : ℝ) (hC : 0 < C) (hCC' : C < C') :
    ∃ M₀ : ℕ, ∀ m₀ : ℕ, M₀ ≤ m₀ →
      let k := ⌊(C + C') / 2 * log (2 * ↑m₀)⌋₊
      1 ≤ k ∧ k ≤ m₀ ∧
      ∀ m : ℕ, m₀ ≤ m → m ≤ 2 * m₀ →
        C * log (2 * ↑m) < ↑k ∧
        (↑k : ℝ) < C' * log (2 * ↑m) := by
  sorry

end Erdos728
EOF
lake env lean /tmp/test_lgb.lean 2>&1
```
Need to disambiguate `log`. Let me use `Real.log` explicitly:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_lgb2.lean << 'EOF'
import Mathlib
import Erdos.Lemmas

open Nat
open scoped Nat Topology

namespace Erdos728

/-- log x ≤ x for x ≥ 1 -/
private lemma log_le_self' {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ x := by
  have hx0 : (0 : ℝ) < x := by linarith
  calc Real.log x ≤ Real.log (Real.exp (x - 1)) := by
        apply Real.log_le_log hx0; linarith [Real.add_one_le_exp (x - 1)]
      _ = x - 1 := Real.log_exp (x - 1)
      _ ≤ x := by linarith

-- For the k ≤ m₀ bound, we need: A * log(x) ≤ x for large x.
-- This is equivalent to log(x) ≤ x/A.
-- Use: log(x) ≤ 2*sqrt(x) for x ≥ 1 (since log(x) ≤ x-1 ≤ x).
-- Actually, we can use the fact that log(x)/x → 0 from Mathlib.

-- Let me check what tendsto results are available
#check Real.tendsto_log_comp_rpow_atTop  -- might not exist
-- #check Real.tendsto_div_pow_mul_atTop_atTop  -- might not exist

-- Actually, for our purposes, a crude bound suffices.
-- We need: (C+C')/2 * log(2*m₀) ≤ m₀
-- Since log(x) ≤ x for x ≥ 1:
-- (C+C')/2 * log(2*m₀) ≤ (C+C')/2 * (2*m₀) = (C+C') * m₀
-- This is ≤ m₀ only if C+C' ≤ 1.
-- For general C, C', we need a sharper bound.

-- Better: log(x) ≤ sqrt(x) for x ≥ ... Let me use exp/log properties.
-- For any A > 0: A * log(x) ≤ x ↔ log(x^A) ≤ x ↔ x^A ≤ exp(x)
-- This holds for large x by exp growing faster than any polynomial.

-- In Mathlib, we should have something like:
#check Real.tendsto_pow_mul_exp_neg_atTop_nhds -- probably not the name
-- Let me search for "log atTop" or "exp atTop"

-- Actually let me just try a direct approach: prove log(x) ≤ sqrt(x) for x ≥ 1
-- Then A * log(2m₀) ≤ A * sqrt(2m₀) ≤ m₀ for m₀ ≥ 2A²

-- log(x) ≤ sqrt(x) for x ≥ 1 because:
-- Let y = sqrt(x), so x = y², and log(x) = 2*log(y) ≤ 2*(y-1) ≤ 2*y ≤ y² = x for y ≥ 2
-- Wait, that gives log(x) ≤ x, not sqrt(x).

-- Hmm, log(x) ≤ sqrt(x):
-- exp(sqrt(x)) ≥ 1 + sqrt(x) + sqrt(x)²/2 = 1 + sqrt(x) + x/2 ≥ x for x ≥ 2
-- So log(x) ≤ sqrt(x) for x ≥ 2... not quite clean.

-- Let me try another approach: use log(x) ≤ 2*(sqrt(x) - 1) for x ≥ 1
-- This follows from: for t ≥ 0, t ≤ 2*(exp(t/2) - 1), i.e., exp(t/2) ≥ 1 + t/2
-- which is add_one_le_exp.
-- So log(x) ≤ 2*(sqrt(x) - 1) < 2*sqrt(x)

-- Then: (C+C')/2 * log(2*m₀) ≤ (C+C') * sqrt(2*m₀)
-- We need (C+C') * sqrt(2*m₀) ≤ m₀, i.e., sqrt(2*m₀) ≤ m₀/(C+C')
-- i.e., 2*m₀ ≤ m₀²/(C+C')², i.e., m₀ ≥ 2*(C+C')²

-- Great! So M₀ = ⌈2*(C+C')²⌉₊ + 1 works (roughly).

-- Actually let me try a simpler approach:
-- log(x) ≤ x for all x ≥ 1 (we proved this above)
-- So for n : ℕ, log(2n) ≤ 2n
-- And (C+C')/2 * log(2n) ≤ (C+C')/2 * 2n = (C+C') * n
-- We need (C+C') * n ≤ n, but that fails when C+C' > 1.

-- Let me try the sqrt route.
-- log(x) ≤ 2*(x^(1/2) - 1) for x ≥ 1
-- This is: log(x)/2 ≤ x^(1/2) - 1
-- Set u = x^(1/2) - 1, x = (u+1)², so log(x) = 2*log(u+1) ≤ 2*u
-- Need: log(u+1) ≤ u for u ≥ 0
-- This follows from log_le_self' with x = u+1 ≥ 1: log(u+1) ≤ u+1
-- Hmm, that gives log(u+1) ≤ u+1, not log(u+1) ≤ u.
-- Actually log(x) ≤ x - 1 for x ≥ 1 (which we showed): log(u+1) ≤ u. ✓

-- So: log(x) = 2*log(sqrt(x)) ≤ 2*(sqrt(x) - 1) < 2*sqrt(x) for x ≥ 1

-- Let me verify this in Lean
lemma log_le_two_sqrt {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hsx : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsx1 : 1 ≤ Real.sqrt x := by
    rwa [← Real.sqrt_one, Real.sqrt_le_sqrt (by norm_num : (0 : ℝ) ≤ 1)]
  calc Real.log x = Real.log (Real.sqrt x ^ 2) := by
          rw [Real.sq_sqrt (by linarith : 0 ≤ x)]
        _ = 2 * Real.log (Real.sqrt x) := by
          rw [Real.log_pow]
          ring
        _ ≤ 2 * (Real.sqrt x - 1) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
          calc Real.log (Real.sqrt x) 
              ≤ Real.log (Real.exp (Real.sqrt x - 1)) := by
                apply Real.log_le_log (by positivity)
                linarith [Real.add_one_le_exp (Real.sqrt x - 1)]
            _ = Real.sqrt x - 1 := Real.log_exp _
        _ ≤ 2 * Real.sqrt x := by linarith

-- Now: (C+C')/2 * log(2*m₀) ≤ (C+C')/2 * 2*sqrt(2*m₀) = (C+C') * sqrt(2*m₀)
-- For m₀ ≥ 2*(C+C')², we have sqrt(2*m₀) ≤ m₀/(C+C'), so the bound ≤ m₀

end Erdos728
EOF
lake env lean /tmp/test_lgb2.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_lgb3.lean << 'EOF'
import Mathlib
open Real

-- Fix the sqrt monotonicity
example (x : ℝ) (hx : 1 ≤ x) : 1 ≤ Real.sqrt x := by
  rw [← Real.sqrt_one]
  exact Real.sqrt_le_sqrt (by linarith : 0 ≤ 1) (by linarith)

-- Wait, sqrt_le_sqrt might have different args
#check @Real.sqrt_le_sqrt
EOF
lake env lean /tmp/test_lgb3.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_lgb4.lean << 'EOF'
import Mathlib
open Real

-- sqrt_le_sqrt only takes one arg (implicit x y, explicit h : x ≤ y)
example (x : ℝ) (hx : 1 ≤ x) : 1 ≤ Real.sqrt x := by
  rw [← Real.sqrt_one]
  exact Real.sqrt_le_sqrt (by linarith)

-- log x ≤ x - 1 for x ≥ 1
lemma log_le_sub_one {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ x - 1 := by
  calc Real.log x ≤ Real.log (Real.exp (x - 1)) := by
        apply Real.log_le_log (by linarith : 0 < x)
        linarith [Real.add_one_le_exp (x - 1)]
      _ = x - 1 := Real.log_exp (x - 1)

-- log(x) ≤ 2 * sqrt(x) for x ≥ 1
lemma log_le_two_sqrt {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hsx : 1 ≤ Real.sqrt x := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith)
  calc Real.log x = Real.log (Real.sqrt x ^ 2) := by
          rw [Real.sq_sqrt (by linarith : 0 ≤ x)]
        _ = 2 * Real.log (Real.sqrt x) := by rw [Real.log_pow]; ring
        _ ≤ 2 * (Real.sqrt x - 1) := by
          apply mul_le_mul_of_nonneg_left (log_le_sub_one hsx) (by norm_num)
        _ ≤ 2 * Real.sqrt x := by linarith
EOF
lake env lean /tmp/test_lgb4.lean 2>&1
```
Now let me build the full `log_gap_bounds` proof. This is quite involved, so let me plan carefully:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_lgb5.lean << 'EOF'
import Mathlib
import Erdos.Lemmas

open Nat
open scoped Nat Topology

namespace Erdos728

private lemma log_le_sub_one {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ x - 1 := by
  calc Real.log x ≤ Real.log (Real.exp (x - 1)) := by
        apply Real.log_le_log (by linarith : 0 < x)
        linarith [Real.add_one_le_exp (x - 1)]
      _ = x - 1 := Real.log_exp (x - 1)

private lemma log_le_two_sqrt {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hsx : 1 ≤ Real.sqrt x := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith)
  calc Real.log x = Real.log (Real.sqrt x ^ 2) := by
          rw [Real.sq_sqrt (by linarith : 0 ≤ x)]
        _ = 2 * Real.log (Real.sqrt x) := by rw [Real.log_pow]; ring
        _ ≤ 2 * (Real.sqrt x - 1) := by
          apply mul_le_mul_of_nonneg_left (log_le_sub_one hsx) (by norm_num)
        _ ≤ 2 * Real.sqrt x := by linarith

lemma log_gap_bounds (C C' : ℝ) (hC : 0 < C) (hCC' : C < C') :
    ∃ M₀ : ℕ, ∀ m₀ : ℕ, M₀ ≤ m₀ →
      let k := ⌊(C + C') / 2 * Real.log (2 * ↑m₀)⌋₊
      1 ≤ k ∧ k ≤ m₀ ∧
      ∀ m : ℕ, m₀ ≤ m → m ≤ 2 * m₀ →
        C * Real.log (2 * ↑m) < ↑k ∧
        (↑k : ℝ) < C' * Real.log (2 * ↑m) := by
  -- Set avg := (C + C') / 2. We have C < avg < C'.
  set avg := (C + C') / 2 with avg_def
  have hC_avg : C < avg := by linarith
  have havg_C' : avg < C' := by linarith
  have havg_pos : 0 < avg := by linarith
  -- We need m₀ large enough for three conditions.
  -- Let L₀ = max of:
  --   (a) log(2m₀) ≥ 1/avg  (ensures k ≥ 1)
  --   (b) log(2m₀) ≥ (2 + 2*C*Real.log 2)/(C'-C)  (ensures lower bound)
  --   (c) avg * log(2m₀) ≤ m₀  (ensures k ≤ m₀)
  -- 
  -- For (a) and (b): m₀ ≥ exp(max(1/avg, ...)) / 2 suffices.
  -- For (c): avg * 2*sqrt(2*m₀) ≤ m₀, so m₀ ≥ 8*avg² suffices
  --
  -- All conditions hold for m₀ large enough. 
  -- For a clean proof, use Filter.eventually_atTop.
  sorry

end Erdos728
EOF
lake env lean /tmp/test_lgb5.lean 2>&1
```
The `log_gap_bounds` proof is quite technical — it requires constructing explicit thresholds for log-based conditions. Let me try a different approach: construct the threshold explicitly and verify each condition:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_lgb6.lean << 'EOF'
import Mathlib
import Erdos.Lemmas

open Nat
open scoped Nat Topology

namespace Erdos728

private lemma log_le_sub_one {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ x - 1 := by
  calc Real.log x ≤ Real.log (Real.exp (x - 1)) := by
        apply Real.log_le_log (by linarith : 0 < x)
        linarith [Real.add_one_le_exp (x - 1)]
      _ = x - 1 := Real.log_exp (x - 1)

private lemma log_le_two_sqrt {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hsx : 1 ≤ Real.sqrt x := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith)
  calc Real.log x = Real.log (Real.sqrt x ^ 2) := by
          rw [Real.sq_sqrt (by linarith : 0 ≤ x)]
        _ = 2 * Real.log (Real.sqrt x) := by rw [Real.log_pow]; ring
        _ ≤ 2 * (Real.sqrt x - 1) := by
          apply mul_le_mul_of_nonneg_left (log_le_sub_one hsx) (by norm_num)
        _ ≤ 2 * Real.sqrt x := by linarith

-- Step 1: For m₀ large enough, avg * log(2*m₀) ≥ 1
-- This means log(2*m₀) ≥ 1/avg, i.e., 2*m₀ ≥ exp(1/avg)
-- Sufficient: m₀ ≥ ⌈exp(1/avg)/2⌉₊

-- Step 2: For m₀ large enough, (C'-C)/2 * log(2*m₀) ≥ 1 + C * log(2) + 1
-- (the extra +1 handles the floor)
-- This means log(2*m₀) ≥ (2 + C*log 2 + 1)*2/(C'-C)  
-- (more margin than needed but fine)

-- Step 3: For m₀ large enough, avg * log(2*m₀) ≤ m₀
-- Using log(2*m₀) ≤ 2*sqrt(2*m₀), sufficient: avg * 2*sqrt(2*m₀) ≤ m₀
-- i.e., 4*avg²*2*m₀ ≤ m₀², i.e., m₀ ≥ 8*avg²

-- Let me try the proof using Filter.eventually_atTop to avoid explicit bounds
-- and just show each condition holds eventually.

-- Actually, for the ∃ M₀ statement, the cleanest Lean approach is to use
-- Nat.find on the conjunction of eventually-true conditions.

-- Even cleaner: show each condition is ∀ᶠ n in atTop and combine.

-- Let me try:
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
  have hgap : 0 < C' - C := by linarith
  -- Condition 1: avg * log(2m₀) ≥ 1 (ensures k ≥ 1)
  -- Condition 2: (avg - C) * log(2m₀) ≥ 2 + C * log 2 (ensures lower bound)
  -- Condition 3: avg * log(2m₀) ≤ m₀ (ensures k ≤ m₀)
  -- Condition 4: m₀ ≥ 1 (ensures log(2m₀) > 0)
  -- 
  -- Use: all conditions are eventually true (∀ᶠ in atTop), 
  -- combine using Filter.Eventually.and, then extract via eventually_atTop.
  rw [← Filter.eventually_atTop]
  -- Show each condition is eventually true
  -- Cond 1: ∀ᶠ m₀ in atTop, avg * Real.log (2 * ↑m₀) ≥ 1
  have cond1 : ∀ᶠ m₀ : ℕ in Filter.atTop, 1 ≤ avg * Real.log (2 * ↑m₀) := by
    sorry -- log → ∞
  -- Cond 2: ∀ᶠ m₀ in atTop, (avg-C) * log(2m₀) ≥ 2 + C*log 2
  have cond2 : ∀ᶠ m₀ : ℕ in Filter.atTop, 
      2 + C * Real.log 2 ≤ (avg - C) * Real.log (2 * ↑m₀) := by
    sorry -- log → ∞
  -- Cond 3: ∀ᶠ m₀ in atTop, avg * log(2m₀) ≤ m₀
  have cond3 : ∀ᶠ m₀ : ℕ in Filter.atTop, avg * Real.log (2 * ↑m₀) ≤ ↑m₀ := by
    sorry -- log/x → 0
  -- Cond 4: m₀ ≥ 1
  have cond4 : ∀ᶠ m₀ : ℕ in Filter.atTop, 1 ≤ m₀ := by
    exact Filter.eventually_atTop.mpr ⟨1, fun _ h => h⟩
  -- Combine and extract
  have combined := cond1.and (cond2.and (cond3.and cond4))
  rw [Filter.eventually_atTop] at combined
  obtain ⟨N, hN⟩ := combined
  refine ⟨N, fun m₀ hm₀ => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hN m₀ hm₀
  constructor
  · -- 1 ≤ k
    rw [Nat.one_le_floor_iff]
    exact h1
  constructor
  · -- k ≤ m₀
    rw [Nat.le_floor_iff (by positivity)] at *
    exact le_trans (Nat.floor_le (by positivity)) (by exact_mod_cast h3)
    sorry
  · -- Gap bounds for all m ∈ [m₀, 2m₀]
    intro m hm_lb hm_ub
    have hm_pos : (0 : ℝ) < m := by exact_mod_cast show 0 < m by omega
    have hm₀_pos : (0 : ℝ) < m₀ := by exact_mod_cast show 0 < m₀ by omega
    -- Upper bound: k ≤ avg * log(2m₀) ≤ avg * log(2m) < C' * log(2m)
    -- Lower bound: k ≥ avg * log(2m₀) - 1 > C * log(2m)
    constructor
    · -- C * log(2m) < k
      -- k > avg * log(2m₀) - 1
      -- log(2m) ≤ log(4m₀) = log(2m₀) + log 2
      -- C * log(2m) ≤ C * (log(2m₀) + log 2) = C * log(2m₀) + C * log 2
      -- avg * log(2m₀) - 1 ≥ C * log(2m₀) + (avg-C) * log(2m₀) - 1
      -- = C * log(2m₀) + (avg-C)*log(2m₀) - 1
      -- By cond2: (avg-C)*log(2m₀) ≥ 2 + C*log 2
      -- So avg * log(2m₀) - 1 ≥ C * log(2m₀) + 1 + C*log 2 ≥ C*log(2m) + 1
      sorry
    · -- k < C' * log(2m)
      -- k ≤ avg * log(2m₀)
      -- For m ≥ m₀: log(2m) ≥ log(2m₀)
      -- avg * log(2m₀) ≤ avg * log(2m) < C' * log(2m) (since avg < C' and log > 0)
      sorry

end Erdos728
EOF
lake env lean /tmp/test_lgb6.lean 2>&1
```
I need to handle the filter differently. Let me not use `rw [← Filter.eventually_atTop]` at the top level:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_lgb7.lean << 'EOF'
import Mathlib
import Erdos.Lemmas

open Nat
open scoped Nat Topology

namespace Erdos728

private lemma log_le_sub_one {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ x - 1 := by
  calc Real.log x ≤ Real.log (Real.exp (x - 1)) := by
        apply Real.log_le_log (by linarith : 0 < x)
        linarith [Real.add_one_le_exp (x - 1)]
      _ = x - 1 := Real.log_exp (x - 1)

private lemma log_le_two_sqrt {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hsx : 1 ≤ Real.sqrt x := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith)
  calc Real.log x = Real.log (Real.sqrt x ^ 2) := by
          rw [Real.sq_sqrt (by linarith : 0 ≤ x)]
        _ = 2 * Real.log (Real.sqrt x) := by rw [Real.log_pow]; ring
        _ ≤ 2 * (Real.sqrt x - 1) := by
          apply mul_le_mul_of_nonneg_left (log_le_sub_one hsx) (by norm_num)
        _ ≤ 2 * Real.sqrt x := by linarith

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
  -- Each sub-condition is eventually true, combine via Filter.eventually_atTop
  have cond1 : ∀ᶠ m₀ : ℕ in Filter.atTop, 1 ≤ avg * Real.log (2 * ↑m₀) := by sorry
  have cond2 : ∀ᶠ m₀ : ℕ in Filter.atTop, 
      2 + C * Real.log 2 ≤ (avg - C) * Real.log (2 * ↑m₀) := by sorry
  have cond3 : ∀ᶠ m₀ : ℕ in Filter.atTop, avg * Real.log (2 * ↑m₀) ≤ ↑m₀ := by sorry
  have cond4 : ∀ᶠ m₀ : ℕ in Filter.atTop, (1 : ℕ) ≤ m₀ := by
    exact Filter.eventually_atTop.mpr ⟨1, fun _ h => h⟩
  -- Combine
  have combined := cond1.and (cond2.and (cond3.and cond4))
  rw [Filter.eventually_atTop] at combined
  obtain ⟨N, hN⟩ := combined
  refine ⟨N, fun m₀ hm₀ => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hN m₀ hm₀
  set k := ⌊avg * Real.log (2 * ↑m₀)⌋₊ with k_def
  have hm₀_pos : (0 : ℝ) < (m₀ : ℝ) := by exact_mod_cast show 0 < m₀ by omega
  have h2m₀_pos : (0 : ℝ) < 2 * (m₀ : ℝ) := by linarith
  have hlog_pos : 0 < Real.log (2 * ↑m₀) := Real.log_pos (by linarith)
  -- k properties from floor
  have hk_le : (k : ℝ) ≤ avg * Real.log (2 * ↑m₀) := Nat.floor_le (by positivity)
  have hk_gt : avg * Real.log (2 * ↑m₀) < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  -- hence k > avg * log(2m₀) - 1
  have hk_lb : avg * Real.log (2 * ↑m₀) - 1 < (k : ℝ) := by linarith
  refine ⟨?_, ?_, ?_⟩
  · -- 1 ≤ k
    rwa [Nat.one_le_floor_iff]
  · -- k ≤ m₀
    rw [← Nat.cast_le (α := ℝ)]
    calc (k : ℝ) ≤ avg * Real.log (2 * ↑m₀) := hk_le
      _ ≤ ↑m₀ := h3
  · -- Gap bounds
    intro m hm_lb hm_ub
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast show 0 < m by omega
    have h2m_pos : (0 : ℝ) < 2 * (m : ℝ) := by linarith
    constructor
    · -- C * log(2m) < k
      -- Key chain:
      -- C * log(2m) ≤ C * log(4m₀)
      --   = C * (log(2m₀) + log 2)  [since log(4m₀) = log(2 * 2m₀) = log 2 + log(2m₀)]
      --   = C * log(2m₀) + C * log 2
      -- k > avg * log(2m₀) - 1
      --   = C * log(2m₀) + (avg-C) * log(2m₀) - 1
      -- By cond2: (avg-C) * log(2m₀) ≥ 2 + C * log 2
      -- So k > C * log(2m₀) + 1 + C * log 2 > C * log(2m) 
      have hlog_2m : Real.log (2 * ↑m) ≤ Real.log (2 * (2 * ↑m₀ : ℝ)) := by
        apply Real.log_le_log h2m_pos
        push_cast
        nlinarith [show (m : ℤ) ≤ 2 * m₀ from by exact_mod_cast hm_ub]
      have hlog_split : Real.log (2 * (2 * (m₀ : ℝ))) = 
          Real.log (2 * ↑m₀) + Real.log 2 := by
        rw [show (2 : ℝ) * (2 * ↑m₀) = 2 * (2 * ↑m₀) from by ring]
        rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by positivity)]
      calc C * Real.log (2 * ↑m) 
          ≤ C * Real.log (2 * (2 * ↑m₀)) := by
            apply mul_le_mul_of_nonneg_left hlog_2m (le_of_lt hC)
        _ = C * (Real.log (2 * ↑m₀) + Real.log 2) := by rw [hlog_split]
        _ = C * Real.log (2 * ↑m₀) + C * Real.log 2 := by ring
        _ < (avg - C) * Real.log (2 * ↑m₀) - 1 + C * Real.log (2 * ↑m₀) := by
            -- need: C * log 2 < (avg-C)*log(2m₀) - 1
            -- i.e., 1 + C * log 2 < (avg-C)*log(2m₀)
            -- By cond2: (avg-C)*log(2m₀) ≥ 2 + C*log 2 > 1 + C*log 2
            linarith
        _ = avg * Real.log (2 * ↑m₀) - 1 := by ring
        _ < ↑k := hk_lb
    · -- k < C' * log(2m)
      -- k ≤ avg * log(2m₀) ≤ avg * log(2m) < C' * log(2m)
      have hlog_mono : Real.log (2 * ↑m₀) ≤ Real.log (2 * ↑m) := by
        apply Real.log_le_log h2m₀_pos
        push_cast
        nlinarith [show (m₀ : ℤ) ≤ m from by exact_mod_cast hm_lb]
      have hlog_2m_pos : 0 < Real.log (2 * ↑m) := by
        calc 0 < Real.log (2 * ↑m₀) := hlog_pos
          _ ≤ Real.log (2 * ↑m) := hlog_mono
      calc (k : ℝ) ≤ avg * Real.log (2 * ↑m₀) := hk_le
        _ ≤ avg * Real.log (2 * ↑m) := by
            apply mul_le_mul_of_nonneg_left hlog_mono (le_of_lt havg_pos)
        _ < C' * Real.log (2 * ↑m) := by
            apply mul_lt_mul_of_pos_right havg_C' hlog_2m_pos

end Erdos728
EOF
lake env lean /tmp/test_lgb7.lean 2>&1
```
A few issues to fix. The `nlinarith` calls with cast issues and the log_mul rewrite. Let me fix these:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_lgb8.lean << 'EOF'
import Mathlib
import Erdos.Lemmas

open Nat
open scoped Nat Topology

namespace Erdos728

private lemma log_le_sub_one {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ x - 1 := by
  calc Real.log x ≤ Real.log (Real.exp (x - 1)) := by
        apply Real.log_le_log (by linarith : 0 < x)
        linarith [Real.add_one_le_exp (x - 1)]
      _ = x - 1 := Real.log_exp (x - 1)

private lemma log_le_two_sqrt {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hsx : 1 ≤ Real.sqrt x := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith)
  calc Real.log x = Real.log (Real.sqrt x ^ 2) := by
          rw [Real.sq_sqrt (by linarith : 0 ≤ x)]
        _ = 2 * Real.log (Real.sqrt x) := by rw [Real.log_pow]; ring
        _ ≤ 2 * (Real.sqrt x - 1) := by
          apply mul_le_mul_of_nonneg_left (log_le_sub_one hsx) (by norm_num)
        _ ≤ 2 * Real.sqrt x := by linarith

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
  -- Sub-conditions (sorry'd for now - these are Filter.Tendsto facts about log)
  have cond1 : ∀ᶠ m₀ : ℕ in Filter.atTop, 1 ≤ avg * Real.log (2 * ↑m₀) := by sorry
  have cond2 : ∀ᶠ m₀ : ℕ in Filter.atTop, 
      2 + C * Real.log 2 ≤ (avg - C) * Real.log (2 * ↑m₀) := by sorry
  have cond3 : ∀ᶠ m₀ : ℕ in Filter.atTop, avg * Real.log (2 * ↑m₀) ≤ ↑m₀ := by sorry
  have cond4 : ∀ᶠ m₀ : ℕ in Filter.atTop, (1 : ℕ) ≤ m₀ := 
    Filter.eventually_atTop.mpr ⟨1, fun _ h => h⟩
  -- Combine
  rw [Filter.eventually_atTop] at cond1 cond2 cond3 cond4
  obtain ⟨N₁, hN₁⟩ := cond1
  obtain ⟨N₂, hN₂⟩ := cond2
  obtain ⟨N₃, hN₃⟩ := cond3
  obtain ⟨N₄, hN₄⟩ := cond4
  refine ⟨max (max N₁ N₂) (max N₃ N₄), fun m₀ hm₀ => ?_⟩
  have h1 := hN₁ m₀ (by omega)
  have h2 := hN₂ m₀ (by omega)
  have h3 := hN₃ m₀ (by omega)
  have h4 := hN₄ m₀ (by omega)
  set k := ⌊avg * Real.log (2 * ↑m₀)⌋₊ with k_def
  have hm₀_pos : (0 : ℝ) < (m₀ : ℝ) := by exact_mod_cast show 0 < m₀ by omega
  have h2m₀_pos : (0 : ℝ) < 2 * (m₀ : ℝ) := by linarith
  have hlog_pos : 0 < Real.log (2 * ↑m₀) := Real.log_pos (by linarith)
  have hk_le : (k : ℝ) ≤ avg * Real.log (2 * ↑m₀) := Nat.floor_le (by positivity)
  have hk_lb : avg * Real.log (2 * ↑m₀) - 1 < (k : ℝ) := Nat.sub_one_lt_floor _
  refine ⟨?_, ?_, ?_⟩
  · rwa [Nat.one_le_floor_iff]
  · rw [← Nat.cast_le (α := ℝ)]; linarith
  · intro m hm_lb hm_ub
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast show 0 < m by omega
    have h2m_pos : (0 : ℝ) < 2 * (m : ℝ) := by linarith
    -- Monotonicity facts for log
    have hm_cast_lb : (m₀ : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hm_lb
    have hm_cast_ub : (m : ℝ) ≤ 2 * (m₀ : ℝ) := by exact_mod_cast hm_ub
    have hlog_mono : Real.log (2 * ↑m₀) ≤ Real.log (2 * ↑m) :=
      Real.log_le_log h2m₀_pos (by linarith)
    have hlog_2m_pos : 0 < Real.log (2 * ↑m) := lt_of_lt_of_le hlog_pos hlog_mono
    have hlog_ub : Real.log (2 * ↑m) ≤ Real.log (4 * ↑m₀) := by
      apply Real.log_le_log h2m_pos
      linarith
    have hlog_split : Real.log (4 * (m₀ : ℝ)) = Real.log 2 + Real.log (2 * ↑m₀) := by
      rw [show (4 : ℝ) * ↑m₀ = 2 * (2 * ↑m₀) from by ring]
      exact Real.log_mul (by norm_num) (by linarith)
    constructor
    · -- C * log(2m) < k
      calc C * Real.log (2 * ↑m) 
          ≤ C * Real.log (4 * ↑m₀) := by
            exact mul_le_mul_of_nonneg_left hlog_ub (le_of_lt hC)
        _ = C * (Real.log 2 + Real.log (2 * ↑m₀)) := by rw [hlog_split]
        _ = C * Real.log (2 * ↑m₀) + C * Real.log 2 := by ring
        _ < avg * Real.log (2 * ↑m₀) - 1 := by nlinarith
        _ < ↑k := hk_lb
    · -- k < C' * log(2m)
      calc (k : ℝ) ≤ avg * Real.log (2 * ↑m₀) := hk_le
        _ ≤ avg * Real.log (2 * ↑m) := by
            exact mul_le_mul_of_nonneg_left hlog_mono (le_of_lt havg_pos)
        _ < C' * Real.log (2 * ↑m) := by
            exact mul_lt_mul_of_pos_right havg_C' hlog_2m_pos

end Erdos728
EOF
lake env lean /tmp/test_lgb8.lean 2>&1
```
Excellent! The `log_gap_bounds` proof compiles! The only remaining sorrys are the three `∀ᶠ ... in Filter.atTop` facts about `log` growing to infinity and `log/x → 0`. Let me now try to prove those:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_conds.lean << 'EOF'
import Mathlib

-- Check tendsto for log
#check Real.tendsto_log_atTop
#check Filter.Tendsto.eventually_ge_atTop
#check Filter.Tendsto.comp
#check Filter.Tendsto.atTop_mul_const

-- cond1: ∀ᶠ m₀ : ℕ in atTop, 1 ≤ avg * log(2 * m₀)
-- This follows from: log(2 * n) → ∞ as n → ∞
-- Since avg > 0, avg * log(2n) → ∞

-- cond2: similar with different constant

-- cond3: ∀ᶠ m₀ : ℕ in atTop, avg * log(2 * m₀) ≤ m₀
-- This follows from: log(x)/x → 0

-- Let me find the right tendsto lemmas
#check Filter.Tendsto.eventually_ge_atTop
-- Tendsto f l atTop → ∀ c, ∀ᶠ x in l, c ≤ f x

-- For cond1, we need: Tendsto (fun n => avg * log(2*n)) atTop atTop
-- This follows from: log is tendsto atTop atTop, composition with 2*cast is atTop → atTop

-- Let me try
example (A : ℝ) (hA : 0 < A) : ∀ᶠ n : ℕ in Filter.atTop, 1 ≤ A * Real.log (2 * ↑n) := by
  -- log(2*n) → ∞ as n → ∞, so A * log(2n) → ∞
  have h1 : Filter.Tendsto (fun n : ℕ => (2 : ℝ) * (n : ℝ)) Filter.atTop Filter.atTop := by
    apply Filter.Tendsto.const_mul_atTop (by norm_num : (0:ℝ) < 2)
    exact Filter.tendsto_natCast_atTop_atTop
  have h2 : Filter.Tendsto (fun n : ℕ => Real.log (2 * (n : ℝ))) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp h1
  have h3 : Filter.Tendsto (fun n : ℕ => A * Real.log (2 * (n : ℝ))) Filter.atTop Filter.atTop := by
    exact Filter.Tendsto.const_mul_atTop hA h2
  exact h3.eventually_ge_atTop 1

-- cond3 is trickier: avg * log(2n) ≤ n
-- i.e., log(2n)/n → 0, so avg * log(2n)/n → 0 < 1
-- We need: ∀ᶠ n, avg * log(2n) ≤ n
-- Equivalently: ∀ᶠ n, avg * log(2n) / n ≤ 1

-- Check if there's a log/x → 0 result
#check Real.tendsto_log_div_rpow_nhds_zero_atTop  -- or similar
-- #check Real.tendsto_log_nat_div_atTop  -- probably not

-- Let me search
EOF
lake env lean /tmp/test_conds.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && grep -r "tendsto_natCast" .lake/packages/mathlib/Mathlib/ --include="*.lean" | grep "atTop" | head -5
```

```bash
$ cd /home/jarred/code/erdos-728b && grep -rn "tendsto_natCast_atTop" .lake/packages/mathlib/Mathlib/ --include="*.lean" | grep "^.*:.*theorem\|^.*:.*lemma\|^.*:.*def" | head -5
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_conds2.lean << 'EOF'
import Mathlib

#check @tendsto_natCast_atTop_atTop ℝ _ _ _
-- Check it works
example : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
  tendsto_natCast_atTop_atTop

-- OK, now cond1:
example (A : ℝ) (hA : 0 < A) : ∀ᶠ n : ℕ in Filter.atTop, 1 ≤ A * Real.log (2 * ↑n) := by
  have h1 : Filter.Tendsto (fun n : ℕ => (2 : ℝ) * (n : ℝ)) Filter.atTop Filter.atTop := by
    exact Filter.Tendsto.const_mul_atTop (by norm_num : (0:ℝ) < 2) tendsto_natCast_atTop_atTop
  have h2 : Filter.Tendsto (fun n : ℕ => Real.log (2 * (n : ℝ))) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp h1
  have h3 : Filter.Tendsto (fun n : ℕ => A * Real.log (2 * (n : ℝ))) Filter.atTop Filter.atTop := by
    apply Filter.Tendsto.atTop_mul_const hA |>.comp -- wait, wrong direction
    sorry
  exact h3.eventually_ge_atTop 1

-- Let me find the right mul_atTop
#check Filter.Tendsto.const_mul_atTop  -- c * f where c > 0 and f → ∞
-- Tendsto f l atTop → Tendsto (c * f) l atTop (for c > 0)
-- But the arg order might be different

example (A : ℝ) (hA : 0 < A) : Filter.Tendsto (fun n : ℕ => A * Real.log (2 * (n : ℝ))) Filter.atTop Filter.atTop := by
  have h1 : Filter.Tendsto (fun n : ℕ => (2 : ℝ) * (n : ℝ)) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
  have h2 : Filter.Tendsto (fun n : ℕ => Real.log (2 * (n : ℝ))) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp h1
  exact Filter.Tendsto.const_mul_atTop hA h2

-- Now for cond3: avg * log(2n) ≤ n eventually
-- Let me check for log/x → 0 type results
#check Real.tendsto_log_div_rpow_nhds_zero_atTop -- doesn't exist by name
EOF
lake env lean /tmp/test_conds2.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_conds3.lean << 'EOF'
import Mathlib

-- cond1 and cond2: A * log(2n) → ∞
lemma tendsto_const_mul_log_atTop (A : ℝ) (hA : 0 < A) : 
    Filter.Tendsto (fun n : ℕ => A * Real.log (2 * (n : ℝ))) Filter.atTop Filter.atTop := by
  have h1 : Filter.Tendsto (fun n : ℕ => (2 : ℝ) * (n : ℝ)) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
  exact Filter.Tendsto.const_mul_atTop hA (Real.tendsto_log_atTop.comp h1)

-- cond3: A * log(2n) ≤ n eventually
-- We need log(2n)/n → 0
-- Let me search for this in Mathlib
-- #check Real.tendsto_log_div_rpow_nhds_zero_atTop  

-- Search for log/id → 0
-- In Analysis/SpecificLimits maybe?

-- Alternative: use log_le_two_sqrt and sqrt(n)/n → 0

-- A * log(2n) ≤ A * 2*sqrt(2n) (for n ≥ 1, by log_le_two_sqrt)
-- = 2A * sqrt(2) * sqrt(n)
-- ≤ n when n ≥ (2A * sqrt(2))^2 = 8A²

-- So the condition A * log(2n) ≤ n holds for n ≥ max(1, ⌈8A²⌉₊)

-- Let me try this approach
private lemma log_le_sub_one {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ x - 1 := by
  calc Real.log x ≤ Real.log (Real.exp (x - 1)) := by
        apply Real.log_le_log (by linarith : 0 < x)
        linarith [Real.add_one_le_exp (x - 1)]
      _ = x - 1 := Real.log_exp (x - 1)

private lemma log_le_two_sqrt {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hsx : 1 ≤ Real.sqrt x := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith)
  calc Real.log x = Real.log (Real.sqrt x ^ 2) := by
          rw [Real.sq_sqrt (by linarith : 0 ≤ x)]
        _ = 2 * Real.log (Real.sqrt x) := by rw [Real.log_pow]; ring
        _ ≤ 2 * (Real.sqrt x - 1) := by
          apply mul_le_mul_of_nonneg_left (log_le_sub_one hsx) (by norm_num)
        _ ≤ 2 * Real.sqrt x := by linarith

-- For n ≥ 8A², A * log(2n) ≤ n
lemma eventually_log_le_id (A : ℝ) (hA : 0 < A) :
    ∀ᶠ n : ℕ in Filter.atTop, A * Real.log (2 * (n : ℝ)) ≤ (n : ℝ) := by
  rw [Filter.eventually_atTop]
  -- We need: A * log(2n) ≤ A * 2*sqrt(2n) ≤ n for n ≥ 8A²
  -- A * 2 * sqrt(2n) ≤ n ↔ 4A² * 2n ≤ n² ↔ n ≥ 8A²
  refine ⟨⌈8 * A ^ 2⌉₊ + 2, fun n hn => ?_⟩
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have h2n_pos : (0 : ℝ) < 2 * (n : ℝ) := by linarith
  have h2n_ge : (1 : ℝ) ≤ 2 * (n : ℝ) := by
    have : 2 ≤ n := by omega
    exact_mod_cast show 1 ≤ 2 * n by omega
  calc A * Real.log (2 * ↑n) 
      ≤ A * (2 * Real.sqrt (2 * ↑n)) := by
        apply mul_le_mul_of_nonneg_left (log_le_two_sqrt h2n_ge) (le_of_lt hA)
    _ = 2 * A * Real.sqrt (2 * ↑n) := by ring
    _ ≤ ↑n := by
        -- Need: (2A)² * (2n) ≤ n², i.e., 8A²n ≤ n², i.e., n ≥ 8A²
        rw [← Real.sqrt_sq (by linarith : 0 ≤ (n : ℝ))]
        rw [← Real.sqrt_mul (by positivity : 0 ≤ (2 * A) ^ 2)]
        apply Real.sqrt_le_sqrt
        have hn_ge : 8 * A ^ 2 ≤ (n : ℝ) := by
          calc 8 * A ^ 2 ≤ ↑(⌈8 * A ^ 2⌉₊ + 2) := by
                push_cast
                have := Nat.le_ceil (8 * A ^ 2)
                linarith
            _ ≤ ↑n := Nat.cast_le.mpr hn
        nlinarith

EOF
lake env lean /tmp/test_conds3.lean 2>&1
```
The sqrt approach is getting messy. Let me try a simpler approach:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_conds4.lean << 'EOF'
import Mathlib

-- Simpler approach for eventually_log_le_id
-- Use: for n ≥ 1, log(2n) ≤ 2n (by log_le_self variant)
-- So A * log(2n) ≤ A * 2n = 2An
-- We need 2An ≤ n, which is false for A ≥ 1/2.

-- Use log_le_two_sqrt more carefully.
-- A * log(2n) ≤ 2A * sqrt(2n)
-- Need: 2A * sqrt(2n) ≤ n
-- Square both sides (both positive): 4A² * 2n ≤ n²
-- i.e., 8A²n ≤ n², i.e., n ≥ 8A²

-- Let me do this without sqrt_sq issues
lemma eventually_log_le_id (A : ℝ) (hA : 0 < A) :
    ∀ᶠ n : ℕ in Filter.atTop, A * Real.log (2 * (n : ℝ)) ≤ (n : ℝ) := by
  rw [Filter.eventually_atTop]
  -- Use log(x) ≤ x - 1 for x ≥ 1, applied twice:
  -- log(2n) = 2*log(sqrt(2n)) ≤ 2*(sqrt(2n) - 1) ≤ 2*sqrt(2n)
  -- Then 2A*sqrt(2n) ≤ n ↔ 4A²*2n ≤ n² ↔ n ≥ 8A²
  refine ⟨⌈8 * A ^ 2⌉₊ + 2, fun n hn => ?_⟩
  have hn2 : 2 ≤ n := by omega
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast show 0 < n by omega
  have h2n_ge1 : (1 : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast show 1 ≤ 2 * n by omega
  -- Step 1: log(2n) ≤ 2*sqrt(2n)
  have hsx : 1 ≤ Real.sqrt (2 * ↑n) := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt h2n_ge1
  have hlog_bound : Real.log (2 * ↑n) ≤ 2 * Real.sqrt (2 * ↑n) := by
    have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 * ↑n by linarith)
    calc Real.log (2 * ↑n) 
        = Real.log (Real.sqrt (2 * ↑n) ^ 2) := by rw [h]
      _ = 2 * Real.log (Real.sqrt (2 * ↑n)) := by rw [Real.log_pow]; ring
      _ ≤ 2 * (Real.sqrt (2 * ↑n) - 1) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
          calc Real.log (Real.sqrt (2 * ↑n))
              ≤ Real.log (Real.exp (Real.sqrt (2 * ↑n) - 1)) := by
                apply Real.log_le_log (by positivity)
                linarith [Real.add_one_le_exp (Real.sqrt (2 * ↑n) - 1)]
            _ = Real.sqrt (2 * ↑n) - 1 := Real.log_exp _
      _ ≤ 2 * Real.sqrt (2 * ↑n) := by linarith
  -- Step 2: 2A*sqrt(2n) ≤ n
  have hn_ge_8A2 : 8 * A ^ 2 ≤ (n : ℝ) := by
    calc 8 * A ^ 2 ≤ ↑(⌈8 * A ^ 2⌉₊ + 2) := by push_cast; linarith [Nat.le_ceil (8 * A ^ 2)]
      _ ≤ ↑n := Nat.cast_le.mpr hn
  have hsqrt_bound : 2 * A * Real.sqrt (2 * ↑n) ≤ (n : ℝ) := by
    -- (2A*sqrt(2n))² = 4A²*2n = 8A²n ≤ n² = n*n
    -- Since both sides are ≥ 0, this gives 2A*sqrt(2n) ≤ n
    have h_sq : (2 * A * Real.sqrt (2 * ↑n)) ^ 2 ≤ (n : ℝ) ^ 2 := by
      have : Real.sqrt (2 * ↑n) ^ 2 = 2 * ↑n := Real.sq_sqrt (by linarith : 0 ≤ 2 * ↑n)
      nlinarith
    have h_nn1 : 0 ≤ 2 * A * Real.sqrt (2 * ↑n) := by positivity
    have h_nn2 : 0 ≤ (n : ℝ) := by linarith
    exact le_of_sq_le_sq h_sq h_nn2
  -- Combine
  calc A * Real.log (2 * ↑n) 
      ≤ A * (2 * Real.sqrt (2 * ↑n)) := by
        exact mul_le_mul_of_nonneg_left hlog_bound (le_of_lt hA)
    _ = 2 * A * Real.sqrt (2 * ↑n) := by ring
    _ ≤ ↑n := hsqrt_bound

-- Check le_of_sq_le_sq exists
#check le_of_sq_le_sq
EOF
lake env lean /tmp/test_conds4.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_conds5.lean << 'EOF'
import Mathlib

-- Wait, le_of_sq_le_sq needs |a| ≤ b, but we have a ≥ 0.
-- Actually it says a ≤ b, not |a| ≤ b. Let me check.

-- le_of_sq_le_sq : a² ≤ b² → 0 ≤ b → a ≤ b
-- Wait that's wrong — it would give a ≤ b even for negative a.
-- Actually it should be: a² ≤ b² and 0 ≤ b → a ≤ b
-- This IS wrong for a = -3, b = 2: (-3)² = 9 > 4 = 2².
-- Oh wait, 9 > 4, so the hypothesis fails. OK.
-- For a ≥ 0: a² ≤ b² and b ≥ 0 → a ≤ b. That's correct.

-- Let me just use sq_le_sq' or similar
-- Actually, for non-negative a, b: a ≤ b ↔ a² ≤ b²
#check sq_le_sq'
-- This might have absolute values

-- Simplest: use the Lean 4 approach
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  nlinarith [sq_abs a, sq_abs b, abs_of_nonneg ha, abs_of_nonneg hb]

-- That works! Let me try the full proof now.
lemma eventually_log_le_id (A : ℝ) (hA : 0 < A) :
    ∀ᶠ n : ℕ in Filter.atTop, A * Real.log (2 * (n : ℝ)) ≤ (n : ℝ) := by
  rw [Filter.eventually_atTop]
  refine ⟨⌈8 * A ^ 2⌉₊ + 2, fun n hn => ?_⟩
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast show 0 < n by omega
  have h2n_ge1 : (1 : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast show 1 ≤ 2 * n by omega
  have h2n_nn : (0 : ℝ) ≤ 2 * (n : ℝ) := by linarith
  -- log(2n) ≤ 2*sqrt(2n)
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
  -- 2A*sqrt(2n) ≤ n (using n ≥ 8A²)
  have hn_ge : 8 * A ^ 2 ≤ (n : ℝ) := by
    calc 8 * A ^ 2 ≤ ↑(⌈8 * A ^ 2⌉₊ + 2) := by push_cast; linarith [Nat.le_ceil (8 * A ^ 2)]
      _ ≤ ↑n := Nat.cast_le.mpr hn
  have hsqrt_bound : 2 * A * Real.sqrt (2 * ↑n) ≤ (n : ℝ) := by
    have h_sq : (2 * A * Real.sqrt (2 * ↑n)) ^ 2 ≤ (n : ℝ) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt h2n_nn]
      nlinarith
    nlinarith [sq_abs (2 * A * Real.sqrt (2 * ↑n)), sq_abs (n : ℝ),
               abs_of_nonneg (show 0 ≤ 2 * A * Real.sqrt (2 * ↑n) from by positivity),
               abs_of_nonneg (show 0 ≤ (n : ℝ) from by linarith)]
  calc A * Real.log (2 * ↑n) 
      ≤ A * (2 * Real.sqrt (2 * ↑n)) := mul_le_mul_of_nonneg_left hlog_bound (le_of_lt hA)
    _ = 2 * A * Real.sqrt (2 * ↑n) := by ring
    _ ≤ ↑n := hsqrt_bound

EOF
lake env lean /tmp/test_conds5.lean 2>&1
```
All three conditions compile. Now let me put the full `log_gap_bounds` together with all the conditions proven:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_lgb_full.lean << 'EOF'
import Mathlib
import Erdos.Lemmas

open Nat
open scoped Nat Topology

namespace Erdos728

private lemma log_le_two_sqrt_real {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hsx : 1 ≤ Real.sqrt x := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith)
  calc Real.log x = Real.log (Real.sqrt x ^ 2) := by
          rw [Real.sq_sqrt (by linarith : 0 ≤ x)]
        _ = 2 * Real.log (Real.sqrt x) := by rw [Real.log_pow]; ring
        _ ≤ 2 * (Real.sqrt x - 1) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
          calc Real.log (Real.sqrt x)
              ≤ Real.log (Real.exp (Real.sqrt x - 1)) := by
                apply Real.log_le_log (by positivity)
                linarith [Real.add_one_le_exp (Real.sqrt x - 1)]
            _ = Real.sqrt x - 1 := Real.log_exp _
        _ ≤ 2 * Real.sqrt x := by linarith

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
  have hlog_bound : Real.log (2 * ↑n) ≤ 2 * Real.sqrt (2 * ↑n) :=
    log_le_two_sqrt_real h2n_ge1
  have hn_ge : 8 * A ^ 2 ≤ (n : ℝ) := by
    calc 8 * A ^ 2 ≤ ↑(⌈8 * A ^ 2⌉₊ + 2) := by push_cast; linarith [Nat.le_ceil (8 * A ^ 2)]
      _ ≤ ↑n := Nat.cast_le.mpr hn
  have hsqrt_bound : 2 * A * Real.sqrt (2 * ↑n) ≤ (n : ℝ) := by
    have : (2 * A * Real.sqrt (2 * ↑n)) ^ 2 ≤ (n : ℝ) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt h2n_nn]; nlinarith
    nlinarith [sq_abs (2 * A * Real.sqrt (2 * ↑n)), sq_abs (n : ℝ),
               abs_of_nonneg (show 0 ≤ 2 * A * Real.sqrt (2 * ↑n) from by positivity),
               abs_of_nonneg (show 0 ≤ (n : ℝ) from by linarith)]
  calc A * Real.log (2 * ↑n)
      ≤ A * (2 * Real.sqrt (2 * ↑n)) := mul_le_mul_of_nonneg_left hlog_bound (le_of_lt hA)
    _ = 2 * A * Real.sqrt (2 * ↑n) := by ring
    _ ≤ ↑n := hsqrt_bound

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
  have hk_le : (k : ℝ) ≤ avg * Real.log (2 * ↑m₀) := Nat.floor_le (by positivity)
  have hk_lb : avg * Real.log (2 * ↑m₀) - 1 < (k : ℝ) := Nat.sub_one_lt_floor _
  refine ⟨?_, ?_, ?_⟩
  · rwa [Nat.one_le_floor_iff]
  · rw [← Nat.cast_le (α := ℝ)]; linarith
  · intro m hm_lb hm_ub
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast show 0 < m by omega
    have h2m_pos : (0 : ℝ) < 2 * (m : ℝ) := by linarith
    have hm_cast_lb : (m₀ : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hm_lb
    have hm_cast_ub : (m : ℝ) ≤ 2 * (m₀ : ℝ) := by exact_mod_cast hm_ub
    have hlog_mono : Real.log (2 * ↑m₀) ≤ Real.log (2 * ↑m) :=
      Real.log_le_log h2m₀_pos (by linarith)
    have hlog_2m_pos : 0 < Real.log (2 * ↑m) := lt_of_lt_of_le hlog_pos hlog_mono
    have hlog_ub : Real.log (2 * ↑m) ≤ Real.log (4 * ↑m₀) :=
      Real.log_le_log h2m_pos (by linarith)
    have hlog_split : Real.log (4 * (m₀ : ℝ)) = Real.log 2 + Real.log (2 * ↑m₀) := by
      rw [show (4 : ℝ) * ↑m₀ = 2 * (2 * ↑m₀) from by ring]
      exact Real.log_mul (by norm_num) (by linarith)
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

end Erdos728
EOF
lake env lean /tmp/test_lgb_full.lean 2>&1
```
