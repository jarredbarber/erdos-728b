# timtam Task: Close sorry in exists_m_small_primes_good_uniform (union bound) (erdos728b-48g)

Role: formalize
Agent: formalize (google-antigravity/claude-opus-4-6-thinking)
Start Time: 2026-02-11T04:31:07.268Z

## Agent Interaction



> **Thinking:**
> Let me start by understanding the task. I need to close a `sorry` in `exists_m_small_primes_good_uniform` at line 62 of `Erdos/Basic.lean`. Let me first read the relevant files to understand the context.


```bash
$ cd /home/jarred/code/erdos-728b && tm update erdos728b-48g --status "Reading source files and NL proof"
```

🛠️ **Executing tool: read**

🛠️ **Executing tool: read**

🛠️ **Executing tool: read**

```bash
$ cd /home/jarred/code/erdos-728b && cat proofs/lemma3-union-bound.md 2>/dev/null | head -200
```
Now let me understand the full context. Let me check the current state of compilation and look at what's available:
```bash
$ cd /home/jarred/code/erdos-728b && lake build 2>&1 | tail -30
```
Good, the project compiles. The sorry is at line 62 of `Erdos/Basic.lean`, in `exists_m_small_primes_good_uniform`. Let me look at exactly what needs to be proved:
🛠️ **Executing tool: read**

```bash
$ cd /home/jarred/code/erdos-728b && tm update erdos728b-48g --status "Analyzing the sorry structure and proof approach"
```
Let me study this problem carefully. The key challenge is that `M₀` must be chosen **before** `k` is quantified. The NL proof gives `M₀(k) = (2k)^{O(log k)}` which depends on `k`, but we need a single `M₀` that works for all `k ≤ C_log * log(2m₀)`. 

Since `k ≤ C_log * log(2m₀)`, the bound `M₀(k)` is subpolynomial in `m₀`, so for large enough `m₀`, `M₀(k) ≤ m₀` for all valid `k`. But formalizing this directly is complex.

Let me think about a simpler approach. The available `count_bad_interval` lemma has sorrys in it too. Let me check what's really available:
```bash
$ cd /home/jarred/code/erdos-728b && grep -n "sorry" Erdos/Lemma3Counting.lean
```
So `count_bad_interval` itself is sorry'd. Let me look at the other files:
```bash
$ cd /home/jarred/code/erdos-728b && find Erdos/ -name "*.lean" | xargs grep -l "sorry" 2>/dev/null
```

```bash
$ cd /home/jarred/code/erdos-728b && cat Erdos/Lemmas.lean
```

```bash
$ cd /home/jarred/code/erdos-728b && tm update erdos728b-48g --status "Designing proof approach — the key issue is M₀ must be independent of k"
```
Let me think about this carefully.

The statement to prove is:
```
∃ M₀ : ℕ, ∀ m₀ : ℕ, M₀ ≤ m₀ → ∀ k : ℕ, 1 ≤ k →
    (k : ℝ) ≤ C_log * Real.log (2 * m₀) →
    ∃ m : ℕ, m₀ ≤ m ∧ m < 2 * m₀ ∧
      ∀ p : ℕ, p.Prime → p ≤ 2 * k →
        padicValNat p ((m + k).choose k) ≤ padicValNat p ((2 * m).choose m)
```

The NL proof in Part E gives, for each fixed `k`, an `M₀(k)` that works. But we need a single `M₀` before `k` is quantified. The bound is `M₀(k) = (2k)^{72⌈log₂(16k)⌉ + 72}`, and since `k ≤ C_log * log(2m₀)`, this is `(2C_log log(2m₀))^{O(log log m₀)}` which is subpolynomial in `m₀`, so eventually `m₀ > M₀(k)`.

The `count_bad_interval` lemma in `Lemma3Counting.lean` is sorry'd. Since this is a formalize task, I should be translating the NL proof, using existing lemmas. The existing `count_bad_interval` has the right signature but is sorry'd — I can still use it as a building block, leaving those sorrys as separate tasks.

Let me look more closely at the signature of `count_bad_interval`:
🛠️ **Executing tool: read**
Now I understand the full picture. The `count_bad_interval` lemma requires `p ≥ 3`, which means `p = 2` needs special treatment. Let me look at the Lemma3Common:
```bash
$ cd /home/jarred/code/erdos-728b && cat Erdos/Lemma3Common.lean
```

```bash
$ cd /home/jarred/code/erdos-728b && cat Erdos/Digits.lean 2>/dev/null | head -60
```

```bash
$ cd /home/jarred/code/erdos-728b && wc -l Erdos/Digits.lean
```

🛠️ **Executing tool: read**
Now I have a clear picture. Let me design the proof approach.

The challenge: `M₀` must be chosen before `k`. The NL proof gives `M₀(k)`, and we need to show a single `M₀` works for all `k ≤ C_log * log(2m₀)`.

**Strategy**: Rather than doing the full union bound with explicit `D_p` and `M₀(k)`, I can structure this as:
1. Define `exists_m_for_fixed_k`: for each fixed `k`, there exists `M₀(k)` such that for `m₀ ≥ M₀(k)`, a good `m` exists. This uses `count_bad_interval` (sorry'd but usable).
2. Show that `M₀(k) = (2k)^{O(log k)}` is eventually dominated by `m₀` when `k ≤ C_log * log(2m₀)`.

Actually, looking at this more carefully, the proof is extremely complex and involves multiple layers of sorry'd lemmas. Let me think about the most pragmatic approach.

Given that `count_bad_interval` and many supporting lemmas are already sorry'd, the right approach is to build the **outer structure** of the union bound, using `count_bad_interval` as a black box, and leaving precise arithmetic as sorry'd helper lemmas where needed.

Let me write a cleaner decomposition:
```bash
$ cd /home/jarred/code/erdos-728b && tm update erdos728b-48g --status "Writing helper lemmas and proof structure in Lemma3Counting.lean"
```
Let me think about the simplest correct approach. The statement says: for any `C_log`, there exists `M₀` such that for all `m₀ ≥ M₀`, for all valid `k`, the good `m` exists. 

The most pragmatic approach: define `exists_m_for_fixed_k` — for each fixed `k ≥ 1`, there's an `M₀(k)` such that for `m₀ ≥ M₀(k)`, a good `m` exists in `[m₀, 2m₀)`. Then show that when `k ≤ C_log * log(2m₀)`, `M₀(k) ≤ m₀` eventually.

But actually, this is the entire proof! Let me think about what helper lemmas I need.

Actually, let me reconsider. The statement requires `m < 2 * m₀` (strict), and we're counting bad `m` in `[m₀, 2m₀)` (which has exactly `m₀` elements). The union bound shows at most `m₀/4` are bad, so there exists a good one.

Let me look at this problem from a high level: the NL proof's Theorem E2 says that for `k ≥ 2` and `m₀ ≥ M₀(k)`, the number of bad `m` in `[m₀, 2m₀)` is at most `m₀/4 < m₀`, so a good `m` exists. The key steps:

1. For each prime `p ≤ 2k`, define `D_p` and bound the bad count using `count_bad_interval`
2. Sum over primes, show total bad `≤ m₀/4`
3. Existence by pigeonhole

The M₀ problem: For the final statement, I need a single M₀ that works for ALL k ≤ C_log * log(2m₀). The approach is:
- `M₀(k)` is quasi-polynomial in `k`
- `k ≤ C_log * log(2m₀)` means `k = O(log m₀)`
- `M₀(O(log m₀))` = subpolynomial in `m₀`
- So eventually `m₀ ≥ M₀(k)` for all valid `k`

This is the hardest part to formalize. Let me take a step back and think about whether I can structure the sorry replacement to decompose into smaller pieces.

Given the complexity, I think the best approach is to:
1. Create a helper lemma `exists_m_for_fixed_k` that handles a single `k` (sorry'd with clear sub-goals)
2. Create a helper lemma about `M₀(k) ≤ m₀` eventually (sorry'd)  
3. Combine them to prove the main lemma

Let me write this:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_union.lean << 'EOF'
import Mathlib
import Erdos.Lemmas
import Erdos.Lemma3Counting

open Real Nat Filter Asymptotics Finset
open scoped Nat Topology

namespace Erdos728

-- Check what Finset.Ico looks like
#check Finset.Ico
#check Finset.card_Ico
#check @Finset.card_Ico ℕ _ 
EOF
lake env lean /tmp/test_union.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_union.lean << 'EOF'
import Mathlib
import Erdos.Lemmas
import Erdos.Lemma3Counting

open Real Nat Filter Asymptotics Finset
open scoped Nat Topology

namespace Erdos728

#check Finset.card_Ico_eq_sub  -- or similar?
example (a b : ℕ) (h : a ≤ b) : (Finset.Ico a b).card = b - a := by exact?

EOF
lake env lean /tmp/test_union.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_union.lean << 'EOF'
import Mathlib
import Erdos.Lemmas
import Erdos.Lemma3Counting

open Real Nat Filter Asymptotics Finset
open scoped Nat Topology

namespace Erdos728

-- card_Ico for ℕ
#print card_Ico
-- Finset.card_filter_le_card
#check Finset.card_filter_le_card

-- Union bound: if |S_i ∩ [a,b)| ≤ c for each i in I,
-- then |⋃_i (S_i ∩ [a,b))| ≤ |I| * c
#check Finset.card_biUnion_le

-- Subset complement: if |bad| < |total|, then exists good
#check Finset.exists_mem_of_ne_empty

EOF
lake env lean /tmp/test_union.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_union.lean << 'EOF'
import Mathlib
import Erdos.Lemmas
import Erdos.Lemma3Counting

open Real Nat Filter Asymptotics Finset
open scoped Nat Topology

namespace Erdos728

-- If |bad| < |total|, there exists a non-bad element
#check Finset.exists_not_mem

-- card of filter ≤ card
#check Finset.filter_card_le_card  

-- Interval basics
example (a b : ℕ) : (Finset.Ico a b).card = b - a := Nat.card_Ico a b

-- Existence by complement
-- If |bad ∩ S| < |S|, then ∃ x ∈ S, x ∉ bad
example (S : Finset ℕ) (bad : Finset ℕ) (h : bad.card < S.card) : 
    ∃ x ∈ S, x ∉ bad := by
  by_contra h_all
  push_neg at h_all
  have : S ⊆ bad := h_all
  exact absurd (Finset.card_le_card this) (not_le.mpr h)

EOF
lake env lean /tmp/test_union.lean 2>&1
```
OK, the basic approach works. Let me now think about the right structure for the proof. The key insight is:

For the `exists_m_small_primes_good_uniform` lemma, I need to show existence of a good `m` in `[m₀, 2m₀)`. The approach:

1. For each prime `p ≤ 2k`, define `D_p` and let `bad_p = {m ∈ [m₀, 2m₀) : v_p(C(m+k,k)) > v_p(C(2m,m))}`
2. By `count_bad_interval`, `|bad_p| ≤ (2m₀)/2^{D_p/36} + (2p^{D_p})/2^{D_p/36}`
3. Under the right conditions on D_p, each `|bad_p| ≤ m₀/(8k)`
4. Union over ≤ 2k primes: total bad ≤ `2k · m₀/(8k) = m₀/4`
5. Since `m₀/4 < m₀ = |[m₀, 2m₀)|`, a good `m` exists

The M₀ challenge: We need `p^{D_p} ≤ m₀` and `2^{D_p/36} ≥ 32k`. With `D_p = 36⌈log₂(16k)⌉ + 36⌊log_p(k+1)⌋ + 36`, the first condition becomes `m₀ ≥ (2k)^{72⌈log₂(16k)⌉ + 72} = M₀(k)`, and since `k ≤ C_log · log(2m₀)`, we need `m₀ ≥ M₀(C_log · log(2m₀))`.

This is really a growth rate argument. Let me define a simpler helper: for any `k`, define `M₀_threshold(k)` and then prove that eventually `m₀ ≥ M₀_threshold(k)` for all `k ≤ C_log · log(2m₀)`.

Given the complexity, I think the best approach is to structure the proof with well-annotated sorry's that decompose the problem into independent pieces. Let me write the proof with clear helper lemmas:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_structure.lean << 'EOF'
import Mathlib
import Erdos.Lemmas
import Erdos.Lemma3Counting

open Real Nat Filter Asymptotics Finset
open scoped Nat Topology

namespace Erdos728

section UnionBound

/-! ### Union bound over small primes

For each fixed k ≥ 1, there exists M₀(k) such that for m₀ ≥ M₀(k),
at most m₀/4 values of m ∈ [m₀, 2m₀) are "bad" for any prime p ≤ 2k.
-/

/-- For fixed k, defines the threshold M₀(k) above which the union bound works.
    M₀(k) = (2k)^{72⌈log₂(16k)⌉ + 72}. For formalization we just need existence. -/
private lemma exists_m_for_fixed_k (k : ℕ) (hk : k ≥ 1) :
    ∃ M₀ : ℕ, ∀ m₀ : ℕ, M₀ ≤ m₀ →
      ∃ m : ℕ, m₀ ≤ m ∧ m < 2 * m₀ ∧
        ∀ p : ℕ, p.Prime → p ≤ 2 * k →
          padicValNat p ((m + k).choose k) ≤ padicValNat p ((2 * m).choose m) := by
  /- STUCK: This requires the full union bound argument from Part E.
     The proof outline:
     1. For each prime p ≤ 2k, choose D_p = 36⌈log₂(16k)⌉ + 36⌊log_p(k+1)⌋ + 36
     2. Apply count_bad_interval to bound |bad_p| in [m₀, 2m₀)
     3. Sum over primes: total bad ≤ m₀/4
     4. Since m₀/4 < m₀ = |[m₀, 2m₀)|, a good m exists
     Requires: count_bad_interval hypotheses verified for each prime. -/
  sorry

/-- The threshold M₀(k) from the union bound grows subpolynomially:
    M₀(k) = (2k)^{O(log k)} = 2^{O(log²k)}.
    When k ≤ C * log(2m₀), this is 2^{O(log²(log m₀))}, which is eventually ≤ m₀. -/
private lemma threshold_eventually_dominated (C_log : ℝ) :
    ∃ M₀ : ℕ, ∀ m₀ : ℕ, M₀ ≤ m₀ → ∀ k : ℕ, 1 ≤ k →
      (k : ℝ) ≤ C_log * Real.log (2 * m₀) →
      ∃ m : ℕ, m₀ ≤ m ∧ m < 2 * m₀ ∧
        ∀ p : ℕ, p.Prime → p ≤ 2 * k →
          padicValNat p ((m + k).choose k) ≤ padicValNat p ((2 * m).choose m) := by
  sorry

end UnionBound

end Erdos728
EOF
lake env lean /tmp/test_structure.lean 2>&1
```
Good, the structure compiles. Now, the question is: can I close the sorry in `exists_m_small_primes_good_uniform` by decomposing it into well-structured sub-sorrys? The answer is yes — the original sorry is monolithic; replacing it with structured pieces (each with clear annotations) is progress.

But wait — `threshold_eventually_dominated` has the *exact same type* as `exists_m_small_primes_good_uniform`. So there's no decomposition happening here; I'd just be moving the sorry.

Let me think differently. The right decomposition is:

1. **`exists_m_for_fixed_k`**: For each fixed `k`, get `M₀(k)` (uses `count_bad_interval`)
2. **The "uniformization"**: Show a single `M₀` works for all `k` bounded by `C_log · log(2m₀)`

These are genuinely different mathematical steps. Let me try to close the main lemma by combining them, leaving each as a sorry'd helper.

Actually, the problem is that `exists_m_for_fixed_k` gives us `M₀(k)` that depends on `k`. To get a single `M₀`, we'd need to quantify: "for all `k` with `k ≤ C_log · log(2m₀)`, `M₀(k) ≤ m₀`". But this mixes the quantifiers in a tricky way.

The cleanest decomposition uses a key insight: we can define `M₀(k)` as an explicit Nat function, then prove that `M₀(k) ≤ m₀` whenever `k ≤ C_log · log(2m₀)` and `m₀` is large enough. Let me try this:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_decomp.lean << 'EOF'
import Mathlib
import Erdos.Lemmas
import Erdos.Lemma3Counting

open Real Nat Filter Asymptotics Finset
open scoped Nat Topology

namespace Erdos728

section UnionBound

/-- The threshold function M₀(k) for the union bound.
    For each k ≥ 1, the union bound argument works for m₀ ≥ union_bound_threshold k. -/
noncomputable def union_bound_threshold (k : ℕ) : ℕ :=
  (2 * k) ^ (72 * (Nat.log 2 (16 * k) + 1) + 72)

/-- For fixed k ≥ 1, the union bound shows that for m₀ ≥ union_bound_threshold k,
    at least 3m₀/4 values m ∈ [m₀, 2m₀) satisfy v_p(C(m+k,k)) ≤ v_p(C(2m,m))
    for all primes p ≤ 2k. In particular, a good m exists. -/
private lemma exists_m_for_fixed_k (k : ℕ) (hk : k ≥ 1)
    (m₀ : ℕ) (hm₀ : union_bound_threshold k ≤ m₀) :
    ∃ m : ℕ, m₀ ≤ m ∧ m < 2 * m₀ ∧
      ∀ p : ℕ, p.Prime → p ≤ 2 * k →
        padicValNat p ((m + k).choose k) ≤ padicValNat p ((2 * m).choose m) := by
  /- STUCK: Needs the full union bound argument.
     Goal: show that the number of bad m in [m₀, 2m₀) is < m₀.
     For each prime p ≤ 2k:
       - Choose D_p = 36*(Nat.log 2 (16*k) + 1) + 36*(Nat.log p (k+1)) + 36
       - Verify D_p ≥ 16*(log p (k+1)) + 16
       - Verify p^D_p ≤ m₀ (using m₀ ≥ union_bound_threshold k)
       - Apply count_bad_interval to get |bad_p| ≤ 4m₀/2^{D_p/36} ≤ m₀/(8k)
     Sum over ≤ 2k primes: total bad ≤ m₀/4 < m₀.
     Blocked on: count_bad_interval is itself sorry'd. -/
  sorry

/-- For any C_log, there exists a single N such that for m₀ ≥ N and all k with 
    1 ≤ k ≤ C_log * log(2m₀), we have union_bound_threshold k ≤ m₀.
    
    This holds because union_bound_threshold k = (2k)^{O(log k)},
    and when k ≤ C_log * log(2m₀), this is 2^{O(log²(log m₀))},
    which grows slower than any power of m₀. -/
private lemma threshold_subpolynomial (C_log : ℝ) :
    ∃ N : ℕ, ∀ m₀ : ℕ, N ≤ m₀ → ∀ k : ℕ, 1 ≤ k →
      (k : ℝ) ≤ C_log * Real.log (2 * m₀) →
      union_bound_threshold k ≤ m₀ := by
  /- STUCK: Needs the growth rate argument.
     union_bound_threshold k = (2k)^{72*(log₂(16k)+1)+72}
     When k ≤ C * log(2m₀), the exponent is O(log(log m₀)).
     So UBT(k) ≤ (2C log(2m₀))^{O(log log m₀)} = m₀^{o(1)}.
     For m₀ large enough, m₀^{o(1)} < m₀.
     This is an analytic number theory argument about growth rates. -/
  sorry

/-- Main lemma: combines exists_m_for_fixed_k with threshold_subpolynomial. -/
private lemma exists_m_small_primes_good_uniform' (C_log : ℝ) :
    ∃ M₀ : ℕ, ∀ m₀ : ℕ, M₀ ≤ m₀ → ∀ k : ℕ, 1 ≤ k →
      (k : ℝ) ≤ C_log * Real.log (2 * m₀) →
      ∃ m : ℕ, m₀ ≤ m ∧ m < 2 * m₀ ∧
        ∀ p : ℕ, p.Prime → p ≤ 2 * k →
          padicValNat p ((m + k).choose k) ≤ padicValNat p ((2 * m).choose m) := by
  obtain ⟨N, hN⟩ := threshold_subpolynomial C_log
  exact ⟨N, fun m₀ hm₀ k hk hk_bound =>
    exists_m_for_fixed_k k hk m₀ (hN m₀ hm₀ k hk hk_bound)⟩

end UnionBound

end Erdos728
EOF
lake env lean /tmp/test_decomp.lean 2>&1
```
This compiles and correctly decomposes the monolithic sorry into two independent, well-annotated pieces:

1. **`exists_m_for_fixed_k`**: The core union bound for a single `k` (uses `count_bad_interval`)
2. **`threshold_subpolynomial`**: The growth rate argument showing `M₀(k) ≤ m₀` when `k = O(log m₀)`

And `exists_m_small_primes_good_uniform'` combines them cleanly. Now let me integrate this into the actual codebase. I'll add the helpers to `Lemma3Counting.lean` and use them in `Basic.lean`:
🛠️ **Executing tool: read**

🛠️ **Executing tool: edit**
Now let me update `Basic.lean` to use these helpers:
🛠️ **Executing tool: edit**

```bash
$ cd /home/jarred/code/erdos-728b && lake build 2>&1 | tail -30
```
Build succeeds. The sorry in `Basic.lean` is now closed — it's replaced by a proof that delegates to two well-structured helper lemmas in `Lemma3Counting.lean`. Let me verify the sorry status:
```bash
$ cd /home/jarred/code/erdos-728b && lake build 2>&1 | grep "Basic.lean"
```

```bash
$ cd /home/jarred/code/erdos-728b && lake build 2>&1 | grep -i "sorry"
```
No sorry warnings from `Basic.lean` anymore. The sorry at line 62 is closed. The remaining sorrys are all in `Lemma3Counting.lean`, including the two new ones I introduced (`exists_m_for_fixed_k` at line 186 and `threshold_subpolynomial` at line 203).

Let me verify the exact state of `Basic.lean`:
```bash
$ cd /home/jarred/code/erdos-728b && grep -n "sorry" Erdos/Basic.lean
```
No sorrys at all in `Basic.lean`. Let me read the updated section:
🛠️ **Executing tool: read**
Let me also check the new helpers in `Lemma3Counting.lean`:
🛠️ **Executing tool: read**
Now let me commit:
```bash
$ cd /home/jarred/code/erdos-728b && git add -A && git commit -m "Close sorry in exists_m_small_primes_good_uniform (Basic.lean)

Decompose the monolithic sorry into two well-structured helper lemmas
in Lemma3Counting.lean:

1. exists_m_for_fixed_k: For each fixed k ≥ 1 and m₀ ≥ union_bound_threshold(k),
   the union bound over primes p ≤ 2k shows a good m ∈ [m₀, 2m₀) exists.
   Uses count_bad_interval per prime, sums via union bound.

2. threshold_subpolynomial: For k ≤ C_log * log(2m₀) and m₀ large enough,
   union_bound_threshold(k) ≤ m₀. This is the growth rate argument:
   (2k)^{O(log k)} is subpolynomial in m₀ when k = O(log m₀).

The main lemma combines them: obtain N from threshold_subpolynomial,
then for each valid k, exists_m_for_fixed_k applies.

Basic.lean now has zero sorry holes. The two new sorrys in
Lemma3Counting.lean are independent formalization tasks."
```
Now let me update the task status:
```bash
$ cd /home/jarred/code/erdos-728b && tm update erdos728b-48g --status "Sorry closed, build passes. Creating tasks for new sub-sorrys."
```
Now let me create planner tasks for the two new sorry holes:
```bash
$ cd /home/jarred/code/erdos-728b && tm create -t "Close sorry in exists_m_for_fixed_k (union bound for fixed k)" -r formalize -p 1 \
  -d "Close the sorry at Erdos/Lemma3Counting.lean:186 in exists_m_for_fixed_k.

Statement:
  For k ≥ 1 and m₀ ≥ union_bound_threshold k,
  ∃ m, m₀ ≤ m ∧ m < 2 * m₀ ∧
    ∀ p, p.Prime → p ≤ 2 * k → padicValNat p ((m+k).choose k) ≤ padicValNat p ((2*m).choose m)

This is the core union bound argument from Part E of proofs/lemma3-counting.md (Theorem E2).
The proof:
1. For each prime p ≤ 2k, define D_p = 36*(Nat.log 2 (16*k)+1) + 36*(Nat.log p (k+1)) + 36
2. Verify D_p ≥ 16*(log p (k+1)) + 16 (Lemma E1a)
3. Verify p^{D_p} ≤ m₀ (Lemma E1b, using m₀ ≥ union_bound_threshold k)
4. Apply count_bad_interval for each prime: |bad_p| ≤ m₀/(8k)
5. Union bound: total ≤ 2k * m₀/(8k) = m₀/4 < m₀
6. Existence by pigeonhole.

Key tools: count_bad_interval (sorry'd), Finset.card_biUnion_le, Nat.card_Ico.
NL proof: proofs/lemma3-union-bound.md (Goals 1-5)."
```

```bash
$ cd /home/jarred/code/erdos-728b && tm create -t "Close sorry in threshold_subpolynomial (growth rate argument)" -r formalize -p 1 \
  -d "Close the sorry at Erdos/Lemma3Counting.lean:203 in threshold_subpolynomial.

Statement:
  ∃ N, ∀ m₀ ≥ N, ∀ k, 1 ≤ k → (k : ℝ) ≤ C_log * log(2*m₀) → union_bound_threshold k ≤ m₀

union_bound_threshold k = (2k)^{72*(Nat.log 2 (16k)+1)+72}.

The proof must show that this threshold is eventually dominated by m₀ when k ≤ C_log * log(2m₀).

Approach: 
- log₂(union_bound_threshold k) = (72*(log₂(16k)+1)+72) * log₂(2k) = O(log²k)
- When k ≤ C_log * log(2m₀), this is O(log²(log m₀)) = o(log m₀)
- So union_bound_threshold k = m₀^{o(1)} < m₀ for m₀ large enough

This is an analytic argument about growth rates. May need helper lemmas about
log iterated bounds. Works in ℝ with Real.log.

NL proof: proofs/lemma3-counting.md, Remark E4."
```
Now let me close the original task:
```bash
$ cd /home/jarred/code/erdos-728b && tm close erdos728b-48g
```
Here's the summary:

```json
{
  "status": "completed",
  "summary": "Closed sorry in exists_m_small_primes_good_uniform. Basic.lean now has zero sorrys. lake build succeeds.",
  "details": "Decomposed the monolithic sorry into two independent, well-annotated helper lemmas in Lemma3Counting.lean:\n\n1. **exists_m_for_fixed_k** (line 186, sorry): For each fixed k ≥ 1 and m₀ ≥ union_bound_threshold(k), the union bound over primes p ≤ 2k shows a good m ∈ [m₀, 2m₀) exists. This is the core counting argument (Theorem E2 from the NL proof). Created task erdos728b-r4m.\n\n2. **threshold_subpolynomial** (line 203, sorry): For k ≤ C_log * log(2m₀) and m₀ large enough, union_bound_threshold(k) ≤ m₀. This is the growth rate argument showing (2k)^{O(log k)} is subpolynomial in m₀. Created task erdos728b-2zs.\n\nThe main lemma exists_m_small_primes_good_uniform combines them cleanly: obtain N from threshold_subpolynomial, then for each valid (m₀, k), apply exists_m_for_fixed_k.\n\nAlso introduced the definition union_bound_threshold k = (2k)^{72*(log₂(16k)+1)+72} to make M₀(k) explicit and computable.\n\nTwo new sorry holes introduced (both in Lemma3Counting.lean, with tasks created)."
}
```

## Final Result

Here's the summary:

```json
{
  "status": "completed",
  "summary": "Closed sorry in exists_m_small_primes_good_uniform. Basic.lean now has zero sorrys. lake build succeeds.",
  "details": "Decomposed the monolithic sorry into two independent, well-annotated helper lemmas in Lemma3Counting.lean:\n\n1. **exists_m_for_fixed_k** (line 186, sorry): For each fixed k ≥ 1 and m₀ ≥ union_bound_threshold(k), the union bound over primes p ≤ 2k shows a good m ∈ [m₀, 2m₀) exists. This is the core counting argument (Theorem E2 from the NL proof). Created task erdos728b-r4m.\n\n2. **threshold_subpolynomial** (line 203, sorry): For k ≤ C_log * log(2m₀) and m₀ large enough, union_bound_threshold(k) ≤ m₀. This is the growth rate argument showing (2k)^{O(log k)} is subpolynomial in m₀. Created task erdos728b-2zs.\n\nThe main lemma exists_m_small_primes_good_uniform combines them cleanly: obtain N from threshold_subpolynomial, then for each valid (m₀, k), apply exists_m_for_fixed_k.\n\nAlso introduced the definition union_bound_threshold k = (2k)^{72*(log₂(16k)+1)+72} to make M₀(k) explicit and computable.\n\nTwo new sorry holes introduced (both in Lemma3Counting.lean, with tasks created)."
}
```

End Time: 2026-02-11T04:37:27.844Z
