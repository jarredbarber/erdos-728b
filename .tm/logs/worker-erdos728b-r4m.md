# timtam Task: Close sorry in exists_m_for_fixed_k (union bound for fixed k) (erdos728b-r4m)

Role: formalize
Agent: formalize (google-antigravity/claude-opus-4-6-thinking)
Start Time: 2026-02-11T06:37:41.369Z

## Agent Interaction



> **Thinking:**
> Let me start by understanding the task. I need to close a `sorry` in `exists_m_for_fixed_k` in `Erdos/Lemma3Counting.lean`. Let me first read the relevant files to understand the current state.


```bash
$ cd /home/jarred/code/erdos-728b && tm update erdos728b-r4m --status "Reading source files and understanding the problem"
```

🛠️ **Executing tool: read**
Let me read the NL proof for context:
```bash
$ ls /home/jarred/code/erdos-728b/proofs/
```

🛠️ **Executing tool: read**
Now let me understand the current state better. Let me look at the existing `count_bad_interval` signature and other relevant definitions:
```bash
$ cd /home/jarred/code/erdos-728b && grep -n "union_bound_threshold\|exists_m_for_fixed_k\|count_bad_interval\|D_p_for_prime" Erdos/Lemma3Counting.lean | head -40
```

🛠️ **Executing tool: read**

🛠️ **Executing tool: read**
Now I need to understand the overall proof strategy. The key steps are:

1. For each prime p ≤ 2k, define D_p = 36*(Nat.log 2 (16*k)+1) + 36*(Nat.log p (k+1)) + 36
2. Verify D_p ≥ 16*(log p (k+1)) + 16
3. Verify p^{D_p} ≤ m₀
4. Apply count_bad_interval for each prime
5. Union bound summing over primes
6. Pigeonhole for existence

This is a complex proof. Let me start building it step by step:
```bash
$ cd /home/jarred/code/erdos-728b && tm update erdos728b-r4m --status "Building proof structure for exists_m_for_fixed_k"
```
Let me first check what Lean API tools are available for dealing with primes and Finset filtering:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_api.lean << 'EOF'
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Fintype.BigOperators

#check Finset.card_Ico
#check Nat.card_Ico
#check Finset.card_biUnion_le
#check Finset.card_filter_le_iff
#check Nat.pow_le_pow_left
#check Nat.log_mono_right
#check Nat.pow_log_le_self
#check Nat.lt_pow_succ_log_self
EOF
lake env lean /tmp/test_api.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_api2.lean << 'EOF'
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Filter.Basic

-- Need to find: how to get a Finset of primes ≤ 2k
#check Finset.filter
-- Finset.range (2*k+1) |>.filter Nat.Prime

-- For the existence argument: pigeonhole / card argument
-- If total bad < m₀ = |[m₀, 2m₀)|, then ∃ good m.
-- This is essentially: if |S| < |T| then T \ S ≠ ∅
#check Finset.exists_mem_of_ne_empty
#check Finset.card_sdiff_le
#check Finset.exists_of_card_lt_card

-- For the summation
#check Finset.sum_le_sum
#check Finset.sum_const
#check Finset.card_le_card
EOF
lake env lean /tmp/test_api2.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_api3.lean << 'EOF'
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Fintype.BigOperators

-- Existence from card argument
#check Finset.card_pos
#check Finset.Nonempty.exists_eq
#check Finset.card_sdiff
#check Finset.sdiff_nonempty
-- If bad ⊆ [m₀, 2m₀) and |bad| < |[m₀, 2m₀)| then ∃ good ∈ [m₀, 2m₀)\bad
-- Actually let's think about this differently: we have the complement
-- We want to show: if A ⊆ S and |A| < |S|, then S \ A is nonempty
-- Finset.sdiff_nonempty : s \ t ≠ ∅ ↔ ¬s ⊆ t 
-- Hmm. Let me think about the right approach.

-- Actually: union of bad sets for each prime has card < m₀ 
-- So there exists an element in Ico m₀ (2*m₀) not in the union.
-- This is: card(biUnion) < card(Ico) → ∃ m ∈ Ico, m ∉ biUnion

-- Let's just use the fact that if A ⊂ B then B \ A is nonempty 
#check Finset.card_lt_card
-- card_lt_card : s ⊂ t → s.card < t.card   (wrong direction)

-- We need: |A| < |S| and A ⊆ S → S \ A nonempty
-- This follows from card_sdiff_add_card_eq_card
-- Or just: by_contra and show card S ≤ card A

-- Actually the simplest: if card (filter P S) < card S, then ∃ m ∈ S, ¬P m
#check Finset.exists_not_of_card_lt_card
EOF
lake env lean /tmp/test_api3.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && grep -r "card_filter.*card" .lake/packages/mathlib/Mathlib/Data/Finset/Card.lean 2>/dev/null | head -10
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_api4.lean << 'EOF'
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Fintype.BigOperators

-- For the existence argument, the simplest approach:
-- The bad set B ⊆ Ico m₀ (2*m₀), |B| ≤ m₀/4 < m₀ = |Ico m₀ (2*m₀)|
-- So by_contra: if ∀ m ∈ Ico, bad m, then |B| = |Ico| = m₀, contradiction

-- Or: define good = Ico \ bad. card good = card Ico - card bad ≥ m₀ - m₀/4 > 0
-- So good is nonempty.

-- Let me check what's available for union bound on filter card
#check Finset.card_biUnion_le -- (s.biUnion t).card ≤ ∑ a ∈ s, (t a).card
#check Finset.card_filter_le -- card (filter p s) ≤ card s

-- The approach: define Bad_p = {m ∈ Ico | v_p(C(m+k,k)) > v_p(C(2m,m))} for each p
-- The overall bad set is ⋃_p Bad_p  
-- Bound |⋃_p Bad_p| ≤ Σ_p |Bad_p| ≤ 2k · m₀/(8k) = m₀/4

-- Actually I realize: we don't even need to form a union. We just need:
-- If ∀ p (prime, ≤ 2k), |{m ∈ Ico | bad_p(m)}| ≤ m₀/(8k)
-- Then |{m ∈ Ico | ∃ p prime, p ≤ 2k, bad_p(m)}| ≤ Σ_p |Bad_p| ≤ 2k · m₀/(8k) = m₀/4
-- So there exists m ∈ Ico not bad for any p.

-- Let me try a simpler approach: by_contra, then for each m in Ico, 
-- ∃ p such that bad_p(m), which gives m ∈ ⋃ Bad_p, so Ico ⊆ ⋃ Bad_p,
-- contradiction with |⋃ Bad_p| ≤ m₀/4 < m₀ = |Ico|.

-- Or just: define bad set as filter of Ico, bound its card, then 
-- use card_sdiff or card argument.

-- For the union bound:
example (s : Finset ℕ) (f : ℕ → Finset ℕ) :
    (s.biUnion f).card ≤ ∑ a ∈ s, (f a).card := Finset.card_biUnion_le

-- We need: for s = {p ≤ 2k | p.Prime}, the biUnion of Bad_p sets
-- Actually, the filter (∃ p bad) on Ico is ⊆ biUnion of filters.

-- Let me just check a simpler thing:
-- How to get "there exists m in a Finset" from Finset.card_pos
example (s : Finset ℕ) (h : 0 < s.card) : ∃ m, m ∈ s := by
  exact Finset.card_pos.mp h |>.exists

EOF
lake env lean /tmp/test_api4.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_api5.lean << 'EOF'
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Fintype.BigOperators

example (s : Finset ℕ) (h : 0 < s.card) : ∃ m, m ∈ s := by
  exact Finset.card_pos.mp h

-- Nonempty to exists
example (s : Finset ℕ) (h : s.Nonempty) : ∃ m, m ∈ s := h

-- Good. Now let me understand the proof plan better.
-- The key is: bad_union = filter (fun m => ∃ p, p.Prime ∧ p ≤ 2k ∧ v_p(C(m+k,k)) > v_p(C(2m,m))) Ico
-- bad_union ⊆ biUnion of bad_p sets
-- card(biUnion) ≤ Σ card(bad_p) ≤ Σ m₀/(8k) ≤ 2k * m₀/(8k) = m₀/4
-- So card(filter) ≤ m₀/4 < m₀ = card(Ico)
-- So Ico \ filter is nonempty, giving a good m.

-- For p=2 we need special handling since count_bad_interval needs p ≥ 3.
-- Wait, let me check if count_bad_interval requires p ≥ 3...
-- Yes, it has hp_ge_3 : p ≥ 3.
-- But for p=2, the NL proof doesn't distinguish. Let me check if k ≥ 1 
-- means we always have primes ≤ 2k that include p=2.
-- Actually for p=2: we need a different treatment.
-- Hmm, but actually looking at the signature of count_bad_single_prime 
-- and count_bad_interval, they both require hp_ge_3 : p ≥ 3.

-- So for p = 2 we need something different.
-- Actually wait - maybe the count_few_high_digits requires p ≥ 3.
-- For p = 2, probHigh p = p/2/p = 1/2, and the Chernoff bound may work differently.
-- Let me check if the lemma is even needed for p=2...

-- For p=2 and k ≥ 1: v_2(C(m+k,k)) ≤ v_2(C(2m,m))?
-- Actually by Kummer's theorem, v_2(C(2m,m)) counts carries in m+m in base 2.
-- And v_2(C(m+k,k)) counts carries in m+k in base 2... 
-- Hmm, this isn't automatically true. We still need the counting argument.
-- But count_bad_interval requires p ≥ 3...

-- Let me look more carefully at what happens for p=2.
EOF
lake env lean /tmp/test_api5.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && grep -n "hp_ge_3\|p ≥ 3\|p >= 3" Erdos/Lemma3Counting.lean
```
So `count_bad_interval` requires `p ≥ 3`. This means we need to handle `p = 2` separately. Let me think about what the NL proof says...

The NL proof says "for each prime p ≤ 2k, define D_p..." It doesn't distinguish p=2. But the formalization has `hp_ge_3 : p ≥ 3` on `count_bad_interval`. 

Let me check: does the `count_few_high_digits` lemma actually need `p ≥ 3`? It's about the probability of high digits. For `p = 2`, a "high digit" in base 2 means digit ≥ p/2 = 1, which means every nonzero digit is "high". The Chernoff argument might still work but the probHigh calculation might differ.

Actually, looking more carefully, the `count_bad_interval` requires `p ≥ 3` because `count_few_high_digits` requires it. We need a version for p=2, or we need to handle p=2 specially.

Wait - actually for p=2, the "high digit" condition means digit = 1 (since p/2 = 1). So every digit that's 1 is "high". The fraction of high digits is about 1/2 for random m. The Chernoff bound should work even better. But the code uses `hp_ge_3`.

Let me look at why `count_few_high_digits` needs `p ≥ 3`:
🛠️ **Executing tool: read**
The `hp_ge_3` is used in `count_few_high_digits` specifically for the `probHigh` bound. For p=2, `probHigh 2 = (2/2)/2 = 1/2`, and the bound `probHigh p ≥ 1/3` still holds. Let me check why it needs p≥3...
```bash
$ cd /home/jarred/code/erdos-728b && sed -n '440,465p' Erdos/Lemma3Counting.lean
```
I see - the `p / 2 * 3 ≥ p` step. For p=2: `2/2 * 3 = 3 ≥ 2`. That's actually true! So `p ≥ 3` might not be strictly needed. But for p=2, the omega proof `p / 2 * 3 ≥ p` is `1 * 3 = 3 ≥ 2` ✓. 

Wait, let me check this more carefully:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_p2.lean << 'EOF'
import Mathlib

example : (2 : ℕ) / 2 * 3 ≥ 2 := by omega
example (p : ℕ) (hp : p.Prime) : p / 2 * 3 ≥ p := by
  have := hp.two_le
  omega
EOF
lake env lean /tmp/test_p2.lean 2>&1
```
So `p / 2 * 3 ≥ p` works for all primes (since p ≥ 2). The `hp_ge_3` restriction might be unnecessary. But I shouldn't modify existing lemmas — I should work with what's available.

So the approach is: for p=2, I need to handle it separately in the union bound. Actually, wait — does the problem even have primes p with p=2? If k ≥ 1, then 2k ≥ 2, so p=2 is always relevant.

Let me think about this differently. For the `exists_m_for_fixed_k` proof, I need to show for ALL primes p ≤ 2k. The `count_bad_interval` only works for p ≥ 3. So either:
1. I handle p=2 separately with a different bound
2. I extend `count_bad_interval` to work for p=2
3. I create a wrapper lemma that works for all primes

Actually, let me re-read count_bad_interval more carefully. It calls `count_few_high_digits` which needs `hp_ge_3`. The issue is downstream. Let me see if I can create a version for p ≥ 2 (all primes).

Actually, the cleanest approach for now is to create a version of `count_bad_interval` that works for p=2 as well. But that requires modifying or extending `count_few_high_digits`. This could be complex.

Alternatively, I could create the proof with a sorry for the p=2 case. But wait—let me first check if the `count_few_high_digits` proof actually uses `hp_ge_3` in an essential way, or if it's just there unnecessarily:
```bash
$ cd /home/jarred/code/erdos-728b && grep -n "hp_ge_3" Erdos/Lemma3Counting.lean
```
So `hp_ge_3` propagates from `count_few_high_digits` → `count_bad_single_prime` → `count_bad_interval`. The key question is: does the proof of `count_few_high_digits` really need `p ≥ 3`?

Looking at the proof, `hp_ge_3` is used in the `omega` proof: `p / 2 * 3 ≥ p`. But we just showed this works for p ≥ 2 (all primes). So the `hp_ge_3` condition is not actually necessary — it could be weakened to `hp : p.Prime` alone. However, modifying existing compiled lemmas is risky and I shouldn't do that.

Instead, I'll take a pragmatic approach: 

For the `exists_m_for_fixed_k` proof, I can handle p=2 with a dedicated approach. But actually, a simpler idea: can I just create a lemma `count_bad_interval_all_primes` that extends the result to all primes? For p=2, I would need the analogous counting argument.

Actually, looking at this more carefully, I think the right approach is much simpler. Let me just focus on the structure of `exists_m_for_fixed_k`:

1. For each prime p ≤ 2k, define D_p 
2. Show the bad set for that prime has card ≤ m₀/(8k)
3. Union bound: total bad ≤ (2k) · m₀/(8k) = m₀/4
4. Existence

For step 2, I use `count_bad_interval` which requires p ≥ 3. For p = 2, I need a separate argument or I can create a wrapper. Let me check if there are any primes ≤ 2 when k ≥ 1 — yes, p=2 is always such a prime. But actually, for k = 1, 2k = 2, and p=2 is the only prime.

Let me think about whether `count_bad_interval` for p=2 could be proved separately. The key issue is that `count_few_high_digits` uses the fact that the probability of a high digit is ≥ 1/3, which holds for p ≥ 2. The proof at line 460 shows `p / 2 * 3 ≥ p` which omega verifies for all p ≥ 2.

I think the safest approach is to create a version of `count_few_high_digits` that works for all primes (without `hp_ge_3`), then lift `count_bad_interval` similarly. Let me do this in a helper lemma.

Actually wait — I realize I can take an even simpler approach. Rather than modifying the chain, I can just prove a direct version of `count_bad_interval` for all primes by copying the key parts. But that's a lot of code.

Alternatively, the simplest approach: use `sorry` for the parts I can't close and leave a clear annotation. But the task says to close the sorry in `exists_m_for_fixed_k`.

Let me think about this more carefully. Maybe I should just prove versions of the needed lemmas without the `p ≥ 3` restriction. Let me check how much of the proof chain I'd need to copy.

Actually, let me take the simplest approach: prove `count_few_high_digits` for all primes (p ≥ 2) as a new lemma, then derive `count_bad_interval` for all primes:
```bash
$ cd /home/jarred/code/erdos-728b && tm update erdos728b-r4m --status "Creating helper lemmas for p=2 case, then building union bound proof"
```
Let me first check if `count_few_high_digits` is actually used with a `p ≥ 3` that is non-trivially needed (maybe for `probHigh`):
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_few_high.lean << 'EOF'
import Mathlib.Data.Nat.Prime.Defs

-- For p ≥ 2 (all primes): p / 2 * 3 ≥ p
-- p=2: 1*3=3 ≥ 2 ✓
-- p=3: 1*3=3 ≥ 3 ✓ 
-- p=5: 2*3=6 ≥ 5 ✓
-- etc.
example (p : ℕ) (hp : p ≥ 2) : p / 2 * 3 ≥ p := by omega
EOF
lake env lean /tmp/test_few_high.lean 2>&1
```
Good. The `p ≥ 3` condition is unnecessary. Let me now create the extended version. I'll add new lemmas to the file and then write the main proof:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_count_few.lean << 'EOF'
import Mathlib.Data.Nat.Prime.Defs

-- Check: can I prove count_few_high_digits without p ≥ 3?
-- The issue is the probHigh bound. Let me check.
-- probHigh p ≥ 1/3 for all p ≥ 2 because p/2 * 3 ≥ p for all p ≥ 2.
-- So we just need hp.Prime (which gives p ≥ 2).

-- But I don't want to duplicate the whole proof. Instead, let me just 
-- add a wrapper that derives count_bad_interval for all primes.
-- For p = 2, I need to verify p ≥ 3 or provide an alternative.
-- Since p = 2 < 3, I can't use the existing lemma directly.

-- Strategy: create count_few_high_digits_all and count_bad_interval_all
-- that work for all primes. For p ≥ 3, delegate to existing lemmas.
-- For p = 2, I need to prove it directly. But the proof is essentially 
-- the same as the p ≥ 3 case since probHigh 2 = 1/2 ≥ 1/3.

-- Actually, the simplest approach is to just prove a lemma:
-- count_few_high_digits' : same as count_few_high_digits but without hp_ge_3
-- by observing that the omega proof works for p ≥ 2.
-- But I can't modify the existing lemma. Can I create a new one?

-- YES. I can just prove it for p = 2 directly (by checking the bound holds)
-- and then combine with the existing p ≥ 3 case.
EOF
lake env lean /tmp/test_count_few.lean 2>&1
```
OK let me take a step back and think about the best approach. The proof has many steps. Let me build it incrementally, leaving `sorry`s where needed, and see how far I can get. I'll write the proof in layers.

Let me write the full proof outline first:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_main.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset Real

-- Testing if count_bad_interval exists with the right signature
#check @Erdos728.count_bad_interval
EOF
lake env lean /tmp/test_main.lean 2>&1
```
Good. Now let me plan the proof. The key issue is handling all primes including p=2. Let me just create a wrapper that handles p ≥ 3 via the existing lemma, and for p=2 we need something.

Actually, I just realized — maybe I don't need `count_bad_interval` to handle p=2 at all. The NL proof says the "bad count for each prime" is bounded. For p=2, the bound would be the same. But we need the formal tool.

Let me take a different approach: instead of trying to handle p=2, let me see if I can just create a `count_bad_interval_prime` that works for all primes by factoring out the `p ≥ 3` condition. The key insight is that `count_few_high_digits` only uses `p ≥ 3` for the `probHigh p ≥ 1/3` bound, which holds for all primes.

Let me create helper lemmas:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_structure.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset Real Erdos728

-- Approach: for the union bound, I need count_bad_interval for all primes.
-- For p ≥ 3, I use the existing lemma.
-- For p = 2, I need a separate proof.

-- Let me first check if I can prove count_few_high_digits for p = 2.
-- Actually, the proof is identical - the key step is probHigh p ≥ 1/3,
-- and probHigh 2 = (2/2)/2 = 1/2 ≥ 1/3.

-- Let me try a different approach: avoid the per-prime decomposition and 
-- just directly prove the union bound.

-- Actually, let me see what happens if I use count_bad_interval only for p ≥ 3
-- and handle the p = 2 case with sorry for now.

-- Better approach: create count_bad_interval_all that works for all primes.
-- For p ≥ 3, delegate to count_bad_interval.
-- For p = 2, prove it directly (the proof is the same, just omega can handle p/2*3 ≥ p for p=2).

-- Actually, the simplest: just create a wrapper.
lemma count_bad_interval_all {p : ℕ} (D k m0 : ℕ)
    (hm0 : m0 ≥ p^D) (hD : D ≥ 16 * (log p (k + 1)) + 16)
    (hp : p.Prime) (hk : k ≥ 1) :
    ((Ico m0 (2 * m0)).filter (fun m => padicValNat p ((m + k).choose k) > padicValNat p ((2 * m).choose m))).card
    ≤ (2 * m0) / 2 ^ (D / 36) + (2 * p^D) / 2 ^ (D / 36) := by
  by_cases hp3 : p ≥ 3
  · exact count_bad_interval D k m0 hm0 hD hp hp3 hk
  · -- p is prime and p < 3, so p = 2
    have hp2 : p = 2 := by
      have := hp.two_le; omega
    subst hp2
    -- Need to prove for p = 2.
    -- The proof follows the same structure as count_bad_interval
    -- but we need count_few_high_digits for p = 2.
    sorry

EOF
lake env lean /tmp/test_structure.lean 2>&1
```
Good, the structure works. Now, for p=2, the proof is essentially identical to the p ≥ 3 case. The only issue is `count_few_high_digits` needing `p ≥ 3`. Let me check if I can just prove the result for p=2 by replicating the key steps or finding an alternative bound.

Actually, let me try a completely different approach: can I just create `count_few_high_digits_p2` for p=2? For p=2, `probHigh 2 = 1/2`, high digits are those ≥ 1 (i.e., digit = 1). In base 2, about half the digits should be 1. The Chernoff bound gives an even stronger result.

But actually, replicating the whole proof for p=2 is a lot of work. Let me instead just prove `count_few_high_digits` without `p ≥ 3` since the condition is unnecessary:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_cfhd.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset Real Erdos728

-- Prove count_few_high_digits for all primes (including p=2)
-- by exactly replicating the proof but using hp.two_le instead of hp_ge_3
lemma count_few_high_digits' {p : ℕ} (D : ℕ) (hp : p.Prime) (t : ℕ) (ht : t ≤ D/6) :
    ((range (p^D)).filter (fun m => count_high_digits p m D < t)).card ≤
    p^D / 2^(D/36) := by
  by_cases hp3 : p ≥ 3
  · exact count_few_high_digits D hp t ht hp3
  · -- p = 2
    have hp2 : p = 2 := by have := hp.two_le; omega
    subst hp2
    -- Handle trivial case t = 0
    by_cases ht0 : t = 0
    · simp [ht0]
    have ht_pos : t ≥ 1 := Nat.pos_of_ne_zero ht0
    have hD_ge_6 : D ≥ 6 := by omega
    have hD_pos : D > 0 := by omega
    -- Transfer from range to DigitSpace
    have h_card_eq_fin :
        ((range (2^D)).filter (fun m => count_high_digits 2 m D < t)).card =
        ((Finset.univ : Finset (Fin (2^D))).filter
          (fun m : Fin (2^D) =>
            count_high_digits 2 m.val D < t)).card := by
      apply Finset.card_bij
        (fun m hm => ⟨m, by rw [mem_filter] at hm; exact mem_range.mp hm.1⟩)
      · intro m hm; rw [mem_filter] at hm ⊢; exact ⟨mem_univ _, hm.2⟩
      · intro a _ b _ h; simp at h; exact h
      · intro b hb; refine ⟨b.val, ?_, Fin.ext rfl⟩
        rw [mem_filter]
        exact ⟨mem_range.mpr b.isLt, (mem_filter.mp hb).2⟩
    have h_card_eq_ds :
        ((Finset.univ : Finset (Fin (2^D))).filter
          (fun m : Fin (2^D) =>
            count_high_digits 2 m.val D < t)).card =
        ((Finset.univ : Finset (DigitSpace D 2)).filter
          (fun m : DigitSpace D 2 => highDigitCount m < t)).card := by
      have hbij := toDigitSpace_bijective (Nat.prime_iff.mpr ⟨by omega, by intro m hm; omega⟩) D
      apply Finset.card_bij (fun m _ => toDigitSpace (Nat.prime_iff.mpr ⟨by omega, by intro m hm; omega⟩) D m)
      · intro m hm; rw [mem_filter] at hm ⊢
        exact ⟨mem_univ _,
          by rw [highDigitCount_eq (Nat.prime_iff.mpr ⟨by omega, by intro m hm; omega⟩) D m]; exact hm.2⟩
      · intro a _ b _ h; exact hbij.1 h
      · intro b hb; obtain ⟨a, ha⟩ := hbij.2 b
        refine ⟨a, ?_, ha⟩; rw [mem_filter]
        exact ⟨mem_univ _, by
          rw [← highDigitCount_eq (Nat.prime_iff.mpr ⟨by omega, by intro m hm; omega⟩) D a, ha]
          exact (mem_filter.mp hb).2⟩
    sorry

EOF
lake env lean /tmp/test_cfhd.lean 2>&1
```
The approach of `Nat.prime_iff.mpr` is too complex. Let me use a simpler approach — just use `hp` directly since `hp : Nat.Prime 2` after substitution:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_cfhd2.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset Real Erdos728

-- Instead of duplicating the whole proof, let me try the simplest approach:
-- Just provide count_few_high_digits with p=2 using a direct argument

-- Actually, the simplest approach is to observe that the existing proof
-- only uses hp_ge_3 for the omega step p / 2 * 3 ≥ p, which holds for p=2.
-- So let me just create a version for all primes that delegates:

private lemma count_few_high_digits_all {p : ℕ} (D : ℕ) (hp : p.Prime) (t : ℕ) (ht : t ≤ D/6) :
    ((range (p^D)).filter (fun m => count_high_digits p m D < t)).card ≤
    p^D / 2^(D/36) := by
  by_cases hp3 : p ≥ 3
  · exact count_few_high_digits D hp t ht hp3
  · -- p = 2 case
    interval_cases p  -- p must be 2 since it's prime and < 3
    -- Now p = 2. The bound holds because count_high_digits counts digits ≥ p/2 = 1,
    -- which is about half the digits. With Chernoff, few have < D/6 high digits.
    -- For now, we use a direct counting argument.
    sorry

EOF
lake env lean /tmp/test_cfhd2.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_cfhd3.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset Real Erdos728

private lemma count_few_high_digits_all {p : ℕ} (D : ℕ) (hp : p.Prime) (t : ℕ) (ht : t ≤ D/6) :
    ((range (p^D)).filter (fun m => count_high_digits p m D < t)).card ≤
    p^D / 2^(D/36) := by
  by_cases hp3 : p ≥ 3
  · exact count_few_high_digits D hp t ht hp3
  · -- p < 3 and p is prime, so p = 2
    have hp2 : p = 2 := by have := hp.two_le; omega
    subst hp2
    -- For p = 2: 2^D / 2^(D/36) = 2^(D - D/36)
    -- count_high_digits with p=2 counts digits ≥ 1, i.e., all 1-digits.
    -- In base 2, a random number has ~D/2 digits equal to 1.
    -- We need #{m < 2^D : count_high_digits 2 m D < t} ≤ 2^D / 2^(D/36)
    -- where t ≤ D/6.
    -- 
    -- This follows from the Chernoff bound since probHigh 2 = 1/2 ≥ 1/3,
    -- and the same proof works as for p ≥ 3.
    -- 
    -- The existing proof of count_few_high_digits only uses hp_ge_3 for
    -- the step "p / 2 * 3 ≥ p" which holds for p = 2 as well.
    -- We reproduce the key steps:
    by_cases ht0 : t = 0
    · simp [ht0]
    have ht_pos : t ≥ 1 := Nat.pos_of_ne_zero ht0
    have hD_ge_6 : D ≥ 6 := by omega
    have hD_pos : D > 0 := by omega
    -- The filter on range(2^D) is bounded by the filter on DigitSpace
    -- via toDigitSpace bijection, which then uses Chernoff.
    -- Key fact: probHigh 2 = 1/2 ≥ 1/3
    -- So D * probHigh 2 = D/2 > D/6 ≥ t
    -- Chernoff gives card ≤ 2^D * exp(-2*(D/2 - t)^2/D) 
    -- ≤ 2^D * exp(-D/18) ≤ 2^D / 2^(D/36)
    --
    -- For the formal proof, this exactly mirrors count_few_high_digits.
    -- Since the only use of hp_ge_3 is in the omega step, we can just do it:
    
    -- Actually let me just apply the Chernoff route directly
    sorry

EOF
lake env lean /tmp/test_cfhd3.lean 2>&1
```
OK, let me take a completely different strategy. Rather than trying to prove `count_few_high_digits` for p=2 (which requires duplicating 100+ lines of Chernoff bound machinery), let me look at the problem from the top down and see what's the minimal change needed.

The simplest approach: I can just add a new version of `count_bad_interval` that works for all primes. For p ≥ 3, it delegates. For p = 2, I can provide the bound with a `sorry` and annotate it. But actually the goal is to close the sorry in `exists_m_for_fixed_k`, not necessarily close all sub-sorrys.

Let me think about this differently. Can I prove `exists_m_for_fixed_k` with the existing tools, perhaps by splitting the primes into p=2 and p≥3?

Actually, let me re-read the proof more carefully. The approach is:
1. For each prime p ≤ 2k, count bad m in [m₀, 2m₀) with `count_bad_interval`
2. Each has count ≤ m₀/(8k)  
3. Union bound: total ≤ 2k · m₀/(8k) = m₀/4
4. So there exists a good m

For the union bound, I form the union of all bad sets. The bad set for prime p is `{m ∈ Ico m₀ (2*m₀) | v_p(C(m+k,k)) > v_p(C(2m,m))}`.

The full bad set is `{m ∈ Ico m₀ (2*m₀) | ∃ p, p.Prime ∧ p ≤ 2k ∧ v_p(C(m+k,k)) > v_p(C(2m,m))}`.

I can bound this by: card(full bad) ≤ Σ_p card(bad_p) ≤ Σ_p [bound from count_bad_interval].

For p ≥ 3, I use count_bad_interval. For p = 2, I need an analogous bound.

Let me try yet another approach: just create `count_bad_interval_all_primes` as a sorry'd lemma with a clear annotation, and then use it to prove `exists_m_for_fixed_k`. This way I'm making real progress on the main proof while leaving a clearly documented sorry for the p=2 extension.

But wait — actually let me think about whether p=2 even matters. The count_bad_interval bound is:

```
count ≤ (2 * m0) / 2 ^ (D / 36) + (2 * p^D) / 2 ^ (D / 36)
```

For the union bound, I need this ≤ m₀/(8k) for each prime. With p^D ≤ m₀ and 2^(D/36) ≥ 32k, I get:
```
count ≤ (2*m₀)/(32k) + (2*m₀)/(32k) = 4*m₀/(32k) = m₀/(8k)
```

This is the same for all primes regardless of whether p=2 or p≥3. The question is just whether count_bad_interval works for p=2.

Actually, hold on. Let me re-examine what `count_bad_interval` uses. It calls `bad_residue_sets`, which calls `valuation_gt_implies_cascade` and `count_high_le_valuation`. Those don't need p ≥ 3. It also calls `residue_count_interval` (no p ≥ 3 needed), `count_large_cascade` (no p ≥ 3), and `count_few_high_digits` (needs p ≥ 3!).

So the only blocker is `count_few_high_digits`. And the only use of `p ≥ 3` in that proof is the omega step `p / 2 * 3 ≥ p`, which actually holds for all p ≥ 2.

Let me try a more surgical approach: prove `count_few_high_digits` without the `p ≥ 3` condition by exactly copying the existing proof and replacing the `omega` step. I'll only need to do this for the `count_few_high_digits` lemma. Then I can derive `count_bad_interval` for all primes.

Actually, there's an even simpler approach: for p=2, the bound `2^D / 2^(D/36) = 2^(D - D/36)`. Since the filter is a subset of range(2^D), the card is at most 2^D. I just need `2^D ≤ 2^D / 2^(D/36)` — no, that's wrong. I need the filter card ≤ 2^D / 2^(D/36), which is a stronger statement.

OK, let me just go with the approach of creating the whole proof. Let me write `count_bad_interval_all` that combines p≥3 and p=2:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_main_proof.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset Real Erdos728

-- For the p=2 case of count_few_high_digits, we need a dedicated proof.
-- The existing proof works for p ≥ 3 but the math is identical for p = 2.
-- We prove a version for all primes.

-- Step 1: probHigh p ≥ 1/3 for all primes p
private lemma probHigh_ge_third (p : ℕ) (hp : p.Prime) : probHigh p ≥ 1/3 := by
  unfold probHigh
  rw [ge_iff_le, div_le_div_iff₀
    (by norm_num : (0:ℝ) < 3) (by positivity : (0:ℝ) < p)]
  have : (↑(p / 2 * 3) : ℝ) ≥ (↑p : ℝ) := by
    exact_mod_cast (show p / 2 * 3 ≥ p by have := hp.two_le; omega)
  push_cast at this; linarith

EOF
lake env lean /tmp/test_main_proof.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_main_proof.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset Real Erdos728

private lemma probHigh_ge_third (p : ℕ) (hp : p.Prime) : probHigh p ≥ 1/3 := by
  unfold probHigh
  rw [ge_iff_le, div_le_div_iff₀
    (by norm_num : (0:ℝ) < 3) (by exact_mod_cast hp.pos : (0:ℝ) < p)]
  have : (↑(p / 2 * 3) : ℝ) ≥ (↑p : ℝ) := by
    exact_mod_cast (show p / 2 * 3 ≥ p by have := hp.two_le; omega)
  push_cast at this; linarith

EOF
lake env lean /tmp/test_main_proof.lean 2>&1
```
Now let me build the full `count_few_high_digits` for all primes. Let me check what the existing proof structure looks like more carefully and replicate it:
🛠️ **Executing tool: read**

🛠️ **Executing tool: read**
I see — the proof of `count_few_high_digits` is long but the only use of `hp_ge_3` is in the `omega` step. The proof would be identical for p=2. But duplicating 120+ lines is painful. 

Let me take a different approach entirely: I can verify that `omega` can prove `p / 2 * 3 ≥ p` from `hp.two_le` alone (which we've confirmed), and then the existing `count_few_high_digits` proof would work without `hp_ge_3`. But I can't modify the existing lemma.

Let me just create the entire chain. I'll create `count_few_high_digits_all` and `count_bad_interval_all` as wrapper lemmas, and then use them in the main proof. For `count_few_high_digits_all`, I can handle p ≥ 3 by delegation and p = 2 with sorry (clearly annotated), then focus on the main proof structure.

Actually wait — let me check something. For p=2, can I use a simpler bound? The bound we need is:
```
#{m < 2^D : count_high_digits 2 m D < t} ≤ 2^D / 2^(D/36)
```
where t ≤ D/6.

In base 2, `count_high_digits 2 m D` counts digits of m that are ≥ 1, which is just the number of 1-bits in positions 0..D-1. This is the Hamming weight. For random m, the expected number of 1-bits is D/2. We need to bound #{m : hamming_weight < D/6}, which is the lower tail of a binomial(D, 1/2).

The Chernoff bound gives this as at most `2^D * exp(-2*(D/2 - D/6)^2/D) = 2^D * exp(-2D/9)`. Since `exp(-2D/9) ≤ 2^(-D/36)` for sufficiently large D (actually for all D ≥ 0), we get the bound.

But I don't need to prove this from scratch — the existing Chernoff machinery (`count_few_high_digits_bound_chernoff`) works for all p (it doesn't require p ≥ 3). Let me check:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_chernoff.lean << 'EOF'
import Erdos.Lemma3Counting
open Erdos728

#check @count_few_high_digits_bound_chernoff
EOF
lake env lean /tmp/test_chernoff.lean 2>&1
```
The Chernoff bound doesn't require p ≥ 3. So I can build `count_few_high_digits_all` by exactly following the existing proof but using `hp.two_le` instead of `hp_ge_3`. Let me write this properly:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_cfhd_all.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset Real Erdos728

/-- Version of count_few_high_digits for all primes (including p=2).
    The existing version requires p ≥ 3 but the proof only uses p ≥ 2. -/
private lemma count_few_high_digits_all {p : ℕ} (D : ℕ) (hp : p.Prime) (t : ℕ) (ht : t ≤ D/6) :
    ((range (p^D)).filter (fun m => count_high_digits p m D < t)).card ≤
    p^D / 2^(D/36) := by
  by_cases hp3 : p ≥ 3
  · exact count_few_high_digits D hp t ht hp3
  · -- p = 2 case: identical proof except omega handles p / 2 * 3 ≥ p for p=2
    have hp_val : p = 2 := by have := hp.two_le; omega
    subst hp_val
    by_cases ht0 : t = 0
    · simp [ht0]
    have ht_pos : t ≥ 1 := Nat.pos_of_ne_zero ht0
    have hD_ge_6 : D ≥ 6 := by omega
    have hD_pos : D > 0 := by omega
    have h_card_eq_fin :
        ((range (2^D)).filter (fun m => count_high_digits 2 m D < t)).card =
        ((Finset.univ : Finset (Fin (2^D))).filter
          (fun m : Fin (2^D) => count_high_digits 2 m.val D < t)).card := by
      apply Finset.card_bij
        (fun m hm => ⟨m, by rw [mem_filter] at hm; exact mem_range.mp hm.1⟩)
      · intro m hm; rw [mem_filter] at hm ⊢; exact ⟨mem_univ _, hm.2⟩
      · intro a _ b _ h; simp at h; exact h
      · intro b hb; refine ⟨b.val, ?_, Fin.ext rfl⟩
        rw [mem_filter]
        exact ⟨mem_range.mpr b.isLt, (mem_filter.mp hb).2⟩
    have h_card_eq_ds :
        ((Finset.univ : Finset (Fin (2^D))).filter
          (fun m : Fin (2^D) => count_high_digits 2 m.val D < t)).card =
        ((Finset.univ : Finset (DigitSpace D 2)).filter
          (fun m : DigitSpace D 2 => highDigitCount m < t)).card := by
      have hbij := toDigitSpace_bijective hp D
      apply Finset.card_bij (fun m _ => toDigitSpace hp D m)
      · intro m hm; rw [mem_filter] at hm ⊢
        exact ⟨mem_univ _, by rw [highDigitCount_eq hp D m]; exact hm.2⟩
      · intro a _ b _ h; exact hbij.1 h
      · intro b hb; obtain ⟨a, ha⟩ := hbij.2 b
        refine ⟨a, ?_, ha⟩; rw [mem_filter]
        exact ⟨mem_univ _, by
          rw [← highDigitCount_eq hp D a, ha]; exact (mem_filter.mp hb).2⟩
    have h_subset :
        (Finset.univ.filter (fun m : DigitSpace D 2 => highDigitCount m < t)) ⊆
        (Finset.univ.filter (fun m : DigitSpace D 2 => (highDigitCount m : ℝ) ≤ ↑t)) := by
      intro m; simp only [mem_filter, mem_univ, true_and]
      exact fun h => by exact_mod_cast le_of_lt h
    have h_prob_ge : probHigh 2 ≥ 1/3 := by
      unfold probHigh; norm_num
    have h_t_le_D6 : (↑t : ℝ) ≤ ↑D / 6 := by
      have : (↑(t * 6) : ℝ) ≤ (↑D : ℝ) := by exact_mod_cast (show t * 6 ≤ D by omega)
      push_cast at this; linarith
    have h_t_lt : (t : ℝ) < ↑D * probHigh 2 := by
      have : (↑D : ℝ) / 6 < ↑D / 3 := by
        apply div_lt_div_of_pos_left
          (by exact_mod_cast hD_pos : (0:ℝ) < ↑D) (by norm_num) (by norm_num)
      nlinarith [show (D:ℝ) ≥ 0 from by positivity]
    have hne : NeZero (2 : ℕ) := ⟨by omega⟩
    have h_chernoff := @count_few_high_digits_bound_chernoff D 2 hne (↑t) h_t_lt
    have h_exp_bound :
        exp (-2 * ((↑D * probHigh 2 - ↑t)^2) / (↑D : ℝ)) ≤ ((2 : ℝ)^(D/36))⁻¹ := by
      have h_gap : ↑D * probHigh 2 - ↑t ≥ ↑D / 6 := by
        nlinarith [show (D:ℝ) ≥ 0 from by positivity]
      have hD_r : (↑D : ℝ) > 0 := by exact_mod_cast hD_pos
      have h_exp_le :
          -2 * ((↑D * probHigh 2 - ↑t)^2) / (↑D : ℝ) ≤ -(↑D : ℝ) / 18 := by
        calc -2 * (↑D * probHigh 2 - ↑t)^2 / ↑D
            ≤ -2 * ((↑D : ℝ) / 6)^2 / ↑D := by
              apply div_le_div_of_nonneg_right _ (le_of_lt hD_r)
              nlinarith [sq_le_sq' (by linarith) h_gap]
          _ = -(↑D : ℝ) / 18 := by field_simp; ring
      calc exp (-2 * ((↑D * probHigh 2 - ↑t)^2) / ↑D)
          ≤ exp (-(↑D : ℝ) / 18) := by rw [exp_le_exp]; exact h_exp_le
        _ ≤ ((2 : ℝ)^(D/36))⁻¹ := by
            rw [show ((2 : ℝ)^(D/36))⁻¹ =
                exp (-(↑(D/36) * Real.log 2)) from by
              rw [exp_neg]; congr 1
              rw [← rpow_natCast, rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
              ring_nf]
            rw [exp_le_exp]
            nlinarith [
              show Real.log 2 ≤ 1 from by
                rw [← Real.log_exp 1]
                exact Real.log_le_log (by norm_num) (by linarith [add_one_le_exp 1]),
              show (↑(D/36) : ℝ) ≤ (D : ℝ) / 18 from by
                have : (↑(D/36) : ℝ) ≤ (D : ℝ) / 36 := by
                  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 36)]
                  exact_mod_cast Nat.div_mul_le_self D 36
                linarith [show (D:ℝ) / 36 ≤ (D:ℝ) / 18 from by
                  apply div_le_div_of_nonneg_left _ (by norm_num) (by norm_num)
                  exact_mod_cast Nat.zero_le D],
              show (↑(D/36) : ℝ) ≥ 0 from by exact_mod_cast Nat.zero_le _]
    rw [h_card_eq_fin, h_card_eq_ds]
    have h2_pos : (2 : ℕ)^(D/36) > 0 := by positivity
    rw [Nat.le_div_iff_mul_le h2_pos]
    have h_card_le := card_le_card h_subset
    suffices h : ((((Finset.univ.filter
        (fun m : DigitSpace D 2 => highDigitCount m < t)).card
        * 2^(D/36) : ℕ) : ℝ) ≤ ↑(2^D)) from by exact_mod_cast h
    push_cast
    calc ↑((Finset.univ.filter
          (fun m : DigitSpace D 2 => highDigitCount m < t)).card) * (2:ℝ)^(D/36)
        ≤ ↑((Finset.univ.filter
          (fun m : DigitSpace D 2 => (highDigitCount m : ℝ) ≤ ↑t)).card) * (2:ℝ)^(D/36) := by
          apply mul_le_mul_of_nonneg_right (by exact_mod_cast h_card_le) (by positivity)
      _ ≤ ((2:ℝ) ^ D * exp (-2 * ((↑D * probHigh 2 - ↑t)^2) / ↑D)) * (2:ℝ)^(D/36) := by
          apply mul_le_mul_of_nonneg_right h_chernoff (by positivity)
      _ ≤ ((2:ℝ) ^ D * ((2 : ℝ)^(D/36))⁻¹) * (2:ℝ)^(D/36) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left h_exp_bound (by positivity)
      _ = (2:ℝ) ^ D := by
          rw [mul_assoc, inv_mul_cancel₀ (by positivity : (2:ℝ)^(D/36) ≠ 0), mul_one]

EOF
lake env lean /tmp/test_cfhd_all.lean 2>&1
```
`count_few_high_digits_all` compiles. Now let me build `count_bad_interval_all` that works for all primes:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_cbi_all.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset Real Erdos728

-- First, count_few_high_digits for all primes (from previous test, known to work)
private lemma count_few_high_digits_all {p : ℕ} (D : ℕ) (hp : p.Prime) (t : ℕ) (ht : t ≤ D/6) :
    ((range (p^D)).filter (fun m => count_high_digits p m D < t)).card ≤
    p^D / 2^(D/36) := by
  by_cases hp3 : p ≥ 3
  · exact count_few_high_digits D hp t ht hp3
  · have hp_val : p = 2 := by have := hp.two_le; omega
    subst hp_val
    by_cases ht0 : t = 0; · simp [ht0]
    have ht_pos : t ≥ 1 := Nat.pos_of_ne_zero ht0
    have hD_ge_6 : D ≥ 6 := by omega
    have hD_pos : D > 0 := by omega
    have h_card_eq_fin :
        ((range (2^D)).filter (fun m => count_high_digits 2 m D < t)).card =
        ((Finset.univ : Finset (Fin (2^D))).filter
          (fun m : Fin (2^D) => count_high_digits 2 m.val D < t)).card := by
      apply Finset.card_bij
        (fun m hm => ⟨m, by rw [mem_filter] at hm; exact mem_range.mp hm.1⟩)
      · intro m hm; rw [mem_filter] at hm ⊢; exact ⟨mem_univ _, hm.2⟩
      · intro a _ b _ h; simp at h; exact h
      · intro b hb; refine ⟨b.val, ?_, Fin.ext rfl⟩
        rw [mem_filter]; exact ⟨mem_range.mpr b.isLt, (mem_filter.mp hb).2⟩
    have h_card_eq_ds :
        ((Finset.univ : Finset (Fin (2^D))).filter
          (fun m : Fin (2^D) => count_high_digits 2 m.val D < t)).card =
        ((Finset.univ : Finset (DigitSpace D 2)).filter
          (fun m : DigitSpace D 2 => highDigitCount m < t)).card := by
      have hbij := toDigitSpace_bijective hp D
      apply Finset.card_bij (fun m _ => toDigitSpace hp D m)
      · intro m hm; rw [mem_filter] at hm ⊢
        exact ⟨mem_univ _, by rw [highDigitCount_eq hp D m]; exact hm.2⟩
      · intro a _ b _ h; exact hbij.1 h
      · intro b hb; obtain ⟨a, ha⟩ := hbij.2 b
        refine ⟨a, ?_, ha⟩; rw [mem_filter]
        exact ⟨mem_univ _, by rw [← highDigitCount_eq hp D a, ha]; exact (mem_filter.mp hb).2⟩
    have h_subset :
        (Finset.univ.filter (fun m : DigitSpace D 2 => highDigitCount m < t)) ⊆
        (Finset.univ.filter (fun m : DigitSpace D 2 => (highDigitCount m : ℝ) ≤ ↑t)) := by
      intro m; simp only [mem_filter, mem_univ, true_and]
      exact fun h => by exact_mod_cast le_of_lt h
    have h_prob_ge : probHigh 2 ≥ 1/3 := by unfold probHigh; norm_num
    have h_t_lt : (t : ℝ) < ↑D * probHigh 2 := by
      have : (↑D : ℝ) / 6 < ↑D / 3 := by
        apply div_lt_div_of_pos_left (by exact_mod_cast hD_pos : (0:ℝ) < ↑D) (by norm_num) (by norm_num)
      nlinarith [show (D:ℝ) ≥ 0 from by positivity]
    have hne : NeZero (2 : ℕ) := ⟨by omega⟩
    have h_chernoff := @count_few_high_digits_bound_chernoff D 2 hne (↑t) h_t_lt
    have h_exp_bound :
        exp (-2 * ((↑D * probHigh 2 - ↑t)^2) / (↑D : ℝ)) ≤ ((2 : ℝ)^(D/36))⁻¹ := by
      have h_gap : ↑D * probHigh 2 - ↑t ≥ ↑D / 6 := by
        nlinarith [show (D:ℝ) ≥ 0 from by positivity]
      have hD_r : (↑D : ℝ) > 0 := by exact_mod_cast hD_pos
      calc exp (-2 * ((↑D * probHigh 2 - ↑t)^2) / ↑D)
          ≤ exp (-(↑D : ℝ) / 18) := by
            rw [exp_le_exp]
            calc -2 * (↑D * probHigh 2 - ↑t)^2 / ↑D
                ≤ -2 * ((↑D : ℝ) / 6)^2 / ↑D := by
                  apply div_le_div_of_nonneg_right _ (le_of_lt hD_r)
                  nlinarith [sq_le_sq' (by linarith) h_gap]
              _ = -(↑D : ℝ) / 18 := by field_simp; ring
        _ ≤ ((2 : ℝ)^(D/36))⁻¹ := by
            rw [show ((2 : ℝ)^(D/36))⁻¹ = exp (-(↑(D/36) * Real.log 2)) from by
              rw [exp_neg]; congr 1; rw [← rpow_natCast, rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]; ring_nf]
            rw [exp_le_exp]
            nlinarith [
              show Real.log 2 ≤ 1 from by
                rw [← Real.log_exp 1]; exact Real.log_le_log (by norm_num) (by linarith [add_one_le_exp 1]),
              show (↑(D/36) : ℝ) ≤ (D : ℝ) / 18 from by
                have : (↑(D/36) : ℝ) ≤ (D : ℝ) / 36 := by
                  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 36)]; exact_mod_cast Nat.div_mul_le_self D 36
                linarith [show (D:ℝ) / 36 ≤ (D:ℝ) / 18 from by
                  apply div_le_div_of_nonneg_left _ (by norm_num) (by norm_num); exact_mod_cast Nat.zero_le D],
              show (↑(D/36) : ℝ) ≥ 0 from by exact_mod_cast Nat.zero_le _]
    rw [h_card_eq_fin, h_card_eq_ds]
    have h2_pos : (2 : ℕ)^(D/36) > 0 := by positivity
    rw [Nat.le_div_iff_mul_le h2_pos]
    have h_card_le := card_le_card h_subset
    suffices h : ((((Finset.univ.filter (fun m : DigitSpace D 2 => highDigitCount m < t)).card
        * 2^(D/36) : ℕ) : ℝ) ≤ ↑(2^D)) from by exact_mod_cast h
    push_cast
    calc ↑((Finset.univ.filter (fun m : DigitSpace D 2 => highDigitCount m < t)).card) * (2:ℝ)^(D/36)
        ≤ ↑((Finset.univ.filter (fun m : DigitSpace D 2 => (highDigitCount m : ℝ) ≤ ↑t)).card) * (2:ℝ)^(D/36) := by
          apply mul_le_mul_of_nonneg_right (by exact_mod_cast h_card_le) (by positivity)
      _ ≤ ((2:ℝ) ^ D * exp (-2 * ((↑D * probHigh 2 - ↑t)^2) / ↑D)) * (2:ℝ)^(D/36) := by
          apply mul_le_mul_of_nonneg_right h_chernoff (by positivity)
      _ ≤ ((2:ℝ) ^ D * ((2 : ℝ)^(D/36))⁻¹) * (2:ℝ)^(D/36) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left h_exp_bound (by positivity)
      _ = (2:ℝ) ^ D := by
          rw [mul_assoc, inv_mul_cancel₀ (by positivity : (2:ℝ)^(D/36) ≠ 0), mul_one]

-- Now, count_bad_interval for all primes
lemma count_bad_interval_all {p : ℕ} (D k m0 : ℕ)
    (hm0 : m0 ≥ p^D) (hD : D ≥ 16 * (log p (k + 1)) + 16)
    (hp : p.Prime) (hk : k ≥ 1) :
    ((Ico m0 (2 * m0)).filter (fun m => padicValNat p ((m + k).choose k) > padicValNat p ((2 * m).choose m))).card
    ≤ (2 * m0) / 2 ^ (D / 36) + (2 * p^D) / 2 ^ (D / 36) := by
  by_cases hp3 : p ≥ 3
  · exact count_bad_interval D k m0 hm0 hD hp hp3 hk
  · -- p = 2 case
    have hp_val : p = 2 := by have := hp.two_le; omega
    subst hp_val
    sorry -- TODO: replicate count_bad_interval for p=2 using count_few_high_digits_all

EOF
lake env lean /tmp/test_cbi_all.lean 2>&1
```
The issue is that `nlinarith` can't handle `probHigh 2` directly because it's opaque. Let me unfold it:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_probhigh.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset Real Erdos728

-- What is probHigh 2?
-- probHigh p = (p / 2 : ℕ) / (p : ℝ)
-- probHigh 2 = (2/2 : ℕ) / (2:ℝ) = 1/2

example : probHigh 2 = 1/2 := by
  unfold probHigh
  norm_num

EOF
lake env lean /tmp/test_probhigh.lean 2>&1
```
Let me fix the proof with explicit `probHigh 2 = 1/2`:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_cfhd_fixed.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset Real Erdos728

private lemma count_few_high_digits_all {p : ℕ} (D : ℕ) (hp : p.Prime) (t : ℕ) (ht : t ≤ D/6) :
    ((range (p^D)).filter (fun m => count_high_digits p m D < t)).card ≤
    p^D / 2^(D/36) := by
  by_cases hp3 : p ≥ 3
  · exact count_few_high_digits D hp t ht hp3
  · have hp_val : p = 2 := by have := hp.two_le; omega
    subst hp_val
    by_cases ht0 : t = 0; · simp [ht0]
    have ht_pos : t ≥ 1 := Nat.pos_of_ne_zero ht0
    have hD_ge_6 : D ≥ 6 := by omega
    have hD_pos : D > 0 := by omega
    have h_card_eq_fin :
        ((range (2^D)).filter (fun m => count_high_digits 2 m D < t)).card =
        ((Finset.univ : Finset (Fin (2^D))).filter
          (fun m : Fin (2^D) => count_high_digits 2 m.val D < t)).card := by
      apply Finset.card_bij
        (fun m hm => ⟨m, by rw [mem_filter] at hm; exact mem_range.mp hm.1⟩)
      · intro m hm; rw [mem_filter] at hm ⊢; exact ⟨mem_univ _, hm.2⟩
      · intro a _ b _ h; simp at h; exact h
      · intro b hb; refine ⟨b.val, ?_, Fin.ext rfl⟩
        rw [mem_filter]; exact ⟨mem_range.mpr b.isLt, (mem_filter.mp hb).2⟩
    have h_card_eq_ds :
        ((Finset.univ : Finset (Fin (2^D))).filter
          (fun m : Fin (2^D) => count_high_digits 2 m.val D < t)).card =
        ((Finset.univ : Finset (DigitSpace D 2)).filter
          (fun m : DigitSpace D 2 => highDigitCount m < t)).card := by
      have hbij := toDigitSpace_bijective hp D
      apply Finset.card_bij (fun m _ => toDigitSpace hp D m)
      · intro m hm; rw [mem_filter] at hm ⊢
        exact ⟨mem_univ _, by rw [highDigitCount_eq hp D m]; exact hm.2⟩
      · intro a _ b _ h; exact hbij.1 h
      · intro b hb; obtain ⟨a, ha⟩ := hbij.2 b
        refine ⟨a, ?_, ha⟩; rw [mem_filter]
        exact ⟨mem_univ _, by rw [← highDigitCount_eq hp D a, ha]; exact (mem_filter.mp hb).2⟩
    have h_subset :
        (Finset.univ.filter (fun m : DigitSpace D 2 => highDigitCount m < t)) ⊆
        (Finset.univ.filter (fun m : DigitSpace D 2 => (highDigitCount m : ℝ) ≤ ↑t)) := by
      intro m; simp only [mem_filter, mem_univ, true_and]
      exact fun h => by exact_mod_cast le_of_lt h
    have hph : probHigh 2 = 1/2 := by unfold probHigh; norm_num
    have h_t_lt : (t : ℝ) < ↑D * probHigh 2 := by
      rw [hph]
      have h1 : (↑t : ℝ) ≤ ↑D / 6 := by
        have : (↑(t * 6) : ℝ) ≤ (↑D : ℝ) := by exact_mod_cast (show t * 6 ≤ D by omega)
        push_cast at this; linarith
      linarith [show (↑D : ℝ) > 0 from by exact_mod_cast hD_pos]
    have hne : NeZero (2 : ℕ) := ⟨by omega⟩
    have h_chernoff := @count_few_high_digits_bound_chernoff D 2 hne (↑t) h_t_lt
    have h_exp_bound :
        exp (-2 * ((↑D * probHigh 2 - ↑t)^2) / (↑D : ℝ)) ≤ ((2 : ℝ)^(D/36))⁻¹ := by
      rw [hph]
      have h_gap : ↑D * (1:ℝ)/2 - ↑t ≥ ↑D / 6 := by
        have h1 : (↑t : ℝ) ≤ ↑D / 6 := by
          have : (↑(t * 6) : ℝ) ≤ (↑D : ℝ) := by exact_mod_cast (show t * 6 ≤ D by omega)
          push_cast at this; linarith
        linarith
      have hD_r : (↑D : ℝ) > 0 := by exact_mod_cast hD_pos
      calc exp (-2 * ((↑D * (1:ℝ) / 2 - ↑t)^2) / ↑D)
          ≤ exp (-(↑D : ℝ) / 18) := by
            rw [exp_le_exp]
            calc -2 * (↑D * (1:ℝ) / 2 - ↑t)^2 / ↑D
                ≤ -2 * ((↑D : ℝ) / 6)^2 / ↑D := by
                  apply div_le_div_of_nonneg_right _ (le_of_lt hD_r)
                  nlinarith [sq_le_sq' (by linarith) h_gap]
              _ = -(↑D : ℝ) / 18 := by field_simp; ring
        _ ≤ ((2 : ℝ)^(D/36))⁻¹ := by
            rw [show ((2 : ℝ)^(D/36))⁻¹ = exp (-(↑(D/36) * Real.log 2)) from by
              rw [exp_neg]; congr 1; rw [← rpow_natCast, rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]; ring_nf]
            rw [exp_le_exp]
            nlinarith [
              show Real.log 2 ≤ 1 from by
                rw [← Real.log_exp 1]; exact Real.log_le_log (by norm_num) (by linarith [add_one_le_exp 1]),
              show (↑(D/36) : ℝ) ≤ (D : ℝ) / 18 from by
                have : (↑(D/36) : ℝ) ≤ (D : ℝ) / 36 := by
                  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 36)]; exact_mod_cast Nat.div_mul_le_self D 36
                linarith [show (D:ℝ) / 36 ≤ (D:ℝ) / 18 from by
                  apply div_le_div_of_nonneg_left _ (by norm_num) (by norm_num); exact_mod_cast Nat.zero_le D],
              show (↑(D/36) : ℝ) ≥ 0 from by exact_mod_cast Nat.zero_le _]
    rw [h_card_eq_fin, h_card_eq_ds]
    have h2_pos : (2 : ℕ)^(D/36) > 0 := by positivity
    rw [Nat.le_div_iff_mul_le h2_pos]
    have h_card_le := card_le_card h_subset
    suffices h : ((((Finset.univ.filter (fun m : DigitSpace D 2 => highDigitCount m < t)).card
        * 2^(D/36) : ℕ) : ℝ) ≤ ↑(2^D)) from by exact_mod_cast h
    push_cast
    calc ↑((Finset.univ.filter (fun m : DigitSpace D 2 => highDigitCount m < t)).card) * (2:ℝ)^(D/36)
        ≤ ↑((Finset.univ.filter (fun m : DigitSpace D 2 => (highDigitCount m : ℝ) ≤ ↑t)).card) * (2:ℝ)^(D/36) := by
          apply mul_le_mul_of_nonneg_right (by exact_mod_cast h_card_le) (by positivity)
      _ ≤ ((2:ℝ) ^ D * exp (-2 * ((↑D * probHigh 2 - ↑t)^2) / ↑D)) * (2:ℝ)^(D/36) := by
          apply mul_le_mul_of_nonneg_right h_chernoff (by positivity)
      _ ≤ ((2:ℝ) ^ D * ((2 : ℝ)^(D/36))⁻¹) * (2:ℝ)^(D/36) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left h_exp_bound (by positivity)
      _ = (2:ℝ) ^ D := by
          rw [mul_assoc, inv_mul_cancel₀ (by positivity : (2:ℝ)^(D/36) ≠ 0), mul_one]

EOF
lake env lean /tmp/test_cfhd_fixed.lean 2>&1
```
Small formatting issue. Let me fix the `1/2` vs `(1/2)`:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_cfhd_fixed2.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset Real Erdos728

private lemma count_few_high_digits_all {p : ℕ} (D : ℕ) (hp : p.Prime) (t : ℕ) (ht : t ≤ D/6) :
    ((range (p^D)).filter (fun m => count_high_digits p m D < t)).card ≤
    p^D / 2^(D/36) := by
  by_cases hp3 : p ≥ 3
  · exact count_few_high_digits D hp t ht hp3
  · have hp_val : p = 2 := by have := hp.two_le; omega
    subst hp_val
    by_cases ht0 : t = 0; · simp [ht0]
    have ht_pos : t ≥ 1 := Nat.pos_of_ne_zero ht0
    have hD_ge_6 : D ≥ 6 := by omega
    have hD_pos : D > 0 := by omega
    have h_card_eq_fin :
        ((range (2^D)).filter (fun m => count_high_digits 2 m D < t)).card =
        ((Finset.univ : Finset (Fin (2^D))).filter
          (fun m : Fin (2^D) => count_high_digits 2 m.val D < t)).card := by
      apply Finset.card_bij
        (fun m hm => ⟨m, by rw [mem_filter] at hm; exact mem_range.mp hm.1⟩)
      · intro m hm; rw [mem_filter] at hm ⊢; exact ⟨mem_univ _, hm.2⟩
      · intro a _ b _ h; simp at h; exact h
      · intro b hb; refine ⟨b.val, ?_, Fin.ext rfl⟩
        rw [mem_filter]; exact ⟨mem_range.mpr b.isLt, (mem_filter.mp hb).2⟩
    have h_card_eq_ds :
        ((Finset.univ : Finset (Fin (2^D))).filter
          (fun m : Fin (2^D) => count_high_digits 2 m.val D < t)).card =
        ((Finset.univ : Finset (DigitSpace D 2)).filter
          (fun m : DigitSpace D 2 => highDigitCount m < t)).card := by
      have hbij := toDigitSpace_bijective hp D
      apply Finset.card_bij (fun m _ => toDigitSpace hp D m)
      · intro m hm; rw [mem_filter] at hm ⊢
        exact ⟨mem_univ _, by rw [highDigitCount_eq hp D m]; exact hm.2⟩
      · intro a _ b _ h; exact hbij.1 h
      · intro b hb; obtain ⟨a, ha⟩ := hbij.2 b
        refine ⟨a, ?_, ha⟩; rw [mem_filter]
        exact ⟨mem_univ _, by rw [← highDigitCount_eq hp D a, ha]; exact (mem_filter.mp hb).2⟩
    have h_subset :
        (Finset.univ.filter (fun m : DigitSpace D 2 => highDigitCount m < t)) ⊆
        (Finset.univ.filter (fun m : DigitSpace D 2 => (highDigitCount m : ℝ) ≤ ↑t)) := by
      intro m; simp only [mem_filter, mem_univ, true_and]
      exact fun h => by exact_mod_cast le_of_lt h
    have hph : probHigh 2 = 1/2 := by unfold probHigh; norm_num
    have h_t_lt : (t : ℝ) < ↑D * probHigh 2 := by
      rw [hph]
      have h1 : (↑t : ℝ) ≤ ↑D / 6 := by
        have : (↑(t * 6) : ℝ) ≤ (↑D : ℝ) := by exact_mod_cast (show t * 6 ≤ D by omega)
        push_cast at this; linarith
      linarith [show (↑D : ℝ) > 0 from by exact_mod_cast hD_pos]
    have hne : NeZero (2 : ℕ) := ⟨by omega⟩
    have h_chernoff := @count_few_high_digits_bound_chernoff D 2 hne (↑t) h_t_lt
    have h_exp_bound :
        exp (-2 * ((↑D * probHigh 2 - ↑t)^2) / (↑D : ℝ)) ≤ ((2 : ℝ)^(D/36))⁻¹ := by
      have h_gap : ↑D * probHigh 2 - ↑t ≥ ↑D / 6 := by
        rw [hph]
        have h1 : (↑t : ℝ) ≤ ↑D / 6 := by
          have : (↑(t * 6) : ℝ) ≤ (↑D : ℝ) := by exact_mod_cast (show t * 6 ≤ D by omega)
          push_cast at this; linarith
        linarith
      have hD_r : (↑D : ℝ) > 0 := by exact_mod_cast hD_pos
      have h_exp_le :
          -2 * ((↑D * probHigh 2 - ↑t)^2) / (↑D : ℝ) ≤ -(↑D : ℝ) / 18 := by
        calc -2 * (↑D * probHigh 2 - ↑t)^2 / ↑D
            ≤ -2 * ((↑D : ℝ) / 6)^2 / ↑D := by
              apply div_le_div_of_nonneg_right _ (le_of_lt hD_r)
              nlinarith [sq_le_sq' (by linarith) h_gap]
          _ = -(↑D : ℝ) / 18 := by field_simp; ring
      calc exp (-2 * ((↑D * probHigh 2 - ↑t)^2) / ↑D)
          ≤ exp (-(↑D : ℝ) / 18) := by rw [exp_le_exp]; exact h_exp_le
        _ ≤ ((2 : ℝ)^(D/36))⁻¹ := by
            rw [show ((2 : ℝ)^(D/36))⁻¹ = exp (-(↑(D/36) * Real.log 2)) from by
              rw [exp_neg]; congr 1; rw [← rpow_natCast, rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]; ring_nf]
            rw [exp_le_exp]
            nlinarith [
              show Real.log 2 ≤ 1 from by
                rw [← Real.log_exp 1]; exact Real.log_le_log (by norm_num) (by linarith [add_one_le_exp 1]),
              show (↑(D/36) : ℝ) ≤ (D : ℝ) / 18 from by
                have : (↑(D/36) : ℝ) ≤ (D : ℝ) / 36 := by
                  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 36)]; exact_mod_cast Nat.div_mul_le_self D 36
                linarith [show (D:ℝ) / 36 ≤ (D:ℝ) / 18 from by
                  apply div_le_div_of_nonneg_left _ (by norm_num) (by norm_num); exact_mod_cast Nat.zero_le D],
              show (↑(D/36) : ℝ) ≥ 0 from by exact_mod_cast Nat.zero_le _]
    rw [h_card_eq_fin, h_card_eq_ds]
    have h2_pos : (2 : ℕ)^(D/36) > 0 := by positivity
    rw [Nat.le_div_iff_mul_le h2_pos]
    have h_card_le := card_le_card h_subset
    suffices h : ((((Finset.univ.filter (fun m : DigitSpace D 2 => highDigitCount m < t)).card
        * 2^(D/36) : ℕ) : ℝ) ≤ ↑(2^D)) from by exact_mod_cast h
    push_cast
    calc ↑((Finset.univ.filter (fun m : DigitSpace D 2 => highDigitCount m < t)).card) * (2:ℝ)^(D/36)
        ≤ ↑((Finset.univ.filter (fun m : DigitSpace D 2 => (highDigitCount m : ℝ) ≤ ↑t)).card) * (2:ℝ)^(D/36) := by
          apply mul_le_mul_of_nonneg_right (by exact_mod_cast h_card_le) (by positivity)
      _ ≤ ((2:ℝ) ^ D * exp (-2 * ((↑D * probHigh 2 - ↑t)^2) / ↑D)) * (2:ℝ)^(D/36) := by
          apply mul_le_mul_of_nonneg_right h_chernoff (by positivity)
      _ ≤ ((2:ℝ) ^ D * ((2 : ℝ)^(D/36))⁻¹) * (2:ℝ)^(D/36) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left h_exp_bound (by positivity)
      _ = (2:ℝ) ^ D := by
          rw [mul_assoc, inv_mul_cancel₀ (by positivity : (2:ℝ)^(D/36) ≠ 0), mul_one]

EOF
lake env lean /tmp/test_cfhd_fixed2.lean 2>&1
```
Now let me build `count_bad_interval_all`. Looking at the `count_bad_interval` proof, it uses `count_few_high_digits` in one place. The rest of the proof doesn't need `p ≥ 3`. So I can replicate the proof, replacing `count_few_high_digits` with `count_few_high_digits_all`:

Actually, looking more carefully at `count_bad_interval`, it doesn't directly call `count_few_high_digits` — it calls `bad_residue_sets`, `residue_count_interval`, `count_large_cascade`, and `count_few_high_digits`. The structure is quite involved. Let me try a simpler approach: just wrap the existing `count_bad_interval` for p ≥ 3, and for p = 2, delegate to `count_bad_single_prime` (which also needs p ≥ 3...).

Hmm, actually looking at the chain:
- `count_bad_single_prime` needs `p ≥ 3`
- `count_bad_interval` needs `p ≥ 3`

Both through `count_few_high_digits`. Let me just create `count_bad_interval_all` by replacing the single call to `count_few_high_digits` with `count_few_high_digits_all`. This means I need to replicate the `count_bad_interval` proof but with the fix.

Actually wait — `count_bad_interval` calls `count_few_high_digits` at line 965 and calls `bad_residue_sets` which also uses `count_high_le_valuation` (which doesn't need p ≥ 3). And `bad_residue_sets` doesn't need p ≥ 3 either. Let me check...
```bash
$ cd /home/jarred/code/erdos-728b && grep -n "hp_ge_3\|p ≥ 3" Erdos/Lemma3Counting.lean
```
So `count_bad_interval` uses `hp_ge_3` only at line 965 for `count_few_high_digits`. Everything else is `p ≥ 2`. So I need to replicate `count_bad_interval` but replacing that one call. That's a lot of code though.

Let me try a more targeted approach: can I just use the fact that for p = 2, I have a slightly simpler argument? Actually, let me just write `count_bad_interval_all` as a wrapper:
```bash
$ cd /home/jarred/code/erdos-728b && wc -l Erdos/Lemma3Counting.lean
```
OK, I think the most practical approach is to NOT replicate `count_bad_interval` for p=2. Instead, I'll modify the `exists_m_for_fixed_k` proof strategy. For the union bound, I'll handle p=2 and p≥3 separately:

- For primes p with p ≥ 3 and p ≤ 2k: use count_bad_interval directly
- For p = 2: use count_bad_interval... wait, I still need it for p=2.

Actually, let me just bite the bullet and replicate the key parts of `count_bad_interval` for all primes. Let me write a cleaner version:
```bash
$ cd /home/jarred/code/erdos-728b && tm update erdos728b-r4m --status "Writing count_bad_interval_all to handle p=2, then building union bound"
```
Let me take a different, more modular approach. Instead of replicating `count_bad_interval` for p=2, I'll just prove the key bound that the union bound needs directly. The union bound needs:

For each prime p ≤ 2k, with D_p chosen appropriately:
```
|{m ∈ [m₀, 2m₀) : bad_p(m)}| ≤ m₀/(8k)
```

From `count_bad_interval`, we have:
```
|bad_p| ≤ (2*m₀)/2^(D_p/36) + (2*p^{D_p})/2^(D_p/36)
```

With p^{D_p} ≤ m₀ and 2^{D_p/36} ≥ 32k, this gives:
```
|bad_p| ≤ (2*m₀)/(32k) + (2*m₀)/(32k) = m₀/(8k)
```

Wait, the arithmetic doesn't quite work in ℕ division. Let me think...

Actually: `(2*m₀)/(32k) + (2*m₀)/(32k)`. In ℕ, `a/n + a/n ≤ 2*a/n` always holds, and `2*(2*m₀)/(32k) = 4*m₀/(32k) = m₀/(8k)`. Hmm, but in ℕ division `4a/32 ≠ a/8` necessarily.

Let me think about this differently. The NL proof says:
- `N(p) ≤ 4*m₀/2^{D_p/36}` (combining the two terms using p^{D_p} ≤ m₀)
- `2^{D_p/36} ≥ 32k`  
- So `N(p) ≤ 4*m₀/(32k) = m₀/(8k)`

And then the union bound gives total ≤ 2k * m₀/(8k) = m₀/4.

In ℕ arithmetic, I need to be more careful. Let me think about what bound I actually need. I need:

```
∑_{p prime, p ≤ 2k} |bad_p| < m₀
```

If each |bad_p| ≤ (2*m₀)/2^{D_p/36} + (2*p^{D_p})/2^{D_p/36}, then I need:

```
∑_p [(2*m₀)/2^{D_p/36} + (2*p^{D_p})/2^{D_p/36}] < m₀
```

With p^{D_p} ≤ m₀, each term ≤ (2*m₀)/2^{D_p/36} + (2*m₀)/2^{D_p/36} = (4*m₀)/2^{D_p/36}... but in ℕ this isn't exact.

Hmm, let me just bound each term by (4*m₀)/2^{D_p/36} ≤ (4*m₀)/(32k) since 2^{D_p/36} ≥ 32k. Actually in ℕ:

`a/n + a/n ≤ (2*a)/n` — this is true for ℕ since `a/n * 2 ≤ (2*a)/n` (rounding down only helps the RHS).

Wait actually: `(2*m₀)/(32k) + (2*m₀)/(32k)` ≤ `2 * ((2*m₀)/(32k))` = `(4*m₀)/(32k)` only if we use `2*x ≤ 2*x` which is trivial but `2*((2*m₀)/(32k))` might not equal `(4*m₀)/(32k)` in ℕ. But actually `(4*m₀)/(32k) ≤ m₀/(8k)` in ℕ? Not necessarily — `4a/32 ≠ a/8` in ℕ in general.

OK, let me just work with the bound directly and avoid these ℕ division issues by using a different approach. Let me bound the total count of bad m directly.

Actually, the simplest approach for ℕ arithmetic: I need the total count to be < m₀. I'll use:

```
total_bad ≤ ∑_{p ≤ 2k, p prime} (2*m₀ + 2*p^{D_p}) / 2^{D_p/36}
         ≤ (2k) * (2*m₀ + 2*m₀) / (32*k)  [using p^{D_p} ≤ m₀ and 2^{D_p/36} ≥ 32k]
         = (2k) * (4*m₀) / (32*k)
         ... hmm, this is getting complicated with ℕ division.
```

Let me try yet another approach. Let me just work with the bound directly and not try to simplify the ℕ arithmetic too much. The key insight is:

For each prime, the count is at most `(2*m₀ + 2*m₀) / (32k) = 4*m₀/(32k)`. The number of primes is at most `2k`. So total is at most `2k * 4*m₀/(32k)`.

In ℕ: `2k * (4*m₀/(32k)) ≤ 8k*m₀/(32k) = m₀/4`. But this doesn't work directly in ℕ.

OK, I think the cleaner approach is to avoid the per-prime bound and go directly to the total. Let me think about this more carefully...

Actually, let me approach this proof in a completely different way. Instead of the per-prime bound + union bound, let me use the fact that the bad set is a union of per-prime bad sets, and bound the cardinality of the union.

Let me write the proof at a high level and see what sub-lemmas I need:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_exists.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset Real Erdos728

-- Helper: count_few_high_digits for all primes
-- (proved in previous test, will be added to file)
private lemma count_few_high_digits_all {p : ℕ} (D : ℕ) (hp : p.Prime) (t : ℕ) (ht : t ≤ D/6) :
    ((range (p^D)).filter (fun m => count_high_digits p m D < t)).card ≤
    p^D / 2^(D/36) := by
  by_cases hp3 : p ≥ 3
  · exact count_few_high_digits D hp t ht hp3
  · sorry -- proved separately

-- count_bad_interval for all primes (including p=2)
-- The existing version requires p ≥ 3; we extend it.
-- For p ≥ 3, delegate. For p = 2, the proof is identical except for 
-- count_few_high_digits → count_few_high_digits_all.
private lemma count_bad_interval_all {p : ℕ} (D k m0 : ℕ)
    (hm0 : m0 ≥ p^D) (hD : D ≥ 16 * (log p (k + 1)) + 16)
    (hp : p.Prime) (hk : k ≥ 1) :
    ((Ico m0 (2 * m0)).filter (fun m => padicValNat p ((m + k).choose k) > padicValNat p ((2 * m).choose m))).card
    ≤ (2 * m0) / 2 ^ (D / 36) + (2 * p^D) / 2 ^ (D / 36) := by
  by_cases hp3 : p ≥ 3
  · exact count_bad_interval D k m0 hm0 hD hp hp3 hk
  · sorry -- proved separately for p=2

-- D_p for each prime p
private def D_p (k p : ℕ) : ℕ :=
  36 * (Nat.log 2 (16 * k) + 1) + 36 * (Nat.log p (k + 1)) + 36

-- Goal 1a: D_p ≥ 16 * log_p(k+1) + 16
private lemma D_p_ge_threshold (k p : ℕ) (hk : k ≥ 1) (hp : p.Prime) :
    D_p k p ≥ 16 * (Nat.log p (k + 1)) + 16 := by
  unfold D_p; omega

-- Goal 1b: p^{D_p} ≤ union_bound_threshold k
-- This is the key inequality. The NL proof uses p ≤ 2k.
private lemma pow_D_p_le_threshold (k p : ℕ) (hk : k ≥ 1) (hp : p.Prime)
    (hp_le : p ≤ 2 * k) :
    p ^ (D_p k p) ≤ union_bound_threshold k := by
  sorry -- key arithmetic, will work on separately

-- Goal 2: 2^{D_p/36} ≥ 32 * k
private lemma decay_estimate (k p : ℕ) (hk : k ≥ 1) (hp : p.Prime) :
    2 ^ (D_p k p / 36) ≥ 32 * k := by
  sorry -- arithmetic

-- The per-prime bad count bound
private lemma per_prime_bad_count (k p : ℕ) (m₀ : ℕ) 
    (hk : k ≥ 1) (hp : p.Prime) (hp_le : p ≤ 2 * k)
    (hm₀ : union_bound_threshold k ≤ m₀) :
    ((Ico m₀ (2 * m₀)).filter 
      (fun m => padicValNat p ((m + k).choose k) > padicValNat p ((2 * m).choose m))).card
    ≤ 4 * m₀ / (32 * k) := by
  sorry -- combine count_bad_interval_all with arithmetic bounds

-- Main proof
lemma exists_m_for_fixed_k' (k : ℕ) (hk : k ≥ 1)
    (m₀ : ℕ) (hm₀ : union_bound_threshold k ≤ m₀) :
    ∃ m : ℕ, m₀ ≤ m ∧ m < 2 * m₀ ∧
      ∀ p : ℕ, p.Prime → p ≤ 2 * k →
        padicValNat p ((m + k).choose k) ≤
          padicValNat p ((2 * m).choose m) := by
  -- The interval [m₀, 2*m₀) has m₀ elements
  -- The bad set for all primes is the union over p of bad_p
  -- Bad m = ∃ p prime, p ≤ 2k, v_p(C(m+k,k)) > v_p(C(2m,m))
  -- Good m = ∀ p prime, p ≤ 2k, v_p(C(m+k,k)) ≤ v_p(C(2m,m))
  -- We show |bad| < |Ico|, so good is nonempty.
  
  -- Step 1: m₀ > 0
  have hm₀_pos : m₀ > 0 := by
    have : union_bound_threshold k > 0 := by
      unfold union_bound_threshold
      positivity
    omega
  
  -- Step 2: Define the bad set
  set bad := (Ico m₀ (2 * m₀)).filter 
    (fun m => ∃ p, p.Prime ∧ p ≤ 2 * k ∧ 
      padicValNat p ((m + k).choose k) > padicValNat p ((2 * m).choose m))
  
  -- Step 3: The bad set is contained in the union of per-prime bad sets
  -- We need: |bad| < m₀ = |Ico m₀ (2*m₀)|
  
  -- Step 4: Bound |bad| using the union bound
  -- |bad| ≤ Σ_p |bad_p| where p ranges over primes ≤ 2k
  -- Each |bad_p| ≤ 4*m₀/(32k) = m₀/(8k)
  -- Total ≤ (2k) * m₀/(8k)
  -- We need this < m₀
  
  -- For now, let's show existence by contradiction
  by_contra h_no_good
  push_neg at h_no_good
  -- h_no_good : ∀ m, m₀ ≤ m → m < 2 * m₀ → ∃ p, p.Prime ∧ p ≤ 2 * k ∧ ...
  -- This means every m ∈ [m₀, 2*m₀) is bad
  -- So |bad| = m₀
  -- But we showed |bad| ≤ m₀/4, contradiction
  sorry

EOF
lake env lean /tmp/test_exists.lean 2>&1
```
The filter needs decidability. Let me use a different approach — use classical logic or change the formulation:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_exists2.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset Real Erdos728

-- Main proof structure
lemma exists_m_for_fixed_k' (k : ℕ) (hk : k ≥ 1)
    (m₀ : ℕ) (hm₀ : union_bound_threshold k ≤ m₀) :
    ∃ m : ℕ, m₀ ≤ m ∧ m < 2 * m₀ ∧
      ∀ p : ℕ, p.Prime → p ≤ 2 * k →
        padicValNat p ((m + k).choose k) ≤
          padicValNat p ((2 * m).choose m) := by
  -- m₀ > 0
  have hm₀_pos : m₀ > 0 := by
    have : union_bound_threshold k > 0 := by unfold union_bound_threshold; positivity
    omega
  -- For each prime p ≤ 2k, define the set of bad m values
  -- bad_p = {m ∈ [m₀, 2m₀) : v_p(C(m+k,k)) > v_p(C(2m,m))}
  -- The full bad set is the union: ⋃_p bad_p (for p prime, p ≤ 2k)
  -- A good m exists if the union is strictly smaller than [m₀, 2m₀)
  
  -- Strategy: by_contra, then every m in the interval is bad for some prime p,
  -- meaning the interval ⊆ ⋃_p bad_p.
  -- But |⋃_p bad_p| ≤ Σ_p |bad_p| < m₀ = |interval|, contradiction.
  
  by_contra h_no_good
  push_neg at h_no_good
  -- h_no_good : ∀ m, m₀ ≤ m → m < 2 * m₀ → ∃ p, p.Prime ∧ p ≤ 2*k ∧ v_p > v_p
  
  -- Define the primes set
  let primes_le_2k := (range (2 * k + 1)).filter Nat.Prime
  
  -- Define bad_p for each prime p
  let bad (p : ℕ) := (Ico m₀ (2 * m₀)).filter 
    (fun m => padicValNat p ((m + k).choose k) > padicValNat p ((2 * m).choose m))
  
  -- The interval Ico m₀ (2*m₀) ⊆ ⋃_{p ∈ primes_le_2k} bad p
  have h_cover : Ico m₀ (2 * m₀) ⊆ primes_le_2k.biUnion bad := by
    intro m hm
    rw [mem_Ico] at hm
    rw [mem_biUnion]
    obtain ⟨p, hp_prime, hp_le, hp_bad⟩ := h_no_good m hm.1 hm.2
    exact ⟨p, mem_filter.mpr ⟨mem_range.mpr (by omega), hp_prime⟩,
           mem_filter.mpr ⟨mem_Ico.mpr hm, hp_bad⟩⟩
  
  -- Card bound: |Ico| ≤ |⋃ bad_p| ≤ Σ |bad_p|
  have h_card_Ico : (Ico m₀ (2 * m₀)).card = m₀ := by simp [Nat.card_Ico]
  
  have h_card_union : (primes_le_2k.biUnion bad).card ≤ ∑ p ∈ primes_le_2k, (bad p).card :=
    card_biUnion_le
  
  -- Now I need: Σ_p |bad_p| < m₀
  -- This requires bounding each |bad_p| and summing
  
  sorry

EOF
lake env lean /tmp/test_exists2.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_exists3.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset Real Erdos728

lemma exists_m_for_fixed_k' (k : ℕ) (hk : k ≥ 1)
    (m₀ : ℕ) (hm₀ : union_bound_threshold k ≤ m₀) :
    ∃ m : ℕ, m₀ ≤ m ∧ m < 2 * m₀ ∧
      ∀ p : ℕ, p.Prime → p ≤ 2 * k →
        padicValNat p ((m + k).choose k) ≤
          padicValNat p ((2 * m).choose m) := by
  have hm₀_pos : m₀ > 0 := by
    have : union_bound_threshold k > 0 := by unfold union_bound_threshold; positivity
    omega
  let primes_le_2k := (range (2 * k + 1)).filter Nat.Prime
  let bad (p : ℕ) := (Ico m₀ (2 * m₀)).filter 
    (fun m => padicValNat p ((m + k).choose k) > padicValNat p ((2 * m).choose m))
  by_contra h_no_good
  push_neg at h_no_good
  have h_cover : Ico m₀ (2 * m₀) ⊆ primes_le_2k.biUnion bad := by
    intro m hm
    rw [mem_Ico] at hm
    rw [mem_biUnion]
    obtain ⟨p, hp_prime, hp_le, hp_bad⟩ := h_no_good m hm.1 hm.2
    exact ⟨p, mem_filter.mpr ⟨mem_range.mpr (by omega), hp_prime⟩,
           mem_filter.mpr ⟨mem_Ico.mpr hm, hp_bad⟩⟩
  have h_card_Ico : (Ico m₀ (2 * m₀)).card = m₀ := by simp [Nat.card_Ico]; omega
  have h_card_le : m₀ ≤ (primes_le_2k.biUnion bad).card := by
    rw [← h_card_Ico]; exact card_le_card h_cover
  have h_card_union : (primes_le_2k.biUnion bad).card ≤ ∑ p ∈ primes_le_2k, (bad p).card :=
    card_biUnion_le
  -- So m₀ ≤ Σ |bad_p|
  -- Now bound each |bad_p|
  -- Need: Σ |bad_p| < m₀, giving contradiction
  
  -- For the bound, we need count_bad_interval for each prime.
  -- Each bad_p has card ≤ (2*m₀)/2^(D_p/36) + (2*p^{D_p})/2^(D_p/36)
  -- With p^{D_p} ≤ m₀ and 2^{D_p/36} ≥ 32k, this gives ≤ 4*m₀/(32k) = m₀/(8k)
  -- Then Σ ≤ 2k * m₀/(8k) = m₀/4 < m₀
  
  sorry

EOF
lake env lean /tmp/test_exists3.lean 2>&1
```
Good, the structure works. Now I need to fill in the sorry. The key issue is bounding `Σ |bad_p| < m₀`.

Let me think about how to do the arithmetic cleanly in ℕ. For each prime p ≤ 2k with D_p chosen:
- count_bad_interval gives |bad_p| ≤ (2*m₀)/2^(D_p/36) + (2*p^{D_p})/2^(D_p/36)
- p^{D_p} ≤ m₀ gives second term ≤ (2*m₀)/2^(D_p/36)  
- So |bad_p| ≤ 2 * ((2*m₀)/2^(D_p/36)) ≤ (4*m₀)/2^(D_p/36) [in ℕ]
- 2^{D_p/36} ≥ 32k ≥ 32, so (4*m₀)/2^(D_p/36) ≤ (4*m₀)/(32k)

Wait, let me check: `2*(a/n) ≤ (2*a)/n` in ℕ? Actually `a/n * 2 + a/n * 2 = 2 * (a/n)` and `(2*a)/n ≥ 2 * (a/n)` since Nat.div is floor. So yes, `a/n + a/n = 2 * (a/n) ≤ (2*a)/n`.

So |bad_p| ≤ (2*m₀)/2^(D_p/36) + (2*m₀)/2^(D_p/36) = 2 * ((2*m₀)/2^(D_p/36)) ≤ (4*m₀)/2^(D_p/36) ≤ (4*m₀)/(32*k).

Now `(4*m₀)/(32*k) = m₀/(8*k)` in exact arithmetic, but in ℕ it's `4*m₀/(32*k)`. Let me check: `32*k = 4*(8*k)`, so `4*m₀/(32*k) = 4*m₀/(4*(8*k))`. And `(4*a)/(4*b) = a/b` in ℕ? Actually `Nat.mul_div_mul_left` gives `(k*a)/(k*b) = a/b` for k > 0. So yes, `4*m₀/(4*(8*k)) = m₀/(8*k)`.

Hmm wait, `32*k` might not equal `4*(8*k)` in some edge cases... no, `32*k = 4*8*k = 4*(8*k)`. OK.

Then the sum: `∑_{p ∈ primes_le_2k} m₀/(8*k)`. The number of terms is at most `(2*k+1).filter Prime .card ≤ 2*k`. So the sum ≤ `2*k * (m₀/(8*k))`.

In ℕ: `2*k * (m₀/(8*k)) ≤ (2*k * m₀)/(8*k) = m₀/4`. For the first step, `a * (b/c) ≤ (a*b)/c` in ℕ? Actually no, it's the opposite: `a * (b/c) ≤ a*b/c` is NOT always true in ℕ. Wait... `b/c ≤ b/c` trivially, and `a * (b/c) = a * floor(b/c)`. But `floor(a*b/c)` might be less than `a * floor(b/c)` since the remainder might accumulate. Actually:

`a * (b/c) ≤ (a*b)/c` is TRUE in ℕ because: let `b = c*q + r` with `r < c`. Then `a * q ≤ a*(c*q+r)/c = (a*c*q + a*r)/c ≥ a*q` since `a*r ≥ 0`. So yes, `a * (b/c) ≤ (a*b)/c`.

Great. So `2*k * (m₀/(8*k)) ≤ (2*k*m₀)/(8*k) = m₀/4`.

And we need `m₀/4 < m₀`, which is true when `m₀ > 0`.

So the arithmetic works. Now let me assemble all the pieces. Let me first prove the helper lemmas (`D_p_ge_threshold`, `pow_D_p_le_threshold`, `decay_estimate`), then prove the main theorem.

Let me start with the helper lemmas:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_helpers.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset Real Erdos728

-- D_p definition
private def D_p (k p : ℕ) : ℕ :=
  36 * (Nat.log 2 (16 * k) + 1) + 36 * (Nat.log p (k + 1)) + 36

-- Goal 1a: D_p ≥ 16 * log_p(k+1) + 16
private lemma D_p_ge_threshold (k p : ℕ) (hk : k ≥ 1) (hp : p.Prime) :
    D_p k p ≥ 16 * (Nat.log p (k + 1)) + 16 := by
  unfold D_p; omega

-- Goal 1b: p^{D_p} ≤ union_bound_threshold k for p ≤ 2k, k ≥ 1
-- D_p = 36*(log₂(16k)+1) + 36*log_p(k+1) + 36
-- union_bound_threshold k = (2k)^{72*(log₂(16k)+1) + 72}
-- 
-- We need p^{D_p} ≤ (2k)^{72*(log₂(16k)+1) + 72}
-- Since p ≤ 2k and k+1 ≤ 2k:
-- p^{D_p} ≤ (2k)^{D_p}
-- D_p = 36*(log₂(16k)+1) + 36*log_p(k+1) + 36
-- And (2k)^{log_p(k+1)} ≤ (2k)^{log₂(16k)+1} (since log_p(k+1) ≤ log₂(k+1) ≤ log₂(16k)+1)
-- Hmm, that's not right either. Let me think again.
-- 
-- p^{36*log_p(k+1)} = (p^{log_p(k+1)})^36 ≤ (k+1)^36 ≤ (2k)^36
-- p^{36*(log₂(16k)+1)} ≤ (2k)^{36*(log₂(16k)+1)}
-- p^{36} ≤ (2k)^{36}
-- So p^{D_p} ≤ (2k)^{36*(log₂(16k)+1)} * (2k)^36 * (2k)^36
--            = (2k)^{36*(log₂(16k)+1) + 72}
-- And 36*(log₂(16k)+1) + 72 ≤ 72*(log₂(16k)+1) + 72 ✓
-- So p^{D_p} ≤ (2k)^{72*(log₂(16k)+1) + 72} = union_bound_threshold k ✓

-- Let me try to prove this step by step.

private lemma pow_D_p_le_threshold (k p : ℕ) (hk : k ≥ 1) (hp : p.Prime)
    (hp_le : p ≤ 2 * k) :
    p ^ (D_p k p) ≤ union_bound_threshold k := by
  unfold D_p union_bound_threshold
  set L := Nat.log 2 (16 * k) + 1
  set S := Nat.log p (k + 1)
  -- Goal: p^(36*L + 36*S + 36) ≤ (2k)^(72*L + 72)
  -- = p^{36*L} * p^{36*S} * p^{36} ≤ (2k)^{36*L} * (2k)^{36} * (2k)^{36}
  -- ... ≤ (2k)^{36*L + 72} ≤ (2k)^{72*L + 72}
  
  -- Step 1: p ≤ 2k, so p^n ≤ (2k)^n for any n
  have h_base : p ≤ 2 * k := hp_le
  have h2k_ge_2 : 2 * k ≥ 2 := by omega
  
  -- Step 2: p^{36*S} ≤ (k+1)^36 ≤ (2k)^36
  -- Because p^S ≤ k+1 (by definition of floor log)
  have h_pS_le : p ^ S ≤ k + 1 := by
    exact Nat.pow_log_le_self p (by omega : k + 1 ≠ 0)
  
  -- Step 3: Combine
  calc p ^ (36 * L + 36 * S + 36)
      = p ^ (36 * L) * p ^ (36 * S) * p ^ 36 := by ring_nf; rw [pow_add, pow_add]
    _ = p ^ (36 * L) * (p ^ S) ^ 36 * p ^ 36 := by rw [pow_mul]
    _ ≤ (2 * k) ^ (36 * L) * (k + 1) ^ 36 * (2 * k) ^ 36 := by
        apply Nat.mul_le_mul
        apply Nat.mul_le_mul
        · exact Nat.pow_le_pow_left h_base _
        · exact Nat.pow_le_pow_left h_pS_le _
        · exact Nat.pow_le_pow_left h_base _
    _ ≤ (2 * k) ^ (36 * L) * (2 * k) ^ 36 * (2 * k) ^ 36 := by
        apply Nat.mul_le_mul_right
        apply Nat.mul_le_mul_left
        exact Nat.pow_le_pow_left (by omega : k + 1 ≤ 2 * k) _
    _ = (2 * k) ^ (36 * L + 36 + 36) := by
        rw [← pow_add, ← pow_add]
    _ = (2 * k) ^ (36 * L + 72) := by ring_nf
    _ ≤ (2 * k) ^ (72 * L + 72) := by
        apply Nat.pow_le_pow_right
        · omega
        · omega

EOF
lake env lean /tmp/test_helpers.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_helpers2.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset Real Erdos728

private def D_p (k p : ℕ) : ℕ :=
  36 * (Nat.log 2 (16 * k) + 1) + 36 * (Nat.log p (k + 1)) + 36

private lemma D_p_ge_threshold (k p : ℕ) :
    D_p k p ≥ 16 * (Nat.log p (k + 1)) + 16 := by
  unfold D_p; omega

-- Break the exponent into pieces  
private lemma pow_D_p_split (k p : ℕ) :
    p ^ (D_p k p) = p ^ (36 * (Nat.log 2 (16 * k) + 1)) * p ^ (36 * (Nat.log p (k + 1))) * p ^ 36 := by
  unfold D_p
  rw [show 36 * (Nat.log 2 (16 * k) + 1) + 36 * Nat.log p (k + 1) + 36 =
    36 * (Nat.log 2 (16 * k) + 1) + (36 * Nat.log p (k + 1) + 36) from by omega,
    pow_add, pow_add]

private lemma pow_D_p_le_threshold (k p : ℕ) (hk : k ≥ 1) (hp : p.Prime)
    (hp_le : p ≤ 2 * k) :
    p ^ (D_p k p) ≤ union_bound_threshold k := by
  unfold union_bound_threshold
  set L := Nat.log 2 (16 * k) + 1
  set S := Nat.log p (k + 1)
  have h2k_pos : 2 * k ≥ 2 := by omega
  have h_pS_le : p ^ S ≤ k + 1 := Nat.pow_log_le_self p (by omega)
  rw [pow_D_p_split]
  calc p ^ (36 * L) * p ^ (36 * S) * p ^ 36
      = p ^ (36 * L) * (p ^ S) ^ 36 * p ^ 36 := by rw [pow_mul p S 36]
    _ ≤ (2 * k) ^ (36 * L) * (k + 1) ^ 36 * (2 * k) ^ 36 := by
        apply Nat.mul_le_mul (Nat.mul_le_mul
          (Nat.pow_le_pow_left hp_le _) (Nat.pow_le_pow_left h_pS_le _))
          (Nat.pow_le_pow_left hp_le _)
    _ ≤ (2 * k) ^ (36 * L) * (2 * k) ^ 36 * (2 * k) ^ 36 := by
        apply Nat.mul_le_mul_right
        apply Nat.mul_le_mul_left
        exact Nat.pow_le_pow_left (by omega) _
    _ = (2 * k) ^ (36 * L + 36 + 36) := by rw [← pow_add, ← pow_add]
    _ = (2 * k) ^ (36 * L + 72) := by ring_nf
    _ ≤ (2 * k) ^ (72 * L + 72) := Nat.pow_le_pow_right (by omega) (by omega)

EOF
lake env lean /tmp/test_helpers2.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_helpers3.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset Real Erdos728

private def D_p (k p : ℕ) : ℕ :=
  36 * (Nat.log 2 (16 * k) + 1) + 36 * (Nat.log p (k + 1)) + 36

private lemma D_p_ge_threshold (k p : ℕ) :
    D_p k p ≥ 16 * (Nat.log p (k + 1)) + 16 := by
  unfold D_p; omega

private lemma pow_D_p_le_threshold (k p : ℕ) (hk : k ≥ 1) (hp : p.Prime)
    (hp_le : p ≤ 2 * k) :
    p ^ (D_p k p) ≤ union_bound_threshold k := by
  unfold union_bound_threshold D_p
  set L := Nat.log 2 (16 * k) + 1
  set S := Nat.log p (k + 1)
  have h_pS_le : p ^ S ≤ k + 1 := Nat.pow_log_le_self p (by omega)
  -- p^{36L + 36S + 36} = (p^{36L}) * (p^S)^{36} * p^{36}
  -- ≤ (2k)^{36L} * (k+1)^{36} * (2k)^{36}
  -- ≤ (2k)^{36L} * (2k)^{36} * (2k)^{36}
  -- = (2k)^{36L+72}
  -- ≤ (2k)^{72L+72}
  have h1 : p ^ (36 * L + 36 * S + 36) = 
      p ^ (36 * L) * (p ^ S) ^ 36 * p ^ 36 := by
    rw [show 36 * S = S * 36 from by ring, ← pow_mul]
    rw [show 36 * L + 36 * S + 36 = 36 * L + (S * 36 + 36) from by ring]
    rw [pow_add, pow_add]
  rw [h1]
  calc p ^ (36 * L) * (p ^ S) ^ 36 * p ^ 36
      ≤ (2 * k) ^ (36 * L) * (k + 1) ^ 36 * (2 * k) ^ 36 := by
        apply Nat.mul_le_mul (Nat.mul_le_mul
          (Nat.pow_le_pow_left hp_le _) (Nat.pow_le_pow_left h_pS_le _))
          (Nat.pow_le_pow_left hp_le _)
    _ ≤ (2 * k) ^ (36 * L) * (2 * k) ^ 36 * (2 * k) ^ 36 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
    _ = (2 * k) ^ (36 * L + 72) := by
        rw [← pow_add, ← pow_add]; ring_nf
    _ ≤ (2 * k) ^ (72 * L + 72) := Nat.pow_le_pow_right (by omega) (by omega)

-- Goal 2: 2^{D_p/36} ≥ 32k
-- D_p/36 = (36*L + 36*S + 36)/36 ≥ L + S + 1 (actually = L + S + 1 when divisible)
-- But in ℕ: (36*(L+S+1))/36 = L+S+1
-- 2^{L+S+1} ≥ 2^L ≥ 2^{log₂(16k)+1} ≥ 16k+1 > 16k ≥ 32k? No, that's wrong.
-- Actually 2^L = 2^{log₂(16k)+1} ≥ 16k+1 > 16k = 16k. But we need 32k.
-- Wait: L = log₂(16k) + 1 and S ≥ 0.
-- D_p/36 = (36*L + 36*S + 36)/36. Since divisible by 36: = L + S + 1.
-- 2^{L+S+1} = 2^L * 2^S * 2.
-- 2^L = 2^{log₂(16k)+1} ≥ 16k (since 2^{log₂(n)+1} > n, so ≥ n+1, but 2^{log₂(n)+1} ≥ n+1 ≥ n).
-- Actually 2^{log₂(n)} ≤ n < 2^{log₂(n)+1} for n ≥ 1.
-- So 2^L = 2^{log₂(16k)+1} ≥ 16k+1 > 16k. No, 2^{log₂(16k)} ≤ 16k.
-- 2^{log₂(16k)+1} = 2 * 2^{log₂(16k)} ... could be ≤ 2*16k = 32k.
-- But we need 2^{D_p/36} ≥ 32k.
-- With S ≥ 0: 2^{L+S+1} ≥ 2^{L+1} = 2 * 2^L ≥ 2 * 16k = 32k.
-- That needs 2^L ≥ 16k.
-- 2^L = 2^{log₂(16k)+1}. Is this ≥ 16k?
-- We know 16k < 2^{log₂(16k)+1}. So 2^{log₂(16k)+1} ≥ 16k + 1 > 16k.
-- Wait: Nat.lt_pow_succ_log_self says x < b^{log_b(x)+1}. So 16k < 2^{log₂(16k)+1}.
-- But that means 2^L > 16k, not ≥. In ℕ, > means ≥ +1, so 2^L ≥ 16k+1 > 16k.
-- But we need 2^L ≥ 16k, and 2^{L+1} = 2 * 2^L ≥ 2*(16k+1) = 32k+2 > 32k.
-- But D_p/36 = L + S + 1 ≥ L + 0 + 1 = L + 1.
-- So 2^{D_p/36} ≥ 2^{L+1} ≥ 32k + 2 > 32k. Wait, we need ≥ 32k, not >. 
-- In ℕ: 2^{L+1} = 2*2^L. 2^L ≥ 16k+1. So 2*2^L ≥ 32k+2 ≥ 32k. 
-- But actually Nat.lt_pow_succ_log_self says x < 2^{log₂(x)+1}, i.e., 2^{log₂(x)+1} ≥ x+1.
-- So 2^L = 2^{log₂(16k)+1} ≥ 16k+1 for 16k ≥ 1.
-- No wait, Nat.lt_pow_succ_log_self requires 1 < b. For b=2, it gives 16k < 2^{log₂(16k)+1}.
-- In ℕ, this means 2^{log₂(16k)+1} ≥ 16k + 1.
-- So 2^L ≥ 16k + 1.
-- But we also know S ≥ 0 and D_p/36 = L + S + 1.
-- So 2^{D_p/36} = 2^{L+S+1} ≥ 2^{L+1} = 2 * 2^L ≥ 2*(16k+1) = 32k + 2 ≥ 32k. Hmm wait...
-- Actually we need to be more careful. 2^L ≥ 16k+1 doesn't give 2*2^L ≥ 32k+2.
-- 2*(16k+1) = 32k+2 ≥ 32k. But I said 2^L ≥ 16k+1. Then 2^{L+1} = 2*2^L ≥ 2*(16k+1) = 32k+2.
-- Hmm, 2*n ≥ 2*m if n ≥ m. So 2^{L+1} ≥ 2*(16k+1) = 32k+2 ≥ 32*k.
-- ✓ (for k ≥ 1, 32k ≤ 32k+2)

private lemma decay_estimate (k p : ℕ) (hk : k ≥ 1) :
    2 ^ (D_p k p / 36) ≥ 32 * k := by
  unfold D_p
  set L := Nat.log 2 (16 * k) + 1
  set S := Nat.log p (k + 1)
  -- D_p/36 = (36*L + 36*S + 36)/36 = L + S + 1
  have hD36 : (36 * L + 36 * S + 36) / 36 = L + S + 1 := by omega
  rw [hD36]
  -- 2^{L+S+1} ≥ 2^{L+1} (since S ≥ 0)
  -- 2^{L+1} = 2 * 2^L
  -- 2^L = 2^{log₂(16k)+1} ≥ 16k + 1 (by Nat.lt_pow_succ_log_self)
  -- So 2^{L+1} ≥ 2*(16k+1) = 32k + 2 ≥ 32k
  have h2L : 2 ^ L ≥ 16 * k + 1 := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (16 * k)
    omega
  calc 2 ^ (L + S + 1) 
      ≥ 2 ^ (L + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    _ = 2 * 2 ^ L := by ring
    _ ≥ 2 * (16 * k + 1) := Nat.mul_le_mul_left 2 h2L
    _ = 32 * k + 2 := by ring
    _ ≥ 32 * k := by omega

EOF
lake env lean /tmp/test_helpers3.lean 2>&1
```
I need to fix the variable name issues — `set` in Lean uses a specific naming. Let me fix these issues:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_helpers4.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset Real Erdos728

private def D_p (k p : ℕ) : ℕ :=
  36 * (Nat.log 2 (16 * k) + 1) + 36 * (Nat.log p (k + 1)) + 36

private lemma D_p_ge_threshold (k p : ℕ) :
    D_p k p ≥ 16 * (Nat.log p (k + 1)) + 16 := by
  unfold D_p; omega

private lemma pow_D_p_le_threshold (k p : ℕ) (hk : k ≥ 1) (hp : p.Prime)
    (hp_le : p ≤ 2 * k) :
    p ^ (D_p k p) ≤ union_bound_threshold k := by
  unfold union_bound_threshold D_p
  -- Goal: p^(36*(log₂(16k)+1) + 36*log_p(k+1) + 36) ≤ (2k)^(72*(log₂(16k)+1) + 72)
  -- Split the LHS exponent
  have h_pS_le : p ^ (Nat.log p (k + 1)) ≤ k + 1 := Nat.pow_log_le_self p (by omega)
  -- p^{36*log_p(k+1)} = (p^{log_p(k+1)})^{36} ≤ (k+1)^{36} ≤ (2k)^{36}
  -- p^{36*(log₂(16k)+1)} ≤ (2k)^{36*(log₂(16k)+1)}
  -- p^{36} ≤ (2k)^{36}
  -- Product ≤ (2k)^{36*(log₂(16k)+1)+72} ≤ (2k)^{72*(log₂(16k)+1)+72}
  
  have h_split : 36 * (Nat.log 2 (16 * k) + 1) + 36 * Nat.log p (k + 1) + 36 =
      36 * (Nat.log 2 (16 * k) + 1) + (Nat.log p (k + 1)) * 36 + 36 := by ring
  rw [h_split, pow_add, pow_add, ← pow_mul]
  calc p ^ (36 * (Nat.log 2 (16 * k) + 1)) * (p ^ Nat.log p (k + 1)) ^ 36 * p ^ 36
      ≤ (2 * k) ^ (36 * (Nat.log 2 (16 * k) + 1)) * (k + 1) ^ 36 * (2 * k) ^ 36 := by
        apply Nat.mul_le_mul (Nat.mul_le_mul
          (Nat.pow_le_pow_left hp_le _) (Nat.pow_le_pow_left h_pS_le _))
          (Nat.pow_le_pow_left hp_le _)
    _ ≤ (2 * k) ^ (36 * (Nat.log 2 (16 * k) + 1)) * (2 * k) ^ 36 * (2 * k) ^ 36 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
    _ = (2 * k) ^ (36 * (Nat.log 2 (16 * k) + 1) + 36 + 36) := by rw [← pow_add, ← pow_add]
    _ ≤ (2 * k) ^ (72 * (Nat.log 2 (16 * k) + 1) + 72) := 
        Nat.pow_le_pow_right (by omega) (by omega)

private lemma decay_estimate (k p : ℕ) (hk : k ≥ 1) :
    2 ^ (D_p k p / 36) ≥ 32 * k := by
  unfold D_p
  have hD36 : (36 * (Nat.log 2 (16 * k) + 1) + 36 * Nat.log p (k + 1) + 36) / 36 = 
      Nat.log 2 (16 * k) + 1 + Nat.log p (k + 1) + 1 := by omega
  rw [hD36]
  have h16k_pos : 16 * k ≥ 1 := by omega
  have h2L : 2 ^ (Nat.log 2 (16 * k) + 1) ≥ 16 * k + 1 := by
    exact Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (16 * k)
  calc 2 ^ (Nat.log 2 (16 * k) + 1 + Nat.log p (k + 1) + 1)
      ≥ 2 ^ (Nat.log 2 (16 * k) + 1 + 0 + 1) := 
        Nat.pow_le_pow_right (by omega) (by omega)
    _ = 2 * 2 ^ (Nat.log 2 (16 * k) + 1) := by ring
    _ ≥ 2 * (16 * k + 1) := Nat.mul_le_mul_left 2 h2L
    _ ≥ 32 * k := by omega

EOF
lake env lean /tmp/test_helpers4.lean 2>&1
```
I see, `pow_mul` only rewrites `a ^ (m * n) = (a ^ m) ^ n`, but the rewrite `← pow_mul` goes the other direction. The issue is that `pow_add` already split it but `pow_mul` goes `a^(n*m) ↔ (a^n)^m`. Let me use `pow_mul'`:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_pow.lean << 'EOF'
import Mathlib.Algebra.GroupPower.Basic

#check @pow_mul
#check @pow_mul'
-- pow_mul (a : M) (m n : ℕ) : a ^ (m * n) = (a ^ m) ^ n
-- I need: a ^ (n * m) = (a ^ n) ^ m
-- pow_mul gives a^(m*n) = (a^m)^n
-- So for a^(S * 36), with m=S, n=36: a^(S*36) = (a^S)^36 ✓

example (p S : ℕ) : p ^ (S * 36) = (p ^ S) ^ 36 := by
  exact pow_mul p S 36

EOF
lake env lean /tmp/test_pow.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_pow.lean << 'EOF'
import Erdos.Lemma3Counting

example (p S : ℕ) : p ^ (S * 36) = (p ^ S) ^ 36 := pow_mul p S 36
EOF
lake env lean /tmp/test_pow.lean 2>&1
```
OK so the issue is that `rw [← pow_mul]` tries to find `(a^m)^n` pattern in the goal, but the goal has `p ^ (Nat.log p (k+1) * 36)` which is `p ^ (S * 36)` before the rewrite. So `rw [pow_mul]` should work to change it to `(p^S)^36`. But the `rw` happens BEFORE the calc, so the goal doesn't have this form yet. Let me restructure:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_helpers5.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset Real Erdos728

private def D_p (k p : ℕ) : ℕ :=
  36 * (Nat.log 2 (16 * k) + 1) + 36 * (Nat.log p (k + 1)) + 36

private lemma D_p_ge_threshold (k p : ℕ) :
    D_p k p ≥ 16 * (Nat.log p (k + 1)) + 16 := by
  unfold D_p; omega

private lemma pow_D_p_le_threshold (k p : ℕ) (hk : k ≥ 1) (hp : p.Prime)
    (hp_le : p ≤ 2 * k) :
    p ^ (D_p k p) ≤ union_bound_threshold k := by
  unfold union_bound_threshold D_p
  have h_pS_le : p ^ (Nat.log p (k + 1)) ≤ k + 1 := Nat.pow_log_le_self p (by omega)
  have h_split : 36 * (Nat.log 2 (16 * k) + 1) + 36 * Nat.log p (k + 1) + 36 =
      36 * (Nat.log 2 (16 * k) + 1) + (Nat.log p (k + 1)) * 36 + 36 := by ring
  rw [h_split, pow_add, pow_add, pow_mul]
  calc p ^ (36 * (Nat.log 2 (16 * k) + 1)) * (p ^ Nat.log p (k + 1)) ^ 36 * p ^ 36
      ≤ (2 * k) ^ (36 * (Nat.log 2 (16 * k) + 1)) * (k + 1) ^ 36 * (2 * k) ^ 36 :=
        Nat.mul_le_mul (Nat.mul_le_mul
          (Nat.pow_le_pow_left hp_le _) (Nat.pow_le_pow_left h_pS_le _))
          (Nat.pow_le_pow_left hp_le _)
    _ ≤ (2 * k) ^ (36 * (Nat.log 2 (16 * k) + 1)) * (2 * k) ^ 36 * (2 * k) ^ 36 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
    _ = (2 * k) ^ (36 * (Nat.log 2 (16 * k) + 1) + 36 + 36) := by rw [← pow_add, ← pow_add]
    _ ≤ (2 * k) ^ (72 * (Nat.log 2 (16 * k) + 1) + 72) := 
        Nat.pow_le_pow_right (by omega) (by omega)

private lemma decay_estimate (k p : ℕ) (hk : k ≥ 1) :
    2 ^ (D_p k p / 36) ≥ 32 * k := by
  unfold D_p
  have hD36 : (36 * (Nat.log 2 (16 * k) + 1) + 36 * Nat.log p (k + 1) + 36) / 36 = 
      Nat.log 2 (16 * k) + 1 + Nat.log p (k + 1) + 1 := by omega
  rw [hD36]
  have h2L : 2 ^ (Nat.log 2 (16 * k) + 1) ≥ 16 * k + 1 :=
    Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (16 * k)
  calc 2 ^ (Nat.log 2 (16 * k) + 1 + Nat.log p (k + 1) + 1)
      ≥ 2 ^ (Nat.log 2 (16 * k) + 1 + 0 + 1) := 
        Nat.pow_le_pow_right (by omega) (by omega)
    _ = 2 * 2 ^ (Nat.log 2 (16 * k) + 1) := by ring
    _ ≥ 2 * (16 * k + 1) := Nat.mul_le_mul_left 2 h2L
    _ ≥ 32 * k := by omega

EOF
lake env lean /tmp/test_helpers5.lean 2>&1
```
The issue is that `pow_mul` rewrites `p ^ (36 * (Nat.log 2 (16*k)+1))` as `(p^36)^(Nat.log 2 (16*k)+1)` rather than `(p^(Nat.log 2 (16*k)+1))^36` because `pow_mul` matches `a^(m*n) → (a^m)^n`. Let me use `show` to fix the form:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_helpers6.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset Real Erdos728

private def D_p (k p : ℕ) : ℕ :=
  36 * (Nat.log 2 (16 * k) + 1) + 36 * (Nat.log p (k + 1)) + 36

private lemma D_p_ge_threshold (k p : ℕ) :
    D_p k p ≥ 16 * (Nat.log p (k + 1)) + 16 := by
  unfold D_p; omega

private lemma pow_D_p_le_threshold (k p : ℕ) (hk : k ≥ 1) (hp : p.Prime)
    (hp_le : p ≤ 2 * k) :
    p ^ (D_p k p) ≤ union_bound_threshold k := by
  unfold union_bound_threshold D_p
  have h_pS_le : p ^ (Nat.log p (k + 1)) ≤ k + 1 := Nat.pow_log_le_self p (by omega)
  -- Rewrite exponent to separate the three parts
  have h1 : p ^ (36 * (Nat.log 2 (16 * k) + 1) + 36 * Nat.log p (k + 1) + 36) =
      p ^ (36 * (Nat.log 2 (16 * k) + 1)) * (p ^ Nat.log p (k + 1)) ^ 36 * p ^ 36 := by
    rw [show 36 * Nat.log p (k + 1) = Nat.log p (k + 1) * 36 from by ring]
    rw [← pow_mul, ← pow_add p, ← pow_add p]
    ring_nf
  rw [h1]
  calc p ^ (36 * (Nat.log 2 (16 * k) + 1)) * (p ^ Nat.log p (k + 1)) ^ 36 * p ^ 36
      ≤ (2 * k) ^ (36 * (Nat.log 2 (16 * k) + 1)) * (k + 1) ^ 36 * (2 * k) ^ 36 :=
        Nat.mul_le_mul (Nat.mul_le_mul
          (Nat.pow_le_pow_left hp_le _) (Nat.pow_le_pow_left h_pS_le _))
          (Nat.pow_le_pow_left hp_le _)
    _ ≤ (2 * k) ^ (36 * (Nat.log 2 (16 * k) + 1)) * (2 * k) ^ 36 * (2 * k) ^ 36 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
    _ = (2 * k) ^ (36 * (Nat.log 2 (16 * k) + 1) + 36 + 36) := by rw [← pow_add, ← pow_add]
    _ ≤ (2 * k) ^ (72 * (Nat.log 2 (16 * k) + 1) + 72) := 
        Nat.pow_le_pow_right (by omega) (by omega)

private lemma decay_estimate (k p : ℕ) (hk : k ≥ 1) :
    2 ^ (D_p k p / 36) ≥ 32 * k := by
  unfold D_p
  have hD36 : (36 * (Nat.log 2 (16 * k) + 1) + 36 * Nat.log p (k + 1) + 36) / 36 = 
      Nat.log 2 (16 * k) + 1 + Nat.log p (k + 1) + 1 := by omega
  rw [hD36]
  have h2L : 2 ^ (Nat.log 2 (16 * k) + 1) ≥ 16 * k + 1 :=
    Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (16 * k)
  calc 2 ^ (Nat.log 2 (16 * k) + 1 + Nat.log p (k + 1) + 1)
      ≥ 2 ^ (Nat.log 2 (16 * k) + 1 + 0 + 1) := 
        Nat.pow_le_pow_right (by omega) (by omega)
    _ = 2 * 2 ^ (Nat.log 2 (16 * k) + 1) := by ring
    _ ≥ 2 * (16 * k + 1) := Nat.mul_le_mul_left 2 h2L
    _ ≥ 32 * k := by omega

EOF
lake env lean /tmp/test_helpers6.lean 2>&1
```
There's an issue with the ring_nf. Let me debug:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_h1.lean << 'EOF'
import Erdos.Lemma3Counting

example (p : ℕ) (L S : ℕ) :
    p ^ (36 * L + 36 * S + 36) =
    p ^ (36 * L) * (p ^ S) ^ 36 * p ^ 36 := by
  rw [show 36 * S = S * 36 from by ring, ← pow_mul, ← pow_add, ← pow_add]
  congr 1; ring

EOF
lake env lean /tmp/test_h1.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_h1b.lean << 'EOF'
import Erdos.Lemma3Counting

example (p : ℕ) (L S : ℕ) :
    p ^ (36 * L + 36 * S + 36) =
    p ^ (36 * L) * (p ^ S) ^ 36 * p ^ 36 := by
  rw [show 36 * S = S * 36 from by ring, ← pow_mul, ← pow_add, ← pow_add]

EOF
lake env lean /tmp/test_h1b.lean 2>&1
```
OK so the `rw` finishes the goal. The extra `ring_nf` caused the error. Let me fix:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_helpers7.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset Real Erdos728

private def D_p (k p : ℕ) : ℕ :=
  36 * (Nat.log 2 (16 * k) + 1) + 36 * (Nat.log p (k + 1)) + 36

private lemma D_p_ge_threshold (k p : ℕ) :
    D_p k p ≥ 16 * (Nat.log p (k + 1)) + 16 := by
  unfold D_p; omega

private lemma pow_D_p_le_threshold (k p : ℕ) (hk : k ≥ 1) (hp : p.Prime)
    (hp_le : p ≤ 2 * k) :
    p ^ (D_p k p) ≤ union_bound_threshold k := by
  unfold union_bound_threshold D_p
  have h_pS_le : p ^ (Nat.log p (k + 1)) ≤ k + 1 := Nat.pow_log_le_self p (by omega)
  have h1 : p ^ (36 * (Nat.log 2 (16 * k) + 1) + 36 * Nat.log p (k + 1) + 36) =
      p ^ (36 * (Nat.log 2 (16 * k) + 1)) * (p ^ Nat.log p (k + 1)) ^ 36 * p ^ 36 := by
    rw [show 36 * Nat.log p (k + 1) = Nat.log p (k + 1) * 36 from by ring,
        ← pow_mul, ← pow_add, ← pow_add]
  rw [h1]
  calc p ^ (36 * (Nat.log 2 (16 * k) + 1)) * (p ^ Nat.log p (k + 1)) ^ 36 * p ^ 36
      ≤ (2 * k) ^ (36 * (Nat.log 2 (16 * k) + 1)) * (k + 1) ^ 36 * (2 * k) ^ 36 :=
        Nat.mul_le_mul (Nat.mul_le_mul
          (Nat.pow_le_pow_left hp_le _) (Nat.pow_le_pow_left h_pS_le _))
          (Nat.pow_le_pow_left hp_le _)
    _ ≤ (2 * k) ^ (36 * (Nat.log 2 (16 * k) + 1)) * (2 * k) ^ 36 * (2 * k) ^ 36 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
    _ = (2 * k) ^ (36 * (Nat.log 2 (16 * k) + 1) + 36 + 36) := by rw [← pow_add, ← pow_add]
    _ ≤ (2 * k) ^ (72 * (Nat.log 2 (16 * k) + 1) + 72) := 
        Nat.pow_le_pow_right (by omega) (by omega)

private lemma decay_estimate (k p : ℕ) (hk : k ≥ 1) :
    2 ^ (D_p k p / 36) ≥ 32 * k := by
  unfold D_p
  have hD36 : (36 * (Nat.log 2 (16 * k) + 1) + 36 * Nat.log p (k + 1) + 36) / 36 = 
      Nat.log 2 (16 * k) + 1 + Nat.log p (k + 1) + 1 := by omega
  rw [hD36]
  have h2L : 2 ^ (Nat.log 2 (16 * k) + 1) ≥ 16 * k + 1 :=
    Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (16 * k)
  calc 2 ^ (Nat.log 2 (16 * k) + 1 + Nat.log p (k + 1) + 1)
      ≥ 2 ^ (Nat.log 2 (16 * k) + 1 + 0 + 1) := 
        Nat.pow_le_pow_right (by omega) (by omega)
    _ = 2 * 2 ^ (Nat.log 2 (16 * k) + 1) := by ring
    _ ≥ 2 * (16 * k + 1) := Nat.mul_le_mul_left 2 h2L
    _ ≥ 32 * k := by omega

EOF
lake env lean /tmp/test_helpers7.lean 2>&1
```
All helper lemmas compile. Now let me assemble the full proof. I need to add:

1. `count_few_high_digits_all` (already proven)
2. `count_bad_interval_all` (needs p=2 case - I'll replicate the proof for p=2)
3. The helper lemmas above
4. The main `exists_m_for_fixed_k` proof

For `count_bad_interval_all`, rather than replicating the entire 100-line proof for p=2, let me try a shortcut: prove the `per_prime_bad_bound` directly using `count_bad_interval` for p≥3 and a sorry for p=2. Then I'll close the sorry as a separate matter.

Actually, wait. Let me re-examine whether I really need `count_bad_interval` for p=2, or if there's a simpler argument.

For k ≥ 1, the primes ≤ 2k include p=2. The bad set for p=2 is {m ∈ [m₀, 2m₀) : v_2(C(m+k,k)) > v_2(C(2m,m))}. We need its cardinality to be bounded.

But actually, the `count_bad_interval` proof for p≥3 is exactly the proof I want, just with `count_few_high_digits` relaxed to all primes. So if I have `count_few_high_digits_all`, I can build `count_bad_interval_all` for all primes.

Let me go ahead and replicate the `count_bad_interval` proof but using `count_few_high_digits_all`:
```bash
$ cd /home/jarred/code/erdos-728b && tm update erdos728b-r4m --status "Building count_bad_interval_all and assembling the full proof"
```
Let me now write the complete proof. I'll put everything into a single file and test it, then merge it into the main file. The key simplification: instead of replicating `count_bad_interval` for p=2, I'll use `count_bad_interval` for p≥3 and a sorry'd wrapper for all primes. Then I'll build the main proof structure.

Actually, let me try the cleanest approach: create `count_bad_interval_all` that simply calls `count_bad_interval` for p≥3 and uses `count_bad_interval` infrastructure for p=2. The `count_bad_interval` proof uses:
1. `bad_residue_sets` (no p≥3 needed)
2. `residue_count_interval` (no p≥3 needed)
3. `count_large_cascade` (no p≥3 needed)
4. `count_few_high_digits` (p≥3 needed → replace with `count_few_high_digits_all`)
5. Various arithmetic (no p≥3 needed)

So I need to replicate steps 1-5 but with step 4 replaced. The `count_bad_interval` proof is about 90 lines. Let me just replicate it with the fix:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_full.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset Real Erdos728

-- ============= Part 1: count_few_high_digits for all primes =============
-- (The existing version requires p ≥ 3 but the proof only uses p ≥ 2)

section AllPrimes

variable {p : ℕ}

private lemma count_few_high_digits_all (D : ℕ) (hp : p.Prime) (t : ℕ) (ht : t ≤ D/6) :
    ((range (p^D)).filter (fun m => count_high_digits p m D < t)).card ≤
    p^D / 2^(D/36) := by
  by_cases hp3 : p ≥ 3
  · exact count_few_high_digits D hp t ht hp3
  · -- p = 2 case (identical proof with probHigh 2 = 1/2)
    have hp_val : p = 2 := by have := hp.two_le; omega
    subst hp_val
    by_cases ht0 : t = 0; · simp [ht0]
    have ht_pos : t ≥ 1 := Nat.pos_of_ne_zero ht0
    have hD_ge_6 : D ≥ 6 := by omega
    have hD_pos : D > 0 := by omega
    have h_card_eq_fin :
        ((range (2^D)).filter (fun m => count_high_digits 2 m D < t)).card =
        ((Finset.univ : Finset (Fin (2^D))).filter
          (fun m : Fin (2^D) => count_high_digits 2 m.val D < t)).card := by
      apply Finset.card_bij
        (fun m hm => ⟨m, by rw [mem_filter] at hm; exact mem_range.mp hm.1⟩)
      · intro m hm; rw [mem_filter] at hm ⊢; exact ⟨mem_univ _, hm.2⟩
      · intro a _ b _ h; simp at h; exact h
      · intro b hb; refine ⟨b.val, ?_, Fin.ext rfl⟩
        rw [mem_filter]; exact ⟨mem_range.mpr b.isLt, (mem_filter.mp hb).2⟩
    have h_card_eq_ds :
        ((Finset.univ : Finset (Fin (2^D))).filter
          (fun m : Fin (2^D) => count_high_digits 2 m.val D < t)).card =
        ((Finset.univ : Finset (DigitSpace D 2)).filter
          (fun m : DigitSpace D 2 => highDigitCount m < t)).card := by
      have hbij := toDigitSpace_bijective hp D
      apply Finset.card_bij (fun m _ => toDigitSpace hp D m)
      · intro m hm; rw [mem_filter] at hm ⊢
        exact ⟨mem_univ _, by rw [highDigitCount_eq hp D m]; exact hm.2⟩
      · intro a _ b _ h; exact hbij.1 h
      · intro b hb; obtain ⟨a, ha⟩ := hbij.2 b
        refine ⟨a, ?_, ha⟩; rw [mem_filter]
        exact ⟨mem_univ _, by rw [← highDigitCount_eq hp D a, ha]; exact (mem_filter.mp hb).2⟩
    have h_subset :
        (Finset.univ.filter (fun m : DigitSpace D 2 => highDigitCount m < t)) ⊆
        (Finset.univ.filter (fun m : DigitSpace D 2 => (highDigitCount m : ℝ) ≤ ↑t)) := by
      intro m; simp only [mem_filter, mem_univ, true_and]
      exact fun h => by exact_mod_cast le_of_lt h
    have hph : probHigh 2 = 1/2 := by unfold probHigh; norm_num
    have h_t_lt : (t : ℝ) < ↑D * probHigh 2 := by
      rw [hph]; linarith [show (↑t : ℝ) ≤ ↑D / 6 from by
        have : (↑(t * 6) : ℝ) ≤ (↑D : ℝ) := by exact_mod_cast (show t * 6 ≤ D by omega)
        push_cast at this; linarith, show (↑D : ℝ) > 0 from by exact_mod_cast hD_pos]
    have hne : NeZero (2 : ℕ) := ⟨by omega⟩
    have h_chernoff := @count_few_high_digits_bound_chernoff D 2 hne (↑t) h_t_lt
    have h_exp_bound :
        exp (-2 * ((↑D * probHigh 2 - ↑t)^2) / (↑D : ℝ)) ≤ ((2 : ℝ)^(D/36))⁻¹ := by
      rw [hph]
      have h_gap : ↑D * ((1:ℝ)/2) - ↑t ≥ ↑D / 6 := by
        linarith [show (↑t : ℝ) ≤ ↑D / 6 from by
          have : (↑(t * 6) : ℝ) ≤ (↑D : ℝ) := by exact_mod_cast (show t * 6 ≤ D by omega)
          push_cast at this; linarith]
      have hD_r : (↑D : ℝ) > 0 := by exact_mod_cast hD_pos
      calc exp (-2 * ((↑D * ((1:ℝ)/2) - ↑t)^2) / ↑D)
          ≤ exp (-(↑D : ℝ) / 18) := by
            rw [exp_le_exp]
            calc -2 * (↑D * ((1:ℝ)/2) - ↑t)^2 / ↑D
                ≤ -2 * ((↑D : ℝ) / 6)^2 / ↑D := by
                  apply div_le_div_of_nonneg_right _ (le_of_lt hD_r)
                  nlinarith [sq_le_sq' (by linarith) h_gap]
              _ = -(↑D : ℝ) / 18 := by field_simp; ring
        _ ≤ ((2 : ℝ)^(D/36))⁻¹ := by
            rw [show ((2 : ℝ)^(D/36))⁻¹ = exp (-(↑(D/36) * Real.log 2)) from by
              rw [exp_neg]; congr 1; rw [← rpow_natCast, rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]; ring_nf]
            rw [exp_le_exp]
            nlinarith [
              show Real.log 2 ≤ 1 from by
                rw [← Real.log_exp 1]; exact Real.log_le_log (by norm_num) (by linarith [add_one_le_exp 1]),
              show (↑(D/36) : ℝ) ≤ (D : ℝ) / 18 from by
                have : (↑(D/36) : ℝ) ≤ (D : ℝ) / 36 := by
                  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 36)]; exact_mod_cast Nat.div_mul_le_self D 36
                linarith [show (D:ℝ) / 36 ≤ (D:ℝ) / 18 from by
                  apply div_le_div_of_nonneg_left _ (by norm_num) (by norm_num); exact_mod_cast Nat.zero_le D],
              show (↑(D/36) : ℝ) ≥ 0 from by exact_mod_cast Nat.zero_le _]
    rw [h_card_eq_fin, h_card_eq_ds]
    have h2_pos : (2 : ℕ)^(D/36) > 0 := by positivity
    rw [Nat.le_div_iff_mul_le h2_pos]
    have h_card_le := card_le_card h_subset
    suffices h : ((((Finset.univ.filter (fun m : DigitSpace D 2 => highDigitCount m < t)).card
        * 2^(D/36) : ℕ) : ℝ) ≤ ↑(2^D)) from by exact_mod_cast h
    push_cast
    calc ↑((Finset.univ.filter (fun m : DigitSpace D 2 => highDigitCount m < t)).card) * (2:ℝ)^(D/36)
        ≤ ↑((Finset.univ.filter (fun m : DigitSpace D 2 => (highDigitCount m : ℝ) ≤ ↑t)).card) * (2:ℝ)^(D/36) := by
          apply mul_le_mul_of_nonneg_right (by exact_mod_cast h_card_le) (by positivity)
      _ ≤ ((2:ℝ) ^ D * exp (-2 * ((↑D * probHigh 2 - ↑t)^2) / ↑D)) * (2:ℝ)^(D/36) := by
          apply mul_le_mul_of_nonneg_right h_chernoff (by positivity)
      _ ≤ ((2:ℝ) ^ D * ((2 : ℝ)^(D/36))⁻¹) * (2:ℝ)^(D/36) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left h_exp_bound (by positivity)
      _ = (2:ℝ) ^ D := by
          rw [mul_assoc, inv_mul_cancel₀ (by positivity : (2:ℝ)^(D/36) ≠ 0), mul_one]

-- count_bad_interval for all primes
-- Replicated from the existing proof, replacing count_few_high_digits with count_few_high_digits_all
private lemma count_bad_interval_all (D k m0 : ℕ)
    (hm0 : m0 ≥ p^D) (hD : D ≥ 16 * (log p (k + 1)) + 16)
    (hp : p.Prime) (hk : k ≥ 1) :
    ((Ico m0 (2 * m0)).filter (fun m => padicValNat p ((m + k).choose k) > padicValNat p ((2 * m).choose m))).card
    ≤ (2 * m0) / 2 ^ (D / 36) + (2 * p^D) / 2 ^ (D / 36) := by
  by_cases hp3 : p ≥ 3
  · exact count_bad_interval D k m0 hm0 hD hp hp3 hk
  · -- p = 2 (or rather p < 3, so p = 2 since prime)
    -- The proof is identical to count_bad_interval, except using count_few_high_digits_all
    -- at the one place where hp_ge_3 was needed.
    have hp2 : p ≥ 2 := hp.two_le
    have hp_pos : p > 0 := hp.pos
    have hpD_pos : p ^ D > 0 := Nat.pos_of_ne_zero (by positivity)
    have h2x_pos : 2 ^ (D / 36) > 0 := Nat.pos_of_ne_zero (by positivity)
    set s := log p k
    set x := D / 36
    let R1 := (range (p ^ D)).filter (fun r => cascade_length (p := p) k D r ≥ D / 6 - s)
    let R2 := (range (p ^ D)).filter (fun r => count_high_digits p r D < D / 6)
    let R := R1 ∪ R2
    have hR_mem : ∀ r ∈ R, r < p ^ D := by
      intro r hr; rw [mem_union] at hr
      rcases hr with hr1 | hr2
      · exact mem_range.mp (mem_filter.mp hr1).1
      · exact mem_range.mp (mem_filter.mp hr2).1
    have h_bad_residues := bad_residue_sets D k hp hD
    have h_subset : (Ico m0 (2 * m0)).filter
        (fun m => padicValNat p ((m + k).choose k) > padicValNat p ((2 * m).choose m)) ⊆
        (Ico m0 (2 * m0)).filter (fun m => m % p ^ D ∈ R) := by
      intro m hm; rw [mem_filter] at hm ⊢; refine ⟨hm.1, ?_⟩
      by_cases h1 : padicValNat p ((m + k).choose k) > D / 6
      · exact mem_union_left R2 (h_bad_residues.1 m h1)
      · push_neg at h1
        exact mem_union_right R1 (h_bad_residues.2 m (by omega))
    have hm0_le : m0 ≤ 2 * m0 := Nat.le_mul_of_pos_left m0 (by omega)
    have h_resid := residue_count_interval D hp hR_mem m0 (2 * m0) hm0_le
    have h_card_R : R.card ≤ R1.card + R2.card := card_union_le R1 R2
    have hD_ge : D ≥ 16 := by omega
    have hs_le : s ≤ (D - 16) / 16 := by
      have : s ≤ log p (k + 1) := Nat.log_mono_right (by omega); omega
    have hT_le : D / 6 - s ≤ D - (s + 1) := by omega
    have h_R1 := count_large_cascade k D hp (D / 6 - s) hT_le
    -- Key change: use count_few_high_digits_all instead of count_few_high_digits
    have h_R2 := count_few_high_digits_all D hp (D / 6) (le_refl _)
    have h_exp_ge : D / 6 - s ≥ D / 36 := by omega
    have h_pow_ge : p ^ (D / 6 - s) ≥ 2 ^ (D / 36) :=
      calc p ^ (D / 6 - s) ≥ 2 ^ (D / 6 - s) := Nat.pow_le_pow_left (by omega) _
        _ ≥ 2 ^ (D / 36) := Nat.pow_le_pow_right (by omega) h_exp_ge
    have h_R1_bound : R1.card ≤ p ^ D / 2 ^ x := by
      calc R1.card ≤ p ^ (D - (D / 6 - s)) := h_R1
        _ = p ^ D / p ^ (D / 6 - s) := by rw [Nat.pow_div (by omega) (by omega)]
        _ ≤ p ^ D / 2 ^ x := Nat.div_le_div_left h_pow_ge h2x_pos
    have h_mul_div : 2 * (p ^ D / 2 ^ x) ≤ 2 * p ^ D / 2 ^ x := by
      rw [Nat.le_div_iff_mul_le h2x_pos]
      calc 2 * (p ^ D / 2 ^ x) * 2 ^ x
          = 2 * (2 ^ x * (p ^ D / 2 ^ x)) := by ring
        _ ≤ 2 * p ^ D := Nat.mul_le_mul_left 2 (Nat.mul_div_le _ _)
    have h_R_bound : R.card ≤ 2 * p ^ D / 2 ^ x := by
      calc R.card ≤ R1.card + R2.card := h_card_R
        _ ≤ p ^ D / 2 ^ x + p ^ D / 2 ^ x := Nat.add_le_add h_R1_bound h_R2
        _ = 2 * (p ^ D / 2 ^ x) := by ring
        _ ≤ 2 * p ^ D / 2 ^ x := h_mul_div
    have h_interval_len : 2 * m0 - m0 = m0 := by omega
    calc ((Ico m0 (2 * m0)).filter _).card
        ≤ ((Ico m0 (2 * m0)).filter (fun m => m % p ^ D ∈ R)).card := card_le_card h_subset
      _ ≤ R.card * (m0 / p ^ D + 1) := by rw [h_interval_len] at h_resid; exact h_resid
      _ ≤ (2 * p ^ D / 2 ^ x) * (m0 / p ^ D + 1) := Nat.mul_le_mul_right _ h_R_bound
      _ = (2 * p ^ D / 2 ^ x) * (m0 / p ^ D) + (2 * p ^ D / 2 ^ x) := by ring
      _ ≤ 2 * m0 / 2 ^ x + 2 * p ^ D / 2 ^ x := by
          apply Nat.add_le_add_right
          conv_lhs => rw [show m0 / p ^ D = 2 * m0 / (2 * p ^ D) from
            (Nat.mul_div_mul_left m0 (p ^ D) (by omega : 2 > 0)).symm]
          exact div_mul_div_le (2 * p ^ D) (2 * m0) (2 ^ x) h2x_pos

end AllPrimes

EOF
lake env lean /tmp/test_full.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && grep -n "div_mul_div_le" Erdos/Lemma3Counting.lean
```
It's a private lemma. Let me add a local version:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_full2.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset Real Erdos728

section AllPrimes

variable {p : ℕ}

private lemma div_mul_div_le' (a b c : ℕ) (hc : c > 0) :
    (a / c) * (b / a) ≤ b / c := by
  rw [Nat.le_div_iff_mul_le hc]
  calc (a / c) * (b / a) * c
      = (c * (a / c)) * (b / a) := by ring
    _ ≤ a * (b / a) := Nat.mul_le_mul_right _ (Nat.mul_div_le a c)
    _ ≤ b := Nat.mul_div_le b a

private lemma count_few_high_digits_all (D : ℕ) (hp : p.Prime) (t : ℕ) (ht : t ≤ D/6) :
    ((range (p^D)).filter (fun m => count_high_digits p m D < t)).card ≤
    p^D / 2^(D/36) := by
  by_cases hp3 : p ≥ 3
  · exact count_few_high_digits D hp t ht hp3
  · have hp_val : p = 2 := by have := hp.two_le; omega
    subst hp_val
    by_cases ht0 : t = 0; · simp [ht0]
    have ht_pos : t ≥ 1 := Nat.pos_of_ne_zero ht0
    have hD_ge_6 : D ≥ 6 := by omega
    have hD_pos : D > 0 := by omega
    have h_card_eq_fin :
        ((range (2^D)).filter (fun m => count_high_digits 2 m D < t)).card =
        ((Finset.univ : Finset (Fin (2^D))).filter
          (fun m : Fin (2^D) => count_high_digits 2 m.val D < t)).card := by
      apply Finset.card_bij
        (fun m hm => ⟨m, by rw [mem_filter] at hm; exact mem_range.mp hm.1⟩)
      · intro m hm; rw [mem_filter] at hm ⊢; exact ⟨mem_univ _, hm.2⟩
      · intro a _ b _ h; simp at h; exact h
      · intro b hb; refine ⟨b.val, ?_, Fin.ext rfl⟩
        rw [mem_filter]; exact ⟨mem_range.mpr b.isLt, (mem_filter.mp hb).2⟩
    have h_card_eq_ds :
        ((Finset.univ : Finset (Fin (2^D))).filter
          (fun m : Fin (2^D) => count_high_digits 2 m.val D < t)).card =
        ((Finset.univ : Finset (DigitSpace D 2)).filter
          (fun m : DigitSpace D 2 => highDigitCount m < t)).card := by
      have hbij := toDigitSpace_bijective hp D
      apply Finset.card_bij (fun m _ => toDigitSpace hp D m)
      · intro m hm; rw [mem_filter] at hm ⊢
        exact ⟨mem_univ _, by rw [highDigitCount_eq hp D m]; exact hm.2⟩
      · intro a _ b _ h; exact hbij.1 h
      · intro b hb; obtain ⟨a, ha⟩ := hbij.2 b
        refine ⟨a, ?_, ha⟩; rw [mem_filter]
        exact ⟨mem_univ _, by rw [← highDigitCount_eq hp D a, ha]; exact (mem_filter.mp hb).2⟩
    have h_subset :
        (Finset.univ.filter (fun m : DigitSpace D 2 => highDigitCount m < t)) ⊆
        (Finset.univ.filter (fun m : DigitSpace D 2 => (highDigitCount m : ℝ) ≤ ↑t)) := by
      intro m; simp only [mem_filter, mem_univ, true_and]
      exact fun h => by exact_mod_cast le_of_lt h
    have hph : probHigh 2 = 1/2 := by unfold probHigh; norm_num
    have h_t_lt : (t : ℝ) < ↑D * probHigh 2 := by
      rw [hph]; linarith [show (↑t : ℝ) ≤ ↑D / 6 from by
        have : (↑(t * 6) : ℝ) ≤ (↑D : ℝ) := by exact_mod_cast (show t * 6 ≤ D by omega)
        push_cast at this; linarith, show (↑D : ℝ) > 0 from by exact_mod_cast hD_pos]
    have hne : NeZero (2 : ℕ) := ⟨by omega⟩
    have h_chernoff := @count_few_high_digits_bound_chernoff D 2 hne (↑t) h_t_lt
    have h_exp_bound :
        exp (-2 * ((↑D * probHigh 2 - ↑t)^2) / (↑D : ℝ)) ≤ ((2 : ℝ)^(D/36))⁻¹ := by
      rw [hph]
      have h_gap : ↑D * ((1:ℝ)/2) - ↑t ≥ ↑D / 6 := by
        linarith [show (↑t : ℝ) ≤ ↑D / 6 from by
          have : (↑(t * 6) : ℝ) ≤ (↑D : ℝ) := by exact_mod_cast (show t * 6 ≤ D by omega)
          push_cast at this; linarith]
      have hD_r : (↑D : ℝ) > 0 := by exact_mod_cast hD_pos
      calc exp (-2 * ((↑D * ((1:ℝ)/2) - ↑t)^2) / ↑D)
          ≤ exp (-(↑D : ℝ) / 18) := by
            rw [exp_le_exp]
            calc -2 * (↑D * ((1:ℝ)/2) - ↑t)^2 / ↑D
                ≤ -2 * ((↑D : ℝ) / 6)^2 / ↑D := by
                  apply div_le_div_of_nonneg_right _ (le_of_lt hD_r)
                  nlinarith [sq_le_sq' (by linarith) h_gap]
              _ = -(↑D : ℝ) / 18 := by field_simp; ring
        _ ≤ ((2 : ℝ)^(D/36))⁻¹ := by
            rw [show ((2 : ℝ)^(D/36))⁻¹ = exp (-(↑(D/36) * Real.log 2)) from by
              rw [exp_neg]; congr 1; rw [← rpow_natCast, rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]; ring_nf]
            rw [exp_le_exp]
            nlinarith [
              show Real.log 2 ≤ 1 from by
                rw [← Real.log_exp 1]; exact Real.log_le_log (by norm_num) (by linarith [add_one_le_exp 1]),
              show (↑(D/36) : ℝ) ≤ (D : ℝ) / 18 from by
                have : (↑(D/36) : ℝ) ≤ (D : ℝ) / 36 := by
                  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 36)]; exact_mod_cast Nat.div_mul_le_self D 36
                linarith [show (D:ℝ) / 36 ≤ (D:ℝ) / 18 from by
                  apply div_le_div_of_nonneg_left _ (by norm_num) (by norm_num); exact_mod_cast Nat.zero_le D],
              show (↑(D/36) : ℝ) ≥ 0 from by exact_mod_cast Nat.zero_le _]
    rw [h_card_eq_fin, h_card_eq_ds]
    have h2_pos : (2 : ℕ)^(D/36) > 0 := by positivity
    rw [Nat.le_div_iff_mul_le h2_pos]
    have h_card_le := card_le_card h_subset
    suffices h : ((((Finset.univ.filter (fun m : DigitSpace D 2 => highDigitCount m < t)).card
        * 2^(D/36) : ℕ) : ℝ) ≤ ↑(2^D)) from by exact_mod_cast h
    push_cast
    calc ↑((Finset.univ.filter (fun m : DigitSpace D 2 => highDigitCount m < t)).card) * (2:ℝ)^(D/36)
        ≤ ↑((Finset.univ.filter (fun m : DigitSpace D 2 => (highDigitCount m : ℝ) ≤ ↑t)).card) * (2:ℝ)^(D/36) := by
          apply mul_le_mul_of_nonneg_right (by exact_mod_cast h_card_le) (by positivity)
      _ ≤ ((2:ℝ) ^ D * exp (-2 * ((↑D * probHigh 2 - ↑t)^2) / ↑D)) * (2:ℝ)^(D/36) := by
          apply mul_le_mul_of_nonneg_right h_chernoff (by positivity)
      _ ≤ ((2:ℝ) ^ D * ((2 : ℝ)^(D/36))⁻¹) * (2:ℝ)^(D/36) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left h_exp_bound (by positivity)
      _ = (2:ℝ) ^ D := by
          rw [mul_assoc, inv_mul_cancel₀ (by positivity : (2:ℝ)^(D/36) ≠ 0), mul_one]

-- count_bad_interval for all primes
private lemma count_bad_interval_all (D k m0 : ℕ)
    (hm0 : m0 ≥ p^D) (hD : D ≥ 16 * (log p (k + 1)) + 16)
    (hp : p.Prime) (hk : k ≥ 1) :
    ((Ico m0 (2 * m0)).filter (fun m => padicValNat p ((m + k).choose k) > padicValNat p ((2 * m).choose m))).card
    ≤ (2 * m0) / 2 ^ (D / 36) + (2 * p^D) / 2 ^ (D / 36) := by
  by_cases hp3 : p ≥ 3
  · exact count_bad_interval D k m0 hm0 hD hp hp3 hk
  · have hp2 : p ≥ 2 := hp.two_le
    have hp_pos : p > 0 := hp.pos
    have hpD_pos : p ^ D > 0 := Nat.pos_of_ne_zero (by positivity)
    have h2x_pos : 2 ^ (D / 36) > 0 := Nat.pos_of_ne_zero (by positivity)
    set s := log p k; set x := D / 36
    let R1 := (range (p ^ D)).filter (fun r => cascade_length (p := p) k D r ≥ D / 6 - s)
    let R2 := (range (p ^ D)).filter (fun r => count_high_digits p r D < D / 6)
    let R := R1 ∪ R2
    have hR_mem : ∀ r ∈ R, r < p ^ D := by
      intro r hr; rw [mem_union] at hr
      rcases hr with hr1 | hr2
      · exact mem_range.mp (mem_filter.mp hr1).1
      · exact mem_range.mp (mem_filter.mp hr2).1
    have h_bad_residues := bad_residue_sets D k hp hD
    have h_subset : (Ico m0 (2 * m0)).filter
        (fun m => padicValNat p ((m + k).choose k) > padicValNat p ((2 * m).choose m)) ⊆
        (Ico m0 (2 * m0)).filter (fun m => m % p ^ D ∈ R) := by
      intro m hm; rw [mem_filter] at hm ⊢; refine ⟨hm.1, ?_⟩
      by_cases h1 : padicValNat p ((m + k).choose k) > D / 6
      · exact mem_union_left R2 (h_bad_residues.1 m h1)
      · push_neg at h1; exact mem_union_right R1 (h_bad_residues.2 m (by omega))
    have hm0_le : m0 ≤ 2 * m0 := Nat.le_mul_of_pos_left m0 (by omega)
    have h_resid := residue_count_interval D hp hR_mem m0 (2 * m0) hm0_le
    have hD_ge : D ≥ 16 := by omega
    have hs_le : s ≤ (D - 16) / 16 := by
      have : s ≤ log p (k + 1) := Nat.log_mono_right (by omega); omega
    have hT_le : D / 6 - s ≤ D - (s + 1) := by omega
    have h_R1 := count_large_cascade k D hp (D / 6 - s) hT_le
    have h_R2 := count_few_high_digits_all D hp (D / 6) (le_refl _)
    have h_exp_ge : D / 6 - s ≥ D / 36 := by omega
    have h_pow_ge : p ^ (D / 6 - s) ≥ 2 ^ (D / 36) :=
      calc p ^ (D / 6 - s) ≥ 2 ^ (D / 6 - s) := Nat.pow_le_pow_left (by omega) _
        _ ≥ 2 ^ (D / 36) := Nat.pow_le_pow_right (by omega) h_exp_ge
    have h_R1_bound : R1.card ≤ p ^ D / 2 ^ x := by
      calc R1.card ≤ p ^ (D - (D / 6 - s)) := h_R1
        _ = p ^ D / p ^ (D / 6 - s) := by rw [Nat.pow_div (by omega) (by omega)]
        _ ≤ p ^ D / 2 ^ x := Nat.div_le_div_left h_pow_ge h2x_pos
    have h_mul_div : 2 * (p ^ D / 2 ^ x) ≤ 2 * p ^ D / 2 ^ x := by
      rw [Nat.le_div_iff_mul_le h2x_pos]
      calc 2 * (p ^ D / 2 ^ x) * 2 ^ x
          = 2 * (2 ^ x * (p ^ D / 2 ^ x)) := by ring
        _ ≤ 2 * p ^ D := Nat.mul_le_mul_left 2 (Nat.mul_div_le _ _)
    have h_R_bound : R.card ≤ 2 * p ^ D / 2 ^ x := by
      calc R.card ≤ R1.card + R2.card := card_union_le R1 R2
        _ ≤ p ^ D / 2 ^ x + p ^ D / 2 ^ x := Nat.add_le_add h_R1_bound h_R2
        _ = 2 * (p ^ D / 2 ^ x) := by ring
        _ ≤ 2 * p ^ D / 2 ^ x := h_mul_div
    have h_interval_len : 2 * m0 - m0 = m0 := by omega
    calc ((Ico m0 (2 * m0)).filter _).card
        ≤ ((Ico m0 (2 * m0)).filter (fun m => m % p ^ D ∈ R)).card := card_le_card h_subset
      _ ≤ R.card * (m0 / p ^ D + 1) := by rw [h_interval_len] at h_resid; exact h_resid
      _ ≤ (2 * p ^ D / 2 ^ x) * (m0 / p ^ D + 1) := Nat.mul_le_mul_right _ h_R_bound
      _ = (2 * p ^ D / 2 ^ x) * (m0 / p ^ D) + (2 * p ^ D / 2 ^ x) := by ring
      _ ≤ 2 * m0 / 2 ^ x + 2 * p ^ D / 2 ^ x := by
          apply Nat.add_le_add_right
          conv_lhs => rw [show m0 / p ^ D = 2 * m0 / (2 * p ^ D) from
            (Nat.mul_div_mul_left m0 (p ^ D) (by omega : 2 > 0)).symm]
          exact div_mul_div_le' (2 * p ^ D) (2 * m0) (2 ^ x) h2x_pos

end AllPrimes

EOF
lake env lean /tmp/test_full2.lean 2>&1
```
Both `count_few_high_digits_all` and `count_bad_interval_all` compile. Now let me build the main proof. Let me assemble everything:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_main_final.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset Real Erdos728

section UnionBoundProof

variable {p : ℕ}

-- Helper lemmas (already verified to compile)
private lemma div_mul_div_le' (a b c : ℕ) (hc : c > 0) :
    (a / c) * (b / a) ≤ b / c := by
  rw [Nat.le_div_iff_mul_le hc]
  calc (a / c) * (b / a) * c = (c * (a / c)) * (b / a) := by ring
    _ ≤ a * (b / a) := Nat.mul_le_mul_right _ (Nat.mul_div_le a c)
    _ ≤ b := Nat.mul_div_le b a

-- D_p definition
private def D_p (k p : ℕ) : ℕ :=
  36 * (Nat.log 2 (16 * k) + 1) + 36 * (Nat.log p (k + 1)) + 36

private lemma D_p_ge_threshold (k p : ℕ) :
    D_p k p ≥ 16 * (Nat.log p (k + 1)) + 16 := by
  unfold D_p; omega

private lemma pow_D_p_le_threshold (k p : ℕ) (hk : k ≥ 1) (hp : p.Prime)
    (hp_le : p ≤ 2 * k) :
    p ^ (D_p k p) ≤ union_bound_threshold k := by
  unfold union_bound_threshold D_p
  have h_pS_le : p ^ (Nat.log p (k + 1)) ≤ k + 1 := Nat.pow_log_le_self p (by omega)
  have h1 : p ^ (36 * (Nat.log 2 (16 * k) + 1) + 36 * Nat.log p (k + 1) + 36) =
      p ^ (36 * (Nat.log 2 (16 * k) + 1)) * (p ^ Nat.log p (k + 1)) ^ 36 * p ^ 36 := by
    rw [show 36 * Nat.log p (k + 1) = Nat.log p (k + 1) * 36 from by ring,
        ← pow_mul, ← pow_add, ← pow_add]
  rw [h1]
  calc p ^ (36 * (Nat.log 2 (16 * k) + 1)) * (p ^ Nat.log p (k + 1)) ^ 36 * p ^ 36
      ≤ (2 * k) ^ (36 * (Nat.log 2 (16 * k) + 1)) * (k + 1) ^ 36 * (2 * k) ^ 36 :=
        Nat.mul_le_mul (Nat.mul_le_mul
          (Nat.pow_le_pow_left hp_le _) (Nat.pow_le_pow_left h_pS_le _))
          (Nat.pow_le_pow_left hp_le _)
    _ ≤ (2 * k) ^ (36 * (Nat.log 2 (16 * k) + 1)) * (2 * k) ^ 36 * (2 * k) ^ 36 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
    _ = (2 * k) ^ (36 * (Nat.log 2 (16 * k) + 1) + 36 + 36) := by rw [← pow_add, ← pow_add]
    _ ≤ (2 * k) ^ (72 * (Nat.log 2 (16 * k) + 1) + 72) :=
        Nat.pow_le_pow_right (by omega) (by omega)

private lemma decay_estimate (k p : ℕ) (hk : k ≥ 1) :
    2 ^ (D_p k p / 36) ≥ 32 * k := by
  unfold D_p
  have hD36 : (36 * (Nat.log 2 (16 * k) + 1) + 36 * Nat.log p (k + 1) + 36) / 36 =
      Nat.log 2 (16 * k) + 1 + Nat.log p (k + 1) + 1 := by omega
  rw [hD36]
  have h2L : 2 ^ (Nat.log 2 (16 * k) + 1) ≥ 16 * k + 1 :=
    Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (16 * k)
  calc 2 ^ (Nat.log 2 (16 * k) + 1 + Nat.log p (k + 1) + 1)
      ≥ 2 ^ (Nat.log 2 (16 * k) + 1 + 0 + 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
    _ = 2 * 2 ^ (Nat.log 2 (16 * k) + 1) := by ring
    _ ≥ 2 * (16 * k + 1) := Nat.mul_le_mul_left 2 h2L
    _ ≥ 32 * k := by omega

-- Forward declaration of count_bad_interval_all (proved separately, will be added)
-- For now, using sorry to test the main proof structure
private lemma count_bad_interval_all (D k m0 : ℕ)
    (hm0 : m0 ≥ p^D) (hD : D ≥ 16 * (log p (k + 1)) + 16)
    (hp : p.Prime) (hk : k ≥ 1) :
    ((Ico m0 (2 * m0)).filter (fun m => padicValNat p ((m + k).choose k) > padicValNat p ((2 * m).choose m))).card
    ≤ (2 * m0) / 2 ^ (D / 36) + (2 * p^D) / 2 ^ (D / 36) := by
  by_cases hp3 : p ≥ 3
  · exact count_bad_interval D k m0 hm0 hD hp hp3 hk
  · sorry -- p=2 case (proved in test_full2.lean)

-- Per-prime bad count ≤ m₀/(8k)
-- Uses count_bad_interval_all + arithmetic
private lemma per_prime_bound (k : ℕ) (hk : k ≥ 1) (p₀ : ℕ) (hp₀ : p₀.Prime) (hp₀_le : p₀ ≤ 2 * k)
    (m₀ : ℕ) (hm₀ : union_bound_threshold k ≤ m₀) :
    ((Ico m₀ (2 * m₀)).filter
      (fun m => padicValNat p₀ ((m + k).choose k) > padicValNat p₀ ((2 * m).choose m))).card
    ≤ m₀ / (8 * k) := by
  -- D_p₀ satisfies the threshold
  set D := D_p k p₀
  have hD_ge : D ≥ 16 * (log p₀ (k + 1)) + 16 := D_p_ge_threshold k p₀
  -- p₀^D ≤ m₀
  have hpD_le : p₀ ^ D ≤ m₀ :=
    le_trans (pow_D_p_le_threshold k p₀ hk hp₀ hp₀_le) hm₀
  -- 2^{D/36} ≥ 32k
  have h_decay : 2 ^ (D / 36) ≥ 32 * k := decay_estimate k p₀ hk
  -- p₀^D ≤ m₀ so both terms ≤ 2*m₀/2^{D/36}
  have h2x_pos : 2 ^ (D / 36) > 0 := by positivity
  -- Apply count_bad_interval_all
  have h_count := count_bad_interval_all D k m₀ hpD_le hD_ge hp₀ hk
  -- Bound: each of the two terms ≤ 2*m₀/(32k)
  -- First term: 2*m₀/2^{D/36} ≤ 2*m₀/(32k)
  -- Second term: 2*p₀^D/2^{D/36} ≤ 2*m₀/2^{D/36} ≤ 2*m₀/(32k)
  have h_term1 : 2 * m₀ / 2 ^ (D / 36) ≤ 2 * m₀ / (32 * k) :=
    Nat.div_le_div_left h_decay (by omega)
  have h_term2 : 2 * p₀ ^ D / 2 ^ (D / 36) ≤ 2 * m₀ / (32 * k) := by
    calc 2 * p₀ ^ D / 2 ^ (D / 36)
        ≤ 2 * m₀ / 2 ^ (D / 36) := Nat.div_le_div_right (by omega)
      _ ≤ 2 * m₀ / (32 * k) := h_term1
  -- Sum ≤ 2 * (2*m₀/(32k))
  have h_sum : 2 * m₀ / 2 ^ (D / 36) + 2 * p₀ ^ D / 2 ^ (D / 36) ≤ 
      2 * (2 * m₀ / (32 * k)) := by omega
  -- 2 * (2*m₀/(32k)) ≤ (4*m₀)/(32k) = m₀/(8k)
  have h_double : 2 * (2 * m₀ / (32 * k)) ≤ 4 * m₀ / (32 * k) := by
    rw [Nat.le_div_iff_mul_le (by omega : 32 * k > 0)]
    calc 2 * (2 * m₀ / (32 * k)) * (32 * k)
        = 2 * ((32 * k) * (2 * m₀ / (32 * k))) := by ring
      _ ≤ 2 * (2 * m₀) := Nat.mul_le_mul_left 2 (Nat.mul_div_le _ _)
      _ = 4 * m₀ := by ring
  have h_simplify : 4 * m₀ / (32 * k) = m₀ / (8 * k) := by
    rw [show 32 * k = 4 * (8 * k) from by ring]
    exact Nat.mul_div_mul_left m₀ (8 * k) (by omega : 4 > 0)
  linarith [h_count]

end UnionBoundProof

EOF
lake env lean /tmp/test_main_final.lean 2>&1
```
The `per_prime_bound` compiles (with the sorry in `count_bad_interval_all` for p=2). Now let me build the final existence proof:
```bash
$ cd /home/jarred/code/erdos-728b && cat >> /tmp/test_main_final.lean << 'EOF'

section MainProof

-- The main theorem
lemma exists_m_for_fixed_k_proof (k : ℕ) (hk : k ≥ 1)
    (m₀ : ℕ) (hm₀ : union_bound_threshold k ≤ m₀) :
    ∃ m : ℕ, m₀ ≤ m ∧ m < 2 * m₀ ∧
      ∀ p : ℕ, p.Prime → p ≤ 2 * k →
        padicValNat p ((m + k).choose k) ≤
          padicValNat p ((2 * m).choose m) := by
  have hm₀_pos : m₀ > 0 := by
    have : union_bound_threshold k > 0 := by unfold union_bound_threshold; positivity
    omega
  -- Proof by contradiction: assume every m ∈ [m₀, 2m₀) is bad
  by_contra h_no_good
  push_neg at h_no_good
  -- h_no_good : ∀ m, m₀ ≤ m → m < 2*m₀ → ∃ p, p.Prime ∧ p ≤ 2k ∧ bad(p,m)
  
  -- The set of primes ≤ 2k
  let primes := (range (2 * k + 1)).filter Nat.Prime
  -- The bad set for each prime
  let bad (q : ℕ) := (Ico m₀ (2 * m₀)).filter
    (fun m => padicValNat q ((m + k).choose k) > padicValNat q ((2 * m).choose m))
  
  -- Every m ∈ Ico is in ⋃_p bad(p)
  have h_cover : Ico m₀ (2 * m₀) ⊆ primes.biUnion bad := by
    intro m hm; rw [mem_Ico] at hm; rw [mem_biUnion]
    obtain ⟨q, hq_prime, hq_le, hq_bad⟩ := h_no_good m hm.1 hm.2
    exact ⟨q, mem_filter.mpr ⟨mem_range.mpr (by omega), hq_prime⟩,
           mem_filter.mpr ⟨mem_Ico.mpr hm, hq_bad⟩⟩
  
  -- So |Ico| ≤ |⋃ bad(p)| ≤ Σ |bad(p)|
  have h_card_Ico : (Ico m₀ (2 * m₀)).card = m₀ := by
    simp [Nat.card_Ico]; omega
  have h_lower : m₀ ≤ ∑ q ∈ primes, (bad q).card := by
    calc m₀ = (Ico m₀ (2 * m₀)).card := h_card_Ico.symm
      _ ≤ (primes.biUnion bad).card := card_le_card h_cover
      _ ≤ ∑ q ∈ primes, (bad q).card := card_biUnion_le
  
  -- Bound each |bad(q)| ≤ m₀/(8k)
  have h_per_prime : ∀ q ∈ primes, (bad q).card ≤ m₀ / (8 * k) := by
    intro q hq; rw [mem_filter] at hq
    exact per_prime_bound k hk q hq.2 (by omega) m₀ hm₀
  
  -- Sum ≤ |primes| * m₀/(8k) ≤ 2k * m₀/(8k)
  have h_primes_le : primes.card ≤ 2 * k := by
    calc primes.card ≤ (range (2 * k + 1)).card := card_filter_le _ _
      _ = 2 * k + 1 := card_range _
      _ ≤ 2 * (2 * k) := by omega  -- wait, 2k+1 ≤ 2*(2k) = 4k? No, that's wrong for k=1
  sorry -- need to fix the primes bound and arithmetic

end MainProof

EOF
lake env lean /tmp/test_main_final.lean 2>&1
```
I need to fix the arithmetic. The number of primes ≤ 2k is at most 2k. `primes.card ≤ card(range(2k+1)) = 2k+1`. But I need `primes.card ≤ 2k`. Actually `primes` = filter Prime (range (2k+1)), and `range(2k+1)` has elements 0, 1, ..., 2k. The primes among these are at most 2k in number (since 0 and 1 are not prime, but some elements > 1 may be prime). Actually `primes.card ≤ 2k` since there are at most 2k-1 numbers in {2, ..., 2k} and primes are a subset of those. But the simplest bound is `primes.card ≤ 2k+1-2 = 2k-1` since 0 and 1 are not prime. Actually:

`primes = filter Prime (range (2k+1))`. `range(2k+1)` has 2k+1 elements. Neither 0 nor 1 is prime. So `primes.card ≤ 2k+1 - 2 = 2k-1 ≤ 2k`.

But I can use a simpler approach: `Σ f(q) ≤ |primes| * max_f ≤ (2k) * m₀/(8k) ≤ m₀/4`. The key is the `sum_le_card_nsmul` lemma:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_sum.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset

#check Finset.sum_le_card_nsmul
-- sum_le_card_nsmul (s : Finset ι) (f : ι → M) (n : M) (h : ∀ x ∈ s, f x ≤ n) :
--   ∑ x ∈ s, f x ≤ s.card • n

-- For ℕ: s.card • n = s.card * n (since nsmul for ℕ is multiplication)
example (s : Finset ℕ) (f : ℕ → ℕ) (n : ℕ) (h : ∀ x ∈ s, f x ≤ n) :
    ∑ x ∈ s, f x ≤ s.card * n := by
  have := Finset.sum_le_card_nsmul s f n h
  simp [nsmul_eq_mul] at this
  exact this

-- Also, number of primes in range(2k+1):
-- We need primes.card ≤ 2k
-- primes = filter Prime (range (2k+1))
-- range(2k+1) = {0, 1, ..., 2k}
-- 0 is not prime, 1 is not prime, so at most 2k-1 primes, which is ≤ 2k

example (k : ℕ) (hk : k ≥ 1) : ((range (2 * k + 1)).filter Nat.Prime).card ≤ 2 * k := by
  calc ((range (2 * k + 1)).filter Nat.Prime).card 
      ≤ (range (2 * k + 1)).card := card_filter_le _ _
    _ = 2 * k + 1 := card_range _
    _ ≤ 2 * (2 * k) := by omega

EOF
lake env lean /tmp/test_sum.lean 2>&1
```
OK so `2k+1 ≤ 2*(2k)` is `2k+1 ≤ 4k` which is NOT true for k=1 (3 ≤ 4 ✓, actually it is true for k ≥ 1). Wait: for k=1, 2k+1=3 and 2*(2k)=4. So 3 ≤ 4 ✓. Let me check:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_arith.lean << 'EOF'
import Mathlib.Tactic.Omega

example (k : ℕ) (hk : k ≥ 1) : 2 * k + 1 ≤ 2 * (2 * k) := by omega
-- 2k+1 ≤ 4k iff 1 ≤ 2k, which is true for k ≥ 1. ✓

-- But the goal in the error was "2*(2*k) ≤ 2*k", not "2k+1 ≤ 2*(2k)".
-- That's because I wrote the calc in the wrong direction!
-- I need primes.card ≤ 2k, not primes.card ≤ 2*(2k)

-- Let me just use a filter exclusion argument:
-- primes ⊆ range(2k+1) \ {0, 1}
-- |primes| ≤ |range(2k+1)| - |{0, 1}| = 2k+1 - 2 = 2k-1 ≤ 2k

-- Actually, simpler: the filter excludes 0 and 1 (not prime), so at most 2k-1 primes.
-- But proving this formally might be tricky. Let me just go with:
-- primes.card ≤ card(range(2k+1)) = 2k+1
-- And then use: (2k+1) * (m₀/(8k)) ≤ m₀/4 + m₀/(8k)
-- Hmm, that's messier.

-- Alternative: I need Σ bad ≤ m₀/4 < m₀. Let me use:
-- Σ bad ≤ primes.card * (m₀/(8k))
-- primes.card ≤ 2k+1 (trivial)
-- (2k+1) * (m₀/(8k)) ≤ (2k+1)*m₀/(8k)
-- For k ≥ 1: (2k+1)/(8k) ≤ 3/(8) < 1/2
-- So (2k+1)*m₀/(8k) ≤ m₀/2 < m₀

-- Actually the simplest: I just need the sum < m₀, not ≤ m₀/4.
-- primes.card ≤ 2k+1
-- Each term ≤ m₀/(8k)
-- Sum ≤ (2k+1) * (m₀/(8k))
-- In ℕ: (2k+1) * (m₀/(8k)) ≤ (2k+1) * m₀ / (8k)
-- = m₀ * (2k+1) / (8k)
-- For k ≥ 1: (2k+1)/(8k) ≤ 3/8 < 1
-- So m₀*(2k+1)/(8k) < m₀
-- In ℕ: (2k+1)*m₀/(8k) ≤ m₀ * (2k+1) / (8k)
-- And m₀*(2k+1) / (8k) < m₀ iff (2k+1)/(8k) < 1 iff 2k+1 < 8k iff 1 < 6k, true for k ≥ 1.

-- Formally: I need (2k+1)*m₀/(8k) < m₀, i.e., (2k+1)*m₀ < m₀*(8k)
-- i.e., (2k+1) < 8k, i.e., 1 < 6k, true for k ≥ 1.
-- In ℕ: n * (a/b) ≤ n*a/b. And n*a/b < a iff n*a < a*b (when b divides).
-- But we can just use: n*(a/b) < a when n < b (and a > 0).
-- n = 2k+1, b = 8k. For k ≥ 1: 2k+1 ≤ 3k ≤ 8k. So n ≤ b.
-- Then n * (a/b) ≤ n * a / b ≤ a (since n ≤ b).
-- Wait, n*a/b ≤ a iff n/b ≤ 1, which is true when n ≤ b.
-- So (2k+1)*(m₀/(8k)) ≤ (2k+1)*m₀/(8k) ≤ m₀ (since 2k+1 ≤ 8k for k ≥ 1).
-- But I need STRICT inequality: sum < m₀.
-- If m₀ > 0 and n < b: n*a/b < a? In ℕ, not necessarily (e.g., 1*1/2 = 0 < 1 ✓).
-- Actually n*a/b ≤ a-1 when n < b and a > 0? Not always.
-- Hmm, but we know sum ≤ (2k+1)*(m₀/(8k)).
-- And (2k+1)*(m₀/(8k)) ≤ m₀ * (2k+1) / (8k).
-- For k ≥ 1: (2k+1) ≤ 8k - 1, so m₀*(2k+1) < m₀*(8k).
-- So m₀*(2k+1)/(8k) ≤ m₀ - 1 < m₀. ✓ (when m₀*(8k) divides)
-- In general: m₀*(2k+1)/(8k) ≤ m₀*(8k-1)/(8k) = m₀ - m₀/(8k) < m₀. 
-- Wait, that's not how floor division works.
-- Let me just prove: a*(b/c) ≤ a*b/c and a*b/c < a when b < c and a > 0.

-- Actually: if 2k+1 < 8k (equiv k ≥ 1), then
-- (2k+1) * m₀ < 8k * m₀
-- So (2k+1)*m₀ / (8k) < m₀ (by Nat.div_lt_iff_lt_mul).
-- And then sum ≤ (2k+1)*(m₀/(8k)) ≤ (2k+1)*m₀/(8k) < m₀.

example (k m₀ : ℕ) (hk : k ≥ 1) (hm₀ : m₀ > 0) :
    (2 * k + 1) * m₀ / (8 * k) < m₀ := by
  rw [Nat.div_lt_iff_lt_mul (by omega : 8 * k > 0)]
  nlinarith

EOF
lake env lean /tmp/test_arith.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_arith2.lean << 'EOF'
import Erdos.Lemma3Counting

example (k m₀ : ℕ) (hk : k ≥ 1) (hm₀ : m₀ > 0) :
    (2 * k + 1) * m₀ / (8 * k) < m₀ := by
  rw [Nat.div_lt_iff_lt_mul (by omega : 8 * k > 0)]
  nlinarith

-- n * (a/b) ≤ n*a/b in ℕ
example (n a b : ℕ) (hb : b > 0) : n * (a / b) ≤ n * a / b := by
  rw [Nat.le_div_iff_mul_le hb]
  calc n * (a / b) * b = n * (b * (a / b)) := by ring
    _ ≤ n * a := Nat.mul_le_mul_left n (Nat.mul_div_le a b)

EOF
lake env lean /tmp/test_arith2.lean 2>&1
```
Now let me write the complete final proof:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_final_exists.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset Real Erdos728

-- All helper lemmas assumed to be available (will be added to file)
-- For this test, I'll use sorry for count_bad_interval_all and per_prime_bound

private def D_p' (k p : ℕ) : ℕ :=
  36 * (Nat.log 2 (16 * k) + 1) + 36 * (Nat.log p (k + 1)) + 36

-- Simplified per-prime bound (wraps all the helper lemmas)
private lemma per_prime_bound' (k : ℕ) (hk : k ≥ 1) (q : ℕ) (hq : q.Prime) (hq_le : q ≤ 2 * k)
    (m₀ : ℕ) (hm₀ : union_bound_threshold k ≤ m₀) :
    ((Ico m₀ (2 * m₀)).filter
      (fun m => padicValNat q ((m + k).choose k) > padicValNat q ((2 * m).choose m))).card
    ≤ m₀ / (8 * k) := by
  sorry -- proved in test_main_final.lean

-- The main theorem
lemma exists_m_for_fixed_k_test (k : ℕ) (hk : k ≥ 1)
    (m₀ : ℕ) (hm₀ : union_bound_threshold k ≤ m₀) :
    ∃ m : ℕ, m₀ ≤ m ∧ m < 2 * m₀ ∧
      ∀ p : ℕ, p.Prime → p ≤ 2 * k →
        padicValNat p ((m + k).choose k) ≤
          padicValNat p ((2 * m).choose m) := by
  have hm₀_pos : m₀ > 0 := by
    have : union_bound_threshold k > 0 := by unfold union_bound_threshold; positivity
    omega
  by_contra h_no_good
  push_neg at h_no_good
  let primes := (range (2 * k + 1)).filter Nat.Prime
  let bad (q : ℕ) := (Ico m₀ (2 * m₀)).filter
    (fun m => padicValNat q ((m + k).choose k) > padicValNat q ((2 * m).choose m))
  -- Every m ∈ Ico is bad for some prime
  have h_cover : Ico m₀ (2 * m₀) ⊆ primes.biUnion bad := by
    intro m hm; rw [mem_Ico] at hm; rw [mem_biUnion]
    obtain ⟨q, hq_prime, hq_le, hq_bad⟩ := h_no_good m hm.1 hm.2
    exact ⟨q, mem_filter.mpr ⟨mem_range.mpr (by omega), hq_prime⟩,
           mem_filter.mpr ⟨mem_Ico.mpr hm, hq_bad⟩⟩
  -- |Ico| ≤ Σ |bad(q)|
  have h_Ico_card : (Ico m₀ (2 * m₀)).card = m₀ := by
    simp [Nat.card_Ico]; omega
  have h_lower : m₀ ≤ ∑ q ∈ primes, (bad q).card :=
    calc m₀ = (Ico m₀ (2 * m₀)).card := h_Ico_card.symm
      _ ≤ (primes.biUnion bad).card := card_le_card h_cover
      _ ≤ ∑ q ∈ primes, (bad q).card := card_biUnion_le
  -- Each |bad(q)| ≤ m₀/(8k)
  have h_per_prime : ∀ q ∈ primes, (bad q).card ≤ m₀ / (8 * k) := by
    intro q hq; rw [mem_filter] at hq
    exact per_prime_bound' k hk q hq.2 (by omega) m₀ hm₀
  -- Sum ≤ |primes| * (m₀/(8k))
  have h_sum_bound : ∑ q ∈ primes, (bad q).card ≤ primes.card * (m₀ / (8 * k)) := by
    have := sum_le_card_nsmul primes (fun q => (bad q).card) (m₀ / (8 * k)) h_per_prime
    simpa using this
  -- |primes| ≤ 2k+1
  have h_primes_card : primes.card ≤ 2 * k + 1 := by
    calc primes.card ≤ (range (2 * k + 1)).card := card_filter_le _ _
      _ = 2 * k + 1 := card_range _
  -- (2k+1) * (m₀/(8k)) ≤ (2k+1)*m₀/(8k) < m₀
  have h_upper : primes.card * (m₀ / (8 * k)) < m₀ := by
    calc primes.card * (m₀ / (8 * k))
        ≤ (2 * k + 1) * (m₀ / (8 * k)) := Nat.mul_le_mul_right _ h_primes_card
      _ ≤ (2 * k + 1) * m₀ / (8 * k) := by
          rw [Nat.le_div_iff_mul_le (by omega : 8 * k > 0)]
          calc (2 * k + 1) * (m₀ / (8 * k)) * (8 * k) = 
              (2 * k + 1) * ((8 * k) * (m₀ / (8 * k))) := by ring
            _ ≤ (2 * k + 1) * m₀ := Nat.mul_le_mul_left _ (Nat.mul_div_le m₀ (8 * k))
      _ < m₀ := by
          rw [Nat.div_lt_iff_lt_mul (by omega : 8 * k > 0)]
          nlinarith
  -- Contradiction: m₀ ≤ sum ≤ primes.card * (m₀/(8k)) < m₀
  linarith [h_lower, h_sum_bound]

EOF
lake env lean /tmp/test_final_exists.lean 2>&1
```
The issue is with the `mem_filter.mp hq` destructuring — the variable `q` from `h_no_good` shadows. Let me fix:
```bash
$ cd /home/jarred/code/erdos-728b && sed -n '47,55p' /tmp/test_final_exists.lean
```
The error is on line 50, `by omega`. The `hq.2` gives `q.Prime` (from the filter). But the `by omega` is trying to prove `q ≤ 2 * k`, which comes from `hq.1` (from `mem_range`). Let me check:

The filter is `(range (2 * k + 1)).filter Nat.Prime`. So `mem_filter.mp hq` gives `⟨h_range, h_prime⟩` where `h_range : q ∈ range (2 * k + 1)` and `h_prime : q.Prime`. From `h_range`, we get `q < 2 * k + 1`, hence `q ≤ 2 * k`.

The error message mentions `2*a - e ≤ -1` which is `2k - q ≤ -1`, i.e., `q > 2k`. This should be false given `q ∈ range(2k+1)`. The issue is that `omega` doesn't have access to `hq.1`. Let me destructure:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_final_exists2.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset Real Erdos728

private lemma per_prime_bound' (k : ℕ) (hk : k ≥ 1) (q : ℕ) (hq : q.Prime) (hq_le : q ≤ 2 * k)
    (m₀ : ℕ) (hm₀ : union_bound_threshold k ≤ m₀) :
    ((Ico m₀ (2 * m₀)).filter
      (fun m => padicValNat q ((m + k).choose k) > padicValNat q ((2 * m).choose m))).card
    ≤ m₀ / (8 * k) := by
  sorry

lemma exists_m_for_fixed_k_test (k : ℕ) (hk : k ≥ 1)
    (m₀ : ℕ) (hm₀ : union_bound_threshold k ≤ m₀) :
    ∃ m : ℕ, m₀ ≤ m ∧ m < 2 * m₀ ∧
      ∀ p : ℕ, p.Prime → p ≤ 2 * k →
        padicValNat p ((m + k).choose k) ≤
          padicValNat p ((2 * m).choose m) := by
  have hm₀_pos : m₀ > 0 := by
    have : union_bound_threshold k > 0 := by unfold union_bound_threshold; positivity
    omega
  by_contra h_no_good
  push_neg at h_no_good
  let primes := (range (2 * k + 1)).filter Nat.Prime
  let bad (q : ℕ) := (Ico m₀ (2 * m₀)).filter
    (fun m => padicValNat q ((m + k).choose k) > padicValNat q ((2 * m).choose m))
  have h_cover : Ico m₀ (2 * m₀) ⊆ primes.biUnion bad := by
    intro m hm; rw [mem_Ico] at hm; rw [mem_biUnion]
    obtain ⟨q, hq_prime, hq_le, hq_bad⟩ := h_no_good m hm.1 hm.2
    exact ⟨q, mem_filter.mpr ⟨mem_range.mpr (by omega), hq_prime⟩,
           mem_filter.mpr ⟨mem_Ico.mpr hm, hq_bad⟩⟩
  have h_Ico_card : (Ico m₀ (2 * m₀)).card = m₀ := by
    simp [Nat.card_Ico]; omega
  have h_lower : m₀ ≤ ∑ q ∈ primes, (bad q).card :=
    calc m₀ = (Ico m₀ (2 * m₀)).card := h_Ico_card.symm
      _ ≤ (primes.biUnion bad).card := card_le_card h_cover
      _ ≤ ∑ q ∈ primes, (bad q).card := card_biUnion_le
  have h_per_prime : ∀ q ∈ primes, (bad q).card ≤ m₀ / (8 * k) := by
    intro q hq
    have hq_mem := mem_filter.mp hq
    have hq_lt := mem_range.mp hq_mem.1
    exact per_prime_bound' k hk q hq_mem.2 (by omega) m₀ hm₀
  have h_sum_bound : ∑ q ∈ primes, (bad q).card ≤ primes.card * (m₀ / (8 * k)) := by
    have := sum_le_card_nsmul primes (fun q => (bad q).card) (m₀ / (8 * k)) h_per_prime
    simpa using this
  have h_primes_card : primes.card ≤ 2 * k + 1 := by
    calc primes.card ≤ (range (2 * k + 1)).card := card_filter_le _ _
      _ = 2 * k + 1 := card_range _
  have h_upper : primes.card * (m₀ / (8 * k)) < m₀ := by
    calc primes.card * (m₀ / (8 * k))
        ≤ (2 * k + 1) * (m₀ / (8 * k)) := Nat.mul_le_mul_right _ h_primes_card
      _ ≤ (2 * k + 1) * m₀ / (8 * k) := by
          rw [Nat.le_div_iff_mul_le (by omega : 8 * k > 0)]
          calc (2 * k + 1) * (m₀ / (8 * k)) * (8 * k) = 
              (2 * k + 1) * ((8 * k) * (m₀ / (8 * k))) := by ring
            _ ≤ (2 * k + 1) * m₀ := Nat.mul_le_mul_left _ (Nat.mul_div_le m₀ (8 * k))
      _ < m₀ := by
          rw [Nat.div_lt_iff_lt_mul (by omega : 8 * k > 0)]
          nlinarith
  linarith [h_lower, h_sum_bound]

EOF
lake env lean /tmp/test_final_exists2.lean 2>&1
```
The main proof structure compiles with only the `per_prime_bound'` as a sorry. Now let me assemble the full proof without any sorrys. I need to put together:

1. `div_mul_div_le'` 
2. `count_few_high_digits_all` (100 lines, for p=2)
3. `count_bad_interval_all` (using count_few_high_digits_all)
4. `D_p`, `D_p_ge_threshold`, `pow_D_p_le_threshold`, `decay_estimate`
5. `per_prime_bound` (using the above)
6. `exists_m_for_fixed_k` (using per_prime_bound)

All of these have been verified to compile individually. Let me now write the complete proof directly into the Lean file:
```bash
$ cd /home/jarred/code/erdos-728b && grep -n "^lemma exists_m_for_fixed_k " Erdos/Lemma3Counting.lean
```

🛠️ **Executing tool: read**
Now I need to replace the sorry. I'll add the helper lemmas before the `exists_m_for_fixed_k` lemma and then replace its proof. Let me prepare the full replacement:
🛠️ **Executing tool: read**
I need to insert helper lemmas between the `union_bound_threshold` definition and `exists_m_for_fixed_k`. Let me do the full edit:
🛠️ **Executing tool: edit**
Now let me build and check if it compiles:
```bash
$ cd /home/jarred/code/erdos-728b && tm update erdos728b-r4m --status "Building with lake build to verify compilation"
```

```bash
$ cd /home/jarred/code/erdos-728b && lake build 2>&1
```
The build succeeded! Let me verify that the `exists_m_for_fixed_k` sorry is now closed:
```bash
$ cd /home/jarred/code/erdos-728b && grep -n "sorry" Erdos/Lemma3Counting.lean
```

```bash
$ cd /home/jarred/code/erdos-728b && sed -n '1380,1395p' Erdos/Lemma3Counting.lean
```
The only remaining sorry in the file is in `threshold_subpolynomial`, which is a different lemma. The `exists_m_for_fixed_k` sorry has been successfully closed.

Let me verify the specific lemma is sorry-free:
```bash
$ cd /home/jarred/code/erdos-728b && lake build 2>&1 | grep -E "sorry|warning.*exists_m_for_fixed_k"
```
The only sorry warning is for `threshold_subpolynomial` on line 1385, not for `exists_m_for_fixed_k`. Let me commit:
```bash
$ cd /home/jarred/code/erdos-728b && git add -A && git commit -m "Close sorry in exists_m_for_fixed_k (union bound for fixed k)

Proved the core union bound argument (Part E of proofs/lemma3-counting.md):

1. Extended count_few_high_digits to all primes (including p=2).
   The existing version required p ≥ 3 but the proof only uses p ≥ 2.
   For p=2, probHigh 2 = 1/2, and the Chernoff bound works identically.

2. Extended count_bad_interval to all primes (count_bad_interval_all).
   For p ≥ 3, delegates to existing lemma. For p=2, replicates the
   proof using count_few_high_digits_all.

3. Proved D_p parameter verification:
   - D_p_val_ge_threshold: D_p ≥ 16*log_p(k+1) + 16
   - pow_D_p_val_le_threshold: p^{D_p} ≤ union_bound_threshold(k)
   - decay_estimate_val: 2^{D_p/36} ≥ 32k

4. Proved per_prime_bound: each prime's bad count ≤ m₀/(8k).

5. Proved exists_m_for_fixed_k by contradiction:
   - If every m ∈ [m₀, 2m₀) is bad, interval ⊆ ⋃_p bad_p
   - Union bound: Σ|bad_p| ≤ (2k+1)·m₀/(8k) < m₀ = |interval|
   - Contradiction.

lake build succeeds. No new sorrys introduced."
```
