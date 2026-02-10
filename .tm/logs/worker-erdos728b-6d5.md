# timtam Task: Formalize Carry Dominance Lemma (carry(m, k) <= carry(m, m) for p > 2k) (erdos728b-6d5)

Role: formalize
Agent: formalize (google-antigravity/claude-opus-4-6-thinking)
Start Time: 2026-02-10T16:27:11.960Z

## Agent Interaction



> **Thinking:**
> Let me start by understanding the task. I need to formalize a "Carry Dominance Lemma" that states carry(m, k) <= carry(m, m) for p > 2k. Let me first read the relevant files to understand the context.


```bash
$ cd /home/jarred/code/erdos-728b && tm update erdos728b-6d5 --status "Reading NL proof and current Lean source"
```

🛠️ **Executing tool: read**

🛠️ **Executing tool: read**

🛠️ **Executing tool: read**
Now let me understand what I need to formalize. The carry dominance lemma (Lemma 2) says: for any prime `p > 2k` and any `m`, `v_p(choose(m+k, k)) ≤ v_p(choose(2m, m))`. Let me look at what's available in Mathlib for p-adic valuations of binomial coefficients and Kummer's theorem.
```bash
$ cd /home/jarred/code/erdos-728b && grep -r "Kummer\|kummer" .lake/packages/mathlib/Mathlib/ --include="*.lean" -l | head -20
```

```bash
$ cd /home/jarred/code/erdos-728b && grep -r "multiplicity.*choose\|choose.*multiplicity\|emultiplicity.*choose\|choose.*emultiplicity\|padicValNat.*choose\|choose.*padicValNat" .lake/packages/mathlib/Mathlib/ --include="*.lean" -l | head -20
```

```bash
$ cd /home/jarred/code/erdos-728b && grep -n "kummer\|Kummer\|choose\|Choose" .lake/packages/mathlib/Mathlib/Data/Nat/Multiplicity.lean | head -30
```

```bash
$ cd /home/jarred/code/erdos-728b && cat .lake/packages/mathlib/Mathlib/Data/Nat/Choose/Factorization.lean
```
Excellent! Now I have a clear picture. Mathlib has `factorization_choose'` (Kummer's theorem) expressed as the number of carries. Let me look at the key API more closely and understand the carry counting formulation.
```bash
$ cd /home/jarred/code/erdos-728b && tm update erdos728b-6d5 --status "Exploring Mathlib API for Kummer's theorem and carry counting"
```
Let me understand the exact formulation. The key is:
- `factorization_choose' hp hnb` says `(choose (n + k) k).factorization p = #{i ∈ Ico 1 b | p ^ i ≤ k % p ^ i + n % p ^ i}`
- The carry set: position `i` has a carry iff `p^i ≤ k % p^i + n % p^i`

So for our lemma:
- `v_p(choose(m+k, k))` = number of carries in `m + k` in base `p` = `#{i ∈ Ico 1 b | p^i ≤ k % p^i + m % p^i}`
- `v_p(choose(2m, m))` = number of carries in `m + m` in base `p` = `#{i ∈ Ico 1 b | p^i ≤ m % p^i + m % p^i}`

We need: for `p > 2k`, at every position `i`, if there's a carry in `m + k`, there's also a carry in `m + m`. That is:
- `∀ i, p^i ≤ k % p^i + m % p^i → p^i ≤ m % p^i + m % p^i`

This is saying: if `k mod p^i + m mod p^i ≥ p^i` then `2 * (m mod p^i) ≥ p^i`.

Let me think about this more carefully. The NL proof works position-by-position using the carry chain, but the Kummer formulation in Mathlib uses the "accumulated" modular condition. Let me check if they're equivalent.

The condition `p^i ≤ k % p^i + m % p^i` is actually a condition about whether the sum of the bottom `i` digits of `k` and `m` in base `p` produces a carry out of position `i-1`. This is exactly the number of carries in the standard sense.

So the lemma to prove is: for all `i ≥ 1`, if `p^i ≤ k % p^i + m % p^i`, then `p^i ≤ m % p^i + m % p^i`. Since `p > 2k`, we have `k < p^1/2` (since `k < p/2`), and also `k < p^i` for all `i ≥ 1`, so `k % p^i = k`.

Let me verify this key insight: since `p > 2k`, we have `k < p`, which means `k < p^i` for all `i ≥ 1`, so `k % p^i = k`.

Therefore the condition becomes: `p^i ≤ k + m % p^i → p^i ≤ 2 * (m % p^i)`.

From `p^i ≤ k + m % p^i`, we get `m % p^i ≥ p^i - k`. Since `k < p/2 ≤ p^i/2` (for `i ≥ 1`), we get `m % p^i > p^i/2`, hence `2 * (m % p^i) > p^i`, which gives `p^i ≤ 2 * (m % p^i)`.

Wait, let me be more precise. We need `2k < p`, so `k ≤ (p-1)/2`. For `i ≥ 1`:
- `k < p ≤ p^i`, so `k % p^i = k`
- If `p^i ≤ k + m % p^i`, then `m % p^i ≥ p^i - k`
- Since `k < p/2` (i.e., `2k + 1 ≤ p`, i.e., `2k < p`), and for `i = 1`, `p^1 - k > p - p/2 = p/2`, so `m % p ≥ p - k > p/2`, hence `2(m % p) > p`, so `2(m % p) ≥ p + 1 > p`, thus `p^1 ≤ 2(m % p^1)` ✓
- For `i ≥ 2`: `k < p ≤ p^{i-1} < p^i`, so `k < p^i/p ≤ p^i/2` (since `p ≥ 2`). Then `m % p^i ≥ p^i - k > p^i - p^i/2 = p^i/2`. So `2(m % p^i) > p^i`. ✓

Actually, even more simply: for all `i ≥ 1`, `k < p ≤ p^i`, so `k % p^i = k`. Also `2k < p ≤ p^i`. So if `k + m % p^i ≥ p^i`, then `m % p^i ≥ p^i - k > p^i - p^i/2 = p^i/2` (using `2k < p^i`). Hence `2 * (m % p^i) > p^i`, i.e., `2 * (m % p^i) ≥ p^i + 1 > p^i`, which means `p^i ≤ 2 * (m % p^i)`.

Wait, but I need `2 * (m % p^i) ≥ p^i`, not `> p^i`. From `m % p^i ≥ p^i - k` and `2k < p ≤ p^i`, we get `2(m % p^i) ≥ 2(p^i - k) = 2p^i - 2k > 2p^i - p^i = p^i`. So `2(m % p^i) ≥ p^i + 1 ≥ p^i`. ✓

Let me now write this as a Lean proof.
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_carry.lean << 'EOF'
import Mathlib

-- Check what we need
#check Nat.factorization_choose'
#check Nat.factorization_choose
#check Nat.centralBinom
#check Finset.card_le_card
#check Finset.filter_subset_filter
EOF
lake env lean /tmp/test_carry.lean 2>&1 | head -30
```
Good. Now let me check how `centralBinom` relates to `choose`:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_carry2.lean << 'EOF'
import Mathlib

#check Nat.centralBinom_eq_choose
#print Nat.centralBinom
#check Nat.choose_two_mul_self
#check Finset.card_filter_le_iff
EOF
lake env lean /tmp/test_carry2.lean 2>&1 | head -20
```
Good. So `centralBinom n = (2 * n).choose n`. Now let me plan the proof structure:

1. Use `factorization_choose'` to express both valuations as cardinalities of carry sets
2. Show one set is a subset of the other (the dominance property)
3. Use `Finset.card_le_card` to conclude

Let me write the proof:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_carry3.lean << 'EOF'
import Mathlib

open Nat Finset

-- The key pointwise lemma: if p > 2k and k + (m mod p^i) >= p^i, then 2*(m mod p^i) >= p^i
-- This needs: k % p^i = k (since k < p <= p^i for i >= 1)
-- and: m % p^i >= p^i - k > p^i/2

lemma carry_dominance_pointwise (p m k i : ℕ) (hp : Nat.Prime p) (hpk : 2 * k < p) (hi : 1 ≤ i)
    (hcarry : p ^ i ≤ k % p ^ i + m % p ^ i) :
    p ^ i ≤ m % p ^ i + m % p ^ i := by
  have hp_pos : 0 < p := hp.pos
  have hpi_pos : 0 < p ^ i := Nat.pos_of_ne_zero (by positivity)
  -- k < p, and since i >= 1, p <= p^i, so k < p^i, meaning k % p^i = k
  have hk_lt_p : k < p := by omega
  have hk_lt_pi : k < p ^ i := by
    calc k < p := hk_lt_p
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ i := Nat.pow_le_pow_right hp_pos hi
  rw [Nat.mod_eq_of_lt hk_lt_pi] at hcarry
  -- m % p^i >= p^i - k
  have hm_mod_ge : m % p ^ i ≥ p ^ i - k := by omega
  -- 2k < p <= p^i (since i >= 1)
  have h2k_lt_pi : 2 * k < p ^ i := by
    calc 2 * k < p := hpk
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ i := Nat.pow_le_pow_right hp_pos hi
  -- So m % p^i > p^i / 2, hence 2 * (m % p^i) > p^i
  omega

#check @carry_dominance_pointwise
EOF
lake env lean /tmp/test_carry3.lean 2>&1
```
The pointwise lemma compiles. Now let me build the full carry dominance lemma:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_carry4.lean << 'EOF'
import Mathlib

open Nat Finset

lemma carry_dominance_pointwise (p m k i : ℕ) (hp : Nat.Prime p) (hpk : 2 * k < p) (hi : 1 ≤ i)
    (hcarry : p ^ i ≤ k % p ^ i + m % p ^ i) :
    p ^ i ≤ m % p ^ i + m % p ^ i := by
  have hp_pos : 0 < p := hp.pos
  have hk_lt_p : k < p := by omega
  have hk_lt_pi : k < p ^ i := by
    calc k < p := hk_lt_p
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ i := Nat.pow_le_pow_right hp_pos hi
  rw [Nat.mod_eq_of_lt hk_lt_pi] at hcarry
  have h2k_lt_pi : 2 * k < p ^ i := by
    calc 2 * k < p := hpk
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ i := Nat.pow_le_pow_right hp_pos hi
  omega

/-- **Carry Dominance Lemma (Lemma 2).**

For any prime p > 2k and any non-negative integer m,
  v_p(choose(m+k, k)) ≤ v_p(choose(2m, m)).

This is because k is a single digit in base p (since k < p),
and every carry in the addition m + k implies a carry at the
same position in the addition m + m. -/
lemma carry_dominance (p m k : ℕ) (hp : Nat.Prime p) (hpk : 2 * k < p) :
    ((m + k).choose k).factorization p ≤ ((2 * m).choose m).factorization p := by
  -- Choose a bound b large enough for both factorization_choose' applications
  set b := max (Nat.log p (m + k)) (Nat.log p (2 * m)) + 1
  have hb1 : Nat.log p (m + k) < b := by omega
  have hb2 : Nat.log p (m + m) < b := by
    have : Nat.log p (m + m) ≤ Nat.log p (2 * m) := by
      congr 1; ring
    omega
  -- Rewrite both sides using Kummer's theorem
  rw [factorization_choose' hp hb1]
  -- For (2m).choose m, note 2*m = m + m
  have h2m : 2 * m = m + m := by ring
  rw [h2m, factorization_choose' hp hb2]
  -- Now show the carry set for (m+k) is a subset of the carry set for (m+m)
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  · exact Finset.Subset.refl _
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_Ico] at hi ⊢
    exact carry_dominance_pointwise p m k i hp hpk hi.1.1 hi.2

#check @carry_dominance
EOF
lake env lean /tmp/test_carry4.lean 2>&1
```
A few issues. Let me fix the approach - the filter_subset_filter isn't matching because of how the notation desugars. I need a different approach for the subset proof.
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_carry5.lean << 'EOF'
import Mathlib

open Nat Finset

lemma carry_dominance_pointwise (p m k i : ℕ) (hp : Nat.Prime p) (hpk : 2 * k < p) (hi : 1 ≤ i)
    (hcarry : p ^ i ≤ k % p ^ i + m % p ^ i) :
    p ^ i ≤ m % p ^ i + m % p ^ i := by
  have hp_pos : 0 < p := hp.pos
  have hk_lt_pi : k < p ^ i := by
    calc k < p := by omega
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ i := Nat.pow_le_pow_right hp_pos hi
  rw [Nat.mod_eq_of_lt hk_lt_pi] at hcarry
  have : 2 * k < p ^ i := by
    calc 2 * k < p := hpk
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ i := Nat.pow_le_pow_right hp_pos hi
  omega

lemma carry_dominance (p m k : ℕ) (hp : Nat.Prime p) (hpk : 2 * k < p) :
    ((m + k).choose k).factorization p ≤ ((2 * m).choose m).factorization p := by
  set b := max (Nat.log p (m + k)) (Nat.log p (2 * m)) + 1
  have hb1 : Nat.log p (m + k) < b := by omega
  have hb2 : Nat.log p (m + m) < b := by
    have : m + m = 2 * m := by ring
    rw [this]; omega
  rw [factorization_choose' hp hb1]
  have h2m : 2 * m = m + m := by ring
  rw [h2m, factorization_choose' hp hb2]
  apply Finset.card_le_card
  intro i
  simp only [Finset.mem_filter, Finset.mem_Ico]
  intro ⟨⟨hi1, hi2⟩, hcarry⟩
  exact ⟨⟨hi1, hi2⟩, carry_dominance_pointwise p m k i hp hpk hi1 hcarry⟩

#check @carry_dominance
EOF
lake env lean /tmp/test_carry5.lean 2>&1
```
Both lemmas compile. Now let me also provide a version in terms of `padicValNat` which might be more directly useful:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_carry6.lean << 'EOF'
import Mathlib

open Nat Finset

-- Check if there's a connection between factorization and padicValNat
#check Nat.factorization_eq_zero_or_pos
#check padicValNat
example (n p : ℕ) (hp : Nat.Prime p) (hn : n ≠ 0) : n.factorization p = padicValNat p n := by
  exact?
EOF
lake env lean /tmp/test_carry6.lean 2>&1 | head -20
```
Good, `factorization_def n hp` converts. Let me also provide a `padicValNat` version and check if the main theorem uses `factorization` or `padicValNat`:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_carry7.lean << 'EOF'
import Mathlib

open Nat Finset

lemma carry_dominance_pointwise (p m k i : ℕ) (hp : Nat.Prime p) (hpk : 2 * k < p) (hi : 1 ≤ i)
    (hcarry : p ^ i ≤ k % p ^ i + m % p ^ i) :
    p ^ i ≤ m % p ^ i + m % p ^ i := by
  have hp_pos : 0 < p := hp.pos
  have hk_lt_pi : k < p ^ i := by
    calc k < p := by omega
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ i := Nat.pow_le_pow_right hp_pos hi
  rw [Nat.mod_eq_of_lt hk_lt_pi] at hcarry
  have : 2 * k < p ^ i := by
    calc 2 * k < p := hpk
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ i := Nat.pow_le_pow_right hp_pos hi
  omega

/-- **Carry Dominance Lemma (Lemma 2).**

For any prime p > 2k and any non-negative integer m,
  v_p(choose(m+k, k)) ≤ v_p(choose(2m, m)).

By Kummer's theorem, v_p(C(a+b,a)) equals the number of positions i ≥ 1 where
p^i ≤ (a % p^i) + (b % p^i). Since p > 2k, k is a single base-p digit, and
every carry in m + k is dominated by a carry at the same position in m + m. -/
lemma carry_dominance (p m k : ℕ) (hp : Nat.Prime p) (hpk : 2 * k < p) :
    ((m + k).choose k).factorization p ≤ ((2 * m).choose m).factorization p := by
  set b := max (Nat.log p (m + k)) (Nat.log p (2 * m)) + 1
  have hb1 : Nat.log p (m + k) < b := by omega
  have hb2 : Nat.log p (m + m) < b := by
    have : m + m = 2 * m := by ring
    rw [this]; omega
  rw [factorization_choose' hp hb1]
  have h2m : 2 * m = m + m := by ring
  rw [h2m, factorization_choose' hp hb2]
  apply Finset.card_le_card
  intro i
  simp only [Finset.mem_filter, Finset.mem_Ico]
  intro ⟨⟨hi1, hi2⟩, hcarry⟩
  exact ⟨⟨hi1, hi2⟩, carry_dominance_pointwise p m k i hp hpk hi1 hcarry⟩

/-- Carry dominance in terms of padicValNat. -/
lemma carry_dominance_padicValNat (p m k : ℕ) (hp : Nat.Prime p) (hpk : 2 * k < p) :
    padicValNat p ((m + k).choose k) ≤ padicValNat p ((2 * m).choose m) := by
  rw [← factorization_def _ hp, ← factorization_def _ hp]
  exact carry_dominance p m k hp hpk

/-- Carry dominance implies divisibility: for p > 2k, p-part of C(m+k,k) divides p-part of C(2m,m). -/
lemma carry_dominance_dvd (p m k : ℕ) (hp : Nat.Prime p) (hpk : 2 * k < p) :
    p ^ ((m + k).choose k).factorization p ∣ p ^ ((2 * m).choose m).factorization p :=
  Nat.pow_dvd_pow p (carry_dominance p m k hp hpk)

#check @carry_dominance
#check @carry_dominance_padicValNat
#check @carry_dominance_dvd
EOF
lake env lean /tmp/test_carry7.lean 2>&1
```
All three versions compile cleanly. Now let me add these to the `Erdos/Lemmas.lean` file and verify the full project builds:
```bash
$ cd /home/jarred/code/erdos-728b && tm update erdos728b-6d5 --status "Writing lemmas to Erdos/Lemmas.lean and building"
```

🛠️ **Executing tool: read**

🛠️ **Executing tool: edit**

```bash
$ cd /home/jarred/code/erdos-728b && lake build 2>&1
```
Build succeeds. The only `sorry` warning is from the main theorem in `Basic.lean` (which is expected and immutable). Let me verify the final state of the file:
🛠️ **Executing tool: read**
Everything looks clean. Let me commit:
```bash
$ cd /home/jarred/code/erdos-728b && git add -A && git commit -m "Formalize carry dominance lemma (Lemma 2): v_p(C(m+k,k)) ≤ v_p(C(2m,m)) for p > 2k

For any prime p > 2k and any m, the p-adic valuation of C(m+k, k)
is at most the p-adic valuation of C(2m, m).

Proof uses Kummer's theorem (Nat.factorization_choose') to express
both valuations as cardinalities of carry sets, then shows the carry
set for m+k is a subset of the carry set for m+m via a pointwise
argument: since k < p/2, any position where m+k carries must have
m % p^i > p^i/2, which implies m+m also carries there.

Three variants provided:
- carry_dominance: in terms of factorization
- carry_dominance_padicValNat: in terms of padicValNat
- carry_dominance_dvd: the p-power divisibility consequence"
```

```bash
$ cd /home/jarred/code/erdos-728b && tm update erdos728b-6d5 --status "Complete. All lemmas compile, lake build succeeds."
```

```bash
$ cd /home/jarred/code/erdos-728b && tm close erdos728b-6d5
```
```json
{
  "status": "completed",
  "summary": "Closed all sorrys in carry dominance lemma. lake build succeeds.",
  "details": "Formalized Lemma 2 from proofs/erdos728_v2.md in Erdos/Lemmas.lean. Three sorry-free lemmas added:\n\n1. **`carry_dominance`** (factorization form): For prime p with 2k < p and any m, `((m + k).choose k).factorization p ≤ ((2 * m).choose m).factorization p`.\n\n2. **`carry_dominance_padicValNat`**: Same result in terms of `padicValNat`.\n\n3. **`carry_dominance_dvd`**: The p-power divisibility consequence.\n\n**Proof approach**: Uses Kummer's theorem (`Nat.factorization_choose'`) to express both p-adic valuations as cardinalities of carry sets `{i ∈ Ico 1 b | p^i ≤ a % p^i + b % p^i}`. A pointwise helper lemma (`carry_dominance_pointwise`) shows the carry set for m+k is a subset of the carry set for m+m: since 2k < p ≤ p^i, k % p^i = k, so if k + (m % p^i) ≥ p^i then m % p^i > p^i/2, hence 2·(m % p^i) > p^i. The cardinality inequality then follows from `Finset.card_le_card`.\n\nNo new sorry holes introduced. `lake build` succeeds with only the expected sorry in the main theorem statement."
}
```

## Final Result

```json
{
  "status": "completed",
  "summary": "Closed all sorrys in carry dominance lemma. lake build succeeds.",
  "details": "Formalized Lemma 2 from proofs/erdos728_v2.md in Erdos/Lemmas.lean. Three sorry-free lemmas added:\n\n1. **`carry_dominance`** (factorization form): For prime p with 2k < p and any m, `((m + k).choose k).factorization p ≤ ((2 * m).choose m).factorization p`.\n\n2. **`carry_dominance_padicValNat`**: Same result in terms of `padicValNat`.\n\n3. **`carry_dominance_dvd`**: The p-power divisibility consequence.\n\n**Proof approach**: Uses Kummer's theorem (`Nat.factorization_choose'`) to express both p-adic valuations as cardinalities of carry sets `{i ∈ Ico 1 b | p^i ≤ a % p^i + b % p^i}`. A pointwise helper lemma (`carry_dominance_pointwise`) shows the carry set for m+k is a subset of the carry set for m+m: since 2k < p ≤ p^i, k % p^i = k, so if k + (m % p^i) ≥ p^i then m % p^i > p^i/2, hence 2·(m % p^i) > p^i. The cardinality inequality then follows from `Finset.card_le_card`.\n\nNo new sorry holes introduced. `lake build` succeeds with only the expected sorry in the main theorem statement."
}
```

End Time: 2026-02-10T16:31:38.227Z
