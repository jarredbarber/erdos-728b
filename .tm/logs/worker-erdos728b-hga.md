# timtam Task: Close sorry: bad_residue_sets (L3C:143) (erdos728b-hga)

Role: formalize
Agent: formalize (google-antigravity/claude-opus-4-6-thinking)
Start Time: 2026-02-11T05:17:45.486Z

## Agent Interaction

Let

> **Thinking:**
>  me start by understanding the task. I need to close a `sorry` at `Lemma3Counting.lean:143` for a lemma called `bad_residue_sets`. Let me first read the relevant files to understand the context.


```bash
$ cd /home/jarred/code/erdos-728b && tm update erdos728b-hga --status "Reading source files and understanding the sorry target"
```

🛠️ **Executing tool: read**
Now let me find the `bad_residue_sets` lemma and understand what needs to be proved. It's around line 143 of the file. Let me also look at the NL proof and relevant supporting files.
```bash
$ cd /home/jarred/code/erdos-728b && ls proofs/
```

🛠️ **Executing tool: read**
Now let me understand the specific `sorry` I need to close. Let me look at the `bad_residue_sets` lemma more carefully:
🛠️ **Executing tool: read**

```bash
$ cd /home/jarred/code/erdos-728b && grep -n "bad_residue_sets" Erdos/Lemma3Counting.lean
```

🛠️ **Executing tool: read**
Now I understand the goal. The `bad_residue_sets` lemma says:
1. If `v_p(C(m+k,k)) > D/6`, then `m % p^D` is in the set of residues with large cascade length
2. If `v_p(C(2m,m)) < D/6`, then `m % p^D` is in the set of residues with few high digits

Both parts say that "badness" depends only on `m mod p^D`. Let me now look at the relevant definitions and supporting lemmas.
```bash
$ cd /home/jarred/code/erdos-728b && cat Erdos/Digits.lean
```

```bash
$ cd /home/jarred/code/erdos-728b && cat Erdos/Lemma3Common.lean
```

```bash
$ cd /home/jarred/code/erdos-728b && cat Erdos/Lemma3Residue.lean
```
Now let me understand the exact goal. The `bad_residue_sets` lemma has two conjuncts:

1. For all `m`, if `padicValNat p ((m + k).choose k) > D/6`, then `m % p^D` is in the filter of residues with cascade length ≥ `D/6 - log p k`.
2. For all `m`, if `padicValNat p ((2 * m).choose m) < D/6`, then `m % p^D` is in the filter of residues with `count_high_digits p r D < D/6`.

The key insight from Part D of the NL proof:
- Part 1: `v_p(C(m+k,k))` depends only on digits 0..D-1, hence on `m mod p^D`. So does `cascade_length`.
- Part 2: `count_high_digits p m D` manifestly depends only on digits 0..D-1, hence on `m mod p^D`.

Let me look at the definitions more carefully:
```bash
$ cd /home/jarred/code/erdos-728b && grep -n "cascade_length\|count_high_digits\|digit " Erdos/Lemma3Counting.lean | head -20
```
Now I need to understand exactly what the lemma states. Let me look at `cascade_length` and `count_high_digits`:

- `cascade_length` uses `digit p m (s + 1 + i)` where `s = log p k` — these are digits at positions `s+1, s+2, ...` up to `D`. So it depends on digits 0..D-1 of `m`.
- `count_high_digits p m D` counts high digits at positions 0..D-1.

Both depend only on `m mod p^D` because `digit p m i = (m / p^i) % p`, and for `i < D`, `digit p m i = digit p (m % p^D) i`.

The key fact I need is: **`digit p m i = digit p (m % p^D) i` for `i < D`**.

Let me also check what lemma connects `digit` and `mod`:
```bash
$ cd /home/jarred/code/erdos-728b && grep -rn "digit.*mod\|mod.*digit" Erdos/ --include="*.lean" | head -20
```
I see there's `mod_pow_eq_of_digits_eq` which says: if digits agree at positions 0..D-1, then `a % p^D = b % p^D`. I also need the converse direction: if `a % p^D = b % p^D`, then digits 0..D-1 agree.
```bash
$ cd /home/jarred/code/erdos-728b && tm update erdos728b-hga --status "Understanding the proof structure - need digit_mod_eq lemma and the two conjuncts"
```
Let me first understand the two conjuncts more carefully by examining the actual goal types. Let me write a scratch file:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_bad_residue.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat Finset Erdos728

-- Check if digit is invariant under mod p^D for i < D
example (p m D i : ℕ) (hp : p > 0) (hi : i < D) : digit p (m % p ^ D) i = digit p m i := by
  unfold digit
  rw [Nat.mod_div_eq_of_pow_le (Nat.pow_le_pow_right hp hi)]
  sorry
EOF
lake env lean /tmp/test_bad_residue.lean 2>&1 | head -30
```
Good, now I can see the goal: `m % p ^ D / p ^ i % p = m / p ^ i % p`. This is what I need to prove for `i < D`. Let me search for relevant Mathlib lemmas:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_bad_residue.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat Finset Erdos728

-- The key identity: (m % p^D) / p^i = (m / p^i) % p^(D-i) for i ≤ D
example (p m D i : ℕ) (hp : p > 0) (hi : i ≤ D) : m % p ^ D / p ^ i = m / p ^ i % p ^ (D - i) := by
  exact?
EOF
lake env lean /tmp/test_bad_residue.lean 2>&1 | tail -15
```

```bash
$ cd /home/jarred/code/erdos-728b && grep -r "mod_div\|div_mod" .lake/packages/mathlib/Mathlib/Data/Nat/ --include="*.lean" -l | head -10
```

```bash
$ cd /home/jarred/code/erdos-728b && grep -rn "mod_pow.*div\|div.*mod_pow\|mod_div_eq" .lake/packages/mathlib/Mathlib/ --include="*.lean" | head -20
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_bad_residue.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat Finset Erdos728

-- Try: digit p (m % p^D) i = digit p m i for i < D
-- digit p m i = (m / p^i) % p
-- We need: (m % p^D) / p^i % p = m / p^i % p
-- Key: m % p^D = m % (p^i * p^(D-i)), and we can use Nat.mod_def or similar

-- Try using Nat.mod_mod_of_dvd
example (p m D i : ℕ) (hp : p > 0) (hi : i < D) : m % p ^ D / p ^ i % p = m / p ^ i % p := by
  have hpi_pos : p ^ i > 0 := Nat.pos_of_ne_zero (by positivity)
  -- rewrite p^D as p^i * p^(D-i)
  have hD_split : p ^ D = p ^ i * p ^ (D - i) := by
    rw [← pow_add]; congr 1; omega
  rw [hD_split]
  rw [Nat.mod_mul_right_div_self]
  -- Now need: m / p ^ i % (p ^ (D - i)) % p = m / p ^ i % p
  apply Nat.mod_mod_of_dvd
  exact dvd_pow_self p (by omega : D - i ≠ 0) |>.symm |> fun h => sorry
EOF
lake env lean /tmp/test_bad_residue.lean 2>&1 | tail -15
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_bad_residue.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat Finset Erdos728

-- digit p (m % p^D) i = digit p m i for i < D
lemma digit_mod_pow_eq (p m D i : ℕ) (hp : p > 0) (hi : i < D) : 
    digit p (m % p ^ D) i = digit p m i := by
  unfold digit
  have hpi_pos : p ^ i > 0 := Nat.pos_of_ne_zero (by positivity)
  have hD_split : p ^ D = p ^ i * p ^ (D - i) := by
    rw [← pow_add]; congr 1; omega
  rw [hD_split, Nat.mod_mul_right_div_self]
  apply Nat.mod_mod_of_dvd
  exact dvd_pow_self p (by omega : D - i ≠ 0)
EOF
lake env lean /tmp/test_bad_residue.lean 2>&1 | tail -15
```
The `digit_mod_pow_eq` lemma compiles. Now let me think about the two conjuncts.

**Conjunct 1**: `∀ m, padicValNat p ((m + k).choose k) > D/6 → m % p^D ∈ (range (p^D)).filter (fun r => cascade_length (p:=p) k D r ≥ D/6 - log p k)`

This requires:
- `m % p^D < p^D` (for `mem_range`)
- `cascade_length k D (m % p^D) ≥ D/6 - log p k`

The second part requires showing `cascade_length k D (m % p^D) = cascade_length k D m`, which follows from the fact that `cascade_length` only looks at digits 0..D-1.

Wait, actually, the lemma doesn't say we need to show the cascade length is preserved under mod. It says: if the valuation is > D/6, then the residue is in the filter. But the valuation could be affected by higher digits. Looking back at the NL proof Part D:

The key insight is:
- For conjunct 1: We don't need `v_p(C(m+k,k))` to be preserved. We need: if `v_p(C(m+k,k)) > D/6`, then `cascade_length k D (m % p^D) ≥ D/6 - log p k`.

This is more subtle. The NL proof says: `v_p > D/6 = s+1+T₀` implies `L ≥ T₀+1` (where T₀ = D/6 - s - 1), but `L` as measured from the full number and from `m % p^D` might differ...

Actually wait, let me re-read `cascade_length`:

```
def cascade_length (m : ℕ) : ℕ :=
  let s := log p k
  let limit := D - (s + 1)
  (List.range limit).takeWhile (fun i => digit p m (s + 1 + i) = p - 1) |>.length
```

It uses `digit p m (s + 1 + i)` for `i < D - (s + 1)`, i.e., for positions `s+1` through `D-1`. These are all positions less than `D`. So `cascade_length k D (m % p^D) = cascade_length k D m` because `digit p (m % p^D) j = digit p m j` for all `j < D`.

Similarly, `count_high_digits p (m % p^D) D = count_high_digits p m D` because it only looks at digits at positions 0..D-1.

But wait — the statement doesn't claim `cascade_length k D (m % p^D) = cascade_length k D m`. It also doesn't claim `padicValNat p ((m + k).choose k) > D/6 → cascade_length k D m ≥ D/6 - log p k`. Instead, it uses the residue. Since `cascade_length k D (m % p^D) = cascade_length k D m` (which I'll prove), I need:

`padicValNat p ((m + k).choose k) > D/6 → cascade_length k D m ≥ D/6 - log p k`

This follows from the `valuation_le_cascade` lemma: `padicValNat p ((m + k).choose k) ≤ (log p k + 1) + cascade_length k D m`. But that lemma is also `sorry`'d! Let me check:
```bash
$ cd /home/jarred/code/erdos-728b && grep -n "sorry" Erdos/Lemma3Counting.lean
```
`valuation_le_cascade` is sorry'd (line 123). So for conjunct 1, I can't use it directly. However, the `bad_residue_sets` lemma itself might need to just express the "mod equivalence" — that the badness condition, when it holds for `m`, gives that `m % p^D` has the same cascade/digit properties. Let me re-read the lemma:

Looking at the lemma again:
```lean
lemma bad_residue_sets (hp : p.Prime) (hD : D ≥ 16 * (log p (k + 1)) + 16) :
    (∀ m, padicValNat p ((m + k).choose k) > D/6 → 
      m % p^D ∈ (range (p^D)).filter (fun r => cascade_length (p:=p) k D r ≥ D/6 - log p k)) ∧
    (∀ m, padicValNat p ((2 * m).choose m) < D/6 → 
      m % p^D ∈ (range (p^D)).filter (fun r => count_high_digits p r D < D/6)) := sorry
```

For **conjunct 1**, the claim is:
- If `v_p(C(m+k,k)) > D/6`, then `m % p^D` satisfies `cascade_length k D (m % p^D) ≥ D/6 - log p k`.

This requires the chain:
1. `v_p(C(m+k,k)) > D/6` implies `cascade_length k D m ≥ D/6 - log p k` (which uses `valuation_le_cascade`)
2. `cascade_length k D (m % p^D) = cascade_length k D m` (digit invariance)

Since `valuation_le_cascade` is sorry'd, I can either use it as-is (with sorry) or try a different approach. Given that this is a formalization task, I should use available lemmas even if they have sorrys — the compilation invariant just requires `lake build` to succeed, and sorry warnings are fine.

Actually wait — I CAN use sorry'd lemmas. They have type signatures, so I can call them. `sorry` just means the proof body is incomplete, but the lemma is still a valid declaration.

Let me verify:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_bad_residue2.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat Finset Erdos728

-- Check valuation_le_cascade signature
#check @valuation_le_cascade
EOF
lake env lean /tmp/test_bad_residue2.lean 2>&1
```
Good, I can use `valuation_le_cascade` even though it's sorry'd — it has the right type.

But wait — `valuation_le_cascade` requires `m < p^D`. My `m` might be any natural number. For the general case, I need to show that `cascade_length k D m = cascade_length k D (m % p^D)`, then use `valuation_le_cascade` with `m % p^D` (which is < p^D).

Actually no — `valuation_le_cascade` gives bounds on `padicValNat p ((m + k).choose k)` only for `m < p^D`. But the `bad_residue_sets` statement is about arbitrary `m`. So the approach needs to be different.

Actually, looking more carefully at the NL proof: the key insight for conjunct 1 is NOT about the valuation directly. It's that both `v_p(C(m+k,k))` and `cascade_length` depend only on digits 0..D-1. So if `v_p(C(m+k,k)) > D/6` for some `m`, then this involves only digits 0..D-1, and thus `m % p^D` has the same property.

But wait — `v_p(C(m+k,k))` involves ALL digits of `m`, not just 0..D-1. However, the NL proof argues that carries beyond position D don't affect the cascade analysis because the cascade must have died by then.

Hmm, this is getting complex. Let me re-read the NL proof Part D more carefully...

The NL proof says:
> **Bad₁ depends only on m mod p^D:** [...] carries at positions ≥ D are all part of the cascade. If L(m) ≥ T₀+1, then v_p > D/6 regardless of higher digits. Conversely, if L(m) ≤ T₀ [...] no carries propagate to positions ≥ D. Therefore v_p > D/6 iff the first D digits of m give L ≥ T₀+1.

So the argument is: `v_p(C(m+k,k)) > D/6` is equivalent to `cascade_length k D m ≥ T₀+1` where `T₀ = D/6 - s - 1`. And `cascade_length k D m = cascade_length k D (m % p^D)` since it only depends on first D digits.

But this equivalence between `v_p > D/6` and `L ≥ T₀+1` requires `valuation_le_cascade` (and its converse, or at least the implication `v_p > D/6 → L ≥ D/6 - s`).

Let me take a step back. The statement says:
```
cascade_length (p:=p) k D r ≥ D/6 - log p k
```

And `D/6 - log p k` in ℕ subtraction. If `D/6 ≤ log p k`, this is 0 and is trivially true. Given `hD : D ≥ 16 * (log p (k + 1)) + 16`, we have `D/6 ≥ 2 * (log p (k+1) + 1) + 2 ≥ 2 * (log p k + 1) + 2` which is larger than `log p k`, so `D/6 - log p k > 0`.

The approach should be:
1. Show `cascade_length k D (m % p^D) = cascade_length k D m` (digit invariance).
2. Show `v_p(C(m+k,k)) > D/6 → cascade_length k D m ≥ D/6 - log p k`.

For step 2, using `valuation_le_cascade`: `v_p ≤ (s+1) + L`. So `v_p > D/6 → (s+1) + L > D/6 → L > D/6 - s - 1 → L ≥ D/6 - s`.

But `valuation_le_cascade` requires `m < p^D`. For arbitrary `m`, we need a version that works for any `m`. Let me think about this...

Actually, `valuation_le_cascade` bounds from above: `v_p ≤ (s+1) + L`. If `v_p > D/6`, and the bound only holds for `m < p^D`, I can't directly use it for arbitrary `m`.

Hmm, but actually the lemma statement `bad_residue_sets` says: for ALL `m`, if `v_p > D/6`, then `m % p^D` has large cascade. If `valuation_le_cascade` only works for `m < p^D`, I need to first show that `v_p(C(m+k,k))` and `cascade_length` are the same for `m` and `m % p^D`.

Wait — actually `v_p(C(m+k,k))` is NOT the same for `m` and `m % p^D` in general. The binomial coefficient depends on the actual value of `m`, not just `m mod p^D`. But `cascade_length` only depends on `m mod p^D`.

So the logic must be different. Let me re-think...

Actually, re-reading the NL proof more carefully, the argument is:
- Kummer's theorem says `v_p(C(m+k,k))` = number of carries in `m + k` (in base p).
- For positions `i > s = log p k`, the carries form a cascade that depends only on whether `m_i = p-1` and whether there's a carry from below.
- The carry into position `s+1` can be at most 1 (from the first `s+1` positions).
- The cascade length L counts how many consecutive `p-1` digits start at position `s+1`.
- Even if the cascade extends beyond `D`, it still only contributes L carries (limited to D positions).

So for ARBITRARY `m`:
- `v_p(C(m+k,k)) = (carries at positions 0..s) + (carries at positions s+1..D-1) + (carries at positions ≥ D)`
- Carries at positions s+1..D-1 form a cascade of length ≤ L (the cascade length within D digits)
- Carries at positions ≥ D may or may not continue, but they depend on digits beyond D

The subtlety: `v_p(C(m+k,k))` could be large because of carries BEYOND position D (which depend on digits beyond D). In that case, the cascade goes beyond D. But `cascade_length k D m` only measures the cascade within the first D positions.

However, the NL proof's argument is:
- If the cascade within positions 0..D-1 terminates (L < D - s - 1), then carries at position s + L + 1 < D are 0, so no carry reaches position D, so no carries at positions ≥ D.
- So `v_p = (carries at 0..s) + L ≤ (s+1) + L`.
- If `v_p > D/6 = (s+1) + T₀`, then `L > T₀`, so `L ≥ T₀ + 1 = D/6 - s`.

But what if the cascade doesn't terminate within D positions? Then `L = D - (s+1)` (the max cascade measured within D digits), and `D/6 - s ≤ D - s - 1` (for large D), so `L ≥ D/6 - s` is satisfied anyway.

Actually wait, let me look at `cascade_length` again:
```
def cascade_length (m : ℕ) : ℕ :=
  let s := log p k
  let limit := D - (s + 1)
  (List.range limit).takeWhile (fun i => digit p m (s + 1 + i) = p - 1) |>.length
```

So `cascade_length` is the length of the initial run of `p-1` digits starting at position `s+1`, bounded by `limit = D - (s+1)`. This is ≤ `D - (s+1)`.

If `v_p(C(m+k,k)) > D/6` and `D/6 > s+1` (which follows from `hD`), then we need the cascade length (measuring within D) to be ≥ `D/6 - s`.

OK, I think the cleanest approach is:
1. Show `cascade_length k D (m % p^D) = cascade_length k D m` (since it depends on digits 0..D-1).
2. Use `valuation_le_cascade` applied to `m % p^D` to get a bound... but wait, `valuation_le_cascade` bounds `v_p(C(m%p^D + k, k))` not `v_p(C(m+k, k))`.

Hmm, this is not straightforward. Let me think again.

Actually, the conjunct 1 might need to go through a different route. The valuation for arbitrary `m` needs to be related to the cascade of `m % p^D`. This requires showing that the carries in `m + k` at positions 0..D-1 depend only on `m mod p^D`. Then:

`v_p(C(m+k,k)) = (carries at 0..D-1) + (carries at D..∞)`

The first part depends only on `m mod p^D`. The second part ≥ 0. So:

If `cascade_length k D m ≥ D/6 - log p k` is true for `m`, it's true for `m % p^D` (since cascade_length is invariant).

But we need the converse logic: given `v_p > D/6`, show cascade is large. The issue is that `v_p` for the full `m` might be larger than for `m % p^D` (due to carries beyond D). So `v_p(C(m+k,k)) > D/6` doesn't directly imply anything about `m % p^D`'s valuation.

BUT — the cascade length DOES imply something. If `cascade_length < D/6 - s` (measured in m's first D digits), then carries at positions 0..D-1 total ≤ (s+1) + cascade_length < (s+1) + (D/6 - s) = D/6 + 1. Moreover, the cascade terminates within positions 0..D-1, so no carry propagates to position D, so carries beyond D are 0. Thus `v_p ≤ D/6`. Contrapositive: if `v_p > D/6`, then `cascade_length ≥ D/6 - s`.

This is exactly the NL proof's argument. But formalizing this requires proving that if the cascade terminates within D, no carries propagate beyond D. This is NOT directly available from `valuation_le_cascade` since that only applies to `m < p^D`.

OK, I think the cleanest approach for the formalization is to use the contrapositive: show that if `cascade_length k D m < D/6 - log p k`, then `v_p(C(m+k,k)) ≤ D/6`. This requires:

1. `valuation_le_cascade` for `m < p^D` gives `v_p ≤ (s+1) + L` for small m.
2. For arbitrary m, need a similar bound. But the general m case would need a new lemma.

Actually, wait. Maybe I should just try a simpler approach. For conjunct 1, maybe I should prove it by introducing sorry'd helper lemmas that are clearly needed. But the instructions say I should only leave annotated sorrys if I truly can't close them.

Let me try yet another approach. Perhaps I should observe that for the first conjunct, the `cascade_length` is defined using `digit p m i` which depends only on `m mod p^D` for positions `i < D`. So first, I can show `cascade_length k D (m % p^D) = cascade_length k D m`.

Then for the valuation: I need to show `v_p(C(m+k,k)) > D/6 → cascade_length k D m ≥ D/6 - log p k`. Let me check if there's an existing lemma that gives a bound on `v_p` for arbitrary `m` using `cascade_length`:
```bash
$ cd /home/jarred/code/erdos-728b && grep -n "valuation\|v_p\|padicValNat.*cascade\|cascade.*padicVal" Erdos/Lemma3Counting.lean | head -20
```
There's only `valuation_le_cascade` which requires `m < p^D`. Let me think about how to handle the general `m` case.

Actually, I realize there might be a much simpler approach. The argument for the general case goes through `carry_propagate`. The key fact is:

**If `v_p(C(m+k,k)) > D/6`, then ALL carries at positions s+1 through s+1+(D/6-s-1) = D/6 must be 1.** This means digits at positions s+1 through s+(D/6-s-1) = D/6-1 must all be `p-1`. These are positions < D. And this condition depends only on `m mod p^D`.

More precisely: carries in `m + k` are determined by the carry recurrence, which at position `i` depends on `m mod p^(i+1)` and `k mod p^(i+1)`. So carries at all positions 0..D-1 depend on `m mod p^D`.

Let me try to use `carry_propagate` to prove conjunct 1 directly. The approach:

1. Show `cascade_length k D (m % p^D) = cascade_length k D m` (digit invariance under mod).
2. Show that if `v_p > D/6 > s+1`, then by the carry structure, the cascade in digits 0..D-1 must be ≥ D/6 - s.

Actually, let me try a different, more direct strategy. Conjunct 1 might be provable without going through carries at all, by using the sorry'd `valuation_le_cascade` for `m % p^D`:

- Given: `v_p(C(m+k,k)) > D/6`.
- We want: `cascade_length k D (m % p^D) ≥ D/6 - log p k`.
- Since `cascade_length k D (m % p^D) = cascade_length k D m`, we want: `cascade_length k D m ≥ D/6 - log p k`.
- By `valuation_le_cascade` (for `m' = m % p^D < p^D`): `v_p(C(m'+k,k)) ≤ (s+1) + cascade_length k D m'`.
- But we have `v_p(C(m+k,k)) > D/6`, not `v_p(C(m'+k,k)) > D/6`.
- These are DIFFERENT valuations since m ≠ m'.

So `valuation_le_cascade` doesn't directly help for arbitrary `m`. We'd need either:
a) `v_p(C(m+k,k)) ≤ (s+1) + cascade_length k D m` for arbitrary m, OR
b) `v_p(C(m+k,k)) = v_p(C(m%p^D + k, k))` (valuation depends only on m mod p^D), OR
c) Some other approach.

Option (a) is actually FALSE for arbitrary m — the cascade length is capped at D-(s+1), but the actual valuation can be larger than (s+1) + D - (s+1) = D.

Option (b) is also likely false — the valuation depends on all digits, not just the first D.

Hmm, but actually the full NL proof argument says that if the cascade within the first D digits terminates before position D, then no carries reach position D, and the total valuation is bounded by the cascade. And if the cascade reaches position D-1, then `cascade_length ≥ D - s - 1 ≥ D/6 - s` (given our assumption on D), so the conclusion holds trivially.

Let me formalize this argument directly. I'll need a helper lemma about carries. Let me look at `carry_propagate` and `carry_cond`:
🛠️ **Executing tool: read**
OK, let me take a pragmatic approach. Since `valuation_le_cascade` is sorry'd but has the right type, I can use it. But it only works for `m < p^D`. For the general case, I need a few things:

1. `cascade_length k D (m % p^D) = cascade_length k D m` — because `cascade_length` depends on digits at positions `< D`.
2. For conjunct 1: I need to show `v_p(C(m+k,k)) > D/6 → cascade_length k D m ≥ D/6 - log p k`. 

This requires either (a) extending `valuation_le_cascade` to arbitrary `m`, or (b) a direct argument about carries.

Let me take approach (b), using `carry_propagate` which IS proved. The argument:

If `cascade_length k D m < D/6 - log p k`, let `L = cascade_length k D m`. Then there exists a position `j = s + 1 + L` with `j < D` where `digit p m j ≠ p-1`. 

Now, the carry at position `j` in `m + k` must be 0 (since `j > s`, the cascade dies at position `j`). If there's no carry into position `j`, then... actually, `carry_propagate` works in the reverse direction (from a higher carry back down). 

Hmm, let me think about this differently. `carry_propagate` says: if there's a carry at position `i > s+1`, then `digit p m (i-1) = p-1` AND there's a carry at position `i-1`. By induction, if there's a carry at position `i > s+1`, then digits at positions `s+1, ..., i-1` are all `p-1`. So the number of carries at positions `> s+1` is at most the cascade length L.

Total carries = (carries at 0..s) + (carries at s+1..∞). The carries at 0..s are ≤ s+1. The carries at positions s+1..∞: each carry at position `i > s+1` requires all digits at s+1..i-1 to be p-1, so the carry can propagate at most until position s+1+L (where L is the cascade length with D positions). Wait, but carries beyond position D-1 could come from digits beyond D...

Actually, `cascade_length k D m` measures the run of `p-1` digits starting at position `s+1` within the first D positions. If the run ends at position `s+1+L < D`, then `digit p m (s+1+L) ≠ p-1`. This means, by `carry_propagate` (contrapositive), there CANNOT be a carry at position `s+1+L+1` (if `s+1+L+1 > s+1`, which it always is since L ≥ 0). So carries at positions ≥ s+1+L+1 are all 0.

But wait — carries at position `i` also depend on `m mod p^i`, not just `digit p m (i-1)`. The `carry_propagate` lemma says: if `carry_cond p k m i` (i.e., `p^i ≤ k%p^i + m%p^i`) and `i > s+1`, then `digit p m (i-1) = p-1` AND `carry_cond p k m (i-1)`. Contrapositive: if digit at `i-1` ≠ p-1 or no carry at `i-1`, then no carry at `i`.

So if `digit p m (s+1+L) ≠ p-1` and `s+1+L+1 > s+1` (always true), then carry at position `s+1+L+1` is impossible (unless the carry at `s+L+1` doesn't hold). Wait, I need to be careful about the indexing.

Let me formalize the contrapositive of `carry_propagate`:

`carry_propagate` says: for `i > s+1`, `carry_cond at i` → `digit at i-1 = p-1 ∧ carry_cond at i-1`.

Contrapositive: `digit at i-1 ≠ p-1 ∨ ¬carry_cond at i-1` → `¬carry_cond at i`.

So if at position `j = s+1+L`, `digit p m j ≠ p-1`, then at position `j+1 = s+2+L > s+1`, we have ¬carry_cond at `j+1`. And by induction, no carry at any position > j.

This means the total number of carries is at most (s+1) + L.

This gives: `v_p(C(m+k,k)) ≤ (s+1) + L` for all m (not just m < p^D), as long as L < D - s - 1 (so that the cascade terminates within D).

If L = D - s - 1 (cascade fills all available positions), then we're done too: D/6 - s ≤ D - s - 1 for D ≥ 16*(s+1)+16 implies D/6 ≤ D-1, which is true for D ≥ 1.

OK, this is getting quite involved. Let me try a different approach: maybe I should just introduce a helper lemma with a sorry for the first conjunct, and focus on what I can prove cleanly.

Actually wait — let me re-read the `bad_residue_sets` statement one more time. Maybe I can take a simpler approach.

For conjunct 2:
```
∀ m, padicValNat p ((2 * m).choose m) < D/6 → 
  m % p^D ∈ (range (p^D)).filter (fun r => count_high_digits p r D < D/6)
```

This requires:
1. `m % p^D < p^D` (for `mem_range` in the filter)
2. `count_high_digits p (m % p^D) D < D/6`

For (2), since `count_high_digits` depends on digits 0..D-1, we have `count_high_digits p (m % p^D) D = count_high_digits p m D`.

But we need `count_high_digits p m D < D/6`. From the hypothesis `v_p(C(2m,m)) < D/6`, combined with `valuation_ge_high_digits` which says `v_p(C(2m,m)) ≥ count_high_digits p m D`, we get `count_high_digits p m D ≤ v_p(C(2m,m)) < D/6`.

Wait, `valuation_ge_high_digits` has a condition `log p (2*m) < D + 1`. For arbitrary m this may not hold! But if `m` is large enough, `log p (2m)` could exceed D.

Hmm, but if `log p (2m) ≥ D + 1`, then `2m ≥ p^(D+1)`, and the valuation could be anything. But actually `count_high_digits p m D` only counts digits 0..D-1, while `v_p(C(2m,m))` counts carries at ALL positions. The valuation is ≥ count_high_digits only for the first D positions.

Actually let me re-read `valuation_ge_high_digits`:
```
lemma valuation_ge_high_digits (hp : p.Prime) (m : ℕ) (h_log : log p (2*m) < D + 1) :
    padicValNat p ((2*m).choose m) ≥ count_high_digits p m D
```

It requires `log p (2*m) < D + 1`. For arbitrary m, this might not hold.

But wait — if `m` is large (log p (2m) ≥ D+1), then `2m ≥ p^(D+1)`, so `m ≥ p^D / 2`. In this case, `count_high_digits p m D` still only counts D digits. And `v_p(C(2m,m)) ≥` carries from all high digits, not just the first D. So the inequality should still hold... but the formalized lemma only handles `log p (2*m) < D + 1`.

For conjunct 2, we need to handle arbitrary `m`. If `log p (2*m) < D + 1`, we can use `valuation_ge_high_digits` directly. If `log p (2*m) ≥ D + 1`, then `2m ≥ p^(D+1)`, and we'd need to extend the lemma.

Alternatively, `lower_bound_valuation_by_high_digits` uses `Nat.factorization_choose` which likely has a condition on the log bound.

This is getting complex. Let me take a step back and think about what's actually practical here. Given the complexity of both conjuncts, let me try to write the proof skeleton with well-isolated helper lemmas that can be sorry'd if needed.

Let me first focus on what I can prove cleanly and build up:
```bash
$ cd /home/jarred/code/erdos-728b && tm update erdos728b-hga --status "Building helper lemmas: digit_mod_pow_eq, cascade_length_mod, count_high_digits_mod"
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_helpers.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat Finset Erdos728

-- Helper 1: digit p (m % p^D) i = digit p m i for i < D
lemma digit_mod_pow_eq (p m D i : ℕ) (hp : p > 0) (hi : i < D) : 
    digit p (m % p ^ D) i = digit p m i := by
  unfold digit
  have hD_split : p ^ D = p ^ i * p ^ (D - i) := by
    rw [← pow_add]; congr 1; omega
  rw [hD_split, Nat.mod_mul_right_div_self]
  apply Nat.mod_mod_of_dvd
  exact dvd_pow_self p (by omega : D - i ≠ 0)

-- Helper 2: cascade_length only depends on m mod p^D
lemma cascade_length_mod_eq {p : ℕ} (k D m : ℕ) (hp : p > 0) (hD : D ≥ log p k + 1) :
    cascade_length (p := p) k D (m % p ^ D) = cascade_length (p := p) k D m := by
  unfold cascade_length
  congr 1
  apply List.takeWhile_ext
  intro i hi
  -- i is in List.range (D - (log p k + 1)), so i < D - (log p k + 1)
  rw [List.mem_range] at hi
  have hi_lt_D : log p k + 1 + i < D := by omega
  rw [digit_mod_pow_eq p m D (log p k + 1 + i) hp hi_lt_D]

-- Helper 3: count_high_digits only depends on m mod p^D
lemma count_high_digits_mod_eq (p m D : ℕ) (hp : p > 0) :
    count_high_digits p (m % p ^ D) D = count_high_digits p m D := by
  unfold count_high_digits high_digits_finset is_high_digit
  congr 1
  ext i
  simp only [mem_filter, mem_range]
  constructor
  · intro ⟨hi, hd⟩; exact ⟨hi, by rw [digit_mod_pow_eq p m D i hp hi] at hd; exact hd⟩
  · intro ⟨hi, hd⟩; exact ⟨hi, by rw [digit_mod_pow_eq p m D i hp hi]; exact hd⟩
EOF
lake env lean /tmp/test_helpers.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && grep -rn "takeWhile" .lake/packages/mathlib/Mathlib/Data/List/ --include="*.lean" | grep -i "ext\|congr" | head -10
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_tw.lean << 'EOF'
import Mathlib.Data.List.Basic

#check @List.takeWhile_eq_takeWhile_iff
#check @List.takeWhile
-- Search for something about takeWhile extensionality
example (l : List ℕ) (p q : ℕ → Bool) (h : ∀ x, x ∈ l → p x = q x) :
    l.takeWhile p = l.takeWhile q := by
  exact?
EOF
lake env lean /tmp/test_tw.lean 2>&1 | tail -10
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_tw.lean << 'EOF'
import Mathlib.Data.List.Basic

-- Try to prove takeWhile extensionality by induction
example (l : List ℕ) (p q : ℕ → Bool) (h : ∀ x, x ∈ l → p x = q x) :
    l.takeWhile p = l.takeWhile q := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.takeWhile_cons]
    rw [h a (List.mem_cons_self a t)]
    split
    · congr 1; exact ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    · rfl
EOF
lake env lean /tmp/test_tw.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_tw.lean << 'EOF'
import Mathlib.Data.List.Basic

example (l : List ℕ) (p q : ℕ → Bool) (h : ∀ x, x ∈ l → p x = q x) :
    l.takeWhile p = l.takeWhile q := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.takeWhile_cons]
    rw [h a (List.mem_cons_self _ _)]
    split
    · congr 1; exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    · rfl
EOF
lake env lean /tmp/test_tw.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_tw.lean << 'EOF'
import Mathlib.Data.List.Basic

#check @List.mem_cons_self
#print List.mem_cons_self
EOF
lake env lean /tmp/test_tw.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_tw.lean << 'EOF'
import Mathlib.Data.List.Basic

example (l : List ℕ) (p q : ℕ → Bool) (h : ∀ x, x ∈ l → p x = q x) :
    l.takeWhile p = l.takeWhile q := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.takeWhile_cons]
    rw [h a List.mem_cons_self]
    split
    · congr 1; exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    · rfl
EOF
lake env lean /tmp/test_tw.lean 2>&1
```
Good. Now let me use `decide` for the equality of predicates in cascade_length. The predicate in cascade_length is `fun i => digit p m (s + 1 + i) = p - 1` which is a decidable equality check. Let me fix the cascade_length_mod_eq lemma:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_helpers2.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat Finset Erdos728

-- Helper 1: digit p (m % p^D) i = digit p m i for i < D
lemma digit_mod_pow_eq' (p m D i : ℕ) (hp : p > 0) (hi : i < D) : 
    digit p (m % p ^ D) i = digit p m i := by
  unfold digit
  have hD_split : p ^ D = p ^ i * p ^ (D - i) := by
    rw [← pow_add]; congr 1; omega
  rw [hD_split, Nat.mod_mul_right_div_self]
  apply Nat.mod_mod_of_dvd
  exact dvd_pow_self p (by omega : D - i ≠ 0)

-- Helper: takeWhile ext for decidable props
private lemma takeWhile_congr {l : List ℕ} {p q : ℕ → Bool} 
    (h : ∀ x, x ∈ l → p x = q x) : l.takeWhile p = l.takeWhile q := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.takeWhile_cons]
    rw [h a List.mem_cons_self]
    split
    · congr 1; exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    · rfl

-- Helper 2: cascade_length only depends on m mod p^D
lemma cascade_length_mod_eq' {p : ℕ} (k D m : ℕ) (hp : p > 0) :
    cascade_length (p := p) k D (m % p ^ D) = cascade_length (p := p) k D m := by
  unfold cascade_length
  simp only
  congr 1
  apply takeWhile_congr
  intro i hi
  rw [List.mem_range] at hi
  -- i < D - (log p k + 1), so log p k + 1 + i < D
  have hi_lt_D : log p k + 1 + i < D := by omega
  simp only [decide_eq_decide]
  rw [digit_mod_pow_eq' p m D (log p k + 1 + i) hp hi_lt_D]
EOF
lake env lean /tmp/test_helpers2.lean 2>&1
```
Now let me work on the main proof. Let me think about the approach:

**Conjunct 1**: `v_p(C(m+k,k)) > D/6 → cascade_length k D (m%p^D) ≥ D/6 - log p k`

Since `cascade_length k D (m%p^D) = cascade_length k D m`, I need:
`v_p(C(m+k,k)) > D/6 → cascade_length k D m ≥ D/6 - log p k`

This is the contrapositive of: `cascade_length k D m < D/6 - log p k → v_p(C(m+k,k)) ≤ D/6`.

The proof of the contrapositive uses `carry_propagate` to show that if the cascade is short, carries at positions beyond the cascade are 0, bounding the total valuation.

But formalizing the connection between carries and `padicValNat` requires `valuation_le_cascade` or its generalization. Since `valuation_le_cascade` is sorry'd but available for `m < p^D`, and the cascade_length doesn't depend on digits beyond D, I need to handle the general case.

Let me think about whether I can factor out a helper lemma for the general case and sorry it cleanly.

Actually, wait. Let me look at this from the perspective of what `carry_propagate` actually gives us. `carry_propagate` tells us about the carry condition `carry_cond p k m i := p ^ i ≤ k % p ^ i + m % p ^ i`. Note that `carry_cond` depends on `m % p^i`, not on all of `m`. So `carry_cond p k m i = carry_cond p k (m % p^D) i` for `i ≤ D`.

The number of carries in base-p addition of `m` and `k` equals `v_p(C(m+k,k))` by Kummer's theorem. The carries at positions 0..D-1 depend on `m mod p^D`. But carries at positions ≥ D may exist for the full `m`.

For the contrapositive argument: if `cascade_length k D m < D/6 - s`, then the cascade dies at some position `j = s + 1 + L < D` where `digit p m j ≠ p-1`. By `carry_propagate` (contrapositive), there's no carry at position `j + 1`. So `¬carry_cond p k m (j+1)`.

Now, `carry_cond p k m (j+1)` is `p^(j+1) ≤ k % p^(j+1) + m % p^(j+1)`. Since `j+1 > s+1`, `k < p^(j+1)`, so `k % p^(j+1) = k`. And `m % p^(j+1)` depends on m (all of it, not just mod p^D).

Wait, `m % p^(j+1)` is just `m % p^(j+1)` — it doesn't depend on anything beyond `j+1` digits. And `j + 1 ≤ D`, so `m % p^(j+1) = (m % p^D) % p^(j+1)`.

So `carry_cond p k m (j+1) = carry_cond p k (m % p^D) (j+1)`. The carry at position `j+1` depends only on `m mod p^(j+1)`, which depends only on `m mod p^D` when `j+1 ≤ D`.

OK so the carry at any position `i ≤ D` depends only on `m mod p^D`. And by the cascade argument, if the cascade dies at position `j < D`, then `carry_cond p k m i` is false for all `i ≥ j+1`. In particular, `carry_cond p k m D` is false.

Now, what about carries at positions ≥ D? `carry_cond p k m D = (p^D ≤ k % p^D + m % p^D)`. Since `k < p^D` (assuming `D > s`), `k % p^D = k`. So `carry_cond p k m D = (p^D ≤ k + m % p^D)`.

If the cascade dies at `j < D`, then by repeated application of carry_propagate (contrapositive), `¬carry_cond p k m (j+1)`, which means `p^(j+1) > k + m % p^(j+1)`.

But then at position `j+2 > s+1`: if there were a carry, then `carry_propagate` would give `digit p m (j+1) = p-1` and carry at `j+1`. But we know there's no carry at `j+1`. So no carry at `j+2`. By induction, no carry at any position ≥ j+1.

Now, the total valuation `v_p(C(m+k,k))` = total number of carries. If no carry at position ≥ j+1, then carries only happen at positions 0..j. There are at most `j+1` positions, so `v_p ≤ j + 1 = s + 1 + L + 1`.

Wait, actually `v_p` is the count of positions where `carry_cond` holds. By Kummer's theorem, the number of carries in `m + k` in base p equals `v_p(C(m+k,k))`.

But hold on — Kummer's theorem says the number of carries at ALL positions (0 to ∞) equals the valuation. If there are only finitely many carries (which there always are since `m + k` is finite), and all carries are at positions 0..j, then `v_p = #{i ∈ 0..j : carry at i} ≤ j + 1`.

So the argument would be:
1. If cascade length L < D/6 - s, then the cascade dies at position j = s + 1 + L < D.
2. No carry at position j + 1 (by contrapositive of carry_propagate and digit ≠ p-1).
3. No carry at any position ≥ j + 1 (by induction using carry_propagate).
4. Total carries ≤ j + 1 = s + 2 + L < s + 2 + D/6 - s = D/6 + 2.
5. Actually, carries at 0..s are ≤ s + 1, and carries at s+1..j are ≤ L, so total ≤ s + 1 + L < s + 1 + D/6 - s = D/6 + 1.
6. So v_p ≤ D/6 (since v_p ≤ s + 1 + L and L < D/6 - s means s + 1 + L < D/6 + 1, so s + 1 + L ≤ D/6).

This is clean but requires formalizing the relationship between carries and padicValNat, which is essentially `valuation_le_cascade` generalized to arbitrary m.

Given the complexity and the fact that `valuation_le_cascade` is already sorry'd, let me introduce a generalization of it as a helper lemma and sorry it, focusing on the parts of `bad_residue_sets` that I CAN close.

Actually, let me reconsider. The statement of `bad_residue_sets` essentially packages two "mod invariance" claims. Maybe I should factor it differently:

1. Introduce a sorry'd helper: `valuation_implies_cascade (hp) (k D m) (hk) : padicValNat p ((m + k).choose k) > D/6 → cascade_length k D m ≥ D/6 - log p k`
2. Prove `cascade_length k D (m % p^D) = cascade_length k D m` (done)
3. Prove `count_high_digits p (m % p^D) D = count_high_digits p m D` (done)
4. Introduce a sorry'd or provable helper for conjunct 2: `valuation_implies_count_high`

For conjunct 2: `v_p(C(2m,m)) < D/6 → count_high_digits p m D < D/6`. This follows from `valuation_ge_high_digits` which says `v_p ≥ count_high_digits` (under a log condition). But the log condition may not hold for arbitrary m.

However! If `count_high_digits p m D ≥ D/6`, then we're done trivially (the hypothesis would be false or unneeded). And if `count_high_digits p m D < D/6`, then the conclusion holds. Wait, that's circular.

The logic is: hypothesis says `v_p < D/6`. We need `count_high_digits < D/6`. By `valuation_ge_high_digits` (if applicable): `count_high_digits ≤ v_p < D/6`. The issue is the log condition.

Hmm, but `valuation_ge_high_digits` uses `lower_bound_valuation_by_high_digits` which in turn uses `Nat.factorization_choose` which requires `2m ≤ p^(D+1)` or similar. For arbitrary large m, this may fail.

But actually, for any m, the carries in `m + m` at positions 0..D-1 all contribute to `v_p(C(2m,m))`, and `count_high_digits p m D` counts a subset of these carries (only counting positions where the digit is high). So the inequality `v_p(C(2m,m)) ≥ count_high_digits p m D` should hold without any restriction on m, since each high digit at position `i < D` creates a carry at position `i`, and these are all distinct contributions to the total valuation.

The fact that `valuation_ge_high_digits` needs the log bound is a limitation of the current formalization, not a mathematical necessity.

Let me take a pragmatic approach: introduce well-annotated sorry'd helper lemmas for the parts I can't prove from existing infrastructure, and prove everything else cleanly.
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_full.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat Finset Erdos728

set_option linter.unusedVariables false

-- Helper: digit p (m % p^D) i = digit p m i for i < D
private lemma digit_mod_pow_eq (p m D i : ℕ) (hp : p > 0) (hi : i < D) : 
    digit p (m % p ^ D) i = digit p m i := by
  unfold digit
  have hD_split : p ^ D = p ^ i * p ^ (D - i) := by
    rw [← pow_add]; congr 1; omega
  rw [hD_split, Nat.mod_mul_right_div_self]
  apply Nat.mod_mod_of_dvd
  exact dvd_pow_self p (by omega : D - i ≠ 0)

-- Helper: takeWhile extensionality
private lemma takeWhile_congr' {l : List ℕ} {p q : ℕ → Bool} 
    (h : ∀ x, x ∈ l → p x = q x) : l.takeWhile p = l.takeWhile q := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.takeWhile_cons]
    rw [h a List.mem_cons_self]
    split
    · congr 1; exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    · rfl

-- cascade_length only depends on m mod p^D
private lemma cascade_length_mod_eq {p : ℕ} (k D m : ℕ) (hp : p > 0) :
    cascade_length (p := p) k D (m % p ^ D) = cascade_length (p := p) k D m := by
  unfold cascade_length
  simp only
  congr 1
  apply takeWhile_congr'
  intro i hi
  rw [List.mem_range] at hi
  simp only [decide_eq_decide]
  rw [digit_mod_pow_eq p m D (log p k + 1 + i) hp (by omega)]

-- count_high_digits only depends on m mod p^D
private lemma count_high_digits_mod_eq (p m D : ℕ) (hp : p > 0) :
    count_high_digits p (m % p ^ D) D = count_high_digits p m D := by
  unfold count_high_digits high_digits_finset is_high_digit
  congr 1
  ext i
  simp only [mem_filter, mem_range]
  constructor
  · intro ⟨hi, hd⟩; exact ⟨hi, by rw [digit_mod_pow_eq p m D i hp hi] at hd; exact hd⟩
  · intro ⟨hi, hd⟩; exact ⟨hi, by rw [digit_mod_pow_eq p m D i hp hi]; exact hd⟩

/-- STUB: For arbitrary m, v_p(C(m+k,k)) > D/6 implies the cascade within D digits
    is at least D/6 - log p k. This follows from carry_propagate (contrapositive):
    if cascade < D/6 - s, no carry reaches position s+1+cascade+1, so total
    carries ≤ (s+1) + cascade < D/6 + 1, contradicting v_p > D/6.
    Needs: formalization of Kummer's theorem carry count for arbitrary m. -/
private lemma valuation_gt_implies_cascade {p : ℕ} (hp : p.Prime) (k D m : ℕ)
    (hk : k ≥ 1) (hD : D ≥ 16 * (log p (k + 1)) + 16) :
    padicValNat p ((m + k).choose k) > D / 6 →
    cascade_length (p := p) k D m ≥ D / 6 - log p k := by
  sorry

/-- STUB: For arbitrary m, count_high_digits p m D ≤ v_p(C(2m,m)).
    Each high digit at position i < D forces a carry at position i in m+m,
    contributing 1 to v_p. The current formalization (valuation_ge_high_digits)
    requires log p (2m) < D+1, but the result holds without this condition since
    carries at positions 0..D-1 always contribute to the total valuation. -/
private lemma count_high_le_valuation {p : ℕ} (hp : p.Prime) (m D : ℕ) :
    count_high_digits p m D ≤ padicValNat p ((2 * m).choose m) := by
  sorry

EOF
lake env lean /tmp/test_full.lean 2>&1
```
Good, these compile. Now let me prove the main lemma using these helpers:
```bash
$ cd /home/jarred/code/erdos-728b && cat >> /tmp/test_full.lean << 'EOF'

-- Now prove bad_residue_sets using the helpers
example {p : ℕ} {D k : ℕ} (hp : p.Prime) (hD : D ≥ 16 * (log p (k + 1)) + 16) :
    (∀ m, padicValNat p ((m + k).choose k) > D/6 → 
      m % p^D ∈ (range (p^D)).filter (fun r => cascade_length (p:=p) k D r ≥ D/6 - log p k)) ∧
    (∀ m, padicValNat p ((2 * m).choose m) < D/6 → 
      m % p^D ∈ (range (p^D)).filter (fun r => count_high_digits p r D < D/6)) := by
  have hp_pos : p > 0 := Nat.Prime.pos hp
  have hpD_pos : p ^ D > 0 := Nat.pos_of_ne_zero (by positivity)
  constructor
  · -- Conjunct 1: high valuation → cascade residue
    intro m hv
    rw [mem_filter]
    constructor
    · exact mem_range.mpr (Nat.mod_lt m hpD_pos)
    · -- cascade_length of (m % p^D) ≥ D/6 - log p k
      rw [cascade_length_mod_eq k D m hp_pos]
      have hk : k ≥ 1 := by
        by_contra hk_lt
        push_neg at hk_lt
        interval_cases k
        simp at hv
      exact valuation_gt_implies_cascade hp k D m hk hD hv
  · -- Conjunct 2: low valuation → few high digits residue
    intro m hv
    rw [mem_filter]
    constructor
    · exact mem_range.mpr (Nat.mod_lt m hpD_pos)
    · -- count_high_digits of (m % p^D) < D/6
      rw [count_high_digits_mod_eq p m D hp_pos]
      exact Nat.lt_of_le_of_lt (count_high_le_valuation hp m D) hv
EOF
lake env lean /tmp/test_full.lean 2>&1
```
Wait, no errors from the final example — but also no warning about it using sorry. Let me check if it compiled:
```bash
$ cd /home/jarred/code/erdos-728b && cat >> /tmp/test_full.lean << 'EOF2'

-- Verify the example compiled
#check @Nat.mod_lt
EOF2
lake env lean /tmp/test_full.lean 2>&1
```
Wait, I need to check if the `example` also uses sorry. Let me check by looking at warnings more carefully:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_full2.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat Finset Erdos728

set_option linter.unusedVariables false

private lemma digit_mod_pow_eq (p m D i : ℕ) (hp : p > 0) (hi : i < D) : 
    digit p (m % p ^ D) i = digit p m i := by
  unfold digit
  have hD_split : p ^ D = p ^ i * p ^ (D - i) := by
    rw [← pow_add]; congr 1; omega
  rw [hD_split, Nat.mod_mul_right_div_self]
  apply Nat.mod_mod_of_dvd
  exact dvd_pow_self p (by omega : D - i ≠ 0)

private lemma takeWhile_congr' {l : List ℕ} {p q : ℕ → Bool} 
    (h : ∀ x, x ∈ l → p x = q x) : l.takeWhile p = l.takeWhile q := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.takeWhile_cons]
    rw [h a List.mem_cons_self]
    split
    · congr 1; exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    · rfl

private lemma cascade_length_mod_eq {p : ℕ} (k D m : ℕ) (hp : p > 0) :
    cascade_length (p := p) k D (m % p ^ D) = cascade_length (p := p) k D m := by
  unfold cascade_length
  simp only
  congr 1
  apply takeWhile_congr'
  intro i hi
  rw [List.mem_range] at hi
  simp only [decide_eq_decide]
  rw [digit_mod_pow_eq p m D (log p k + 1 + i) hp (by omega)]

private lemma count_high_digits_mod_eq (p m D : ℕ) (hp : p > 0) :
    count_high_digits p (m % p ^ D) D = count_high_digits p m D := by
  unfold count_high_digits high_digits_finset is_high_digit
  congr 1
  ext i
  simp only [mem_filter, mem_range]
  constructor
  · intro ⟨hi, hd⟩; exact ⟨hi, by rw [digit_mod_pow_eq p m D i hp hi] at hd; exact hd⟩
  · intro ⟨hi, hd⟩; exact ⟨hi, by rw [digit_mod_pow_eq p m D i hp hi]; exact hd⟩

/-- STUCK: For arbitrary m, v_p(C(m+k,k)) > D/6 implies the cascade within D digits
    is at least D/6 - log p k. This follows from carry_propagate (contrapositive):
    if cascade < D/6 - s, no carry reaches position s+1+cascade+1, so total
    carries ≤ (s+1) + cascade < D/6 + 1, contradicting v_p > D/6.
    Needs: formalization of Kummer's carry count as a sum over all positions,
    then induction using carry_propagate to show carries beyond cascade are 0. -/
private lemma valuation_gt_implies_cascade {p : ℕ} (hp : p.Prime) (k D m : ℕ)
    (hk : k ≥ 1) (hD : D ≥ 16 * (log p (k + 1)) + 16) :
    padicValNat p ((m + k).choose k) > D / 6 →
    cascade_length (p := p) k D m ≥ D / 6 - log p k := by
  sorry

/-- STUCK: For arbitrary m, count_high_digits p m D ≤ v_p(C(2m,m)).
    Each high digit at position i < D forces a carry at position i in m+m (Lemma B1),
    contributing 1 to v_p. The existing valuation_ge_high_digits requires
    log p (2m) < D+1. This general version needs Kummer's carry formulation
    without the log bound restriction, or a direct argument about carries. -/
private lemma count_high_le_valuation {p : ℕ} (hp : p.Prime) (m D : ℕ) :
    count_high_digits p m D ≤ padicValNat p ((2 * m).choose m) := by
  sorry

lemma bad_residue_sets' {p : ℕ} (D k : ℕ) (hp : p.Prime) (hD : D ≥ 16 * (log p (k + 1)) + 16) :
    (∀ m, padicValNat p ((m + k).choose k) > D/6 → 
      m % p^D ∈ (range (p^D)).filter (fun r => cascade_length (p:=p) k D r ≥ D/6 - log p k)) ∧
    (∀ m, padicValNat p ((2 * m).choose m) < D/6 → 
      m % p^D ∈ (range (p^D)).filter (fun r => count_high_digits p r D < D/6)) := by
  have hp_pos : p > 0 := Nat.Prime.pos hp
  have hpD_pos : p ^ D > 0 := Nat.pos_of_ne_zero (by positivity)
  constructor
  · intro m hv
    rw [mem_filter]
    constructor
    · exact mem_range.mpr (Nat.mod_lt m hpD_pos)
    · rw [cascade_length_mod_eq k D m hp_pos]
      have hk : k ≥ 1 := by
        by_contra hk_lt
        push_neg at hk_lt
        interval_cases k
        simp at hv
      exact valuation_gt_implies_cascade hp k D m hk hD hv
  · intro m hv
    rw [mem_filter]
    constructor
    · exact mem_range.mpr (Nat.mod_lt m hpD_pos)
    · rw [count_high_digits_mod_eq p m D hp_pos]
      exact Nat.lt_of_le_of_lt (count_high_le_valuation hp m D) hv
EOF
lake env lean /tmp/test_full2.lean 2>&1
```
Hmm, I only see warnings for the two sorry'd helper lemmas. The `bad_residue_sets'` itself doesn't show a warning, which is surprising since it uses those sorry'd lemmas. Let me check:
```bash
$ cd /home/jarred/code/erdos-728b && echo '#check @bad_residue_sets'"'" >> /tmp/test_full2.lean && lake env lean /tmp/test_full2.lean 2>&1 | tail -5
```
Good, it compiles. Now let me try to close the two sorry'd helper lemmas. Let me first try `count_high_le_valuation`:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_count_high.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat Finset Erdos728

-- For arbitrary m, count_high_digits p m D ≤ v_p(C(2m,m))
-- The existing valuation_ge_high_digits requires log p (2m) < D+1
-- Let's try: if m = 0, both sides are 0. If m > 0, we need to handle it.
-- Actually, if log p (2m) ≥ D + 1, then 2m ≥ p^(D+1).
-- But count_high_digits only counts D digits, so it's ≤ D.
-- And v_p(C(2m,m)) ≥ count of carries at ALL positions ≥ D digits with high values.
-- We can prove this by extending valuation_ge_high_digits or by a direct argument.

-- Actually, let me check: maybe we can always ensure log p (2m) < D + 1 
-- by reducing to m mod p^D?
-- No, that would change the binomial coefficient.

-- Key insight: Nat.factorization_choose hp requires log p (2m) < D+1.
-- But high_digit_forces_carry works for any position i regardless of m's size.
-- The factorization_choose formula sums carries at positions 1..log_p(2m).
-- For i+1 ≤ D (i.e., i < D), the carry at position i+1 is determined by m mod p^(i+1).
-- Each high digit at position i creates a carry that contributes to the sum.

-- The connection: v_p(C(2m,m)) = sum over j≥1 of floor((2m mod p^j + 2m mod p^j - 2m mod p^j) / p^j)
-- No, Kummer: v_p(C(2m,m)) = # carries in m + m in base p.

-- Let me try a different approach: bound factorization directly
-- Actually, for the case where m is large, v_p(C(2m,m)) is even larger.
-- The key is that v_p(C(2m,m)) ≥ number of carries at positions 0..D-1.
-- Each high digit forces a carry (by high_digit_forces_carry).
-- So v_p(C(2m,m)) ≥ count of high digits at positions 0..D-1 = count_high_digits p m D.

-- The issue is connecting "carries at positions 0..D-1" to v_p.
-- v_p(C(2m,m)) = (sum of carries at positions 0..D-1) + (carries at positions ≥ D) ≥ carries at 0..D-1.

-- Can we express v_p as a sum? Yes: 
-- v_p(C(a+b,a)) = sum_{i≥1} floor((a%p^i + b%p^i) / p^i) - floor(a%p^i / p^i) - floor(b%p^i / p^i)
-- For C(2m,m): a=b=m, so each term is floor((2*(m%p^i))/p^i) - 2*floor((m%p^i)/p^i)
-- But this is complicated.

-- Alternative: Use the Legendre formula directly.
-- v_p(n!) = sum_{i≥1} floor(n/p^i)
-- v_p(C(2m,m)) = v_p((2m)!) - 2*v_p(m!) = sum_{i≥1} (floor(2m/p^i) - 2*floor(m/p^i))

-- Each term floor(2m/p^i) - 2*floor(m/p^i) ∈ {0, 1}.
-- It equals 1 iff 2*(m mod p^i) ≥ p^i, i.e., the carry condition at position i.

-- So v_p(C(2m,m)) = sum_{i≥1} 1_{carry at position i}
-- And count_high_digits p m D = #{j ∈ 0..D-1 : digit j is high}
-- By high_digit_forces_carry: if digit j is high, then 2*(m%p^(j+1)) ≥ p^(j+1), i.e., carry at j+1.
-- So {j : digit j is high} ⊆ {j : carry at j+1 - 1}, meaning count_high_digits ≤ #{i ∈ 1..D : carry at i} ≤ v_p(C(2m,m)).

-- This is essentially what lower_bound_valuation_by_high_digits does, but that uses 
-- Nat.factorization_choose which requires a log bound.

-- Let me check if Nat.factorization_choose works without the log bound or if we can use 
-- the Legendre formula directly.

#check @Nat.factorization_choose
EOF
lake env lean /tmp/test_count_high.lean 2>&1 | grep "factorization_choose"
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_fc.lean << 'EOF'
import Mathlib.Data.Nat.Choose.Factorization

#print Nat.factorization_choose
EOF
lake env lean /tmp/test_fc.lean 2>&1 | head -20
```
So `Nat.factorization_choose` says:
```
v_p(C(n,k)) = #{i ∈ Ico 1 b : p^i ≤ k % p^i + (n-k) % p^i}
```
where `b > log p n`. This requires `k ≤ n` and `log p n < b`.

For `C(2m, m)`: `n = 2m`, `k = m`, so `n - k = m`. The formula gives:
```
v_p(C(2m,m)) = #{i ∈ Ico 1 b : p^i ≤ m % p^i + m % p^i} = #{i ∈ Ico 1 b : 2*(m % p^i) ≥ p^i}
```

And `count_high_digits p m D = #{j ∈ range D : digit j is high}`.

By `high_digit_forces_carry`: for each j < D with high digit, `p^(j+1) ≤ 2*(m % p^(j+1))`. So `j+1 ∈ Ico 1 b` (if b > D) and the carry condition holds at `j+1`.

The map `j ↦ j+1` is injective and maps high-digit positions into carry positions. So `count_high_digits ≤ v_p(C(2m,m))`.

The issue is: we need `b > log p (2m)`. For large `m`, we'd need a large `b`. But we can just take `b = max(D+1, log p (2m) + 1)`. The factorization formula works for any `b > log p n`.

Actually, looking at `lower_bound_valuation_by_high_digits` more carefully — it uses `b = D + 1` and requires `log p (2m) < D + 1`. For the general case, we can use `b = log p (2m) + 1` which always works (assuming `m > 0` so that `2m > 0`).

Let me try to prove `count_high_le_valuation` by using `factorization_choose` with a large enough `b`:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_count_high2.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat Finset Erdos728

set_option linter.unusedVariables false

-- For arbitrary m, count_high_digits p m D ≤ v_p(C(2m,m))
lemma count_high_le_valuation' {p : ℕ} (hp : p.Prime) (m D : ℕ) :
    count_high_digits p m D ≤ padicValNat p ((2 * m).choose m) := by
  -- Handle m = 0 case
  by_cases hm : m = 0
  · simp [hm, count_high_digits, high_digits_finset, is_high_digit, digit]
  have hm_pos : m ≥ 1 := Nat.pos_of_ne_zero hm
  -- Use factorization_choose with b = max(D+1, log p (2m) + 1)
  let b := max (D + 1) (log p (2 * m) + 1)
  have hb : log p (2 * m) < b := by omega
  have hle : m ≤ 2 * m := Nat.le_mul_of_pos_left m (by omega)
  rw [Nat.factorization_def _ hp]
  rw [Nat.factorization_choose hp hle hb]
  -- Now: count_high_digits p m D ≤ card of {i ∈ Ico 1 b : p^i ≤ m%p^i + (2m-m)%p^i}
  -- Simplify: 2m - m = m
  have h2m_sub : 2 * m - m = m := by omega
  rw [h2m_sub]
  -- count_high_digits = card of {j ∈ range D : is_high_digit p m j}
  -- We inject via j ↦ j + 1: {j ∈ range D : high digit j} → {i ∈ Ico 1 b : carry at i}
  apply card_le_card_of_injOn (fun j => j + 1)
  · -- maps high digit positions into carry positions
    intro j hj
    simp only [mem_coe, high_digits_finset, mem_filter, mem_range] at hj
    simp only [mem_coe, mem_filter, mem_Ico]
    constructor
    · constructor
      · omega
      · omega  -- j + 1 ≤ D + 1 ≤ b
    · -- carry condition at j+1: p^(j+1) ≤ m % p^(j+1) + m % p^(j+1)
      exact high_digit_forces_carry p m j hj.2
  · -- injectivity
    intros x _ y _ hxy
    omega
EOF
lake env lean /tmp/test_count_high2.lean 2>&1
```
I need to fix the m=0 case and the factorization_def rewrite. Let me fix:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_count_high3.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat Finset Erdos728

set_option linter.unusedVariables false

-- m=0 case separately
private lemma count_high_zero (p D : ℕ) (hp : p > 0) : count_high_digits p 0 D = 0 := by
  unfold count_high_digits high_digits_finset is_high_digit digit
  simp [Nat.zero_div, Nat.zero_mod]
  intro i _
  omega

-- For arbitrary m, count_high_digits p m D ≤ v_p(C(2m,m))
lemma count_high_le_valuation' {p : ℕ} (hp : p.Prime) (m D : ℕ) :
    count_high_digits p m D ≤ padicValNat p ((2 * m).choose m) := by
  by_cases hm : m = 0
  · rw [hm, count_high_zero p D hp.pos]; exact Nat.zero_le _
  have hm_pos : m ≥ 1 := Nat.pos_of_ne_zero hm
  let b := max (D + 1) (log p (2 * m) + 1)
  have hb : log p (2 * m) < b := by omega
  have hle : m ≤ 2 * m := Nat.le_mul_of_pos_left m (by omega)
  have h2m_sub : 2 * m - m = m := by omega
  -- Rewrite padicValNat using factorization
  rw [← Nat.factorization_def _ hp, Nat.factorization_choose hp hle hb, h2m_sub]
  -- Now need: count_high_digits ≤ #{i ∈ Ico 1 b : p^i ≤ m%p^i + m%p^i}
  apply card_le_card_of_injOn (fun j => j + 1)
  · intro j hj
    simp only [mem_coe, high_digits_finset, mem_filter, mem_range] at hj
    simp only [mem_coe, mem_filter, mem_Ico]
    exact ⟨⟨by omega, by omega⟩, high_digit_forces_carry p m j hj.2⟩
  · intros x _ y _ hxy; omega
EOF
lake env lean /tmp/test_count_high3.lean 2>&1
```
Two issues: (1) the m=0 case has a problem, (2) the injection bound needs fixing. Let me fix both:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_count_high4.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat Finset Erdos728

set_option linter.unusedVariables false

-- Check what the simp produces for m=0
example (p D : ℕ) (hp : p > 0) : count_high_digits p 0 D = 0 := by
  unfold count_high_digits high_digits_finset is_high_digit digit
  simp [Nat.zero_div, Nat.zero_mod]
  -- The goal after simp should be: filter on range D where (p+1)/2 ≤ 0 is empty
  sorry
EOF
lake env lean /tmp/test_count_high4.lean 2>&1 | tail -10
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_count_high4.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat Finset Erdos728

set_option linter.unusedVariables false

example (p D : ℕ) (hp : p > 0) : count_high_digits p 0 D = 0 := by
  unfold count_high_digits high_digits_finset is_high_digit digit
  simp only [Nat.zero_div, Nat.zero_mod]
  -- What does the goal look like?
  rw [Finset.filter_false_of_mem]
  · exact Finset.card_empty
  · intro i _
    omega
EOF
lake env lean /tmp/test_count_high4.lean 2>&1
```
Now let me fix the injection bound. The issue is `j + 1 < b` where `b = max(D+1, log p (2m) + 1)` and `j < D`:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_count_high5.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat Finset Erdos728

set_option linter.unusedVariables false

lemma count_high_le_valuation' {p : ℕ} (hp : p.Prime) (m D : ℕ) :
    count_high_digits p m D ≤ padicValNat p ((2 * m).choose m) := by
  by_cases hm : m = 0
  · subst hm
    unfold count_high_digits high_digits_finset is_high_digit digit
    simp only [Nat.zero_div, Nat.zero_mod]
    rw [Finset.filter_false_of_mem]
    · exact Nat.zero_le _
    · intro i _; omega
  have hm_pos : m ≥ 1 := Nat.pos_of_ne_zero hm
  let b := max (D + 1) (log p (2 * m) + 1)
  have hb : log p (2 * m) < b := by simp [b]; omega
  have hle : m ≤ 2 * m := Nat.le_mul_of_pos_left m (by omega)
  have h2m_sub : 2 * m - m = m := by omega
  rw [← Nat.factorization_def _ hp, Nat.factorization_choose hp hle hb, h2m_sub]
  apply card_le_card_of_injOn (fun j => j + 1)
  · intro j hj
    simp only [mem_coe, high_digits_finset, mem_filter, mem_range] at hj
    simp only [mem_coe, mem_filter, mem_Ico]
    constructor
    · constructor
      · omega
      · simp [b]; omega  -- j + 1 ≤ D < D + 1 ≤ b
    · exact high_digit_forces_carry p m j hj.2
  · intros x _ y _ hxy; omega
EOF
lake env lean /tmp/test_count_high5.lean 2>&1
```
The m=0 case has the issue `(p+1)/2 ≤ 0` — omega can't prove this is false because it IS false (it's ≥ 1). Let me fix the filter_false approach:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_count_high6.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat Finset Erdos728

set_option linter.unusedVariables false

-- m=0: check what the goal looks like
example (p D : ℕ) (hp : Nat.Prime p) : count_high_digits p 0 D = 0 := by
  unfold count_high_digits high_digits_finset is_high_digit digit
  simp only [Nat.zero_div, Nat.zero_mod]
  -- goal should be card of filter ≤ something
  convert Finset.card_empty
  rw [Finset.eq_empty_iff_forall_not_mem]
  intro i
  simp only [mem_filter, mem_range, not_and]
  intro _
  have := Nat.Prime.two_le hp
  omega
EOF
lake env lean /tmp/test_count_high6.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_count_high6.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat Finset Erdos728

set_option linter.unusedVariables false

example (p D : ℕ) (hp : Nat.Prime p) : count_high_digits p 0 D = 0 := by
  unfold count_high_digits high_digits_finset is_high_digit digit
  simp only [Nat.zero_div, Nat.zero_mod]
  rw [Finset.filter_false_of_mem]
  · simp
  · intro i _
    have := Nat.Prime.two_le hp
    simp only [not_le]
    omega
EOF
lake env lean /tmp/test_count_high6.lean 2>&1
```
Good. Now let me fix the injection bound issue. The problem is `j + 1 < b` where `b = max(D+1, log p (2m) + 1)`. Since `j ∈ range D`, we have `j < D`, so `j + 1 ≤ D < D + 1 ≤ b`. Let me investigate the omega error more carefully:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_inj.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat Finset Erdos728

-- The injection needs j + 1 < b where j < D and b = max (D + 1) (log p (2 * m) + 1)
example (j D : ℕ) (hj : j < D) (b : ℕ) (hb : b = max (D + 1) (log 2 (2 * 3) + 1)) :
    j + 1 < b := by
  omega

-- The omega issue was about y, not about j+1 < b. Let me re-read the error.
-- The error said j+1 < b was fine but the overall Ico membership wasn't.
-- Actually the error mentions variables e, f (y, x from injectivity). 
-- The injectivity proof x _ y _ hxy seems OK with omega on x+1 = y+1 → x = y.
-- Wait, maybe the issue was in the "maps into" part, not injectivity.

-- Let me re-check. The error was:
-- omega could not prove the goal:
--  g ≥ 0, f ≥ 0, e ≥ 0, e - f ≥ 1, d ≥ 0, c ≥ 1, a ≥ 0, a - g ≥ 0
-- This looks like the injectivity proof, where x and y from coe need to satisfy x+1 = y+1 → x = y.
-- But omega should handle that... The constraint says e - f ≥ 1 which means y - x ≥ 1 (y ≠ x).
-- And d = (fun j => j+1) y = y + 1. But there's no constraint forcing x+1 = y+1.
-- Hmm, maybe the issue is that hxy isn't properly being used.

-- Actually wait, `intros x _ y _ hxy; omega` should work for injectivity on ℕ.
-- Let me check: the issue might be that card_le_card_of_injOn wants InjOn on coe...
EOF
lake env lean /tmp/test_inj.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_count_high7.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat Finset Erdos728

set_option linter.unusedVariables false

lemma count_high_le_valuation' {p : ℕ} (hp : p.Prime) (m D : ℕ) :
    count_high_digits p m D ≤ padicValNat p ((2 * m).choose m) := by
  by_cases hm : m = 0
  · subst hm
    unfold count_high_digits high_digits_finset is_high_digit digit
    simp only [Nat.zero_div, Nat.zero_mod]
    rw [Finset.filter_false_of_mem]
    · simp
    · intro i _; simp only [not_le]; have := hp.two_le; omega
  have hm_pos : m ≥ 1 := Nat.pos_of_ne_zero hm
  let b := max (D + 1) (log p (2 * m) + 1)
  have hb : log p (2 * m) < b := by simp [b]; omega
  have hb_gt_D : D < b := by simp [b]; omega
  have hle : m ≤ 2 * m := Nat.le_mul_of_pos_left m (by omega)
  have h2m_sub : 2 * m - m = m := by omega
  rw [← Nat.factorization_def _ hp, Nat.factorization_choose hp hle hb, h2m_sub]
  apply card_le_card_of_injOn (fun j => j + 1)
  · intro j hj
    rw [mem_coe] at hj
    simp only [high_digits_finset, mem_filter, mem_range] at hj
    rw [mem_coe, mem_filter, mem_Ico]
    exact ⟨⟨by omega, by omega⟩, high_digit_forces_carry p m j hj.2⟩
  · intro x hx y hy hxy
    rw [mem_coe] at hx hy
    omega
EOF
lake env lean /tmp/test_count_high7.lean 2>&1
```
There are multiple errors. The issue with "No goals to be solved" suggests that some earlier tactic already solved the goal. Let me debug step by step:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_count_high8.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat Finset Erdos728

set_option linter.unusedVariables false

-- Check what rw does to factorization_def and factorization_choose
example {p : ℕ} (hp : p.Prime) (m D : ℕ) (hm : m ≥ 1) :
    count_high_digits p m D ≤ padicValNat p ((2 * m).choose m) := by
  let b := max (D + 1) (log p (2 * m) + 1)
  have hb : log p (2 * m) < b := by simp [b]; omega
  have hle : m ≤ 2 * m := Nat.le_mul_of_pos_left m (by omega)
  have h2m_sub : 2 * m - m = m := by omega
  -- Let's see what happens step by step
  have key : padicValNat p ((2 * m).choose m) = 
      ((Ico 1 b).filter (fun i => p ^ i ≤ m % p ^ i + m % p ^ i)).card := by
    rw [← Nat.factorization_def _ hp, Nat.factorization_choose hp hle hb, h2m_sub]
  rw [key]
  sorry
EOF
lake env lean /tmp/test_count_high8.lean 2>&1
```
The `rw [← Nat.factorization_def _ hp, ...]` closes the goal somehow, or the chain is wrong. Let me check individually:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_count_high9.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat Finset Erdos728

-- Check factorization_def
#check @Nat.factorization_def
-- factorization_def : ∀ {n : ℕ} (p : ℕ), Nat.Prime p → (Nat.factorization n) p = padicValNat p n
-- So padicValNat p n = (Nat.factorization n) p
-- And ← factorization_def replaces padicValNat with factorization

example {p : ℕ} (hp : p.Prime) (m : ℕ) (hm : m ≥ 1) :
    padicValNat p ((2 * m).choose m) = 
    ((2 * m).choose m).factorization p := by
  rw [← Nat.factorization_def _ hp]
EOF
lake env lean /tmp/test_count_high9.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_count_high10.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat Finset Erdos728

set_option linter.unusedVariables false

example {p : ℕ} (hp : p.Prime) (m D : ℕ) (hm : m ≥ 1) :
    count_high_digits p m D ≤ padicValNat p ((2 * m).choose m) := by
  let b := max (D + 1) (log p (2 * m) + 1)
  have hb : log p (2 * m) < b := by simp [b]; omega
  have hle : m ≤ 2 * m := Nat.le_mul_of_pos_left m (by omega)
  have h2m_sub : 2 * m - m = m := by omega
  -- Rewrite padicValNat to factorization
  rw [← Nat.factorization_def _ hp]
  -- Now goal: count_high_digits ≤ ((2*m).choose m).factorization p
  rw [Nat.factorization_choose hp hle hb]
  -- Now goal: count_high_digits ≤ card of filter
  rw [h2m_sub]
  -- Now: count_high_digits p m D ≤ #{i ∈ Ico 1 b : p^i ≤ m%p^i + m%p^i}
  sorry
EOF
lake env lean /tmp/test_count_high10.lean 2>&1
```
Hmm, the `simp [b]; omega` resolves the entire goal? That's strange. Let me check:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_count_high11.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat Finset Erdos728

set_option linter.unusedVariables false

example {p : ℕ} (hp : p.Prime) (m D : ℕ) (hm : m ≥ 1) :
    count_high_digits p m D ≤ padicValNat p ((2 * m).choose m) := by
  let b := max (D + 1) (log p (2 * m) + 1)
  have hb : log p (2 * m) < b := by
    show log p (2 * m) < max (D + 1) (log p (2 * m) + 1)
    omega
  sorry
EOF
lake env lean /tmp/test_count_high11.lean 2>&1
```
Good. Now let me continue:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_count_high12.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat Finset Erdos728

set_option linter.unusedVariables false

example {p : ℕ} (hp : p.Prime) (m D : ℕ) (hm : m ≥ 1) :
    count_high_digits p m D ≤ padicValNat p ((2 * m).choose m) := by
  let b := max (D + 1) (log p (2 * m) + 1)
  have hb : log p (2 * m) < b := by
    show log p (2 * m) < max (D + 1) (log p (2 * m) + 1); omega
  have hle : m ≤ 2 * m := Nat.le_mul_of_pos_left m (by omega)
  have h2m_sub : 2 * m - m = m := by omega
  have hb_gt_D : D + 1 ≤ b := by show D + 1 ≤ max (D + 1) (log p (2 * m) + 1); omega
  rw [← Nat.factorization_def _ hp, Nat.factorization_choose hp hle hb, h2m_sub]
  apply card_le_card_of_injOn (fun j => j + 1)
  · intro j hj
    rw [mem_coe] at hj
    rw [high_digits_finset, mem_filter, mem_range] at hj
    rw [mem_coe, mem_filter, mem_Ico]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact Nat.succ_le_succ (Nat.zero_le j)
    · exact Nat.lt_of_lt_of_le (Nat.succ_lt_succ hj.1) hb_gt_D
    · exact high_digit_forces_carry p m j hj.2
  · intro x hx y hy hxy
    rw [mem_coe] at hx hy
    exact Nat.succ_injective hxy
EOF
lake env lean /tmp/test_count_high12.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_count_high13.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat Finset Erdos728

set_option linter.unusedVariables false

-- Check is_high_digit decidability
#check @instDecidableIsHighDigit -- doesn't exist?

-- is_high_digit p m i = digit p m i ≥ (p + 1) / 2, which is decidable
instance (p m i : ℕ) : Decidable (is_high_digit p m i) :=
  inferInstanceAs (Decidable ((p + 1) / 2 ≤ digit p m i))
EOF
lake env lean /tmp/test_count_high13.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && grep "Decidable\|decidable\|instance" Erdos/Digits.lean
```
So `is_high_digit` doesn't have a `Decidable` instance. Let me check `count_high_digits` — it uses `Finset.filter` on `is_high_digit`, which requires decidability. Let me check:
```bash
$ cd /home/jarred/code/erdos-728b && grep "noncomputable" Erdos/Digits.lean
```
Ah, it's `noncomputable` and uses `open Classical` at the top. So the decidability comes from classical logic. I need to use `Classical.dec` or just open Classical:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_count_high14.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat Finset Erdos728 Classical

set_option linter.unusedVariables false

example {p : ℕ} (hp : p.Prime) (m D : ℕ) (hm : m ≥ 1) :
    count_high_digits p m D ≤ padicValNat p ((2 * m).choose m) := by
  let b := max (D + 1) (log p (2 * m) + 1)
  have hb : log p (2 * m) < b := by
    show log p (2 * m) < max (D + 1) (log p (2 * m) + 1); omega
  have hle : m ≤ 2 * m := Nat.le_mul_of_pos_left m (by omega)
  have h2m_sub : 2 * m - m = m := by omega
  have hb_gt_D : D + 1 ≤ b := by show D + 1 ≤ max (D + 1) (log p (2 * m) + 1); omega
  rw [← Nat.factorization_def _ hp, Nat.factorization_choose hp hle hb, h2m_sub]
  apply card_le_card_of_injOn (fun j => j + 1)
  · intro j hj
    rw [mem_coe] at hj
    rw [high_digits_finset, mem_filter, mem_range] at hj
    rw [mem_coe, mem_filter, mem_Ico]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact Nat.succ_le_succ (Nat.zero_le j)
    · exact Nat.lt_of_lt_of_le (Nat.succ_lt_succ hj.1) hb_gt_D
    · exact high_digit_forces_carry p m j hj.2
  · intro x hx y hy hxy
    rw [mem_coe] at hx hy
    exact Nat.succ_injective hxy
EOF
lake env lean /tmp/test_count_high14.lean 2>&1
```
Excellent! `count_high_le_valuation` compiles without sorry! Now let me try `valuation_gt_implies_cascade`. This is the harder one. Let me think about whether I can close it or if I should leave a well-annotated sorry.

The key argument: if `v_p(C(m+k,k)) > D/6`, then `cascade_length k D m ≥ D/6 - log p k`.

This is the contrapositive of: `cascade_length k D m < D/6 - log p k → v_p(C(m+k,k)) ≤ D/6`.

The proof of the forward direction requires connecting `padicValNat` to carries via Kummer's theorem, then using `carry_propagate` to bound the total number of carries.

Let me check what's available for Kummer's theorem in the codebase:
```bash
$ cd /home/jarred/code/erdos-728b && grep -rn "Kummer\|kummer\|factorization_choose" Erdos/ --include="*.lean" | head -10
```

```bash
$ cd /home/jarred/code/erdos-728b && read -r -d '' _ <<'EOF'
Let me check Nat.factorization_choose' signature
EOF
cat > /tmp/test_fc2.lean << 'EOF'
import Mathlib.Data.Nat.Choose.Factorization
#check @Nat.factorization_choose'
#print Nat.factorization_choose'
EOF
lake env lean /tmp/test_fc2.lean 2>&1 | head -15
```
So `Nat.factorization_choose'` says:
```
v_p(C(n+k, k)) = #{i ∈ Ico 1 b : p^i ≤ k%p^i + n%p^i}
```
where `b > log p (n+k)`. This is essentially Kummer's theorem: `v_p = number of carry positions`.

Now, the carry condition at position `i` is: `p^i ≤ k % p^i + m % p^i`. This is exactly `carry_cond p k m i`.

So `v_p(C(m+k,k)) = #{i ∈ Ico 1 b : carry_cond p k m i}` for any `b > log p (m+k)`.

Using this, I can prove `valuation_gt_implies_cascade`. Let me outline the proof:

1. Express `v_p = #{i ∈ Ico 1 b : carry_cond p k m i}` using `factorization_choose'`.
2. If `v_p > D/6`, then there are > D/6 carry positions in `Ico 1 b`.
3. By `carry_propagate` (contrapositive), if `carry_cond p k m (j+1)` and `j > s`, then `digit p m j = p-1` and `carry_cond p k m j`.
4. By repeated application: if there's a carry at position `i > s+1`, then digits s+1, ..., i-1 are all p-1.
5. The maximum position with a carry determines the cascade length.
6. If > D/6 carries exist, the cascade must extend far enough.

Actually, let me think about this more carefully. The total number of carries is:
- At most `s+1` carries at positions 1..s+1 (from the first `s+1` digit positions)
- Carries at positions s+2, s+3, ... form a cascade that requires consecutive p-1 digits starting at position s+1.

So the total carries ≤ (s+1) + (cascade length starting at s+1).

If the cascade length is L (up to D positions), then the cascade covers positions s+1 through s+L. Carries at positions s+2 through s+L+1 require the cascade to be at least that long. And the cascade dies at position s+L+1 (if L < D-s-1), meaning no carry at position s+L+2 onwards.

So total carries ≤ (s+1) + L (where L is the cascade within D positions).

Wait, but carries at position s+L+2 and beyond could theoretically be non-zero if the digits beyond D restart a new cascade. But by `carry_propagate`, a carry at position i > s+1 requires a carry at position i-1. So if there's no carry at position s+L+2 (because the cascade died), there's no carry at any position > s+L+1.

But the cascade dying means `digit p m (s+1+L) ≠ p-1` (within the first D digits). However, for `m` with more than D digits, the cascade WITHIN D digits might end, but the digit at position `s+1+L` when considered as a digit of the full number `m` might differ from `digit p (m % p^D) (s+1+L)` only if `s+1+L ≥ D`. 

Wait, `cascade_length` is defined to look at positions `s+1, s+2, ..., D-1`. If the cascade reaches the boundary (L = D - s - 1), then ALL positions s+1..D-1 are p-1. The carry might continue beyond D. In this case:
- cascade_length = D - s - 1
- D/6 - s ≤ D - s - 1 iff D/6 ≤ D - 1, which is true for D ≥ 1.

So if the cascade fills all D positions, `cascade_length ≥ D/6 - s` is automatically satisfied.

If the cascade DOESN'T fill all D positions (L < D - s - 1), then `digit p m (s+1+L) ≠ p-1` (where `s+1+L < D`). By `carry_propagate`, the carry at position `s+1+L+1` requires `digit p m (s+1+L) = p-1`, contradiction. So `¬carry_cond p k m (s+1+L+1)`. By induction (repeated carry_propagate), no carry at any position ≥ s+L+2.

Total carries = (carries at 1..s+1) + (carries at s+2..s+L+1) ≤ (s+1) + L.

So `v_p ≤ (s+1) + L`. If `v_p > D/6`, then `(s+1) + L > D/6`, so `L > D/6 - s - 1`, so `L ≥ D/6 - s`.

This is clean but requires connecting `factorization_choose'` to `carry_propagate`. Let me try to formalize this:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_cascade.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat Finset Erdos728

set_option linter.unusedVariables false
set_option maxHeartbeats 400000

-- First, let me prove a key helper: if carry_cond at position j+1 (with j > s),
-- then digit p m j = p-1.
-- This is already proved in carry_propagate, but let me extract the part I need.

-- Main lemma: v_p(C(m+k,k)) ≤ (s+1) + cascade_length k D m for arbitrary m
-- when D is large enough.
-- The key observation: carries beyond position s + 1 + cascade_length must be 0.

-- Step 1: If cascade_length = L < D - s - 1, then ¬carry_cond at position s+L+2.
-- Step 2: By carry_propagate, ¬carry_cond at all positions > s+L+1.
-- Step 3: Total carries ≤ (s+1) + L.

-- Step 1 helper: cascade dies → no carry beyond
-- If digit p m (s+1+L) ≠ p-1, then ¬carry_cond p k m (s+1+L+1+1)
-- Actually, carry_propagate says: carry_cond at i AND i > s+1 → digit at i-1 = p-1.
-- Contrapositive: digit at i-1 ≠ p-1 → ¬carry_cond at i (when i > s+1).

-- But carry_propagate requires k ≥ 1. Let me check.

-- Let me try a cleaner approach: bound total carries directly.

-- For each carry position i in Ico 1 b with i > s+1, carry_propagate gives
-- digit at i-1 = p-1 and carry at i-1. So by induction down from i to s+2,
-- digits s+1, s+2, ..., i-2 are all p-1.

-- The maximum carry position beyond s+1 is at most s+1+L+1 (one past the cascade).
-- Wait: the cascade length L means digits s+1, ..., s+L are p-1, and digit s+1+L ≠ p-1
-- (or L = D - s - 1). A carry at position s+1+L+1 would require digit s+L = p-1 via
-- carry_propagate. But digit s+L ≠ p-1 (when L < D-s-1), contradiction.

-- Actually wait, carry_propagate says carry at position i > s+1 implies:
-- 1) digit at i-1 = p-1
-- 2) carry at i-1
-- It does NOT directly say ¬carry at i if digit ≠ p-1. It says the contrapositive.

-- Let me check carry_propagate more carefully:
-- carry_propagate (hp) (m i) (hi : i > log p k + 1) (h_carry : carry_cond p k m i) (hk : k ≥ 1) :
--     digit p m (i - 1) = p - 1 ∧ carry_cond p k m (i - 1)

-- So contrapositive: for i > s+1, if digit at i-1 ≠ p-1 OR ¬carry at i-1, then ¬carry at i.

-- I'll prove: for i ≥ s+L+2 (where L = cascade_length, and L < D-s-1), ¬carry_cond at i.
-- By strong induction: 
--   Base: at position s+L+2 > s+1. If carry at s+L+2, then digit at s+L+1 = p-1.
--         But s+L+1 = s+1+L, and digit at s+1+L ≠ p-1 (cascade ended there). Contradiction.
--   Step: at position i > s+L+2 > s+1. If carry at i, then carry at i-1 (by carry_propagate).
--         By IH, ¬carry at i-1. Contradiction.

-- Actually the induction is DOWN from i, not up. Let me use carry_propagate directly:
-- carry at i > s+1 → carry at i-1 (and digit at i-1 = p-1).
-- carry at i-1 > s+1 → carry at i-2 (and digit at i-2 = p-1).
-- ...continuing down...
-- carry at s+L+2 → digit at s+L+1 = p-1. But cascade ended at s+L, so digit at s+1+L ≠ p-1.
-- Contradiction.

-- So: for ANY i > s+L+1 (with i > s+1), carry at i is impossible when L < D-s-1.

-- But this requires showing that the cascade ending means digit at s+1+L ≠ p-1.
-- cascade_length k D m is defined as:
--   (List.range (D-(s+1))).takeWhile (fun j => digit p m (s+1+j) = p-1) |>.length
-- So if L = cascade_length < D-s-1, then:
--   the (L+1)-th element of the range was NOT taken, meaning digit at s+1+L ≠ p-1.
-- Wait: takeWhile stops at the first element NOT satisfying the predicate.
-- So length L means: digits at s+1, s+2, ..., s+L are p-1, and digit at s+1+L is NOT p-1
-- (assuming L < D-s-1, so s+1+L is in range).

-- Actually: List.range (D-(s+1)) = [0, 1, ..., D-s-2].
-- takeWhile (fun j => digit at s+1+j = p-1) takes j=0,1,...,L-1 (all satisfying),
-- and j=L does NOT satisfy. So:
-- digit at s+1+0 = p-1, ..., digit at s+1+(L-1) = p-1, digit at s+1+L ≠ p-1.
-- i.e., digit at s+1, s+2, ..., s+L are p-1, and digit at s+1+L is NOT p-1.

-- Perfect. So if L = cascade_length < D-s-1, then digit at s+1+L ≠ p-1.

-- Now I can proceed.

-- Let me check: does List.takeWhile have a lemma about elements after the prefix?
-- Something like: if takeWhile has length L and L < list.length, then the L-th element
-- doesn't satisfy the predicate.

#check @List.not_of_length_takeWhile_lt
EOF
lake env lean /tmp/test_cascade.lean 2>&1 | tail -5
```

```bash
$ cd /home/jarred/code/erdos-728b && grep -rn "takeWhile" .lake/packages/mathlib/Mathlib/ --include="*.lean" -l | head -5
```

```bash
$ cd /home/jarred/code/erdos-728b && grep -n "takeWhile.*length\|length.*takeWhile\|get.*takeWhile\|takeWhile.*get\|takeWhile.*not\|not.*takeWhile" .lake/packages/mathlib/Mathlib/Data/List/TakeWhile.lean | head -20
```

```bash
$ cd /home/jarred/code/erdos-728b && grep -rn "takeWhile" ~/.elan/toolchains/leanprover-lean4-v4.27.0/lib/lean4/library/ --include="*.lean" | grep -i "length\|get\|not" | head -20
```

```bash
$ cd /home/jarred/code/erdos-728b && find ~/.elan/toolchains/leanprover-lean4-v4.27.0/ -name "*.olean" -path "*/List*" | head -5
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_tw2.lean << 'EOF'
import Mathlib

-- Search for lemmas about takeWhile and not-predicate at the boundary
#check List.takeWhile_length_lt_iff
#check List.getElem_takeWhile
#check List.length_takeWhile_lt
EOF
lake env lean /tmp/test_tw2.lean 2>&1 | head -10
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_tw3.lean << 'EOF'
import Mathlib.Data.List.TakeWhile

-- Search for relevant lemmas
example : True := by
  #check @List.takeWhile_append_of_pos
  trivial
EOF
lake env lean /tmp/test_tw3.lean 2>&1 | head -5
```

```bash
$ cd /home/jarred/code/erdos-728b && grep "theorem\|lemma" .lake/packages/mathlib/Mathlib/Data/List/TakeWhile.lean | head -20
```
I need to prove: if `takeWhile` on a list has length `L < list.length`, then the element at position `L` doesn't satisfy the predicate. Let me prove this directly:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_tw4.lean << 'EOF'
import Mathlib.Data.List.TakeWhile

-- If takeWhile has length L < list length, the L-th element doesn't satisfy p
lemma not_of_takeWhile_length {α : Type*} {p : α → Bool} {l : List α}
    (h : l.takeWhile p |>.length < l.length) :
    ¬(p (l.get ⟨l.takeWhile p |>.length, h⟩) = true) := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
    simp only [List.takeWhile_cons] at h ⊢
    split at h ⊢
    case isTrue hp =>
      simp only [List.length_cons, Nat.succ_lt_succ_iff] at h
      simp only [List.length_cons, List.get_cons_succ]
      exact ih h
    case isFalse hn =>
      simp only [List.length_nil] at h ⊢
      simp only [List.get_cons_zero]
      exact hn
EOF
lake env lean /tmp/test_tw4.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_tw4.lean << 'EOF'
import Mathlib.Data.List.TakeWhile

-- If takeWhile has length L < list length, the L-th element doesn't satisfy p
lemma not_of_takeWhile_length {α : Type*} {p : α → Bool} {l : List α}
    (h : (l.takeWhile p).length < l.length) :
    p (l.get ⟨(l.takeWhile p).length, h⟩) = false := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
    simp only [List.takeWhile_cons] at h ⊢
    split at h ⊢
    case isTrue hp =>
      simp only [List.length_cons, Nat.succ_lt_succ_iff] at h
      simp only [List.length_cons, List.get_cons_succ]
      exact ih h
    case isFalse hn =>
      simp only [List.length_nil] at h ⊢
      simp only [List.get_cons_zero]
      exact Bool.eq_false_iff.mpr hn
EOF
lake env lean /tmp/test_tw4.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_tw4.lean << 'EOF'
import Mathlib.Data.List.TakeWhile

lemma not_of_takeWhile_length {α : Type*} {p : α → Bool} {l : List α}
    (h : (l.takeWhile p).length < l.length) :
    p (l.get ⟨(l.takeWhile p).length, h⟩) = false := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
    simp only [List.takeWhile_cons]
    split
    case isTrue hp =>
      simp only [List.length_cons, Nat.succ_lt_succ_iff] at h
      simp only [List.length_cons, List.get_cons_succ]
      exact ih h
    case isFalse hn =>
      simp only [List.length_nil, List.get_cons_zero]
      exact Bool.eq_false_iff.mpr hn
EOF
lake env lean /tmp/test_tw4.lean 2>&1
```
The issue is that `split` on the goal changes the takeWhile, but `h` still has the original form. Let me restructure:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_tw4.lean << 'EOF'
import Mathlib.Data.List.TakeWhile

-- More direct approach
lemma not_of_takeWhile_length {α : Type*} {p : α → Bool} :
    ∀ {l : List α} (h : (l.takeWhile p).length < l.length),
    p (l.get ⟨(l.takeWhile p).length, h⟩) = false := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons a t ih =>
    intro h
    by_cases ha : p a = true
    · -- p a = true, so takeWhile (a::t) p = a :: takeWhile t p
      simp only [List.takeWhile_cons, ha, ite_true, List.length_cons, Nat.succ_lt_succ_iff] at h ⊢
      exact ih h
    · -- p a = false, so takeWhile = [], length = 0
      simp only [List.takeWhile_cons, Bool.eq_false_iff.mpr (by simpa using ha), ite_false,
        List.length_nil, List.get_cons_zero] at h ⊢
      simpa using ha
EOF
lake env lean /tmp/test_tw4.lean 2>&1
```
OK, it compiles with warnings. Good enough. Now this approach is getting very involved. Let me step back and think about whether there's a simpler way to prove `valuation_gt_implies_cascade`.

Given the complexity, let me take a pragmatic approach: I'll leave `valuation_gt_implies_cascade` with a well-annotated sorry and prove everything else. The main lemma `bad_residue_sets` will compile with sorry warnings but will have substantial progress — I'll close everything except the carry-cascade connection.

Actually, wait. Let me check if `valuation_le_cascade` (which is sorry'd at line 123) can be applied to `m % p^D` to get the bound we need:

The approach:
1. `v_p(C(m+k,k)) > D/6` (given)
2. We need: `cascade_length k D m ≥ D/6 - log p k`
3. `cascade_length k D m = cascade_length k D (m % p^D)` (digit invariance, proved)
4. By `valuation_le_cascade` applied to `m' = m % p^D < p^D`: `v_p(C(m'+k,k)) ≤ (s+1) + cascade_length k D m'`

But step 4 gives a bound on `v_p(C(m'+k,k))`, not `v_p(C(m+k,k))`. These are different!

Unless I can show `v_p(C(m+k,k)) ≤ v_p(C(m'+k,k))` or `v_p(C(m+k,k)) = v_p(C(m'+k,k))` ... which isn't true in general.

Actually, the contrapositive approach works differently. We don't need `v_p(C(m+k,k)) ≤ (s+1) + L`. We need the CONTRA-positive: `L < D/6 - s → v_p ≤ D/6`.

But this requires bounding `v_p(C(m+k,k))` for ARBITRARY m, which `valuation_le_cascade` can't do (it requires `m < p^D`).

OK, I think the cleanest path is to leave a well-annotated sorry for `valuation_gt_implies_cascade` and close the rest of `bad_residue_sets`. This still makes substantial progress. Let me now write the actual code to put into the file.
```bash
$ cd /home/jarred/code/erdos-728b && tm update erdos728b-hga --status "Writing the proof into Lemma3Counting.lean - closing count_high_le_valuation fully, leaving cascade helper sorry'd"
```
Let me re-read the section where I need to insert the code:
🛠️ **Executing tool: read**
Now let me write the replacement. I'll add the helper lemmas right before `bad_residue_sets` and replace its sorry with the proof:
🛠️ **Executing tool: edit**
Now let me compile:
```bash
$ cd /home/jarred/code/erdos-728b && lake build 2>&1 | tail -30
```
There's an error! The omega failure is in the `count_high_le_valuation` proof — the `by omega` for `j + 1 < b`. Let me check:
```bash
$ cd /home/jarred/code/erdos-728b && lake build 2>&1 | grep "error:"
```

```bash
$ cd /home/jarred/code/erdos-728b && lake build 2>&1 | grep -A5 "487:"
```
The `DecidablePred` issue. I need to use `Classical` or add a decidable instance. The file uses `open Classical` in the `Digits.lean` but not here. Let me check:
```bash
$ cd /home/jarred/code/erdos-728b && grep "Classical" Erdos/Lemma3Counting.lean
```
It doesn't open Classical. I need to add it or use `open Classical in` locally. Let me also fix the omega issue. Let me find line 487:
🛠️ **Executing tool: read**
Line 487 is `rw [high_digits_finset, mem_filter, mem_range] at hj` — the DecidablePred issue. And line 489 has the omega issues in `⟨by omega, by omega⟩`.

The DecidablePred issue: `high_digits_finset` uses `filter` on `is_high_digit`, which uses Classical decidability. When I `rw [high_digits_finset]` in a non-Classical context, Lean can't synthesize the decidability.

Let me fix by adding `open Classical in` to the lemma:
🛠️ **Executing tool: edit**

```bash
$ cd /home/jarred/code/erdos-728b && lake build 2>&1 | tail -20
```
Build succeeded! Let me check the sorry warnings to make sure they're as expected:
```bash
$ cd /home/jarred/code/erdos-728b && lake build 2>&1 | grep "sorry"
```
Let me verify which sorry is from `valuation_gt_implies_cascade` and which are pre-existing. Let me check the lines:
```bash
$ cd /home/jarred/code/erdos-728b && sed -n '454p;455p;456p;457p' Erdos/Lemma3Counting.lean
```
Good, line 456 is `valuation_gt_implies_cascade`. Let me check the other new sorry at line 525 and the others:
```bash
$ cd /home/jarred/code/erdos-728b && sed -n '525p' Erdos/Lemma3Counting.lean
```
Lines 525, 566, 583 are pre-existing sorrys (count_bad_interval, exists_m_for_fixed_k, threshold_subpolynomial). Lines 54, 122, 125, 319 are also pre-existing.

The only NEW sorry I introduced is `valuation_gt_implies_cascade` at line 456. The `bad_residue_sets` lemma itself is now proved (modulo this helper sorry).

Let me now try to close `valuation_gt_implies_cascade` as well. This is the key mathematical content I need to formalize.
```bash
$ cd /home/jarred/code/erdos-728b && tm update erdos728b-hga --status "bad_residue_sets proved modulo 1 helper sorry (valuation_gt_implies_cascade). Attempting to close it."
```
Let me now formalize `valuation_gt_implies_cascade`. The key idea is:

1. Express `v_p(C(m+k,k))` using `factorization_choose'`: `v_p = #{i ∈ Ico 1 b : carry_cond p k m i}`.
2. Show that if `cascade_length < D/6 - s`, then carry_cond is false for all `i > s+1+cascade_length`.
3. Therefore the set of carry positions is contained in `Ico 1 (s+2+cascade_length)`, so its card ≤ s+1+cascade_length.
4. Thus `v_p ≤ s+1+cascade_length ≤ D/6` (since cascade_length < D/6 - s).

Let me implement this step by step:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_vtc.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat Finset Erdos728

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

-- Key helper: if cascade_length = L < D - s - 1, then digit at s+1+L ≠ p-1
-- (the cascade dies because the predicate is false at position L in the takeWhile)
private lemma cascade_digit_neq {p : ℕ} (k D m : ℕ)
    (L : ℕ) (hL_eq : cascade_length (p := p) k D m = L)
    (hL_lt : L < D - (log p k + 1)) :
    digit p m (log p k + 1 + L) ≠ p - 1 := by
  -- cascade_length = length of takeWhile on List.range (D - (s+1))
  -- If L < D - (s+1), the takeWhile stopped because the L-th element didn't satisfy the pred
  unfold cascade_length at hL_eq
  simp only at hL_eq
  -- The list is List.range (D - (log p k + 1))
  -- takeWhile stopped at index L, so (decide (digit p m (log p k + 1 + L) = p - 1)) = false
  have hL_in_range : L < (List.range (D - (log p k + 1))).length := by
    simp [List.length_range]; exact hL_lt
  -- We need that the L-th element of the original list doesn't satisfy the predicate.
  -- The original list is List.range (D - (s+1)), so element L is just L.
  -- The predicate is (fun i => decide (digit p m (s + 1 + i) = p - 1))
  -- takeWhile has length L < list.length, so the element at index L in the list
  -- does NOT satisfy the predicate.
  have h_range_get : (List.range (D - (log p k + 1)))[L]'hL_in_range = L := by
    simp [List.getElem_range]
  -- By List.takeWhile properties: if takeWhile has length L < list.length,
  -- then the L-th element doesn't satisfy the predicate.
  -- Let me prove this directly by contradiction.
  intro h_eq
  -- If digit at s+1+L = p-1, then the predicate IS satisfied at index L,
  -- so takeWhile should have taken at least L+1 elements.
  have h_pred_true : (decide (digit p m (log p k + 1 + L) = p - 1)) = true := by
    exact decide_eq_true h_eq
  -- This means takeWhile should be at least L+1 elements
  -- because all elements 0..L satisfy the predicate.
  -- Elements 0..L-1 satisfy (from hL_eq, they were taken).
  -- Element L satisfies (from h_pred_true).
  -- So takeWhile length ≥ L + 1.
  -- But hL_eq says it's exactly L. Contradiction.
  -- We need: if all elements 0..L satisfy the predicate, then takeWhile ≥ L+1.
  -- Let's use List.takeWhile_cons and induction.
  sorry
EOF
lake env lean /tmp/test_vtc.lean 2>&1 | tail -5
```
OK, I can compile the structure. Now let me prove the sorry about takeWhile. This is a basic fact about takeWhile — if the L-th element satisfies the predicate and L < list length, then takeWhile length ≥ L+1. Actually, let me use a different approach: prove the contrapositive of what I need:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_tw_stop.lean << 'EOF'
import Mathlib.Data.List.TakeWhile

-- If takeWhile stops at position L (length = L and L < list.length),
-- the L-th element doesn't satisfy the predicate.
-- Proved by induction: takeWhile on (a::t) with p a = true has length 1 + takeWhile t,
-- and with p a = false has length 0.

-- Cleaner: the element right after takeWhile in the original list is NOT in takeWhile,
-- hence doesn't satisfy the predicate.

-- Actually, a clean approach: show that takeWhile doesn't contain the L-th element,
-- then show that if the L-th element satisfies p, it would be in takeWhile.

-- Let me try: l.takeWhile p ++ l.dropWhile p = l, and 
-- (l.dropWhile p).head satisfies ¬p (for non-empty dropWhile).

-- dropWhile_get_zero_not
-- List.dropWhile_get_zero_not : ¬p (l.dropWhile p)[0]

-- And takeWhile ++ dropWhile = l
-- So l[takeWhile.length] = dropWhile[0]

-- This is exactly what we need!

#check @List.dropWhile_get_zero_not
#check @List.takeWhile_append_dropWhile
EOF
lake env lean /tmp/test_tw_stop.lean 2>&1
```
`List.dropWhile_get_zero_not` says: the first element of `dropWhile` doesn't satisfy `p`.
`List.takeWhile_append_dropWhile` says: `takeWhile ++ dropWhile = l`.

So `l[takeWhile.length] = dropWhile[0]`, and `¬p(dropWhile[0])`. This gives me what I need!
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_tw_stop2.lean << 'EOF'
import Mathlib.Data.List.TakeWhile

-- Key lemma: if takeWhile has length L < list.length, the L-th element doesn't satisfy p
lemma not_pred_at_takeWhile_length {α : Type*} {p : α → Bool} {l : List α}
    (h : (l.takeWhile p).length < l.length) :
    ¬(p (l[l.takeWhile p |>.length]'h) = true) := by
  -- dropWhile is nonempty since takeWhile.length < l.length
  have h_drop_pos : 0 < (l.dropWhile p).length := by
    have := List.takeWhile_append_dropWhile (p := p) (l := l)
    have h1 : (l.takeWhile p).length + (l.dropWhile p).length = l.length := by
      rw [← List.length_append]; congr 1; exact List.takeWhile_append_dropWhile
    omega
  have h_drop := List.dropWhile_get_zero_not p l h_drop_pos
  -- l[takeWhile.length] = dropWhile[0]
  have h_eq : l[l.takeWhile p |>.length]'h = (l.dropWhile p).get ⟨0, h_drop_pos⟩ := by
    have := List.takeWhile_append_dropWhile (p := p) (l := l)
    rw [← this]
    simp [List.getElem_append_right (by omega)]
  rw [h_eq]
  exact h_drop
EOF
lake env lean /tmp/test_tw_stop2.lean 2>&1
```
The rewrite is tricky because of dependent types. Let me use a different approach:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_tw_stop3.lean << 'EOF'
import Mathlib.Data.List.TakeWhile

-- Key: if takeWhile length = L < list length, then l[L] doesn't satisfy p
-- Use: l = takeWhile ++ dropWhile, and dropWhile.head doesn't satisfy p
lemma not_pred_at_takeWhile_length {α : Type*} {p : α → Bool} {l : List α}
    (h : (l.takeWhile p).length < l.length) :
    ¬(p (l[l.takeWhile p |>.length]'h) = true) := by
  have h_drop_pos : 0 < (l.dropWhile p).length := by
    have h1 : (l.takeWhile p).length + (l.dropWhile p).length = l.length := by
      rw [← List.length_append]; congr 1; exact List.takeWhile_append_dropWhile
    omega
  -- l[takeWhile.length] = (takeWhile ++ dropWhile)[takeWhile.length] = dropWhile[0]
  have key : l[l.takeWhile p |>.length]'h =
      (l.dropWhile p)[0]'h_drop_pos := by
    conv_lhs => rw [← List.takeWhile_append_dropWhile (p := p) (l := l)]
    rw [List.getElem_append_right (by omega : ¬ _ < _)]
    simp
  rw [key]
  exact List.dropWhile_get_zero_not p l h_drop_pos
EOF
lake env lean /tmp/test_tw_stop3.lean 2>&1
```
Two issues. Let me fix them:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_tw_stop4.lean << 'EOF'
import Mathlib.Data.List.TakeWhile

#check @List.getElem_append
-- Maybe I should just do this by induction
lemma not_pred_at_takeWhile_length {α : Type*} {p : α → Bool} :
    ∀ (l : List α) (h : (l.takeWhile p).length < l.length),
    p l[(l.takeWhile p).length] = false := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons a t ih =>
    intro h
    simp only [List.takeWhile_cons]
    split
    case isTrue ha =>
      simp only [List.length_cons, Nat.succ_lt_succ_iff] at h
      simp only [List.length_cons, List.getElem_cons_succ]
      exact ih t h
    case isFalse hn =>
      simp only [List.length_nil, List.getElem_cons_zero]
      exact Bool.eq_false_iff.mpr hn
EOF
lake env lean /tmp/test_tw_stop4.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_tw_stop5.lean << 'EOF'
import Mathlib.Data.List.TakeWhile

lemma not_pred_at_takeWhile_length {α : Type*} {p : α → Bool} :
    ∀ (l : List α) (h : (l.takeWhile p).length < l.length),
    p l[(l.takeWhile p).length] = false := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons a t ih =>
    intro h
    simp only [List.takeWhile_cons]
    split
    case isTrue ha =>
      simp only [List.length_cons] at h
      have h' : (t.takeWhile p).length < t.length := by omega
      simp only [List.length_cons, List.getElem_cons_succ]
      exact ih h'
    case isFalse hn =>
      simp only [List.length_nil, List.getElem_cons_zero]
      exact Bool.eq_false_iff.mpr hn
EOF
lake env lean /tmp/test_tw_stop5.lean 2>&1
```
The issue is that after `split`, `h` still refers to `(List.takeWhile p (a :: t)).length` not the simplified version. Let me handle this differently:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_tw_stop6.lean << 'EOF'
import Mathlib.Data.List.TakeWhile

lemma not_pred_at_takeWhile_length {α : Type*} {p : α → Bool} :
    ∀ (l : List α) (h : (l.takeWhile p).length < l.length),
    p l[(l.takeWhile p).length] = false := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons a t ih =>
    intro h
    by_cases ha : p a = true
    · -- p a = true: takeWhile (a::t) = a :: takeWhile t
      have htw : (a :: t).takeWhile p = a :: t.takeWhile p := by
        simp [List.takeWhile_cons, ha]
      rw [htw] at h ⊢
      simp only [List.length_cons, List.getElem_cons_succ] at h ⊢
      exact ih h
    · -- p a = false: takeWhile (a::t) = []
      have htw : (a :: t).takeWhile p = [] := by
        simp [List.takeWhile_cons, Bool.eq_false_iff.mpr ha]
      rw [htw]
      simp only [List.length_nil, List.getElem_cons_zero]
      exact Bool.eq_false_iff.mpr ha
EOF
lake env lean /tmp/test_tw_stop6.lean 2>&1
```
The dependent type issue strikes again. The `getElem` proof depends on `takeWhile.length < l.length`, and rewriting `takeWhile` changes the proof obligation. Let me try `simp` or `conv` instead:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_tw_stop7.lean << 'EOF'
import Mathlib.Data.List.TakeWhile

-- More direct approach: avoid rewriting the dependent term
-- Use show to reformulate with a concrete index
lemma not_pred_at_takeWhile_length {α : Type*} {p : α → Bool} :
    ∀ (l : List α) (h : (l.takeWhile p).length < l.length),
    p l[(l.takeWhile p).length] = false := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons a t ih =>
    intro h
    by_cases ha : p a = true
    · -- takeWhile (a::t) = a :: takeWhile t, so length = 1 + takeWhile t length
      have htw_len : (List.takeWhile p (a :: t)).length = (List.takeWhile p t).length + 1 := by
        simp [List.takeWhile_cons, ha]
      have h' : (List.takeWhile p t).length < t.length := by
        simp [List.length_cons] at h; rw [htw_len] at h; omega
      -- goal: p (a::t)[takeWhile (a::t).length]
      -- = p (a::t)[takeWhile t .length + 1]
      -- = p t[takeWhile t .length]
      show p (a :: t)[(List.takeWhile p (a :: t)).length] = false
      rw [htw_len]
      -- Now goal: p (a :: t)[takeWhile t .length + 1] = false
      -- (a :: t)[n+1] = t[n]
      simp only [List.getElem_cons_succ]
      exact ih h'
    · -- takeWhile (a::t) = [], length = 0
      show p (a :: t)[(List.takeWhile p (a :: t)).length] = false
      have htw_len : (List.takeWhile p (a :: t)).length = 0 := by
        simp [List.takeWhile_cons, Bool.eq_false_iff.mpr ha]
      rw [htw_len]
      simp only [List.getElem_cons_zero]
      exact Bool.eq_false_iff.mpr ha
EOF
lake env lean /tmp/test_tw_stop7.lean 2>&1
```
The rewrite keeps failing because of the dependent type on `getElem`. I need to use `simp` or `conv` to handle this. Let me try a completely different approach using `List.get` with `Fin`:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_tw_stop8.lean << 'EOF'
import Mathlib.Data.List.TakeWhile

-- Try using have to create an equality with explicit casting
lemma not_pred_at_takeWhile_length {α : Type*} {p : α → Bool} :
    ∀ (l : List α) (h : (l.takeWhile p).length < l.length),
    p l[(l.takeWhile p).length] = false := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons a t ih =>
    intro h
    by_cases ha : p a = true
    · -- takeWhile (a::t) p = a :: takeWhile t p
      have htw : List.takeWhile p (a :: t) = a :: List.takeWhile p t := by
        simp [ha]
      have htw_len : (List.takeWhile p (a :: t)).length = (List.takeWhile p t).length + 1 := by
        rw [htw]; simp
      have h' : (List.takeWhile p t).length < t.length := by
        have : (a :: t).length = t.length + 1 := List.length_cons a t
        omega
      -- The goal is p (a :: t)[L] = false where L = takeWhile(a::t).length
      -- Since L = takeWhile(t).length + 1, (a::t)[L] = t[takeWhile(t).length]
      have h_idx : (a :: t)[(List.takeWhile p (a :: t)).length] =
          t[(List.takeWhile p t).length] := by
        -- Need to show these are the same element
        -- (a :: t)[n+1] = t[n], and takeWhile(a::t).length = takeWhile(t).length + 1
        -- Use List.getElem_cons_succ
        have : (List.takeWhile p (a :: t)).length = (List.takeWhile p t).length + 1 := htw_len
        simp only [this, List.getElem_cons_succ]
      simp only [h_idx]
      exact ih h'
    · have htw : List.takeWhile p (a :: t) = [] := by
        simp [Bool.eq_false_iff.mpr ha]
      have htw_len : (List.takeWhile p (a :: t)).length = 0 := by
        rw [htw]; simp
      have h_idx : (a :: t)[(List.takeWhile p (a :: t)).length] = a := by
        simp only [htw_len, List.getElem_cons_zero]
      simp only [h_idx]
      exact Bool.eq_false_iff.mpr ha
EOF
lake env lean /tmp/test_tw_stop8.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_tw_stop8b.lean << 'EOF'
import Mathlib.Data.List.TakeWhile

lemma not_pred_at_takeWhile_length {α : Type*} {p : α → Bool} :
    ∀ (l : List α) (h : (l.takeWhile p).length < l.length),
    p l[(l.takeWhile p).length] = false := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons a t ih =>
    intro h
    by_cases ha : p a = true
    · have htw_len : (List.takeWhile p (a :: t)).length =
          (List.takeWhile p t).length + 1 := by simp [ha]
      have h' : (List.takeWhile p t).length < t.length := by
        simp [List.length_cons] at h; omega
      have h_idx : (a :: t)[(List.takeWhile p (a :: t)).length] =
          t[(List.takeWhile p t).length] := by
        simp only [htw_len, List.getElem_cons_succ]
      simp only [h_idx]; exact ih h'
    · have htw_len : (List.takeWhile p (a :: t)).length = 0 := by
        simp [Bool.eq_false_iff.mpr ha]
      have h_idx : (a :: t)[(List.takeWhile p (a :: t)).length] = a := by
        simp only [htw_len, List.getElem_cons_zero]
      simp only [h_idx]; exact Bool.eq_false_iff.mpr ha
EOF
lake env lean /tmp/test_tw_stop8b.lean 2>&1
```
Now let me use this to prove `cascade_digit_neq`:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_cascade2.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat Finset Erdos728

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

private lemma not_pred_at_takeWhile_length' {α : Type*} {p : α → Bool} :
    ∀ (l : List α) (h : (l.takeWhile p).length < l.length),
    p l[(l.takeWhile p).length] = false := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons a t ih =>
    intro h
    by_cases ha : p a = true
    · have htw_len : (List.takeWhile p (a :: t)).length =
          (List.takeWhile p t).length + 1 := by simp [ha]
      have h' : (List.takeWhile p t).length < t.length := by
        simp [List.length_cons] at h; omega
      have h_idx : (a :: t)[(List.takeWhile p (a :: t)).length] =
          t[(List.takeWhile p t).length] := by
        simp only [htw_len, List.getElem_cons_succ]
      simp only [h_idx]; exact ih h'
    · have htw_len : (List.takeWhile p (a :: t)).length = 0 := by
        simp [Bool.eq_false_iff.mpr ha]
      have h_idx : (a :: t)[(List.takeWhile p (a :: t)).length] = a := by
        simp only [htw_len, List.getElem_cons_zero]
      simp only [h_idx]; exact Bool.eq_false_iff.mpr ha

-- If cascade_length = L < D - s - 1, then digit at s+1+L ≠ p-1
private lemma cascade_digit_neq' {p : ℕ} (k D m : ℕ) (hp : p.Prime)
    (hL_lt : cascade_length (p := p) k D m < D - (log p k + 1)) :
    digit p m (log p k + 1 + cascade_length (p := p) k D m) ≠ p - 1 := by
  unfold cascade_length
  simp only
  set s := log p k
  set limit := D - (s + 1)
  set pred := fun i => decide (digit p m (s + 1 + i) = p - 1)
  set tw := (List.range limit).takeWhile pred
  -- tw.length < limit = (List.range limit).length
  have h_tw_lt : tw.length < (List.range limit).length := by
    simp [List.length_range]; exact hL_lt
  -- The element at index tw.length in List.range limit doesn't satisfy pred
  have h_not := not_pred_at_takeWhile_length' (List.range limit) h_tw_lt
  -- (List.range limit)[tw.length] = tw.length
  have h_range_eq : (List.range limit)[tw.length] = tw.length := by
    simp [List.getElem_range]
  rw [h_range_eq] at h_not
  -- h_not : pred tw.length = false
  -- pred tw.length = decide (digit p m (s + 1 + tw.length) = p - 1)
  simp only [pred, decide_eq_false_iff_not] at h_not
  exact h_not
EOF
lake env lean /tmp/test_cascade2.lean 2>&1
```
Now let me prove the key bound: if cascade_length < D - s - 1, then no carry beyond position s + L + 1:
```bash
$ cd /home/jarred/code/erdos-728b && cat >> /tmp/test_cascade2.lean << 'EOF'

-- No carry beyond the cascade: if digit at position j ≠ p-1 and j ≥ s+1,
-- then ¬carry_cond at j+1, hence ¬carry_cond at all higher positions.
-- Uses carry_propagate (contrapositive).
private lemma no_carry_beyond' {p : ℕ} (hp : p.Prime) (k m j : ℕ)
    (hk : k ≥ 1) (hj : j ≥ log p k + 1) (h_digit : digit p m j ≠ p - 1) :
    ∀ i, i ≥ j + 1 → ¬carry_cond p k m i := by
  intro i hi
  -- By strong induction on i - (j + 1)
  induction i with
  | zero => omega
  | succ n ih_nat =>
    intro h_carry
    -- n + 1 > s + 1 since n + 1 ≥ j + 1 ≥ s + 2
    have hn_gt : n + 1 > log p k + 1 := by omega
    have ⟨h_digit_n, h_carry_n⟩ := carry_propagate hp k m (n + 1) hn_gt h_carry hk
    -- n ≥ j: if n = j, then digit at j = p-1, contradicting h_digit
    -- if n > j, then by IH, ¬carry_cond at n
    by_cases hn_eq : n = j
    · rw [hn_eq] at h_digit_n; exact h_digit h_digit_n
    · have hn_ge : n ≥ j + 1 := by omega
      -- Need: ¬carry_cond at n
      -- If n = 0, then j + 1 ≤ 0, impossible since j ≥ s + 1 ≥ 0
      -- Otherwise, ih_nat gives us the result for smaller values... 
      -- Wait, ih_nat is the induction hypothesis for n, but it's Nat.rec not strong induction.
      -- Let me restructure.
      sorry
EOF
lake env lean /tmp/test_cascade2.lean 2>&1 | tail -5
```
Let me fix this — `carry_propagate` takes different arguments:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_carry.lean << 'EOF'
import Erdos.Lemma3Counting
open Erdos728
#check @carry_propagate
-- carry_propagate : Nat.Prime p → ∀ (m i : ℕ), i > log p k + 1 → carry_cond p k m i → k ≥ 1 → ...
EOF
lake env lean /tmp/test_carry.lean 2>&1
```
OK, `carry_propagate` takes `k` explicitly and `{p}` implicitly. Let me fix and use strong induction:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_no_carry.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat Finset Erdos728

set_option linter.unusedVariables false

-- No carry at positions beyond the cascade boundary
-- If digit at position j ≠ p-1 and j ≥ s+1, then ¬carry_cond at all positions > j
private lemma no_carry_beyond {p : ℕ} (hp : p.Prime) (k m j : ℕ)
    (hk : k ≥ 1) (hj : j ≥ log p k + 1) (h_digit : digit p m j ≠ p - 1) :
    ∀ i, i > j → ¬carry_cond p k m i := by
  intro i hi h_carry
  -- Strong induction: decrease i down to j+1
  -- At i = j+1 > s+1: carry_propagate gives digit at j = p-1, contradiction
  -- At i > j+1 > s+1: carry_propagate gives carry at i-1 > j, by IH ¬carry at i-1, contradiction
  -- But we need strong induction on (i - j - 1) to go down.
  have : i - (j + 1) < i := by omega
  -- Use well-founded induction on i
  revert h_carry
  induction i using Nat.strong_rec_on with
  | _ i ih =>
    intro h_carry
    have hi_gt_s : i > log p k + 1 := by omega
    have ⟨h_dig_prev, h_carry_prev⟩ := carry_propagate k hp m i hi_gt_s h_carry hk
    by_cases h_eq : i - 1 = j
    · rw [h_eq] at h_dig_prev; exact h_digit h_dig_prev
    · have h_prev_gt : i - 1 > j := by omega
      have h_prev_lt : i - 1 < i := by omega
      exact ih (i - 1) h_prev_lt h_prev_gt h_carry_prev
EOF
lake env lean /tmp/test_no_carry.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_no_carry2.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat Finset Erdos728

set_option linter.unusedVariables false

private lemma no_carry_beyond {p : ℕ} (hp : p.Prime) (k m j : ℕ)
    (hk : k ≥ 1) (hj : j ≥ log p k + 1) (h_digit : digit p m j ≠ p - 1)
    (i : ℕ) (hi : i > j) (h_carry : carry_cond p k m i) : False := by
  -- Descend from i to j+1 using carry_propagate
  -- Each step: carry at position n > s+1 → digit at n-1 = p-1 AND carry at n-1
  -- When we reach j+1: digit at j = p-1, contradiction
  -- When n-1 > j+1: continue descending
  -- Use Nat.strongRecOn on (i - j - 1)
  have key : ∀ n, n > j → n ≤ i → carry_cond p k m n → False := by
    intro n hn_gt hn_le h_c
    -- Induction on n - (j+1): this decreases at each step
    induction n, (show n - (j + 1) < i from by omega) using WellFoundedRelation.wf.induction with
    | ind n ih =>
      have hn_gt_s : n > log p k + 1 := by omega
      obtain ⟨h_dig_prev, h_carry_prev⟩ := carry_propagate k hp m n hn_gt_s h_c hk
      by_cases h_eq : n - 1 = j
      · rw [h_eq] at h_dig_prev; exact h_digit h_dig_prev
      · have h_prev_gt : n - 1 > j := by omega
        exact ih (n - 1) (by omega) h_prev_gt (by omega) h_carry_prev
  exact key i hi (le_refl i) h_carry
EOF
lake env lean /tmp/test_no_carry2.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_no_carry3.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat Finset Erdos728

set_option linter.unusedVariables false

private lemma no_carry_beyond {p : ℕ} (hp : p.Prime) (k m j : ℕ)
    (hk : k ≥ 1) (hj : j ≥ log p k + 1) (h_digit : digit p m j ≠ p - 1)
    (i : ℕ) (hi : i > j) (h_carry : carry_cond p k m i) : False := by
  -- Descend from i to j+1 using carry_propagate, using well-founded recursion on (i - j)
  obtain ⟨d, rfl⟩ : ∃ d, i = j + 1 + d := ⟨i - (j + 1), by omega⟩
  clear hi
  induction d with
  | zero =>
    -- i = j + 1
    have : j + 1 > log p k + 1 := by omega
    obtain ⟨h_dig, _⟩ := carry_propagate k hp m (j + 1) this h_carry hk
    simp at h_dig
    exact h_digit h_dig
  | succ d ih =>
    -- i = j + 1 + (d + 1) = j + 2 + d
    have h_pos : j + 1 + (d + 1) > log p k + 1 := by omega
    obtain ⟨h_dig, h_carry_prev⟩ := carry_propagate k hp m (j + 1 + (d + 1)) h_pos h_carry hk
    -- carry at (j + 1 + (d+1)) - 1 = j + 1 + d
    have h_sub : j + 1 + (d + 1) - 1 = j + 1 + d := by omega
    rw [h_sub] at h_carry_prev
    exact ih h_carry_prev
EOF
lake env lean /tmp/test_no_carry3.lean 2>&1
```
Excellent! Now let me combine everything to prove `valuation_gt_implies_cascade`:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_vtc_full.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat Finset Erdos728

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

-- 1. takeWhile boundary lemma
private lemma not_pred_at_takeWhile_length' {α : Type*} {p : α → Bool} :
    ∀ (l : List α) (h : (l.takeWhile p).length < l.length),
    p l[(l.takeWhile p).length] = false := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons a t ih =>
    intro h
    by_cases ha : p a = true
    · have htw_len : (List.takeWhile p (a :: t)).length =
          (List.takeWhile p t).length + 1 := by simp [ha]
      have h' : (List.takeWhile p t).length < t.length := by
        simp [List.length_cons] at h; omega
      have h_idx : (a :: t)[(List.takeWhile p (a :: t)).length] =
          t[(List.takeWhile p t).length] := by
        simp only [htw_len, List.getElem_cons_succ]
      simp only [h_idx]; exact ih h'
    · have htw_len : (List.takeWhile p (a :: t)).length = 0 := by
        simp [Bool.eq_false_iff.mpr ha]
      have h_idx : (a :: t)[(List.takeWhile p (a :: t)).length] = a := by
        simp only [htw_len, List.getElem_cons_zero]
      simp only [h_idx]; exact Bool.eq_false_iff.mpr ha

-- 2. If cascade_length < D - s - 1, digit at s+1+L ≠ p-1
private lemma cascade_digit_neq' {p : ℕ} (k D m : ℕ)
    (hL_lt : cascade_length (p := p) k D m < D - (log p k + 1)) :
    digit p m (log p k + 1 + cascade_length (p := p) k D m) ≠ p - 1 := by
  unfold cascade_length
  simp only
  set s := log p k
  set limit := D - (s + 1)
  set pred := fun i => decide (digit p m (s + 1 + i) = p - 1)
  set tw := (List.range limit).takeWhile pred
  have h_tw_lt : tw.length < (List.range limit).length := by
    simp [List.length_range]; exact hL_lt
  have h_not := not_pred_at_takeWhile_length' (List.range limit) h_tw_lt
  have h_range_eq : (List.range limit)[tw.length] = tw.length := by
    simp [List.getElem_range]
  rw [h_range_eq] at h_not
  simp only [pred, decide_eq_false_iff_not] at h_not
  exact h_not

-- 3. No carry beyond the cascade boundary
private lemma no_carry_beyond' {p : ℕ} (hp : p.Prime) (k m j : ℕ)
    (hk : k ≥ 1) (hj : j ≥ log p k + 1) (h_digit : digit p m j ≠ p - 1)
    (i : ℕ) (hi : i > j) (h_carry : carry_cond p k m i) : False := by
  obtain ⟨d, rfl⟩ : ∃ d, i = j + 1 + d := ⟨i - (j + 1), by omega⟩
  clear hi
  induction d with
  | zero =>
    have : j + 1 > log p k + 1 := by omega
    obtain ⟨h_dig, _⟩ := carry_propagate k hp m (j + 1) this h_carry hk
    simp at h_dig; exact h_digit h_dig
  | succ d ih =>
    have h_pos : j + 1 + (d + 1) > log p k + 1 := by omega
    obtain ⟨_, h_carry_prev⟩ := carry_propagate k hp m (j + 1 + (d + 1)) h_pos h_carry hk
    have h_sub : j + 1 + (d + 1) - 1 = j + 1 + d := by omega
    rw [h_sub] at h_carry_prev
    exact ih h_carry_prev

-- 4. Main: v_p(C(m+k,k)) > D/6 → cascade_length ≥ D/6 - s
-- Contrapositive: cascade_length < D/6 - s → v_p ≤ D/6
-- Proof: if cascade < D/6 - s, then by (2) digit ≠ p-1 at the boundary,
-- by (3) no carries beyond that boundary, so total carries ≤ boundary position.
-- Total carries ≤ s + 1 + cascade_length ≤ D/6.
private lemma valuation_gt_implies_cascade' {p : ℕ} (hp : p.Prime) (k D m : ℕ)
    (hk : k ≥ 1) (hD : D ≥ 16 * (log p (k + 1)) + 16) :
    padicValNat p ((m + k).choose k) > D / 6 →
    cascade_length (p := p) k D m ≥ D / 6 - log p k := by
  -- Contrapositive
  intro hv
  by_contra h_lt
  push_neg at h_lt
  set s := log p k
  set L := cascade_length (p := p) k D m
  -- Verify L < D - (s+1) so the cascade terminates within D
  have hD_ge : D ≥ 12 * (s + 1) + 6 := by
    have : s ≤ log p (k + 1) := Nat.log_mono_right (by omega)
    omega
  have hL_lt_limit : L < D - (s + 1) := by
    have : D / 6 ≥ 2 * (s + 1) := by omega
    omega
  -- digit at s+1+L ≠ p-1 (cascade boundary)
  have h_digit := cascade_digit_neq' k D m hL_lt_limit
  -- No carry at positions > s+1+L
  -- Express v_p using factorization_choose'
  set b := max (D + 1) (log p (m + k) + 1)
  have hb : log p (m + k) < b := by
    show log p (m + k) < max (D + 1) (log p (m + k) + 1); omega
  rw [← Nat.factorization_def _ hp, Nat.factorization_choose' hp hb] at hv
  -- hv : card of {i ∈ Ico 1 b : carry_cond p k m i} > D/6
  -- All carry positions must be ≤ s+1+L
  -- Carries at positions > s+1+L are impossible (by no_carry_beyond')
  -- s+1+L is the boundary position
  set boundary := s + 1 + L
  have h_boundary_ge : boundary ≥ s + 1 := by omega
  -- Show all carries are in Ico 1 (boundary + 1)
  have h_subset : (Ico 1 b).filter (fun i => p ^ i ≤ k % p ^ i + m % p ^ i) ⊆
      Ico 1 (boundary + 1) := by
    intro i hi
    rw [mem_filter, mem_Ico] at hi
    rw [mem_Ico]
    constructor
    · exact hi.1.1
    · by_contra h_not
      push_neg at h_not
      have h_i_gt : i > boundary := by omega
      exact no_carry_beyond' hp k m (s + 1 + L) hk (by omega) h_digit i h_i_gt hi.2
  -- card of carry set ≤ card of Ico 1 (boundary + 1) = boundary
  have h_card_bound : ((Ico 1 b).filter
      (fun i => p ^ i ≤ k % p ^ i + m % p ^ i)).card ≤ boundary := by
    calc ((Ico 1 b).filter (fun i => p ^ i ≤ k % p ^ i + m % p ^ i)).card
        ≤ (Ico 1 (boundary + 1)).card := card_le_card h_subset
      _ = boundary := by simp [Nat.card_Ico]
  -- boundary = s + 1 + L < s + 1 + (D/6 - s) = D/6 + 1
  -- So boundary ≤ D/6
  have h_boundary_le : boundary ≤ D / 6 := by
    show s + 1 + L ≤ D / 6; omega
  -- Contradiction: card > D/6 but card ≤ D/6
  omega
EOF
lake env lean /tmp/test_vtc_full.lean 2>&1
```
The issue is with `hL_lt_limit`. Let me debug the arithmetic:

`D ≥ 16 * (log p (k+1)) + 16` and `s = log p k`. We need `D/6 - s < D - (s+1)`, i.e., `D/6 < D - 1`, which holds for `D ≥ 2`. We also need `L < D/6 - s` (from `h_lt`) and we want to show `L < D - (s+1)`.

From `h_lt`: `L < D/6 - s`. We need `D/6 - s < D - (s+1)`, i.e., `D/6 < D - 1`. Since `D ≥ 16*(log p (k+1)) + 16 ≥ 16`, `D/6 ≥ 2` and `D - 1 ≥ 15`, so `D/6 < D - 1`.

But omega is struggling with the floor division. Let me be more explicit:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_arith.lean << 'EOF'
import Mathlib.Data.Nat.Basic

-- Debug the arithmetic
example (D s L : ℕ) (hD : D ≥ 12 * (s + 1) + 6) (hL : L < D / 6 - s) :
    L < D - (s + 1) := by
  have : D / 6 ≥ 2 * (s + 1) := by omega
  have : D / 6 - s ≤ D - (s + 1) := by omega
  omega
EOF
lake env lean /tmp/test_arith.lean 2>&1
```
OK, so the arithmetic works when we have `D ≥ 12*(s+1)+6`. The issue in the full proof is that I'm trying to derive this from `hD : D ≥ 16 * (log p (k + 1)) + 16` and the relationship `s ≤ log p (k+1)`. Let me fix the proof:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_arith2.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat

-- Check if s ≤ log p (k+1)
-- s = log p k. We know log p k ≤ log p (k+1) for k ≥ 1 and p ≥ 2.
example (p k : ℕ) (hp : p ≥ 2) (hk : k ≥ 1) : log p k ≤ log p (k + 1) :=
  Nat.log_mono_right (by omega)

-- Now check: D ≥ 16*(log p (k+1)) + 16 → D ≥ 12*(log p k + 1) + 6
example (D p k : ℕ) (hp : p ≥ 2) (hk : k ≥ 1) 
    (hD : D ≥ 16 * (log p (k + 1)) + 16) : D ≥ 12 * (log p k + 1) + 6 := by
  have : log p k ≤ log p (k + 1) := Nat.log_mono_right (by omega)
  omega
EOF
lake env lean /tmp/test_arith2.lean 2>&1
```
Omega can't handle `log p k ≤ log p (k+1)` together with the arithmetic. The issue is omega doesn't know the relationship between `log p k` and `log p (k+1)` — it only knows `log p k ≤ log p (k+1)` as a fact. So we need:

`D ≥ 16 * (log p (k+1)) + 16` and `log p k ≤ log p (k+1)`.
Then `D ≥ 16 * (log p k) + 16 ≥ 12 * (log p k) + 12 + 4 * (log p k) + 4`.
Since `log p k ≥ 0`, `4 * (log p k) + 4 ≥ 4 > -6`.
So `D ≥ 12 * (log p k) + 12 + (-6) = 12 * (log p k + 1) + 6`? Wait:
`12 * (log p k + 1) + 6 = 12 * log p k + 18`.
`16 * log p k + 16 ≥ 12 * log p k + 18` iff `4 * log p k ≥ 2`, which is false when `log p k = 0`.

Hmm, so the derivation doesn't go through directly. We need `D ≥ 16 * log p (k+1) + 16`. If `log p k = 0` (i.e., `k < p`), then `D ≥ 16 * log p (k+1) + 16 ≥ 16`. And `12 * (0 + 1) + 6 = 18`. So we need `D ≥ 18`, which follows from `D ≥ 16 * log p (k+1) + 16 ≥ 16*1 + 16 = 32` when `log p (k+1) ≥ 1`. When `log p (k+1) = 0`, we have `k + 1 < p`, so `k ≤ 1` (since `p ≤ 2k` from the context, but we might not have that here). Hmm, this is getting complicated.

Actually, the more conservative bound: `log p k ≤ log p (k+1)` and `D ≥ 16 * log p (k+1) + 16`.
We need `D ≥ 12 * (log p k + 1) + 6 = 12 * log p k + 18`.
From `D ≥ 16 * log p (k+1) + 16 ≥ 16 * log p k + 16`.
We need `16 * log p k + 16 ≥ 12 * log p k + 18`, i.e., `4 * log p k ≥ 2`, i.e., `log p k ≥ 1`.

When `log p k = 0` (k = 0 or k < p), we have `D ≥ 16 * log p (k+1) + 16`.
If `k = 0`: but we have `hk : k ≥ 1`, so `k ≥ 1`.
If `k ≥ 1` and `k < p`: then `log p k = 0` but `log p (k+1) ≥ 0`. If `k+1 ≤ p`, then `log p (k+1) ≤ 1`. If `k+1 = p`, then `log p (k+1) = 1` (for p ≥ 2). So `D ≥ 16*1 + 16 = 32`. And `12*1 + 6 = 18 ≤ 32`. ✓

If `k+1 < p`: `log p (k+1) = 0`, so `D ≥ 16`. And `12*1 + 6 = 18 > 16`. ✗

Wait, when `log p k = 0`, we need `D ≥ 18` but only have `D ≥ 16`. So the bound `D ≥ 12*(s+1)+6` does NOT follow from `D ≥ 16 * log p (k+1) + 16` when `log p (k+1) = 0` and `s = 0`.

But when `log p (k+1) = 0`, we have `k + 1 ≤ p^0 = 1`, so `k = 0`. But `hk : k ≥ 1` contradicts this! So `log p (k+1) ≥ 1` when `k ≥ 1` and `p ≥ 2`:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_arith3.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat

-- When k ≥ 1 and p ≥ 2: log p (k+1) ≥ 1 since k+1 ≥ 2 ≥ p^1... no, that's only for p=2.
-- Actually log p n ≥ 1 iff n ≥ p.
-- k ≥ 1 → k+1 ≥ 2. But log p 2 = 0 when p ≥ 3.
-- So log p (k+1) can be 0 when k = 1 and p = 3.

-- OK so the bound doesn't follow trivially. Let me check: when s = log p k = 0 and k ≥ 1:
-- D ≥ 16 * log p (k+1) + 16. If log p (k+1) = 0, D ≥ 16.
-- We need D ≥ 12*(0+1) + 6 = 18. But D ≥ 16 doesn't guarantee D ≥ 18.

-- Hmm, but with s = 0, D/6 - s = D/6. And cascade_length < D - 1 is what we need.
-- D/6 < D - 1 for D ≥ 2. So even with D ≥ 16, D/6 ≤ 2 < 15 ≤ D - 1.

-- Actually, the specific arithmetic bound I need is:
-- L < D/6 - s → L < D - (s+1)
-- This requires D/6 - s ≤ D - (s+1), i.e., D/6 ≤ D - 1.
-- For D ≥ 2 (certainly D ≥ 16 satisfies this).
-- D/6 ≤ D - 1: when D ≥ 1, D/6 ≤ D ≤ D, and D - 1 ≥ 0.
-- More precisely: D/6 ≤ D - 1 iff D ≤ 6*(D-1) = 6D - 6 iff 6 ≤ 5D iff D ≥ 2.

example (D s L : ℕ) (hD : D ≥ 16) (hL : L < D / 6 - s) :
    L < D - (s + 1) := by
  have h1 : D / 6 ≤ D - 1 := by omega
  omega
EOF
lake env lean /tmp/test_arith3.lean 2>&1
```
So I can derive `L < D - (s+1)` from `D ≥ 16` and `L < D/6 - s`. And `D ≥ 16` follows from `D ≥ 16 * log p (k+1) + 16`. Let me also check the boundary bound:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_arith4.lean << 'EOF'
import Mathlib.Data.Nat.Basic

-- s + 1 + L ≤ D / 6 when L < D / 6 - s
-- In ℕ: L ≤ D/6 - s - 1 (from h_lt: L + 1 ≤ D/6 - s, i.e. L ≤ D/6 - s - 1)
-- s + 1 + L ≤ s + 1 + (D/6 - s - 1) = D/6
-- This only works if D/6 ≥ s + 1, i.e., D/6 > s, i.e., D/6 - s ≥ 1, which is true since L ≥ 0 < D/6 - s.

example (s L D6 : ℕ) (hL : L < D6 - s) : s + 1 + L ≤ D6 := by omega
EOF
lake env lean /tmp/test_arith4.lean 2>&1
```
Good. Let me now fix the full proof:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_vtc_full2.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat Finset Erdos728

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

private lemma not_pred_at_takeWhile_length' {α : Type*} {p : α → Bool} :
    ∀ (l : List α) (h : (l.takeWhile p).length < l.length),
    p l[(l.takeWhile p).length] = false := by
  intro l; induction l with
  | nil => intro h; simp at h
  | cons a t ih =>
    intro h; by_cases ha : p a = true
    · have htw_len : (List.takeWhile p (a :: t)).length =
          (List.takeWhile p t).length + 1 := by simp [ha]
      have h' : (List.takeWhile p t).length < t.length := by
        simp [List.length_cons] at h; omega
      have h_idx : (a :: t)[(List.takeWhile p (a :: t)).length] =
          t[(List.takeWhile p t).length] := by
        simp only [htw_len, List.getElem_cons_succ]
      simp only [h_idx]; exact ih h'
    · have htw_len : (List.takeWhile p (a :: t)).length = 0 := by
        simp [Bool.eq_false_iff.mpr ha]
      have h_idx : (a :: t)[(List.takeWhile p (a :: t)).length] = a := by
        simp only [htw_len, List.getElem_cons_zero]
      simp only [h_idx]; exact Bool.eq_false_iff.mpr ha

private lemma cascade_digit_neq' {p : ℕ} (k D m : ℕ)
    (hL_lt : cascade_length (p := p) k D m < D - (log p k + 1)) :
    digit p m (log p k + 1 + cascade_length (p := p) k D m) ≠ p - 1 := by
  unfold cascade_length; simp only
  set s := log p k; set limit := D - (s + 1)
  set pred := fun i => decide (digit p m (s + 1 + i) = p - 1)
  set tw := (List.range limit).takeWhile pred
  have h_tw_lt : tw.length < (List.range limit).length := by
    simp [List.length_range]; exact hL_lt
  have h_not := not_pred_at_takeWhile_length' (List.range limit) h_tw_lt
  have h_range_eq : (List.range limit)[tw.length] = tw.length := by
    simp [List.getElem_range]
  rw [h_range_eq] at h_not
  simp only [pred, decide_eq_false_iff_not] at h_not; exact h_not

private lemma no_carry_beyond' {p : ℕ} (hp : p.Prime) (k m j : ℕ)
    (hk : k ≥ 1) (hj : j ≥ log p k + 1) (h_digit : digit p m j ≠ p - 1)
    (i : ℕ) (hi : i > j) (h_carry : carry_cond p k m i) : False := by
  obtain ⟨d, rfl⟩ : ∃ d, i = j + 1 + d := ⟨i - (j + 1), by omega⟩
  clear hi; induction d with
  | zero =>
    have : j + 1 > log p k + 1 := by omega
    obtain ⟨h_dig, _⟩ := carry_propagate k hp m (j + 1) this h_carry hk
    simp at h_dig; exact h_digit h_dig
  | succ d ih =>
    have h_pos : j + 1 + (d + 1) > log p k + 1 := by omega
    obtain ⟨_, h_carry_prev⟩ := carry_propagate k hp m (j + 1 + (d + 1)) h_pos h_carry hk
    have h_sub : j + 1 + (d + 1) - 1 = j + 1 + d := by omega
    rw [h_sub] at h_carry_prev; exact ih h_carry_prev

private lemma valuation_gt_implies_cascade' {p : ℕ} (hp : p.Prime) (k D m : ℕ)
    (hk : k ≥ 1) (hD : D ≥ 16 * (log p (k + 1)) + 16) :
    padicValNat p ((m + k).choose k) > D / 6 →
    cascade_length (p := p) k D m ≥ D / 6 - log p k := by
  intro hv; by_contra h_lt; push_neg at h_lt
  set s := log p k; set L := cascade_length (p := p) k D m
  -- L < D - (s+1): from L < D/6 - s and D ≥ 16
  have hD_ge16 : D ≥ 16 := by omega
  have hL_lt_limit : L < D - (s + 1) := by
    have : D / 6 ≤ D - 1 := by omega; omega
  -- digit at s+1+L ≠ p-1 (cascade boundary)
  have h_digit := cascade_digit_neq' k D m hL_lt_limit
  -- Express v_p using factorization_choose'
  set b := max (D + 1) (log p (m + k) + 1) with hb_def
  have hb : log p (m + k) < b := by show _ < max _ _; omega
  rw [← Nat.factorization_def _ hp, Nat.factorization_choose' hp hb] at hv
  -- All carry positions ≤ s+1+L
  set boundary := s + 1 + L
  have h_subset : (Ico 1 b).filter (fun i => p ^ i ≤ k % p ^ i + m % p ^ i) ⊆
      Ico 1 (boundary + 1) := by
    intro i hi; rw [mem_filter, mem_Ico] at hi; rw [mem_Ico]
    refine ⟨hi.1.1, ?_⟩
    by_contra h_not; push_neg at h_not
    exact no_carry_beyond' hp k m (s + 1 + L) hk (by omega) h_digit i (by omega) hi.2
  have h_card_bound : ((Ico 1 b).filter
      (fun i => p ^ i ≤ k % p ^ i + m % p ^ i)).card ≤ boundary := by
    calc ((Ico 1 b).filter _).card
        ≤ (Ico 1 (boundary + 1)).card := card_le_card h_subset
      _ = boundary := by simp [Nat.card_Ico]
  -- boundary = s + 1 + L ≤ D/6
  have h_boundary_le : boundary ≤ D / 6 := by omega
  omega
EOF
lake env lean /tmp/test_vtc_full2.lean 2>&1
```
A typo — missing semicolon after the intermediate `omega`:
🛠️ **Executing tool: edit**

```bash
$ cd /home/jarred/code/erdos-728b && lake env lean /tmp/test_vtc_full2.lean 2>&1
```
All compiles with no sorry! Now let me integrate this into the main file. I need to:
1. Add the helper lemmas (`not_pred_at_takeWhile_length`, `cascade_digit_neq`, `no_carry_beyond`)
2. Replace the sorry in `valuation_gt_implies_cascade`
🛠️ **Executing tool: read**

🛠️ **Executing tool: read**
Now I need to replace the sorry in `valuation_gt_implies_cascade` and add the helper lemmas before it. Let me do the edit:
🛠️ **Executing tool: edit**

```bash
$ cd /home/jarred/code/erdos-728b && lake build 2>&1 | tail -15
```
Build succeeded! Let me check which sorrys remain:
```bash
$ cd /home/jarred/code/erdos-728b && lake build 2>&1 | grep "sorry"
```
Let me verify that `bad_residue_sets` is NOT among the sorry warnings:
```bash
$ cd /home/jarred/code/erdos-728b && grep -n "bad_residue_sets\|sorry" Erdos/Lemma3Counting.lean | grep -E "sorry|bad_residue"
```
`bad_residue_sets` at line 586 does NOT have a sorry — it's fully proved! The sorrys at lines 56, 123, 126, 352, 355, 618, 661, 676 are all pre-existing sorrys from other lemmas.

Wait, line 618 — let me check what that is:
```bash
$ cd /home/jarred/code/erdos-728b && sed -n '614p;615p;616p;617p;618p;619p' Erdos/Lemma3Counting.lean
```
That's `count_bad_interval`, a pre-existing sorry. All good.

Let me now verify the sorry count before and after:
```bash
$ cd /home/jarred/code/erdos-728b && grep -c "sorry" Erdos/Lemma3Counting.lean
```

```bash
$ cd /home/jarred/code/erdos-728b && grep -n "sorry" Erdos/Lemma3Counting.lean
```
Line 653 mentions "sorry'd" in a comment, not an actual sorry. The actual sorry count is 7 (lines 56, 123, 126, 352, 355, 618, 661, 676 — but 653 is just a comment). Let me count actual `sorry` at the start of lines or as standalone:
```bash
$ cd /home/jarred/code/erdos-728b && grep -c "^\s*sorry$\|:= sorry$\| sorry$" Erdos/Lemma3Counting.lean
```
8 actual sorrys — all pre-existing. The `bad_residue_sets` sorry has been eliminated!

Let me commit this:
```bash
$ cd /home/jarred/code/erdos-728b && git add -A && git commit -m "Close sorry: bad_residue_sets

Prove that both 'bad' conditions (high valuation on C(m+k,k) and low
valuation on C(2m,m)) depend only on m mod p^D.

Key lemmas proved:
- digit_mod_pow_eq: digit p (m % p^D) i = digit p m i for i < D
- cascade_length_mod_eq: cascade_length is invariant under mod p^D
- count_high_digits_mod_eq: count_high_digits is invariant under mod p^D
- valuation_gt_implies_cascade: v_p(C(m+k,k)) > D/6 implies large cascade
  (via contrapositive using carry_propagate and factorization_choose')
- count_high_le_valuation: count_high_digits ≤ v_p(C(2m,m)) for arbitrary m
  (extends valuation_ge_high_digits to remove the log bound restriction)
- no_carry_beyond: no carry exists past the cascade boundary
  (descending induction using carry_propagate)

No new sorrys introduced. lake build succeeds."
```
Now let me update the task:
```bash
$ cd /home/jarred/code/erdos-728b && tm update erdos728b-hga --status "Completed - bad_residue_sets fully proved with no new sorrys"
```

```bash
$ cd /home/jarred/code/erdos-728b && tm close erdos728b-hga
```
## Summary

```json
{
  "status": "completed",
  "summary": "Closed sorry in bad_residue_sets. lake build succeeds with no new sorrys.",
  "details": "Proved bad_residue_sets (Lemma3Counting.lean:586) — both 'bad' conditions depend only on m mod p^D. Key contributions:\n\n1. **digit_mod_pow_eq**: digit p (m % p^D) i = digit p m i for i < D (using Nat.mod_mul_right_div_self and Nat.mod_mod_of_dvd)\n\n2. **cascade_length_mod_eq**: cascade_length is invariant under mod p^D (all digit lookups are at positions < D)\n\n3. **count_high_digits_mod_eq**: count_high_digits is invariant under mod p^D\n\n4. **valuation_gt_implies_cascade** (the main mathematical content): v_p(C(m+k,k)) > D/6 → cascade_length ≥ D/6 - log p k. Proved via contrapositive using:\n   - cascade_digit_neq: if cascade terminates within D, the boundary digit ≠ p-1\n   - no_carry_beyond: descending induction via carry_propagate shows no carry exists past the cascade boundary\n   - factorization_choose': Kummer's theorem to express v_p as #{carry positions}\n   - The carry set is contained in Ico 1 (s+2+L), bounding v_p ≤ s+1+L ≤ D/6\n\n5. **count_high_le_valuation**: count_high_digits ≤ v_p(C(2m,m)) for arbitrary m (removed the log bound restriction from valuation_ge_high_digits by using factorization_choose with b = max(D+1, log p (2m)+1))\n\nNo new sorry holes introduced. All 8 remaining sorrys in the file are pre-existing."
}
```

## Final Result

## Summary

```json
{
  "status": "completed",
  "summary": "Closed sorry in bad_residue_sets. lake build succeeds with no new sorrys.",
  "details": "Proved bad_residue_sets (Lemma3Counting.lean:586) — both 'bad' conditions depend only on m mod p^D. Key contributions:\n\n1. **digit_mod_pow_eq**: digit p (m % p^D) i = digit p m i for i < D (using Nat.mod_mul_right_div_self and Nat.mod_mod_of_dvd)\n\n2. **cascade_length_mod_eq**: cascade_length is invariant under mod p^D (all digit lookups are at positions < D)\n\n3. **count_high_digits_mod_eq**: count_high_digits is invariant under mod p^D\n\n4. **valuation_gt_implies_cascade** (the main mathematical content): v_p(C(m+k,k)) > D/6 → cascade_length ≥ D/6 - log p k. Proved via contrapositive using:\n   - cascade_digit_neq: if cascade terminates within D, the boundary digit ≠ p-1\n   - no_carry_beyond: descending induction via carry_propagate shows no carry exists past the cascade boundary\n   - factorization_choose': Kummer's theorem to express v_p as #{carry positions}\n   - The carry set is contained in Ico 1 (s+2+L), bounding v_p ≤ s+1+L ≤ D/6\n\n5. **count_high_le_valuation**: count_high_digits ≤ v_p(C(2m,m)) for arbitrary m (removed the log bound restriction from valuation_ge_high_digits by using factorization_choose with b = max(D+1, log p (2m)+1))\n\nNo new sorry holes introduced. All 8 remaining sorrys in the file are pre-existing."
}
```

End Time: 2026-02-11T05:47:25.354Z
