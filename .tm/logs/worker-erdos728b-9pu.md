# timtam Task: Close sorry: count_few_high_digits (L3C:82) (erdos728b-9pu)

Role: formalize
Agent: formalize (google-antigravity/claude-opus-4-6-thinking)
Start Time: 2026-02-11T05:01:37.253Z

## Agent Interaction



> **Thinking:**
> Let me start by understanding the task. I need to close a `sorry` in `Lemma3Counting.lean` at line 82, specifically for `count_few_high_digits`. Let me read the relevant files first.


```bash
$ cd /home/jarred/code/erdos-728b && tm update erdos728b-9pu --status "Reading relevant files to understand the sorry"
```

🛠️ **Executing tool: read**
Now let me read the Chernoff file to understand `count_few_high_digits_bound_chernoff`:
🛠️ **Executing tool: read**
Now let me read the `Lemma3Common.lean` to understand `probHigh`, `count_high_digits`, `highDigitCount`, `isHigh`, etc.:
🛠️ **Executing tool: read**

🛠️ **Executing tool: read**
Now let me check the NL proof:
```bash
$ cd /home/jarred/code/erdos-728b && ls proofs/
```

```bash
$ cd /home/jarred/code/erdos-728b && grep -n "count_few_high_digits\|high_digits\|Chernoff\|exp(-D/18)\|2\^(D/36)\|ln 2" proofs/lemma3-counting.md | head -40
```

```bash
$ cd /home/jarred/code/erdos-728b && sed -n '140,170p' proofs/lemma3-counting.md
```

```bash
$ cd /home/jarred/code/erdos-728b && tm update erdos728b-9pu --status "Analyzing the sorry and planning the proof approach"
```
Let me understand the sorry I need to close:

```lean
lemma count_few_high_digits (hp : p.Prime) (t : ℕ) (ht : t ≤ D/6) (hp_ge_3 : p ≥ 3) :
    ((range (p^D)).filter (fun m => count_high_digits p m D < t)).card ≤ p^D / 2^(D/36) := sorry
```

The key challenge is bridging between:
1. `count_few_high_digits_bound_chernoff` which works on `DigitSpace D p` with `highDigitCount` and gives a real-valued bound `p^D * exp(-2 * ((D * probHigh p) - t)^2 / D)`
2. The target which works on `range (p^D)` with `count_high_digits` and needs `p^D / 2^(D/36)` (natural number division)

The plan:
1. Use `toDigitSpace_bijective` to convert between `range (p^D)` and `DigitSpace D p`
2. Use `highDigitCount_eq` to relate `highDigitCount` and `count_high_digits`
3. Apply `count_few_high_digits_bound_chernoff` with appropriate `t`
4. Show the exponential bound: `exp(-2 * ((D * probHigh p) - t)^2 / D) ≤ 1/2^(D/36)`

Let me first check what `probHigh` evaluates to for `p ≥ 3`:

- For `p ≥ 3`: `probHigh p = (p/2 : ℕ) / (p : ℝ)`. For `p = 3`, this is `1/3`. For `p = 5`, it's `2/5`. Generally `≥ 1/3`.
- `D * probHigh p ≥ D/3`
- We need `t < D * probHigh p`. Since `t ≤ D/6` and `D * probHigh p ≥ D/3`, this holds for `D ≥ 1` (and is trivially true for `D = 0`).
- The Chernoff exponent: `-2 * ((D * probHigh p) - t)^2 / D`. With `probHigh p ≥ 1/3` and `t ≤ D/6`:
  - `(D * probHigh p) - t ≥ D/3 - D/6 = D/6`
  - So exponent ≤ `-2 * (D/6)^2 / D = -2 * D/36 = -D/18`
- We need `exp(-D/18) ≤ 2^(-D/36)`, i.e., `exp(-1/18) ≤ 2^(-1/36)`, i.e., `1/18 ≥ ln(2)/36`, i.e., `2 ≥ ln(2)`, which is true.

This is a substantial proof. Let me start writing it step by step.
```bash
$ cd /home/jarred/code/erdos-728b && lake build 2>&1 | tail -20
```
Good, it builds. Now let me write the proof. I need to carefully plan this.

Let me first explore what API is available:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_api.lean << 'EOF'
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real

-- Check key lemmas
#check Real.exp_le_exp
#check Real.rpow_natCast
#check Real.exp_neg
#check Real.log_le_log_of_le
#check Nat.div_le_self
#check Nat.floor_le
#check Real.exp_log
#check Real.log_two_gt_half
EOF
lake env lean /tmp/test_api.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_api2.lean << 'EOF'
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real

#check Real.log_le_log
#check Real.exp_le_one_of_nonpos
#check Real.rpow_le_rpow
#check Real.rpow_le_one
#check Real.log_two_pos
#check exp_le_exp
#check pow_le_pow_left
#check inv_pow
#check Real.rpow_neg
EOF
lake env lean /tmp/test_api2.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_api3.lean << 'EOF'
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real

#check Real.add_pow_le_pow_mul_pow_of_sq_le_sq
#check Real.log_lt_one_of_lt
#check Real.log_two_gt_half  
#check @Real.log_lt
-- log 2 < 2
example : Real.log 2 < 2 := by
  calc Real.log 2 < Real.log (Real.exp 2) := by
    apply Real.log_lt_log (by norm_num : (0:ℝ) < 2)
    calc (2:ℝ) < 3 := by norm_num
    _ ≤ Real.exp 2 := by
      have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [this]
      have h1 : (2.5 : ℝ) ≤ Real.exp 1 := by
        sorry
      linarith
  _ = 2 := Real.log_exp 2
EOF
lake env lean /tmp/test_api3.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_api4.lean << 'EOF'
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real

-- Key fact we need: log 2 ≤ 2 (or more precisely log 2 < 1)
#check Real.log_le_sub_one_of_le  
#check Real.log_le_of_le_exp
#check @Real.exp_ge_one_add_of_nonneg
example : Real.log 2 ≤ 1 := by
  rw [← Real.log_exp 1]
  apply Real.log_le_log (by norm_num : (0:ℝ) < 2)
  calc (2:ℝ) ≤ 1 + 1 := by norm_num
    _ ≤ Real.exp 1 := Real.add_one_le_exp 1
EOF
lake env lean /tmp/test_api4.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_api4b.lean << 'EOF'
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real

#check @Real.add_one_le_exp
example : Real.log 2 ≤ 1 := by
  rw [← Real.log_exp 1]
  apply Real.log_le_log (by norm_num : (0:ℝ) < 2)
  calc (2:ℝ) ≤ 1 + 1 := by norm_num
    _ ≤ Real.exp 1 := Real.add_one_le_exp 1
EOF
lake env lean /tmp/test_api4b.lean 2>&1
```
Good, that works. Now let me think about the overall proof strategy more carefully.

The target is:
```
((range (p^D)).filter (fun m => count_high_digits p m D < t)).card ≤ p^D / 2^(D/36)
```

The Chernoff bound gives:
```
(Finset.univ.filter (fun m : DigitSpace D p => (highDigitCount m : ℝ) ≤ t)).card ≤ 
    p ^ D * exp (-2 * ((D * probHigh p) - t)^2 / D)
```

Steps:
1. Translate between `range (p^D)` and `DigitSpace D p` using `toDigitSpace_bijective`
2. Show `count_high_digits p m D < t` implies `(highDigitCount (toDigitSpace ...) : ℝ) ≤ t` using `highDigitCount_eq`
3. Show `t < D * probHigh p` (needed for the Chernoff bound)
4. Apply the Chernoff bound
5. Show `exp(-2 * ((D * probHigh p) - t)^2 / D) ≤ 1/2^(D/36)` (the exponential to integer bound)
6. Combine to get `≤ p^D / 2^(D/36)`

Step 5 is the hardest. Let me think about this more carefully.

We need: `p^D * exp(-2 * ((D * probHigh p) - t)^2 / D) ≤ p^D / 2^(D/36)`

This is equivalent to: `exp(-2 * ((D * probHigh p) - t)^2 / D) ≤ 1/2^(D/36)`

Which is: `exp(-2 * ((D * probHigh p) - t)^2 / D) ≤ 2^(-(D/36 : ℕ))`

But we're working in ℕ on the right, so we need to be careful. Actually, the RHS is natural number division `p^D / 2^(D/36)`. So we need:

`⌊p^D * exp(...)⌋ ≤ p^D / 2^(D/36)`

Actually, the Chernoff bound gives a ℝ upper bound on a ℕ card. So:
`card ≤ p^D * exp(...)` (as reals)

And we need `card ≤ p^D / 2^(D/36)` (as nats).

So if we can show `p^D * exp(...) ≤ p^D / 2^(D/36)` as reals, then by integrality we're done. But `p^D / 2^(D/36)` in nat is floor division... 

Actually, we can go: `card ≤ p^D * exp(...)` (reals) and `p^D * exp(...) ≤ (p^D / 2^(D/36) : ℝ)` which becomes `exp(...) ≤ 1/2^(D/36)`. But nat division is `⌊p^D / 2^(D/36)⌋`, not exactly `p^D / 2^(D/36)` as reals.

So we need: `(card : ℝ) ≤ p^D * exp(...) ≤ p^D / 2^(D/36)` and since card and `p^D / 2^(D/36)` are both nats, `card ≤ ⌊p^D * exp(...)⌋ ≤ p^D / 2^(D/36)`.

Wait, let me be more careful. We have `card : ℕ` and `p^D * exp(...) : ℝ` where `card ≤ p^D * exp(...)` in ℝ. So `card ≤ ⌊p^D * exp(...)⌋`. If we show `p^D * exp(...) ≤ ↑(p^D / 2^(D/36))`, then `card ≤ ⌊p^D * exp(...)⌋ ≤ p^D / 2^(D/36)`.

But `↑(p^D / 2^(D/36)) ≤ (↑(p^D)) / (↑(2^(D/36)))`, so we'd need the other direction.

Actually, the simplest approach: If `(card : ℝ) ≤ X` and `X ≤ ↑n` for some `n : ℕ`, then `card ≤ n`. Because `↑card ≤ ↑n` implies `card ≤ n`.

So we need `p^D * exp(...) ≤ ↑(p^D / 2^(D/36))`.

Hmm, but `↑(p^D / 2^(D/36))` could be smaller than `(↑p^D) / (↑2^(D/36))` due to floor. So this direction is harder.

Actually, let me think again. The simplest approach: just show `exp(...) ≤ (2^(D/36))⁻¹` as reals, then `p^D * exp(...) ≤ p^D * (2^(D/36))⁻¹ = p^D / 2^(D/36)` as reals. Then cast: if `(card : ℝ) ≤ p^D / 2^(D/36)` as reals, and `p^D / 2^(D/36)` as nat is `⌊(p^D : ℝ) / (2^(D/36) : ℝ)⌋`, then `card ≤ ⌊...⌋`.

Actually, `Nat.div` is floor division, so `↑(a / b) ≤ (↑a) / (↑b)` always holds (Nat.cast_div_le or similar). But we need the other direction: from `(card : ℝ) ≤ (↑(p^D)) / (↑(2^(D/36)))` to `card ≤ p^D / 2^(D/36)`. This is `Nat.le_div_iff_mul_le` or we can use `Nat.cast_le` after `Nat.floor`.

Actually, `Nat.floor_le_div` or something. Let me check:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_floor.lean << 'EOF'
import Mathlib.Data.Nat.Defs
import Mathlib.Order.Defs.Basic

open Nat

-- If (card : ℝ) ≤ (a : ℝ) / (b : ℝ), and card, a, b are ℕ, then card ≤ a / b
-- This is because a / b in ℕ = ⌊(a : ℝ) / (b : ℝ)⌋
-- and card : ℕ with ↑card ≤ ↑a / ↑b means card ≤ ⌊↑a / ↑b⌋ = a / b

#check Nat.cast_le
#check Nat.le_div_iff_mul_le
#check Nat.div_le_iff_le_mul
#check @Nat.le_of_cast_le_cast
EOF
lake env lean /tmp/test_floor.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_floor.lean << 'EOF'
import Mathlib.Analysis.SpecialFunctions.Log.Basic

-- From (card : ℝ) ≤ (a : ℝ) / (b : ℝ) where card a b : ℕ
-- we want card ≤ a / b (nat div)
-- Approach: Nat.cast_le + floor

example (card a b : ℕ) (hb : b > 0) (h : (card : ℝ) ≤ (a : ℝ) / (b : ℝ)) : card ≤ a / b := by
  rw [Nat.le_div_iff_mul_le hb]
  have : (card * b : ℝ) ≤ a := by
    rw [← div_le_iff₀ (by positivity : (b : ℝ) > 0)]
    exact h
  exact_mod_cast this
EOF
lake env lean /tmp/test_floor.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_floor.lean << 'EOF'
import Mathlib.Analysis.SpecialFunctions.Log.Basic

example (card a b : ℕ) (hb : b > 0) (h : (card : ℝ) ≤ (a : ℝ) / (b : ℝ)) : card ≤ a / b := by
  rw [Nat.le_div_iff_mul_le hb]
  have : (card * b : ℝ) ≤ a := by
    rwa [le_div_iff₀ (by positivity : (b : ℝ) > 0)] at h
  exact_mod_cast this
EOF
lake env lean /tmp/test_floor.lean 2>&1
```
Now let me figure out the bijection approach and then the exponential bound. Let me first check what we have for relating the finset filter to the digit space:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_bij.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset Real Erdos728

-- Check that we can relate card of filter on range to card of filter on DigitSpace
variable {p : ℕ} (hp : p.Prime) (D : ℕ)

#check @toDigitSpace_bijective
#check @highDigitCount_eq
#check @count_few_high_digits_bound_chernoff
#check @count_few_high_digits_bound
EOF
lake env lean /tmp/test_bij.lean 2>&1
```
Good. Now let me think about the overall approach. The filter on `range (p^D)` with `count_high_digits p m D < t` can be related to the filter on `Finset.univ (DigitSpace D p)` with `highDigitCount ≤ t - 1` via the bijection.

Let me write the proof step by step:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_proof.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset Real Erdos728

-- First, let me verify probHigh p ≥ 1/3 for p ≥ 3
example (p : ℕ) (hp : p ≥ 3) : probHigh p ≥ 1/3 := by
  unfold probHigh
  rw [ge_iff_le, div_le_div_iff (by norm_num : (0:ℝ) < 3) (by positivity : (0:ℝ) < p)]
  have : p / 2 * 3 ≥ p := by omega
  exact_mod_cast this
EOF
lake env lean /tmp/test_proof.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_proof.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset Real Erdos728

example (p : ℕ) (hp : p ≥ 3) : probHigh p ≥ 1/3 := by
  unfold probHigh
  rw [ge_iff_le, div_le_div_iff₀ (by norm_num : (0:ℝ) < 3) (by positivity : (0:ℝ) < p)]
  push_cast
  have : p / 2 * 3 ≥ p := by omega
  linarith
EOF
lake env lean /tmp/test_proof.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_proof.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset Real Erdos728

example (p : ℕ) (hp : p ≥ 3) : probHigh p ≥ 1/3 := by
  unfold probHigh
  rw [ge_iff_le, div_le_div_iff₀ (by norm_num : (0:ℝ) < 3) (by positivity : (0:ℝ) < p)]
  have : p / 2 * 3 ≥ p := by omega
  have : (↑(p / 2) : ℝ) * 3 ≥ 1 * ↑p := by
    have h1 : (↑(p / 2 * 3) : ℝ) ≥ (↑p : ℝ) := by exact_mod_cast this
    push_cast at h1
    linarith
  linarith
EOF
lake env lean /tmp/test_proof.lean 2>&1
```
Good. Now let me work on the bijection part — relating the filter on `range (p^D)` to the filter on `Finset.univ`:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_proof2.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset Real Erdos728

-- The filter on range(p^D) with count_high_digits < t
-- maps bijectively to the filter on Fin(p^D) with count_high_digits < t
-- which maps bijectively to the filter on DigitSpace D p with highDigitCount < t

-- Step 1: range(p^D) ↔ Fin(p^D)
example (p D : ℕ) :
    ((range (p^D)).filter (fun m => count_high_digits p m D < 3)).card =
    ((Finset.univ : Finset (Fin (p^D))).filter (fun m => count_high_digits p m.val D < 3)).card := by
  rw [← Finset.card_map (Fin.equivSubtype.toEmbedding)]
  sorry
EOF
lake env lean /tmp/test_proof2.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_proof2.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset Real Erdos728

-- Better: use Finset.card_map or equivFin
-- range(p^D) and Fin(p^D) have same cardinality
-- Let me try a simpler approach: just convert range to univ via Fin

-- The key relation: for m : Fin(p^D), count_high_digits p m D = highDigitCount (toDigitSpace hp D m)
-- So we need a bijection between filters

-- Let me try the approach of directly establishing the card equality
-- between filter on range and filter on DigitSpace

-- Actually, the simplest: use Finset.card_bij
example (p D t : ℕ) (hp : Nat.Prime p) :
    ((range (p^D)).filter (fun m => count_high_digits p m D < t)).card =
    ((Finset.univ : Finset (Fin (p^D))).filter (fun m : Fin (p^D) => count_high_digits p m.val D < t)).card := by
  apply Finset.card_nbij (fun m hm => ⟨m, by simp [mem_filter] at hm; exact hm.1⟩)
  · intro m hm; simp [mem_filter] at hm ⊢; exact hm.2
  · intro a ha b hb h; simp at h; exact h
  · intro b hb; simp [mem_filter] at hb ⊢; exact ⟨b.val, ⟨b.isLt, hb⟩, Fin.ext rfl⟩
EOF
lake env lean /tmp/test_proof2.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_proof2.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset Real Erdos728

-- Use Finset.card_bij
example (p D t : ℕ) (hp : Nat.Prime p) :
    ((range (p^D)).filter (fun m => count_high_digits p m D < t)).card =
    ((Finset.univ : Finset (Fin (p^D))).filter (fun m : Fin (p^D) => count_high_digits p m.val D < t)).card := by
  apply Finset.card_bij (fun m _ => (⟨m, by sorry⟩ : Fin (p^D)))
  · sorry
  · sorry
  · sorry
EOF
lake env lean /tmp/test_proof2.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_proof2.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset Real Erdos728

-- Use Finset.card_bij
example (p D t : ℕ) (hp : Nat.Prime p) :
    ((range (p^D)).filter (fun m => count_high_digits p m D < t)).card =
    ((Finset.univ : Finset (Fin (p^D))).filter
      (fun m : Fin (p^D) => count_high_digits p m.val D < t)).card := by
  apply Finset.card_bij (fun m hm => ⟨m, by rw [mem_filter] at hm; exact mem_range.mp hm.1⟩)
  · intro m hm
    rw [mem_filter] at hm ⊢
    exact ⟨mem_univ _, hm.2⟩
  · intro a ha b hb h
    simp at h; exact h
  · intro b hb
    exact ⟨b.val, by rw [mem_filter] at hb ⊢; exact ⟨mem_range.mpr b.isLt, hb.2⟩,
      Fin.ext rfl⟩
EOF
lake env lean /tmp/test_proof2.lean 2>&1
```
Now let me work on the bijection from Fin(p^D) to DigitSpace:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_proof3.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset Real Erdos728

-- Now relate filter on Fin(p^D) to filter on DigitSpace via toDigitSpace
example (p D t : ℕ) (hp : Nat.Prime p) :
    ((Finset.univ : Finset (Fin (p^D))).filter
      (fun m : Fin (p^D) => count_high_digits p m.val D < t)).card =
    ((Finset.univ : Finset (DigitSpace D p)).filter
      (fun m : DigitSpace D p => highDigitCount m < t)).card := by
  have hbij := toDigitSpace_bijective hp D
  apply Finset.card_bij (fun m _ => toDigitSpace hp D m)
  · intro m hm
    rw [mem_filter] at hm ⊢
    constructor
    · exact mem_univ _
    · rw [highDigitCount_eq hp D m]; exact hm.2
  · intro a _ b _ h
    exact hbij.1 h
  · intro b _
    obtain ⟨a, ha⟩ := hbij.2 b
    exact ⟨a, by simp [mem_filter, ← ha, highDigitCount_eq], ha⟩
EOF
lake env lean /tmp/test_proof3.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_proof3.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset Real Erdos728

example (p D t : ℕ) (hp : Nat.Prime p) :
    ((Finset.univ : Finset (Fin (p^D))).filter
      (fun m : Fin (p^D) => count_high_digits p m.val D < t)).card =
    ((Finset.univ : Finset (DigitSpace D p)).filter
      (fun m : DigitSpace D p => highDigitCount m < t)).card := by
  have hbij := toDigitSpace_bijective hp D
  apply Finset.card_bij (fun m _ => toDigitSpace hp D m)
  · intro m hm
    rw [mem_filter] at hm ⊢
    constructor
    · exact mem_univ _
    · rw [highDigitCount_eq hp D m]; exact hm.2
  · intro a _ b _ h
    exact hbij.1 h
  · intro b _
    obtain ⟨a, ha⟩ := hbij.2 b
    refine ⟨a, ?_, ha⟩
    rw [mem_filter]
    constructor
    · exact mem_univ _
    · rw [← highDigitCount_eq hp D a, ha]; 
      simp [mem_filter] at *
      assumption
EOF
lake env lean /tmp/test_proof3.lean 2>&1
```
Now let me work on the exponential bound. The key inequality is:

For `p ≥ 3`, `probHigh p ≥ 1/3`, so `D * probHigh p ≥ D/3`. With `t ≤ D/6`:
- `D * probHigh p - t ≥ D/3 - D/6 = D/6`
- Exponent: `-2 * (D/6)^2 / D = -D/18`
- Need: `exp(-D/18) ≤ 2^(-D/36) = (1/2)^(D/36)`
- Equiv: `exp(-1/18) ≤ 2^(-1/36)` per unit of D
- Equiv: `exp(-1/18)^36 ≤ exp(-1/18)^36 ≤ 1/2`, i.e., `exp(-2) ≤ 1/2`
- Actually better: `exp(-D/18) ≤ 2^(-D/36)` iff `D/18 ≥ (D/36) * ln 2` iff `1/18 ≥ ln(2)/36` iff `2 ≥ ln 2`, which is clearly true.

But we're dealing with natural number `D/36` (floor division). So the actual target is `exp(-D/18) ≤ (1/2)^(D/36 : ℕ)`.

Since `D/36 ≤ D/36` (real), we need: `exp(-D/18) ≤ 2^(-(D/36 : ℕ))`. 

Since `(D/36 : ℕ) ≤ D/36` (real), and `2^(-x)` is decreasing, `2^(-(D/36 : ℕ)) ≥ 2^(-D/36)`. So it suffices to show `exp(-D/18) ≤ 2^(-D/36)` (with real D/36).

Actually, let me be very careful. We need `exp(-D/18) ≤ (1/2)^(D/36 : ℕ)` where `D/36 : ℕ` is nat division. Since `(D/36 : ℕ) ≤ D/36` (real), and `(1/2)^x` is decreasing in x, we get `(1/2)^(D/36 : ℕ) ≥ (1/2)^(D/36 : ℝ)`. So it suffices to show `exp(-D/18) ≤ (1/2)^(D/36 : ℝ) = 2^(-D/36 : ℝ)`.

Now `2^(-D/36) = exp(-(D/36) * ln 2)`. So we need `exp(-D/18) ≤ exp(-(D/36) * ln 2)`, i.e., `-D/18 ≤ -(D/36) * ln 2`, i.e., `(D/36) * ln 2 ≤ D/18`, i.e., `ln 2 ≤ 2`. And `ln 2 < 1 ≤ 2`. Done.

But actually, in the Chernoff bound, the exponent is `-2 * ((D * probHigh p) - t)^2 / D`, with `t : ℝ`. Let me be more careful about how we set `t`.

The lemma says `t : ℕ` and `t ≤ D/6`. We want to apply the Chernoff bound with `t' = (t : ℝ)` (or maybe `t' = (t - 1 : ℝ)` since the original filter uses `< t` but Chernoff uses `≤ t'`).

Since filter has `count_high_digits p m D < t` which is `count_high_digits p m D ≤ t - 1` (for natural numbers), and the Chernoff bound has `highDigitCount m ≤ t'` (reals), we can use `t' = t - 1` or just `t' = t` (since `< t` for nats implies `≤ t - 1` implies `(· : ℝ) ≤ t - 1 < t`).

Actually, looking at the Chernoff bound signature more carefully:

```
count_few_high_digits_bound_chernoff (t : ℝ) (ht : t < (D * probHigh p)) :
    (Finset.univ.filter (fun m : DigitSpace D p => (highDigitCount m : ℝ) ≤ t)).card ≤ ...
```

And our filter is `highDigitCount m < t` (nat). So `highDigitCount m < t` implies `(highDigitCount m : ℝ) ≤ t - 1 ≤ t`. We can use the Chernoff bound with `t' = (t : ℝ)` (or `t - 1`), but the filter sets differ. Using `t'` = `(t : ℝ)`:

`{m | highDigitCount m < t} ⊆ {m | (highDigitCount m : ℝ) ≤ t}`

So `card {m | highDigitCount m < t} ≤ card {m | (highDigitCount m : ℝ) ≤ t}`.

But actually, wait — `< t` in nat is `≤ t - 1` in nat, and `(highDigitCount m : ℝ) ≤ ↑(t - 1) ≤ ↑t`. So using `t' = ↑t` would work. But actually, `{m | highDigitCount m < t}` = `{m | (highDigitCount m : ℝ) < t}` since cast preserves `<`. And `{m | (highDigitCount m : ℝ) < t} ⊆ {m | (highDigitCount m : ℝ) ≤ t}`. So we can use `t' = (t : ℝ)`.

But wait, we need `t' < D * probHigh p`. We have `t ≤ D/6` and `probHigh p ≥ 1/3`, so `D * probHigh p ≥ D/3 ≥ 2 * D/6 ≥ 2t ≥ t + 1 > t` (when `t ≥ 1`). Actually for `t = 0` the result is trivially true (empty filter ≤ anything). For `t ≥ 1`, we need `(t : ℝ) < D * probHigh p`. Since `t ≤ D/6` and `D * probHigh p ≥ D/3`, we need `D/6 < D/3`, which is true for `D ≥ 1`. For `D = 0`, `t ≤ 0/6 = 0` so `t = 0` and the filter is empty.

Actually I realize it may also be the case that `D/6 = 0` (when `D < 6`), in which case `t = 0` and the filter is empty. Let me handle those edge cases.

Let me also think about how to handle `< t` vs `≤ t`:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_proof4.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset Real Erdos728

-- Key helper: subset relationship between < t and ≤ (t : ℝ)
-- in the DigitSpace world
example (p D t : ℕ) :
    ((Finset.univ : Finset (DigitSpace D p)).filter
      (fun m : DigitSpace D p => highDigitCount m < t)) ⊆
    ((Finset.univ : Finset (DigitSpace D p)).filter
      (fun m : DigitSpace D p => (highDigitCount m : ℝ) ≤ (t : ℝ))) := by
  apply Finset.filter_subset_filter
  · exact Finset.Subset.rfl
  · intro m hm
    exact_mod_cast Nat.lt_add_one_iff.mp (Nat.lt_add_of_lt_right hm)
EOF
lake env lean /tmp/test_proof4.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_proof4.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset Real Erdos728

example (p D t : ℕ) :
    ((Finset.univ : Finset (DigitSpace D p)).filter
      (fun m : DigitSpace D p => highDigitCount m < t)) ⊆
    ((Finset.univ : Finset (DigitSpace D p)).filter
      (fun m : DigitSpace D p => (highDigitCount m : ℝ) ≤ (t : ℝ))) := by
  intro m
  simp only [mem_filter, mem_univ, true_and]
  intro h
  exact_mod_cast le_of_lt h
EOF
lake env lean /tmp/test_proof4.lean 2>&1
```
Good. Now let me work on the exponential bound part. This is the hardest step.
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_exp.lean << 'EOF'
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real

-- We need: exp(-D/18) ≤ (1/2)^(D/36 : ℕ) for natural D
-- Strategy: (1/2)^(D/36 : ℕ) = exp(-(D/36 : ℕ) * ln 2)
-- exp(-D/18) ≤ exp(-(D/36 : ℕ) * ln 2)
-- iff -D/18 ≤ -(D/36 : ℕ) * ln 2
-- iff (D/36 : ℕ) * ln 2 ≤ D/18

-- Key fact: ln 2 ≤ 1, so (D/36 : ℕ) * ln 2 ≤ (D/36 : ℕ) ≤ D/36 ≤ D/18
-- Wait, D/36 is NOT ≤ D/18 in general! D/36 < D/18 iff 18 < 36, but (D/36 : ℕ) ≤ D/36 ≤ D/18
-- So (D/36 : ℕ) * ln 2 ≤ (D/36 : ℕ) * 1 ≤ D/36 ≤ D/18. Yes!

-- Step 1: ln 2 ≤ 1
example : Real.log 2 ≤ 1 := by
  rw [← Real.log_exp 1]
  apply Real.log_le_log (by norm_num : (0:ℝ) < 2)
  calc (2:ℝ) ≤ 1 + 1 := by norm_num
    _ ≤ Real.exp 1 := add_one_le_exp 1

-- Step 2: (D/36 : ℕ) ≤ D/36 (real)
example (D : ℕ) : (↑(D / 36) : ℝ) ≤ (D : ℝ) / 36 := by
  exact_mod_cast Nat.div_le_self D 36  -- wrong, this gives D/36 ≤ D
  
EOF
lake env lean /tmp/test_exp.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_exp.lean << 'EOF'
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real

-- (D/36 : ℕ) ≤ D/36 (real)
example (D : ℕ) : (↑(D / 36) : ℝ) ≤ (D : ℝ) / 36 := by
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 36)]
  have := Nat.div_mul_le_self D 36
  exact_mod_cast this

-- (D/36 : ℕ) * ln 2 ≤ D/18
-- Since (D/36 : ℕ) * ln 2 ≤ (D/36 : ℕ) * 1 ≤ D/36 ≤ D/18
-- Wait, D/36 ≤ D/18 is correct since 18 ≤ 36, so D/36 = D/(2*18) ≤ D/18

-- Hmm, actually we need the full bound. Let me think again.
-- We need: exp(-2 * ((D * probHigh p) - t)^2 / D) ≤ 1/2^(D/36)
-- With probHigh p ≥ 1/3 and t ≤ D/6:
-- D * probHigh p - t ≥ D/3 - D/6 = D/6
-- So exponent ≤ -2 * (D/6)^2 / D = -2*D^2/(36*D) = -D/18  (for D > 0)
-- So we need exp(-D/18) ≤ 2^(-(D/36 : ℕ))
-- 
-- Now 2^(-(D/36 : ℕ)) = exp(-(D/36 : ℕ) * ln 2)
-- So we need -D/18 ≤ -(D/36 : ℕ) * ln 2
-- i.e., (D/36 : ℕ) * ln 2 ≤ D/18
-- Since ln 2 ≤ 1 and (D/36 : ℕ) ≤ D/36 (real), we get:
-- (D/36 : ℕ) * ln 2 ≤ D/36 * 1 = D/36 ≤ D/18
-- Yes! This works since D/36 ≤ D/18 (for D ≥ 0).

example (D : ℕ) : (D : ℝ) / 36 ≤ (D : ℝ) / 18 := by
  apply div_le_div_of_nonneg_left (by positivity : (0:ℝ) < D + 1) (by norm_num) (by norm_num)
  -- hmm this is wrong approach
  sorry
EOF
lake env lean /tmp/test_exp.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_exp.lean << 'EOF'
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real

example (D : ℕ) : (D : ℝ) / 36 ≤ (D : ℝ) / 18 := by
  apply div_le_div_of_nonneg_left _ (by norm_num) (by norm_num)
  exact_mod_cast Nat.zero_le D
  -- oops, div_le_div_of_nonneg_left needs a > 0 
  sorry
EOF
lake env lean /tmp/test_exp.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_exp.lean << 'EOF'
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real

example (D : ℕ) : (D : ℝ) / 36 ≤ (D : ℝ) / 18 := by
  apply div_le_div_of_nonneg_left _ (by norm_num) (by norm_num)
  exact_mod_cast Nat.zero_le D
EOF
lake env lean /tmp/test_exp.lean 2>&1
```
Now let me put together the exponential bound step:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_exp2.lean << 'EOF'
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real

-- Main inequality: exp(-D/18) ≤ (1/2)^(D/36 : ℕ)
-- We'll prove this step by step

-- Step 1: (1/2)^n = exp(-n * ln 2)
#check Real.rpow_natCast  
#check Real.exp_mul_rpow

-- Actually let me use a different approach
-- (1/2 : ℝ)^n = 1 / 2^n, and we want exp(-D/18) ≤ 1/2^(D/36)
-- equivalent: 2^(D/36) ≤ exp(D/18)
-- equivalent: exp((D/36) * ln 2) ≤ exp(D/18)  
-- equivalent: (D/36) * ln 2 ≤ D/18
-- equivalent: ln 2 ≤ 2 (dividing by D/36, assuming D > 0; for D = 0 trivial)

-- But working with ℕ exponents is easier. Let's use pow instead of rpow.

example (D : ℕ) : exp (-(D : ℝ) / 18) ≤ ((1 : ℝ) / 2)^(D/36) := by
  by_cases hD : D = 0
  · simp [hD]
  · -- (1/2)^(D/36) ≥ exp(-(D/36) * ln 2) ≥ exp(-D/18)
    -- Use: (1/2)^n = exp(n * ln(1/2)) = exp(-n * ln 2)
    have hln2 : Real.log 2 ≤ 1 := by
      rw [← Real.log_exp 1]
      apply Real.log_le_log (by norm_num : (0:ℝ) < 2)
      linarith [add_one_le_exp 1]
    have hln2_pos : 0 < Real.log 2 := by positivity
    -- Convert pow to exp
    have h_pow : ((1:ℝ)/2)^(D/36) = exp (-(↑(D/36) * Real.log 2)) := by
      rw [one_div, inv_pow, ← exp_nat_mul, ← exp_neg]
      congr 1
      rw [neg_mul, ← Real.log_inv, inv_eq_one_div]
      rfl
    sorry
EOF
lake env lean /tmp/test_exp2.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_exp2.lean << 'EOF'
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real

#check @Real.exp_natMul
-- exp_natMul : rexp (↑n * x) = rexp x ^ n
#check @Real.rpow_natCast
-- For 2^n as exp:
-- 2^n = exp(n * ln 2) 
-- (1/2)^n = exp(-n * ln 2) = (exp(ln 2))^(-n)... 
-- Actually simpler: 2 = exp(ln 2), so 2^n = exp(ln 2)^n = exp(n * ln 2)

example (n : ℕ) : (2 : ℝ)^n = exp (↑n * Real.log 2) := by
  rw [← exp_natMul, Real.exp_log (by norm_num : (0:ℝ) < 2)]

example (n : ℕ) : ((2 : ℝ)^n)⁻¹ = exp (-(↑n * Real.log 2)) := by
  rw [exp_neg, ← exp_natMul, Real.exp_log (by norm_num : (0:ℝ) < 2)]
EOF
lake env lean /tmp/test_exp2.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && grep -r "exp_nat" .lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/ --include="*.lean" | head -5
grep -r "exp.*natMul\|exp.*mul.*nat\|exp_nsmul" .lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ --include="*.lean" -l | head -5
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_exp3.lean << 'EOF'
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real

#check @exp_nsmul
-- Maybe this doesn't exist. Let me try a different approach.
-- 2^n = exp(n * log 2) can be proved by induction

-- Or: use rpow
-- (2 : ℝ) ^ (n : ℕ) = (2 : ℝ) ^ ((n : ℕ) : ℝ) via rpow_natCast
-- and x ^ y = exp(y * log x) for x > 0

#check @Real.rpow_def_of_pos
-- rpow_def_of_pos : 0 < x → x ^ y = exp (log x * y)

example (n : ℕ) : (2 : ℝ) ^ n = exp (↑n * Real.log 2) := by
  rw [← rpow_natCast]
  rw [rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
  ring_nf
EOF
lake env lean /tmp/test_exp3.lean 2>&1
```
Now let me build the full exponential bound lemma:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_exp4.lean << 'EOF'
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real

-- Main bound: exp(-D/18) ≤ (1/2)^(D/36)
-- Strategy: show both sides as exp(...) and compare exponents

lemma exp_bound_aux (D : ℕ) : exp (-(D : ℝ) / 18) ≤ ((2 : ℝ)^(D/36))⁻¹ := by
  -- Write RHS as exp(-(D/36) * log 2)
  have h2_pow : ((2 : ℝ)^(D/36))⁻¹ = exp (-(↑(D/36) * Real.log 2)) := by
    rw [exp_neg]
    congr 1
    rw [← rpow_natCast]
    rw [rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
    ring_nf
  rw [h2_pow]
  rw [exp_le_exp]
  -- Goal: -D/18 ≤ -(D/36 : ℕ) * log 2
  -- i.e., (D/36 : ℕ) * log 2 ≤ D/18
  linarith [show Real.log 2 ≤ 1 from by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (by norm_num) (by linarith [add_one_le_exp 1]),
    show (↑(D/36) : ℝ) ≤ (D : ℝ) / 18 from by
      have h1 : (↑(D/36) : ℝ) ≤ (D : ℝ) / 36 := by
        rw [le_div_iff₀ (by norm_num : (0:ℝ) < 36)]
        exact_mod_cast Nat.div_mul_le_self D 36
      linarith [show (D : ℝ) / 36 ≤ (D : ℝ) / 18 from by
        apply div_le_div_of_nonneg_left _ (by norm_num) (by norm_num)
        exact_mod_cast Nat.zero_le D],
    show (↑(D/36) : ℝ) ≥ 0 from by exact_mod_cast Nat.zero_le _,
    show Real.log 2 > 0 from by positivity]
EOF
lake env lean /tmp/test_exp4.lean 2>&1
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_exp4.lean << 'EOF'
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real

lemma exp_bound_aux (D : ℕ) : exp (-(D : ℝ) / 18) ≤ ((2 : ℝ)^(D/36))⁻¹ := by
  have h2_pow : ((2 : ℝ)^(D/36))⁻¹ = exp (-(↑(D/36) * Real.log 2)) := by
    rw [exp_neg]
    congr 1
    rw [← rpow_natCast]
    rw [rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
    ring_nf
  rw [h2_pow, exp_le_exp]
  -- Goal: -D/18 ≤ -(D/36 : ℕ) * log 2
  -- Equiv: (D/36 : ℕ) * log 2 ≤ D/18
  have hln2 : Real.log 2 ≤ 1 := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (by norm_num) (by linarith [add_one_le_exp 1])
  have hln2_pos : 0 < Real.log 2 := by positivity
  have h_nat_div : (↑(D/36) : ℝ) ≤ (D : ℝ) / 36 := by
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 36)]
    exact_mod_cast Nat.div_mul_le_self D 36
  have h_36_18 : (D : ℝ) / 36 ≤ (D : ℝ) / 18 := by
    apply div_le_div_of_nonneg_left _ (by norm_num) (by norm_num)
    exact_mod_cast Nat.zero_le D
  -- (D/36 : ℕ) * log 2 ≤ (D/36 : ℕ) * 1 ≤ D/36 ≤ D/18
  have h1 : (↑(D/36) : ℝ) * Real.log 2 ≤ ↑(D/36) := by
    calc (↑(D/36) : ℝ) * Real.log 2 ≤ ↑(D/36) * 1 := by
          apply mul_le_mul_of_nonneg_left hln2 (by exact_mod_cast Nat.zero_le _)
      _ = ↑(D/36) := by ring
  -- Chain: (D/36) * log 2 ≤ D/36 ≤ D/36 ≤ D/18
  -- so -D/18 ≤ -(D/36) * log 2
  nlinarith
EOF
lake env lean /tmp/test_exp4.lean 2>&1
```
Excellent! Now let me put together the full proof. Let me also verify the Chernoff exponent bound:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_exp5.lean << 'EOF'
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Erdos.Lemma3Common

open Real Erdos728

-- For p ≥ 3, probHigh p ≥ 1/3
-- For t ≤ D/6, D * probHigh p - t ≥ D/3 - D/6 = D/6
-- So -2 * (D*probHigh p - t)^2 / D ≤ -2*(D/6)^2/D = -D/18

lemma chernoff_exponent_bound (D : ℕ) (p : ℕ) (hp_ge_3 : p ≥ 3) (t : ℕ) (ht : t ≤ D / 6) 
    (hD : D > 0) :
    -2 * ((↑D * probHigh p - ↑t)^2) / (↑D : ℝ) ≤ -(↑D : ℝ) / 18 := by
  -- probHigh p ≥ 1/3
  have h_prob : probHigh p ≥ 1/3 := by
    unfold probHigh
    rw [ge_iff_le, div_le_div_iff₀ (by norm_num : (0:ℝ) < 3) (by positivity : (0:ℝ) < p)]
    have : p / 2 * 3 ≥ p := by omega
    have : (↑(p / 2 * 3) : ℝ) ≥ (↑p : ℝ) := by exact_mod_cast this
    push_cast at this
    linarith
  -- D * probHigh p ≥ D/3
  have h_mu : (↑D : ℝ) * probHigh p ≥ ↑D / 3 := by nlinarith [show (D:ℝ) ≥ 0 from by positivity]
  -- t ≤ D/6 as reals
  have h_t : (↑t : ℝ) ≤ ↑D / 6 := by
    have := Nat.div_mul_le_self D 6
    have : t * 6 ≤ D := by omega
    have : (↑(t * 6) : ℝ) ≤ (↑D : ℝ) := by exact_mod_cast this
    push_cast at this; linarith
  -- D * probHigh p - t ≥ D/3 - D/6 = D/6
  have h_gap : ↑D * probHigh p - ↑t ≥ ↑D / 6 := by linarith
  -- (gap)^2 ≥ (D/6)^2
  have h_sq : (↑D * probHigh p - ↑t)^2 ≥ ((↑D : ℝ) / 6)^2 := by
    apply sq_le_sq' <;> linarith
  -- -2 * gap^2 / D ≤ -2 * (D/6)^2 / D = -D/18
  have hD_pos : (↑D : ℝ) > 0 := by exact_mod_cast hD
  have h1 : -2 * (↑D * probHigh p - ↑t)^2 / (↑D : ℝ) ≤ -2 * ((↑D : ℝ) / 6)^2 / ↑D := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hD_pos)
    · nlinarith
  calc -2 * (↑D * probHigh p - ↑t)^2 / ↑D 
      ≤ -2 * ((↑D : ℝ) / 6)^2 / ↑D := h1
    _ = -(↑D : ℝ) / 18 := by field_simp; ring
EOF
lake env lean /tmp/test_exp5.lean 2>&1
```
Now let me put the entire proof together. I need to handle:

1. The edge case where `D = 0` or `t = 0` 
2. The bijection between `range (p^D)` and `DigitSpace D p`
3. The filter subset relationship
4. The Chernoff bound application
5. The exponential bound
6. Converting from real to nat
```bash
$ cd /home/jarred/code/erdos-728b && tm update erdos728b-9pu --status "Writing the full proof for count_few_high_digits"
```

```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_full.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset Real Erdos728

-- Test the full proof
set_option maxHeartbeats 800000

lemma count_few_high_digits' {p : ℕ} (hp : p.Prime) (D : ℕ) (t : ℕ) (ht : t ≤ D/6) (hp_ge_3 : p ≥ 3) :
    ((range (p^D)).filter (fun m => count_high_digits p m D < t)).card ≤ p^D / 2^(D/36) := by
  -- Handle trivial case t = 0
  by_cases ht0 : t = 0
  · simp [ht0]
  -- Now t ≥ 1, hence D ≥ 6 (since t ≤ D/6 and t ≥ 1 implies D/6 ≥ 1 implies D ≥ 6)
  have ht_pos : t ≥ 1 := Nat.pos_of_ne_zero ht0
  have hD_ge_6 : D ≥ 6 := by omega
  have hD_pos : D > 0 := by omega
  -- Step 1: Relate range(p^D) filter to DigitSpace filter
  -- First, range(p^D) → Fin(p^D)
  have h_card_eq_fin :
      ((range (p^D)).filter (fun m => count_high_digits p m D < t)).card =
      ((Finset.univ : Finset (Fin (p^D))).filter
        (fun m : Fin (p^D) => count_high_digits p m.val D < t)).card := by
    apply Finset.card_bij (fun m hm => ⟨m, by rw [mem_filter] at hm; exact mem_range.mp hm.1⟩)
    · intro m hm; rw [mem_filter] at hm ⊢; exact ⟨mem_univ _, hm.2⟩
    · intro a _ b _ h; simp at h; exact h
    · intro b _; exact ⟨b.val, by rw [mem_filter]; exact ⟨mem_range.mpr b.isLt, by simpa [mem_filter] using ‹_›⟩, Fin.ext rfl⟩
  -- Then, Fin(p^D) → DigitSpace via toDigitSpace
  have h_card_eq_ds :
      ((Finset.univ : Finset (Fin (p^D))).filter
        (fun m : Fin (p^D) => count_high_digits p m.val D < t)).card =
      ((Finset.univ : Finset (DigitSpace D p)).filter
        (fun m : DigitSpace D p => highDigitCount m < t)).card := by
    have hbij := toDigitSpace_bijective hp D
    apply Finset.card_bij (fun m _ => toDigitSpace hp D m)
    · intro m hm; rw [mem_filter] at hm ⊢
      exact ⟨mem_univ _, by rw [highDigitCount_eq hp D m]; exact hm.2⟩
    · intro a _ b _ h; exact hbij.1 h
    · intro b _; obtain ⟨a, ha⟩ := hbij.2 b
      refine ⟨a, ?_, ha⟩; rw [mem_filter]
      constructor; exact mem_univ _
      rw [← highDigitCount_eq hp D a, ha]; simpa [mem_filter] using ‹_›
  -- Step 2: The DigitSpace filter with < t is a subset of filter with ≤ (t : ℝ)  
  have h_subset :
      ((Finset.univ : Finset (DigitSpace D p)).filter
        (fun m : DigitSpace D p => highDigitCount m < t)) ⊆
      ((Finset.univ : Finset (DigitSpace D p)).filter
        (fun m : DigitSpace D p => (highDigitCount m : ℝ) ≤ (t : ℝ))) := by
    intro m; simp only [mem_filter, mem_univ, true_and]
    intro h; exact_mod_cast le_of_lt h
  -- Step 3: Show t < D * probHigh p (needed for Chernoff)
  have h_prob_ge : probHigh p ≥ 1/3 := by
    unfold probHigh
    rw [ge_iff_le, div_le_div_iff₀ (by norm_num : (0:ℝ) < 3) (by positivity : (0:ℝ) < p)]
    have : p / 2 * 3 ≥ p := by omega
    have : (↑(p / 2 * 3) : ℝ) ≥ (↑p : ℝ) := by exact_mod_cast this
    push_cast at this; linarith
  have h_t_lt : (t : ℝ) < ↑D * probHigh p := by
    have : (↑t : ℝ) ≤ ↑D / 6 := by
      have : t * 6 ≤ D := by omega
      have : (↑(t * 6) : ℝ) ≤ (↑D : ℝ) := by exact_mod_cast this
      push_cast at this; linarith
    have : (↑D : ℝ) / 6 < ↑D * probHigh p := by
      have : (↑D : ℝ) / 6 < ↑D / 3 := by
        apply div_lt_div_of_pos_left (by exact_mod_cast hD_pos : (0:ℝ) < ↑D) (by norm_num) (by norm_num)
      linarith [show ↑D / 3 ≤ ↑D * probHigh p from by nlinarith [show (D:ℝ) ≥ 0 from by positivity]]
    linarith
  -- Step 4: Apply Chernoff bound
  have hne : NeZero p := ⟨Nat.Prime.ne_zero hp⟩
  have h_chernoff := @count_few_high_digits_bound_chernoff D p hne (↑t) h_t_lt
  -- Step 5: Bound the exponent
  -- -2 * (D*probHigh p - t)^2 / D ≤ -D/18
  have h_exp_bound : exp (-2 * ((↑D * probHigh p - ↑t)^2) / (↑D : ℝ)) ≤ ((2 : ℝ)^(D/36))⁻¹ := by
    -- First show exponent ≤ -D/18
    have h_exp_le : -2 * ((↑D * probHigh p - ↑t)^2) / (↑D : ℝ) ≤ -(↑D : ℝ) / 18 := by
      have h_gap : ↑D * probHigh p - ↑t ≥ ↑D / 6 := by
        have h_t_le : (↑t : ℝ) ≤ ↑D / 6 := by
          have : t * 6 ≤ D := by omega
          have : (↑(t * 6) : ℝ) ≤ (↑D : ℝ) := by exact_mod_cast this
          push_cast at this; linarith
        nlinarith [show (D:ℝ) ≥ 0 from by positivity]
      have h_sq : (↑D * probHigh p - ↑t)^2 ≥ ((↑D : ℝ) / 6)^2 := by
        apply sq_le_sq' <;> linarith
      have hD_r : (↑D : ℝ) > 0 := by exact_mod_cast hD_pos
      have h1 : -2 * (↑D * probHigh p - ↑t)^2 / ↑D ≤ -2 * ((↑D : ℝ) / 6)^2 / ↑D := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hD_r); nlinarith
      calc -2 * (↑D * probHigh p - ↑t)^2 / ↑D 
          ≤ -2 * ((↑D : ℝ) / 6)^2 / ↑D := h1
        _ = -(↑D : ℝ) / 18 := by field_simp; ring
    -- Then show exp(-D/18) ≤ (2^(D/36))⁻¹ 
    calc exp (-2 * ((↑D * probHigh p - ↑t)^2) / ↑D)
        ≤ exp (-(↑D : ℝ) / 18) := by rw [exp_le_exp]; exact h_exp_le
      _ ≤ ((2 : ℝ)^(D/36))⁻¹ := by
          -- (2^(D/36))⁻¹ = exp(-(D/36)*ln 2)
          have h2_pow : ((2 : ℝ)^(D/36))⁻¹ = exp (-(↑(D/36) * Real.log 2)) := by
            rw [exp_neg]; congr 1
            rw [← rpow_natCast]; rw [rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]; ring_nf
          rw [h2_pow, exp_le_exp]
          have hln2 : Real.log 2 ≤ 1 := by
            rw [← Real.log_exp 1]
            exact Real.log_le_log (by norm_num) (by linarith [add_one_le_exp 1])
          have h_nat_div : (↑(D/36) : ℝ) ≤ (D : ℝ) / 18 := by
            have h1 : (↑(D/36) : ℝ) ≤ (D : ℝ) / 36 := by
              rw [le_div_iff₀ (by norm_num : (0:ℝ) < 36)]
              exact_mod_cast Nat.div_mul_le_self D 36
            linarith [show (D : ℝ) / 36 ≤ (D : ℝ) / 18 from by
              apply div_le_div_of_nonneg_left _ (by norm_num) (by norm_num)
              exact_mod_cast Nat.zero_le D]
          nlinarith [show (↑(D/36) : ℝ) ≥ 0 from by exact_mod_cast Nat.zero_le _]
  -- Step 6: Combine all bounds
  -- card ≤ chernoff_card ≤ p^D * exp(...) ≤ p^D * (2^(D/36))⁻¹ = p^D / 2^(D/36)
  rw [h_card_eq_fin, h_card_eq_ds]
  -- card of < t filter ≤ card of ≤ t filter
  have h_card_le := card_le_card h_subset
  -- chernoff gives: card of ≤ t filter ≤ p^D * exp(...)
  -- Then p^D * exp(...) ≤ p^D / 2^(D/36)
  -- Combined: card ≤ p^D / 2^(D/36)
  apply Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero (by positivity)).mp
  sorry
EOF
lake env lean /tmp/test_full.lean 2>&1
```
Good progress. Let me fix the issues:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_full2.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset Real Erdos728

set_option maxHeartbeats 800000

lemma count_few_high_digits' {p : ℕ} (hp : p.Prime) (D : ℕ) (t : ℕ) (ht : t ≤ D/6) (hp_ge_3 : p ≥ 3) :
    ((range (p^D)).filter (fun m => count_high_digits p m D < t)).card ≤ p^D / 2^(D/36) := by
  -- Handle trivial case t = 0
  by_cases ht0 : t = 0
  · simp [ht0]
  have ht_pos : t ≥ 1 := Nat.pos_of_ne_zero ht0
  have hD_ge_6 : D ≥ 6 := by omega
  have hD_pos : D > 0 := by omega
  -- Step 1: Relate range(p^D) filter to DigitSpace filter
  have h_card_eq_fin :
      ((range (p^D)).filter (fun m => count_high_digits p m D < t)).card =
      ((Finset.univ : Finset (Fin (p^D))).filter
        (fun m : Fin (p^D) => count_high_digits p m.val D < t)).card := by
    apply Finset.card_bij (fun m hm => ⟨m, by rw [mem_filter] at hm; exact mem_range.mp hm.1⟩)
    · intro m hm; rw [mem_filter] at hm ⊢; exact ⟨mem_univ _, hm.2⟩
    · intro a _ b _ h; simp at h; exact h
    · intro b hb
      refine ⟨b.val, ?_, Fin.ext rfl⟩
      rw [mem_filter]; constructor
      · exact mem_range.mpr b.isLt
      · rw [mem_filter] at hb; exact hb.2
  have h_card_eq_ds :
      ((Finset.univ : Finset (Fin (p^D))).filter
        (fun m : Fin (p^D) => count_high_digits p m.val D < t)).card =
      ((Finset.univ : Finset (DigitSpace D p)).filter
        (fun m : DigitSpace D p => highDigitCount m < t)).card := by
    have hbij := toDigitSpace_bijective hp D
    apply Finset.card_bij (fun m _ => toDigitSpace hp D m)
    · intro m hm; rw [mem_filter] at hm ⊢
      exact ⟨mem_univ _, by rw [highDigitCount_eq hp D m]; exact hm.2⟩
    · intro a _ b _ h; exact hbij.1 h
    · intro b hb; obtain ⟨a, ha⟩ := hbij.2 b
      refine ⟨a, ?_, ha⟩; rw [mem_filter]
      constructor; · exact mem_univ _
      · rw [mem_filter] at hb; rw [← highDigitCount_eq hp D a, ha]; exact hb.2
  -- Step 2: Filter subset
  have h_subset :
      ((Finset.univ : Finset (DigitSpace D p)).filter
        (fun m : DigitSpace D p => highDigitCount m < t)) ⊆
      ((Finset.univ : Finset (DigitSpace D p)).filter
        (fun m : DigitSpace D p => (highDigitCount m : ℝ) ≤ (t : ℝ))) := by
    intro m; simp only [mem_filter, mem_univ, true_and]
    intro h; exact_mod_cast le_of_lt h
  -- Step 3: probHigh p ≥ 1/3 and t < D * probHigh p
  have h_prob_ge : probHigh p ≥ 1/3 := by
    unfold probHigh
    rw [ge_iff_le, div_le_div_iff₀ (by norm_num : (0:ℝ) < 3) (by positivity : (0:ℝ) < p)]
    have : p / 2 * 3 ≥ p := by omega
    have : (↑(p / 2 * 3) : ℝ) ≥ (↑p : ℝ) := by exact_mod_cast this
    push_cast at this; linarith
  have h_t_lt : (t : ℝ) < ↑D * probHigh p := by
    have ht_le : (↑t : ℝ) ≤ ↑D / 6 := by
      have : t * 6 ≤ D := by omega
      have : (↑(t * 6) : ℝ) ≤ (↑D : ℝ) := by exact_mod_cast this
      push_cast at this; linarith
    have : (↑D : ℝ) / 6 < ↑D / 3 := by
      apply div_lt_div_of_pos_left (by exact_mod_cast hD_pos : (0:ℝ) < ↑D) (by norm_num) (by norm_num)
    have : ↑D / 3 ≤ ↑D * probHigh p := by nlinarith [show (D:ℝ) ≥ 0 from by positivity]
    linarith
  -- Step 4: Apply Chernoff
  have hne : NeZero p := ⟨Nat.Prime.ne_zero hp⟩
  have h_chernoff := @count_few_high_digits_bound_chernoff D p hne (↑t) h_t_lt
  -- Step 5: Bound exponent
  have h_exp_bound : exp (-2 * ((↑D * probHigh p - ↑t)^2) / (↑D : ℝ)) ≤ ((2 : ℝ)^(D/36))⁻¹ := by
    have h_exp_le : -2 * ((↑D * probHigh p - ↑t)^2) / (↑D : ℝ) ≤ -(↑D : ℝ) / 18 := by
      have h_gap : ↑D * probHigh p - ↑t ≥ ↑D / 6 := by
        have : (↑t : ℝ) ≤ ↑D / 6 := by
          have : t * 6 ≤ D := by omega
          exact_mod_cast show (↑(t * 6) : ℝ) ≤ ↑D from by exact_mod_cast (by omega : t * 6 ≤ D)
        nlinarith [show (D:ℝ) ≥ 0 from by positivity]
      have h_sq : (↑D * probHigh p - ↑t)^2 ≥ ((↑D : ℝ) / 6)^2 := by
        apply sq_le_sq' <;> linarith
      have hD_r : (↑D : ℝ) > 0 := by exact_mod_cast hD_pos
      calc -2 * (↑D * probHigh p - ↑t)^2 / ↑D 
          ≤ -2 * ((↑D : ℝ) / 6)^2 / ↑D := by
            apply div_le_div_of_nonneg_right _ (le_of_lt hD_r); nlinarith
        _ = -(↑D : ℝ) / 18 := by field_simp; ring
    calc exp (-2 * ((↑D * probHigh p - ↑t)^2) / ↑D)
        ≤ exp (-(↑D : ℝ) / 18) := by rw [exp_le_exp]; exact h_exp_le
      _ ≤ ((2 : ℝ)^(D/36))⁻¹ := by
          have h2_pow : ((2 : ℝ)^(D/36))⁻¹ = exp (-(↑(D/36) * Real.log 2)) := by
            rw [exp_neg]; congr 1
            rw [← rpow_natCast]; rw [rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]; ring_nf
          rw [h2_pow, exp_le_exp]
          have hln2 : Real.log 2 ≤ 1 := by
            rw [← Real.log_exp 1]
            exact Real.log_le_log (by norm_num) (by linarith [add_one_le_exp 1])
          have h_nat_div : (↑(D/36) : ℝ) ≤ (D : ℝ) / 18 := by
            have : (↑(D/36) : ℝ) ≤ (D : ℝ) / 36 := by
              rw [le_div_iff₀ (by norm_num : (0:ℝ) < 36)]
              exact_mod_cast Nat.div_mul_le_self D 36
            linarith [show (D : ℝ) / 36 ≤ (D : ℝ) / 18 from by
              apply div_le_div_of_nonneg_left _ (by norm_num) (by norm_num)
              exact_mod_cast Nat.zero_le D]
          nlinarith [show (↑(D/36) : ℝ) ≥ 0 from by exact_mod_cast Nat.zero_le _]
  -- Step 6: Combine to get natural number bound
  -- We have: card_ds_lt ≤ card_ds_le ≤ p^D * exp(...) ≤ p^D * (2^(D/36))⁻¹ = p^D / 2^(D/36)
  rw [h_card_eq_fin, h_card_eq_ds]
  have h_card_le := card_le_card h_subset
  -- card (< t) ≤ card (≤ t) ≤ p^D * exp(...)
  have h_real_bound : (((Finset.univ : Finset (DigitSpace D p)).filter
      (fun m => highDigitCount m < t)).card : ℝ) ≤ ↑(p^D) / ↑(2^(D/36)) := by
    calc (((Finset.univ.filter (fun m => highDigitCount m < t)).card : ℝ))
        ≤ ((Finset.univ.filter (fun m : DigitSpace D p => (highDigitCount m : ℝ) ≤ ↑t)).card : ℝ) := by
          exact_mod_cast h_card_le
      _ ≤ ↑p ^ D * exp (-2 * ((↑D * probHigh p - ↑t)^2) / ↑D) := h_chernoff
      _ ≤ ↑p ^ D * ((2 : ℝ)^(D/36))⁻¹ := by
          apply mul_le_mul_of_nonneg_left h_exp_bound
          positivity
      _ = ↑(p^D) / ↑(2^(D/36)) := by
          push_cast
          rw [mul_inv_cancel_comm₀ (by positivity : (2:ℝ)^(D/36) ≠ 0)]
          sorry -- need to rewrite this
  sorry
EOF
lake env lean /tmp/test_full2.lean 2>&1
```
Let me fix these issues:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_full3.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset Real Erdos728

set_option maxHeartbeats 800000

lemma count_few_high_digits' {p : ℕ} (hp : p.Prime) (D : ℕ) (t : ℕ) (ht : t ≤ D/6) (hp_ge_3 : p ≥ 3) :
    ((range (p^D)).filter (fun m => count_high_digits p m D < t)).card ≤ p^D / 2^(D/36) := by
  by_cases ht0 : t = 0
  · simp [ht0]
  have ht_pos : t ≥ 1 := Nat.pos_of_ne_zero ht0
  have hD_ge_6 : D ≥ 6 := by omega
  have hD_pos : D > 0 := by omega
  -- Step 1: Relate range(p^D) filter to DigitSpace filter via bijection
  have h_card_eq_fin :
      ((range (p^D)).filter (fun m => count_high_digits p m D < t)).card =
      ((Finset.univ : Finset (Fin (p^D))).filter
        (fun m : Fin (p^D) => count_high_digits p m.val D < t)).card := by
    apply Finset.card_bij (fun m hm => ⟨m, by rw [mem_filter] at hm; exact mem_range.mp hm.1⟩)
    · intro m hm; rw [mem_filter] at hm ⊢; exact ⟨mem_univ _, hm.2⟩
    · intro a _ b _ h; simp at h; exact h
    · intro b hb; refine ⟨b.val, ?_, Fin.ext rfl⟩
      rw [mem_filter]; exact ⟨mem_range.mpr b.isLt, (mem_filter.mp hb).2⟩
  have h_card_eq_ds :
      ((Finset.univ : Finset (Fin (p^D))).filter
        (fun m : Fin (p^D) => count_high_digits p m.val D < t)).card =
      ((Finset.univ : Finset (DigitSpace D p)).filter
        (fun m : DigitSpace D p => highDigitCount m < t)).card := by
    have hbij := toDigitSpace_bijective hp D
    apply Finset.card_bij (fun m _ => toDigitSpace hp D m)
    · intro m hm; rw [mem_filter] at hm ⊢
      exact ⟨mem_univ _, by rw [highDigitCount_eq hp D m]; exact hm.2⟩
    · intro a _ b _ h; exact hbij.1 h
    · intro b hb; obtain ⟨a, ha⟩ := hbij.2 b
      refine ⟨a, ?_, ha⟩; rw [mem_filter]
      exact ⟨mem_univ _, by rw [← highDigitCount_eq hp D a, ha]; exact (mem_filter.mp hb).2⟩
  -- Step 2: Filter subset (< t implies ≤ (t : ℝ))
  have h_subset :
      ((Finset.univ : Finset (DigitSpace D p)).filter (fun m => highDigitCount m < t)) ⊆
      ((Finset.univ : Finset (DigitSpace D p)).filter (fun m => (highDigitCount m : ℝ) ≤ ↑t)) := by
    intro m; simp only [mem_filter, mem_univ, true_and]
    exact fun h => by exact_mod_cast le_of_lt h
  -- Step 3: probHigh p ≥ 1/3 and t < D * probHigh p
  have h_prob_ge : probHigh p ≥ 1/3 := by
    unfold probHigh
    rw [ge_iff_le, div_le_div_iff₀ (by norm_num : (0:ℝ) < 3) (by positivity : (0:ℝ) < p)]
    have : (↑(p / 2 * 3) : ℝ) ≥ (↑p : ℝ) := by exact_mod_cast (show p / 2 * 3 ≥ p by omega)
    push_cast at this; linarith
  have h_t_le_D6 : (↑t : ℝ) ≤ ↑D / 6 := by
    have : (↑(t * 6) : ℝ) ≤ (↑D : ℝ) := by exact_mod_cast (show t * 6 ≤ D by omega)
    push_cast at this; linarith
  have h_t_lt : (t : ℝ) < ↑D * probHigh p := by
    have : (↑D : ℝ) / 6 < ↑D / 3 := by
      apply div_lt_div_of_pos_left (by exact_mod_cast hD_pos : (0:ℝ) < ↑D) (by norm_num) (by norm_num)
    nlinarith [show (D:ℝ) ≥ 0 from by positivity]
  -- Step 4: Apply Chernoff
  have hne : NeZero p := ⟨Nat.Prime.ne_zero hp⟩
  have h_chernoff := @count_few_high_digits_bound_chernoff D p hne (↑t) h_t_lt
  -- Step 5: Exponent bound
  have h_exp_bound : exp (-2 * ((↑D * probHigh p - ↑t)^2) / (↑D : ℝ)) ≤ ((2 : ℝ)^(D/36))⁻¹ := by
    have h_gap : ↑D * probHigh p - ↑t ≥ ↑D / 6 := by nlinarith [show (D:ℝ) ≥ 0 from by positivity]
    have hD_r : (↑D : ℝ) > 0 := by exact_mod_cast hD_pos
    have h_exp_le : -2 * ((↑D * probHigh p - ↑t)^2) / (↑D : ℝ) ≤ -(↑D : ℝ) / 18 := by
      calc -2 * (↑D * probHigh p - ↑t)^2 / ↑D 
          ≤ -2 * ((↑D : ℝ) / 6)^2 / ↑D := by
            apply div_le_div_of_nonneg_right _ (le_of_lt hD_r)
            nlinarith [show (↑D * probHigh p - ↑t)^2 ≥ ((↑D : ℝ) / 6)^2 from sq_le_sq' (by linarith) h_gap]
        _ = -(↑D : ℝ) / 18 := by field_simp; ring
    calc exp (-2 * ((↑D * probHigh p - ↑t)^2) / ↑D)
        ≤ exp (-(↑D : ℝ) / 18) := by rw [exp_le_exp]; exact h_exp_le
      _ ≤ ((2 : ℝ)^(D/36))⁻¹ := by
          rw [show ((2 : ℝ)^(D/36))⁻¹ = exp (-(↑(D/36) * Real.log 2)) from by
            rw [exp_neg]; congr 1
            rw [← rpow_natCast, rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]; ring_nf]
          rw [exp_le_exp]
          nlinarith [
            show Real.log 2 ≤ 1 from by
              rw [← Real.log_exp 1]; exact Real.log_le_log (by norm_num) (by linarith [add_one_le_exp 1]),
            show (↑(D/36) : ℝ) ≤ (D : ℝ) / 18 from by
              have : (↑(D/36) : ℝ) ≤ (D : ℝ) / 36 := by
                rw [le_div_iff₀ (by norm_num : (0:ℝ) < 36)]
                exact_mod_cast Nat.div_mul_le_self D 36
              linarith [show (D : ℝ) / 36 ≤ (D : ℝ) / 18 from by
                apply div_le_div_of_nonneg_left _ (by norm_num) (by norm_num)
                exact_mod_cast Nat.zero_le D],
            show (↑(D/36) : ℝ) ≥ 0 from by exact_mod_cast Nat.zero_le _]
  -- Step 6: Combine to get nat bound
  rw [h_card_eq_fin, h_card_eq_ds]
  -- Use the approach: show (card : ℝ) ≤ p^D / 2^(D/36) as reals, then cast
  have h2_pos : (2 : ℕ)^(D/36) > 0 := by positivity
  rw [Nat.le_div_iff_mul_le h2_pos]
  -- Goal: card * 2^(D/36) ≤ p^D
  have h_card_le := card_le_card h_subset
  have h_real : (((Finset.univ.filter (fun m : DigitSpace D p => highDigitCount m < t)).card * 2^(D/36) : ℕ) : ℝ) ≤ ↑(p^D) := by
    push_cast
    calc ↑((Finset.univ.filter (fun m : DigitSpace D p => highDigitCount m < t)).card) * ↑(2^(D/36))
        ≤ ↑((Finset.univ.filter (fun m : DigitSpace D p => (highDigitCount m : ℝ) ≤ ↑t)).card) * ↑(2^(D/36)) := by
          apply mul_le_mul_of_nonneg_right (by exact_mod_cast h_card_le) (by positivity)
      _ ≤ (↑p ^ D * exp (-2 * ((↑D * probHigh p - ↑t)^2) / ↑D)) * ↑(2^(D/36)) := by
          apply mul_le_mul_of_nonneg_right h_chernoff (by positivity)
      _ ≤ (↑p ^ D * ((2 : ℝ)^(D/36))⁻¹) * ↑(2^(D/36)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_left h_exp_bound (by positivity)
      _ = ↑p ^ D := by
          rw [mul_assoc, inv_mul_cancel₀ (by positivity : (2:ℝ)^(D/36) ≠ 0), mul_one]
          push_cast; rfl
  exact_mod_cast h_real
EOF
lake env lean /tmp/test_full3.lean 2>&1
```
Close! Let me fix the last part:
```bash
$ cd /home/jarred/code/erdos-728b && cat > /tmp/test_full3b.lean << 'EOF'
import Erdos.Lemma3Counting

open Nat BigOperators Finset Real Erdos728

set_option maxHeartbeats 800000

lemma count_few_high_digits' {p : ℕ} (hp : p.Prime) (D : ℕ) (t : ℕ) (ht : t ≤ D/6) (hp_ge_3 : p ≥ 3) :
    ((range (p^D)).filter (fun m => count_high_digits p m D < t)).card ≤ p^D / 2^(D/36) := by
  by_cases ht0 : t = 0
  · simp [ht0]
  have ht_pos : t ≥ 1 := Nat.pos_of_ne_zero ht0
  have hD_ge_6 : D ≥ 6 := by omega
  have hD_pos : D > 0 := by omega
  have h_card_eq_fin :
      ((range (p^D)).filter (fun m => count_high_digits p m D < t)).card =
      ((Finset.univ : Finset (Fin (p^D))).filter
        (fun m : Fin (p^D) => count_high_digits p m.val D < t)).card := by
    apply Finset.card_bij (fun m hm => ⟨m, by rw [mem_filter] at hm; exact mem_range.mp hm.1⟩)
    · intro m hm; rw [mem_filter] at hm ⊢; exact ⟨mem_univ _, hm.2⟩
    · intro a _ b _ h; simp at h; exact h
    · intro b hb; refine ⟨b.val, ?_, Fin.ext rfl⟩
      rw [mem_filter]; exact ⟨mem_range.mpr b.isLt, (mem_filter.mp hb).2⟩
  have h_card_eq_ds :
      ((Finset.univ : Finset (Fin (p^D))).filter
        (fun m : Fin (p^D) => count_high_digits p m.val D < t)).card =
      ((Finset.univ : Finset (DigitSpace D p)).filter
        (fun m : DigitSpace D p => highDigitCount m < t)).card := by
    have hbij := toDigitSpace_bijective hp D
    apply Finset.card_bij (fun m _ => toDigitSpace hp D m)
    · intro m hm; rw [mem_filter] at hm ⊢
      exact ⟨mem_univ _, by rw [highDigitCount_eq hp D m]; exact hm.2⟩
    · intro a _ b _ h; exact hbij.1 h
    · intro b hb; obtain ⟨a, ha⟩ := hbij.2 b
      refine ⟨a, ?_, ha⟩; rw [mem_filter]
      exact ⟨mem_univ _, by rw [← highDigitCount_eq hp D a, ha]; exact (mem_filter.mp hb).2⟩
  have h_subset :
      ((Finset.univ : Finset (DigitSpace D p)).filter (fun m => highDigitCount m < t)) ⊆
      ((Finset.univ : Finset (DigitSpace D p)).filter (fun m => (highDigitCount m : ℝ) ≤ ↑t)) := by
    intro m; simp only [mem_filter, mem_univ, true_and]
    exact fun h => by exact_mod_cast le_of_lt h
  have h_prob_ge : probHigh p ≥ 1/3 := by
    unfold probHigh
    rw [ge_iff_le, div_le_div_iff₀ (by norm_num : (0:ℝ) < 3) (by positivity : (0:ℝ) < p)]
    have : (↑(p / 2 * 3) : ℝ) ≥ (↑p : ℝ) := by exact_mod_cast (show p / 2 * 3 ≥ p by omega)
    push_cast at this; linarith
  have h_t_le_D6 : (↑t : ℝ) ≤ ↑D / 6 := by
    have : (↑(t * 6) : ℝ) ≤ (↑D : ℝ) := by exact_mod_cast (show t * 6 ≤ D by omega)
    push_cast at this; linarith
  have h_t_lt : (t : ℝ) < ↑D * probHigh p := by
    have : (↑D : ℝ) / 6 < ↑D / 3 := by
      apply div_lt_div_of_pos_left (by exact_mod_cast hD_pos : (0:ℝ) < ↑D) (by norm_num) (by norm_num)
    nlinarith [show (D:ℝ) ≥ 0 from by positivity]
  have hne : NeZero p := ⟨Nat.Prime.ne_zero hp⟩
  have h_chernoff := @count_few_high_digits_bound_chernoff D p hne (↑t) h_t_lt
  have h_exp_bound : exp (-2 * ((↑D * probHigh p - ↑t)^2) / (↑D : ℝ)) ≤ ((2 : ℝ)^(D/36))⁻¹ := by
    have h_gap : ↑D * probHigh p - ↑t ≥ ↑D / 6 := by nlinarith [show (D:ℝ) ≥ 0 from by positivity]
    have hD_r : (↑D : ℝ) > 0 := by exact_mod_cast hD_pos
    have h_exp_le : -2 * ((↑D * probHigh p - ↑t)^2) / (↑D : ℝ) ≤ -(↑D : ℝ) / 18 := by
      calc -2 * (↑D * probHigh p - ↑t)^2 / ↑D 
          ≤ -2 * ((↑D : ℝ) / 6)^2 / ↑D := by
            apply div_le_div_of_nonneg_right _ (le_of_lt hD_r)
            nlinarith [show (↑D * probHigh p - ↑t)^2 ≥ ((↑D : ℝ) / 6)^2 from sq_le_sq' (by linarith) h_gap]
        _ = -(↑D : ℝ) / 18 := by field_simp; ring
    calc exp (-2 * ((↑D * probHigh p - ↑t)^2) / ↑D)
        ≤ exp (-(↑D : ℝ) / 18) := by rw [exp_le_exp]; exact h_exp_le
      _ ≤ ((2 : ℝ)^(D/36))⁻¹ := by
          rw [show ((2 : ℝ)^(D/36))⁻¹ = exp (-(↑(D/36) * Real.log 2)) from by
            rw [exp_neg]; congr 1
            rw [← rpow_natCast, rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]; ring_nf]
          rw [exp_le_exp]
          nlinarith [
            show Real.log 2 ≤ 1 from by
              rw [← Real.log_exp 1]; exact Real.log_le_log (by norm_num) (by linarith [add_one_le_exp 1]),
            show (↑(D/36) : ℝ) ≤ (D : ℝ) / 18 from by
              have : (↑(D/36) : ℝ) ≤ (D : ℝ) / 36 := by
                rw [le_div_iff₀ (by norm_num : (0:ℝ) < 36)]
                exact_mod_cast Nat.div_mul_le_self D 36
              linarith [show (D : ℝ) / 36 ≤ (D : ℝ) / 18 from by
                apply div_le_div_of_nonneg_left _ (by norm_num) (by norm_num)
                exact_mod_cast Nat.zero_le D],
            show (↑(D/36) : ℝ) ≥ 0 from by exact_mod_cast Nat.zero_le _]
  -- Final step: combine in ℕ
  rw [h_card_eq_fin, h_card_eq_ds]
  have h2_pos : (2 : ℕ)^(D/36) > 0 := by positivity
  rw [Nat.le_div_iff_mul_le h2_pos]
  have h_card_le := card_le_card h_subset
  suffices h : (((Finset.univ.filter (fun m : DigitSpace D p => highDigitCount m < t)).card
      * 2^(D/36) : ℕ) : ℝ) ≤ ↑(p^D) from by exact_mod_cast h
  push_cast
  calc ↑((Finset.univ.filter (fun m : DigitSpace D p => highDigitCount m < t)).card) * (2:ℝ)^(D/36)
      ≤ ↑((Finset.univ.filter (fun m : DigitSpace D p => (highDigitCount m : ℝ) ≤ ↑t)).card) * (2:ℝ)^(D/36) := by
        apply mul_le_mul_of_nonneg_right (by exact_mod_cast h_card_le) (by positivity)
    _ ≤ (↑p ^ D * exp (-2 * ((↑D * probHigh p - ↑t)^2) / ↑D)) * (2:ℝ)^(D/36) := by
        apply mul_le_mul_of_nonneg_right h_chernoff (by positivity)
    _ ≤ (↑p ^ D * ((2 : ℝ)^(D/36))⁻¹) * (2:ℝ)^(D/36) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left h_exp_bound (by positivity)
    _ = ↑p ^ D := by
        rw [mul_assoc, inv_mul_cancel₀ (by positivity : (2:ℝ)^(D/36) ≠ 0), mul_one]
EOF
lake env lean /tmp/test_full3b.lean 2>&1
```
The proof compiles. Now let me integrate it into the actual file:
```bash
$ cd /home/jarred/code/erdos-728b && tm update erdos728b-9pu --status "Proof compiles in test file, integrating into Lemma3Counting.lean"
```

🛠️ **Executing tool: edit**

```bash
$ cd /home/jarred/code/erdos-728b && lake build 2>&1 | tail -30
```
Build completed successfully. The sorry in `count_few_high_digits` has been closed. Let me verify it's no longer listed as a sorry:
```bash
$ cd /home/jarred/code/erdos-728b && grep -n "sorry" Erdos/Lemma3Counting.lean
```
The `count_few_high_digits` sorry at the former line 82 is gone. Let me commit:
```bash
$ cd /home/jarred/code/erdos-728b && git add -A && git commit -m "Close sorry: count_few_high_digits in Lemma3Counting.lean

Prove that #{m ∈ {0..p^D-1} : count_high_digits p m D < t} ≤ p^D/2^(D/36)
for t ≤ D/6 and p ≥ 3.

Proof strategy:
1. Biject range(p^D) → Fin(p^D) → DigitSpace D p via toDigitSpace
2. Relate count_high_digits to highDigitCount via highDigitCount_eq
3. Apply count_few_high_digits_bound_chernoff from Erdos/Chernoff.lean
4. Show the Chernoff exponent ≤ -D/18 (since probHigh p ≥ 1/3 for p ≥ 3
   and the gap D*probHigh(p) - t ≥ D/6)
5. Show exp(-D/18) ≤ 2^(-D/36) since ln 2 ≤ 1 and ⌊D/36⌋ ≤ D/18
6. Convert real bound to natural number floor division"
```

```bash
$ cd /home/jarred/code/erdos-728b && tm update erdos728b-9pu --status "Sorry closed, lake build succeeds, committed"
```

```bash
$ cd /home/jarred/code/erdos-728b && tm close erdos728b-9pu
```
```json
{
  "status": "completed",
  "summary": "Closed sorry in count_few_high_digits. lake build succeeds.",
  "details": "Proved that #{m ∈ {0..p^D-1} : count_high_digits p m D < t} ≤ p^D/2^(D/36) for t ≤ D/6 and p ≥ 3. The proof proceeds in 6 steps:\n\n1. **Bijection**: Relate `range(p^D)` to `DigitSpace D p` via `toDigitSpace_bijective`, preserving the filter predicate via `highDigitCount_eq`.\n\n2. **Filter subset**: The nat filter `highDigitCount m < t` is a subset of the real filter `(highDigitCount m : ℝ) ≤ ↑t`.\n\n3. **Precondition**: Show `(t : ℝ) < D * probHigh p` (needed for Chernoff). Uses `probHigh p ≥ 1/3` for `p ≥ 3` and `t ≤ D/6 < D/3 ≤ D * probHigh p`.\n\n4. **Chernoff application**: Apply `count_few_high_digits_bound_chernoff` from `Erdos/Chernoff.lean`.\n\n5. **Exponent bound**: Show `exp(-2 * gap² / D) ≤ (2^(D/36))⁻¹` by chaining:\n   - gap ≥ D/6, so exponent ≤ -D/18\n   - exp(-D/18) ≤ exp(-⌊D/36⌋ * ln 2) = (2^(D/36))⁻¹ since ln 2 ≤ 1 and ⌊D/36⌋ ≤ D/18\n\n6. **Real-to-nat conversion**: Use `Nat.le_div_iff_mul_le` to convert the real inequality to nat floor division.\n\nNo new sorry holes introduced."
}
```

## Final Result

```json
{
  "status": "completed",
  "summary": "Closed sorry in count_few_high_digits. lake build succeeds.",
  "details": "Proved that #{m ∈ {0..p^D-1} : count_high_digits p m D < t} ≤ p^D/2^(D/36) for t ≤ D/6 and p ≥ 3. The proof proceeds in 6 steps:\n\n1. **Bijection**: Relate `range(p^D)` to `DigitSpace D p` via `toDigitSpace_bijective`, preserving the filter predicate via `highDigitCount_eq`.\n\n2. **Filter subset**: The nat filter `highDigitCount m < t` is a subset of the real filter `(highDigitCount m : ℝ) ≤ ↑t`.\n\n3. **Precondition**: Show `(t : ℝ) < D * probHigh p` (needed for Chernoff). Uses `probHigh p ≥ 1/3` for `p ≥ 3` and `t ≤ D/6 < D/3 ≤ D * probHigh p`.\n\n4. **Chernoff application**: Apply `count_few_high_digits_bound_chernoff` from `Erdos/Chernoff.lean`.\n\n5. **Exponent bound**: Show `exp(-2 * gap² / D) ≤ (2^(D/36))⁻¹` by chaining:\n   - gap ≥ D/6, so exponent ≤ -D/18\n   - exp(-D/18) ≤ exp(-⌊D/36⌋ * ln 2) = (2^(D/36))⁻¹ since ln 2 ≤ 1 and ⌊D/36⌋ ≤ D/18\n\n6. **Real-to-nat conversion**: Use `Nat.le_div_iff_mul_le` to convert the real inequality to nat floor division.\n\nNo new sorry holes introduced."
}
```

End Time: 2026-02-11T05:15:50.168Z
