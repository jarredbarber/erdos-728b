# Task Guide: Lemma3Counting Sorry Closure

This document provides detailed instructions for each formalization task in `Erdos/Lemma3Counting.lean`. All tasks reference the verified NL proof in `proofs/lemma3-counting.md`.

## Architecture Overview

```
Basic.lean:62  (exists_m_small_primes_good_uniform)  — Union bound, Part E
  └── Lemma3Counting.lean:149  (count_bad_interval)  — Per-prime interval bound
        ├── :143  (bad_residue_sets)         — Periodicity of bad set
        ├── :134  (count_congruent_le)       — ALREADY PROVED in Lemma3Residue.lean
        ├── :137  (residue_count_interval)   — ALREADY PROVED in Lemma3Residue.lean
        ├── :98   (h_T_val)                  — Arithmetic: 2s+3 ≤ D/6
        ├── :122  (Bad1 bound)               — Uses cascade counting
        │     ├── :45  (valuation_le_cascade)   — Lemma A2
        │     │     └── :42  (carry_propagate)  — Lemma A1
        │     └── :48  (count_large_cascade)    — Lemma A3
        │           ├── :26  (count_digits_fixed) — Digit fixing count
        │           └── :22  (toDigitSpace_bijective) — Digit bijection
        └── :125  (Bad2 bound)               — Uses high digit counting
              ├── :56  (valuation_ge_high_digits)  — Cor B2
              └── :82  (count_few_high_digits)     — Lemma B4' (Chernoff)
```

## Independent tasks (no dependencies, can start immediately)

### erdos-728-d1cd: toDigitSpace_bijective (L3C:22)

**Goal:** `Function.Bijective (toDigitSpace hp D)`

**Approach:** `toDigitSpace` maps `m : Fin (p^D)` to the function `i ↦ ⟨digit p m i, ...⟩`. Need to show:
- **Injective:** If two numbers have the same digits in positions 0..D-1, they are equal (mod p^D). Use the fact that m = Σ digit(p,m,i) * p^i for i < D when m < p^D.
- **Surjective:** Given any tuple (d_0,...,d_{D-1}) with d_i < p, construct m = Σ d_i * p^i and show m < p^D and digit(p,m,i) = d_i.

`digit p m i` is defined as `(m / p^i) % p` in `Erdos/Digits.lean`.

### erdos-728-mj9i: carry_propagate (L3C:42)

**Goal:** For `i > log p k + 1` and `carry_cond p k m i` and `k ≥ 1`:
`digit p m (i-1) = p-1 ∧ carry_cond p k m (i-1)`

**Approach (Lemma A1):** `carry_cond p k m i` means `p^i ≤ k % p^i + m % p^i`. For `i > s+1` where `s = log p k`, we have `k < p^(s+1) ≤ p^(i-1)`, so `k % p^i = k`. The carry condition `p^i ≤ k + m % p^i` implies `m % p^i ≥ p^i - k`. Write `m % p^i = digit(p,m,i-1) * p^(i-1) + m % p^(i-1)`. Since `k < p^(i-1)`, we need `digit(p,m,i-1) * p^(i-1) + m%(p^(i-1)) ≥ p^i - k > p^i - p^(i-1) = (p-1)*p^(i-1)`. So `digit(p,m,i-1) ≥ p-1`, forcing `digit(p,m,i-1) = p-1`. Then `carry_cond` at `i-1` follows from the remaining inequality.

### erdos-728-l1np: valuation_ge_high_digits (L3C:56)

**Goal:** `padicValNat p ((2*m).choose m) ≥ count_high_digits p m D`

**Approach:** Already proved as `lower_bound_valuation_by_high_digits` in `Erdos/Digits.lean`, which gives `count_high_digits p m D ≤ ((2*m).choose m).factorization p`. Convert factorization to padicValNat using `Nat.factorization_def`.

### erdos-728-eeuz: h_T_val arithmetic (L3C:98)

**Goal:** `2 * s + 3 ≤ T_val` where `s = log p k`, `T_val = D/6`, given `hD : D ≥ 12 * (log p k + 1) + 6`.

**Approach:** Pure Nat arithmetic. `D ≥ 12s + 18`, so `D/6 ≥ (12s+18)/6 = 2s+3`. Use `Nat.le_div_iff_mul_le` or `omega` after establishing `6 * (2*s+3) ≤ D`.

### erdos-728-8rw8: Wire residue lemmas (L3C:134, 137) — PRIORITY 0

**Goal:** Replace sorrys with calls to already-proved lemmas.

`Erdos/Lemma3Residue.lean` already contains a proved `residue_count_interval` with matching signature. For `count_congruent_le`, it may be a specialization. Add `import Erdos.Lemma3Residue` and replace:
- L3C:134 sorry → call residue lemma or derive from it
- L3C:137 sorry → `exact residue_count_interval hp hR a b h_ba` (check exact signature match)

## Tasks with dependencies

### erdos-728-pt18: count_digits_fixed (L3C:26) — depends on d1cd

**Goal:** `((range (p^D)).filter (fun m => ∀ k : Fin T, digit p m (indices k) = values k)).card = p ^ (D - T)`

**Approach:** Via the bijection, this set maps to {tuples with T specified coordinates}, which has cardinality p^(D-T). Use `Finset.card_bij` with `toDigitSpace`.

### erdos-728-rf32: valuation_le_cascade (L3C:45) — depends on d1cd

**Goal:** `padicValNat p ((m + k).choose k) ≤ (log p k + 1) + cascade_length k D m`

**Approach (Lemma A2):** Use Kummer's theorem (`Nat.factorization_choose`). Carries at positions 0..s contribute ≤ s+1. At positions > s, carries cascade only through digits = p-1, stopping at cascade_length. Total ≤ (s+1) + cascade_length.

### erdos-728-iqbw: count_large_cascade (L3C:48) — depends on d1cd, pt18

**Goal:** `((range (p^D)).filter (fun m => cascade_length k D m ≥ T)).card ≤ p ^ (D - T)`

**Approach (Lemma A3):** cascade_length ≥ T requires digits at positions s+1,...,s+T all equal p-1. This fixes T coordinates. Apply count_digits_fixed.

### erdos-728-ukvp: count_few_high_digits (L3C:82)

**Goal:** For `p ≥ 3` and `t ≤ D/6`: `((range (p^D)).filter (fun m => count_high_digits p m D < t)).card ≤ p^D / 2^(D/36)`

**Approach (Lemma B4'):** 
1. Transfer: Use `toDigitSpace_bijective` and `highDigitCount_eq` to relate the filter over `range(p^D)` to a filter over `DigitSpace D p`.
2. Apply `count_few_high_digits_bound_chernoff` (already proved in Chernoff.lean) to get the exponential bound `p^D * exp(-2*(D*probHigh - t)^2/D)`.
3. Show `exp(-2*(D*probHigh - t)^2/D) ≤ 1/2^(D/36)` when `t ≤ D/6` and `p ≥ 3`:
   - For `p ≥ 3`, `probHigh = ⌊p/2⌋/p ≥ 1/3`
   - So `D*probHigh - t ≥ D/3 - D/6 = D/6`  
   - `2*(D/6)^2/D = D/18`
   - `exp(-D/18) ≤ 2^(-D/36)` since `1/18 > ln(2)/36`

### erdos-728-oqq1: Bad1 bound (L3C:122) — depends on iqbw, rf32

**Goal:** `Bad1.card ≤ (p^D) / p^(D/6 - log p k)`

**Approach:** Bad1 = {m : v_p(C(m+k,k)) > D/6}. By valuation_le_cascade, v_p > D/6 implies cascade_length > D/6 - s - 1, i.e., cascade_length ≥ D/6 - s. By count_large_cascade with T = D/6 - s: |Bad1| ≤ p^(D - (D/6 - s)) = p^(D - D/6 + s). Then p^(D-D/6+s) = p^D / p^(D/6-s). The exponent arithmetic in `Lemma3Counting_Scratch.lean` has partial work.

### erdos-728-tqtk: Bad2 bound (L3C:125) — depends on l1np, ukvp

**Goal:** `Bad2.card ≤ (p^D) / 2^(D/36)`

**Approach:** Bad2 = {m : v_p(C(2m,m)) < D/6}. By valuation_ge_high_digits, this implies count_high_digits < D/6. Apply count_few_high_digits.

### erdos-728-3mnb: bad_residue_sets (L3C:143)

**Goal:** Show badness depends only on m mod p^D.

**Approach (Part D):** Both v_p(C(m+k,k)) and count_high_digits depend only on digits of m in positions 0..D-1, which are determined by m mod p^D. Formalize: `digit p m i = digit p (m % p^D) i` for `i < D`.

### erdos-728-lihe: count_bad_interval (L3C:149) — depends on many

**Goal:** Full interval counting bound combining all pieces.

**Approach:** 
1. By bad_residue_sets, bad m in [m0,2m0) have residues in R1 ∪ R2 (mod p^D).
2. |R1| ≤ p^(D-T) by count_large_cascade, |R2| ≤ p^D/2^(D/36) by count_few_high_digits.  
3. By residue_count_interval, #{bad m in [m0,2m0)} ≤ (|R1|+|R2|) * (m0/p^D + 1).
4. Since m0 ≥ p^D, m0/p^D + 1 ≤ 2m0/p^D.
5. Combine and simplify to get the stated bound.
