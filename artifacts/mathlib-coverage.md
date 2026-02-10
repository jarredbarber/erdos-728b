# Mathlib Coverage: Factorials and p-adic Valuations

## Legendre's Formula
- `Nat.Prime.multiplicity_factorial` (in `Mathlib/Data/Nat/Multiplicity.lean`) — Multiplicity of `p` in `n!` is `∑ i ∈ Ico 1 b, n / p ^ i`.
- `padicValNat_factorial` (in `Mathlib/NumberTheory/Padics/PadicVal/Basic.lean`) — Same as above but stated for `padicValNat`.
- `sub_one_mul_padicValNat_factorial` (in `Mathlib/NumberTheory/Padics/PadicVal/Basic.lean`) — Relates `padicValNat p (n!)` to digit sum: `(p - 1) * padicValNat p (n!) = n - (p.digits n).sum`.

## Digit Sums
- `Nat.digits` (in `Mathlib/Data/Nat/Digits/Defs.lean`) — List of digits in base `b`.
- `Nat.ofDigits` (in `Mathlib/Data/Nat/Digits/Defs.lean`) — Convert list of digits back to number.
- `Nat.digit_sum_le` (in `Mathlib/Data/Nat/Digits/Defs.lean`) — `(digits b n).sum ≤ n`.
- `sub_one_mul_padicValNat_choose_eq_sub_sum_digits'` (in `Mathlib/NumberTheory/Padics/PadicVal/Basic.lean`) — Relates `padicValNat p (choose (n + k) k)` to digit sums of `k`, `n`, and `n + k`. Specifically: `(p - 1) * padicValNat p (choose (n + k) k) = (p.digits k).sum + (p.digits n).sum - (p.digits (n + k)).sum`.

## Subadditivity of Digit Sums
- Implied by `sub_one_mul_padicValNat_choose_eq_sub_sum_digits'` since `padicValNat` is non-negative, so `(p.digits (n + k)).sum ≤ (p.digits k).sum + (p.digits n).sum`.

## Carries in Addition
- `padicValNat_choose` (in `Mathlib/NumberTheory/Padics/PadicVal/Basic.lean`) — Kummer's Theorem: The valuation of `choose n k` is the number of carries when adding `k` and `n - k` in base `p`.
- `padicValNat_choose'` (in `Mathlib/NumberTheory/Padics/PadicVal/Basic.lean`) — Variant for `choose (n + k) k`, counting carries when adding `n` and `k`.

## Notes
- `sum_digits` is not defined as a standalone function; use `(Nat.digits b n).sum`.
- `subadditivity` is not stated as a standalone lemma `sum_digits (a + b) ≤ sum_digits a + sum_digits b`, but follows directly from Kummer's theorem.
