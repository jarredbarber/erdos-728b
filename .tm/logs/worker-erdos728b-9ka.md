# timtam Task: Mathlib coverage check for factorials and p-adic valuations (erdos728b-9ka)

Role: librarian
Agent: librarian (google-antigravity/gemini-3-pro-high:high)
Start Time: 2026-02-10T14:45:10.530Z

## Agent Interaction



> **Thinking:**
> **Analyzing Mathlib Coverage**
> 
> I'm currently focused on assessing Mathlib's coverage of factorials and p-adic valuations. Specifically, I'm checking for Legendre's formula, digit sums in base p, and fundamental inequalities pertaining to those sums. I'm also searching for pertinent lemmas that could be beneficial.
> 
> 
> 


```bash
$ tm update erdos728b-9ka --status "Searching Mathlib for Legendre's formula and digit sum properties"
```

```bash
$ ls -R .lake/packages/mathlib/Mathlib/ | grep -i "digits" | head -n 20
```

```bash
$ ls -R .lake/packages/mathlib/Mathlib/ | grep -i "factorial" | head -n 20
```

```bash
$ grep -r "Legendre" .lake/packages/mathlib/Mathlib/Data/Nat/ | grep "factorial"
```

```bash
$ cat .lake/packages/mathlib/Mathlib/Data/Nat/Multiplicity.lean
```


> **Thinking:**
> **Locating Missing Definitions**
> 
> I'm currently investigating the whereabouts of the `padicValNat_factorial` definition. While I found Legendre's Formula, `Nat.Prime.emultiplicity_factorial`, in `Mathlib/Data/Nat/Multiplicity.lean`, the supporting definition seems absent from the file. I'll need to broaden the search within the library to locate it.
> 
> 
> 


```bash
$ grep -r "padicValNat_factorial" .lake/packages/mathlib/Mathlib/
```

```bash
$ cat .lake/packages/mathlib/Mathlib/NumberTheory/Padics/PadicVal/Basic.lean
```


> **Thinking:**
> **Analyzing Factorial Valuations**
> 
> I've been working on Legendre's Formula, specifically `padicValNat_factorial`. I've successfully identified and formulated the theorem: `padicValNat_factorial`. I can now compute the p-adic valuation of a factorial. The theorem leverages a summation over powers of p less than b, where `b` is an upper bound on the base-p logarithm of n.
> 
> 
> **Connecting Valuation and Digits**
> 
> I've made significant progress by formulating `sub_one_mul_padicValNat_factorial`, which connects the p-adic valuation of a factorial to the digit sum. I'm now delving into the properties of `Nat.digits` in `Mathlib` to understand how digit sums behave. I am focusing on subadditivity for sums of digits. I am examining carries during addition.
> 
> 
> 


```bash
$ cat .lake/packages/mathlib/Mathlib/Data/Nat/Digits.lean
```

```bash
$ ls .lake/packages/mathlib/Mathlib/Data/Nat/
```

```bash
$ ls .lake/packages/mathlib/Mathlib/Data/Nat/Digits/
```

```bash
$ cat .lake/packages/mathlib/Mathlib/Data/Nat/Digits/Defs.lean
```


> **Thinking:**
> **Investigating Mathlib Digits**
> 
> I'm currently looking into `Mathlib/Data/Nat/Digits.lean`. Specifically, I've confirmed, by using `cat`, that `Defs.lean` contains the definition for `digits`. This should be useful!
> 
> 
> 


```bash
$ cat .lake/packages/mathlib/Mathlib/Data/Nat/Digits/Lemmas.lean
```


> **Thinking:**
> **Locating Useful Definitions**
> 
> I've discovered `Nat.digit_sum_le` in `Mathlib/Data/Nat/Digits/Defs.lean`, which is relevant. It provides a bound on the sum of digits, stating that `List.sum (digits p n) ≤ n`. Now, my focus is on finding or proving the subadditivity of digit sums. Specifically, I'm aiming for an inequality like `sum_digits (a + b) ≤ sum_digits a + sum_digits b`.
> 
> 
> **Analyzing Carrying Lemmas**
> 
> I'm now investigating carrying behavior and its connection to digit sums, focusing on `padicValNat_choose` in `Mathlib/NumberTheory/Padics/PadicVal/Basic.lean`. I'm exploring how the valuation relates to carries and am aiming to leverage Legendre's formula, or a similar approach, to prove subadditivity of the digit sum function. The current approach involves rewriting formulas with factorials and binomial coefficients with Legendre's formula and hoping for progress.
> 
> 
> 


```bash
$ grep -r "sum_digits" .lake/packages/mathlib/Mathlib/ | grep "add"
```

```bash
$ grep -r "digits" .lake/packages/mathlib/Mathlib/ | grep "sum" | grep "add"
```


> **Thinking:**
> **Investigating Additivity Properties**
> 
> I haven't found a direct reference to `sum_digits_add_le`. Now, I'm checking for explicit mentions of the subadditivity of `sum_digits`, or some variations like `digits_sum_add` or `sum_digits_add`. I'm also considering the implications of carries in the addition process.
> 
> 
> **Connecting Valuation and Digits**
> 
> I've made a connection between valuation and carries, relating to `icValNat_choose`, which refers to Kummer's Theorem. This links the number of carries when adding *k* and *n-k* in base *p* to the p-adic valuation of the binomial coefficient. This is a direct path to the subadditivity of `sum_digits`, thanks to the relationship between binomial coefficients and `sum_digits`. I believe the result is now within reach, pending the existence of `sub_one_mul_padicValNat_choose_eq_sub_sum_digits'`. I am checking its existence.
> 
> 
> 


```bash
$ grep -r "def sum_digits" .lake/packages/mathlib/Mathlib/
```


> **Thinking:**
> **Analyzing Digit Summation**
> 
> I've realized `sum_digits` isn't a stand-alone function. It appears to be shorthand for `(digits b n).sum`. I'm now looking into the `Mathlib/Data/Nat/Digits/Defs.lean` file, specifically the `digit_sum_le` theorem, to see if there are any related concepts or relevant properties. I am working on building a mental model on the relation of digits and their summation.
> 
> 
> **Refining Formula Derivation**
> 
> I've confirmed `List.sum (digits p n)` is used, and it's essential. I've located Legendre's formula via `padicValNat_factorial`. I'm verifying the connection of digit sums, particularly `padicValNat_choose`, to the core problem. The connection to carries is increasingly important. I'm investigating specific lemmas around carries and addition to ensure a complete response.
> 
> 
> 


🛠️ **Executing tool: write**


> **Thinking:**
> **Checking Mathlib Coverage**
> 
> I've just finished documenting the mathlib coverage in `artifacts/mathlib-coverage.md`. Now, I'm carefully re-examining the `sub_one_mul_padicValNat_choose_eq_sub_sum_digits'` result. I need to make sure I haven't missed any edge cases in `Mathlib/NumberTheory/Padics/PadicVal/Basic.lean`.
> 
> 
> 


```bash
$ tm update erdos728b-9ka --status "completed"
```

```bash
$ tm update erdos728b-9ka --status "Done"
```
```json
{
  "status": "completed",
  "summary": "Surveyed Legendre's formula, digit sums, and related results in Mathlib. Found `padicValNat_factorial`, `Nat.digits`, and `sub_one_mul_padicValNat_choose_eq_sub_sum_digits'`.",
  "details": "Published findings to `artifacts/mathlib-coverage.md`. Key results include:\n- Legendre's Formula: `padicValNat_factorial` in `Mathlib/NumberTheory/Padics/PadicVal/Basic.lean`.\n- Digit Sums: `Nat.digits` and `(digits p n).sum`.\n- Subadditivity: Implied by `sub_one_mul_padicValNat_choose_eq_sub_sum_digits'`.\n- Carries: `padicValNat_choose` relates valuation to carries (Kummer's Theorem)."
}
```

## Final Result

```json
{
  "status": "completed",
  "summary": "Surveyed Legendre's formula, digit sums, and related results in Mathlib. Found `padicValNat_factorial`, `Nat.digits`, and `sub_one_mul_padicValNat_choose_eq_sub_sum_digits'`.",
  "details": "Published findings to `artifacts/mathlib-coverage.md`. Key results include:\n- Legendre's Formula: `padicValNat_factorial` in `Mathlib/NumberTheory/Padics/PadicVal/Basic.lean`.\n- Digit Sums: `Nat.digits` and `(digits p n).sum`.\n- Subadditivity: Implied by `sub_one_mul_padicValNat_choose_eq_sub_sum_digits'`.\n- Carries: `padicValNat_choose` relates valuation to carries (Kummer's Theorem)."
}
```

End Time: 2026-02-10T14:55:08.756Z
