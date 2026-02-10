# timtam Task: Check Mathlib for carry bounds on binomial coefficients (erdos728b-fsl)

Role: librarian
Agent: librarian (google-antigravity/gemini-3-pro-high:high)
Start Time: 2026-02-10T16:21:45.167Z

## Agent Interaction



> **Thinking:**
> **Investigating Carry Bounds**
> 
> I'm currently focused on Mathlib and aiming to find lemmas that establish carry bounds for binomial coefficients. My attention is directed to bounding the p-adic valuation. I'm trying to establish a connection between the representation of binomial coefficients in different number bases and how that relates to the $p$-adic valuation. This is the main approach at the moment.
> 
> 
> 


```bash
$ tm update erdos728b-fsl --status "Searching Mathlib for carry bounds and valuation lemmas"
```

```bash
$ grep -r "carry" .lake/packages/mathlib/Mathlib/Data/Nat/Choose
```

```bash
$ grep -r "valuation" .lake/packages/mathlib/Mathlib/Data/Nat/Choose
```

```bash
$ grep -r "digits" .lake/packages/mathlib/Mathlib/Data/Nat/Choose
```

```bash
$ grep -r "kummer" .lake/packages/mathlib/Mathlib/
```


> **Thinking:**
> **Exploring Related Files**
> 
> I've been searching for relevant code snippets. Initially, I looked for "carry" and "valuation" within `Data.Nat.Choose`, but it wasn't fruitful. The search for "digits" within the same directory led me to `Factorization.lean` and `Lucas.lean`. I noticed `Lucas.lean` explicitly mentions "digits," which seems promising for further investigation.
> 
> 
> 


🛠️ **Executing tool: read**


> **Thinking:**
> **Examining Factorization Concepts**
> 
> I'm now delving into the implementation details within `Mathlib/Data/Nat/Choose/Factorization.lean`. Specifically, I've noted `factorization_choose` and `factorization_choose'`, which seems to be a variation. I see that `factorization_choose'` includes a hypothesis about the primality of a variable, `hp`.
> 
> 
> **Investigating p-adic Valuations**
> 
> I've made progress on relating $v_p(\binom{n+k}{k})$ and $v_p(\binom{2m}{m})$. I found relevant lemmas on carries and binomial coefficients, specifically `factorization_choose`. Now, I'm focusing on the relationship between these valuations, and am searching for lemmas involving `centralBinom` within the relevant libraries.
> 
> 
> 


```bash
$ grep -r "centralBinom" .lake/packages/mathlib/Mathlib/Data/Nat/Choose
```


> **Thinking:**
> **Discovering Factorization Lemmas**
> 
> I've located `factorization_choose` and its prime version in `Mathlib/Data/Nat/Choose/Factorization.lean`, linking p-adic valuations to carry counts. Now, I'm trying to find if lemmas exist relating the $p$-adic valuation of binomial coefficients to the variables within the binomial coefficient.
> 
> 
> 


🛠️ **Executing tool: read**


> **Thinking:**
> **Investigating Central Binomials**
> 
> I'm currently focused on the `Central.lean` file, examining `centralBinom` and its properties. While it's established, I haven't found a direct connection to $p$-adic valuations or the specific binomial coefficient relationship I need. My next step involves searching for potentially useful lemmas to bridge that gap.
> 
> 
> 


```bash
$ ls .lake/packages/mathlib/Mathlib/Data/Nat/Digits
```

🛠️ **Executing tool: read**


> **Thinking:**
> **Locating Relevant Theorems**
> 
> I've examined `Mathlib/Data/Nat/Digits/Lemmas.lean`, but it lacks the necessary properties related to binomial coefficients or carries that I need. However, I did find `factorization_choose` and `factorization_choose'` within `Mathlib/Data/Nat/Choose`, which seem promising for further exploration.
> 
> 
> 


```bash
$ grep -r "carry" .lake/packages/mathlib/Mathlib/Data/Nat/Choose
```


> **Thinking:**
> **Analyzing "Carry" in Lemmas**
> 
> My search for "carry" continues to be unfruitful in `Data/Nat/Choose`. The word seems absent from lemma names and docstrings in that specific file. Curiously, `Factorization.lean` uses the factorization of p in the docstring, which is good.
> 
> 
> 


```bash
$ ls .lake/packages/mathlib/Mathlib/NumberTheory/Padics
```

🛠️ **Executing tool: read**


> **Thinking:**
> **Verifying PadicVal Location**
> 
> Okay, I was mistaken earlier about `PadicVal`. Upon closer inspection of the `ls` output, within `.lake/packages/mathlib/Mathlib/NumberTheory/Padics/`, it appears to be a potential file rather than a directory. I'm double-checking to confirm its exact nature.
> 
> 
> 


```bash
$ ls -F .lake/packages/mathlib/Mathlib/NumberTheory/Padics/PadicVal/
```

🛠️ **Executing tool: read**
**Discovering Equivalences**
> 
> I've located `padicValNat_choose` and `padicValNat_choose'` within `Mathlib/NumberTheory/Padics/PadicVal/Basic.lean`, and it seems they're fundamentally identical to the `factorization_choose` and `factorization_choose'` functions defined in `Data/Nat/Choose`. This equivalence is quite interesting.
> 
> 
> 

> **Thinking:**
> 


```bash
$ grep -r "centralBinom" .lake/packages/mathlib/Mathlib/NumberTheory
```

🛠️ **Executing tool: read**


> **Thinking:**
> **Reporting on Bertrand's Postulate**
> 
> I've examined the Bertrand.lean file, noting its use of `Nat.four_pow_lt_mul_centralBinom` and `centralBinom_le_of_no_bertrand_prime`. My analysis highlights a focus on bounds and the inclusion of `factorization`. This should prove useful in summarizing the approach taken.
> 
> 
> **Analyzing p-adic Valuation Details**
> 
> I've been investigating the p-adic valuation aspects, concentrating on relevant lemmas. I've found `padicValNat_choose`, `padicValNat_choose'`, and `sub_one_mul_padicValNat_choose_eq_sub_sum_digits`. While I couldn't find a direct link between $v_p(\binom{m+k}{k})$ and $v_p(\binom{2m}{m})$, I found lemmas about the factorization of central binomial coefficients, such as `factorization_centralBinom_of_two_mul_self_lt_three_mul`. I'll present these findings, noting that a direct relationship might be absent or require further derivation, perhaps using Kummer's theorem.
> 
> 
> 


🛠️ **Executing tool: read**


> **Thinking:**
> **Finalizing Divisibility Findings**
> 
> I've been examining the current lean mathematical library. It seems `Dvd.lean` has some relevant theorems, specifically `dvd_choose_add` and `dvd_choose` in relation to prime divisibility, though they don't directly compute valuations. Additionally, I believe that `Bounds.lean` focuses more on bounds, not valuations. I am now closing the books and finalizing my findings.
> 
> 
> 

```json
{
  "status": "completed",
  "summary": "Surveyed Mathlib for carry bounds on binomial coefficients and p-adic valuations. Found key lemmas relating valuation to carries (Kummer's Theorem) but no direct lemma relating v_p(choose (m+k) k) to v_p(choose (2m) m).",
  "details": "1. **Carry Lemmas (Kummer's Theorem)**:\n   - `Nat.factorization_choose` and `Nat.factorization_choose'` in `Mathlib/Data/Nat/Choose/Factorization.lean` state that the exponent of a prime `p` in the factorization of `choose n k` is the number of carries when adding `k` and `n - k` (or `k` and `n` for `choose (n+k) k`) in base `p`.\n   - `padicValNat.padicValNat_choose` and `padicValNat.padicValNat_choose'` in `Mathlib/NumberTheory/Padics/PadicVal/Basic.lean` provide the same result in terms of `padicValNat`.\n\n2. **Valuation Bounds and Digits**:\n   - `padicValNat.sub_one_mul_padicValNat_choose_eq_sub_sum_digits` in `Mathlib/NumberTheory/Padics/PadicVal/Basic.lean` relates `(p-1) * v_p(choose n k)` to the difference in sum of digits.\n   - `Nat.factorization_choose_le_log` gives a logarithmic upper bound on the valuation.\n   - `Nat.factorization_choose_le_one` states that primes `p > sqrt(n)` appear at most once.\n\n3. **Central Binomial Coefficient**:\n   - `Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul` bounds prime factors for `centralBinom`.\n   - No direct lemma was found relating `v_p(choose (m+k) k)` to `v_p(choose (2m) m)`. This relationship likely needs to be derived from the carry lemmas."
}
```

## Final Result

```json
{
  "status": "completed",
  "summary": "Surveyed Mathlib for carry bounds on binomial coefficients and p-adic valuations. Found key lemmas relating valuation to carries (Kummer's Theorem) but no direct lemma relating v_p(choose (m+k) k) to v_p(choose (2m) m).",
  "details": "1. **Carry Lemmas (Kummer's Theorem)**:\n   - `Nat.factorization_choose` and `Nat.factorization_choose'` in `Mathlib/Data/Nat/Choose/Factorization.lean` state that the exponent of a prime `p` in the factorization of `choose n k` is the number of carries when adding `k` and `n - k` (or `k` and `n` for `choose (n+k) k`) in base `p`.\n   - `padicValNat.padicValNat_choose` and `padicValNat.padicValNat_choose'` in `Mathlib/NumberTheory/Padics/PadicVal/Basic.lean` provide the same result in terms of `padicValNat`.\n\n2. **Valuation Bounds and Digits**:\n   - `padicValNat.sub_one_mul_padicValNat_choose_eq_sub_sum_digits` in `Mathlib/NumberTheory/Padics/PadicVal/Basic.lean` relates `(p-1) * v_p(choose n k)` to the difference in sum of digits.\n   - `Nat.factorization_choose_le_log` gives a logarithmic upper bound on the valuation.\n   - `Nat.factorization_choose_le_one` states that primes `p > sqrt(n)` appear at most once.\n\n3. **Central Binomial Coefficient**:\n   - `Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul` bounds prime factors for `centralBinom`.\n   - No direct lemma was found relating `v_p(choose (m+k) k)` to `v_p(choose (2m) m)`. This relationship likely needs to be derived from the carry lemmas."
}
```

End Time: 2026-02-10T16:27:10.040Z
