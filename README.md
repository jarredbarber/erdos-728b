# Erdős 728: Formal Proof by Autonomous AI Agents

## Motivation

In January 2026, GPT-5.2 + Aristotle resolved Erdős Problem 728 ([arXiv:2601.07421](https://arxiv.org/abs/2601.07421)). That system used a tight loop between GPT-5.2 (proof strategy) and Aristotle/Harmonic (MCTS-based tactic search over Lean proof states) — a purpose-built pipeline with specialized Lean search.

We wanted to know: **can general-purpose LLMs do this without specialized search?** No MCTS, no tactic-level tree search, no Lean-specific training. Just off-the-shelf models writing Lean as text, iterating against the compiler, coordinated by a custom agent orchestrator.

**Result:** 2,906 lines of Lean 4, **0 sorrys, 0 axioms**, verified by `lake build`. The agents found a different construction for the hardest step — Chernoff + union bound instead of carry-rich/spike-free counting — with no access to the published proof.

## The Problem

**Erdős Problem 728:** For sufficiently small ε > 0 and any 0 < C < C', show there exist a, b, n ∈ ℕ with a, b > εn such that a!b! | n!(a+b-n)! and C log n < a+b-n < C' log n.

## Experimental Design

- **Zero human mathematical input.** No hints about proof techniques. Agents received only the problem statement.
- **No web search.** No access to arXiv, Mathlib docs, or external references.
- **The compiler is the only reviewer.** `lake build` with 0 sorrys and 0 axioms is the sole acceptance criterion.
- **Models:** Claude Opus 4.6 (Anthropic), Gemini 3 Pro, and Gemini 3 Flash (Google), randomly assigned per task.
- **Formalization:** LLMs generate Lean code, get compiler errors back, fix and retry. No specialized search.
- **Workflow:** Multi-agent system — explore agents discover NL proofs, verify agents review them, formalize agents write Lean. A planner decomposes problems into tasks.
- **Lean:** 4.27.0 + Mathlib 4.27.0
- **Effort:** 66 tasks, all closed

---

## Construction

Set **a = m, b = m+k, n = 2m** where k = a+b-n is the "gap." This reduces the divisibility condition to:

**C(m+k, k) | C(2m, m)**

(i.e., the binomial coefficient C(m+k,k) divides the central binomial coefficient C(2m,m)).

Choose k ≈ (C+C')/2 · log(2m₀) and find a suitable m ∈ [m₀, 2m₀].

## Three Lemmas

### Lemma 1: Reduction (`reduction_lemma`, Erdos/Lemmas.lean)
The factorial divisibility a!b! | n!k! is equivalent to C(m+k,k) | C(2m,m). Pure algebra.

### Lemma 2: Carry Dominance (`carry_dominance`, Erdos/Lemmas.lean)
For any prime **p > 2k** and any m: v_p(C(m+k,k)) ≤ v_p(C(2m,m)).

*Proof via Kummer's theorem.* Since p > 2k, k is a single base-p digit. Any carry in m+k forces a carry in m+m at the same position (because k < p/2, so m₀ ≥ p-k > p/2 implies 2m₀ ≥ p). Carry cascades through positions where mᵢ = p-1, which produce carries in m+m as well (2(p-1)+1 = 2p-1 ≥ p).

This holds for ALL m with no conditions.

### Lemma 3: Probabilistic bound (`count_bad_interval` + supporting infrastructure, Erdos/Lemma3*.lean + Erdos/Chernoff.lean)
For a prime **p ≤ 2k**, the number of "bad" m in [m₀, 2m₀) is at most m₀/(8k). Union bound over all primes p ≤ 2k: total bad < m₀, so a good m exists.

The argument has two parts:

**Upper bound on v_p(C(m+k,k)):** Carries in m+k beyond the digits of k form a "cascade" — a run of (p-1) digits in m. The cascade length L satisfies Pr[L ≥ ℓ] ≤ (1/p)^ℓ. So v_p(C(m+k,k)) ≤ (digits of k) + L, which is concentrated around log_p(k).

**Lower bound on v_p(C(2m,m)):** Carries in m+m are driven by independent events Aᵢ = {mᵢ ≥ ⌈p/2⌉}, each with probability ≥ 1/3. By Chernoff, v_p(C(2m,m)) ≥ D/6 with high probability, where D = log_p(m) is the number of digits.

Since D grows with m while log_p(k) = O(log log m), the lower bound dominates for large m.

## Main Theorem (`erdos_728`, Erdos/Basic.lean)

**Union bound** over all primes p ≤ 2k (there are O(k/log k) of them):

Total bad m ≤ Σ_{p≤2k} m₀/(8k) < m₀.

Therefore there exists m ∈ [m₀, 2m₀] with C(m+k,k) | C(2m,m), giving the desired (a,b,n) triple. Works for **all C > 0**, not just C < 1/2.

---

## Formalization

| File | Lines | Content |
|------|-------|---------|
| Basic.lean | 300 | Main theorem, union bound over small primes |
| Lemmas.lean | 152 | Reduction lemma, carry dominance (Kummer) |
| Lemma3Counting.lean | 1,510 | Core counting argument — bad residue sets, interval bounds |
| Lemma3.lean | 373 | Top-level probabilistic lemma |
| Chernoff.lean | 328 | Chernoff-type concentration over digit spaces |
| Lemma3Residue.lean | 138 | Residue class counting in intervals |
| Lemma3Common.lean | 28 | Shared definitions (high digits, digit spaces) |
| Digits.lean | 77 | Base-p digit manipulation, carry–valuation connection |
| **Total** | **2,906** | **0 sorrys, 0 axioms** |

---

## Prior Human Work

The high-level proof strategy traces back to human work on divisors of the central binomial coefficient:

- **Pomerance (2015)**, ["Divisors of the Middle Binomial Coefficient"](https://math.dartmouth.edu/~carlp/catalan5.pdf), *Amer. Math. Monthly*. Proved that for each fixed k ≥ 1, the set of n for which (n+k) | C(2n,n) has asymptotic density 1, using Kummer's theorem and the heuristic that base-p digit patterns behave "randomly."
- **Ford & Konyagin (2021)**, "Divisibility of the central binomial coefficient C(2n,n)," *Trans. AMS*. Extended Pomerance's methods to determine the density of n where n^ℓ | C(2n,n).

Our proof and the GPT-5.2/Aristotle proof both extend Pomerance's approach from fixed k to growing k ≍ log n. As the [Aletheia paper](https://arxiv.org/abs/2601.22401) (DeepMind, 2026) notes, these AI solutions "closely follow prior human arguments" by Pomerance.

**On originality:** We cannot distinguish whether agents independently discovered this strategy (Kummer → digit counting is arguably the natural approach once you know Kummer's theorem) or reproduced it from training data. Pomerance 2015 appeared in the widely-read *American Mathematical Monthly* and is almost certainly in LLM training corpora. This is the "subconscious plagiarism" problem identified by the Aletheia team: formal verification confirms correctness but cannot confirm originality.

## Comparison with Published Proof (GPT-5.2 / Aristotle)

The published proof is [arXiv:2601.07421](https://arxiv.org/abs/2601.07421) by Sothanaphan (writeup of a proof by GPT-5.2 Pro + Aristotle/Harmonic, operated by Barreto). Our agents had no access to this paper.

### What's the same

Both proofs share the same high-level architecture (also shared with Pomerance 2015):

| Step | Published | Ours (728b) |
|------|-----------|-------------|
| Substitution | a=m, b=m+k, n=2m | a=m, b=m+k, n=2m |
| Reduction | C(m+k,k) \| C(2m,m) | C(m+k,k) \| C(2m,m) |
| Key tool | Kummer's theorem (carry counting) | Kummer's theorem (carry counting) |
| Large primes (p > 2k) | Carry dominance (automatic) | Carry dominance (automatic) |
| Search space | m ∈ [M, 2M] | m ∈ [m₀, 2m₀] |

The symmetric construction and the Kummer-based prime-by-prime analysis appear to be natural attractors — multiple independent systems converged on this framework.

### What's different

The proofs diverge on **how they handle small primes (p ≤ 2k)**:

| Aspect | Published ("carry-rich, spike-free") | Ours (Chernoff + union bound) |
|--------|--------------------------------------|-------------------------------|
| **Strategy** | Find m that is simultaneously "carry-rich" and "spike-free" | Bound failure count per prime, then union bound |
| **Carries in m+m** | Counting argument: enough m in [M,2M] have ≥ threshold carries for all p ≤ 2k simultaneously | Chernoff bound: each digit independently contributes a carry with prob ≥ 1/3, so v_p(C(2m,m)) ≥ D/6 whp |
| **Carries in m+k** | "Spike-free" condition: avoid m where some m+j has unusually high p-adic valuation | Cascade length bound: carries beyond k's digits form a geometric run, Pr[L≥ℓ] ≤ (1/p)^ℓ |
| **Combining primes** | Deterministic counting: show "good" m is nonempty | Probabilistic: count bad m per prime, sum < m₀ |
| **Flavor** | Combinatorial counting / sieve | Probabilistic method (Chernoff + union bound) |

Both proofs are valid. Our proof is more modular — each lemma is self-contained — which made it possible for agents to formalize in pieces.

## Comparison with DeepMind's Aletheia (Gemini Deep Think)

The [Aletheia paper](https://arxiv.org/abs/2601.22401) (DeepMind, 2026) ran Gemini Deep Think on 700 open Erdős problems. **Aletheia did not solve 728.** The 728 result came separately from K. Barreto using GPT-5.2 Pro + Aristotle (Harmonic). Barreto is a co-author on both papers.

The two efforts represent fundamentally different approaches to AI-assisted mathematics:

| | Aletheia (DeepMind) | Our system |
|---|---|---|
| **Model** | Gemini Deep Think | Claude Opus 4.6 + Gemini 3 Pro (randomized) |
| **Scale** | 700 problems, broad sweep | Single problem, deep focus |
| **Output** | Natural language proofs | Formal Lean 4 proofs |
| **Verification** | Human expert evaluation (15+ mathematicians) | Lean compiler (`lake build`) |
| **Correctness rate** | 31.5% technically correct, 6.5% meaningfully correct | Binary: compiles or doesn't |
| **Focus** | "Can AI solve open problems?" | "Can AI produce reusable formalized infrastructure?" |
| **Biggest challenge** | Literature search + problem misinterpretation | Lean/Mathlib friction (casting, simp failures) |

### What Aletheia found that we can't

- **Problem misinterpretation**: 50 of their 63 correct solutions answered the wrong question (definitional ambiguity, Erdős's intent vs literal statement). Formal verification can't catch this — if the theorem statement is wrong, a correct proof of the wrong statement still compiles.
- **Literature identification**: 9 of their 13 results were already in the literature. Determining originality requires human expertise that no formal system provides.
- **"Subconscious plagiarism"**: LLMs may reproduce training data without attribution. They flag this explicitly.

### What we found that Aletheia can't

- **Guaranteed correctness**: Their 68.5% false-positive rate (137/200 solutions were wrong) is eliminated by compiler verification. Our proof either compiles with 0 sorrys or it doesn't.
- **Reusable formalized infrastructure**: The proof produced standalone lemma files — Kummer criterion, carry dominance, Chernoff over digit spaces — that future proofs can import directly.
- **Agent failure transcripts**: 269 worker logs documenting exactly how agents fail with Lean/Mathlib, useful for improving both agents and Mathlib's API ([friction report](https://gist.github.com/jarredbarber/c541d6d7f35582d97fffc227b2dde692)).

### The complementarity

Aletheia is better at breadth: sweep 700 problems, find the low-hanging fruit, identify literature gaps. Our system is better at depth: take one problem and produce a compiler-verified proof with reusable infrastructure. Neither system catches both mathematical errors AND problem misformulation. The ideal pipeline would combine NL exploration (Aletheia-style) with formal verification (our style), with human experts auditing the theorem statement.

## Limitations and Honest Assessment

This is an **AI systems contribution, not a mathematics contribution.** The mathematical content — extending Pomerance's density-1 result from fixed k to growing k ≍ log n — is incremental. Any number theorist familiar with Pomerance's work could likely produce this proof. The contribution is demonstrating that general-purpose LLMs can discover and formally verify such proofs autonomously.

We are not mathematicians. We cannot evaluate the significance of the individual lemmas or whether they represent genuinely novel abstractions vs. recombination of training data. A number theorist's evaluation would be needed for that determination.

## Key Findings

- **Agents independently discovered Kummer's theorem** as the key tool (confirmed by clean replication — no technique hints given)
- **Agents CAN formalize probabilistic arguments** given sufficient task decomposition. The 1,510-line counting argument was the hardest part. It succeeded because it was decomposed into digit manipulation, residue classes, concentration bounds, and the main counting — each tractable alone
- **Decomposition is the meta-strategy.** 66 tasks, broken into focused pieces. Monolithic attempts at the probabilistic bound failed; decomposed attempts succeeded
- **Multi-model randomization** (Gemini + Claude, randomized per task) may contribute different strengths to different subtasks. This was ultimately done to "load balance" over model usage quotas, but we conjecture there may be value in this by e.g. reducing failure mode correlations.

---

*Completed: 2026-02-11. 2,906 lines Lean 4, 0 sorrys, 0 axioms, 66 tasks.*
