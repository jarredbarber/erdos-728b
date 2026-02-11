# Erdős 728: Formal Proof by Autonomous AI Agents

## The Experiment

Can autonomous LLM agents discover and formally verify a proof of an Erdős problem — with zero human mathematical input?

This repo contains the answer: **yes.** 2,906 lines of Lean 4, **0 sorrys, 0 axioms**, verified by `lake build`. The entire proof — strategy, lemma design, and Lean formalization — was produced by agents. A human (who deliberately did not learn the mathematics) selected the problem, set up infrastructure, and pressed go.

### Rules

- **Zero human mathematical input.** No hints about proof techniques. Agents received only the problem statement.
- **No web search.** Agents had no access to arXiv, Mathlib docs, or external references.
- **The compiler is the only reviewer.** `lake build` with 0 sorrys and 0 axioms is the sole acceptance criterion. Everything else is intermediate.

### Setup

- **Models:** Claude Opus 4.6 (Anthropic), Gemini 3 Pro, and Gemini 3 Flash (Google), randomly assigned per task
- **Workflow:** [timtam](https://github.com/jarredbarber/timtam) multi-agent system — explore agents discover NL proofs, verify agents review them, formalize agents write Lean. A planner decomposes problems into tasks. An overseer monitors progress.
- **Formalization:** Standard LLMs writing Lean as text, iterating against the compiler. No MCTS, no tactic-level search, no Lean-specific training. Just general-purpose models and `lake build`.
- **Lean:** 4.27.0 + Mathlib 4.27.0
- **Effort:** 66 tasks, all closed

### The Problem

**Erdős Problem 728:** For sufficiently small ε > 0 and any 0 < C < C', show there exist a, b, n ∈ ℕ with a, b > εn such that a!b! | n!(a+b-n)! and C log n < a+b-n < C' log n.

Previously resolved by GPT-5.2 + Aristotle ([arXiv:2601.07421](https://arxiv.org/abs/2601.07421)), which used MCTS-based tactic search (Aristotle/Harmonic) for formalization. Our agents had no access to that paper, used no specialized search — just LLMs generating Lean code and fixing compiler errors — and found a different construction for the hardest step (Chernoff + union bound vs. carry-rich/spike-free counting).

This is one of several Erdős problems attacked in this experiment. See the [full experiment writeup](https://gist.github.com/jarredbarber/10dff24643366d160e80e75766ae4df1) for results across all problems.

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

## Comparison with Published Proof (GPT-5.2 / Aristotle)

The published proof is [arXiv:2601.07421](https://arxiv.org/abs/2601.07421) by Sothanaphan (writeup of a proof by GPT-5.2 Pro + Aristotle/Harmonic, operated by Barreto). Our agents had no access to this paper.

### What's the same

Both proofs share the same high-level architecture:

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

### Assessment

Both proofs are valid. Our proof is more modular — each lemma is self-contained — which made it possible for agents to formalize in pieces. The Chernoff bound over digit spaces (328 lines) is reusable infrastructure. The carry dominance lemma is a clean standalone result about p-adic valuations of binomial coefficients.

---

## Architectural Comparison: Agent Systems

| | GPT-5.2 + Aristotle | Our system (timtam) |
|---|---|---|
| **Strategy generation** | GPT-5.2 Pro | Gemini 3 Pro / Claude Opus 4.6 (randomized) |
| **Formalization** | Aristotle (MCTS over Lean tactic states) | Same LLMs writing Lean as text, iterating against compiler |
| **Search method** | Tree search in tactic space | Generate-compile-fix loop |
| **Workflow** | Unclear (likely iterative NL→formal) | Explicit multi-agent pipeline: explore→verify→formalize with planner/advisor oversight |
| **Proof discovery** | Single system with tight NL↔formal loop | Role separation: explorers never see Lean, formalizers never invent math |

The MCTS approach (Aristotle) is likely more efficient at closing individual Lean goals — it searches the tactic space directly. Our agents fight the compiler iteratively, which is slower but uses only general-purpose LLMs with no Lean-specific training. The fact that both systems converged on the same mathematical strategy suggests the bottleneck is proof discovery, not formalization.

## Key Findings

- **Agents independently discovered Kummer's theorem** as the key tool (confirmed by clean replication — no technique hints given)
- **Agents CAN formalize probabilistic arguments** given sufficient task decomposition. The 1,510-line counting argument was the hardest part. It succeeded because it was decomposed into digit manipulation, residue classes, concentration bounds, and the main counting — each tractable alone
- **Decomposition is the meta-strategy.** 66 tasks, broken into focused pieces. Monolithic attempts at the probabilistic bound failed; decomposed attempts succeeded
- **Multi-model randomization** (Gemini + Claude, randomized per task) may contribute different strengths to different subtasks

---

*Completed: 2026-02-11. 2,906 lines Lean 4, 0 sorrys, 0 axioms, 66 tasks.*
