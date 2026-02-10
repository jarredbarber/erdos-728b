# Mathlib Coverage: Chernoff Bounds

## Available Results

The primary source for Chernoff-Hoeffding type bounds in Mathlib is `Mathlib.Probability.Moments.SubGaussian`. This file contains general sub-Gaussian concentration inequalities which imply the standard Chernoff bounds for sums of independent bounded random variables (like Bernoulli trials).

### Sub-Gaussian Concentration (Hoeffding)

For independent sub-Gaussian random variables $X_i$, the sum $S_n = \sum X_i$ satisfies:

$$ \Pr(S_n - \mathbb{E}[S_n] \ge t) \le \exp\left( \frac{-t^2}{2 \sum c_i} \right) $$

where $c_i$ is the sub-Gaussian parameter of $X_i$.

**Mathlib Theorem:** `ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun`
```lean
lemma measure_sum_ge_le_of_iIndepFun {ι : Type*} {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    {c : ι → ℝ≥0}
    {s : Finset ι} (h_subG : ∀ i ∈ s, HasSubgaussianMGF (X i) (c i) μ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i ∈ s, X i ω} ≤ exp (-ε ^ 2 / (2 * ∑ i ∈ s, c i))
```

### Application to Bernoulli Trials

For a Bernoulli variable $X_i \in \{0, 1\}$ with mean $p$, $X_i - p \in [-p, 1-p]$ is sub-Gaussian with parameter $1/4$ (by Hoeffding's Lemma, range length 1).

**Mathlib Lemma:** `ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`
```lean
lemma hasSubgaussianMGF_of_mem_Icc [IsProbabilityMeasure μ] {a b : ℝ} (hm : AEMeasurable X μ)
    (hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    HasSubgaussianMGF (fun ω ↦ X ω - μ[X]) ((‖b - a‖₊ / 2) ^ 2) μ
```

For sum of $n$ i.i.d. Bernoulli(p) trials, $\mu = np$.
We want to bound $\Pr(S_n < \mu/2) = \Pr(S_n - \mu < -\mu/2)$.
This is equivalent to bounding the upper tail of $-(S_n - \mu)$.
Since $-(X_i - p)$ is also sub-Gaussian with parameter $1/4$, the sum of $n$ such variables has parameter $n/4$.
Applying `measure_sum_ge_le_of_iIndepFun` with $\epsilon = \mu/2$:

$$ \Pr(S_n < \mu/2) \le \exp\left( \frac{-(\mu/2)^2}{2 (n/4)} \right) = \exp\left( \frac{-\mu^2/4}{n/2} \right) = \exp\left( \frac{-\mu^2}{2n} \right) = \exp\left( \frac{-n^2 p^2}{2n} \right) = \exp\left( \frac{-n p^2}{2} \right) $$

For $p=1/2$, $\mu = n/2$.
Bound: $\exp(-n/8) = \exp(-\mu/4)$.

This is stronger than the requested bound $\exp(-\mu/8)$.

## General Chernoff Bound (Method)

Mathlib also provides the general Chernoff bound method using moment-generating functions in `Mathlib.Probability.Moments.Basic`.

**Mathlib Theorem:** `ProbabilityTheory.measure_le_le_exp_cgf`
```lean
theorem measure_le_le_exp_cgf [IsFiniteMeasure μ] (ε : ℝ) (ht : t ≤ 0)
    (h_int : Integrable (fun ω => exp (t * X ω)) μ) :
    μ.real {ω | X ω ≤ ε} ≤ exp (-t * ε + cgf X μ t)
```

This can be used to derive the standard multiplicative Chernoff bound $\exp(-\mu \delta^2 / 2)$ if needed, by optimizing over $t$. However, for most applications involving bounded variables, the sub-Gaussian bound in `SubGaussian.lean` is more convenient and sufficient.

## Recommendation

Use `ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun` in `Mathlib.Probability.Moments.SubGaussian.lean`.
You will need to use `hasSubgaussianMGF_of_mem_Icc` to establish the sub-Gaussian property for Bernoulli variables.
For the lower tail, apply the upper tail bound to the negated variables.
