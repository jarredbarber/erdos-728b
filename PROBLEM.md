# Erdős Problem 728

## Problem Statement

Let $\varepsilon > 0$ be sufficiently small and $C, C' > 0$ with $C < C'$. Are there infinitely many integers $a, b, n$ with $a, b > \varepsilon n$ such that

$$a! \cdot b! \mid n! \cdot (a+b-n)!$$

and

$$C \log n < a + b - n < C' \log n?$$

This asks whether the logarithmic gap phenomenon for factorial divisibility is achievable with balanced $a, b$ (both proportional to $n$).

## Formal Statement

```lean
theorem erdos_728 :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ C > (0 : ℝ), ∀ C' > C,
      ∃ a b n : ℕ,
        0 < n ∧
        ε * n < a ∧
        ε * n < b ∧
        a ! * b ! ∣ n ! * (a + b - n)! ∧
        a + b > n + C * log n ∧
        a + b < n + C' * log n
```

## Notes

This theorem has been proved.

---

# Erdős Problem 729

## Problem Statement

Let $P$ be a fixed positive integer. Suppose $a, b, n$ are positive integers such that for every prime $p > P$,

$$\nu_p(a!) + \nu_p(b!) \leq \nu_p(n!)$$

where $\nu_p$ denotes the $p$-adic valuation. Then $a + b \leq n + O(\log n)$.

## Formal Statement

```lean
theorem erdos_729 (P : ℕ) (hP : 0 < P) :
    ∃ C > (0 : ℝ), ∀ a b n : ℕ,
      (∀ p, p.Prime → P < p → padicValNat p a.factorial + padicValNat p b.factorial ≤ padicValNat p n.factorial) →
      (a : ℝ) + b ≤ n + C * Real.log (n + 2)
```

## Notes

This theorem has been proved.
