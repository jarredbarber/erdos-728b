# Lemma 3: Union Bound Arithmetic (Part E)

**Status:** Draft ✏️
**Statement:** Arithmetic proof of the union bound for Lemma 3, Part E.
**Dependencies:** `proofs/lemma3-counting.md` (for context)
**Confidence:** Certain

This document provides the detailed arithmetic proof for the union bound step in Lemma 3 (Part E). It is structured to facilitate direct formalization in Lean 4.

## Definitions

Fix an integer $k \ge 1$.
Let $m_0$ be a natural number.
Let $p$ be a prime with $p \le 2k$.

**Definition 1 (D_p):**
$$D_p := 36 \lceil \log_2(16k) \rceil + 36 \lfloor \log_p(k+1) \rfloor + 36$$

**Definition 2 (M_0):**
$$M_0(k) := (2k)^{72 \lceil \log_2(16k) \rceil + 72}$$

**Assumption:**
We assume $m_0 \ge M_0(k)$.

## Goal 1: Bounds on $D_p$

We prove two properties for $D_p$:
1.  $D_p \ge 16 \log_p(k+1) + 16$ (needed for the cascade threshold).
2.  $p^{D_p} \le m_0$ (needed to ensure $m_0$ is large enough).

### Proof of 1a: $D_p \ge 16 \log_p(k+1) + 16$

**Case 1: $p > k+1$**
1.  Since $p > k+1$, we have $k+1 < p$, so $\log_p(k+1) < 1$.
2.  Therefore, $\lfloor \log_p(k+1) \rfloor = 0$.
3.  The definition of $D_p$ becomes:
    $$D_p = 36 \lceil \log_2(16k) \rceil + 0 + 36 \ge 36$$
    (since $\lceil \dots \rceil \ge 0$).
4.  The RHS target is $16 \log_p(k+1) + 16$.
5.  Since $\log_p(k+1) < 1$, we have $16 \log_p(k+1) + 16 < 16(1) + 16 = 32$.
6.  Thus $D_p \ge 36 > 32 > 16 \log_p(k+1) + 16$. $\square$

**Case 2: $p \le k+1$**
1.  Since $p \le k+1$, we have $\log_p(k+1) \ge 1$.
2.  Use the inequality $x - 1 < \lfloor x \rfloor$ for $x = \log_p(k+1)$.
    $$D_p > 36 \lceil \log_2(16k) \rceil + 36 (\log_p(k+1) - 1) + 36$$
3.  Simplify:
    $$D_p > 36 \lceil \log_2(16k) \rceil + 36 \log_p(k+1) - 36 + 36$$
    $$D_p > 36 \lceil \log_2(16k) \rceil + 36 \log_p(k+1)$$
4.  Since $k \ge 1$, $16k \ge 16$, so $\log_2(16k) \ge 4$, so $\lceil \dots \rceil \ge 4 \ge 0$.
    $$D_p > 36 \log_p(k+1)$$
5.  We need to show $36 \log_p(k+1) \ge 16 \log_p(k+1) + 16$.
    Subtracting $16 \log_p(k+1)$ from both sides, this is equivalent to:
    $$20 \log_p(k+1) \ge 16$$
    $$\log_p(k+1) \ge \frac{16}{20} = \frac{4}{5} = 0.8$$
6.  This is true because we are in Case 2 where $\log_p(k+1) \ge 1$.
    ($1 \ge 0.8$).
7.  Thus $D_p > 36 \log_p(k+1) \ge 16 \log_p(k+1) + 16$. $\square$

### Proof of 1b: $p^{D_p} \le M_0(k) \le m_0$

We show $p^{D_p} \le M_0(k)$. The inequality $M_0(k) \le m_0$ is by assumption.

1.  Recall $D_p = 36 \lceil \log_2(16k) \rceil + 36 \lfloor \log_p(k+1) \rfloor + 36$.
2.  Exponentiate with base $p$:
    $$p^{D_p} = p^{36 \lceil \log_2(16k) \rceil} \cdot p^{36 \lfloor \log_p(k+1) \rfloor} \cdot p^{36}$$
3.  Bound the middle term:
    Since $\lfloor x \rfloor \le x$, we have $p^{\lfloor \log_p(k+1) \rfloor} \le p^{\log_p(k+1)} = k+1$.
    So $p^{36 \lfloor \log_p(k+1) \rfloor} \le (k+1)^{36}$.
4.  Bound $p$ by $2k$:
    Since $p \le 2k$, we have $p^X \le (2k)^X$ for any $X \ge 0$.
    Also $k+1 \le 2k$ (for $k \ge 1$).
5.  Substitute bounds into the product:
    $$p^{D_p} \le (2k)^{36 \lceil \log_2(16k) \rceil} \cdot (2k)^{36} \cdot (2k)^{36}$$
6.  Combine exponents:
    $$p^{D_p} \le (2k)^{36 \lceil \log_2(16k) \rceil + 36 + 36}$$
    $$p^{D_p} \le (2k)^{36 \lceil \log_2(16k) \rceil + 72}$$
7.  Compare with $M_0(k) = (2k)^{72 \lceil \log_2(16k) \rceil + 72}$:
    The exponent of $p^{D_p}$ is $36 \lceil \dots \rceil + 72$.
    The exponent of $M_0(k)$ is $72 \lceil \dots \rceil + 72$.
    Since $\lceil \log_2(16k) \rceil \ge 0$ (actually $\ge 4$), the exponent of $M_0(k)$ is strictly larger.
8.  Thus $p^{D_p} \le M_0(k) \le m_0$. $\square$

## Goal 2: Decay Estimate

We prove $2^{D_p/36} \ge 32k$.

1.  Start with the definition of $D_p$:
    $$D_p = 36 \lceil \log_2(16k) \rceil + 36 \lfloor \log_p(k+1) \rfloor + 36$$
2.  Divide by 36:
    $$\frac{D_p}{36} = \lceil \log_2(16k) \rceil + \lfloor \log_p(k+1) \rfloor + 1$$
3.  Since $\lfloor \log_p(k+1) \rfloor \ge 0$ (as $k+1 \ge 2, p \ge 2$), we have:
    $$\frac{D_p}{36} \ge \lceil \log_2(16k) \rceil + 1$$
4.  Use $\lceil x \rceil \ge x$:
    $$\frac{D_p}{36} \ge \log_2(16k) + 1$$
5.  Use logarithm rules: $\log_2(16k) + 1 = \log_2(16k) + \log_2(2) = \log_2(32k)$.
    $$\frac{D_p}{36} \ge \log_2(32k)$$
6.  Exponentiate base 2:
    $$2^{D_p/36} \ge 2^{\log_2(32k)} = 32k$$
    $\square$

## Goal 3: Per-Prime Contribution

Let $N(p)$ be the counting bound for a single prime $p$.
From Part C of Lemma 3, we have (using $D_p$ satisfies the condition 1a):
$$N(p) \le \frac{4 m_0}{2^{D_p/36}}$$
(Note: The bound is actually $\le \frac{2 m_0}{2^{D_p/36}} + \frac{2 p^{D_p}}{2^{D_p/36}}$. Using $p^{D_p} \le m_0$, this is $\le \frac{4 m_0}{2^{D_p/36}}$.)

1.  Substitute the decay estimate ($2^{D_p/36} \ge 32k$):
    $$\frac{1}{2^{D_p/36}} \le \frac{1}{32k}$$
2.  Multiply by $4 m_0$:
    $$N(p) \le \frac{4 m_0}{32k}$$
3.  Simplify fraction:
    $$N(p) \le \frac{m_0}{8k}$$
    $\square$

## Goal 4: Union Bound

We sum the bad counts over all primes $p \le 2k$.

1.  Total bad count $N_{total} \le \sum_{p \le 2k} N(p)$.
2.  Substitute per-prime bound:
    $$N_{total} \le \sum_{p \le 2k} \frac{m_0}{8k}$$
3.  The term $\frac{m_0}{8k}$ is constant with respect to $p$.
    $$N_{total} \le \pi(2k) \cdot \frac{m_0}{8k}$$
    where $\pi(x)$ is the prime-counting function.
4.  Use the trivial bound $\pi(x) \le x$ for $x \ge 2$:
    Since $k \ge 1$, $2k \ge 2$, so $\pi(2k) \le 2k$.
5.  Combine:
    $$N_{total} \le 2k \cdot \frac{m_0}{8k} = \frac{m_0}{4}$$
    $\square$

## Goal 5: Existence

1.  The number of bad $m \in [m_0, 2m_0)$ is at most $m_0/4$.
2.  The total number of integers in $[m_0, 2m_0)$ is $2m_0 - m_0 = m_0$.
3.  The number of good $m$ is:
    $$N_{good} \ge m_0 - \frac{m_0}{4} = \frac{3 m_0}{4}$$
4.  Since $m_0 \ge M_0(k) \ge (2k)^{72 \cdot 4 + 72} > 0$, we have $m_0 > 0$.
5.  Thus $3m_0/4 > 0$, so there exists at least one good $m$.
    $\square$
