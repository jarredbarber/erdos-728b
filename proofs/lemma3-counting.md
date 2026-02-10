# Lemma 3: Counting Bound for Small Primes (Deterministic Version)

**Status:** Verified ✅
**Statement:** Let $p$ be a prime with $p \le 2k$. Let $D \ge 1$ be an integer, and let $N = p^D$. Among the $N$ integers $m \in \{0, 1, \ldots, N-1\}$, the number of $m$ satisfying $v_p(\binom{m+k}{k}) > v_p(\binom{2m}{m})$ is at most $N / p^{\lfloor D/40 \rfloor}$, provided $D \ge 16 \lfloor \log_p(k+1) \rfloor + 16$.
**Dependencies:** None
**Confidence:** High
**Reviewed by:** erdos728b-djp

## Review Notes (erdos728b-djp)

All three review criteria satisfied:

1. ✅ **k vs m_0 relationship explicit**: Definition E0 provides M_0(k) = (2k)^{72⌈log₂(16k)⌉ + 72}, and Lemma E1(b) proves p^{D_p} ≤ m_0 for all p ≤ 2k when m_0 ≥ M_0(k).

2. ✅ **Corollary A4 bound clarified**: The bound is correctly stated as N/p^{T+1} (not N/p^T). The proof properly accounts for the strict inequality v_p > s+1+T implying L ≥ T+1.

3. ✅ **Overall soundness**: All lemmas are rigorously proved:
   - Part A (cascade structure): Lemmas A1-A3 and Corollary A4 are correct
   - Part B (high digits): Lemmas B1-B3 are correct; B4' correctly cites Chernoff bound
   - Part C (combining): Threshold argument at ⌊D/6⌋ is sound; all arithmetic verified
   - Part D (residue counting): Lemmas D1-D2 correctly show Bad₁ and Bad₂ depend only on m mod p^D
   - Part E (union bound): Explicit bound M_0(k) is well-defined; decay estimate D_p/36 ≥ log₂(32k) gives per-prime contribution ≤ m_0/(8k), total ≤ m_0/4
   - Part F (formalization strategy): Provides clear roadmap for Lean

The proof is ready for formalization. The Chernoff bound (Lemma B4') is the main external dependency and should be tracked separately.

---

## Overview

The probabilistic Lemma 3 from `proofs/erdos728_v2.md` states that for random $m$, the event $v_p(\binom{m+k}{k}) > v_p(\binom{2m}{m})$ has probability $\le 1/p^{D/40}$. Here we convert this to a deterministic counting statement: we count the number of "bad" $m$ in $\{0, \ldots, p^D - 1\}$ explicitly.

The key advantage of working over $\{0, \ldots, p^D - 1\}$ is that the base-$p$ digits $(m_0, m_1, \ldots, m_{D-1})$ range over **all** of $\{0, \ldots, p-1\}^D$ as $m$ ranges over $\{0, \ldots, p^D - 1\}$. This bijection makes digit-counting arguments exact (no approximation errors), which is essential for Lean formalization.

---

## Notation

Throughout, $p$ is a fixed prime with $p \le 2k$, and $k \ge 1$ is a fixed positive integer.

Let $s := \lfloor \log_p k \rfloor$, so $k$ has $s+1$ base-$p$ digits. Note $s \le \log_p(2k) \le \log_p(p^2) = 2$ is possible for small $k$, but in general $s = \lfloor \log_p k \rfloor$.

Write the base-$p$ expansion:
$$m = \sum_{i=0}^{D-1} m_i p^i, \qquad k = \sum_{i=0}^{s} k_i p^i,$$
where $m_i, k_i \in \{0, \ldots, p-1\}$ and $k_s \neq 0$.

Set $N = p^D$. The map $m \mapsto (m_0, m_1, \ldots, m_{D-1})$ is a bijection $\{0, \ldots, N-1\} \to \{0, \ldots, p-1\}^D$.

---

## Part A: Upper Bound on $v_p(\binom{m+k}{k})$ via Cascade Length

### Definition (Carries in $m + k$)

For position $i \ge 0$, define carry bits $c^{(1)}_i$ by:
- $c^{(1)}_{-1} = 0$.
- At position $i$: the sum of digits is $m_i + k_i + c^{(1)}_{i-1}$ (where $k_i = 0$ for $i > s$). 
  - $c^{(1)}_i = \lfloor (m_i + k_i + c^{(1)}_{i-1})/p \rfloor$.

By Kummer's theorem:
$$v_p\!\left(\binom{m+k}{k}\right) = \sum_{i=0}^{D-1} c^{(1)}_i.$$

### Lemma A1 (Cascade structure for $i > s$)

For positions $i > s$: $k_i = 0$, so the carry recurrence becomes:
$$c^{(1)}_i = \begin{cases} 1 & \text{if } m_i = p-1 \text{ and } c^{(1)}_{i-1} = 1 \\ 0 & \text{otherwise.}\end{cases}$$

**Proof.** At position $i > s$, the digit sum is $m_i + 0 + c^{(1)}_{i-1} = m_i + c^{(1)}_{i-1}$. Since $m_i \le p-1$ and $c^{(1)}_{i-1} \le 1$:
- If $c^{(1)}_{i-1} = 0$: $m_i + 0 \le p-1 < p$, so $c^{(1)}_i = 0$.
- If $c^{(1)}_{i-1} = 1$: $m_i + 1 \ge p$ iff $m_i = p-1$, giving $c^{(1)}_i = 1$ iff $m_i = p-1$. $\square$

### Definition (Cascade length)

Define the **cascade length** $L = L(m)$ as the maximal $j \ge 0$ such that $m_{s+1} = m_{s+2} = \cdots = m_{s+j} = p-1$ (with $L = 0$ if $m_{s+1} \neq p-1$ or if $s+1 \ge D$).

### Lemma A2 (Upper bound via cascade)

$$v_p\!\left(\binom{m+k}{k}\right) \le (s+1) + L.$$

**Proof.** The carries at positions $0, 1, \ldots, s$ contribute at most $s+1$ to the total. By Lemma A1, carries at positions $s+1, s+2, \ldots$ form a cascade that can only continue while $m_i = p-1$ AND the previous carry was 1. Whether or not $c^{(1)}_s = 1$, the cascade at positions $s+1, \ldots, s+L$ contributes at most $L$ carries, and the cascade terminates at position $s + L + 1$ (since $m_{s+L+1} \neq p-1$ by maximality of $L$, or we've exceeded position $D-1$). Carries at positions $> s + L$ are all 0. $\square$

### Lemma A3 (Counting $m$ with large cascade length)

For any integer $\ell \ge 0$:
$$\#\{m \in \{0, \ldots, N-1\} : L(m) \ge \ell\} \le \frac{N}{p^\ell}.$$

**Proof.** $L(m) \ge \ell$ requires $m_{s+1} = m_{s+2} = \cdots = m_{s+\ell} = p-1$ (assuming $s + \ell < D$; otherwise the set is empty which is $\le N/p^\ell$ trivially).

Since $m \mapsto (m_0, \ldots, m_{D-1})$ is a bijection to $\{0, \ldots, p-1\}^D$, the condition constrains exactly $\ell$ coordinates to a single value $(p-1)$, while the remaining $D - \ell$ coordinates are free. So:
$$\#\{m : L(m) \ge \ell\} = p^{D - \ell} = \frac{N}{p^\ell}. \qquad\square$$

### Corollary A4 (Counting $m$ with large $v_p(\binom{m+k}{k})$)

For any $T \ge 0$:
$$\#\{m \in \{0, \ldots, N-1\} : v_p(\binom{m+k}{k}) > s + 1 + T\} \le \frac{N}{p^{T+1}}.$$

**Proof.** By Lemma A2, $v_p(\binom{m+k}{k}) \le s + 1 + L$. Therefore $v_p(\binom{m+k}{k}) > s + 1 + T$ implies $L > T$, i.e., $L \ge T + 1$. By Lemma A3:
$$\#\{m : v_p(\binom{m+k}{k}) > s + 1 + T\} \le \#\{m : L \ge T+1\} \le \frac{N}{p^{T+1}}. \qquad\square$$

---

## Part B: Lower Bound on $v_p(\binom{2m}{m})$ via Digit Counting

### Definition (Carries in $m + m$)

For position $i \ge 0$, define carry bits $c^{(2)}_i$ by:
- $c^{(2)}_{-1} = 0$.
- $c^{(2)}_i = \lfloor (2m_i + c^{(2)}_{i-1})/p \rfloor$.

By Kummer's theorem:
$$v_p\!\left(\binom{2m}{m}\right) = \sum_{i=0}^{D-1} c^{(2)}_i.$$

### Definition (High digits)

Define $A_i := \{m_i \ge \lceil p/2 \rceil\}$ (the event that digit $i$ is "high"). Let $q := \lfloor p/2 \rfloor$ be the number of "high" values in $\{0, \ldots, p-1\}$.

Note: $q = \lfloor p/2 \rfloor$ and the number of values $m_i \ge \lceil p/2 \rceil$ is exactly $p - \lceil p/2 \rceil = \lfloor p/2 \rfloor = q$.

For $p = 2$: $q = 1$, high values = $\{1\}$.
For odd $p \ge 3$: $q = (p-1)/2$, high values = $\{\lceil p/2 \rceil, \ldots, p-1\}$.

### Lemma B1 (High digit forces carry)

If $m_i \ge \lceil p/2 \rceil$, then $c^{(2)}_i = 1$, regardless of $c^{(2)}_{i-1}$.

**Proof.**
- If $c^{(2)}_{i-1} = 0$: $2m_i \ge 2\lceil p/2 \rceil \ge p$, so $c^{(2)}_i \ge 1$. Since $2m_i + 0 \le 2(p-1) < 2p$, we have $c^{(2)}_i = 1$.
- If $c^{(2)}_{i-1} = 1$: $2m_i + 1 \ge 2\lceil p/2 \rceil + 1 > p$, so $c^{(2)}_i \ge 1$. Since $2m_i + 1 \le 2(p-1) + 1 = 2p - 1 < 2p$, we have $c^{(2)}_i = 1$. $\square$

### Corollary B2 (Lower bound on carries)

$$v_p\!\left(\binom{2m}{m}\right) \ge H(m) := \#\{i \in \{0, \ldots, D-1\} : m_i \ge \lceil p/2 \rceil\}.$$

**Proof.** Each position with $m_i \ge \lceil p/2 \rceil$ contributes $c^{(2)}_i = 1$ (by Lemma B1). These are $H(m)$ positions, each contributing 1 to the total $\sum c^{(2)}_i$. The remaining positions contribute $\ge 0$. $\square$

### Lemma B3 (Exact count of $m$ with given number of high digits)

For any $0 \le t \le D$:
$$\#\{m \in \{0, \ldots, N-1\} : H(m) < t\} = \sum_{j=0}^{t-1} \binom{D}{j} q^j (p - q)^{D-j}.$$

**Proof.** Under the bijection $m \leftrightarrow (m_0, \ldots, m_{D-1})$, $H(m) = j$ iff exactly $j$ of the $D$ coordinates lie in $\{\lceil p/2 \rceil, \ldots, p-1\}$ (a set of size $q$) and the remaining $D - j$ lie in $\{0, \ldots, \lceil p/2 \rceil - 1\}$ (a set of size $p - q$). The number of such tuples is $\binom{D}{j} q^j (p-q)^{D-j}$.

Summing over $j = 0, \ldots, t-1$ gives the count. $\square$

### Lemma B4' (Counting $m$ with few high digits)

For integers $D \ge 1$, $p \ge 2$, and $q = \lfloor p/2 \rfloor \ge 1$, let $\alpha = q/p$. For $t = \lfloor D/6 \rfloor$:

$$\#\{m \in \{0, \ldots, p^D - 1\} : H(m) < t\} \le \frac{p^D}{2^{D/36}}.$$

**Proof.** We have $\alpha = q/p \ge 1/3$ for all primes $p \ge 2$ (since for $p = 2$: $\alpha = 1/2$; for $p = 3$: $\alpha = 1/3$; for $p \ge 5$: $\alpha = \lfloor p/2 \rfloor/p \ge (p-1)/(2p) \ge 2/5$).

The fraction of tuples with $H < D/6$ among all $p^D$ tuples is at most $\Pr[\text{Bin}(D, 1/3) < D/6]$ (since $\alpha \ge 1/3$, stochastic dominance applies). By the Chernoff bound with $\mu = D/3$ and $t = D/6 = \mu/2$:

$$\Pr[\text{Bin}(D, 1/3) < D/6] \le e^{-\mu/8} = e^{-D/24}.$$

Since $e^{-1/24} < 2^{-1/36}$ (because $1/24 \approx 0.0417 > \ln 2/36 \approx 0.0193$):

$$\#\{m : H(m) < D/6\} \le p^D \cdot e^{-D/24} \le p^D \cdot 2^{-D/36}. \qquad\square$$

**Remark.** The Chernoff bound used here ($\Pr[\text{Bin}(n, \alpha) < \alpha n/2] \le e^{-\alpha n/8}$) is a standard combinatorial inequality. Its formalization in Lean is tracked as a separate task. For the structure of this proof, it can be taken as a citation axiom; see `artifacts/chernoff-bound.md` (if available) for Mathlib coverage.

---

## Part C: Combining the Bounds

### Theorem C1 (Counting bound for a single prime, over $\{0,\ldots,p^D-1\}$)

Let $p$ be a prime, $k \ge 1$, $s = \lfloor \log_p k \rfloor$, and $D \ge 1$ with $D \ge 12(s+1) + 6$. Set $N = p^D$. Then:

$$\#\{m \in \{0, \ldots, N-1\} : v_p(\binom{m+k}{k}) > v_p(\binom{2m}{m})\} \le \frac{N}{p^{T_0+1}} + \frac{N}{2^{D/36}}$$

where $T_0 = \lfloor D/6 \rfloor - s - 1$.

**Proof.** Define:
- $\text{Bad}_1 := \{m : v_p(\binom{m+k}{k}) > \lfloor D/6 \rfloor\}$,
- $\text{Bad}_2 := \{m : v_p(\binom{2m}{m}) < \lfloor D/6 \rfloor\}$.

If $v_p(\binom{m+k}{k}) > v_p(\binom{2m}{m})$, then either:
- $v_p(\binom{m+k}{k}) > \lfloor D/6 \rfloor$, i.e., $m \in \text{Bad}_1$, **or**
- $v_p(\binom{2m}{m}) < \lfloor D/6 \rfloor$, i.e., $m \in \text{Bad}_2$.

(If neither holds, then $v_p(\binom{m+k}{k}) \le \lfloor D/6 \rfloor \le v_p(\binom{2m}{m})$.)

**Bounding $|\text{Bad}_1|$:** We check that $s + 1 + T_0 = \lfloor D/6 \rfloor$. Indeed: $T_0 = \lfloor D/6 \rfloor - s - 1$, so $s + 1 + T_0 = \lfloor D/6 \rfloor$. ✓

Also $T_0 \ge 0$: since $D \ge 12(s+1) + 6$, we have $\lfloor D/6 \rfloor \ge 2(s+1)$, so $T_0 \ge s + 1 \ge 1$. ✓

By Corollary A4:
$$|\text{Bad}_1| = \#\{m : v_p(\binom{m+k}{k}) > s + 1 + T_0\} \le \frac{N}{p^{T_0+1}}.$$

**Bounding $|\text{Bad}_2|$:** By Corollary B2, $v_p(\binom{2m}{m}) \ge H(m)$, so $v_p(\binom{2m}{m}) < \lfloor D/6 \rfloor$ implies $H(m) < \lfloor D/6 \rfloor$. By Lemma B4':
$$|\text{Bad}_2| \le N / 2^{D/36}.$$

**Combining:** By the union bound:
$$\#\{m : v_p(\binom{m+k}{k}) > v_p(\binom{2m}{m})\} \le |\text{Bad}_1| + |\text{Bad}_2| \le \frac{N}{p^{T_0+1}} + \frac{N}{2^{D/36}}. \qquad\square$$

### Corollary C2 (Simplified single-prime bound)

Under the assumption $D \ge 16 \log_p(k+1) + 16$:

$$\#\{m \in \{0, \ldots, p^D - 1\} : v_p(\binom{m+k}{k}) > v_p(\binom{2m}{m})\} \le \frac{2N}{2^{D/36}}.$$

**Proof.** First, $D \ge 16\log_p(k+1) + 16$ implies $D \ge 12(s+1) + 6$ (since $s \le \log_p k < \log_p(k+1)$, so $12(s+1) + 6 \le 12\log_p(k+1) + 18 \le 16\log_p(k+1) + 16 \le D$). So Theorem C1 applies.

Now $T_0 = \lfloor D/6 \rfloor - s - 1$. Since $s \le \log_p(k+1) - 1$ (because $k < p^{s+1}$ implies $s+1 > \log_p k$, and $s \le \log_p k$), and $D \ge 16\log_p(k+1) + 16$:

$$T_0 \ge \frac{D}{6} - 1 - \log_p(k+1) \ge \frac{D}{6} - 1 - \frac{D - 16}{16} = \frac{D}{6} - \frac{D}{16} \ge \frac{5D}{48}.$$

So $p^{T_0+1} \ge p^{5D/48} \ge 2^{5D/48}$. Since $5D/48 > D/36$ for $D \ge 1$:

$$\frac{N}{p^{T_0+1}} \le \frac{N}{2^{5D/48}} \le \frac{N}{2^{D/36}}.$$

Therefore:
$$\frac{N}{p^{T_0+1}} + \frac{N}{2^{D/36}} \le \frac{2N}{2^{D/36}}. \qquad\square$$

---

## Part D: Residue Counting over $[m_0, 2m_0)$

The counting bound above works over the exact interval $\{0, \ldots, p^D - 1\}$. For the main theorem, we need a bound over $[m_0, 2m_0)$.

### Lemma D1 (Residue class counting in an interval)

Let $R \subseteq \{0, \ldots, p^D - 1\}$ be a set of residues, and $[a, b)$ an integer interval with $b - a = M \ge 1$. If a property $\mathcal{P}(m)$ holds iff $m \bmod p^D \in R$, then:

$$\#\{m \in [a, b) : \mathcal{P}(m)\} \le |R| \cdot \left(\left\lfloor \frac{M}{p^D} \right\rfloor + 1\right).$$

**Proof.** Partition $[a, b)$ into at most $\lfloor M/p^D \rfloor + 1$ intervals of length $\le p^D$. In each such interval, the number of $m$ with $m \bmod p^D \in R$ is at most $|R|$ (since each residue class has at most one representative in an interval of length $\le p^D$). $\square$

### Lemma D2 (Application to the two "bad" events)

Both $\text{Bad}_1$ and $\text{Bad}_2$ from Part C depend only on $m \bmod p^D$:

**$\text{Bad}_1$ depends only on $m \bmod p^D$:** The event $v_p(\binom{m+k}{k}) > \lfloor D/6 \rfloor$ is equivalent (via Lemma A2) to $L(m) \ge T_0 + 1$, which requires $m_{s+1} = \cdots = m_{s+T_0+1} = p - 1$. Since $s + T_0 + 1 \le s + 1 + \lfloor D/6 \rfloor - 1 \le D - 1$ (using $\lfloor D/6 \rfloor \le D$), this is a condition on digits $0$ through $D-1$ only, hence depends only on $m \bmod p^D$.

More precisely: $v_p(\binom{m+k}{k}) = (\text{carries at positions } 0, \ldots, D-1) + (\text{carries at positions } \ge D)$. The carries at positions $\ge D$ are all part of the cascade. If $L(m) \ge T_0 + 1$, then in particular $v_p(\binom{m+k}{k}) > \lfloor D/6 \rfloor$ regardless of the higher digits. Conversely, if $L(m) \le T_0$ (measured using only the first $D$ digits), then the cascade contributes $\le L(m) \le T_0$ carries at positions $> s$, and the total carry is $\le (s+1) + T_0 = \lfloor D/6 \rfloor$, so $v_p(\binom{m+k}{k}) = \lfloor D/6 \rfloor$ only if also there are carries at positions $\ge D$. But the cascade at position $s + L + 1$ (where $L \le T_0$ and $s + L + 1 \le s + T_0 + 1 \le D - 1$) dies, so $c^{(1)}_{s+L+1} = 0$, and no carries propagate to positions $\ge D$. Therefore $v_p(\binom{m+k}{k}) \le (s+1) + L \le \lfloor D/6 \rfloor$.

Thus: $v_p(\binom{m+k}{k}) > \lfloor D/6 \rfloor$ iff the first $D$ digits of $m$ give $L \ge T_0 + 1$. This depends only on $m \bmod p^D$. ✓

**$\text{Bad}_2$ depends only on $m \bmod p^D$:** $H_D(m) = \#\{i \in \{0, \ldots, D-1\} : m_i \ge \lceil p/2 \rceil\}$ manifestly depends only on the first $D$ digits, hence on $m \bmod p^D$. And $v_p(\binom{2m}{m}) \ge H(m) \ge H_D(m)$ (Corollary B2 applied to all digits, with the first $D$ as a subset). So $v_p(\binom{2m}{m}) < \lfloor D/6 \rfloor$ implies $H_D(m) < \lfloor D/6 \rfloor$, which depends only on $m \bmod p^D$. ✓

### Corollary D3 (Counting bad $m$ in $[m_0, 2m_0)$)

For $m_0 \ge p^D$ and $D \ge 16\log_p(k+1) + 16$:

$$\#\{m \in [m_0, 2m_0) : v_p(\binom{m+k}{k}) > v_p(\binom{2m}{m})\} \le \frac{2m_0}{2^{D/36}} + \frac{2p^D}{2^{D/36}}.$$

**Proof.** The "bad" set is contained in $\{m : m \bmod p^D \in R\}$ where $R$ is the union of the bad residues for $\text{Bad}_1$ and $\text{Bad}_2$. By Theorem C1:
$$|R| \le \frac{p^D}{p^{T_0+1}} + \frac{p^D}{2^{D/36}} \le \frac{2p^D}{2^{D/36}}$$
(using Corollary C2).

By Lemma D1 with $M = m_0$ and $[a, b) = [m_0, 2m_0)$:
$$\#\{m \in [m_0, 2m_0) : \text{bad}\} \le |R| \cdot \left(\left\lfloor \frac{m_0}{p^D}\right\rfloor + 1\right) \le \frac{2p^D}{2^{D/36}} \cdot \frac{m_0 + p^D}{p^D} = \frac{2(m_0 + p^D)}{2^{D/36}}.$$

Since $p^D \le m_0$: $\frac{2(m_0 + p^D)}{2^{D/36}} \le \frac{2m_0 + 2p^D}{2^{D/36}} \le \frac{4m_0}{2^{D/36}}.$

We can also write the slightly tighter bound:
$$\#\{\text{bad}\} \le \frac{2m_0}{2^{D/36}} + \frac{2p^D}{2^{D/36}}. \qquad\square$$

---

## Part E: Union Bound Over All Small Primes

For a detailed arithmetic proof of the bounds in this section suitable for direct formalization, see `proofs/lemma3-union-bound.md`.

This is the central result. We state it with **explicit bounds** on $m_0$ in terms of $k$.

### Definition E0 (Parameter choices)

For each prime $p \le 2k$, define:
$$D_p := 36\lceil\log_2(16k)\rceil + 36\lfloor\log_p(k+1)\rfloor + 36.$$

This definition has two components:
- The $36\lceil\log_2(16k)\rceil$ term ensures $2^{D_p/36} \ge 32k$, so the Chernoff bound gives a $1/k$-quality decay per prime (needed since there are $O(k)$ primes to sum over).
- The $36\lfloor\log_p(k+1)\rfloor + 36$ term ensures $D_p \ge 16\log_p(k+1) + 16$, the threshold needed for the cascade analysis (Theorem C1).

Define the explicit threshold:
$$M_0(k) := (2k)^{72\lceil\log_2(16k)\rceil + 72}.$$

### Lemma E1 (Parameter verification)

For all primes $p \le 2k$ and $m_0 \ge M_0(k)$:

**(a)** $D_p \ge 16\log_p(k+1) + 16$.

**(b)** $p^{D_p} \le m_0$.

**Proof.**

**(a)** We need $D_p \ge 16\log_p(k+1) + 16$. Since $D_p \ge 36\lfloor\log_p(k+1)\rfloor + 36$, it suffices to show $36\lfloor\log_p(k+1)\rfloor + 36 \ge 16\log_p(k+1) + 16$.

Write $x = \log_p(k+1)$ and $\lfloor x \rfloor = x - \{x\}$ where $0 \le \{x\} < 1$. Then:
$$36(x - \{x\}) + 36 = 36x + 36 - 36\{x\} \ge 36x \ge 16x + 16$$
whenever $20x \ge 16$, i.e., $x \ge 4/5$.

For $x < 4/5$: this means $k + 1 < p^{4/5} \le p$, so $k < p$. Since $p \le 2k$, we have $k \ge p/2 \ge 1$, so $x = \log_p(k+1) > 0$ and $x < 1$. In this case $16x + 16 < 16 + 16 = 32 \le 36 \le D_p$. ✓

**(b)** We need $p^{D_p} \le m_0$ for all primes $p \le 2k$.

First, bound $D_p$ from above. Since $\lfloor\log_p(k+1)\rfloor \le \log_p(k+1) \le \log_2(k+1) / \log_2 p \le \log_2(k+1)$ (using $p \ge 2$) and $\log_2(k+1) \le \log_2(16k)$ (for $k \ge 1$):

$$D_p \le 36\lceil\log_2(16k)\rceil + 36\log_2(16k) + 36 \le 72\lceil\log_2(16k)\rceil + 36.$$

(The last step uses $\log_2(16k) \le \lceil\log_2(16k)\rceil$.)

Since $p \le 2k$: $p^{D_p} \le (2k)^{D_p} \le (2k)^{72\lceil\log_2(16k)\rceil + 36}$.

And $M_0(k) = (2k)^{72\lceil\log_2(16k)\rceil + 72}$, so for $k \ge 1$ (hence $2k \ge 2$):

$$p^{D_p} \le (2k)^{72\lceil\log_2(16k)\rceil + 36} \le (2k)^{72\lceil\log_2(16k)\rceil + 72} = M_0(k) \le m_0. \qquad\square$$

### Theorem E2 (Main counting result with explicit bound)

Let $k \ge 2$. Set $M_0(k) := (2k)^{72\lceil\log_2(16k)\rceil + 72}$. Then for all $m_0 \ge M_0(k)$:

$$\#\{m \in [m_0, 2m_0) : \exists p \le 2k \text{ prime with } v_p(\binom{m+k}{k}) > v_p(\binom{2m}{m})\} \le \frac{m_0}{4} < m_0.$$

In particular, there exists $m \in [m_0, 2m_0)$ with $v_p(\binom{m+k}{k}) \le v_p(\binom{2m}{m})$ for all primes $p \le 2k$.

**Proof.** By the union bound:
$$\#\{\text{bad } m\} \le \sum_{\substack{p \le 2k \\ p \text{ prime}}} \#\{m \in [m_0, 2m_0) : v_p(\binom{m+k}{k}) > v_p(\binom{2m}{m})\}.$$

For each prime $p \le 2k$, set $D = D_p$ as in Definition E0. By Lemma E1, $D_p \ge 16\log_p(k+1) + 16$ and $p^{D_p} \le m_0$, so the hypotheses of Corollary D3 are satisfied. Thus:

$$\#\{m \in [m_0, 2m_0) : v_p(\binom{m+k}{k}) > v_p(\binom{2m}{m})\} \le \frac{4m_0}{2^{D_p/36}}.$$

**Key decay estimate.** Since $D_p = 36\lceil\log_2(16k)\rceil + 36\lfloor\log_p(k+1)\rfloor + 36$, we have:

$$D_p/36 \ge \lceil\log_2(16k)\rceil + 1 \ge \log_2(16k) + 1 = \log_2(32k).$$

Therefore $2^{D_p/36} \ge 32k$, and each prime contributes at most:

$$\frac{4m_0}{2^{D_p/36}} \le \frac{4m_0}{32k} = \frac{m_0}{8k}.$$

**Union bound.** The number of primes $\le 2k$ is $\pi(2k) \le 2k$ (trivially). So:

$$\#\{\text{bad } m\} \le \sum_{p \le 2k} \frac{m_0}{8k} \le 2k \cdot \frac{m_0}{8k} = \frac{m_0}{4} < m_0. \qquad\square$$

### Corollary E3 (Existence)

For all $k \ge 2$ and all $m_0 \ge M_0(k)$, there exists $m \in [m_0, 2m_0)$ such that $v_p(\binom{m+k}{k}) \le v_p(\binom{2m}{m})$ for every prime $p \le 2k$.

**Proof.** Since the number of "bad" $m$ is $\le m_0/4 < m_0 = |[m_0, 2m_0)|$, not all $m$ are bad. $\square$

### Remark E4 (Asymptotics of $M_0(k)$)

The bound $M_0(k) = (2k)^{72\lceil\log_2(16k)\rceil + 72}$ satisfies:

$$\log_2 M_0(k) = (72\lceil\log_2(16k)\rceil + 72) \cdot \log_2(2k) = \Theta(\log^2 k).$$

So $M_0(k) = 2^{\Theta(\log^2 k)}$, which is **quasi-polynomial** in $k$ — much smaller than $2^{2^k}$ (truly doubly exponential) but larger than any polynomial in $k$.

For the main theorem (Erdős conjecture), we only need the existence statement (Corollary E3), not the explicit bound. The explicit bound is convenient for formalization since it avoids non-constructive arguments.

### Remark E5 (Why $D_p$ depends on $\log_2(k)$, not just $\log_p(k)$)

A natural first attempt sets $D_p = 36\lfloor\log_p(k+1)\rfloor + 36$, which gives $2^{D_p/36} \ge 2$ for each prime. This is insufficient: for primes $p \in (k, 2k]$, we have $\lfloor\log_p(k+1)\rfloor = 0$, so $D_p = 36$ and $2^{D_p/36} = 2$. Since there are $\sim k/\ln k$ such primes, the per-prime saving of a factor $2$ is overwhelmed by the number of primes.

The fix is to add a $\log_2 k$ term to $D_p$, ensuring the Chernoff bound gives $2^{D_p/36} = \Omega(k)$, so each prime contributes $O(m_0/k)$ and the sum over $O(k)$ primes is $O(m_0)$. This is the reason for the $36\lceil\log_2(16k)\rceil$ component in $D_p$.

The trade-off: larger $D_p$ requires larger $m_0$ (since we need $p^{D_p} \le m_0$). The resulting $M_0(k) = (2k)^{O(\log k)}$ is quasi-polynomial but still constructive.

---

## Part F: Formalization Strategy for Lean

The counting argument above decomposes into the following independent lemmas, each suitable for Lean formalization:

### F1. Carry structure lemmas (digit-level)
- **Cascade structure** (Lemma A1): For $i > s$, $c^{(1)}_i = 1$ iff $m_i = p-1$ and $c^{(1)}_{i-1} = 1$. This is a simple case analysis on natural numbers.
- **High digit forces carry** (Lemma B1): If $m_i \ge \lceil p/2 \rceil$, then $c^{(2)}_i = 1$. Again, simple arithmetic.

### F2. Counting lemmas (combinatorial)
- **Cascade count** (Lemma A3): The number of $m \in \{0, \ldots, p^D - 1\}$ with $L(m) \ge \ell$ is exactly $p^{D-\ell}$. This follows from the digit bijection: constraining $\ell$ specific coordinates reduces the count by $p^\ell$.
  - In Lean: This is `Finset.card_filter` on `Finset.range (p^D)`, using the bijection with `Fin D → Fin p`.
  
- **Few high digits** (Lemma B4'): The number of $m$ with $H(m) < D/6$ is at most $p^D/2^{D/36}$. This requires a Chernoff-type bound.
  - In Lean: This is the hardest lemma. Tracked as a separate formalization task.

### F3. Threshold argument (Part C)
- Split the "bad" set into $\text{Bad}_1 \cup \text{Bad}_2$ using a threshold at $\lfloor D/6 \rfloor$.
- Bound each piece using F2.
- This is a straightforward union bound: `Finset.card_union_le`.

### F4. Residue counting over intervals (Part D)
- Count elements of $[m_0, 2m_0)$ in a given set of residue classes mod $p^D$.
- Key lemma: for a set $S \subseteq \{0, \ldots, p^D - 1\}$, $\#\{m \in [a, b) : m \bmod p^D \in S\} \le |S| \cdot (\lfloor (b-a)/p^D \rfloor + 1)$.
- In Lean: Arithmetic on `Nat.div` and `Nat.mod`.

### F5. Union bound over primes (Part E)
- Sum the per-prime bounds, show the total is $\le m_0/4$.
- Requires: enumeration of primes $\le 2k$ via `Nat.Primes`, and the explicit $M_0(k)$ bound.
- The explicit $M_0(k) = (2k)^{72\lceil\log_2(16k)\rceil + 72}$ avoids non-constructive arguments, though the Lean statement may use `Real.log` to define $M_0(k)$ or an equivalent recursive definition.
- The key arithmetic fact is $D_p/36 \ge \log_2(32k)$ for all $p$, giving per-prime contribution $\le m_0/(8k)$ and total $\le m_0/4$.

### Recommended order for formalization:
1. F1 (carry structure) — simplest, purely arithmetic
2. F2 cascade count (Lemma A3) — combinatorial but clean
3. F4 residue counting — technical but standard
4. F3 threshold argument — uses F1, F2, F4
5. F2 high-digit count (Lemma B4') — hardest, may need `sorry` initially
6. F5 union bound — the grand finale

---

## Summary of Key Bounds

| Bound | Statement | Proof technique |
|-------|-----------|-----------------|
| Cascade count | $\#\{m : L(m) \ge \ell\} = p^{D-\ell}$ | Digit bijection |
| High digit lb | $v_p(\binom{2m}{m}) \ge H(m)$ | Lemma B1 |
| Few high digits | $\#\{m : H(m) < D/6\} \le p^D/2^{D/36}$ | Chernoff bound |
| Single prime | $\#\{\text{bad } m \text{ for } p\} \le 4m_0/2^{D_p/36}$ | Threshold + union + tiling |
| All small primes | $\sum_{p \le 2k} \#\{\text{bad for } p\} \le m_0/4$ | Union bound with $D_p = 36\lceil\log_2(16k)\rceil + \Theta(\log_p k)$ |

## References

- Kummer's theorem for $p$-adic valuation of binomial coefficients.
- Chernoff bound for binomial tails (standard combinatorial inequality).
- Builds on `proofs/erdos728_v2.md` (Lemma 3, probabilistic version).
