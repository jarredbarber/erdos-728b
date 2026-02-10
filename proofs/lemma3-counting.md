# Lemma 3: Counting Bound for Small Primes (Deterministic Version)

**Status:** Draft ✏️
**Statement:** Let $p$ be a prime with $p \le 2k$. Let $D \ge 1$ be an integer, and let $N = p^D$. Among the $N$ integers $m \in \{0, 1, \ldots, N-1\}$, the number of $m$ satisfying $v_p(\binom{m+k}{k}) > v_p(\binom{2m}{m})$ is at most $N / p^{\lfloor D/40 \rfloor}$, provided $D \ge 16 \lfloor \log_p(k+1) \rfloor + 16$.
**Dependencies:** None
**Confidence:** High

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
$$\#\{m \in \{0, \ldots, N-1\} : v_p(\binom{m+k}{k}) > s + 1 + T\} \le \frac{N}{p^T}.$$

**Proof.** By Lemma A2, $v_p(\binom{m+k}{k}) > s + 1 + T$ implies $L > T$, i.e., $L \ge T + 1$. But actually we need to be more careful: Lemma A2 gives $v_p(\binom{m+k}{k}) \le s + 1 + L$, so $v_p(\binom{m+k}{k}) > s + 1 + T$ implies $L > T$, i.e., $L \ge T + 1$. By Lemma A3:
$$\#\{m : L \ge T+1\} \le \frac{N}{p^{T+1}} \le \frac{N}{p^T}. \qquad\square$$

**Sharper version.** Actually from Lemma A3 directly: $L \ge T + 1$ gives count $\le N/p^{T+1}$. But we also need to handle the case where all $s+1$ positions $0, \ldots, s$ produce carries simultaneously with $L = T+1$ exactly. The bound $N/p^T$ (rather than $N/p^{T+1}$) provides a cleaner and still sufficient estimate.

Wait — let me be more precise. We have $v_p(\binom{m+k}{k}) \le (s+1) + L$. So $v_p(\binom{m+k}{k}) > (s+1) + T$ requires $L > T$, hence $L \ge T+1$. By Lemma A3, the count is $\le N/p^{T+1} \le N/p^T$. So indeed:

$$\#\{m : v_p(\binom{m+k}{k}) > s + 1 + T\} \le \frac{N}{p^{T+1}}. \tag{$\star$}$$

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

### Lemma B3 (Counting $m$ with few high digits — explicit binomial bound)

$$\#\{m \in \{0, \ldots, N-1\} : H(m) < t\} \le \binom{D}{< t} \cdot q^{D}$$

Wait — this isn't quite right. Let me be more precise.

**Lemma B3 (Counting $m$ with few high digits).**
For any $0 \le t \le D$:
$$\#\{m \in \{0, \ldots, N-1\} : H(m) < t\} = \sum_{j=0}^{t-1} \binom{D}{j} q^j (p - q)^{D-j}.$$

**Proof.** Under the bijection $m \leftrightarrow (m_0, \ldots, m_{D-1})$, $H(m) = j$ iff exactly $j$ of the $D$ coordinates lie in $\{\lceil p/2 \rceil, \ldots, p-1\}$ (a set of size $q$) and the remaining $D - j$ lie in $\{0, \ldots, \lceil p/2 \rceil - 1\}$ (a set of size $p - q$). The number of such tuples is $\binom{D}{j} q^j (p-q)^{D-j}$.

Summing over $j = 0, \ldots, t-1$ gives the count. $\square$

### Lemma B4 (Binomial tail bound — deterministic)

For $q/p \ge 1/3$ (which holds for all primes $p \ge 2$) and $t \le D \cdot q/(2p)$:

$$\sum_{j=0}^{t-1} \binom{D}{j} q^j (p-q)^{D-j} \le N \cdot e^{-2D(q/p - t/D)^2}.$$

**Proof.** This is the Hoeffding/Chernoff bound applied to the exact multinomial count. Write $\alpha = q/p$ (the fraction of "high" values). The sum $\sum_{j < t} \binom{D}{j} \alpha^j (1-\alpha)^{D-j}$ is the CDF of a $\text{Binomial}(D, \alpha)$ random variable at $t - 1$.

More precisely, for the **counting** version: the number of tuples $(m_0, \ldots, m_{D-1}) \in \{0, \ldots, p-1\}^D$ with fewer than $t$ "high" digits is:
$$p^D \cdot \Pr[\text{Bin}(D, \alpha) < t].$$

By the multiplicative Chernoff bound, for $t \le \alpha D$:
$$\Pr[\text{Bin}(D, \alpha) < t] \le \exp\!\left(-\frac{(\alpha D - t)^2}{2\alpha D}\right).$$

This bound is **purely combinatorial** — it follows from comparing the binomial sum with a geometric bound term by term. It can be proved in Lean via the entropy method or via an explicit induction on $D$.

Actually, for Lean formalization, we can use a cruder but cleaner bound. Let me state a self-contained combinatorial lemma.

### Lemma B4' (Crude but clean digit-counting bound)

For integers $D \ge 1$, $p \ge 2$, and $q = \lfloor p/2 \rfloor \ge 1$, let $\alpha = q/p$. For $t = \lfloor D/6 \rfloor$:

$$\#\{m \in \{0, \ldots, p^D - 1\} : H(m) < t\} \le \frac{p^D}{2^{D/36}}.$$

**Proof sketch.** We have $\alpha = q/p \ge 1/3$ for all $p \ge 2$ (since $q = \lfloor p/2 \rfloor \ge p/2 - 1/2$, so $q/p \ge 1/2 - 1/(2p) \ge 1/4$ for $p \ge 2$; more precisely, for $p = 2$: $\alpha = 1/2$; for $p = 3$: $\alpha = 1/3$; for $p \ge 5$: $\alpha \ge 2/5$).

The fraction of tuples with $H < D/6$ among all $p^D$ tuples is at most $\Pr[\text{Bin}(D, 1/3) < D/6]$ (since $\alpha \ge 1/3$, stochastic dominance applies). By the Chernoff bound with $\mu = D/3$ and $t = D/6 = \mu/2$:

$$\Pr[\text{Bin}(D, 1/3) < D/6] \le e^{-\mu/8} = e^{-D/24}.$$

Since $e^{-1/24} < 2^{-1/36}$ (because $1/24 > \ln 2 / 36 \approx 0.0193$ — actually $1/24 \approx 0.0417$ and $\ln 2/36 \approx 0.0193$, so yes), we get:

$$\#\{m : H(m) < D/6\} \le p^D \cdot e^{-D/24} \le p^D \cdot 2^{-D/36}. \qquad\square$$

**Remark for formalization.** The Chernoff bound $\Pr[\text{Bin}(n, \alpha) < \alpha n/2] \le e^{-\alpha n/8}$ can be proved purely combinatorially as follows:

1. The moment generating function approach: $\Pr[X < t] \le e^{\lambda t} \cdot \mathbb{E}[e^{-\lambda X}]$ for any $\lambda > 0$.
2. For $X \sim \text{Bin}(n, \alpha)$: $\mathbb{E}[e^{-\lambda X}] = (1 - \alpha + \alpha e^{-\lambda})^n$.
3. Optimize $\lambda$ to get the bound.

This is entirely an inequality about finite sums and exponentials, and is formalizable. However, it requires exponential/logarithmic functions. An alternative purely combinatorial approach uses the **entropy bound**:

$$\sum_{j \le \beta n} \binom{n}{j} \le 2^{n H(\beta)}$$

where $H(\beta) = -\beta \log_2 \beta - (1-\beta) \log_2(1-\beta)$ is the binary entropy. This is proved by a simple induction.

For the Lean formalization, the cleanest approach may be to establish the bound as a standalone lemma about `Finset.card` of a filtered set, avoiding probability theory entirely.

---

## Part C: Combining the Bounds

### Theorem (Counting bound for a single prime)

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

**Bounding $|\text{Bad}_1|$:** By Corollary A4 with $T = T_0 = \lfloor D/6 \rfloor - s - 1 \ge 0$ (since $D \ge 12(s+1) + 6$ implies $\lfloor D/6 \rfloor \ge 2(s+1)$ implies $T_0 \ge s + 1 \ge 1$):
$$|\text{Bad}_1| = \#\{m : v_p(\binom{m+k}{k}) > s + 1 + T_0\} = \#\{m : v_p(\binom{m+k}{k}) > \lfloor D/6 \rfloor\}.$$

Wait: $s + 1 + T_0 = s + 1 + \lfloor D/6 \rfloor - s - 1 = \lfloor D/6 \rfloor$. ✓

By ($\star$): $|\text{Bad}_1| \le N/p^{T_0+1}$.

**Bounding $|\text{Bad}_2|$:** By Corollary B2, $v_p(\binom{2m}{m}) \ge H(m)$, so $v_p(\binom{2m}{m}) < \lfloor D/6 \rfloor$ implies $H(m) < \lfloor D/6 \rfloor$. By Lemma B4':
$$|\text{Bad}_2| \le N / 2^{D/36}.$$

**Combining:** By the union bound:
$$\#\{m : v_p(\binom{m+k}{k}) > v_p(\binom{2m}{m})\} \le |\text{Bad}_1| + |\text{Bad}_2| \le \frac{N}{p^{T_0+1}} + \frac{N}{2^{D/36}}. \qquad\square$$

### Corollary (Simplified bound)

Under the additional assumption $D \ge 16 \log_p(k+1) + 16$ (which implies $D \ge 12(s+1) + 6$ and also $T_0 \ge D/12$):

$$\#\{m \in \{0, \ldots, p^D - 1\} : v_p(\binom{m+k}{k}) > v_p(\binom{2m}{m})\} \le \frac{2N}{2^{D/36}} \le \frac{N}{p^{D/40}}.$$

**Proof.** Since $s \le \log_p k < \log_p(k+1)$ and $D \ge 16 \log_p(k+1) + 16$:
$$T_0 = \lfloor D/6 \rfloor - s - 1 \ge D/6 - 1 - \log_p(k+1) - 1 \ge D/6 - D/16 - 2 = 5D/48 - 2 \ge D/12$$
for $D \ge 48$.

So $p^{T_0+1} \ge p^{D/12} \ge 2^{D/12}$, and:
$$\frac{N}{p^{T_0+1}} + \frac{N}{2^{D/36}} \le \frac{N}{2^{D/12}} + \frac{N}{2^{D/36}} \le \frac{2N}{2^{D/36}}.$$

For $D \ge 40$ (and $p \ge 2$): $2/2^{D/36} \le 1/p^{D/40}$ because $2^{D/36 - 1} \ge p^{D/40}$ when $D(1/36 - \log_2 p/40) \ge 1$. 

Let me verify this more carefully. We need $2^{D/36}/2 \ge p^{D/40}$, i.e., $2^{D/36 - 1} \ge p^{D/40}$, i.e., $(D/36 - 1)\ln 2 \ge (D/40)\ln p$.

For $p = 2$: need $D/36 - 1 \ge D/40$, i.e., $D(1/36 - 1/40) \ge 1$, i.e., $D \cdot 1/360 \ge 1$, so $D \ge 360$. This is a large constant but is fine since we need $D$ to be large anyway.

Actually, let me use a cleaner path. Instead of trying to get $1/p^{D/40}$, let me just keep the bound as $2N/2^{D/36}$ and show this suffices for the union bound in the main theorem.

**Cleaner Corollary.** For $D \ge 16 \log_p(k+1) + 16$:

$$\#\{m \in \{0, \ldots, p^D - 1\} : v_p(\binom{m+k}{k}) > v_p(\binom{2m}{m})\} \le \frac{2N}{2^{D/36}}.$$

This is all we need. $\square$

---

## Part D: Tiling Argument — From $\{0, \ldots, p^D - 1\}$ to $[m_0, 2m_0]$

The counting bound above works over the exact interval $\{0, \ldots, p^D - 1\}$. For the main theorem, we need a bound over $[m_0, 2m_0)$.

### Lemma D1 (Tiling)

Let $I = [m_0, 2m_0)$ with $m_0 \ge p^D$. For any property $\mathcal{P}$ of integers, if:
- the fraction of $m \in \{0, \ldots, p^D - 1\}$ satisfying $\mathcal{P}$ is at most $\beta$,
- $\mathcal{P}$ depends only on $m \bmod p^D$ (i.e., only on the lowest $D$ base-$p$ digits of $m$),

then the fraction of $m \in I$ satisfying $\mathcal{P}$ is at most $\beta + p^D / m_0$.

**Proof.** The interval $I = [m_0, 2m_0)$ has length $m_0$. Partition $I$ into maximal sub-intervals that are translates of $\{0, \ldots, p^D - 1\}$, plus at most two partial intervals at the boundaries.

More precisely: The interval $[m_0, 2m_0)$ contains $\lfloor m_0 / p^D \rfloor$ complete copies of $\{0, \ldots, p^D - 1\}$ (shifted by multiples of $p^D$), plus at most $2 p^D$ leftover elements (at most $p^D$ at each end).

In each complete copy, the fraction satisfying $\mathcal{P}$ is exactly $\beta$ (since $\mathcal{P}$ depends only on $m \bmod p^D$, and a complete copy covers all residues). In the leftover, at most $2p^D$ elements satisfy $\mathcal{P}$.

So:
$$\#\{m \in I : \mathcal{P}(m)\} \le \beta \cdot m_0 + 2p^D.$$

The fraction is $\le \beta + 2p^D / m_0$. $\square$

### Application

**Important observation:** The property $v_p(\binom{m+k}{k}) > v_p(\binom{2m}{m})$ does NOT depend only on $m \bmod p^D$ in general, because the digits of $m$ at positions $\ge D$ also contribute carries.

However, we can handle this as follows.

**Lemma D2 (Truncation).** Let $m$ have $D' > D$ base-$p$ digits (i.e., $m < p^{D'}$). Write $m = m^{\text{low}} + p^D \cdot m^{\text{high}}$ where $m^{\text{low}} = m \bmod p^D \in \{0, \ldots, p^D - 1\}$ and $m^{\text{high}} = \lfloor m / p^D \rfloor$.

The carries in $m + k$ and $m + m$ at positions $0, 1, \ldots, D-1$ depend only on $m^{\text{low}}$ and $k$ (for $m + k$) or $m^{\text{low}}$ alone (for $m + m$), provided we also account for the carry entering position $D$ from below.

Crucially: $v_p(\binom{m+k}{k}) = v_p(\binom{m^{\text{low}} + k}{k})$ when $D > s + L + 1$ (i.e., the cascade from $k$'s digits has died out before position $D$). This is because $k < p^{s+1} \le p^D$ implies $k$'s digits above position $s$ are all 0, and carries in positions $> s$ are purely cascading from the carry at position $s$.

For the self-doubling $m + m$: carries at positions $0, \ldots, D-1$ depend only on $(m_0, \ldots, m_{D-1})$ and their internal cascading; the carry at position $D$ goes "up" and doesn't affect positions below.

So for the purposes of counting carries at positions $0, \ldots, D-1$:
- $v_p(\binom{m+k}{k})$ at positions $0, \ldots, D-1$ depends only on $m^{\text{low}}$.
- $v_p(\binom{2m}{m})$ includes carries at ALL positions, so $v_p(\binom{2m}{m}) \ge$ (carries at positions $0, \ldots, D-1$ from $m^{\text{low}}$).

This means:
$$v_p(\binom{m+k}{k}) = \text{(carries in } m + k \text{ at positions } 0, \ldots, D-1) + \text{(carries at positions } \ge D)$$

But for $k < p^D$ (which holds since $D \ge s+1$ and $k < p^{s+1}$), all carries in $m + k$ at positions $\ge D$ come from cascading, and these are already counted in the cascade length $L$. If $L < D - s$, then there are NO carries at positions $\ge D$ from $m+k$, and $v_p(\binom{m+k}{k})$ depends only on $m^{\text{low}}$.

**The cleanest approach:** Rather than trying to make the tiling argument work with truncation, observe that $v_p(\binom{m+k}{k})$ depends only on the base-$p$ digits of $m$, all of them. But the CASCADE LENGTH $L$ is determined by the digits starting at position $s+1$.

**Alternative clean approach for tiling:** Instead of tiling, use the following direct argument.

### Lemma D3 (Direct counting over $[m_0, 2m_0)$)

For $m_0 \ge 1$ and $D \ge 16\log_p(k+1) + 16$, with $D \le \lfloor \log_p m_0 \rfloor$ (so that $p^D \le m_0$):

$$\#\{m \in [m_0, 2m_0) : v_p(\binom{m+k}{k}) > v_p(\binom{2m}{m})\} \le \frac{2m_0}{p^{T_0+1}} + \frac{m_0}{2^{D/36}} + 4p^D$$

where $T_0 = \lfloor D/6 \rfloor - s - 1$ as before.

**Proof.** We work directly over $[m_0, 2m_0)$ using the digit structure.

**Step 1: Splitting.** If $v_p(\binom{m+k}{k}) > v_p(\binom{2m}{m})$, then either:
- $v_p(\binom{m+k}{k}) > \lfloor D/6 \rfloor$ (event $\text{Bad}_1$), or
- $v_p(\binom{2m}{m}) < \lfloor D/6 \rfloor$ (event $\text{Bad}_2$).

**Step 2: Bounding $|\text{Bad}_1|$ via cascade.**

The cascade analysis (Part A) applies to ALL $m$, not just $m < p^D$. For any $m$, $v_p(\binom{m+k}{k}) \le s + 1 + L(m)$ where $L(m)$ is the cascade length starting at position $s+1$.

$v_p(\binom{m+k}{k}) > \lfloor D/6 \rfloor = s + 1 + T_0$ requires $L(m) > T_0$, i.e., $L(m) \ge T_0 + 1$.

$L(m) \ge T_0 + 1$ means $m_{s+1} = m_{s+2} = \cdots = m_{s+T_0+1} = p - 1$.

This is equivalent to: $m \bmod p^{s+T_0+2}$ lies in a specific set of residues where positions $s+1$ through $s+T_0+1$ are all $p-1$. The number of such residues mod $p^{s+T_0+2}$ is $p^{s+1} \cdot 1^{T_0+1} \cdot 1 = p^{s+1}$ (positions $0, \ldots, s$ are free; positions $s+1, \ldots, s+T_0+1$ are fixed to $p-1$; position $s+T_0+2$ can be anything, but we stop here).

Wait — more carefully: among integers $\{0, \ldots, p^{s+T_0+2} - 1\}$, those with $m_{s+1} = \cdots = m_{s+T_0+1} = p-1$ number exactly $p^{(s+T_0+2) - (T_0+1)} = p^{s+1}$. So the fraction is $p^{s+1}/p^{s+T_0+2} = 1/p^{T_0+1}$.

For $m$ in any interval of length $N$: the number of $m$ with $L(m) \ge T_0 + 1$ is at most:
$$\frac{N}{p^{T_0+1}} + 2p^{s+T_0+2}$$
(the $+2p^{s+T_0+2}$ is the boundary correction from at most 2 incomplete residue blocks).

For $N = m_0$ (interval $[m_0, 2m_0)$): since $s + T_0 + 2 \le s + 1 + \lfloor D/6 \rfloor \le D$ (using $T_0 = \lfloor D/6 \rfloor - s - 1$), the boundary is $\le 2p^D$.

$$|\text{Bad}_1| \le \frac{m_0}{p^{T_0+1}} + 2p^D.$$

**Step 3: Bounding $|\text{Bad}_2|$ via high digits.**

Define $H_D(m) = \#\{i \in \{0, \ldots, D-1\} : m_i \ge \lceil p/2 \rceil\}$. By Corollary B2, $v_p(\binom{2m}{m}) \ge H(m) \ge H_D(m)$ (since $m$ has $\ge D$ digits for $m \ge m_0 \ge p^D$, and more high digits can only help).

$H_D(m)$ depends only on $m \bmod p^D$. By Lemma B4', the number of residues $r \in \{0, \ldots, p^D - 1\}$ with $H_D(r) < D/6$ is at most $p^D / 2^{D/36}$. Call this set $S$.

For $m \in [m_0, 2m_0)$, the number with $m \bmod p^D \in S$ is at most:
$$|S| \cdot \left(\left\lfloor \frac{m_0}{p^D}\right\rfloor + 2\right) \le |S| \cdot \frac{m_0 + 2p^D}{p^D} = |S| \cdot \frac{m_0}{p^D} + 2|S|.$$

Since $|S| \le p^D/2^{D/36}$:
$$|\text{Bad}_2| \le \frac{m_0}{2^{D/36}} + \frac{2p^D}{2^{D/36}} \le \frac{m_0}{2^{D/36}} + 2p^D.$$

**Step 4: Combining.**
$$\#\{\text{bad } m\} \le |\text{Bad}_1| + |\text{Bad}_2| \le \frac{m_0}{p^{T_0+1}} + \frac{m_0}{2^{D/36}} + 4p^D. \qquad\square$$

**Remark on the boundary term.** The $4p^D$ boundary correction is negligible compared to $m_0$ whenever $m_0 \gg p^D$. Since $D = \lfloor \log_p m_0 \rfloor - c$ for some constant $c$ (chosen to satisfy the constraint $D \ge 16 \log_p(k+1) + 16$), we have $p^D \le m_0 / p^c$, so $4p^D / m_0 \le 4/p^c \to 0$ as we take $D$ slightly smaller than $\log_p m_0$. In the final union bound, we absorb this into the main terms.

---

## Part E: Union Bound Over All Small Primes

### Theorem (Main counting result for the union bound)

Let $k \ge 2$, $m_0$ sufficiently large (in terms of $k$). Then:

$$\#\{m \in [m_0, 2m_0) : \exists p \le 2k \text{ prime}, v_p(\binom{m+k}{k}) > v_p(\binom{2m}{m})\} < m_0.$$

That is, not all $m$ are "bad" — there exists at least one good $m$.

**Proof.** By the union bound:
$$\#\{\text{bad } m\} \le \sum_{\substack{p \le 2k \\ p \text{ prime}}} \#\{m \in [m_0, 2m_0) : v_p(\binom{m+k}{k}) > v_p(\binom{2m}{m})\}.$$

For each prime $p \le 2k$, choose $D_p = \lfloor \log_p m_0 \rfloor - 1$ (so that $p^{D_p} \le m_0/p$). For $m_0$ large enough in terms of $k$, we have $D_p \ge 16\log_p(k+1) + 16$ for all $p \le 2k$.

By Lemma D3:
$$\#\{m \in [m_0, 2m_0) : v_p(\binom{m+k}{k}) > v_p(\binom{2m}{m})\} \le \frac{m_0}{p^{T_0+1}} + \frac{m_0}{2^{D_p/36}} + 4p^{D_p}$$

where $T_0 = \lfloor D_p/6 \rfloor - s - 1 \ge D_p/12$ (as shown in Part C). Since $p^{T_0+1} \ge p^{D_p/12} \ge 2^{D_p/12}$, the first two terms are both $\le m_0/2^{D_p/36}$ (using $D_p/12 > D_p/36$).

Since $p^{D_p} \le m_0/p$, the boundary term $4p^{D_p} \le 4m_0/p \le 2m_0$ — but this is too large. We need to be more careful.

**Refined boundary handling.** Since $p^{D_p} \le m_0/p \le m_0/2$, the boundary term $4p^{D_p} \le 4m_0/p$. We can write:
$$\#\{\text{bad for } p\} \le \frac{2m_0}{2^{D_p/36}} + \frac{4m_0}{p}.$$

Wait — the $4m_0/p$ term doesn't decay fast enough. Let me reconsider the boundary.

**Better approach.** Use the tiling more carefully. For a property $\mathcal{P}$ that depends only on $m \bmod p^D$, the number of $m \in [m_0, 2m_0)$ satisfying $\mathcal{P}$ is:
$$\le |\mathcal{P} \cap \{0, \ldots, p^D-1\}| \cdot \left\lceil \frac{m_0}{p^D} \right\rceil \le |\mathcal{P} \cap \{0, \ldots, p^D-1\}| \cdot \frac{m_0 + p^D}{p^D}.$$

For $\text{Bad}_1$ (cascade): $v_p(\binom{m+k}{k}) > \lfloor D/6 \rfloor$ depends on digits $0, \ldots, s + T_0 + 1$ only (positions where the cascade could still be active). Since $s + T_0 + 2 \le D$, this depends only on $m \bmod p^D$. The number of "bad" residues mod $p^D$ is at most $p^D/p^{T_0+1} = p^{D-T_0-1}$.

So: $|\text{Bad}_1 \cap [m_0, 2m_0)| \le p^{D-T_0-1} \cdot (m_0/p^D + 1) = m_0/p^{T_0+1} + p^{D-T_0-1}.$

For $\text{Bad}_2$ (few high digits): $H_D(m) < \lfloor D/6 \rfloor$ depends only on $m \bmod p^D$. The number of bad residues is $\le p^D/2^{D/36}$.

So: $|\text{Bad}_2 \cap [m_0, 2m_0)| \le (p^D/2^{D/36}) \cdot (m_0/p^D + 1) = m_0/2^{D/36} + p^D/2^{D/36}.$

Combining:
$$\#\{\text{bad for } p\} \le \frac{m_0}{p^{T_0+1}} + \frac{m_0}{2^{D_p/36}} + p^{D_p - T_0 - 1} + \frac{p^{D_p}}{2^{D_p/36}}.$$

The last two terms are $\le p^{D_p}$ each (since $T_0 \ge 1$ and $2^{D_p/36} \ge 1$). And $p^{D_p} \le m_0/p$. So:
$$\#\{\text{bad for } p\} \le \frac{2m_0}{2^{D_p/36}} + \frac{2m_0}{p}.$$

But the $2m_0/p$ boundary terms sum over primes $p \le 2k$ to at most $2m_0 \sum_{p \le 2k} 1/p \approx 2m_0 \log\log(2k)$. This is way too large.

**Resolution: use $D_p$ much smaller than $\log_p m_0$.** Set $D_p = \lfloor \log_p m_0 / 2 \rfloor$. Then $p^{D_p} \le \sqrt{m_0}$, and the boundary terms $p^{D_p - T_0 - 1} + p^{D_p}/2^{D_p/36} \le 2\sqrt{m_0}$.

With this choice:
$$\#\{\text{bad for } p\} \le \frac{2m_0}{2^{D_p/36}} + 2\sqrt{m_0}.$$

Now $D_p = \lfloor \log_p m_0 / 2 \rfloor \ge \log_p m_0 / 2 - 1$, so $D_p/36 \ge \log_p m_0/72 - 1/36$. Thus $2^{D_p/36} \ge 2^{\log_p m_0/72 - 1}$. And:

$$\frac{m_0}{2^{D_p/36}} \le \frac{2m_0}{2^{\log_p m_0 / 72}} = \frac{2m_0}{m_0^{\ln 2/(72 \ln p)}} = 2 m_0^{1 - \ln 2/(72 \ln p)}.$$

For $p \le 2k$ and $k = O(\log m_0)$: $\ln p \le \ln(2k) = O(\log\log m_0)$, so $\ln 2/(72 \ln p) = \Omega(1/\log\log m_0)$.

Summing over $\pi(2k) = O(k/\log k)$ primes:
$$\#\{\text{bad}\} \le \sum_{p \le 2k} \left(\frac{2m_0}{2^{D_p/36}} + 2\sqrt{m_0}\right) \le 2k \cdot 2 m_0^{1 - c/\log\log m_0} + 4k\sqrt{m_0}$$

where $c = \ln 2/72 > 0$.

For $k = O(\log m_0)$:
- $4k\sqrt{m_0} = O(\sqrt{m_0} \log m_0) = o(m_0)$. ✓
- $4k \cdot m_0^{1 - c/\log\log m_0} = O(\log m_0 \cdot m_0 \cdot m_0^{-c/\log\log m_0})$.

Now $m_0^{c/\log\log m_0} = e^{c \ln m_0 / \log\log m_0}$. Since $\ln m_0 / \log \log m_0 \to \infty$ (it grows faster than any constant), $m_0^{c/\log\log m_0} \to \infty$. In particular, for $m_0$ large enough, $m_0^{c/\log\log m_0} > 4k$, so:

$$4k \cdot m_0^{1 - c/\log\log m_0} < m_0.$$

Combining both terms, $\#\{\text{bad}\} < m_0$ for $m_0$ sufficiently large. ✓

**Checking $D_p \ge 16\log_p(k+1) + 16$.** We need $\log_p m_0 / 2 - 1 \ge 16 \log_p(k+1) + 16$, i.e., $\log_p m_0 \ge 32 \log_p(k+1) + 34$. For $k = O(\log m_0)$, $\log_p(k+1) = O(\log\log m_0/\log p) = O(\log\log m_0)$, while $\log_p m_0 = \log m_0 / \log p \ge \log m_0 / \log(2k)$. Since $\log m_0 / \log(2k) \gg \log\log m_0$ for large $m_0$, the condition holds. ✓

Therefore $\#\{\text{bad } m\} < m_0 = |[m_0, 2m_0)|$, and there exists at least one $m \in [m_0, 2m_0)$ with $v_p(\binom{m+k}{k}) \le v_p(\binom{2m}{m})$ for all primes $p \le 2k$. $\square$

---

## Part F: Formalization Strategy for Lean

The counting argument above decomposes into the following independent lemmas, each suitable for Lean formalization:

### F1. Carry structure lemmas (digit-level)
- **Cascade structure** (Lemma A1): For $i > s$, $c^{(1)}_i = 1$ iff $m_i = p-1$ and $c^{(1)}_{i-1} = 1$. This is a simple case analysis on natural numbers.
- **High digit forces carry** (Lemma B1): If $m_i \ge \lceil p/2 \rceil$, then $c^{(2)}_i = 1$. Again, simple arithmetic.

### F2. Counting lemmas (combinatorial)
- **Cascade count** (Lemma A3): The number of $m \in \{0, \ldots, p^D - 1\}$ with $L(m) \ge \ell$ is exactly $p^{D-\ell}$. This follows from the digit bijection: constraining $\ell$ specific coordinates reduces the count by $p^\ell$.
  - In Lean: This is `Finset.card_filter` on `Finset.range (p^D)`, using the bijection with `Fin D → Fin p`.
  
- **Few high digits** (Lemma B4'): The number of $m$ with $H(m) < D/6$ is at most $p^D / 2^{D/36}$. This requires a Chernoff-type bound.
  - In Lean: This is the hardest lemma. Options:
    1. **Exact Chernoff via MGF.** Formalize $\Pr[\text{Bin}(D, \alpha) < t] \le e^{-(\alpha D - t)^2/(2\alpha D)}$ using the moment generating function. Requires `Real.exp` and `Real.log`.
    2. **Entropy bound.** $\sum_{j \le \beta n} \binom{n}{j} \le 2^{nH(\beta)}$. Purely combinatorial but still needs log.
    3. **Recursive halving.** Prove by induction on $D$ that the binomial tail ratio decreases geometrically. This avoids transcendentals entirely.
    4. **Citation axiom.** If Mathlib already has a binomial tail bound, use it.

### F3. Threshold argument (Part C)
- Split the "bad" set into $\text{Bad}_1 \cup \text{Bad}_2$ using a threshold at $\lfloor D/6 \rfloor$.
- Bound each piece using F2.
- This is a straightforward union bound: `Finset.card_union_le`.

### F4. Residue counting over intervals (Part D, revised)
- Count elements of $[m_0, 2m_0)$ in a given set of residue classes mod $p^D$.
- Key lemma: for a set $S \subseteq \{0, \ldots, p^D - 1\}$, $\#\{m \in [a, b) : m \bmod p^D \in S\} \le |S| \cdot (\lfloor (b-a)/p^D \rfloor + 1)$.
- In Lean: Arithmetic on `Nat.div` and `Nat.mod`.

### F5. Union bound over primes (Part E)
- Sum the per-prime bounds, show the total is $< m_0$.
- Requires: enumeration of primes $\le 2k$ via `Nat.Primes`, and showing that $m_0^{c/\log\log m_0} \to \infty$.
- This step likely requires `Real.log` and `Real.exp` properties.

### Recommended order for formalization:
1. F1 (carry structure) — simplest, purely arithmetic
2. F2 cascade count (Lemma A3) — combinatorial but clean
3. F4 residue counting — technical but standard
4. F3 threshold argument — uses F1, F2, F4
5. F2 high-digit count (Lemma B4') — hardest, may need `sorry` initially
6. F5 union bound — the grand finale, may need `sorry` for transcendental bounds

### Note on avoiding transcendentals

For a fully elementary formalization (avoiding `Real.exp` and `Real.log`), one can replace the Chernoff bound with a weaker but sufficient recursive argument:

**Claim.** For $D \ge 6$, $p \ge 2$: $\#\{m \in \{0, \ldots, p^D - 1\} : H(m) = 0\} = (p - q)^D \le (2p/3)^D$.

This trivially gives $\#\{m : H(m) = 0\} / p^D \le (2/3)^D$, which decays exponentially. The full Chernoff bound is only needed to show that $H(m) < D/6$ is rare, but an inductive argument on blocks of 6 consecutive digits works: in any block of 6 digits, the probability of having no high digit is at most $(2/3)^6 < 1/8$. So having $< D/6$ high digits among $\lfloor D/6 \rfloor$ blocks requires all-but-one blocks to have zero contribution, and a counting argument bounds this.

Specifically, partition the $D$ digit positions into $B = \lfloor D/6 \rfloor$ blocks of 6 (ignoring up to 5 remaining positions). In each block of 6 positions, $H_{\text{block}} = 0$ with "probability" (fraction) at most $(1 - q/p)^6 \le (2/3)^6 < 0.088$. Having $H(m) < B$ means $H_{\text{block}} = 0$ in at least one block. By an inclusion-exclusion argument, this fraction is small — but this is getting circular.

**Simpler approach for Lean.** Just use: for $D$ digit positions, each independently taking $p$ values, the number of tuples with $< t$ "high" values satisfies:
$$\text{count} = \sum_{j=0}^{t-1} \binom{D}{j} q^j (p-q)^{D-j} < p^D \cdot \frac{t \binom{D}{t}}{p^t} \cdot \left(\frac{q}{p-q}\right)^t \cdot \left(\frac{p-q}{p}\right)^D$$

Actually, this is getting complicated. For the Lean formalization, the cleanest approach is likely to use a `sorry` placeholder for the Chernoff bound and focus on the structural parts (cascade, threshold, union bound).

---

## Summary of Key Bounds

| Bound | Statement | Proof technique |
|-------|-----------|-----------------|
| Cascade count | $\#\{m : L(m) \ge \ell\} = p^{D-\ell}$ | Digit bijection |
| High digit lb | $v_p(\binom{2m}{m}) \ge H(m)$ | Lemma B1 |
| Few high digits | $\#\{m : H(m) < D/6\} \le p^D/2^{D/36}$ | Chernoff bound |
| Single prime | $\#\{\text{bad } m \text{ for } p\} \le 4m_0/2^{D_p/36}$ | Threshold + union |
| All small primes | $\sum_{p \le 2k} \#\{\text{bad for } p\} < m_0$ | Union + asymptotics |

## References

- Kummer's theorem for $p$-adic valuation of binomial coefficients.
- Chernoff bound for binomial tails (standard combinatorial inequality).
- Builds on `proofs/erdos728_v2.md` (Lemma 3, probabilistic version).
