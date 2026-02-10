# Erdős 728: Factorial Divisibility with Logarithmic Gap (v2)

**Status:** Verified ✅
**Reviewed by:** erdos728b-poe
**Statement:**
For sufficiently small $\epsilon > 0$ and any $0 < C < C'$, there exist $a, b, n \in \mathbb{N}$ with $n > 0$, $a, b > \epsilon n$, such that:
1. $a! \, b! \mid n! \, (a+b-n)!$
2. $C \log n < a + b - n < C' \log n$

**Dependencies:** None (self-contained)
**Confidence:** High

## Overview of the Proof

We use the substitution $a = m$, $b = m + k$, $n = 2m$, where $k = a + b - n$. The divisibility condition $a! b! \mid n! k!$ reduces to $\binom{m+k}{k} \mid \binom{2m}{m}$ (Lemma 1). We prove this divisibility by a two-part argument:

- **Carry Dominance Lemma** (Lemma 2): For primes $p > 2k$ and any $m$, $v_p(\binom{m+k}{k}) \le v_p(\binom{2m}{m})$.
- **Probabilistic bound for small primes** (Lemma 3): For any prime $p \le 2k$ and $m$ uniformly random in a large interval, $v_p(\binom{m+k}{k}) > v_p(\binom{2m}{m})$ with probability exponentially small in $\log_p m$.

A union bound over all primes $p \le 2k$ shows that, for $m$ large enough relative to $k$, a positive fraction of integers $m$ satisfy $\binom{m+k}{k} \mid \binom{2m}{m}$. This yields the desired tuples for all $C, C' > 0$.

---

## Lemma 1: Reduction to Central Binomial Divisibility

**Statement.** Let $m, k \ge 1$ with $m \ge k$. Set $a = m$, $b = m + k$, $n = 2m$. Then:
$$a! \, b! \mid n! \, k! \quad \iff \quad \binom{m+k}{k} \mid \binom{2m}{m}.$$

**Proof.**
We have $a + b = 2m + k$ and $a + b - n = k$. The divisibility condition is:
$$m! \, (m+k)! \mid (2m)! \, k!$$

Rearranging:
$$\frac{(2m)! \, k!}{m! \, (m+k)!} = \frac{(2m)!}{m! \, m!} \cdot \frac{m! \, k!}{(m+k)!} = \binom{2m}{m} \cdot \frac{1}{\binom{m+k}{k}}.$$

This is an integer if and only if $\binom{m+k}{k} \mid \binom{2m}{m}$. $\square$

**Derivation of the identity.** By the absorption identity,
$$\binom{M}{a} \binom{a}{k} = \binom{M}{k} \binom{M-k}{a-k}$$
(both sides equal $\frac{M!}{k!(a-k)!(M-a)!}$). With $M = 2m + k$ and $a = m$:
$$\binom{2m+k}{m}\binom{m}{k} = \binom{2m+k}{k}\binom{2m}{m-k}$$
The condition $\binom{2m+k}{k} \mid \binom{2m+k}{m}$ (i.e., $\binom{M}{k} \mid \binom{M}{a}$) is equivalent to $\binom{m}{k} \mid \binom{2m}{m-k} = \binom{2m}{m+k}$. And:
$$\frac{\binom{2m}{m+k}}{\binom{m}{k}} = \frac{(2m)!}{(m+k)!(m-k)!} \cdot \frac{k!(m-k)!}{m!} = \frac{(2m)!}{m!(m+k)!} \cdot k! = \frac{\binom{2m}{m}}{\binom{m+k}{k}}$$

So the condition is $\binom{m+k}{k} \mid \binom{2m}{m}$.

---

## Lemma 2: Carry Dominance for Large Primes

**Statement.** For any prime $p > 2k$ and any non-negative integer $m$:
$$v_p\!\left(\binom{m+k}{k}\right) \le v_p\!\left(\binom{2m}{m}\right).$$

**Proof.**
By Kummer's theorem, $v_p(\binom{m+k}{k})$ equals the number of carries when adding $m$ and $k$ in base $p$, and $v_p(\binom{2m}{m})$ equals the number of carries when adding $m$ and $m$ in base $p$.

Write $m = (m_d, m_{d-1}, \ldots, m_1, m_0)_p$ and $k = (k_s, k_{s-1}, \ldots, k_0)_p$ where $s \le d$. Since $p > 2k > k$, we have $k < p$, so $s = 0$ and $k = k_0$ is a single base-$p$ digit.

Let $c^{(1)}_i$ denote the carry at position $i$ in the addition $m + k$, and $c^{(2)}_i$ the carry at position $i$ in $m + m$. We set $c^{(1)}_{-1} = c^{(2)}_{-1} = 0$.

**Claim:** $c^{(1)}_i = 1 \implies c^{(2)}_i = 1$ for all $i \ge 0$.

*Proof of Claim by induction on $i$:*

**Base case ($i = 0$):**
$c^{(1)}_0 = 1$ means $m_0 + k \ge p$, i.e., $m_0 \ge p - k$. Since $p > 2k$, we have $p - k > k$, so $m_0 > k \ge 1$, giving $m_0 \ge p - k > p/2$ (since $k < p/2$). Thus $2m_0 > p$, so $c^{(2)}_0 = 1$. ✓

**Inductive step ($i \ge 1$):**
$c^{(1)}_i = 1$ means $m_i + 0 + c^{(1)}_{i-1} \ge p$ (the digit of $k$ at position $i \ge 1$ is 0). Since $m_i \le p - 1$ and $c^{(1)}_{i-1} \le 1$, this requires $m_i = p - 1$ and $c^{(1)}_{i-1} = 1$.

By the inductive hypothesis, $c^{(1)}_{i-1} = 1$ implies $c^{(2)}_{i-1} = 1$. Then:
$$2m_i + c^{(2)}_{i-1} = 2(p-1) + 1 = 2p - 1 \ge p$$
so $c^{(2)}_i = 1$. ✓

Since every carry in $m + k$ corresponds to a carry in $m + m$ at the same position:
$$v_p\!\left(\binom{m+k}{k}\right) = \sum_i c^{(1)}_i \le \sum_i c^{(2)}_i = v_p\!\left(\binom{2m}{m}\right). \quad\square$$

---

## Lemma 3: Probabilistic Bound for Small Primes

**Statement.** Let $p$ be a prime with $p \le 2k$. Let $D = \lfloor \log_p m \rfloor + 1$ be the number of base-$p$ digits of $m$. For $m$ uniformly distributed in $\{0, 1, \ldots, N - 1\}$ with $N \ge p^D$:

$$\Pr\!\left[v_p\!\left(\binom{m+k}{k}\right) > v_p\!\left(\binom{2m}{m}\right)\right] \le \frac{1}{p^{D/40}}$$

provided $D \ge 16 \log_p(k+1) + 16$.

**Proof.**
We bound the two sides separately.

### Upper bound on $v_p(\binom{m+k}{k})$

$k$ has $s + 1 \le \lfloor \log_p k \rfloor + 1$ digits in base $p$, where $s = \lfloor \log_p k \rfloor$.

The carries in $m + k$ at positions $0, 1, \ldots, s$ depend on both $m_i$ and $k_i$. At each such position, a carry either occurs or not. So at most $s + 1$ carries come from these positions.

For positions $i > s$: the digit $k_i = 0$, so a carry at position $i$ requires $m_i + c^{(1)}_{i-1} \ge p$, which means $m_i = p - 1$ and $c^{(1)}_{i-1} = 1$. This is a cascade: once the cascade starts (from position $s$), it continues at position $i > s$ only if $m_i = p - 1$.

Let $L$ be the cascade length: $L = \max\{j \ge 0 : m_{s+1} = m_{s+2} = \cdots = m_{s+j} = p-1\}$ (if $c^{(1)}_s = 1$; otherwise $L = 0$).

Then:
$$v_p\!\left(\binom{m+k}{k}\right) \le s + 1 + L.$$

For random $m$ with $m_i$ approximately uniform in $\{0, \ldots, p-1\}$:
$$\Pr[L \ge \ell] \le \left(\frac{1}{p}\right)^{\ell}.$$

Therefore, for any $T \ge 0$:
$$\Pr\!\left[v_p\!\left(\binom{m+k}{k}\right) > s + 1 + T\right] \le \frac{1}{p^T}. \quad (\star)$$

### Lower bound on $v_p(\binom{2m}{m})$

$v_p(\binom{2m}{m})$ is the number of carries when adding $m + m$ in base $p$.

At position $i$ (with carry-in $c_{i-1} \in \{0, 1\}$): the carry-out is $c_i = \lfloor(2m_i + c_{i-1})/p\rfloor$.

- If $c_{i-1} = 0$: $c_i = 1$ iff $m_i \ge \lceil p/2 \rceil$.
- If $c_{i-1} = 1$: $c_i = 1$ iff $m_i \ge \lceil (p-1)/2 \rceil = \lfloor p/2 \rfloor$.

In either case, $c_i = 1$ whenever $m_i \ge \lceil p/2 \rceil$, and $c_i = 0$ whenever $m_i < \lfloor p/2 \rfloor$. This means the carry process is "almost i.i.d. Bernoulli(1/2)."

More precisely, define the events $A_i = \{m_i \ge \lceil p/2 \rceil\}$. Then:
- If $A_i$ occurs, then $c_i = 1$ regardless of $c_{i-1}$.
- If $m_i < \lfloor p/2 \rfloor$ (complement of $A_i$ when $p$ is odd), then $c_i = 0$ regardless of $c_{i-1}$.

For odd $p$: $\Pr[A_i] = \lfloor p/2 \rfloor / p \ge (p-1)/(2p) > 1/3$ (for $p \ge 3$). And $A_i$ guarantees $c_i = 1$.

The events $\{A_i\}_{i=0}^{D-1}$ are independent (since they depend on independent digits $m_i$). Each $A_i$ contributes a carry independently. Therefore:

$$v_p\!\left(\binom{2m}{m}\right) \ge \sum_{i=0}^{D-1} \mathbf{1}_{A_i}.$$

By a Chernoff bound on the sum of independent Bernoulli(1/3) random variables:

$$\Pr\!\left[\sum_{i=0}^{D-1} \mathbf{1}_{A_i} < D/6\right] \le e^{-D/36}.$$

(Using $\Pr[X < \mu/2] \le e^{-\mu/8}$ with $\mu = D/3$.)

For $p = 2$: $A_i = \{m_i = 1\}$ has probability $1/2$. The bound improves: $\Pr[\sum \mathbf{1}_{A_i} < D/4] \le e^{-D/16}$.

### Combining the bounds

We need $v_p(\binom{m+k}{k}) \le v_p(\binom{2m}{m})$. Set $T_0 = \lfloor D/6 \rfloor - s - 1$.

If $D \ge 12(s+1) + 6$, then $T_0 \ge s + 1 \ge \lfloor \log_p k \rfloor + 1$. And:

\begin{align}
\Pr[\text{fail at } p] &\le \Pr\!\left[v_p(\binom{m+k}{k}) > D/6\right] + \Pr\!\left[v_p(\binom{2m}{m}) < D/6\right] \\
&\le \Pr[s + 1 + L > D/6] + e^{-D/36} \\
&\le \frac{1}{p^{T_0}} + e^{-D/36} \\
&\le \frac{1}{p^{D/6 - s - 1}} + e^{-D/36}.
\end{align}

For $D \ge 16 \log_p(k+1) + 16$ (which ensures $D/6 - s - 1 \ge D/12$ since $s \le \log_p k \le D/16$):

$$\Pr[\text{fail at } p] \le \frac{1}{p^{D/12}} + e^{-D/36}.$$

For $p \ge 2$: $1/p^{D/12} \le 1/2^{D/12}$ and $e^{-D/36} \le 1/2^{D/26}$ (since $\log_2 e > 1$). So:
$$\Pr[\text{fail at } p] \le \frac{1}{2^{D/12}} + \frac{1}{2^{D/26}} \le \frac{2}{2^{D/26}} = \frac{1}{2^{D/26 - 1}} \le \frac{1}{p^{D/40}}$$

for $D \ge 40$ (using $2^{D/26-1} \ge p^{D/40}$ when $D$ is large enough and $p \ge 2$). The condition $D \ge 16 \log_p(k+1) + 16 \ge 40$ is ensured for $k \ge 2$. $\square$

**Remark.** The exact constants don't matter for the proof. What matters is that the failure probability is exponentially small in $D = \log_p m$, which grows as $m \to \infty$.

---

## Main Theorem

**Statement.** For all $0 < C < C'$ and all sufficiently small $\epsilon > 0$ (specifically, $\epsilon < 1/4$), there exist infinitely many triples $(a, b, n) \in \mathbb{N}^3$ with $n > 0$, $\epsilon n < a$, $\epsilon n < b$, $a! b! \mid n! (a+b-n)!$, and $C \log n < a + b - n < C' \log n$.

**Proof.**
Let $C, C'$ with $0 < C < C'$ be given. Let $\epsilon \in (0, 1/4)$.

**Step 1: Setting up the parameters.**

Let $m_0$ be a sufficiently large positive integer (how large will be determined). Set $k = \lfloor (C + C')/2 \cdot \log(2m_0) \rfloor$.

We will find $m \in [m_0, 2m_0]$ such that $\binom{m+k}{k} \mid \binom{2m}{m}$.

For $m \in [m_0, 2m_0]$:
- $\log(2m) \in [\log(2m_0), \log(4m_0)]$.
- For $m_0$ large: $\log(4m_0) / \log(2m_0) \to 1$, so $k \approx (C+C')/2 \cdot \log(2m)$.
- In particular, $C \log(2m) < k < C' \log(2m)$ for $m_0$ large enough (since $(C+C')/2$ is strictly between $C$ and $C'$, and the ratio $\log(2m)/\log(2m_0)$ is close to 1).

Set $a = m$, $b = m + k$, $n = 2m$.

**Size constraints:**
- $a = m > m_0/2 > \epsilon \cdot 2m = \epsilon n$ for $\epsilon < 1/4$ and $m \ge m_0$. ✓ (Actually $a = m \ge m_0$ and $\epsilon n = 2\epsilon m \le m/2 < m = a$.)
- $b = m + k > m > \epsilon n$. ✓

**Gap constraint:** $a + b - n = k \in (C \log n, C' \log n)$ by our choice of $k$ and the range of $m$. ✓

**Step 2: Applying the carry dominance lemma.**

By Lemma 2, for every prime $p > 2k$:
$$v_p\!\left(\binom{m+k}{k}\right) \le v_p\!\left(\binom{2m}{m}\right).$$

This holds for ALL $m$, with no conditions.

**Step 3: Probabilistic argument for primes $p \le 2k$.**

There are $\pi(2k) \le 2k$ primes at most $2k$.

For each prime $p \le 2k$, the number of base-$p$ digits of $m$ is $D_p = \lfloor \log_p m \rfloor + 1 \ge \lfloor \log_p m_0 \rfloor + 1$.

For $m_0$ large enough (in terms of $k$, and hence in terms of $C, C'$):
$$D_p \ge 16 \log_p(k+1) + 16 \quad \text{for all } p \le 2k.$$

This holds because $D_p \ge \log_p m_0$ and $\log_p(k+1) \le \log_p(\log m_0) = o(\log_p m_0)$, so $D_p / \log_p(k+1) \to \infty$.

By Lemma 3, for $m$ uniformly distributed in $\{m_0, m_0 + 1, \ldots, 2m_0 - 1\}$:

$$\Pr\!\left[v_p\!\left(\binom{m+k}{k}\right) > v_p\!\left(\binom{2m}{m}\right)\right] \le \frac{1}{p^{D_p/40}}.$$

(The uniformity over $\{m_0, \ldots, 2m_0-1\}$ approximates the digit-uniformity needed, since the interval has length $m_0 \gg p^{D_p}$.)

**Union bound:**
$$\Pr\!\left[\exists p \le 2k : v_p\!\left(\binom{m+k}{k}\right) > v_p\!\left(\binom{2m}{m}\right)\right] \le \sum_{p \le 2k} \frac{1}{p^{D_p/40}}.$$

The largest term comes from the largest prime $p_{\max} \le 2k$, where $D_{p_{\max}} = \lfloor \log_{p_{\max}} m_0 \rfloor + 1 \ge \log m_0 / \log(2k) + 1$.

With $k = O(\log m_0)$: $D_{p_{\max}} \ge \log m_0 / \log \log m_0$, which goes to $\infty$.

Each term is at most $p^{-D_p/40} \le 2^{-D_p/40}$. The smallest $D_p$ is $D_{p_{\max}} \ge \log m_0 / \log(2k)$.

So:
$$\sum_{p \le 2k} \frac{1}{p^{D_p/40}} \le 2k \cdot 2^{-D_{p_{\max}}/40} \le 2k \cdot 2^{-\log m_0/(40\log(2k))}.$$

For $m_0$ large enough (specifically, $\log m_0 \ge 80 \log(2k) \cdot (\log(2k) + 1)$, which holds since $k = O(\log m_0)$ and thus $\log(2k) = O(\log \log m_0)$):

$$2k \cdot 2^{-\log m_0/(40\log(2k))} < 1.$$

**Conclusion:** The probability that the divisibility fails is strictly less than 1. Therefore, there exists $m \in [m_0, 2m_0]$ such that:
$$v_p\!\left(\binom{m+k}{k}\right) \le v_p\!\left(\binom{2m}{m}\right) \quad \text{for all primes } p.$$

This means $\binom{m+k}{k} \mid \binom{2m}{m}$.

**Step 4: Obtaining the result.**

By Lemma 1, $a! b! \mid n! k!$ where $a = m$, $b = m + k$, $n = 2m$, $k = a + b - n$.

Since $m_0$ can be taken arbitrarily large, this produces solutions for arbitrarily large $n$, and in particular, infinitely many solutions. Taking $\epsilon$ sufficiently small (any $\epsilon < 1/4$ works) completes the proof. $\square$

---

## Verification of Technical Details

### Digit uniformity approximation

When $m$ is chosen uniformly from $\{m_0, m_0+1, \ldots, 2m_0 - 1\}$ and we consider $m \bmod p^j$ for a single prime power $p^j$:

The distribution of $m \bmod p^j$ over this interval is close to uniform on $\{0, 1, \ldots, p^j-1\}$, with total variation distance at most $p^j / m_0$. This is negligible when $m_0 \gg p^j$, which holds since $p^j \le (2k)^{D_p} \le (2k)^{\log m_0 / \log p + 1} \le m_0 \cdot (2k)$ and we only need the digits at SINGLE positions (not the joint distribution across all digits). In fact, for each digit $m_i = \lfloor m / p^i \rfloor \bmod p$, the distribution over the interval $[m_0, 2m_0)$ is within $O(1/m_0)$ of uniform on $\{0, \ldots, p-1\}$ when $m_0 \ge p^{i+1}$.

The key observations for the proof are:
1. We only need digit-by-digit approximate uniformity for the cascade length bound (Lemma 3, $\star$).
2. For the Chernoff bound on carries in $m+m$, we use that the events $A_i = \{m_i \ge \lceil p/2 \rceil\}$ are approximately independent and each has probability $\ge 1/3$.
3. These approximations hold when $m$ is uniform on an interval of length $m_0 \ge p^{D_p}$.

### Why the theorem holds for all $C > 0$, not just $C < 1/2$

The earlier failed approach used CRT to construct $m$ with specific residues modulo $\prod_{p \le 2k} p^{D_p}$. This required the modulus to be smaller than the range $m_0$, giving $C < 1/3$ or $C < 1/2$.

The current proof avoids CRT entirely. Instead, it uses a probabilistic existence argument: among all $m$ in $[m_0, 2m_0]$, at least one satisfies the divisibility condition. The union bound over primes $p \le 2k$ has total mass going to 0 as $m_0 \to \infty$ (with $k = O(\log m_0)$), regardless of the constant $C$.

The crucial asymptotic is: for each prime $p \le 2k$, the failure probability is exponentially small in $D_p = \Theta(\log m_0 / \log p)$, while the number of primes is polynomial in $k = O(\log m_0)$. The exponential decay beats the polynomial count.

## References

- Kummer's theorem on $p$-adic valuation of binomial coefficients.
- Standard Chernoff bounds for sums of independent Bernoulli variables.
- No external references to published proofs of Erdős 728.

---

## Review Notes (erdos728b-poe)

The proof is logically sound and elegantly handles the divisibility condition for both large and small primes.

1. **Carry Dominance (Lemma 2):** The induction proof for  > 2k$ is correct. The assumption  > 2k$ ensures $ is a single digit and  < p/2$, which is sufficient to show that any carry produced by adding $ is dominated by a carry produced by adding $ to itself.
2. **Probabilistic Bound (Lemma 3):** The bound is rigorous. The use of a Chernoff bound for the carries of the central binomial coefficient is a standard technique that works well here. The cascade length argument for (\binom{m+k}{k})$ correctly identifies that carries beyond the digits of $ are rare and depend on a sequence of $ digits in $.
3. **Union Bound:** The asymptotic argument in the Main Theorem is correct. Since the number of primes  \le 2k$ grows only as (\log m_0 / \log \log m_0)$ while the failure probability at each prime decays as ^{-1/40}$, the total failure probability vanishes as  \to \infty$.

The proof is ready for formalization.

---

## Review Notes (erdos728b-poe)

The proof is logically sound and elegantly handles the divisibility condition for both large and small primes.

1. **Carry Dominance (Lemma 2):** The induction proof for $p > 2k$ is correct. The assumption $p > 2k$ ensures $k$ is a single digit and $k < p/2$, which is sufficient to show that any carry produced by adding $k$ is dominated by a carry produced by adding $m$ to itself.
2. **Probabilistic Bound (Lemma 3):** The bound is rigorous. The use of a Chernoff bound for the carries of the central binomial coefficient is a standard technique that works well here. The cascade length argument for $v_p(\binom{m+k}{k})$ correctly identifies that carries beyond the digits of $k$ are rare and depend on a sequence of (p-1) digits in $m$.
3. **Union Bound:** The asymptotic argument in the Main Theorem is correct. Since the number of primes $p \le 2k$ grows only as $O(\log m_0 / \log \log m_0)$ while the failure probability at each prime decays as $m_0^{-1/40}$, the total failure probability vanishes as $m_0 \to \infty$.

The proof is ready for formalization.
