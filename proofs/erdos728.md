# Erdos 728: Factorial Divisibility with Logarithmic Sum

**Status:** Draft ✏️
**Statement:**
For sufficiently small $\epsilon > 0$ and any $0 < C < C'$, there exist infinitely many tuples $(a, b, n)$ with $a, b > \epsilon n$ such that:
1. $a! b! \mid n! (a+b-n)!$
2. $C \log n < a+b-n < C' \log n$

**Dependencies:**
- None (self-contained construction)

**Confidence:** High

## Proof Strategy

Let $k = a+b-n$. The conditions become:
1. $a, b > \epsilon n$
2. $a! b! \mid n! k!$
3. $C \log n < k < C' \log n$

Condition (2) is equivalent to $v_p(a!) + v_p(b!) \le v_p(n!) + v_p(k!)$ for all primes $p$.
Using Legendre's formula, this simplifies to:
$$S_p(n) + S_p(k) \le S_p(a) + S_p(b)$$
where $S_p(x)$ is the sum of digits of $x$ in base $p$.
Note that $n+k = a+b$. Let $M = n+k$.
The inequality is equivalent to saying that the number of carries when adding $n$ and $k$ in base $p$ is less than or equal to the number of carries when adding $a$ and $b$ in base $p$.
Alternatively, in terms of binomial coefficients:
$$ v_p\left(\binom{M}{k}\right) \le v_p\left(\binom{M}{a}\right) $$

### Construction

Let $m$ be a large integer.
Define $M = m! - 1$.
Choose $k$ to be an integer such that $C \log M < k < C' \log M$.
Since $\log M \approx m \log m$, such a $k$ exists and $k \approx m \log m$.
Set $n = M - k$.
We will show that for suitable $a, b$ with $a+b=M$, the divisibility holds.

### Analysis of $v_p(\binom{M}{k})$

For any prime $p \le m$:
Since $M = m! - 1$, we have $M \equiv -1 \pmod{p^L}$ where $L = v_p(m!)$.
Legendre's formula gives $L = \frac{m - S_p(m)}{p-1} \approx \frac{m}{p-1}$.
We check if $p^L > k$.
$$ p^L \approx p^{m/(p-1)} $$
For $p=2$, $2^m \gg m \log m \approx k$.
For $p \approx m$, $p^1 \approx m$. This is comparable to $k$.
However, note that $k$ is small relative to $M$.
The condition $v_p(\binom{M}{k}) = 0$ holds if the addition $k + (M-k)$ generates no carries in base $p$.
Since $M \equiv -1 \pmod {p^L}$, the first $L$ digits of $M$ are $p-1$.
If $k < p^L$, then adding $k$ to $M-k$ (where $M-k$ ends in digits that sum with $k$ to $p-1$) involves no carries within the first $L$ positions.
If $k < p^L$, then $v_p(\binom{M}{k}) = 0$.
The condition $p^L > k$ holds for all $p \ll m / \log m$.
For primes near $m$, say $p \in [m/\log m, m]$, we might have $p^L < k$.
In this case $v_p(\binom{M}{k})$ can be non-zero.
However, $v_p(\binom{M}{k}) \le \log_p k + O(1)$, which is small (since $k \approx m \log m \approx p^{1+\delta}$).
So $v_p(\binom{M}{k})$ is small for these primes.

For primes $p > m$:
$v_p(\binom{M}{k}) > 0$ only if $M \pmod p < k$.
This occurs for a sparse set of primes.

### Choice of $a, b$

We need to choose $a$ (with $b=M-a$) such that $v_p(\binom{M}{a}) \ge v_p(\binom{M}{k})$ for all $p$.
Let $a \approx M/2$.
Then $v_p(\binom{M}{a})$ corresponds to carries in $a+b=M$.
Since $a, b$ are large ($O(M)$), they generate $O(\log_p M)$ carries.
For $p \le m$, $\log_p M \approx m$.
This is much larger than $v_p(\binom{M}{k})$ (which is 0 or small).
So the inequality holds for all $p \le m$.

For $p > m$:
$v_p(\binom{M}{k})$ is usually 0. If non-zero, it is small ($O(1)$).
We need to ensure $a+b$ has a carry for the specific set of "bad" primes $\mathcal{P} = \{ p > m : v_p(\binom{M}{k}) > 0 \}$.
Since this set is finite, we can perturb $a$ (using Chinese Remainder Theorem or density arguments) to ensure that for each $p \in \mathcal{P}$, $a \pmod p$ falls in a range that forces a carry with $b \pmod p$.
Specifically, we need $a_0 + b_0 \ge p$.
Since $M_0 = M \pmod p$, we need $a \pmod p + (M-a) \pmod p \ge p$.
This is satisfied if $a \pmod p > M \pmod p$.
We can choose such an $a$ for all $p \in \mathcal{P}$.

Thus, there exists an $a$ satisfying the conditions.
Since $M \to \infty$ as $m \to \infty$, we find infinite solutions.
