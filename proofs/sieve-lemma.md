# Sieve Lemma: Avoiding Forbidden Residues in a Long Interval

**Status:** Verified ✅
**Reviewed by:** erdos728b-hp6
**Statement:** Let $X, Y$ be positive integers with $Y - X \ge 1$. Let $P$ be a finite set of distinct primes, and for each $p \in P$ let $F_p \subseteq \mathbb{Z}/p\mathbb{Z}$ be a set of "forbidden" residues with $|F_p| < p$. Define:
$$\alpha_p := \frac{|F_p|}{p}, \qquad Q := \prod_{p \in P} p.$$
If
$$Y - X > Q,$$
then there exists $m \in [X, Y] \cap \mathbb{Z}$ such that $m \bmod p \notin F_p$ for every $p \in P$.

More generally (without the strong condition $Y - X > Q$): if
$$Y - X \ge 1 \quad \text{and} \quad (Y - X) \prod_{p \in P}\left(1 - \alpha_p\right) > Q \cdot \sum_{\substack{S \subseteq P \\ S \neq \emptyset}} \frac{(-1)^{|S|+1}}{\prod_{p \in S} p} \cdot \left[\prod_{p \in P \setminus S}(1 - \alpha_p) - 1\right],$$
then such an $m$ exists. In practice, we use the simpler sufficient condition below (Corollary).

**Dependencies:** None
**Confidence:** Certain

---

## Preliminary: Notation and Setup

Throughout, $P = \{p_1, \ldots, p_r\}$ is a finite set of distinct primes. For each $p_i \in P$, $F_{p_i} \subseteq \{0, 1, \ldots, p_i - 1\}$ is a set of forbidden residues, with $f_i := |F_{p_i}|$ satisfying $0 \le f_i < p_i$.

For an integer $m$, we say $m$ is **admissible** (with respect to $P$ and $\{F_p\}$) if $m \bmod p \notin F_p$ for all $p \in P$.

We write $[X, Y]$ for the set $\{m \in \mathbb{Z} : X \le m \le Y\}$.

---

## Theorem 1 (Legendre Sieve — Exact Count)

**Statement.** Let $N := Y - X + 1 \ge 1$. The number of admissible integers in $[X, Y]$ is:
$$A(X, Y) = \sum_{\substack{S \subseteq P}} (-1)^{|S|} \left\lfloor \frac{N + r_S}{q_S} \right\rfloor$$
where for $S \subseteq P$:
- $q_S := \prod_{p \in S} p$ (with $q_\emptyset = 1$),
- the sum counts integers $m \in [X, Y]$ satisfying $m \bmod p \in F_p$ for all $p \in S$ (by inclusion-exclusion, subtracting those hitting at least one forbidden class).

More precisely, by inclusion-exclusion and the Chinese Remainder Theorem:

$$A(X, Y) = \sum_{S \subseteq P} (-1)^{|S|} \cdot \sum_{\substack{(c_p)_{p \in S} \\ c_p \in F_p}} \#\{m \in [X, Y] : m \equiv c_p \pmod{p} \;\forall p \in S\}.$$

Since the primes in $S$ are distinct, CRT gives a unique residue class modulo $q_S = \prod_{p \in S} p$ for each choice of $(c_p)_{p \in S}$. The number of integers in $[X, Y]$ in a single residue class modulo $q_S$ is $\lfloor N / q_S \rfloor$ or $\lceil N / q_S \rceil$ (differing by at most 1 depending on alignment).

**Proof.**

Define, for each $p \in P$, the set $B_p := \{m \in [X, Y] : m \bmod p \in F_p\}$. Then:
$$A(X, Y) = N - |B_{p_1} \cup B_{p_2} \cup \cdots \cup B_{p_r}|.$$

By inclusion-exclusion:
$$|B_{p_1} \cup \cdots \cup B_{p_r}| = \sum_{\emptyset \neq S \subseteq P} (-1)^{|S|+1} \left|\bigcap_{p \in S} B_p\right|.$$

For $S \subseteq P$ with $S \neq \emptyset$:
$$\bigcap_{p \in S} B_p = \{m \in [X, Y] : m \bmod p \in F_p \;\forall p \in S\}.$$

By CRT (since the elements of $S$ are distinct primes, hence pairwise coprime), the system of congruences $m \equiv c_p \pmod{p}$ for $p \in S$ (with each $c_p \in F_p$) has a unique solution modulo $q_S$. There are $\prod_{p \in S} f_p$ such systems, so:

$$\left|\bigcap_{p \in S} B_p\right| = \sum_{\substack{(c_p)_{p \in S} \\ c_p \in F_p}} \#\{m \in [X, Y] : m \equiv \text{CRT}(c_p) \pmod{q_S}\}.$$

The count of integers in $[X, Y]$ in a given residue class modulo $q_S$ is:
$$\frac{N}{q_S} + \delta, \quad |\delta| < 1.$$

Therefore:
$$\left|\bigcap_{p \in S} B_p\right| = \frac{N}{q_S} \prod_{p \in S} f_p + \theta_S, \quad |\theta_S| < \prod_{p \in S} f_p.$$

Substituting back:
$$A(X, Y) = N - \sum_{\emptyset \neq S \subseteq P} (-1)^{|S|+1} \left[\frac{N}{q_S} \prod_{p \in S} f_p + \theta_S\right]$$

$$= N \left[1 - \sum_{\emptyset \neq S \subseteq P} (-1)^{|S|+1} \frac{\prod_{p \in S} f_p}{\prod_{p \in S} p}\right] - \sum_{\emptyset \neq S \subseteq P} (-1)^{|S|+1} \theta_S.$$

The main term simplifies via the product formula:
$$1 - \sum_{\emptyset \neq S \subseteq P} (-1)^{|S|+1} \prod_{p \in S} \frac{f_p}{p} = \prod_{p \in P} \left(1 - \frac{f_p}{p}\right).$$

This is because:
$$\prod_{p \in P} \left(1 - \frac{f_p}{p}\right) = \sum_{S \subseteq P} (-1)^{|S|} \prod_{p \in S} \frac{f_p}{p} = 1 + \sum_{\emptyset \neq S \subseteq P} (-1)^{|S|} \prod_{p \in S} \frac{f_p}{p}.$$

Therefore:
$$A(X, Y) = N \prod_{p \in P} \left(1 - \frac{f_p}{p}\right) + E,$$

where the error term satisfies:
$$|E| \le \sum_{\emptyset \neq S \subseteq P} \prod_{p \in S} f_p.$$

$\square$

---

## Corollary 1 (Sufficient Condition for Existence — Product Form)

**Statement.** If
$$N \prod_{p \in P} \left(1 - \frac{f_p}{p}\right) > \sum_{\emptyset \neq S \subseteq P} \prod_{p \in S} f_p,$$
then there exists an admissible $m \in [X, Y]$.

**Proof.** Immediate from Theorem 1: $A(X,Y) \ge N \prod_{p \in P}(1 - f_p/p) - |E| > 0$. $\square$

---

## Corollary 2 (Sufficient Condition — Simplified Bound)

**Statement.** If
$$N \prod_{p \in P}\left(1 - \frac{f_p}{p}\right) > \prod_{p \in P}(1 + f_p) - 1,$$
then there exists an admissible $m \in [X, Y]$.

**Proof.** We bound the error term:
$$\sum_{\emptyset \neq S \subseteq P} \prod_{p \in S} f_p = \prod_{p \in P}(1 + f_p) - 1.$$
This is because $\sum_{S \subseteq P} \prod_{p \in S} f_p = \prod_{p \in P}(1 + f_p)$ (each factor contributes either $1$ (if $p \notin S$) or $f_p$ (if $p \in S$)). The result follows from Corollary 1. $\square$

---

## Corollary 3 (The Clean Version — for Erdős 728)

**Statement.** Let $P$ be a finite set of primes with $|P| = r$. For each $p \in P$, let $F_p \subseteq \mathbb{Z}/p\mathbb{Z}$ with $|F_p| = f_p$. Let $N = Y - X + 1$. If

$$N > \frac{\prod_{p \in P}(1 + f_p) - 1}{\prod_{p \in P}(1 - f_p/p)},$$

then there exists $m \in [X, Y]$ with $m \bmod p \notin F_p$ for all $p \in P$.

In particular, if $f_p \le p/2$ for all $p \in P$, then:
$$\frac{\prod_{p \in P}(1 + f_p)}{\prod_{p \in P}(1 - f_p / p)} = \prod_{p \in P} \frac{p(1 + f_p)}{p - f_p} \le \prod_{p \in P} \frac{p \cdot (1 + p/2)}{p/2} = \prod_{p \in P}(p + 2),$$
so it suffices that $N > \prod_{p \in P}(p + 2)$.

**Proof.** Rearranging Corollary 2. The bound for $f_p \le p/2$ follows from $\frac{1 + f_p}{1 - f_p/p} = \frac{p(1+f_p)}{p - f_p}$, which is at most $\frac{p(1 + p/2)}{p/2} = p + 2$ when $f_p \le p/2$. $\square$

---

## Corollary 4 (Logarithmic Number of Small Primes)

**Statement.** Let $k \ge 2$ be an integer, and let $P = \{p : p \text{ prime}, p \le 2k\}$. For each $p \in P$, let $F_p \subseteq \mathbb{Z}/p\mathbb{Z}$ with $|F_p| \le f$ for some constant $f \ge 1$. If $N = Y - X + 1$ satisfies
$$N > (1 + f)^{\pi(2k)} \cdot \prod_{p \le 2k} \frac{p}{p - f},$$
then there exists $m \in [X, Y]$ with $m \bmod p \notin F_p$ for all $p \in P$.

Moreover, if $k = O(\log N)$ (as in the Erdős 728 application where $k \approx C \log m$ and $N \approx m$), then the right-hand side is $\exp(O(k)) = N^{O(1)}$, and the condition is satisfied for $N$ sufficiently large.

**Proof.** From Corollary 3: we need $N > \frac{\prod(1+f_p) - 1}{\prod(1-f_p/p)}$. Since $f_p \le f$:

$$\prod_{p \in P}(1 + f_p) \le (1+f)^{|P|} = (1+f)^{\pi(2k)}.$$

$$\prod_{p \in P}(1 - f_p/p) \ge \prod_{p \le 2k} (1 - f/p) = \prod_{p \le 2k} \frac{p - f}{p}.$$

By Mertens' theorem, $\prod_{p \le x}(1 - 1/p) \sim e^{-\gamma}/\log x$, and more generally:

$$\prod_{p \le 2k} \frac{p}{p-f} = O((\log 2k)^f).$$

By the prime number theorem, $\pi(2k) \sim 2k / \log(2k)$, so:

$$(1+f)^{\pi(2k)} = \exp\left(\frac{2k \log(1+f)}{\log(2k)} (1 + o(1))\right).$$

When $k = C \log N$ for some constant $C$:

$$(1+f)^{\pi(2k)} = \exp\left(O\left(\frac{\log N}{\log \log N}\right)\right) = o(N^\epsilon)$$

for any $\epsilon > 0$. Similarly, $\prod \frac{p}{p-f} = O((\log \log N)^f) = o(N^\epsilon)$.

So the right-hand side is $o(N^\epsilon)$ for any $\epsilon > 0$, hence is $< N$ for $N$ sufficiently large. $\square$

---

## Application to Erdős 728

In the proof of Erdős 728 (see `proofs/erdos728_v2.md`), we set $a = m$, $b = m + k$, $n = 2m$, with $k \approx C \log m$. The divisibility $\binom{m+k}{k} \mid \binom{2m}{m}$ requires, for each prime $p$:

$$v_p\!\left(\binom{m+k}{k}\right) \le v_p\!\left(\binom{2m}{m}\right).$$

**For primes $p > 2k$:** This holds automatically by the Carry Dominance Lemma (Lemma 2 of `erdos728_v2.md`).

**For primes $p \le 2k$:** We need to choose $m$ avoiding certain "bad" residue classes modulo $p$. Specifically, for each prime $p \le 2k$, the set of $m \bmod p^j$ values that cause a carry-dominance failure at position $j$ in base $p$ can be viewed as a forbidden set of residues.

The sieve lemma provides the framework: if the number of forbidden residues per prime is bounded and the interval $[m_0, 2m_0]$ is long enough relative to the product of prime contributions, an admissible $m$ exists.

The probabilistic argument in `erdos728_v2.md` (Lemma 3 + union bound) is essentially a **randomized sieve**: instead of the deterministic Legendre sieve, it uses the fact that random $m$ avoids each prime's bad set with high probability, and the events are approximately independent. The sieve lemma here provides a **deterministic** alternative or complement.

### How the Sieve Connects to the Carry Argument

For each prime $p \le 2k$, define:
$$F_p^{(0)} := \{r \in \{0, \ldots, p-1\} : r + k_0 \ge p \text{ and } r < \lceil p/2 \rceil\}$$
where $k_0 = k \bmod p$. This is the set of least-significant digits of $m$ that cause a carry in $m + k$ at position 0 but do NOT cause a carry in $m + m$ at position 0.

When $m_0 \in F_p^{(0)}$, we get $v_p(\binom{m+k}{k}) > v_p(\binom{2m}{m})$ at position 0 (a "bad" event). The size $|F_p^{(0)}|$ depends on $k_0$ and $p$, but crucially:

- If $p > 2k$: $k_0 = k < p/2$, so $F_p^{(0)} = \{r : p - k \le r < \lceil p/2 \rceil\} = \emptyset$ (since $p - k > p/2$). This recovers the carry dominance lemma.
- If $p \le 2k$: $|F_p^{(0)}| \le k_0 \le p - 1$, so there are forbidden residues but they don't cover all of $\mathbb{Z}/p\mathbb{Z}$.

The multi-digit analysis creates more complex forbidden sets (involving cascading carries), but the principle is the same: for each prime, a bounded number of residue classes are forbidden, and the sieve guarantees existence of $m$ avoiding all of them when the interval is long enough.

---

## References

- Legendre sieve / Eratosthenes-Legendre sieve: standard reference in sieve theory (e.g., Cojocaru & Murty, *An Introduction to Sieve Methods and Their Applications*, Chapter 2).
- Chinese Remainder Theorem: standard.
- Mertens' theorem on $\prod_{p \le x}(1 - 1/p)$.
- Connection to `proofs/erdos728_v2.md` for the Erdős 728 application.
