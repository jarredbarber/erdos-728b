# Literature Survey: Erdos Problem 728

## Problem Statement
**Erdos Problem 728**: Construct integers $a, b, n$ such that $a!b! \mid n!(a+b-n)!$ with $a+b > n$.
Specifically, find the standard construction that maximizes the gap $k = a+b-n$.
It is known that $k$ can be as large as $\Theta(\frac{\log n}{\log \log n})$.

## Standard Construction
The standard construction uses factorials to handle small primes ("bad primes").
Let $m$ be a parameter.
Define:
- $n = m!$
- $a = m! - 1$
- $b = m$
- $k = m - 1$

Check: $a+b = m!-1 + m = n + m - 1 = n + k$. Consistent.
We require $a!b! \mid n!k!$.

### Analysis of the Construction
We verify $\nu_p(a!) + \nu_p(b!) \le \nu_p(n!) + \nu_p(k!)$ for all primes $p$.
This is equivalent to checking Legendre's formula condition:
$S_p(n) + S_p(k) \le S_p(a) + S_p(b)$.

**Case 1: Small Primes ($p \le m$)**
- $n = m!$ is divisible by $p$ (with high multiplicity). In base $p$, $n$ ends in many zeros.
- $S_p(n)$ is small. (Specifically $S_p(n) = S_p(n/p^e)$).
- $a = m! - 1$. In base $p$, $a$ ends in digits $(p-1)$.
- Adding $1$ to $a$ causes a cascade of carries.
- Thus $S_p(a)$ is large (close to maximal for numbers of that size).
- The inequality $S_p(n) + S_p(k) \le S_p(a) + S_p(b)$ holds easily because RHS is large and LHS is small.

**Case 2: Large Primes ($p > m$)**
- $p$ does not divide $m!$ (since $m! = 1 \times \dots \times m$ and $p > m$).
- $n = m! \not\equiv 0 \pmod p$.
- $a = m! - 1$.
- Since $n \not\equiv 0 \pmod p$, $n \pmod p \neq 0$.
- $a = n-1$.
- Addition $a+1 = n$ does not cause a carry in base $p$ (unless $a \equiv -1 \pmod p$, i.e., $n \equiv 0 \pmod p$, which is false).
- Since no carry occurs when adding 1 to $a$ to get $n$:
  $S_p(n) = S_p(a) + 1$.
- We need $S_p(n) + S_p(k) \le S_p(a) + S_p(b)$.
  $(S_p(a) + 1) + S_p(k) \le S_p(a) + S_p(b)$.
  $1 + S_p(k) \le S_p(b)$.
- Since $k = m-1$ and $b = m$, and $p > m$, we have $k, b < p$.
- So $S_p(k) = k$ and $S_p(b) = b$.
- The inequality becomes $1 + (m-1) \le m \iff m \le m$.
- This holds with equality.

### Conclusion
The construction $n = m!$ works and provides a gap $k = m-1$.
Since $n \approx m^m$, $m \approx \frac{\log n}{\log \log n}$.
Thus $k = \Theta(\frac{\log n}{\log \log n})$.

## Handling Bad Primes
The "bad primes" are the small primes where digit sum inequalities are hardest to satisfy.
- The construction handles them by choosing $n$ to be a factorial ($m!$), which forces $n$ to have many trailing zeros in base $p$ for all $p \le m$.
- This effectively "clears" the digit sum of $n$ for small primes, making the LHS of the inequality small.
- This avoids the need for complex CRT or Sieve methods for this specific problem, as the factorial structure naturally aligns with the prime requirements.
