# Related Work

## Problem 729 (weaker, proved)

This group has independently proved the weaker Problem 729:

> If $\nu_p(a!) + \nu_p(b!) \leq \nu_p(n!)$ for all primes $p > P$, then $a + b \leq n + O(\log n)$.

Two independent proofs exist:
- `../erdos-729/Erdos/Basic.lean` — 318 lines, 0 sorrys, 0 axioms
- `../erdos-729-google/Erdos/Lemmas.lean` + `Basic.lean` — 717 lines, 0 sorrys, 0 axioms

Both use Legendre's formula and digit sum bounds in base $p$ for a fixed prime $p > P$.

**Key domain knowledge from 729:**
- Legendre's formula: $\nu_p(n!) = (n - S_p(n))/(p-1)$ where $S_p$ is the digit sum in base $p$
- Digit sum bound: $S_p(n) \leq (p-1)(\log_p n + 1)$
- The divisibility $a!b! \mid n!$ (ignoring small primes) forces $a + b \leq n + O(\log n)$

**Important: 729 ≠ 728.** Problem 729 is a universal bound (for all valid triples, the gap is bounded). Problem 728 asks for existence of triples where the gap is exactly $\Theta(\log n)$. These are opposite proof directions — 729 uses bounding, 728 requires construction.
