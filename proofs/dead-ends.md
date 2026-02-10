# Dead Ends

## Factorial Divisibility with Logarithmic Sum via $M=m!-1$ (rejected 2026-02-10)
**Tried:** Using $M=m!-1$ to handle $p \le m$ and CRT to handle $p > m$.
**Failed because:** The modulus of "bad" primes $Q \approx M^k$ is much larger than $M$, and the density of valid $a$ is too small ($\exp(-m(\log m)^2)$) to guarantee existence in $[0, M]$.

## CRT construction with $M = \text{lcm}(1,\ldots,2k)-1$ (explored, superseded 2026-02-10)
**Tried:** Using $M = t \cdot \text{lcm}(1,\ldots,2k) - 1$ with symmetric split $a = m$, $n = 2m$, and CRT to force digit conditions.
**Issue:** The CRT modulus $L \approx e^{3k}$ exceeds the target range $e^{k/C}$ when $C \ge 1/3$, limiting the construction to $C < 1/3$. Not a dead end per se (works for small $C$), but superseded by the probabilistic approach in `erdos728_v2.md` which handles all $C > 0$.
