# Dead Ends

## Factorial Divisibility with Logarithmic Sum via $M=m!-1$ (rejected 2026-02-10)
**Tried:** Using $M=m!-1$ to handle $p \le m$ and CRT to handle $p > m$.
**Failed because:** The modulus of "bad" primes $Q \approx M^k$ is much larger than $M$, and the density of valid $a$ is too small ($\exp(-m(\log m)^2)$) to guarantee existence in $[0, M]$.
