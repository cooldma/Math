# Counterexample Search for Triangular $D(n)$-Pairs $\{n, 2n\}$ (arXiv:2611.25270v1)

High-performance multi-threaded C++20 counterexample search for **Conjecture 1.3** of Alan Filipin, Yasutsugu Fujita, and Ana Jurasić, *"On the Non-extendibility of Triangular $D(n)$-Pairs $\{n, 2n\}$ with $n = 2k^2 \pm k$"* ([arXiv:2611.25270v1](https://arxiv.org/abs/2611.25270v1), Nov 2026).

## Conjecture

Let $k$ be an odd positive integer and $\varepsilon \in \{-1, 1\}$ such that $p = 4k + \varepsilon$ is prime (equivalently, $p \ge 3$ is prime with $p \equiv 3 \text{ or } 5 \pmod 8$), and let $n = 2k^2 + \varepsilon k = (p^2 - 1)/8$. Conjecture 1.3 states that there does not exist a Triangular $D(n)$-quadruple $\{n, 2n, c, d\}$ (distinct positive integers such that $ab + n$ is a triangular number for all distinct $a, b$ in the set).

The paper proves the conjecture for 8 pairs $(k, \varepsilon)$ ($k \le 27$) and reports a heuristic elliptic-curve search up to $k = 249$.

## Exact Reduction

By Section 2 of the paper, a Triangular $D(n)$-quadruple $\{n, 2n, c, d\}$ exists if and only if there exist integers $1 \le \ell < m$ such that:

1. $\lambda \mid C_\ell$ and $\lambda \mid C_m$, where $\lambda = n/3 = (p^2 - 1)/24$ and $C_\ell$ is OEIS A305539:
   $$C_0 = 0, \quad C_1 = 1, \quad C_{\ell+1} = 34 C_\ell - C_{\ell-1} + 1, \qquad 24 C_\ell = P_{2\ell} P_{2\ell+2},$$
   with $(P_j)$ the Pell numbers ($P_0 = 0, P_1 = 1, P_{j+1} = 2 P_j + P_{j-1}$).
2. $8 p^2 (C_\ell / \lambda)(C_m / \lambda) + 1 = (Z')^2$ is a perfect square.

Since $n = (p-1)(p+1)/8$ is odd and $\gcd(P_{2\ell}, P_{2\ell+2}) = 2$, the divisibility condition $\lambda \mid C_\ell$ is equivalent to the CRT system
$$\ell \equiv 0 \text{ or } -1 \pmod{r(q^e)} \qquad \forall\, q^e \parallel n,$$
where $r(q^e)$ is the even-index Pell rank of apparition (the smallest $r \ge 1$ with $q^e \mid P_{2r}$).

## Programs

* [`search_tdn.cpp`](search_tdn.cpp): Multi-threaded C++20 engine over all primes $p \equiv 3, 5 \pmod 8$ in $[P_{\min}, P_{\max}]$.
  * Linear smallest-prime-factor sieve + $O(\log q)$ Lucas $U_k(6, 1) = P_{2k}/2$ rank precomputation.
  * Exact min-heap CRT expansion to extract the smallest valid indices $\ell \le L_{\max}$.
  * 64-bit bitset-vectorized 12-prime quadratic-residue filter using primes with prime Pell periods $T \in [47, 160]$ (reducing 12-prime survival to ~0.045% and running in $O(1)$ per pair regardless of the digit length of $C_\ell, C_m$), followed by 36 additional small primes and 64 large 31-bit primes.
  * Built-in self-test suite reproducing Lemma 4.1 (all 8 small triples for $3 \le k < 1000$).
* [`search_pell.cpp`](search_pell.cpp): Dedicated modular quadratic-residue search for Pell primes $p = Q_\ell = P_{2\ell+1}$ ($\ell \equiv 1, 2 \pmod 4$, where $\lambda = C_\ell$ and $c' = 1$), testing $m$ across all 4 CRT residue classes modulo $\ell(\ell+1)$.

## Build & Run

```bash
g++ -O3 -march=native -flto -std=c++20 -pthread search_tdn.cpp -o search_tdn
g++ -O3 -march=native -flto -std=c++20 -pthread search_pell.cpp -o search_pell

# Example runs
./search_tdn --pmax 200000000 --lmax 10000000 --maxidx 4096 --threads 20
./search_tdn --pmax 20000 --lmax 100000000 --maxidx 32768 --skip-proved --threads 20
./search_pell --steps 20000000 2 5 6 14 26 29 50 90 261 650
```

## Search Results

All runs on a 10-core / 20-thread Intel Xeon E5-2630 v4 found **0 counterexamples** across **549.77 billion** $(\ell, m)$ pairs:

| Campaign | Scope | Pairs / Candidates | Throughput | Time | Counterexamples |
| :--- | :--- | ---: | ---: | ---: | ---: |
| Broad prime sweep | All **5,539,901** primes $p \in [11, 2 \times 10^8]$ ($k \le 5 \times 10^7$), $L_{\max}=10^7$, `maxidx=4096` | 40,899,013,166 | 2,733.9 M/s | 14.96 s | **0** |
| Deep unproved sweep | All **1,130** unproved primes $p \in [11, 20{,}000]$, $L_{\max}=10^8$ ($c, d \le 10^{153{,}000{,}000}$), `maxidx=32768` | 379,222,559,222 | 25,531.0 M/s | 14.85 s | **0** |
| Ultra-deep small primes | **15** smallest unproved primes $p \in [59, 200]$, $L_{\max}=10^9$, `maxidx=131072` | 128,848,035,840 | 3,399.9 M/s | 37.90 s | **0** |
| Pell primes $Q_\ell$ | All **10** Pell primes $Q_\ell$ ($2 \le \ell \le 1500$, up to 498-digit $Q_{650}$), $m \le 8.46 \times 10^{12}$ | 800,000,000 | 57.0 M/s | 14.03 s | **0** |
| Singular curves (Lemma 4.3) | $8n^2+8n+1=\square$ and $32n^2+8n+1=\square$ for $j \le 1500$ ($p \le 10^{574}$) | 3,000 | — | < 0.1 s | **0** |
