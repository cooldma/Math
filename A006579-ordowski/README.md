# OEIS A006579: smallest counterexample to Ordowski's conjecture

**Sequence.** A006579: a(n) = Σ_{k=1}^{n−1} gcd(n, k) = P(n) − n, where
P(n) = Σ_{k=1}^{n} gcd(k, n) is Pillai's arithmetical function (A018804).

**Conjecture** (Thomas Ordowski, A006579, Jun 2025): a(n) ≢ −1 (mod n) for every composite n.
Since a(n) ≡ P(n) (mod n), this is the same as P(n) ≢ −1 (mod n). For prime p it fails trivially,
because P(p) = 2p − 1.

**Status before this work.** The conjecture is false. The counterexample

  n = 23492890653051 = 3 · 37 · 43 · 42307 · 116341,  P(n) + 1 = 26 · n,

is credited to Vejalla and Adamczewski on A018804 and A340079. As of 25 Nov 2026, A006579 itself carried no note,
and no one had shown whether this n is the smallest.

## Result

**Theorem.** n = 23492890653051 is the smallest composite n with P(n) ≡ −1 (mod n). It is the only
one below 10¹⁵.

## Reduction

1. **Counterexamples are squarefree.** P is multiplicative, and P(p^a) = p^{a−1}((a+1)p − a).
   So if p² | n, then p | P(n), which gives P(n) + 1 ≡ 1 (mod p) and n ∤ P(n) + 1.
2. **Squarefree formula.** For squarefree n, P(n) = ∏_{p | n} (2p − 1).
3. **Split off the largest prime.** Write n = m·q with q = gpf(n), m > 1 squarefree, and
   g = gpf(m) < q. Then P(n) = P(m)(2q − 1), and P(n) ≡ −1 (mod n) holds iff both of these hold:
   * (mod q) 2q − 1 ≡ −1, so q | P(m) − 1;
   * (mod m) P(m)(2q − 1) ≡ −1. This forces gcd(P(m), m) = 1 and puts q in one residue class
     mod m (or mod m/2 when m is even), or rules m out.

## Search ([`dfs.c`](dfs.c))

A depth-first search over primes enumerates every squarefree m with m·(gpf(m) + 1) ≤ X,
which is exactly the set of m that leave room for some q > g with mq ≤ X. For each m it does one of two things:

* **m ≤ T (default 2·10⁶):** factor P(m) − 1 by trial division and try each prime factor q in (g, X/m].
* **m > T:** walk the residue class of q from the mod-m condition through (g, X/m] (about 2X/m²
  values). Test q | P(m) − 1, then test q for primality with deterministic Miller–Rabin.

Every candidate is re-checked exactly with 128-bit arithmetic before it is reported. With 2¹³·X < 2⁶⁴, all
intermediate values fit for X ≤ 10¹⁵.

```
gcc -O3 -march=native -fopenmp -o dfs dfs.c -lm
./dfs 1000000000000000          # X [k] [T]; searches P(n) == -k (mod n), default k = 1
```

| X | nodes (m) | hits | time (consumer desktop, OpenMP) |
|---|---|---|---|
| 2.35·10¹³ | 7.78·10⁸ | 23492890653051 | 61 s |
| 10¹⁵ | 1.37·10¹⁰ | 23492890653051 | 1049 s ([log](run_dfs_1e15.log)) |

## Validation

[`search.c`](search.c) is an independent segmented sieve. It computes ∏(2p − 1) for every
squarefree n in a range and tests n | P(n) + k directly.

* `search test 30000` matches brute-force Σ gcd(k, n) for all n ≤ 30000.
* For the generalized condition P(n) ≡ −k (mod n) with k ∈ {−1, −3, −5, 7, 11, −7}, the sieve
  and the DFS give identical hit lists up to 10⁹. These k have real solutions to compare.
  The DFS misses only solutions that depend on k: a prime dividing both m and k,
  or P(m) < k. Neither can happen for k = 1.
* The DFS has two branches. Running with T = 3·10³ and with T = 3·10⁶ moves most of the work between them,
  and both settings give identical results up to 10¹³ for k = 1, −3, 11.
* The sieve rediscovers 23492890653051 in the window [23492890000000, 23492891000000] and finds no
  hits for k = 1 in [2, 10⁹] or [10¹², 1.002·10¹²].
