# Counterexamples to Conjecture 1.28 of arXiv:2611.32519

**Paper.** S. Mandal and Mohan, *Integral Means of Fibonacci Numbers: Divisibility, Density, and Arithmetic Structure*, arXiv:2611.32519 (24 Nov 2026).

**Definitions.** Let 𝒜 = { n ≥ 2 : n divides F₁ + F₂ + … + Fₙ }.

**Conjecture 1.28.** If m ≥ 5 is odd, then F_m ∉ 𝒜.

The authors checked this for 5 ≤ m ≤ 2·10⁶.

## The conjecture is false

| m | factorisation | digits of m |
|---|---|---|
| 1173933867159082366307 | 743 · 1579991745839949349 | 22 |
| 43751231619735900774341 | 197 · 222087470150943658753 | 23 |

For both values, m is odd and 5 ∤ m. Both cofactors are prime. Primality isn't needed for the counterexample itself, but it is how the numbers were found. For each m:

- m | F_m + 3,
- equivalently, (F_m + 2) mod 4m = 4m − 1,
- hence F_m ∈ 𝒜.

## Why the check is valid

Start from F₁ + … + Fₙ = F_{n+2} − 1. So n ∈ 𝒜 exactly when F_{n+2} ≡ 1 (mod n).

**Lemma** (Lemma 2.18(2) in the paper, re-proved here). For odd m ≥ 5, F_k ≡ 1 (mod F_m) exactly when k mod 4m ∈ {1, 2, 2m−2, 4m−1}.

*Proof.*
1. By the addition formula, F_{m+b} ≡ F_{m+1}·F_b (mod F_m). Let u = F_{m+1}.
2. Cassini's identity with m odd, together with F_{m−1} ≡ F_{m+1} (mod F_m), gives u² ≡ −1. So F_{qm+j} ≡ u^q·F_j.
3. Take 0 ≤ j < m, so that 0 ≤ F_j < F_m. Check each class of q mod 4:
   - q ≡ 0: F_j = 1, so j = 1 or 2.
   - q ≡ 2: F_j = F_m − 1, which is impossible for m ≥ 5.
   - q ≡ 1: F_j ≡ −u ≡ F_{m−2}, so j = m − 2.
   - q ≡ 3: F_j ≡ u ≡ F_{m−1}, so j = m − 1. ∎

Apply the lemma with n = F_m and k = n + 2. Then F_m ∈ 𝒜 exactly when (F_m + 2) mod 4m lies in that set, and F_m mod 4m can be computed in about 75 modular squarings.

## Verification

The residue was confirmed by three independent implementations:

- **C:** GMP fast doubling (`kpsearch.c`, `check_def`).
- **Python:** fast doubling (`verify_hit.py`).
- **Python:** 2×2 matrix powering.

The lemma was also brute-force checked for every odd m ≤ 101 and k < 8m. The full definition was checked by direct summation for small m.

Reproduce:

```bash
python -I verify_hit.py 743*1579991745839949349 197*222087470150943658753
```

## How they were found

**Reduction.** For odd m ≥ 5 (with 5 ∤ m), F_m ∈ 𝒜 ⟺ m | F_m + t, where t = 4 if 3 | m and t = 3 otherwise.

**Exhaustive search (`fibsearch2.c`).** A segmented sieve plus a Montgomery Lucas-V test. It runs at about 0.7 ns per odd m on 20 threads. It was validated against brute force on many offsets t.

**Structured search (`kpsearch.c`).** Write m = k·P with P prime. Lemma 2.19 gives F_{kP} ≡ (P/5)·F_k (mod P), so P must divide F_k ± t.

- For each odd k ≤ 1000, factor F_k ± t (trial division, p−1, Pollard rho, ECM).
- Test each prime factor P modulo k, via the Pisano period π(k).
- This was validated against the exhaustive engine on offsets t = 1, −1, 2, −3, 6, −12.
- The k ≤ 1000 pass took 53 min on 2 threads and produced exactly the two hits above.

## Coverage

- **Exhaustive:** no counterexample with m < 10¹³. See `run1e13.log`.
- **Structured, k ≤ 1000:** 136 of 399 values of k were fully factored (per-k details in `kp1000_factoring.txt`). For those k, every m = k·P with P prime and P ∤ k has been checked.
- **Open:** whether a smaller counterexample exists between 10¹³ and 1.17·10²¹.

## Files

| File | Purpose |
|---|---|
| `verify_hit.py` | Standalone verifier for a candidate m. Pure Python, no dependencies. |
| `kpsearch.c` | Structured search over m = k·P. Factors F_k ± t with its own p−1, rho and ECM routines (GMP). |
| `fibsearch2.c` | Exhaustive segmented-sieve search over odd m. Uses a Montgomery Lucas-V test (OpenMP, AVX2). |
| `naive.c` | Independent brute-force checker, used to validate `fibsearch2`. |
| `ref.py` | Checks the reduction against the definition with exact big integers (m ≤ 1500). |
| `offsets.py` | Counts odd m with m \| F_m + c for small offsets c, as a heuristic sanity check. |
| `run1e13.log` | Summary of the exhaustive run to 10¹³: 0 hits, 6049 s on 18 threads. |
| `kp1000.log`, `kp1000_factoring.txt` | Hits and per-k factoring status for the structured run, k ≤ 1000. |

Build (gcc with OpenMP; GMP needed for `kpsearch`):

```bash
gcc -O3 -march=native -funroll-loops -fopenmp -o fibsearch2 fibsearch2.c
gcc -O3 -march=native -fopenmp -o kpsearch kpsearch.c -lgmp
gcc -O3 -o naive naive.c
```

Example runs:

```bash
./fibsearch2 5 10000000000001 -B 4194304 -ckpt run.ckpt
./kpsearch 3 1000
```
