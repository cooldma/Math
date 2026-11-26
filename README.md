# Math

* [`A000139-parity/`](A000139-parity/): proof, with a Lean 4 formalization, of Peter Bala's OEIS
  conjecture that A000139(n) = 2·(3n)!/((2n+1)!·(n+1)!) is odd iff n is an odd fibbinary number (A022341).
* [`Erdos504-blumenthal/`](Erdos504-blumenthal/): Lean 4 formalization of Blumenthal's problem
  (Erdős #504): every 2^n points in the plane determine an angle of at least π(1 − 1/n), and this
  is sharp (Erdős–Szekeres 1960).
* [`Erdos216-horton/`](Erdos216-horton/): Lean 4 formalization of Horton's theorem (Erdős #216):
  arbitrarily large point sets in general position have no empty convex k-gon for any k ≥ 7.
* [`Erdos617-r6/`](Erdos617-r6/): elementary, SAT-free proof and standalone Lean 4 formalization
  of Erdős Problem #617 at r = 6 (every 6-coloring of E(K₃₇) has a 7-vertex subset missing at
  least one color), plus general-r structural theorems and a disproof of the single-graph
  relaxation for r = 7, 9 and all r ≥ 11.
* [`A006579-ordowski/`](A006579-ordowski/): computer search showing that n = 23492890653051 is the
  smallest counterexample to Ordowski's conjecture that Σ_{k<n} gcd(n,k) ≢ −1 (mod n) for composite n
  (OEIS A006579), and the only one below 10¹⁵.
* [`TriangularDn-2611.25270/`](TriangularDn-2611.25270/): multi-threaded bitset-vectorized C++20
  counterexample search for Conjecture 1.3 of Filipin, Fujita, and Jurasić (arXiv:2611.25270v1) on
  the non-extendibility of triangular D(n)-pairs {n, 2n} with n = 2k² ± k; 549.77 billion pairs
  checked across 5.54 million primes (k ≤ 5 × 10⁷) with 0 counterexamples.
