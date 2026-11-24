# Parity of OEIS A000139: proof of Bala's conjecture

**Sequence.** A000139: a(n) = 2·(3n)! / ((2n+1)!·(n+1)!) = 2, 1, 2, 6, 22, 91, 408, …
(rooted non-separable planar maps; 2-stack-sortable permutations).

**Conjecture** (Peter Bala, A000139, 24 Jul 2025; the same claim for A007226, 13 Mar 2023):
a(n) is odd iff n is in A022341, the *odd fibbinary numbers* 1, 5, 9, 17, 21, 33, … These are the
odd n whose binary expansion has no two adjacent 1s.

**Status before this work.** Both OEIS entries still list it as "Conjecture" (last edited May 2026),
and no proof is noted. A324964 ("A000139 mod 2") states the equivalence without proof and cites
the 2005 Permutation Patterns problem list, so the fact may be folklore. No written proof was found.

## Proof

Let s(m) be the binary digit sum of m.

1. **Legendre:** v₂(m!) = m − s(m). Since a(n)·(2n+1)!·(n+1)! = 2·(3n)!, and using
   s(2n+1) = s(n)+1, we get
   v₂(a(n)) = s(n) + s(n+1) − s(3n).
   So a(n) is odd ⟺ s(3n) = s(n) + s(n+1).
2. **Subadditivity:** s(x+y) ≤ s(x) + s(y), with equality iff x and y share no 1-bit.
   Proof by induction on x: if both are odd a carry occurs, so the inequality is strict.
3. **Case analysis on n mod 4**, using s(2m) = s(m) and s(2m+1) = s(m)+1:
   * n even: s(n+1) = s(n)+1 and s(3n) ≤ s(n)+s(2n) = 2s(n), so the inequality is strict.
   * n = 4j+3: s(3n) = 1 + s(3j+2), and s(3j+2) ≤ s(j) + s(2j+2) = s(j) + s(j+1),
     while s(n) + s(n+1) = s(j) + 2 + s(j+1). So the inequality is strict.
   * n = 4j+1: the condition becomes s(3j) = s(j) + s(2j). By step 2 this holds iff j and 2j
     share no 1-bit, i.e. iff j has no two adjacent 1s. That is exactly the condition that
     n = 4j+1 is an odd fibbinary number. ∎

**Corollary (A007226).** A007226(n) = (2n+1)·A000139(n) (F. Chapoton's formula on the OEIS page).
Since 2n+1 is odd, Bala's 2023 conjecture for A007226 follows. (This last step relies on that
formula, which links the determinant definition of A007226 to A000139; it is not formalized here.)

## Lean formalization

[`lean/A000139Parity/A000139.lean`](lean/A000139Parity/A000139.lean) (Lean 4.37.0-rc1 + Mathlib) proves

```lean
theorem A000139.A000139_odd_iff (n : ℕ) : Odd (a n) ↔ IsOddFibbinary n
-- a n = 2 * (3n)! / ((2n+1)! * (n+1)!)            (ℕ division, shown to be exact)
-- IsOddFibbinary n = n % 2 = 1 ∧ ∀ i, ¬(n.testBit i ∧ n.testBit (i+1))
```

The file has no `sorry` and no `native_decide`. `#print axioms` reports only
propext, Classical.choice and Quot.sound ([`lean/AxiomCheck.lean`](lean/AxiomCheck.lean)). `lake build` succeeds.
The file's main pieces are:

* `s_add`: digit-sum subadditivity with its equality case.
* `key`: s(3n) = s(n)+s(n+1) ⟺ odd fibbinary.
* `dvd_two_choose` and `a_mul`: the quotient is exact.
* `legendre`: from Mathlib's `Nat.Prime.sub_one_mul_multiplicity_factorial`.

The statement was also checked numerically for n < 3000 before the proof was written
([`check_parity.py`](check_parity.py)).

## Building

```bash
cd lean
lake exe cache get   # download prebuilt Mathlib
lake build
lake env lean AxiomCheck.lean
```
