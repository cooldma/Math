# Erdős #216 / JSP-000198: Horton sets have no empty convex 7-gon, formalized

**Problem** (Erdős Problem 216; JSP-000198). Let g(k) be the least number such that any g(k)
points in general position in the plane contain an *empty* convex k-gon, meaning k points in
convex position whose convex hull contains no other point of the set. Does g(k) exist for every k?

**Answer.** No. Horton (1983) built arbitrarily large point sets in general position with no
empty convex 7-gon. So g(k) does not exist for any k ≥ 7.

The known finite values are g(3)=3, g(4)=5, g(5)=10 (Harborth 1978) and g(6)=30
(Heule–Scheucher 2024).

## Lean statement

[`lean/Erdos216Horton/Horton.lean`](lean/Erdos216Horton/Horton.lean) (about 750 lines). No formal-conjectures file exists for #216, so
the definitions are written out explicitly:

```lean
namespace Erdos216
def GeneralPosition (S : Finset (ℝ × ℝ)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → p ≠ r → q ≠ r →
    ¬Collinear ℝ ({p, q, r} : Set (ℝ × ℝ))

def HasEmptyConvexPolygon (k : ℕ) (S : Finset (ℝ × ℝ)) : Prop :=
  ∃ T ⊆ S, T.card = k ∧ ConvexIndependent ℝ ((↑) : ↥(T : Set (ℝ × ℝ)) → ℝ × ℝ) ∧
    ∀ p ∈ S, p ∉ T → p ∉ convexHull ℝ (T : Set (ℝ × ℝ))

theorem horton (N : ℕ) : ∃ S : Finset (ℝ × ℝ), S.card = N ∧ GeneralPosition S ∧
    ¬HasEmptyConvexPolygon 7 S
theorem horton_ge {k : ℕ} (hk : 7 ≤ k) (N : ℕ) : ∃ S, S.card = N ∧ GeneralPosition S ∧
    ¬HasEmptyConvexPolygon k S
theorem no_g_of_ge_seven {k : ℕ} (hk : 7 ≤ k) :
    ¬∃ g : ℕ, ∀ S : Finset (ℝ × ℝ), g ≤ S.card → GeneralPosition S → HasEmptyConvexPolygon k S
theorem erdos_216 : ¬∀ k : ℕ, ∃ g : ℕ, ∀ S : Finset (ℝ × ℝ), S.card = g →
    GeneralPosition S → HasEmptyConvexPolygon k S
```

**Checks.**
* Lean 4 with Mathlib v4.37.0-rc1. `lake build` succeeds.
* The file has no `sorry`, `admit` or `native_decide`.
* `#print axioms` reports only `[propext, Classical.choice, Quot.sound]` for all five theorems
  (`lean/AxiomCheck.lean`).

## Proof outline

The points are (i, f(i)) for i < 2^K. `O f i j k` is the orientation determinant.

1. **Horton sets** (`IsHorton`). f is Horton at level K+1 when three things hold:
   * its even half and its odd half are both Horton at level K;
   * one half lies *deep below* the other (`DB`): every line through two low points passes
     below all high points;
   * every line through two high points passes above all low points.

   Horton sets are closed under f ↦ −f, which swaps the low and high halves, and under adding a
   constant.
2. **Existence** (`exists_horton`). Interleave f with a copy of f shifted up by
   D = (B+1)·8·2^K, where B bounds f.
3. **General position** (`gp`). Three points in the same half reduce to the smaller set. A
   mixed triple has a nonzero orientation by `DB`.
4. **No open 4-cup** (`no_open_cup`). Four points can form a convex chain seen from below with no
   point of the set above the chain. Using A for a low point and B for a high point:
   * `DB` forbids the triple patterns A-B-A, B-B-A and A-B-B;
   * `DB` also forbids two consecutive low points, because the point between them is a high
     point above their chord.

   So all four points are high, and induction applies.
5. **The seven points** (`bad`, `mixed`). Take seven points in convex position with no other
   point of the set inside their hull.
   * If they all lie in one half, induction applies.
   * Otherwise the low ones form a cup, since a right turn would put a low point inside a
     triangle with a high point. Likewise the high ones form a cap.
   * By pigeonhole one half holds at least 4 of the points. Emptiness then makes their
     consecutive chords open, which gives an open 4-cup (or 4-cap, via f ↦ −f) in a smaller
     Horton set. That contradicts step 4.
6. **Geometry** (`tri_mem`, `O_eq_zero_of_collinear`). A positive-orientation triangle contains a
   point via explicit barycentric weights, and collinearity forces the orientation to be zero.
   Together these translate steps 3–5 into `Collinear`, `ConvexIndependent` and `convexHull`.

## Scope

This formalizes the k ≥ 7 part of the question, which settles Erdős #216 as stated (the answer
is no). The finite values g(5)=10 and g(6)=30 are not formalized here. g(6)=30 was verified
separately by the EmptyHexagonLean project (Subercaseaux, Nawrocki, Heule et al.) using a SAT
certificate.

## Building

```bash
cd lean
lake exe cache get
lake build
lake env lean AxiomCheck.lean
```

## Credit

The construction and theorem are due to J. D. Horton, "Sets with no empty convex 7-gons",
Canad. Math. Bull. 26 (1983). This repository contributes the Lean 4 formalization. Problem
references: [Erdős Problem #216](https://www.erdosproblems.com/216), Justin Sun Prize problem
JSP-000198.
