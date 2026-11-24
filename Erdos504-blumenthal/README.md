# Erdős #504 / JSP-000404: α_{2^n} = π(1 − 1/n), formalized

**Problem** (Blumenthal; Erdős Problem 504). Let α_N be the supremum of all α ∈ [0, π] such that
every set of N points in the plane contains three distinct points x, z, y with ∠xzy ≥ α.
Erdős and Szekeres (1960) proved α_{2^n} = π(1 − 1/n).

**Lean statement.** [`lean/Erdos504Blumenthal/Blumenthal.lean`](lean/Erdos504Blumenthal/Blumenthal.lean) proves the formal-conjectures statement
word for word. `minimaxAngle` is copied verbatim from
`FormalConjectures/ErdosProblems/504.lean`.

```lean
namespace Erdos504
noncomputable def minimaxAngle (N : ℕ) : ℝ :=
  sSup {α : ℝ | α ∈ Set.Icc 0 π ∧
    ∀ S : Finset ℂ, S.card = N →
      ∃ x ∈ S, ∃ z ∈ S, ∃ y ∈ S, x ≠ z ∧ y ≠ z ∧ x ≠ y ∧
        α ≤ EuclideanGeometry.angle x z y}

theorem erdos_504 {n : ℕ} (hn : 3 ≤ n) :
    minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π
```

**Checks.**
* Lean 4 with Mathlib v4.37.0-rc1. `lake build` succeeds.
* The file has no `sorry`, `admit` or `native_decide`.
* `#print axioms Erdos504.erdos_504` reports only `[propext, Classical.choice, Quot.sound]`
  (`lean/AxiomCheck.lean`).
* The file is about 600 lines.

## Proof outline

Write β = π − π/n.

### Lower bound (`Blumenthal.lower`, any n ≥ 2)

Every 2^n points have an angle of at least β. Suppose instead that all angles are < β.

1. **Colouring the pairs.** Fix a direction offset s. For distinct p and q, exactly one of the
   directions of q − p and p − q lies in the half-turn [s, s + π). Orient the pair that way.
   Then colour it by which of the n sectors of width π/n it falls in.
2. **No monochromatic 2-path.** If u→v and v→w have the same colour, then ∠uvw > β
   (`two_path`).
3. **Labels are a bijection.** Label each point by the set of colours on its incoming edges.
   Step 2 forces the labels to be injective (`lab_injOn`). There are 2^n points and 2^n possible
   labels, so the labelling is bijective (`lab_surj`).
4. **Choosing a and u₁.** Take the point a whose label is empty. Rotate s onto a's extreme
   outgoing direction, toward a point u₁.
5. **Finding the large angle.** Rotate s back by π/n and compare with the point whose label is
   {n−1}. Injectivity then forces a to have an outgoing edge in the last sector, toward some
   point u. So ∠u a u₁ ≥ β, a contradiction.

This is a compact variant of the sector/labelling idea and differs from the original papers.

### Upper bound (`Blumenthal.upper`, any n ≥ 2)

For every α > β there is a configuration of 2^n points with all angles < α.

1. **The points.** P(e) = Σ_{m ∈ e} L^{−m} e^{iπm/n} for e ⊆ {0,…,n−1}.
2. **Difference formula.** Suppose e and e′ first differ at index i. Then
   P(e′) − P(e) = L^{−i}(±e^{iπi/n} + η), where |η| ≤ n/L (`decomp`).
3. **Unperturbed angles.** Without the η terms, every angle is at most β (`angle_bv_le`).
   Same first index gives angle 0. Different first indices give |i−j|π/n or π − |i−j|π/n.
4. **Choosing L.** The angle is continuous, and there are only finitely many base pairs
   (`perturb`). So a large enough L keeps all angles < α. The same choice makes P injective.

### Main theorem

The lower bound puts β in the set, so the supremum is ≥ β. The upper bound shows every member
of the set is ≤ β.

## Building

```bash
cd lean
lake exe cache get
lake build
lake env lean AxiomCheck.lean
```

## Credit

The theorem is due to Erdős and Szekeres (1960); this repository contributes the Lean 4
formalization. Problem references: [Erdős Problem #504](https://www.erdosproblems.com/504),
Justin Sun Prize problem JSP-000404.
