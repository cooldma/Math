# Erdős #617 at r = 6 (K₃₇), formalized in standalone Lean 4

**Problem** (Erdős–Gyárfás, 1999; Erdős Problem #617). For every integer $r \ge 3$, in any $r$-coloring of the edges of $K_{r^2+1}$, there exists an $(r+1)$-vertex subset whose induced subgraph misses at least one color.

Equivalently, $K_{r^2+1}$ admits no *balanced* $r$-edge-coloring (one where every $(r+1)$-subset spans at least one edge of each color).

- Known prior baseline: $r = 3, 4$ proved by Erdős–Gyárfás (1999); $r = 5$ ($K_{26}$) proved by Xia–Szeider (2026) via Turán stability + SAT.
- This directory proves **$r = 6$ ($K_{37}$)** via a **purely elementary, SAT-free** argument, together with structural theorems for general $r$ (including an explicit disproof of the Xia–Szeider single-graph relaxation for $r = 7, 9$ and all $r \ge 11$, and a general multi-color obstruction for all $r \ge 4$), fully formalized in standalone Lean 4 with **zero external dependencies** (no Mathlib).

## Provenance

- Developed autonomously using **Gemini 4 Neon on High**.
- **No web searches, no browser visits, and no external repository lookups** were performed during discovery or formalization.
- Prior knowledge was limited to results up to **$r = 5$**; the entire $r = 6$ proof, general-$r$ results, C++ adversarial searches, and 9,144-line Lean 4 formalization were constructed independently from scratch.
- Full research log, dead ends, and audit details are in [`notes.md`](notes.md).

## Lean Statement

[`lean/Erdos617_r6_proof.lean`](lean/Erdos617_r6_proof.lean) proves:

```lean
structure EdgeColoring (n r : Nat) where
  col : Fin n → Fin n → Fin r
  symm : ∀ u v, col u v = col v u

def IsBalanced {r : Nat} (C : EdgeColoring (r * r + 1) r) : Prop :=
  ∀ (c : Fin r) (S : Fin (r * r + 1) → Bool),
    subsetCard S = r + 1 → edgesIn (colorClass C c) S ≥ 1

theorem erdos617_r6 : ∀ C : EdgeColoring (6 * 6 + 1) 6, ¬ IsBalanced C
```

**Additional verified theorems:**
- `Erdos617.single_graph_relaxation_fails_c5` ([`lean/Erdos617.lean`](lean/Erdos617.lean)): for every $r \in \{7, 9\} \cup \{11, 12, \dots\}$, the balanced $C_5$-blowup complement $\overline{C_5[\mathbf{a}]} \sqcup (r-2) K_r$ satisfies the single-graph relaxation on $K_{r^2+1}$.
- `Erdos617.no_2r_plus_1_alpha_le_2` ([`lean/Erdos617.lean`](lean/Erdos617.lean)): for all $r \ge 4$, no color class of a balanced $r$-coloring of $K_{r^2+1}$ contains a $(2r+1)$-subset with $\alpha \le 2$.
- `Erdos617.furedi_stability` ([`lean/Erdos617_r6.lean`](lean/Erdos617_r6.lean)) & `Erdos617.r6_exact_two_partitions` ([`lean/Erdos617_r6_peel.lean`](lean/Erdos617_r6_peel.lean)): Füredi's Turán stability theorem and exact reduction of $r = 6$ Füredi peel partitions to `[7,7,6,6,6,5]` and `[7,6,6,6,6,6]`.

**Verification checks:**
- Standalone Lean 4 `v4.37.0-rc1` (no Mathlib). `lake build` succeeds with 0 errors and 0 warnings.
- Zero `sorry`, `axiom`, `admit`, `native_decide`, `unsafe`, `implemented_by`, or `partial` across all 4 files (9,144 lines total).
- `#print axioms Erdos617.erdos617_r6` reports strictly `[propext, Classical.choice, Quot.sound]` ([`lean/AxiomCheck.lean`](lean/AxiomCheck.lean)).

## Proof Outline (`r = 6`, `K₃₇`)

Let $G = G_c$ be the sparsest color class ($|V| = 37$, $e(G) \le 111$, $\alpha(G) \le 6$). Using the multi-scale Turán-complement bound $2 e(\overline{G}[U]) + 5 k(k+1) \cdot 6 \ge 10 k |U|$ across all subsets $U$:

1. **Andrásfai–Erdős–Sós (`andrasfai_erdos_sos_bipartite`):** Every triangle-free graph on $U$ with $\delta \ge d$ and $5d > 2|U|$ is bipartite.
2. **Lemma 1 (`no_12_alpha_le_2_K6_free`):** Every 12-set with $\alpha \le 2$ contains a $K_6$.
3. **Lemma 2 (`no_19_alpha_le_3`):** No 19-set in $G$ has $\alpha \le 3$.
4. **Lemma 3 (`K6_free_18_edges_ge_54`):** Every $K_6$-free 18-set with $\alpha \le 3$ has $e \ge 54$.
5. **Lemma 4 (`no_25_alpha_le_4_e_le_81`):** No 25-set with $\alpha \le 4$ has $e \le 81$ (peeling at min-degree $6$ forces `crossEdges ≤ 12`, while a 2-matching in $\overline{G}[B]$ + Lemma 1 forces `crossEdges ≥ 14`).
6. **Lemma 5 (`K6_free_24_edges_ge_70`):** Every $K_6$-free 24-set with $\alpha \le 4$ has $e \ge 70$.
7. **Lemma 6 (`exists_sub_card_twoEdges_le`):** Max-degree $\ge 6$ deletion helper.
8. **Lemma 7 (`no_31_alpha_le_5_e_le_96`):** No 31-set with $\alpha \le 5$ has $e \le 96$ (peeling forces `crossEdges ≤ 10`, while a 2-matching + Lemma 2 forces `crossEdges ≥ 12`).
9. **Lemma 8 (`K6_free_30_edges_ge_86`):** Every $K_6$-free 30-set with $\alpha \le 5$ has $e \ge 86$.
10. **Closure (`erdos617_r6`):**
    - Lemmas 6–7 force $G$ to be **6-regular** ($e(G) = 111$).
    - Lemma 8 forces $G$ to contain a clique $K_1 \cong K_6$.
    - For every $K_6$ $K$, its external neighborhood $N(K)$ has size 6, matches $K$ bijectively, and is the unique 6-IS in $V \setminus K$ (`K6_unique_nbr_IS`).
    - No two disjoint $K_6$'s have 0 cross-edges (`no_disjoint_K6_zero_cross`), else Lemma 4 on their 25-vertex complement extends a 5-IS to a 7-IS.
    - Deleting one vertex of $N(K_1)$ and applying Lemma 8 gives a disjoint $K_2$ with a unique cross-edge $u_y y$ to $K_1$.
    - On $R = V \setminus (K_1 \cup K_2)$ ($|R| = 25, e(R) = 70$), $J = N(K_1) \setminus \{y\} = N(K_2) \setminus \{u_y\}$ is the unique 5-IS; deleting one vertex of $J$ and applying Lemma 5 gives a third disjoint $K_3 \subseteq R$ with 0 cross-edges to $K_1$ (any shared vertex with $J$ would have degree $\ge 7$), contradiction.

## Building

```bash
cd lean
lake build
lake env lean AxiomCheck.lean
```

## Directory Layout

- [`lean/`](lean/): Standalone Lean 4 proof (`Erdos617.lean`, `Erdos617_r6.lean`, `Erdos617_r6_peel.lean`, `Erdos617_r6_proof.lean`, `AxiomCheck.lean`, `lakefile.toml`, `lean-toolchain`).
- [`notes.md`](notes.md): Full chronological research log, dead ends, adversarial checks, and audit summary.
- [`search/`](search/): Multi-threaded C++ local search programs used to probe single-graph and subgraph thresholds during Phase 1–5 discovery.
