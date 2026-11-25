# Erdős Problem #617 — Research Log

> **Status:** **Erdős Problem #617 at $r = 6$ ($K_{37}$) is SOLVED and machine-verified in standalone Lean 4 (`Erdos617.erdos617_r6`), with zero SAT, zero `sorry`, zero `native_decide`, and zero warnings.**
>
> **Provenance & Methodology:**
> - Produced autonomously using **Gemini 4 Neon on High**.
> - **No web searches, no browser visits, and no external repository lookups** were performed at any point during the session.
> - Prior problem knowledge was limited to results up to **$r = 5$** ($r = 3, 4$ by Erdős–Gyárfás 1999; $r = 5$ on $K_{26}$ by Xia–Szeider 2026 via Turán stability + SAT). All $r = 6$ structural lemmas, counterexamples for $r \ge 7$ to the single-graph relaxation, C++ adversarial searches, the elementary $r = 6$ proof, and the 9,144-line standalone Lean 4 formalization were derived from scratch.

## Problem Statement
For every integer $r \ge 3$, in any $r$-coloring of $E(K_{r^2+1})$, there exists an $(r+1)$-vertex subset whose induced subgraph misses at least one color.

Equivalently, $K_{r^2+1}$ cannot be edge-partitioned into $r$ graphs $G_1, \dots, G_r$ such that every $(r+1)$-subset spans at least $1$ edge in each $G_c$.

### Standard Single-Graph Relaxation (Xia–Szeider 2026)
Let $n = r^2 + 1$. Note that $\binom{r^2+1}{2} = \frac{r^2(r^2+1)}{2}$ is **always** divisible by $r$ (since $r(r^2+1)$ is always even), so the average edges per color class is the exact integer
$$E_{\mathrm{avg}}(r) = \frac{r(r^2+1)}{2}.$$
Let $M(r) = \binom{r+1}{2} - (r - 1) = \binom{r}{2} + 1$.
In any counterexample $r$-coloring, the sparsest color class $G$ satisfies:
1. $|V(G)| = r^2 + 1$,
2. $|E(G)| \le \frac{r(r^2+1)}{2}$,
3. $\alpha(G) \le r$ (every $(r+1)$-subset spans $\ge 1$ edge),
4. $\max_{|S|=r+1} e(G[S]) \le \binom{r}{2} + 1$.

---

## Phase 1: Computational Investigation at $r = 6$ ($K_{37}$)

Target: Search for $G$ on $n = 37$ vertices with $e(G) \le 111$, $\alpha(G) \le 6$, and $\max_{|S|=7} e(G[S]) \le 16$.

### Structural Observations Used in Search
1. **Turán excess:** $e_{\min}(r) = e(K_{r+1} \sqcup (r-1) K_r) = \frac{r(r^2-r+2)}{2}$, so the edge slack of the sparsest color class over Turán is exactly $E_{\mathrm{avg}}(r) - e_{\min}(r) = \binom{r}{2}$ ($= 15$ for $r=6$).
2. **Rigid $K_r$ constraint:** Since $e(K_r) = \binom{r}{2} = M(r) - 1$, any vertex outside an induced $K_r$ has at most $1$ neighbor inside that $K_r$.
3. **Turán $K_4$-threshold at $r=6$:** Since $\mathrm{ex}(7, K_4) = t(7, 3) = 16 = M(6)$, every $7$-subset with $\ge 17$ edges must contain a $K_4$, and also a vertex of internal degree $\ge 5$. Moreover, any edge $(u, v)$ with $N(u) \cap N(v) = \emptyset$ participates in zero $7$-sets with $\ge 17$ edges.
4. **Disjoint-union reduction $G = H \sqcup (6-k) K_6$:** For $H$ on $6k+1$ vertices, $\alpha(H) \le k$, $e(H) \le 15k + 21$, and $\max_{|S|=7} e(H[S]) \le 16$ automatically implies the full $K_{37}$ conditions (by convexity of $\binom{x}{2}$, any $7$-set crossing components has at most $\binom{6}{2} = 15 < 16$ edges).

### Experiments & Results (20 CPU Threads)
1. **Circulants on $K_{37}$:** Exhaustive check of all $\binom{18}{3} = 816$ 6-regular circulants on $37$ vertices: **0** satisfy $\alpha(G) \le 6$.
2. **`search_r6.cpp` (full recomputation, canonical dense-7 enumeration, self-tested against brute force on 20 random $n=15$ graphs):**
   - $k=2$ ($N=13, \alpha \le 2, E \le 51$): 3.66M steps, no witness, best `ind=7, dense=0`.
   - $k=3$ ($N=19, \alpha \le 3, E \le 66$): 9.28M steps, no witness, best `ind=0, dense=1, dense_ex=5` (single $K_7$).
   - $k=6$ ($N=37, \alpha \le 6, E \le 111$): 0.96M steps, no witness, best `ind=0, dense=3, dense_ex=8`. (Identified bottleneck: `IND_CAP=5000` created flat plateaus for random/K4-free starts.)
3. **`search_r6_v2.cpp` (exact incremental $\Delta\mathrm{ind}$ and $\Delta\mathrm{dense}_7$ with NO cap, self-tested against full recomputation on 100 random flips):**
   - Unconstrained SA (log-scaled energy):
     - $N=19, \alpha \le 3, E \le 66$: 33.8M steps, no witness, crystallized to `ind=0, dense=1, dex=5`.
     - $N=25, \alpha \le 4, E \le 81$: 38.6M steps, no witness, crystallized to `ind=0, dense=1, dex=5`.
     - $N=37, \alpha \le 6, E \le 111$: 10.2M steps, no witness; even random 6-regular and greedy $K_4$-free initializations collapsed to `ind=0, dense=1, dex=5` ($K_7 \sqcup 5 K_6$ plus extra edges).
   - Hard-constrained `dense == 0` ($\max_{|S|=7} e(G[S]) \le 16$ strictly forbidden from breaking, eliminating the $K_7 \sqcup 5K_6$ attractor):
     - $N=19, \alpha \le 3, E \le 66$: 30.4M steps, best `ind = 15`.
     - $N=25, \alpha \le 4, E \le 81$: 26.2M steps, best `ind = 82`.
     - $N=37, \alpha \le 6, E \le 111$: 6.4M steps, best `ind = 2950` (note $82 \times 6^2 = 2952$, showing the search naturally assembled $H_{25} \sqcup 2 K_6$ and still hit a hard floor near $2950$ independent sets).
4. **`search_tf.cpp` (exact search over maximal triangle-free complements $F = \overline{H}$ for $k=2$):**
   - $r=6$ ($n=13$, need $e(F) \ge 27$, $\min_{|S|=7} e(F[S]) \ge 5$): no witness found. Analytically proved $\Delta(F) \le 5$ (if $d_F(v) \ge 6$, $N_F(v)$ is a $6$-IS, forcing every $w \notin N_F(v)$ to have $\ge 5$ neighbors in $N_F(v)$, so $V \setminus N_F(v)$ must be a $7$-IS by triangle-freeness). Best circulant $C_{13}(1,5)$ has $e(F)=26$, $\min e = 4$.
   - $r=8$ ($n=17$, need $e(F) \ge 44$, $\min_{|S|=9} e(F[S]) \ge 7$): no $k=2$ witness found; best non-bipartite had $5$ bad $9$-sets of $6$ edges (including $C_5[4,4,3,3,3]$ with $e=58, \min e = 6$ and $C_{17}(1,3,5)$ with $e=51, \min e = 6$).

### Phase 1 Honest Conclusion
Over 120M+ exact local-search steps across unconstrained, hard-dense, and triangle-free formulations found **no** single-graph witness at $r = 6$ ($K_{37}$), with severe structural rigidity around $K_7 \sqcup 5 K_6$. Local search is not an impossibility proof, so $r=6$ remains a plausible final case where a Xia–Szeider SAT + Turán stability refutation could succeed, whereas $r \ge 7$ behaves completely differently (Phase 2).

---

## Phase 2(a): Disproof of the Standard Single-Graph Relaxation for $r = 7, 9, 10$ and All $r \ge 11$

### Theorem 1 (Explicit Single-Graph Counterexamples)
For every integer $r \in \{7, 9\} \cup \{11, 12, 13, \dots\}$, define the graph $G_r$ on $V = \{0, 1, \dots, r^2\}$ ($r^2 + 1$ vertices) as the disjoint union
$$G_r = H_r \sqcup (r - 2) K_r,$$
where $H_r$ on $\{0, \dots, 2r\}$ is the complement of the balanced $C_5$-blowup $F_r = C_5[a_0, a_1, a_2, a_3, a_4]$ with $A_i = \{v < 2r+1 : v \equiv i \pmod 5\}$ (i.e., $u, v < 2r+1$ are adjacent in $H_r$ iff $u \ne v$ and $(u - v) \bmod 5 \notin \{1, 4\}$).

Then $G_r$ satisfies **every** condition of the Xia–Szeider single-graph relaxation:
1. $|V(G_r)| = (2r + 1) + (r - 2) r = r^2 + 1$.
2. $|E(G_r)| \le \frac{r(r^2+1)}{2}$.
   *Proof:* Let $2r + 1 = 5q + t$ ($0 \le t < 5$). Direct calculation in all 5 residue classes gives $5 e(F_r) \ge (2r+1)^2 - 1 = 4r^2 + 4r$, hence $10 e(F_r) \ge 8r^2 + 8r \ge 5r^2 + 15r = 5r(r+3)$ for all $r \ge 3$. Thus $e(F_r) \ge \frac{r(r+3)}{2}$, which is equivalent to $e(H_r) + (r-2)\binom{r}{2} \le \frac{r(r^2+1)}{2}$.
3. $\alpha(G_r) \le r$.
   *Proof:* Since $C_5$ is triangle-free, $F_r$ is triangle-free, so $\alpha(H_r) = \omega(F_r) \le 2$. Each disjoint $K_r$ contributes at most $1$ vertex to any independent set, so $\alpha(G_r) \le 2 + (r - 2) = r$.
4. $\max_{|S|=r+1} e(G_r[S]) \le \binom{r}{2} + 1$.
   *Proof:*
   - If $S \not\subseteq V(H_r)$, then every component $C_j$ gets $s_j = |S \cap C_j| \le r$ vertices with $\sum s_j = r + 1$. Choosing $j^*$ maximizing $s_j$ gives $a = s_{j^*} \in [1, r]$ and $b = r + 1 - a = \sum_{j \ne j^*} s_j \in [1, r]$, so
     $$2 e(G_r[S]) \le \sum_j s_j(s_j - 1) \le a(a-1) + b(b-1) = r(r-1) - 2(a-1)(b-1) \le r(r-1) = 2\binom{r}{2}.$$
   - If $S \subseteq V(H_r)$, let $x_i = |S \cap A_i|$, so $0 \le x_i \le M := \lceil (2r+1)/5 \rceil$ and $\sum_{i=0}^4 x_i = r+1$. Then $e(H_r[S]) = \binom{r+1}{2} - Q(x)$ where $Q(x) = \sum_{i \in \mathbb{Z}/5\mathbb{Z}} x_i x_{i+1}$.
     For any two strictly interior coordinates $0 < x_i, x_j < M$, shifting $(x_i, x_j) \mapsto (x_i - d_1, x_j + d_1)$ or $(x_i + d_2, x_j - d_2)$ (with $d_1 = \min(x_i, M - x_j) \ge 1, d_2 = \min(M - x_i, x_j) \ge 1$) satisfies $d_2 Q(x^-) + d_1 Q(x^+) \le (d_1 + d_2) Q(x)$ because the quadratic term along $x_i + x_j = \text{const}$ is $-c_{ij} t^2 \le 0$. By induction on the number of interior coordinates, the minimum is attained when at most $1$ coordinate lies in $(0, M)$. Since $2M \le r+1 \le 3M$ (for $r \ge 5$), at least $2$ coordinates equal $M$ and any remaining mass $r+1-2M$ sits at a vertex adjacent in $C_5$ to at least one $M$-part, yielding $Q(x) \ge M(r + 1 - 2M)$.
     Direct verification modulo $5$ shows $M(r + 1 - 2M) \ge r - 1$ for $r \in \{7, 9\}$ and all $r \ge 11$ (in fact $M(r+1-2M) \sim \frac{2}{25} r^2 \gg r - 1$).

### Bonus Witness at $r = 10$
For $r = 10$ ($n = 101$, budget $505$, $M(10) = 46$), the balanced $C_5$-blowup fails by 1 edge ($\min Q = 8 < 9$), but replacing $C_5$ with the Andrásfai graph $\mathrm{And}_3 = C_8(1, 4)$ gives $F = \mathrm{And}_3[3,3,3,3,3,2,2,2]$ on $21$ vertices: triangle-free, $e(F) = 83 \ge 65$, $\min_{|S|=11} e(F[S]) = 9 = r - 1$, yielding $G_{10} = \overline{F} \sqcup 8 K_{10}$ with $e(G_{10}) = 127 + 360 = 487 \le 505$, $\alpha(G_{10}) = 10$, $\max_{|S|=11} e(G_{10}[S]) = 46$.

**Implication:** The Xia–Szeider single-graph reduction **cannot** prove Erdős #617 for $r = 7, 9, 10$ or any $r \ge 11$.

---

## Phase 2(b): Multi-Scale Turán-Complement Hierarchy & Multi-Color Obstruction

Why do the single-graph counterexamples $G_r = \overline{C_5[\mathbf{a}]} \sqcup (r-2) K_r$ fail to extend to a genuine balanced $r$-coloring of $K_{r^2+1}$?

### Theorem A (Exact Linear Envelope of Turán's Theorem — 4-Line Proof)
For any graph $G$ on $n$ vertices with $\alpha(G) \le r$, and every $k \in \mathbb{N}$:
$$2 e(G) + k(k+1) r \ge 2 k n.$$
*Proof:* Induction on $r$. For $r = 0$, $n = 0$. For $r \ge 1, n \ge 1$, pick $v$ of minimum degree $\delta = d(v)$ and set $H = G \setminus N[v]$ ($n - (\delta+1)$ vertices, $\alpha(H) \le r - 1$). Every vertex in $N[v]$ has degree $\ge \delta$ in $G$, so $2(e(G) - e(H)) \ge \sum_{u \in N[v]} d_G(u) \ge \delta(\delta+1)$. Combining with the IH on $H$:
$$2 e(G) + k(k+1) r - 2 k n \ge \delta(\delta+1) - 2k(\delta+1) + k(k+1) = (\delta - k)(\delta - k + 1) \ge 0.$$
Setting $k = \lfloor m / r \rfloor$ recovers the exact Turán number $t^*(m, r)$; at $m = 2r + 1, k = 2$, $e(G) \ge r + 2$.

### Theorem C (Multi-Scale Turán-Complement Bound)
In any balanced $r$-edge-coloring $(G_1, \dots, G_r)$ of $K_{r^2+1}$, for every color $c$, every subset $U \subseteq V(K_{r^2+1})$ of size $m$, and every $k \in \mathbb{N}$:
$$2 e(\overline{G_c}[U]) + (r - 1) k(k+1) r \ge 2 (r - 1) k m.$$
In particular, at $m = 2r + 1, k = 2$:
$$e(\overline{G_c}[U]) \ge (r - 1)(r + 2) = r^2 + r - 2.$$

### Theorem D (Non-Bipartite Mantel Theorem — Elementary Proof)
Every triangle-free, non-bipartite graph $F$ on $n \ge 5$ vertices satisfies $4 e(F) \le (n - 1)^2 + 4$ (so $e(F) \le r^2 + 1$ for $n = 2r + 1$).
*Proof:* Let $C$ be a shortest odd cycle of length $L = 2k + 1 \ge 5$. Minimality of $L$ implies $C$ has no chords ($e(F[C]) = L$) and every $u \notin C$ has at most $2$ neighbors in $C$ (otherwise the $\ge 3$ neighbors split $C$ into arcs of lengths $\ge 2$, at least one odd of length $\le L - 4$, closing with $u$ to a shorter odd cycle of length $\le L - 2$). By Mantel's theorem on $V \setminus C$, $4 e(F[V \setminus C]) \le (n - L)^2$. Summing gives
$$4 e(F) \le 4 L + 8(n - L) + (n - L)^2 = (n - 1)^2 + 4 - (L - 5)(2n - L - 1) \le (n - 1)^2 + 4.$$

### Theorem E (Multi-Color Obstruction: No $(2r+1)$-Subset with $\alpha \le 2$)
For every $r \ge 4$, in any balanced $r$-edge-coloring $(G_1, \dots, G_r)$ of $K_{r^2+1}$:
1. **No color class $G_c$ contains any $(2r+1)$-subset $U$ with $\alpha(G_c[U]) \le 2$.**
   *Proof:* Let $F = \overline{G_c}[U]$. Then $F$ is triangle-free on $2r+1$ vertices with $e(F) \ge r^2 + r - 2$ (Theorem C). For $r \ge 4$, $r^2 + r - 2 > r^2 + 1$, so by Theorem D, $F$ is bipartite. Thus $F$ has an independent set $A$ of size $\ge r + 1$, giving a $K_{r+1}$ in $G_c$, contradicting $e(\overline{G_c}[S]) \ge r - 1 > 0$.
2. **Closed-neighborhood and degree-sum bound on $(r-2)$-independent sets:**
   For every color class $G_c$ and every independent set $I$ of size $r - 2$ in $G_c$, the non-neighborhood $R = V \setminus N_{G_c}[I]$ satisfies $\alpha(G_c[R]) \le 2$, so $|R| \le 2r$, hence
   $$|N_{G_c}[I]| \ge (r - 1)^2 \quad \text{and} \quad \sum_{v \in I} d_{G_c}(v) \ge (r - 2)(r - 1) + 1.$$
3. **Low-degree independence bound:**
   For every color class $G_c$, the set $L_c = \{v \in V : d_{G_c}(v) \le r - 1\}$ satisfies $\alpha(G_c[L_c]) \le r - 3$ (sharper than the naive $\alpha \le r - 2$ from $\omega(G_c) \le r$).

### Dead End Checked Adversarially: Does Theorem E Generalize to $k = 3$?
Tested via `search_k3_ms.cpp`: does the Multi-Scale condition alone rule out a $K_4$-free graph $F$ on $3r+1$ vertices with $e(F) \ge 3r^2 - 3$, $\min_{|S|=r+1} e(F[S]) \ge r - 1$, $\min_{|U|=2r+1} e(F[U]) \ge r^2 + r - 2$?
- **Result at $r = 4$ ($n = 13$): WITNESS FOUND** ($e(F) = 45$, $\min_S = 3$, $\min_U = 18$). Note this graph has $e(\overline{F} \sqcup K_4) = 39 > 34 = E_{\mathrm{avg}}(4)$, so it cannot be the *sparsest* color class, only a non-sparsest one. Thus Theorem E does **not** blindly extend to $k = 3$ without using the sparsest-color edge budget (or deeper multi-color interactions).

---

## Phase 3: Lean 4 Verification (Complete)
All five main theorems have been formalized and machine-checked in standalone Lean 4 (`Erdos617.lean`, Lean v4.37.0-rc1, zero external dependencies, exit code 0, zero warnings, zero `sorry`, zero `axiom`, zero `admit`, zero `native_decide`):

- `Erdos617.turan_linear_envelope` (Theorem A): Exact linear envelope of Turán's theorem `2 * edgesIn G S + k * (k + 1) * r ≥ 2 * k * subsetCard S`.
- `Erdos617.single_graph_relaxation_fails_c5` (Theorem B): For every `r = 7 ∨ r = 9 ∨ r ≥ 11`, `witnessGraph r = complement(C₅[a₀..a₄]) ⊔ (r - 2) K_r` satisfies `SatisfiesSingleGraphRelaxation r (witnessGraph r)`.
- `Erdos617.multiscale_turan_complement` & `Erdos617.multiscale_2r_plus_1` (Theorem C): Multi-scale Turán-complement lower bound on every subset `U` in any balanced `r`-coloring of `K_{r²+1}`.
- `Erdos617.non_bipartite_mantel` (Theorem D): Elementary proof via shortest closed odd walk + Cauchy–Schwarz Mantel that `4 * edgesIn F U ≤ (|U| - 1)² + 4` for triangle-free non-bipartite `F[U]` with `|U| ≥ 5`.
- `Erdos617.no_2r_plus_1_alpha_le_2` (Theorem E1): For all `r ≥ 4`, no color class in a balanced `r`-coloring of `K_{r²+1}` contains a `(2r+1)`-subset with `α ≤ 2` (ruling out every `k = 2` single-graph witness from extending to a balanced `r`-coloring).
- `Erdos617.indep_r_minus_2_bounds` & `Erdos617.low_degree_alpha_bound` (Theorems E2–E3): For all `r ≥ 4`, every `(r-2)`-independent set `I` in any color class satisfies `|N[I]| ≥ (r - 1)²` and `∑_{v ∈ I} deg v ≥ (r - 2)(r - 1) + 1`, hence `α(G_c[{v : deg v ≤ r - 1}]) ≤ r - 3`.

Axiom audit (`#print axioms`) confirmed every theorem depends solely on Lean's standard core axioms `[propext, Classical.choice, Quot.sound]`.


---

## Phase 4: Lean 4 Formalization of the $r = 6$ ($K_{37}$) Structural Reduction

We built two modular Lean 4 files importing `Erdos617` (`Erdos617_r6.lean`, 1,013 lines; `Erdos617_r6_peel.lean`, 1,562 lines), both compiling cleanly under Lean v4.37.0-rc1 with exit code 0, zero warnings, zero `sorry`/`axiom`/`admit`/`native_decide`, and depending strictly on `[propext, Classical.choice, Quot.sound]`.

### 1. Füredi Stability & Initial 9-Partition Reduction (`Erdos617_r6.lean`)
- **`furedi_stability` (Theorem R1):** Complement-form proof of Füredi's Turán Stability Theorem (2015) from scratch for all $n, r \ge 1$:
  $$\alpha(G[S]) \le r \implies \exists \text{part} : \text{Fin } n \to \text{Fin } r,\quad m_{\mathrm{in}}(G, S, \text{part}) + t^*(|S|, r) \le e(G[S]).$$
- **`exists_sparsest_colorClass` & `furedi_overflow_bound` (Theorem R2):** For every $r \ge 3$, in any balanced $r$-coloring of $K_{r^2+1}$, the sparsest color class $G_c$ ($e(G_c) \le \lfloor r(r^2+1)/2 \rfloor$) admits an $r$-partition with $m_{\mathrm{in}} \le \binom{r}{2}$, per-part missing edges $m_j \ge (r - 1)(s_j - r)$, total overflow $\sum (s_j - r) \le \lfloor r/2 \rfloor$, total deficit $\sum (r - s_j) \le \lfloor r/2 \rfloor - 1$, and $r + 1 - \lfloor r/2 \rfloor \le s_j \le r + \lfloor r/2 \rfloor$.
- **`r6_low_degree_card_le_18` & `r6_rigid_K6` (Theorem R3):** At $r = 6$ ($K_{37}$), for every color class $G_c$:
  - $|\{v : d_{G_c}(v) \le 5\}| \le 18$ and $|\{v : d_{G_c}(v) \ge 6\}| \ge 19$ (from `low_degree_alpha_bound` + `turan_linear_envelope` + $e(G_c[L]) \le \frac{5}{2}|L|$).
  - Any vertex outside a complete $K_6 \subseteq G_c$ has at most $1$ neighbor in that $K_6$.
- **`r6_exact_nine_partitions`:** Reduces all 6-partitions of 37 at $r = 6$ to exactly 9 sorted partitions:
  `(9,6,6,6,6,4)`, `(9,6,6,6,5,5)`, `(8,7,6,6,6,4)`, `(8,7,6,6,5,5)`, `(8,6,6,6,6,5)`, `(7,7,7,6,6,4)`, `(7,7,7,6,5,5)`, `(7,7,6,6,6,5)`, `(7,6,6,6,6,6)`.

### 2. Strengthened Füredi Peel & Exact 2-Partition Reduction (`Erdos617_r6_peel.lean`)
Keeping the exact peel order $B_0, \dots, B_{r-1}$ (where at step $j$, $v_j$ achieves minimum degree in $S_j = \bigcup_{i \le j} B_i$ and $B_j = N_{G[S_j]}[v_j]$) avoids discarding the quadratic imbalance $\Delta_{\mathrm{bal}} = \sum_j \binom{s_j}{2} - t^*(|S|, r)$ and yields an **exact** decomposition:
- **`furedi_peel_stability` & `furedi_peel_sparsest` (Theorems P1–P2):**
  For every $r \ge 3$ and balanced $r$-coloring of $K_{r^2+1}$, the sparsest color class $G_c$ admits a Füredi peel with:
  1. Prefix independence: $\alpha(G_c[S_j]) \le j + 1$ for all $j < r$ (so $B_0$ is a clique and $|B_0| + |B_1| \le 2r$ for $r \ge 4$ by Theorem E1).
  2. Prefix minimum degree: $\forall u \in S_j,\; d_{G_c[S_j]}(u) \ge s_j - 1$.
  3. Exact step cross-edges: $e(G_c[A_j, B_j]) = 2 m_j + D_j$, where $D_j = \sum_{u \in B_j} (d_{G_c[S_j]}(u) - (s_j - 1)) \ge 0$.
  4. Exact global identity:
     $$\sum_{j=0}^{r-1} \bigl(s_j(s_j - 1) + 2 m_j + 2 D_j\bigr) = 2 e(G_c) \le r(r^2 + 1), \quad 2 m_j \ge 2(r - 1)(s_j - r).$$
  This strengthens the overflow bound for all even $r \ge 4$ to $\sum_{s_j > r} (s_j - r) \le r/2 - 1$.
- **`r4_unique_partition` (Corollary):** At $r = 4$ ($K_{17}$), immediately forces the unique sorted partition `[5, 4, 4, 4]`.
- **`classify_6tuple_imbalance`:** At $r = 6$ ($K_{37}$), eliminates all **6 tight partitions** (every partition with overflow 3) in one step because $\sum s_j(s_j - 1) + 10 \sum (s_j - 6) \ge 226 > 222$, leaving only 3 partitions: `[8,6,6,6,6,5]`, `[7,7,6,6,6,5]`, `[7,6,6,6,6,6]`.
- **`r6_no_size_8_part` (Theorem P3):** Eliminates `[8, 6, 6, 6, 6, 5]` across **all 30 peel orderings** ($j_8 \in \{0, 1, 2, 3, 4, 5\}$):
  - $j_8 = 0$: $B_0$ is a clique ($m_0 = 0$), contradicting $m_0 \ge 10$.
  - $j_8 = 1$: $|S_1| = s_0 + 8 \ge 13$ with $\alpha(G[S_1]) \le 2$, contradicting `no_2r_plus_1_alpha_le_2`.
  - $j_8 = 5$: $\delta(G) \ge 7 \implies 2 e(G) \ge 259 > 222$.
  - $j_8 \in \{3, 4\}$, or $j_8 = 2$ with $5 \in \{s_0, s_1\}$: aggregate min-degree $7$ on $A_{j_8}$ inside $S_{j_8}$ gives $\sum_{i < j_8} (7 s_i - s_i(s_i - 1)) \le 2(m_{\mathrm{in}} + D_{\mathrm{ex}}) \le 26$, whereas the LHS is $\ge 27$.
  - $j_8 = 2$ with $(s_0, s_1, s_2) = (6, 6, 8)$: min-degree $7$ on $B_1$ inside $S_2$ gives $D_1 + e(B_1, B_2) \ge 12$, while `multiscale_turan_complement` ($k = 2$) on $B_1 \cup B_2$ ($|U| = 14$) gives $2 e(B_1, B_2) + 4 \le 2 m_1 + 2 m_2$, hence $2 m_1 + 2 m_2 + 2 D_1 \ge 28 > 26$, contradiction.
- **`r6_exact_two_partitions` (Theorem P4):** Reduces ALL balanced 6-colorings of $K_{37}$ to **exactly two** sorted Füredi peel partitions for the sparsest color class $G_c$:
  1. **`[7, 7, 6, 6, 6, 5]`** with $m_{\mathrm{in}} + D_{\mathrm{ex}} \le 14$ ($m_{\mathrm{in}} \ge 10$, total slack $\le 4$), or
  2. **`[7, 6, 6, 6, 6, 6]`** with $m_{\mathrm{in}} + D_{\mathrm{ex}} \le 15$ ($m_{\mathrm{in}} \ge 5$, total slack $\le 10$).

### 3. Intermediate Phase 4 Assessment (Resolved in Phase 5)
At the end of Phase 4, the two surviving Füredi peel partitions `[7, 7, 6, 6, 6, 5]` and `[7, 6, 6, 6, 6, 6]` could not be eliminated by global degree/Turán/multi-scale counting alone (for instance, the integer parameter profile `s = (5, 7, 7, 6, 6, 6)`, `m = (0, 5, 5, 0, 0, 0)`, `D = (0, 0, 0, 0, 0, 0)` satisfies every global peel inequality simultaneously). Closing these remaining cases led directly to the local $K_6$-peeling + Andrásfai–Erdős–Sós ladder in Phase 5 below.

### 4. Phase 4 Lean 4 Verification Summary (Intermediate)
| File | Lines | Exit Code | Warnings | Forbidden Tokens | Axioms Used |
|---|---:|---:|---:|---:|---|
| `Erdos617.lean` | 3,530 | 0 | 0 | 0 | `[propext, Classical.choice, Quot.sound]` |
| `Erdos617_r6.lean` | 1,013 | 0 | 0 | 0 | `[propext, Classical.choice, Quot.sound]` |
| `Erdos617_r6_peel.lean` | 1,562 | 0 | 0 | 0 | `[propext, Classical.choice, Quot.sound]` |

---

## Phase 5 — Complete Elementary Proof & Machine-Checked Lean 4 Verification of Erdős Problem #617 at $r = 6$ ($K_{37}$)

**RESULT: SOLVED & MACHINE-VERIFIED IN LEAN 4 (ZERO SAT, ZERO `sorry`, ZERO `native_decide`).**

We discovered a **purely elementary, completely SAT-free proof** of Erdős Problem #617 at $r = 6$ ($K_{37}$), and formalized and machine-checked the entire proof from scratch in standalone Lean 4 (`v4.37.0-rc1`, no Mathlib) in [`lean/Erdos617_r6_proof.lean`](lean/Erdos617_r6_proof.lean).

### 0. Adversarial Threshold Experiments (`search_n19.cpp`, `test_deg6.cpp`)
Before formalizing, we stress-tested the candidate subgraph thresholds with fast multi-threaded C++ local searches:
- `search_n19.cpp`: on $N = 19, \alpha \le 3, \max_{|S|=7} e \le 16$, the existence threshold sits at $e \in \{73, 74\}$ (no witness at $e \le 72$ or $66$).
- `test_deg6.cpp`: verified no witness on $N = 13$ (even unconstrained) and no witness on $N = 19$ with $\delta = 6, e \le 66$.
- `search_r6_v2.cpp` on $N = 25, \alpha \le 4$: witness found at $E = 88$ ($K_6 \sqcup H_{19}$), none at $E \le 85, 83, 81$.

### 1. Key Breakthrough: Recursive Clique-Peeling + Andrásfai–Erdős–Sós Ladder
Combining the **multi-scale Turán-complement hierarchy** (`multiscale_turan_complement`, which exploits $\alpha(G_{c'}) \le 6$ across all $5$ complementary color classes $c' \neq c$) with the sparsest color class budget ($e(G_c) \le 111$) yields a tight, purely elementary bottom-up ladder of $K_6$-freeness and edge lower bounds at $N = 12, 19, 18, 25, 24, 31, 30, 37$:

1. **`andrasfai_erdos_sos_bipartite`:** Every triangle-free graph $F$ on $U$ with minimum degree $\delta(F[U]) \ge d$ and $5d > 2|U|$ is bipartite. (Proof: a shortest odd cycle $C$ of length $L \ge 5$ has no chords and at most $2$ neighbors per outside vertex, yielding $5d \le dL \le 2L + 2(|U| - L) = 2|U|$.)
2. **Lemma 1 (`no_12_alpha_le_2_K6_free`):** Every 12-set $R$ with $\alpha(G[R]) \le 2$ contains a $K_6$. (If $K_6$-free, $F = \overline{G}[R]$ is triangle-free with $\Delta(F) \le 5$; `multiscale_turan_complement` ($k=1$) gives $2e(F) \ge 60 \implies F$ is $5$-regular; $5 \cdot 5 = 25 > 24 = 2 \cdot 12 \implies F$ is bipartite $\implies \alpha(F) \ge 6 \implies K_6 \subseteq G[R]$.)
3. **Lemma 2 (`no_19_alpha_le_3`):** No 19-set $U$ in $G_c$ has $\alpha(G[U]) \le 3$. (Must be $K_6$-free by `no_2r_plus_1_alpha_le_2` on 13 vertices + `extend_indep_with_K6`; `multiscale_turan_complement` ($k=3$) gives $2e(G[U]) \le 132 \implies \delta \le 6$; peeling at a min-degree vertex leaves $\ge 12$ vertices with $\alpha \le 2 \implies K_6$ by Lemma 1.)
4. **Lemma 3 (`K6_free_18_edges_ge_54`):** Every $K_6$-free 18-set $A$ with $\alpha(G[A]) \le 3$ has `twoEdgesIn G A ≥ 108` ($e \ge 54$). (Else $\delta \le 5$, peeling leaves $\ge 12$ vertices with $\alpha \le 2 \implies K_6$.)
5. **Lemma 4 (`no_25_alpha_le_4_e_le_81`):** No 25-set $U$ with $\alpha(G[U]) \le 4$ has `twoEdgesIn G U ≤ 162` ($e \le 81$). ($K_6$-free by Lemma 2; min-degree vertex has $d = 6$ leaving $|B|=7, |A|=18$; Lemma 3 gives $2e(A) \ge 108$, `multiscale` gives $2e(\overline{G}[B]) \ge 10$, forcing `crossEdges G A B ≤ 12`. By `exists_two_matching_in_B`, $\overline{G}[B]$ contains a 2-matching $\{a_1, b_1\}, \{a_2, b_2\}$; each non-edge $\{x, y\} \subseteq B$ has $\le 11$ common non-neighbors in $A$ by Lemma 1, so `crossEdges G A B ≥ 7 + 7 = 14 > 12`, contradiction.)
6. **Lemma 5 (`K6_free_24_edges_ge_70`):** Every $K_6$-free 24-set $A$ with $\alpha(G[A]) \le 4$ has `twoEdgesIn G A ≥ 140` ($e \ge 70$). (Else $\delta \le 5$, cannot be $\le 4$ by Lemma 2, so $d = 5$, $|B_w|=6$, $2e(\overline{G}[B_w]) \ge 2$, leaving 18 vertices with $2e \le 107$, contradicting Lemma 3.)
7. **Lemma 6 (`exists_sub_card_twoEdges_le`):** Max-degree deletion helper: if $|A| = M + t$, $E_2 + 1 > 5|A|$, and $2e(A) \le E_2 + 12t$, repeatedly deleting a vertex of max degree $\ge 6$ yields $A' \subseteq A$ with $|A'| = M$ and $2e(A') \le E_2$.
8. **Lemma 7 (`no_31_alpha_le_5_e_le_96`):** No 31-set $U$ with $\alpha(G[U]) \le 5$ has `twoEdgesIn G U ≤ 192` ($e \le 96$). ($K_6$-free by Lemma 4; $\delta = 6$ by Lemma 6 + Lemma 4; Lemma 5 gives $2e(A) \ge 140$ and `crossEdges G A B ≤ 10`; 2-matching in $\overline{G}[B]$ + Lemma 2 on common non-neighbors forces `crossEdges G A B ≥ 6 + 6 = 12 > 10`, contradiction.)
9. **Lemma 8 (`K6_free_30_edges_ge_86`):** Every $K_6$-free 30-set $A$ with $\alpha(G[A]) \le 5$ has `twoEdgesIn G A ≥ 172` ($e \ge 86$). (Else $\delta = 5$ by Lemma 6 + Lemma 4, leaving 24 vertices with $2e \le 139$, contradicting Lemma 5.)

### 2. Closing $K_{37}$ (`erdos617_r6`)
Let $G = G_c$ be the sparsest color class ($|V| = 37$, $2e(G) \le 222$, $\alpha(G) \le 6$):
- **Step 1 (6-regularity):** If $\delta(G) \le 5$, peeling + Lemma 6 + Lemma 7 contradict $\alpha(G) \le 6$. Thus $\delta(G) \ge 6$ and $2e(G) \le 222 = 37 \cdot 6 \implies G$ is **6-regular** ($2e(G) = 222$).
- **Step 2 (Existence of $K_1 \cong K_6$):** If $G$ is $K_6$-free, peeling any vertex leaves 30 vertices with $\alpha \le 5$ and $2e \le 222 - 42 - 10 = 170 < 172$, contradicting Lemma 8.
- **Step 3 (`K6_unique_nbr_IS`):** For every $K_6$ $K$ in 6-regular $G$, each $u \in K$ has a unique external neighbor, and by `r6_rigid_K6` each $z \notin K$ has $\le 1$ neighbor in $K$. Thus $N(K)$ has size 6, matches $K$ bijectively, and is the **unique** 6-IS in $V \setminus K$ (existence via Lemma 7 on $V \setminus K$, which has 31 vertices and $2e = 180 \le 192$).
- **Step 4 (`no_disjoint_K6_zero_cross`):** No two disjoint $K_6$'s $K_1, K_2$ can have $e(K_1, K_2) = 0$. Otherwise $N(K_1) \subseteq V \setminus K_2 \implies N(K_1) = N(K_2)$; on $R = V \setminus (K_1 \cup K_2)$ ($|R| = 25, 2e(R) = 138 \le 162$), Lemma 4 gives a 5-IS $J$, which misses some $z \in N(K_1) = N(K_2)$; adding the matched neighbors $u_1 \in K_1, u_2 \in K_2$ of $z$ produces a **7-IS**, contradiction.
- **Step 5 (Pair of disjoint $K_6$'s with 1 cross-edge):** Delete one vertex $z_0 \in N(K_1)$ from $V \setminus K_1$ to get $W^*$ ($|W^*| = 30$, $\alpha \le 5$ since $N(K_1)$ was unique, $2e(W^*) = 180 - 10 = 170 < 172$). Lemma 8 produces $K_2 \subseteq W^*$. By Step 4, $e(K_1, K_2) \ge 1$, and since $N(K_1)$ is an IS while $K_2$ is a clique, $K_2 \cap N(K_1) = \{y\}$ is a singleton, giving a unique cross-edge $u_y y$ ($u_y \in K_1, y \in K_2$).
- **Step 6 (Third disjoint $K_6$ with 0 cross-edges to $K_1$):** On $R = V \setminus (K_1 \cup K_2)$ ($|R| = 25, 2e(R) = 140 \le 162$), every 5-IS in $R$ must equal both $J_1 = N(K_1) \setminus \{y\}$ and $J_2 = N(K_2) \setminus \{u_y\}$ (else adding $y$ and the $K_1$-mate of a missed vertex in $J_1$ forms a 7-IS). Lemma 4 gives a 5-IS in $R$, so $J_1 = J_2$ is the unique 5-IS in $R$. Deleting one vertex $z_1 \in J_1 = J_2$ (which has degree $6 - 2 = 4$ in $R$) gives $U_1$ ($|U_1| = 24, \alpha \le 4, 2e(U_1) = 132 < 140$). Lemma 5 produces $K_3 \subseteq U_1 \subseteq R$. Any vertex $w \in K_3 \cap N(K_1)$ would lie in $J_1 = J_2$, giving $\deg_G(w) \ge 5 + 1 + 1 = 7 > 6$, impossible. Hence $e(K_1, K_3) = 0$, contradicting Step 4. $\blacksquare$

### 3. Complete 4-File Lean 4 Verification & Independent Audit Summary
Compiled with standalone Lean `v4.37.0-rc1` (no Mathlib, no external tactics, no SAT oracles).

| File | Lines | Exit Code | Warnings | Forbidden Tokens (`sorry`/`axiom`/`admit`/`native_decide`/`unsafe`/`implemented_by`/`partial`) | Axioms Used |
|---|---:|---:|---:|---:|---|
| `Erdos617.lean` | 3,530 | 0 | 0 | `{}` (0) | `[propext, Classical.choice, Quot.sound]` |
| `Erdos617_r6.lean` | 1,013 | 0 | 0 | `{}` (0) | `[propext, Classical.choice, Quot.sound]` |
| `Erdos617_r6_peel.lean` | 1,562 | 0 | 0 | `{}` (0) | `[propext, Classical.choice, Quot.sound]` |
| `Erdos617_r6_proof.lean` | 3,039 | 0 | 0 | `{}` (0) | `[propext, Classical.choice, Quot.sound]` |
| **Total** | **9,144** | **0** | **0** | **0** | **Standard Lean 4 core only** |

Verified top-level theorem signature (`#check @Erdos617.erdos617_r6`):
```lean
Erdos617.erdos617_r6 : ∀ (C : Erdos617.EdgeColoring (6 * 6 + 1) 6), ¬Erdos617.IsBalanced C
```
where `IsBalanced C` is `∀ (c : Fin 6) (S : Fin (6 * 6 + 1) → Bool), subsetCard S = 6 + 1 → edgesIn (colorClass C c) S ≥ 1`.
`#print axioms Erdos617.erdos617_r6` reports strictly: `[propext, Classical.choice, Quot.sound]`.

