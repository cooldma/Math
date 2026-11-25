/-
  Erdős Problem #617 — Lean 4 Formalization of Füredi Stability & the r = 6 (K₃₇) Structural Reduction
  Imports `Erdos617` (Theorems A–E). Zero sorry, zero axiom, zero admit, zero native_decide.

  Contents:
  1. Exact Turán edge function `twoTStar m r` and its linear-envelope convexity
     `twoTStar_add_clique : twoTStar m (r + 1) ≤ twoTStar (m - b) r + b * (b - 1)`.
  2. Theorem R1 (`furedi_stability`): Füredi's Turán Stability Theorem (2015) proved from scratch
     in complement form for all `n, r ≥ 1`:
       α(G[S]) ≤ r  →  ∃ part : Fin n → Fin r, m_in(G, S, part) + twoTStar |S| r ≤ twoEdgesIn G S.
  3. Theorem R2 (`sparsest_color_class` & `furedi_overflow_bound`):
     For every `r ≥ 3`, in any balanced `r`-coloring of `K_{r²+1}`, there exists a sparsest color
     class `G` with `edges G ≤ r * (r * r + 1) / 2` and an `r`-partition `part : Fin (r²+1) → Fin r`
     whose part sizes `s_j` satisfy:
       - `m_in ≤ r * (r - 1) / 2`,
       - `∑ (s_j - r) ≤ r / 2` (total overflow above `r`),
       - `∑ (r - s_j) ≤ r / 2 - 1` (total deficit below `r`),
       - `∀ j, r + 1 - r / 2 ≤ s_j ∧ s_j ≤ r + r / 2`,
       - `∀ j, edgesIn G.compl V_j ≥ (r - 1) * (s_j - r)`.
  4. Theorem R3 (`r6_low_degree_card_le_18`, `r6_rigid_K6`, `r6_exact_nine_partitions`):
     Complete structural reduction for `r = 6` (`K₃₇`):
       - `|{v : deg G v ≤ 5}| ≤ 18` and `|{v : deg G v ≥ 6}| ≥ 19`,
       - Any vertex outside a `K₆` in `G` has at most `1` neighbor in that `K₆`,
       - Total missing edges `m_in ≤ 15`, imbalance + cross edges `≤ 15 + m_in ≤ 30`,
       - Every part size satisfies `4 ≤ s_j ≤ 9` with `∑ (s_j - 6) ≤ 3`, reducing `r = 6` to
         the exact 9 sorted 6-partitions of 37:
         (9,6,6,6,6,4), (9,6,6,6,5,5), (8,7,6,6,6,4), (8,7,6,6,5,5), (8,6,6,6,6,5),
         (7,7,7,6,6,4), (7,7,7,6,5,5), (7,7,6,6,6,5), (7,6,6,6,6,6).
-/

import Erdos617

namespace Erdos617

/-! ## Section 1: Exact Turán Function `twoTStar` and Convexity -/

/-- Twice the minimum number of edges in an `m`-vertex graph with independence number `≤ r`. -/
def twoTStar (m r : Nat) : Nat :=
  if r = 0 then 0
  else
    let q := m / r
    let rem := m % r
    rem * ((q + 1) * q) + (r - rem) * (q * (q - 1))

theorem pair_linear_envelope (x k : Nat) :
    x * (x - 1) + k * (k + 1) ≥ 2 * k * x := by
  by_cases hkx : k ≤ x
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkx
    cases d with
    | zero =>
      simp only [Nat.add_zero]
      cases k with
      | zero => simp
      | succ k' =>
        simp only [Nat.add_sub_cancel]
        have : (k' + 1) * k' + (k' + 1) * (k' + 1 + 1) = 2 * (k' + 1) * (k' + 1) := by
          simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
          have : 2 * k' * k' = 2 * (k' * k') := Nat.mul_assoc 2 k' k'
          omega
        omega
    | succ d' =>
      have hsub : k + (d' + 1) - 1 = k + d' := by omega
      rw [hsub]
      have hid : (k + (d' + 1)) * (k + d') + k * (k + 1) =
                 2 * k * (k + (d' + 1)) + (d' + 1) * d' := by
        simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
        have hc : k * d' = d' * k := Nat.mul_comm k d'
        have h2k : 2 * k * k = 2 * (k * k) := Nat.mul_assoc 2 k k
        have h2d : 2 * k * d' = 2 * (k * d') := Nat.mul_assoc 2 k d'
        omega
      omega
  · have hxk : x + 1 ≤ k := by omega
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hxk
    cases x with
    | zero => simp
    | succ x' =>
      simp only [Nat.add_sub_cancel]
      have hid : (x' + 1) * x' + (x' + 1 + 1 + d) * (x' + 1 + 1 + d + 1) =
                 2 * (x' + 1 + 1 + d) * (x' + 1) + (d + 2) * (d + 1) := by
        simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
        have hc : x' * d = d * x' := Nat.mul_comm x' d
        have h2x : 2 * x' * x' = 2 * (x' * x') := Nat.mul_assoc 2 x' x'
        have h2d : 2 * d * x' = 2 * (d * x') := Nat.mul_assoc 2 d x'
        omega
      omega

theorem twoTStar_ge_linear (m r k : Nat) (hr : r ≥ 1) :
    twoTStar m r + k * (k + 1) * r ≥ 2 * k * m := by
  unfold twoTStar
  have hr0 : r ≠ 0 := by omega
  simp only [hr0, ↓reduceIte]
  let q := m / r
  let rem := m % r
  have hrm : rem < r := Nat.mod_lt m (by omega)
  have hdm : rem * (q + 1) + (r - rem) * q = m := by
    have h1 : r * q + rem = m := by
      have := Nat.div_add_mod m r
      dsimp [q, rem]; omega
    have h2 : rem * (q + 1) + (r - rem) * q = r * q + rem := by
      rw [Nat.mul_add, Nat.mul_one]
      have h3 : rem * q + (r - rem) * q = r * q := by
        rw [← Nat.add_mul, Nat.add_sub_of_le (by omega)]
      omega
    omega
  have h1 := pair_linear_envelope (q + 1) k
  simp only [Nat.add_sub_cancel] at h1
  have h2 := pair_linear_envelope q k
  have hm1 : rem * ((q + 1) * q) + rem * (k * (k + 1)) ≥ rem * (2 * k * (q + 1)) := by
    rw [← Nat.mul_add]; exact Nat.mul_le_mul_left rem h1
  have hm2 : (r - rem) * (q * (q - 1)) + (r - rem) * (k * (k + 1)) ≥ (r - rem) * (2 * k * q) := by
    rw [← Nat.mul_add]; exact Nat.mul_le_mul_left (r - rem) h2
  have hkk : rem * (k * (k + 1)) + (r - rem) * (k * (k + 1)) = k * (k + 1) * r := by
    rw [← Nat.add_mul, Nat.add_sub_of_le (by omega), Nat.mul_comm]
  have hrhs : rem * (2 * k * (q + 1)) + (r - rem) * (2 * k * q) = 2 * k * m := by
    have ha : rem * (2 * k * (q + 1)) = 2 * k * (rem * (q + 1)) := by
      rw [← Nat.mul_assoc, Nat.mul_comm rem (2 * k), Nat.mul_assoc]
    have hb : (r - rem) * (2 * k * q) = 2 * k * ((r - rem) * q) := by
      rw [← Nat.mul_assoc, Nat.mul_comm (r - rem) (2 * k), Nat.mul_assoc]
    rw [ha, hb, ← Nat.mul_add, hdm]
  change rem * ((q + 1) * q) + (r - rem) * (q * (q - 1)) + k * (k + 1) * r ≥ 2 * k * m
  omega

theorem twoTStar_eq_linear (m r : Nat) (hr : r ≥ 1) :
    let q := m / r
    twoTStar m r + q * (q + 1) * r = 2 * q * m := by
  intro q
  unfold twoTStar
  have hr0 : r ≠ 0 := by omega
  simp only [hr0, ↓reduceIte]
  let rem := m % r
  have hrm : rem < r := Nat.mod_lt m (by omega)
  have hdm : r * q + rem = m := by
    have := Nat.div_add_mod m r
    dsimp [q, rem]; omega
  change rem * ((q + 1) * q) + (r - rem) * (q * (q - 1)) + q * (q + 1) * r = 2 * q * m
  cases hq : q with
  | zero =>
    simp
  | succ q' =>
    have hsub : q' + 1 - 1 = q' := by omega
    rw [hsub]
    have hrem_add : rem + (r - rem) = r := Nat.add_sub_of_le (by omega)
    rw [hq] at hdm
    rw [← hdm]
    have hleft :
        rem * ((q' + 1 + 1) * (q' + 1)) + (r - rem) * ((q' + 1) * q') + (q' + 1) * (q' + 1 + 1) * r =
        (q' + 1) * (rem * (q' + 2) + (r - rem) * q' + r * (q' + 2)) := by
      have p1 : rem * ((q' + 1 + 1) * (q' + 1)) = (q' + 1) * (rem * (q' + 2)) := by
        rw [Nat.mul_comm (q' + 1 + 1) (q' + 1), ← Nat.mul_assoc, Nat.mul_comm rem (q' + 1), Nat.mul_assoc]
      have p2 : (r - rem) * ((q' + 1) * q') = (q' + 1) * ((r - rem) * q') := by
        rw [← Nat.mul_assoc, Nat.mul_comm (r - rem) (q' + 1), Nat.mul_assoc]
      have p3 : (q' + 1) * (q' + 1 + 1) * r = (q' + 1) * (r * (q' + 2)) := by
        rw [Nat.mul_assoc, Nat.mul_comm (q' + 2) r]
      rw [p1, p2, p3, ← Nat.mul_add, ← Nat.mul_add]
    have hright : 2 * (q' + 1) * (r * (q' + 1) + rem) =
        (q' + 1) * (2 * (r * (q' + 1) + rem)) := by
      rw [Nat.mul_comm 2 (q' + 1), Nat.mul_assoc]
    rw [hleft, hright]
    congr 1
    have hmerge : rem * q' + (r - rem) * q' = r * q' := by
      rw [← Nat.add_mul, hrem_add]
    simp only [Nat.mul_add, Nat.mul_one]
    omega

/-- Convexity step for Füredi's stability theorem:
    `twoTStar m (r + 1) ≤ twoTStar (m - b) r + b * (b - 1)`. -/
theorem twoTStar_add_clique (m b r : Nat) (hr : r ≥ 1) (hb : b ≤ m) :
    twoTStar m (r + 1) ≤ twoTStar (m - b) r + b * (b - 1) := by
  let k := m / (r + 1)
  have heq : twoTStar m (r + 1) + k * (k + 1) * (r + 1) = 2 * k * m := twoTStar_eq_linear m (r + 1) (by omega)
  have h1 := twoTStar_ge_linear (m - b) r k hr
  have h2 := pair_linear_envelope b k
  have hsum : 2 * k * (m - b) + 2 * k * b = 2 * k * m := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hb]
  have hk_add : k * (k + 1) * r + k * (k + 1) = k * (k + 1) * (r + 1) := (Nat.mul_succ _ _).symm
  omega

/-! ## Section 2: Theorem R1 — Füredi's Turán Stability Theorem (2015) -/

/-- Exact edge decomposition of `twoEdgesIn G S` across a partition `S = A ⊔ B`. -/
theorem twoEdgesIn_split {n : Nat} (G : SGraph n) (S q : Fin n → Bool) :
    let B : Fin n → Bool := fun u => S u && q u
    let A : Fin n → Bool := fun u => S u && !q u
    let cross := (((verts n).filter B).map (degIn G A)).sum
    twoEdgesIn G S = twoEdgesIn G A + 2 * cross + twoEdgesIn G B ∧
    (((verts n).filter B).map (degIn G S)).sum = twoEdgesIn G B + cross := by
  intro B A cross
  have hdeg_split : ∀ x : Fin n, degIn G S x = degIn G B x + degIn G A x := by
    intro x; unfold degIn
    have hp := filter_length_partition (verts n) (fun v => S v && G.adj x v) q
    have h1 : ((verts n).filter (fun v => (S v && G.adj x v) && q v)).length =
              ((verts n).filter (fun v => B v && G.adj x v)).length := by
      apply filter_length_eq; intro v _; dsimp [B]; cases S v <;> cases q v <;> cases G.adj x v <;> simp
    have h2 : ((verts n).filter (fun v => (S v && G.adj x v) && !q v)).length =
              ((verts n).filter (fun v => A v && G.adj x v)).length := by
      apply filter_length_eq; intro v _; dsimp [A]; cases S v <;> cases q v <;> cases G.adj x v <;> simp
    omega
  have hBsum : (((verts n).filter B).map (degIn G S)).sum = twoEdgesIn G B + cross := by
    rw [sum_map_eq _ _ (fun x => degIn G B x + degIn G A x) (fun x _ => hdeg_split x), sum_map_add]
    rfl
  refine ⟨?_, hBsum⟩
  have hsym : (((verts n).filter A).map (degIn G B)).sum = cross := by
    dsimp [cross]; unfold degIn
    rw [sum_filter_eq_sum_ite, sum_filter_eq_sum_ite]
    have h1 : ∀ u ∈ verts n,
        (if A u then ((verts n).filter (fun v => B v && G.adj u v)).length else 0) =
        ((verts n).map (fun v => if A u && B v && G.adj u v then 1 else 0)).sum := by
      intro u _
      cases hAu : A u
      · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]; symm; rw [sum_map_const, Nat.mul_zero]
      · simp only [Bool.true_and, ↓reduceIte]; exact length_filter_eq_sum (verts n) _
    have h2 : ∀ u ∈ verts n,
        (if B u then ((verts n).filter (fun v => A v && G.adj u v)).length else 0) =
        ((verts n).map (fun v => if B u && A v && G.adj u v then 1 else 0)).sum := by
      intro u _
      cases hBu : B u
      · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]; symm; rw [sum_map_const, Nat.mul_zero]
      · simp only [Bool.true_and, ↓reduceIte]; exact length_filter_eq_sum (verts n) _
    rw [sum_map_eq (verts n) _ _ h1, sum_map_eq (verts n) _ _ h2, sum_swap (verts n) (verts n)]
    apply sum_map_eq; intro v _
    apply sum_map_eq; intro u _
    rw [G.symm u v]
    cases A u <;> cases B v <;> cases G.adj v u <;> simp
  have hAsum : (((verts n).filter A).map (degIn G S)).sum = cross + twoEdgesIn G A := by
    rw [sum_map_eq _ _ (fun x => degIn G B x + degIn G A x) (fun x _ => hdeg_split x), sum_map_add, hsym]
    rfl
  have hSsplit : twoEdgesIn G S =
      (((verts n).filter B).map (degIn G S)).sum + (((verts n).filter A).map (degIn G S)).sum := by
    unfold twoEdgesIn
    rw [sum_filter_eq_sum_ite, sum_filter_eq_sum_ite, sum_filter_eq_sum_ite, ← sum_map_add]
    apply sum_map_eq; intro u _
    dsimp [B, A]
    by_cases hSu : S u = true
    · by_cases hqu : q u = true
      · simp [hSu, hqu]
      · have hqu' : q u = false := by cases h : q u; rfl; exact absurd h hqu
        simp [hSu, hqu']
    · have hSu' : S u = false := by cases h : S u; rfl; exact absurd h hSu
      simp [hSu']
  omega

/-- **Theorem R1 (Füredi's Turán Stability Theorem, 2015 — Complement Form):**
    If `G` restricted to `S` has `α(G[S]) ≤ r` (`r ≥ 1`), then there exists an `r`-partition
    `part : Fin n → Fin r` whose total missing edges inside the parts satisfy:
      `∑_{j : Fin r} twoEdgesIn G.compl (S ∩ part⁻¹(j)) + twoTStar |S| r ≤ twoEdgesIn G S`. -/
theorem furedi_stability {n : Nat} (G : SGraph n) :
    ∀ r : Nat, r ≥ 1 → ∀ S : Fin n → Bool,
      (∀ I : Fin n → Bool, (∀ v, I v = true → S v = true) → IsIndep G I → subsetCard I ≤ r) →
      ∃ part : Fin n → Fin r,
        ((verts r).map (fun j => twoEdgesIn G.compl (fun v => S v && decide (part v = j)))).sum +
        twoTStar (subsetCard S) r ≤ twoEdgesIn G S := by
  intro r hr
  induction r with
  | zero => omega
  | succ r ih =>
    intro S hα
    cases r with
    | zero =>
      -- Base case r = 1: α(G[S]) ≤ 1 => G[S] is a clique, so twoEdgesIn G.compl S = 0
      refine ⟨fun _ => ⟨0, by omega⟩, ?_⟩
      have h1 : verts 1 = [⟨0, by decide⟩] := by decide
      rw [h1]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      have h0 : twoEdgesIn G.compl (fun v => S v && decide True) = 0 := by
        rw [← isIndep_iff_twoEdgesIn_zero]
        intro u v hu hv
        simp only [Bool.and_eq_true, decide_true] at hu hv
        unfold SGraph.compl
        by_cases huv : u = v
        · subst huv; simp
        · cases hadj : G.adj u v
          · exfalso
            let I : Fin n → Bool := fun x => decide (x = u) || decide (x = v)
            have hIsub : ∀ x, I x = true → S x = true := by
              intro x hx; simp [I] at hx
              rcases hx with rfl | rfl
              · exact hu.1
              · exact hv.1
            have hIind : IsIndep G I := by
              intro a b ha hb; simp [I] at ha hb
              rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
              · exact G.loopless _
              · exact hadj
              · rw [G.symm]; exact hadj
              · exact G.loopless _
            have hIcard : subsetCard I = 2 := by
              unfold subsetCard
              have hp := filter_length_partition (verts n) I (fun x => decide (x = u))
              have ha : ((verts n).filter (fun x => I x && decide (x = u))).length = 1 := by
                have heq : ((verts n).filter (fun x => I x && decide (x = u))).length =
                           ((verts n).filter (fun x => decide (x = u))).length := by
                  apply filter_length_eq; intro x _; by_cases hx : x = u <;> simp [I, hx]
                rw [heq]; exact length_filter_eq_one_of_nodup (verts n) (nodup_verts n) u (mem_verts u)
              have hb : ((verts n).filter (fun x => I x && !decide (x = u))).length = 1 := by
                have heq : ((verts n).filter (fun x => I x && !decide (x = u))).length =
                           ((verts n).filter (fun x => decide (x = v))).length := by
                  apply filter_length_eq; intro x _
                  by_cases hx : x = v
                  · subst hx; simp [I, Ne.symm huv]
                  · by_cases hxu : x = u
                    · subst hxu; simp [I, hx]
                    · simp [I, hx, hxu]
                rw [heq]; exact length_filter_eq_one_of_nodup (verts n) (nodup_verts n) v (mem_verts v)
              omega
            have hle := hα I hIsub hIind
            omega
          · simp [huv, hadj]
      rw [h0, Nat.zero_add]
      have hts : twoTStar (subsetCard S) 1 = subsetCard S * (subsetCard S - 1) := by
        unfold twoTStar; simp [Nat.mod_one]
      rw [hts]
      have hcompl0 : twoEdgesIn G.compl S = 0 := by
        have heq : twoEdgesIn G.compl S = twoEdgesIn G.compl (fun v => S v && decide True) := by
          rw [twoEdgesIn_eq_double_sum, twoEdgesIn_eq_double_sum]
          apply sum_map_eq; intro u _; apply sum_map_eq; intro v _; simp
        rw [heq, h0]
      have hadd := twoEdgesIn_add_compl G S
      omega
    | succ r' =>
      -- Inductive step: r + 1 = (r' + 1) + 1 ≥ 2
      let r1 := r' + 1
      by_cases hS0 : subsetCard S = 0
      · refine ⟨fun _ => ⟨0, by omega⟩, ?_⟩
        have hSfalse : ∀ v : Fin n, S v = false := by
          intro v
          cases hSv : S v
          · rfl
          · exfalso
            have h1 : subsetCard (fun x => decide (x = v)) = 1 := subsetCard_singleton v
            have hle : subsetCard (fun x => decide (x = v)) ≤ subsetCard S := by
              unfold subsetCard
              apply filter_length_le; intro x _ hx; rw [of_decide_eq_true hx]; exact hSv
            omega
        have hts0 : twoTStar 0 (r1 + 1) = 0 := by unfold twoTStar; simp
        rw [hS0, hts0, Nat.add_zero]
        have hz : ∀ j ∈ verts (r1 + 1), twoEdgesIn G.compl (fun v => S v && decide ((⟨0, by omega⟩ : Fin (r1 + 1)) = j)) = 0 := by
          intro j _
          rw [twoEdgesIn_eq_double_sum]
          have h0 : ∀ u ∈ verts n, ((verts n).map (fun v =>
              if (S u && decide ((⟨0, by omega⟩ : Fin (r1 + 1)) = j)) &&
                 (S v && decide ((⟨0, by omega⟩ : Fin (r1 + 1)) = j)) && G.compl.adj u v then 1 else 0)).sum = 0 := by
            intro u _; simp [hSfalse u, sum_map_const]
          rw [sum_map_eq (verts n) _ (fun _ => 0) h0, sum_map_const, Nat.mul_zero]
        rw [sum_map_eq (verts (r1 + 1)) _ (fun _ => 0) hz, sum_map_const, Nat.mul_zero]
        exact Nat.zero_le _
      · have hpos : subsetCard S > 0 := by omega
        obtain ⟨v, hSv, hmin⟩ := exists_min_degIn G S hpos
        let q : Fin n → Bool := fun u => decide (u = v) || G.adj v u
        let B : Fin n → Bool := fun u => S u && q u
        let A : Fin n → Bool := fun u => S u && !q u
        obtain ⟨hcard, hBcard, _⟩ := twoEdgesIn_remove_closedNbr G S v hSv
        change subsetCard S = subsetCard B + subsetCard A at hcard
        change subsetCard B = degIn G S v + 1 at hBcard
        -- α(G[A]) ≤ r1
        have hαA : ∀ I : Fin n → Bool, (∀ u, I u = true → A u = true) → IsIndep G I →
            subsetCard I ≤ r1 := by
          intro I hsub hind
          let I' : Fin n → Bool := fun u => I u || decide (u = v)
          have hvnotI : I v = false := by
            cases hIv : I v
            · rfl
            · have hAv := hsub v hIv; simp [A, q] at hAv
          have hsub' : ∀ u, I' u = true → S u = true := by
            intro u hu; simp [I'] at hu
            rcases hu with hIu | rfl
            · exact (Bool.and_eq_true _ _ |>.mp (hsub u hIu)).1
            · exact hSv
          have hind' : IsIndep G I' := by
            intro a b ha hb; simp [I'] at ha hb
            rcases ha with hIa | rfl <;> rcases hb with hIb | rfl
            · exact hind a b hIa hIb
            · have hAa := hsub a hIa; simp [A, q] at hAa; rw [G.symm]; exact hAa.2.2
            · have hAb := hsub b hIb; simp [A, q] at hAb; exact hAb.2.2
            · exact G.loopless _
          have hcardI' : subsetCard I' = subsetCard I + 1 := by
            unfold subsetCard
            have hp := filter_length_partition (verts n) I' (fun u => decide (u = v))
            have h1 : ((verts n).filter (fun u => I' u && decide (u = v))).length = 1 := by
              have heq : ((verts n).filter (fun u => I' u && decide (u = v))).length =
                         ((verts n).filter (fun u => decide (u = v))).length := by
                apply filter_length_eq; intro u _; by_cases hu : u = v <;> simp [I', hu]
              rw [heq]; exact length_filter_eq_one_of_nodup (verts n) (nodup_verts n) v (mem_verts v)
            have h2 : ((verts n).filter (fun u => I' u && !decide (u = v))).length =
                      ((verts n).filter I).length := by
              apply filter_length_eq; intro u _
              by_cases hu : u = v
              · subst hu; simp [hvnotI]
              · simp [I', hu]
            omega
          have hle := hα I' hsub' hind'
          omega
        obtain ⟨partA, hpartA⟩ := ih (by omega) A hαA
        -- Extend partA on A with B as the last part `r1`
        let part : Fin n → Fin (r1 + 1) := fun u =>
          if A u then ⟨(partA u).val, by omega⟩ else ⟨r1, by omega⟩
        refine ⟨part, ?_⟩
        -- Split the sum over `j : Fin (r1 + 1)` into `j < r1` (which matches A) and `j = r1` (which matches B)
        have hpart_sum :
            ((verts (r1 + 1)).map (fun j => twoEdgesIn G.compl (fun u => S u && decide (part u = j)))).sum =
            ((verts r1).map (fun j => twoEdgesIn G.compl (fun u => A u && decide (partA u = j)))).sum +
            twoEdgesIn G.compl B := by
          -- Split verts (r1 + 1) = (verts r1).map Fin.castSucc ++ [Fin.last r1]
          have hfr : verts (r1 + 1) = (verts r1).map (fun j : Fin r1 => (⟨j.val, by omega⟩ : Fin (r1 + 1))) ++ [⟨r1, by omega⟩] := by
            apply List.ext_getElem
            · simp [length_verts]
            · intro i hi1 hi2
              simp only [verts] at hi1 hi2 ⊢
              by_cases hlt : i < r1
              · rw [List.getElem_append_left (by simp [hlt])]
                simp
              · have heq : i = r1 := by simp at hi1; omega
                subst heq
                rw [List.getElem_append_right (by simp)]
                simp
          rw [hfr, List.map_append, List.sum_append, List.map_map]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
          congr 1
          · apply sum_map_eq; intro j _
            dsimp only [Function.comp]
            rw [twoEdgesIn_eq_double_sum, twoEdgesIn_eq_double_sum]
            apply sum_map_eq; intro u _; apply sum_map_eq; intro w _
            have heq_p : ∀ x : Fin n, (S x && decide (part x = ⟨j.val, by omega⟩)) = (A x && decide (partA x = j)) := by
              intro x
              dsimp [part]
              by_cases hAx : A x = true
              · have hSx : S x = true := (Bool.and_eq_true _ _ |>.mp hAx).1
                simp only [hAx, hSx, ↓reduceIte, Bool.true_and]
                by_cases hp : partA x = j
                · simp [hp]
                · have hne : (⟨(partA x).val, by omega⟩ : Fin (r1 + 1)) ≠ ⟨j.val, by omega⟩ := by
                    intro h
                    have hv : (partA x).val = j.val := congrArg (fun a : Fin (r1 + 1) => a.val) h
                    exact hp (Fin.ext hv)
                  simp [hp, hne]
              · have hAx' : A x = false := by cases h : A x; rfl; exact absurd h hAx
                simp only [hAx', Bool.false_eq_true, ↓reduceIte, Bool.false_and]
                have hne : (⟨r1, by omega⟩ : Fin (r1 + 1)) ≠ ⟨j.val, by omega⟩ := by
                  intro h; have := congrArg Fin.val h; dsimp at this; omega
                simp [hne]
            rw [heq_p u, heq_p w]
          · rw [twoEdgesIn_eq_double_sum, twoEdgesIn_eq_double_sum]
            apply sum_map_eq; intro u _; apply sum_map_eq; intro w _
            have heq_last : ∀ x : Fin n, (S x && decide (part x = ⟨r1, by omega⟩)) = B x := by
              intro x
              dsimp [part]
              by_cases hAx : A x = true
              · simp only [hAx, ↓reduceIte]
                have hne : (⟨(partA x).val, by omega⟩ : Fin (r1 + 1)) ≠ ⟨r1, by omega⟩ := by
                  intro h; have := congrArg Fin.val h; dsimp at this; omega
                rw [decide_eq_false hne, Bool.and_false]
                dsimp [A, B] at hAx ⊢
                cases hSx : S x <;> cases hqx : q x <;> simp_all
              · have hAx' : A x = false := by cases h : A x; rfl; exact absurd h hAx
                simp only [hAx', Bool.false_eq_true, ↓reduceIte, decide_true, Bool.and_true]
                dsimp [A, B] at hAx' ⊢
                cases hSx : S x <;> cases hqx : q x <;> simp_all
            rw [heq_last u, heq_last w]
        rw [hpart_sum]
        -- Key degree bound on B: every u ∈ B has degIn G S u ≥ degIn G S v = subsetCard B - 1
        obtain ⟨hsplit, hBsum⟩ := twoEdgesIn_split G S q
        let cross := (((verts n).filter B).map (degIn G A)).sum
        have hdegB : (((verts n).filter B).map (degIn G S)).sum ≥ subsetCard B * (subsetCard B - 1) := by
          have hle := sum_map_le ((verts n).filter B) (fun _ => degIn G S v) (degIn G S)
            (fun u hu => hmin u (Bool.and_eq_true _ _ |>.mp (List.mem_filter.mp hu).2).1)
          rw [sum_map_const] at hle
          change subsetCard B * degIn G S v ≤ _ at hle
          have hsub : subsetCard B - 1 = degIn G S v := by omega
          rw [hsub]; exact hle
        have hBadd := twoEdgesIn_add_compl G B
        have hcross_ge : cross ≥ twoEdgesIn G.compl B := by
          change (((verts n).filter B).map (degIn G S)).sum = twoEdgesIn G B + cross at hBsum
          omega
        have hGS_ge : twoEdgesIn G S ≥ twoEdgesIn G A + subsetCard B * (subsetCard B - 1) + twoEdgesIn G.compl B := by
          change twoEdgesIn G S = twoEdgesIn G A + 2 * cross + twoEdgesIn G B at hsplit
          omega
        have hconv := twoTStar_add_clique (subsetCard S) (subsetCard B) r1 (by omega) (by omega)
        have hAsub : subsetCard S - subsetCard B = subsetCard A := by omega
        rw [hAsub] at hconv
        dsimp [r1] at hconv hpartA ⊢
        omega

/-! ## Section 3: Theorem R2 — Sparsest Color Class & General-`r` Overflow Bound -/

theorem exists_le_avg {α : Type} (l : List α) (f : α → Nat) (M : Nat)
    (hl : l.length > 0) (hsum : (l.map f).sum ≤ l.length * M) :
    ∃ x ∈ l, f x ≤ M := by
  induction l with
  | nil => simp at hl
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hsum
    by_cases ha : f a ≤ M
    · exact ⟨a, by simp, ha⟩
    · cases rest with
      | nil => simp at hsum; omega
      | cons b bs =>
        have hrest : ((b :: bs).map f).sum ≤ (b :: bs).length * M := by
          have : ((b :: bs).length + 1) * M = (b :: bs).length * M + M := by
            rw [Nat.add_mul, Nat.one_mul]
          omega
        obtain ⟨x, hx, hfx⟩ := ih (by simp) hrest
        exact ⟨x, by simp [hx], hfx⟩

/-- Sum of `twoEdges (colorClass C c)` over all colors `c : Fin r` equals `n * (n - 1)`. -/
theorem sum_all_colorClasses {n r : Nat} (C : EdgeColoring n r) :
    ((verts r).map (fun c => twoEdges (colorClass C c))).sum = n * (n - 1) := by
  have h1 : ∀ c ∈ verts r, twoEdges (colorClass C c) =
      ((verts n).map (fun u => ((verts n).map (fun v =>
        if decide (u ≠ v) && decide (C.col u v = c) then 1 else 0)).sum)).sum := by
    intro c _
    unfold twoEdges
    rw [twoEdgesIn_eq_double_sum]
    apply sum_map_eq; intro u _; apply sum_map_eq; intro v _
    unfold colorClass
    by_cases huv : u = v <;> by_cases hc : C.col u v = c <;> simp [huv, hc]
  rw [sum_map_eq (verts r) _ _ h1, sum_swap (verts r) (verts n)]
  have hrow : ∀ u ∈ verts n,
      ((verts n).map (fun v => ((verts r).map (fun c =>
        if decide (u ≠ v) && decide (C.col u v = c) then 1 else 0)).sum)).sum = n - 1 := by
    intro u _
    have hinner : ∀ v ∈ verts n,
        ((verts r).map (fun c => if decide (u ≠ v) && decide (C.col u v = c) then 1 else 0)).sum =
        if decide (v = u) then 0 else 1 := by
      intro v _
      by_cases huv : v = u
      · subst huv; simp [sum_map_const]
      · have hne : u ≠ v := Ne.symm huv
        have hstep : ((verts r).map (fun c => if decide (u ≠ v) && decide (C.col u v = c) then 1 else 0)).sum =
                     ((verts r).map (fun c => if decide (C.col u v = c) then 1 else 0)).sum := by
          apply sum_map_eq; intro c _; simp [hne]
        rw [hstep, decide_eq_false huv]
        simp only [Bool.false_eq_true, ↓reduceIte]
        have heq : ((verts r).map (fun c => if decide (C.col u v = c) then 1 else 0)).sum =
                   ((verts r).filter (fun c => decide (c = C.col u v))).length := by
          rw [length_filter_eq_sum]
          apply sum_map_eq; intro c _
          by_cases hc : c = C.col u v
          · subst hc; simp
          · simp [hc, Ne.symm hc]
        rw [heq]
        exact length_filter_eq_one_of_nodup (verts r) (nodup_verts r) (C.col u v) (mem_verts _)
    rw [sum_map_eq (verts n) _ _ hinner]
    have hp := filter_length_partition (verts n) (fun _ => true) (fun v => decide (v = u))
    rw [filter_true_eq, length_verts] at hp
    have h1u : ((verts n).filter (fun v => true && decide (v = u))).length = 1 :=
      length_filter_eq_one_of_nodup (verts n) (nodup_verts n) u (mem_verts u)
    have hrest : ((verts n).map (fun v => if decide (v = u) then 0 else 1)).sum =
                 ((verts n).filter (fun v => true && !decide (v = u))).length := by
      rw [length_filter_eq_sum]
      apply sum_map_eq; intro v _
      by_cases hv : v = u <;> simp [hv]
    rw [hrest]; omega
  -- Apply sum_swap on each u's inner sum:
  have hrow' : ∀ u ∈ verts n,
      ((verts r).map (fun c => ((verts n).map (fun v =>
        if decide (u ≠ v) && decide (C.col u v = c) then 1 else 0)).sum)).sum = n - 1 := by
    intro u hu
    rw [← sum_swap (verts n) (verts r)]
    exact hrow u hu
  rw [sum_map_eq (verts n) _ (fun _ => n - 1) hrow', sum_map_const, length_verts]

/-- Every `r`-coloring of `K_{r²+1}` (`r ≥ 1`) has a color class with at most `r*(r²+1)/2` edges. -/
theorem exists_sparsest_colorClass {r : Nat} (hr : r ≥ 1) (C : EdgeColoring (r * r + 1) r) :
    ∃ c : Fin r, edges (colorClass C c) ≤ r * (r * r + 1) / 2 := by
  have hsum := sum_all_colorClasses C
  have hsub : r * r + 1 - 1 = r * r := by omega
  rw [hsub] at hsum
  have hmul : (r * r + 1) * (r * r) = r * (r * (r * r + 1)) := by
    rw [Nat.mul_comm (r * r + 1) (r * r), Nat.mul_assoc r r (r * r + 1)]
  rw [hmul] at hsum
  have hlen : (verts r).length = r := length_verts r
  obtain ⟨c, _, hc⟩ := exists_le_avg (verts r) (fun c => twoEdges (colorClass C c)) (r * (r * r + 1))
    (by omega) (by rw [hlen, hsum]; exact Nat.le_refl _)
  refine ⟨c, ?_⟩
  have h2e := two_mul_edges (colorClass C c)
  omega

/-- Exact Turán minimum on `r² + 1` vertices for `α ≤ r`: `twoTStar (r² + 1) r = r * (r² - r + 2)`. -/
theorem twoTStar_sq_add_one (r : Nat) (hr : r ≥ 2) :
    twoTStar (r * r + 1) r + r * (r - 1) = r * (r * r + 1) := by
  have heq := twoTStar_eq_linear (r * r + 1) r (by omega)
  have hdiv : (r * r + 1) / r = r := by
    have h1 : r * r + 1 = 1 + r * r := Nat.add_comm _ _
    rw [h1, Nat.add_mul_div_left 1 r (by omega)]
    have h1r : 1 / r = 0 := Nat.div_eq_of_lt (by omega)
    omega
  dsimp only at heq
  rw [hdiv] at heq
  have hr_eq : r * (r - 1) + r = r * r := by
    rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
  have h1 : 2 * r * (r * r + 1) = r * (r * r + 1) + r * (r * r + 1) := by
    rw [Nat.mul_comm 2 r, Nat.mul_assoc, Nat.two_mul, Nat.mul_add]
  have h2 : r * (r + 1) * r = r * (r * r + 1) + r * (r - 1) := by
    have ha : r * (r + 1) * r = r * (r * r + r) := by
      rw [Nat.mul_assoc, Nat.mul_comm (r + 1) r, Nat.mul_add, Nat.mul_one]
    rw [ha]
    have hb : r * (r * r + r) = r * (r * r) + r * r := Nat.mul_add _ _ _
    have hc : r * (r * r + 1) = r * (r * r) + r := by rw [Nat.mul_add, Nat.mul_one]
    omega
  omega

/-- **Theorem R2 (Füredi + Multi-Scale Overflow Bound for All `r ≥ 3`):**
    In any balanced `r`-coloring of `K_{r²+1}`, there exists a sparsest color class `c : Fin r`
    and an `r`-partition `part : Fin (r²+1) → Fin r` such that:
    1. `edges (colorClass C c) ≤ r * (r * r + 1) / 2`,
    2. Total missing edges inside parts `m_in ≤ r * (r - 1) / 2`,
    3. Every part `V_j` satisfies `edgesIn (colorClass C c).compl V_j ≥ (r - 1) * (|V_j| - r)`,
    4. Total overflow above `r`: `∑_j (|V_j| - r) ≤ r / 2`,
    5. Every part size lies in `[r + 1 - r / 2, r + r / 2]`. -/
theorem furedi_overflow_bound {r : Nat} (hr : r ≥ 3) (C : EdgeColoring (r * r + 1) r)
    (hbal : IsBalanced C) :
    ∃ (c : Fin r) (part : Fin (r * r + 1) → Fin r),
      let G := colorClass C c
      let partS := fun j : Fin r => (fun v : Fin (r * r + 1) => decide (part v = j))
      let mIn2 := ((verts r).map (fun j => twoEdgesIn G.compl (partS j))).sum
      edges G ≤ r * (r * r + 1) / 2 ∧
      mIn2 ≤ r * (r - 1) ∧
      (∀ j : Fin r, edgesIn G.compl (partS j) ≥ (r - 1) * (subsetCard (partS j) - r)) ∧
      ((verts r).map (fun j => subsetCard (partS j) - r)).sum ≤ r / 2 ∧
      ((verts r).map (fun j => r - subsetCard (partS j))).sum ≤ r / 2 - 1 ∧
      (∀ j : Fin r, r + 1 - r / 2 ≤ subsetCard (partS j) ∧ subsetCard (partS j) ≤ r + r / 2) := by
  obtain ⟨c, hsparse⟩ := exists_sparsest_colorClass (by omega) C
  let G := colorClass C c
  have hα : ∀ I : Fin (r * r + 1) → Bool, (∀ v, I v = true → true = true) →
      IsIndep G I → subsetCard I ≤ r :=
    fun I _ hind => isBalanced_indep_le C hbal c I hind
  obtain ⟨part, hfur⟩ := furedi_stability G r (by omega) (fun _ => true) hα
  rw [subsetCard_true] at hfur
  let partS := fun j : Fin r => (fun v : Fin (r * r + 1) => decide (part v = j))
  let mIn2 := ((verts r).map (fun j => twoEdgesIn G.compl (partS j))).sum
  have hmIn2_eq : ((verts r).map (fun j => twoEdgesIn G.compl (fun v => true && decide (part v = j)))).sum = mIn2 := rfl
  rw [hmIn2_eq] at hfur
  have hts := twoTStar_sq_add_one r (by omega)
  have h2e := two_mul_edges G
  have hmIn2_le : mIn2 ≤ r * (r - 1) := by
    have hG_le : twoEdgesIn G (fun _ => true) ≤ r * (r * r + 1) := by
      change twoEdges G ≤ _
      dsimp [G] at h2e ⊢
      omega
    omega
  -- Per-part lower bound from Theorem C at k = 1: edgesIn G.compl (partS j) ≥ (r - 1) * (|V_j| - r)
  have hper : ∀ j : Fin r, edgesIn G.compl (partS j) ≥ (r - 1) * (subsetCard (partS j) - r) := by
    intro j
    have hmc := multiscale_turan_complement C hbal c (partS j) 1
    by_cases hgt : subsetCard (partS j) ≥ r
    · have h1 : 2 * (r - 1) * 1 * subsetCard (partS j) =
                (r - 1) * (2 * r) + 2 * ((r - 1) * (subsetCard (partS j) - r)) := by
        have hsub : r + (subsetCard (partS j) - r) = subsetCard (partS j) := Nat.add_sub_of_le hgt
        have hl : 2 * (r - 1) * 1 * subsetCard (partS j) = (r - 1) * (2 * subsetCard (partS j)) := by
          rw [Nat.mul_one, Nat.mul_comm 2 (r - 1), Nat.mul_assoc]
        have hr1 : 2 * ((r - 1) * (subsetCard (partS j) - r)) = (r - 1) * (2 * (subsetCard (partS j) - r)) := by
          rw [← Nat.mul_assoc, Nat.mul_comm 2 (r - 1), Nat.mul_assoc]
        rw [hl, hr1, ← Nat.mul_add]
        congr 1; omega
      have h2 : (r - 1) * (1 * (1 + 1) * r) = (r - 1) * (2 * r) := rfl
      dsimp [G]
      omega
    · have hz : subsetCard (partS j) - r = 0 := by omega
      rw [hz, Nat.mul_zero]; exact Nat.zero_le _
  -- Sum over all j : Fin r => 2 * (r - 1) * ∑ (s_j - r) ≤ mIn2 ≤ r * (r - 1) => ∑ (s_j - r) ≤ r / 2!
  have hover : ((verts r).map (fun j => subsetCard (partS j) - r)).sum ≤ r / 2 := by
    have hsum_lb : ((verts r).map (fun j => 2 * (r - 1) * (subsetCard (partS j) - r))).sum ≤ mIn2 := by
      apply sum_map_le; intro j _
      have hj := hper j
      have h2 := two_mul_edgesIn G.compl (partS j)
      have hm : 2 * (r - 1) * (subsetCard (partS j) - r) = 2 * ((r - 1) * (subsetCard (partS j) - r)) :=
        Nat.mul_assoc _ _ _
      omega
    rw [sum_map_mul_left] at hsum_lb
    have hle : 2 * (r - 1) * ((verts r).map (fun j => subsetCard (partS j) - r)).sum ≤ r * (r - 1) :=
      Nat.le_trans hsum_lb hmIn2_le
    have hcomm : 2 * (r - 1) * ((verts r).map (fun j => subsetCard (partS j) - r)).sum =
                 (2 * ((verts r).map (fun j => subsetCard (partS j) - r)).sum) * (r - 1) := by
      rw [Nat.mul_comm 2 (r - 1), Nat.mul_assoc, Nat.mul_comm (r - 1)]
    rw [hcomm] at hle
    have hcancel := Nat.le_of_mul_le_mul_right hle (by omega : 0 < r - 1)
    omega
  -- Sum of all part sizes equals r² + 1, so ∑ (s_j - r) = ∑ (r - s_j) + 1!
  have hsum_sizes : ((verts r).map (fun j => subsetCard (partS j))).sum = r * r + 1 := by
    have h := subsetCard_partition_fin (fun _ : Fin (r * r + 1) => true) part
    rw [subsetCard_true] at h
    exact h
  have hbal_od : ((verts r).map (fun j => subsetCard (partS j) - r)).sum =
                 ((verts r).map (fun j => r - subsetCard (partS j))).sum + 1 := by
    have haux : ∀ l : List (Fin r),
        (l.map (fun j => subsetCard (partS j))).sum + (l.map (fun j => r - subsetCard (partS j))).sum =
        l.length * r + (l.map (fun j => subsetCard (partS j) - r)).sum := by
      intro l
      induction l with
      | nil => simp
      | cons j rest ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        have h1 : (rest.length + 1) * r = rest.length * r + r := by rw [Nat.add_mul, Nat.one_mul]
        omega
    have h := haux (verts r)
    rw [hsum_sizes, length_verts] at h
    omega
  have hdef : ((verts r).map (fun j => r - subsetCard (partS j))).sum ≤ r / 2 - 1 := by omega
  have hbounds : ∀ j : Fin r, r + 1 - r / 2 ≤ subsetCard (partS j) ∧ subsetCard (partS j) ≤ r + r / 2 := by
    intro j
    have h1 : subsetCard (partS j) - r ≤ ((verts r).map (fun j => subsetCard (partS j) - r)).sum :=
      le_sum_of_mem (List.mem_map.mpr ⟨j, mem_verts j, rfl⟩)
    have h2 : r - subsetCard (partS j) ≤ ((verts r).map (fun j => r - subsetCard (partS j))).sum :=
      le_sum_of_mem (List.mem_map.mpr ⟨j, mem_verts j, rfl⟩)
    omega
  exact ⟨c, part, hsparse, hmIn2_le, hper, hover, hdef, hbounds⟩

/-! ## Section 4: Theorem R3 — Complete `r = 6` (`K₃₇`) Structural Reduction -/

/-- At `r = 6` (`K₃₇`), every color class `G_c` in a balanced 6-coloring has at most 18 vertices
    of degree `≤ 5` (and hence at least 19 vertices of degree `≥ 6`). -/
theorem r6_low_degree_card_le_18 (C : EdgeColoring (6 * 6 + 1) 6)
    (hbal : IsBalanced C) (c : Fin 6) :
    subsetCard (fun v => decide (deg (colorClass C c) v ≤ 5)) ≤ 18 ∧
    subsetCard (fun v => decide (deg (colorClass C c) v ≥ 6)) ≥ 19 := by
  let G := colorClass C c
  let L : Fin (6 * 6 + 1) → Bool := fun v => decide (deg G v ≤ 5)
  have hα3 : ∀ I : Fin (6 * 6 + 1) → Bool, (∀ v, I v = true → L v = true) →
      IsIndep G I → subsetCard I ≤ 3 := by
    intro I hsub hind
    have hlow : ∀ v, I v = true → deg G v ≤ 6 - 1 := fun v hv => of_decide_eq_true (hsub v hv)
    exact low_degree_alpha_bound (r := 6) (by omega) C hbal c I hind hlow
  have ht := turan_linear_envelope G L 3 6 hα3
  rw [two_mul_edgesIn] at ht
  have hub : twoEdgesIn G L ≤ 5 * subsetCard L := by
    unfold twoEdgesIn
    have hle := sum_map_le ((verts (6 * 6 + 1)).filter L) (degIn G L) (fun _ => 5)
      (fun u hu => by
        have hLu : deg G u ≤ 5 := of_decide_eq_true (List.mem_filter.mp hu).2
        have hsub : degIn G L u ≤ deg G u := by
          unfold deg degIn
          apply filter_length_le; intro v _ hv
          simp only [Bool.and_eq_true] at hv ⊢
          exact ⟨trivial, hv.2⟩
        omega)
    rw [sum_map_const] at hle
    change _ ≤ subsetCard L * 5 at hle
    omega
  have hL18 : subsetCard L ≤ 18 := by omega
  have hpart : subsetCard L + subsetCard (fun v => decide (deg G v ≥ 6)) = 37 := by
    have hp := filter_length_partition (verts (6 * 6 + 1)) (fun _ => true) L
    rw [filter_true_eq, length_verts] at hp
    have h1 : ((verts (6 * 6 + 1)).filter (fun v => true && L v)).length = subsetCard L := rfl
    have h2 : ((verts (6 * 6 + 1)).filter (fun v => true && !L v)).length =
              subsetCard (fun v => decide (deg G v ≥ 6)) := by
      unfold subsetCard
      apply filter_length_eq; intro v _
      dsimp [L]
      by_cases h : deg G v ≤ 5
      · have h6 : ¬ (deg G v ≥ 6) := by omega
        simp [h, h6]
      · have h6 : deg G v ≥ 6 := by omega
        simp [h, h6]
    omega
  have h18 : subsetCard (fun v => decide (deg (colorClass C c) v ≤ 5)) ≤ 18 := hL18
  have h37 : subsetCard (fun v => decide (deg (colorClass C c) v ≤ 5)) +
             subsetCard (fun v => decide (deg (colorClass C c) v ≥ 6)) = 37 := hpart
  exact ⟨h18, by omega⟩

/-- Rigid `K₆` Lemma at `r = 6`: if `K` is a 6-clique in `G_c` (i.e. `subsetCard K = 6` and
    `edgesIn G_c.compl K = 0`), then every vertex `v ∉ K` has at most `1` neighbor in `K`. -/
theorem r6_rigid_K6 (C : EdgeColoring (6 * 6 + 1) 6) (hbal : IsBalanced C) (c : Fin 6)
    (K : Fin (6 * 6 + 1) → Bool) (hKcard : subsetCard K = 6)
    (hKclq : edgesIn (colorClass C c).compl K = 0)
    (v : Fin (6 * 6 + 1)) (hvnot : K v = false) :
    degIn (colorClass C c) K v ≤ 1 := by
  let G := colorClass C c
  let S : Fin (6 * 6 + 1) → Bool := fun u => K u || decide (u = v)
  have hScard : subsetCard S = 7 := by
    unfold subsetCard
    have hp := filter_length_partition (verts (6 * 6 + 1)) S (fun u => decide (u = v))
    have h1 : ((verts (6 * 6 + 1)).filter (fun u => S u && decide (u = v))).length = 1 := by
      have heq : ((verts (6 * 6 + 1)).filter (fun u => S u && decide (u = v))).length =
                 ((verts (6 * 6 + 1)).filter (fun u => decide (u = v))).length := by
        apply filter_length_eq; intro u _; by_cases hu : u = v <;> simp [S, hu]
      rw [heq]; exact length_filter_eq_one_of_nodup (verts _) (nodup_verts _) v (mem_verts v)
    have h2 : ((verts (6 * 6 + 1)).filter (fun u => S u && !decide (u = v))).length =
              ((verts (6 * 6 + 1)).filter K).length := by
      apply filter_length_eq; intro u _
      by_cases hu : u = v
      · subst hu; simp [hvnot]
      · simp [S, hu]
    unfold subsetCard at hKcard
    omega
  have hcompl_lb := balanced_compl_r_plus_1 C hbal c S hScard
  have hadd := twoEdgesIn_add_compl G S
  rw [hScard] at hadd
  have h2ec := two_mul_edgesIn G.compl S
  -- twoEdgesIn G S = twoEdgesIn G K + 2 * degIn G K v
  obtain ⟨hsplit, _⟩ := twoEdgesIn_split G S (fun u => decide (u = v))
  have hB : ∀ u : Fin (6 * 6 + 1), (S u && decide (u = v)) = decide (u = v) := by
    intro u; by_cases hu : u = v <;> simp [S, hu]
  have hA : ∀ u : Fin (6 * 6 + 1), (S u && !decide (u = v)) = K u := by
    intro u; by_cases hu : u = v
    · subst hu; simp [hvnot]
    · simp [S, hu]
  have hG_A : twoEdgesIn G (fun u => S u && !decide (u = v)) = twoEdgesIn G K := by
    rw [twoEdgesIn_eq_double_sum, twoEdgesIn_eq_double_sum]
    apply sum_map_eq; intro u _; apply sum_map_eq; intro w _; rw [hA u, hA w]
  have hG_B : twoEdgesIn G (fun u => S u && decide (u = v)) = 0 := by
    rw [← isIndep_iff_twoEdgesIn_zero]
    intro a b ha hb
    dsimp only at ha hb
    rw [hB a] at ha; rw [hB b] at hb
    rw [of_decide_eq_true ha, of_decide_eq_true hb]; exact G.loopless v
  have hcross_eq : (((verts (6 * 6 + 1)).filter (fun u => S u && decide (u = v))).map
      (degIn G (fun u => S u && !decide (u = v)))).sum = degIn G K v := by
    have hfilt : (verts (6 * 6 + 1)).filter (fun u => S u && decide (u = v)) = [v] := by
      have hlen : ((verts (6 * 6 + 1)).filter (fun u => S u && decide (u = v))).length = 1 := by
        have heq : ((verts (6 * 6 + 1)).filter (fun u => S u && decide (u = v))).length =
                   ((verts (6 * 6 + 1)).filter (fun u => decide (u = v))).length := by
          apply filter_length_eq; intro u _; rw [hB u]
        rw [heq]; exact length_filter_eq_one_of_nodup (verts _) (nodup_verts _) v (mem_verts v)
      match hm : (verts (6 * 6 + 1)).filter (fun u => S u && decide (u = v)) with
      | [] => simp [hm] at hlen
      | x :: [] =>
        have hx : x ∈ (verts (6 * 6 + 1)).filter (fun u => S u && decide (u = v)) := by rw [hm]; simp
        have hxv := (List.mem_filter.mp hx).2
        rw [hB x] at hxv
        rw [of_decide_eq_true hxv]
      | _ :: _ :: _ => simp [hm] at hlen
    rw [hfilt]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    unfold degIn
    apply filter_length_eq; intro w _; dsimp only; rw [hA w]
  rw [hG_A, hG_B, hcross_eq] at hsplit
  have hKadd := twoEdgesIn_add_compl G K
  have h2K := two_mul_edgesIn G.compl K
  rw [hKcard] at hKadd
  dsimp [G] at hsplit hadd h2ec hKadd h2K
  omega

/-- The exact 9 surviving sorted 6-partitions of 37 under Füredi stability + Theorem C. -/
def validR6Partitions : List (List Nat) :=
  [ [9, 6, 6, 6, 6, 4]
  , [9, 6, 6, 6, 5, 5]
  , [8, 7, 6, 6, 6, 4]
  , [8, 7, 6, 6, 5, 5]
  , [8, 6, 6, 6, 6, 5]
  , [7, 7, 7, 6, 6, 4]
  , [7, 7, 7, 6, 5, 5]
  , [7, 7, 6, 6, 6, 5]
  , [7, 6, 6, 6, 6, 6] ]

/-- Pure arithmetic classification: any descending 6-tuple of `Nat`s summing to 37
    with overflow `∑ (x - 6) ≤ 3` belongs to `validR6Partitions`. -/
theorem classify_6tuple_overflow3 (a b c d e f : Nat)
    (hord : a ≥ b ∧ b ≥ c ∧ c ≥ d ∧ d ≥ e ∧ e ≥ f)
    (hsum : a + b + c + d + e + f = 37)
    (hover : (a - 6) + (b - 6) + (c - 6) + (d - 6) + (e - 6) + (f - 6) ≤ 3) :
    [a, b, c, d, e, f] ∈ validR6Partitions := by
  have ha : a = 9 ∨ a = 8 ∨ a = 7 := by omega
  rcases ha with rfl | rfl | rfl
  · have hbc : b = 6 ∧ c = 6 ∧ d = 6 := by omega
    rcases hbc with ⟨rfl, rfl, rfl⟩
    have hef : (e = 6 ∧ f = 4) ∨ (e = 5 ∧ f = 5) := by omega
    rcases hef with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [validR6Partitions]
  · have hb : b = 7 ∨ b = 6 := by omega
    rcases hb with rfl | rfl
    · have hcd : c = 6 ∧ d = 6 := by omega
      rcases hcd with ⟨rfl, rfl⟩
      have hef : (e = 6 ∧ f = 4) ∨ (e = 5 ∧ f = 5) := by omega
      rcases hef with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [validR6Partitions]
    · have hrest : c = 6 ∧ d = 6 ∧ e = 6 ∧ f = 5 := by omega
      rcases hrest with ⟨rfl, rfl, rfl, rfl⟩
      simp [validR6Partitions]
  · have hb : b = 7 ∨ b = 6 := by omega
    rcases hb with rfl | rfl
    · have hc : c = 7 ∨ c = 6 := by omega
      rcases hc with rfl | rfl
      · have hd : d = 6 := by omega
        have hef : (e = 6 ∧ f = 4) ∨ (e = 5 ∧ f = 5) := by omega
        rcases hef with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [validR6Partitions, hd]
      · have hrest : d = 6 ∧ e = 6 ∧ f = 5 := by omega
        rcases hrest with ⟨rfl, rfl, rfl⟩
        simp [validR6Partitions]
    · have hrest : c = 6 ∧ d = 6 ∧ e = 6 ∧ f = 6 := by omega
      rcases hrest with ⟨rfl, rfl, rfl, rfl⟩
      simp [validR6Partitions]

/-- Simple descending insertion sort on `List Nat`, preserving length, sum, and any mapped sum. -/
def insertDesc (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≥ y then x :: y :: ys else y :: insertDesc x ys

def sortDesc : List Nat → List Nat
  | [] => []
  | x :: xs => insertDesc x (sortDesc xs)

theorem insertDesc_length (x : Nat) (l : List Nat) : (insertDesc x l).length = l.length + 1 := by
  induction l with
  | nil => simp [insertDesc]
  | cons y ys ih => unfold insertDesc; split <;> simp [ih]

theorem sortDesc_length (l : List Nat) : (sortDesc l).length = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [sortDesc, insertDesc_length, ih]

theorem insertDesc_map_sum (f : Nat → Nat) (x : Nat) (l : List Nat) :
    ((insertDesc x l).map f).sum = f x + (l.map f).sum := by
  induction l with
  | nil => simp [insertDesc]
  | cons y ys ih =>
    unfold insertDesc; split
    · simp
    · simp [ih]; omega

theorem sortDesc_map_sum (f : Nat → Nat) (l : List Nat) :
    ((sortDesc l).map f).sum = (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [sortDesc, insertDesc_map_sum, ih]

theorem sortDesc_sum (l : List Nat) : (sortDesc l).sum = l.sum := by
  have h := sortDesc_map_sum id l
  simpa using h

theorem insertDesc_sorted (x : Nat) (l : List Nat) (h : l.Pairwise (· ≥ ·)) :
    (insertDesc x l).Pairwise (· ≥ ·) := by
  induction l with
  | nil => simp [insertDesc]
  | cons y ys ih =>
    rw [List.pairwise_cons] at h
    unfold insertDesc
    split
    · rename_i hxy
      rw [List.pairwise_cons]
      refine ⟨?_, List.pairwise_cons.mpr h⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz'
      · exact hxy
      · exact Nat.le_trans (h.1 z hz') hxy
    · rename_i hxy
      rw [List.pairwise_cons]
      refine ⟨?_, ih h.2⟩
      intro z hz
      have hmem : ∀ w ∈ insertDesc x ys, w = x ∨ w ∈ ys := by
        clear ih h hxy z hz
        induction ys with
        | nil => intro w hw; simp [insertDesc] at hw; exact Or.inl hw
        | cons a as iha =>
          intro w hw; unfold insertDesc at hw; split at hw
          · rcases List.mem_cons.mp hw with rfl | hw'
            · exact Or.inl rfl
            · exact Or.inr hw'
          · rcases List.mem_cons.mp hw with rfl | hw'
            · exact Or.inr (by simp)
            · rcases iha w hw' with rfl | hw''
              · exact Or.inl rfl
              · exact Or.inr (by simp [hw''])
      rcases hmem z hz with rfl | hz'
      · omega
      · exact h.1 z hz'

theorem sortDesc_sorted (l : List Nat) : (sortDesc l).Pairwise (· ≥ ·) := by
  induction l with
  | nil => simp [sortDesc]
  | cons x xs ih => exact insertDesc_sorted x (sortDesc xs) ih

/-- **Theorem R3 (`r6_exact_nine_partitions`):**
    In any balanced 6-coloring of `K₃₇`, there exists a sparsest color class `c : Fin 6`
    and a 6-partition `part : Fin 37 → Fin 6` such that:
    1. `edges (colorClass C c) ≤ 111`,
    2. `|{v : deg (colorClass C c) v ≤ 5}| ≤ 18` and `|{v : deg (colorClass C c) v ≥ 6}| ≥ 19`,
    3. Total missing edges inside parts `m_in ≤ 15` (i.e. `mIn2 ≤ 30`),
    4. Every part `V_j` has `edgesIn G.compl V_j ≥ 5 * (|V_j| - 6)`,
    5. The descending-sorted 6-tuple of part sizes belongs to `validR6Partitions` (9 exact cases!). -/
theorem r6_exact_nine_partitions (C : EdgeColoring (6 * 6 + 1) 6) (hbal : IsBalanced C) :
    ∃ (c : Fin 6) (part : Fin (6 * 6 + 1) → Fin 6),
      let G := colorClass C c
      let partS := fun j : Fin 6 => (fun v : Fin (6 * 6 + 1) => decide (part v = j))
      let sizes := (verts 6).map (fun j => subsetCard (partS j))
      edges G ≤ 111 ∧
      subsetCard (fun v => decide (deg G v ≤ 5)) ≤ 18 ∧
      ((verts 6).map (fun j => twoEdgesIn G.compl (partS j))).sum ≤ 30 ∧
      (∀ j : Fin 6, edgesIn G.compl (partS j) ≥ 5 * (subsetCard (partS j) - 6)) ∧
      sortDesc sizes ∈ validR6Partitions := by
  obtain ⟨c, part, hsparse, hmIn2, hper, hover, _, _⟩ := furedi_overflow_bound (r := 6) (by omega) C hbal
  refine ⟨c, part, hsparse, (r6_low_degree_card_le_18 C hbal c).1, hmIn2, hper, ?_⟩
  let partS := fun j : Fin 6 => (fun v : Fin (6 * 6 + 1) => decide (part v = j))
  let sizes := (verts 6).map (fun j => subsetCard (partS j))
  have hlen : (sortDesc sizes).length = 6 := by
    rw [sortDesc_length]; dsimp [sizes]; simp [length_verts]
  have hsum : (sortDesc sizes).sum = 37 := by
    rw [sortDesc_sum]; dsimp [sizes]
    have h := subsetCard_partition_fin (fun _ : Fin (6 * 6 + 1) => true) part
    rw [subsetCard_true] at h
    exact h
  have hover' : ((sortDesc sizes).map (fun x => x - 6)).sum ≤ 3 := by
    rw [sortDesc_map_sum]; dsimp [sizes]; rw [List.map_map]
    exact hover
  have hpw := sortDesc_sorted sizes
  match hsd : sortDesc sizes with
  | [a, b, c', d, e, f] =>
    rw [hsd] at hsum hover' hpw
    simp only [List.sum_cons, List.sum_nil, Nat.add_zero, List.map_cons, List.map_nil] at hsum hover'
    rw [List.pairwise_cons] at hpw
    have hpw2 := hpw.2; rw [List.pairwise_cons] at hpw2
    have hpw3 := hpw2.2; rw [List.pairwise_cons] at hpw3
    have hpw4 := hpw3.2; rw [List.pairwise_cons] at hpw4
    have hpw5 := hpw4.2; rw [List.pairwise_cons] at hpw5
    exact classify_6tuple_overflow3 a b c' d e f
      ⟨hpw.1 b (by simp), hpw2.1 c' (by simp), hpw3.1 d (by simp), hpw4.1 e (by simp), hpw5.1 f (by simp)⟩
      (by omega) (by omega)
  | [] => simp [hsd] at hlen
  | [_] => simp [hsd] at hlen
  | [_, _] => simp [hsd] at hlen
  | [_, _, _] => simp [hsd] at hlen
  | [_, _, _, _] => simp [hsd] at hlen
  | [_, _, _, _, _] => simp [hsd] at hlen
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => simp [hsd] at hlen

end Erdos617
