/-
  Erdős Problem #617 — Complete Elementary Lean 4 Proof for r = 6 (K₃₇)
  Imports `Erdos617_r6_peel`. Zero sorry, zero axiom, zero admit, zero native_decide.

  Theorem (`erdos617_r6`):
    For every 6-coloring `C : EdgeColoring (6 * 6 + 1) 6` of the edges of `K₃₇`,
    `¬ IsBalanced C` — i.e., there exists a 7-vertex subset whose induced subgraph misses
    at least one of the 6 colors.

  Proof architecture (100% elementary, zero SAT):
  1. `andrasfai_erdos_sos_bipartite`: Every triangle-free graph `F` on `U` with `5 * δ > 2 * |U|`
     is bipartite (via shortest odd cycle from `Erdos617`).
  2. Lemma 1 (`no_12_alpha_le_2_K6_free`): Every 12-set `R` in any color class with `α(G[R]) ≤ 2`
     contains a `K₆` (otherwise `F = compl(G)[R]` is 5-regular triangle-free on 12 vertices,
     hence bipartite by Andrásfai–Erdős–Sós, giving a `K₆`).
  3. Lemma 2 (`no_19_alpha_le_3`): No 19-set in any color class has `α ≤ 3`.
  4. Lemma 3 (`K6_free_18_edges_ge_54`): Every `K₆`-free 18-set with `α ≤ 3` has `≥ 54` edges.
  5. Lemma 4 (`no_25_alpha_le_4_e_le_81`): No 25-set with `α ≤ 4` has `≤ 81` edges
     (via `no_K6_in_25`, `δ = 6`, Lemma 3, 2-matching in `compl(B')`, and Lemma 1 on `R(x, y)`).
  6. Lemma 5 (`K6_free_24_edges_ge_70`): Every `K₆`-free 24-set with `α ≤ 4` has `≥ 70` edges.
  7. Lemma 6 (`exists_sub_card_edges_le`): Max-degree deletion helper for `δ ≤ 5`.
  8. Lemma 7 (`no_31_alpha_le_5_e_le_96`): No 31-set with `α ≤ 5` has `≤ 96` edges.
  9. Lemma 8 (`K6_free_30_edges_ge_86`): Every `K₆`-free 30-set with `α ≤ 5` has `≥ 86` edges.
  10. Main Theorem (`erdos617_r6`): Sparsest color class `G` (`e(G) ≤ 111`) must be 6-regular
      (by Lemma 7), must contain a `K₆` (by Lemma 8), whose neighborhood `N(K)` is the unique
      6-IS in `V \ K`. Deleting one vertex of `N(K)` forces a disjoint `K₂` (Lemma 8); zero
      cross-edges between two disjoint `K₆`'s is impossible (Lemma 4), forcing `e(K₁, K₂) = 1`;
      deleting one vertex of the unique 5-IS `J` in `V \ (K₁ ∪ K₂)` forces a third `K₃` (Lemma 5)
      with `e(K₁, K₃) = 0` (by 6-regularity), contradiction!
-/

import Erdos617_r6_peel

namespace Erdos617

/-! ## Section 1: Andrásfai–Erdős–Sós Bipartiteness & Lemma 1 (12-Vertex `K₆`-Free Obstruction) -/

/-- **Andrásfai–Erdős–Sós (1974) Bipartiteness Theorem:**
    Every triangle-free graph `F` on `U` with minimum degree `d` satisfying `5 * d > 2 * |U|`
    is bipartite on `U`. -/
theorem andrasfai_erdos_sos_bipartite {n : Nat} (F : SGraph n) (U : Fin n → Bool) (d : Nat)
    (htf : IsTriangleFreeOn F U)
    (hmin_deg : ∀ v : Fin n, U v = true → degIn F U v ≥ d)
    (hd : 5 * d > 2 * subsetCard U) :
    IsBipartiteOn F U := by
  apply Classical.byContradiction
  intro hnb
  obtain ⟨L, u0, hLodd, hru0, hmin⟩ := not_bipartite_exists_min_odd_walk F U hnb
  have hLpos : L ≥ 1 := by omega
  obtain ⟨C, hC, hCL⟩ := reach_closed_to_walk hLpos hru0
  have hL5 : L ≥ 5 := by
    have hne1 : L ≠ 1 := by
      intro h1
      have h0 := hC.adj_next 0 (by omega)
      have hm : (0 + 1) % C.length = 0 := by rw [hCL, h1]
      simp only [hm] at h0
      rw [F.loopless] at h0; exact Bool.noConfusion h0
    have hne3 : L ≠ 3 := by
      intro h3
      have h01 := hC.adj_next 0 (by omega)
      have h12 := hC.adj_next 1 (by omega)
      have h20 := hC.adj_next 2 (by omega)
      have m1 : (0 + 1) % C.length = 1 := by rw [hCL, h3]
      have m2 : (1 + 1) % C.length = 2 := by rw [hCL, h3]
      have m0 : (2 + 1) % C.length = 0 := by rw [hCL, h3]
      simp only [m1] at h01; simp only [m2] at h12; simp only [m0] at h20
      have hf := htf (C[0]'(by omega)) (C[1]'(by omega)) (C[2]'(by omega))
        (hC.mem_U _ (List.getElem_mem _)) (hC.mem_U _ (List.getElem_mem _)) (hC.mem_U _ (List.getElem_mem _))
        h01 h12
      rw [F.symm] at h20
      rw [h20] at hf; exact Bool.noConfusion hf
    omega
  have hC_inj : ∀ i j (hi : i < C.length) (hj : j < C.length), C[i]'hi = C[j]'hj → i = j := by
    intro i j hi hj heq
    by_cases hij : i = j
    · exact hij
    · exfalso
      have hlt_case : ∀ a b (ha : a < C.length) (hb : b < C.length), a < b → C[a]'ha = C[b]'hb → False := by
        intro a b ha hb hab hEq
        have hf := hC.reach_arc_fwd ha hb (by omega)
        have hb' := hC.reach_arc_bwd ha hb (by omega)
        rw [← hEq] at hf hb'
        by_cases hodd1 : (b - a) % 2 = 1
        · have := hmin (b - a) (C[a]'ha) hodd1 hf; omega
        · have hodd2 : (C.length - (b - a)) % 2 = 1 := by omega
          have := hmin (C.length - (b - a)) (C[a]'ha) hodd2 hb'; omega
      by_cases hlt : i < j
      · exact hlt_case i j hi hj hlt heq
      · exact hlt_case j i hj hi (by omega) heq.symm
  have hno_chord : ∀ i j (hi : i < C.length) (hj : j < C.length), i < j →
      F.adj (C[i]'hi) (C[j]'hj) = true → j = i + 1 ∨ (i = 0 ∧ j = C.length - 1) := by
    intro i j hi hj hij hadj
    by_cases h1 : j = i + 1
    · exact Or.inl h1
    · by_cases h2 : i = 0 ∧ j = C.length - 1
      · exact Or.inr h2
      · exfalso
        have hr1 : Reach F U (j - i + 1) (C[i]'hi) (C[i]'hi) :=
          (hC.reach_arc_fwd hi hj (by omega)).trans
            (Reach.step (hC.mem_U _ (List.getElem_mem _)) (by rw [F.symm]; exact hadj)
              (Reach.zero (hC.mem_U _ (List.getElem_mem _))))
        have hr2 : Reach F U (C.length - (j - i) + 1) (C[j]'hj) (C[j]'hj) :=
          (hC.reach_arc_bwd hi hj (by omega)).trans
            (Reach.step (hC.mem_U _ (List.getElem_mem _)) hadj
              (Reach.zero (hC.mem_U _ (List.getElem_mem _))))
        by_cases hodd1 : (j - i + 1) % 2 = 1
        · have := hmin (j - i + 1) _ hodd1 hr1; omega
        · have hodd2 : (C.length - (j - i) + 1) % 2 = 1 := by omega
          have := hmin (C.length - (j - i) + 1) _ hodd2 hr2; omega
  have hno_three_nbrs : ∀ u : Fin n, U u = true → u ∉ C →
      ∀ i j k (hi : i < C.length) (hj : j < C.length) (hk : k < C.length),
      i < j → j < k →
      F.adj u (C[i]'hi) = true → F.adj u (C[j]'hj) = true → F.adj u (C[k]'hk) = true → False := by
    intro u hUu _ i j k hi hj hk hij hjk hai haj hak
    have hnot_consec : ∀ a (ha : a < C.length),
        F.adj u (C[a]'ha) = true →
        F.adj u (C[(a + 1) % C.length]'(Nat.mod_lt _ hC.pos)) = true → False := by
      intro a ha h1 h2
      have hnext := hC.adj_next a ha
      have hf := htf u (C[a]'ha) (C[(a + 1) % C.length]'(Nat.mod_lt _ hC.pos))
        hUu (hC.mem_U _ (List.getElem_mem _)) (hC.mem_U _ (List.getElem_mem _)) h1 hnext
      rw [h2] at hf; exact Bool.noConfusion hf
    have hg1 : j - i ≥ 2 := by
      by_cases h : j = i + 1
      · exfalso
        have hm : (i + 1) % C.length = j := by rw [← h]; exact Nat.mod_eq_of_lt (by omega)
        exact hnot_consec i hi hai (by simpa [hm] using haj)
      · omega
    have hg2 : k - j ≥ 2 := by
      by_cases h : k = j + 1
      · exfalso
        have hm : (j + 1) % C.length = k := by rw [← h]; exact Nat.mod_eq_of_lt (by omega)
        exact hnot_consec j hj haj (by simpa [hm] using hak)
      · omega
    have hg3 : C.length - (k - i) ≥ 2 := by
      by_cases h : i = 0 ∧ k = C.length - 1
      · exfalso
        have hm : (k + 1) % C.length = i := by rw [h.1, h.2, Nat.sub_add_cancel hC.pos, Nat.mod_self]
        exact hnot_consec k hk hak (by simpa [hm] using hai)
      · omega
    have hwalk_arc : ∀ d' (a b : Fin n), F.adj u a = true → F.adj u b = true →
        Reach F U d' a b → Reach F U (d' + 2) u u := by
      intro d' a b hua hub hrab
      exact Reach.step hUu hua (hrab.trans (Reach.step hrab.mem_right (by rw [F.symm]; exact hub) (Reach.zero hUu)))
    have hw1 := hwalk_arc (j - i) _ _ hai haj (hC.reach_arc_fwd hi hj (by omega))
    have hw2 := hwalk_arc (k - j) _ _ haj hak (hC.reach_arc_fwd hj hk (by omega))
    have hw3 := hwalk_arc (C.length - (k - i)) _ _ hak hai (hC.reach_arc_bwd hi hk (by omega))
    by_cases o1 : (j - i + 2) % 2 = 1
    · have := hmin _ u o1 hw1; omega
    · by_cases o2 : (k - j + 2) % 2 = 1
      · have := hmin _ u o2 hw2; omega
      · have o3 : (C.length - (k - i) + 2) % 2 = 1 := by omega
        have := hmin _ u o3 hw3; omega
  let inC : Fin n → Bool := fun v => decide (v ∈ C)
  let outC : Fin n → Bool := fun v => U v && !inC v
  have hinC_sub : ∀ v, inC v = true → U v = true := fun v hv => hC.mem_U v (of_decide_eq_true hv)
  have hinC_card : subsetCard inC = L := by
    unfold subsetCard
    have hCnd : C.Nodup := nodup_of_inj_getElem C hC_inj
    have haux : ∀ l : List (Fin n), l.Nodup →
        ((verts n).filter (fun v => decide (v ∈ l))).length = l.length := by
      intro l; induction l with
      | nil => intro _; simp
      | cons x xs ih =>
        intro hnd; rw [List.nodup_cons] at hnd
        have hp := filter_length_partition (verts n) (fun v => decide (v ∈ x :: xs)) (fun v => decide (v = x))
        have h1 : ((verts n).filter (fun v => decide (v ∈ x :: xs) && decide (v = x))).length = 1 := by
          have heq : ((verts n).filter (fun v => decide (v ∈ x :: xs) && decide (v = x))).length =
                     ((verts n).filter (fun v => decide (v = x))).length := by
            apply filter_length_eq; intro v _
            by_cases hv : v = x
            · subst hv; simp
            · simp [hv]
          rw [heq]; exact length_filter_eq_one_of_nodup (verts n) (nodup_verts n) x (mem_verts x)
        have h2 : ((verts n).filter (fun v => decide (v ∈ x :: xs) && !decide (v = x))).length =
                  ((verts n).filter (fun v => decide (v ∈ xs))).length := by
          apply filter_length_eq; intro v _
          by_cases hv : v = x
          · subst hv; simp [hnd.1]
          · simp [hv]
        have hih := ih hnd.2
        simp only [List.length_cons]; omega
    rw [← hCL]; exact haux C hCnd
  have hU_part : subsetCard U = L + subsetCard outC := by
    unfold subsetCard
    have hp := filter_length_partition (verts n) U inC
    have h1 : ((verts n).filter (fun v => U v && inC v)).length = subsetCard inC := by
      unfold subsetCard; apply filter_length_eq; intro v _
      cases h : inC v
      · simp
      · simp [hinC_sub v h]
    rw [h1, hinC_card] at hp; exact hp
  have hcount_inC : ∀ P : Fin n → Bool,
      ((verts n).filter (fun v => inC v && P v)).length =
      ((verts C.length).filter (fun i => P (C[i.val]'i.isLt))).length := by
    intro P
    have haux : ∀ l : List (Fin n), l.Nodup →
        ((verts n).filter (fun v => decide (v ∈ l) && P v)).length = (l.filter P).length := by
      intro l; induction l with
      | nil => intro _; simp
      | cons x xs ih =>
        intro hnd; rw [List.nodup_cons] at hnd
        have hp := filter_length_partition (verts n) (fun v => decide (v ∈ x :: xs) && P v) (fun v => decide (v = x))
        have h2 : ((verts n).filter (fun v => (decide (v ∈ x :: xs) && P v) && !decide (v = x))).length =
                  ((verts n).filter (fun v => decide (v ∈ xs) && P v)).length := by
          apply filter_length_eq; intro v _
          by_cases hv : v = x
          · subst hv; simp [hnd.1]
          · simp [hv]
        have hih := ih hnd.2
        cases hPx : P x
        · have h1 : ((verts n).filter (fun v => (decide (v ∈ x :: xs) && P v) && decide (v = x))).length = 0 := by
            have heq : ((verts n).filter (fun v => (decide (v ∈ x :: xs) && P v) && decide (v = x))).length =
                       ((verts n).filter (fun _ => false)).length := by
              apply filter_length_eq; intro v _
              by_cases hv : v = x
              · subst hv; simp [hPx]
              · simp [hv]
            rw [heq]; simp
          rw [List.filter_cons]; simp only [hPx, Bool.false_eq_true, ↓reduceIte]; omega
        · have h1 : ((verts n).filter (fun v => (decide (v ∈ x :: xs) && P v) && decide (v = x))).length = 1 := by
            have heq : ((verts n).filter (fun v => (decide (v ∈ x :: xs) && P v) && decide (v = x))).length =
                       ((verts n).filter (fun v => decide (v = x))).length := by
              apply filter_length_eq; intro v _
              by_cases hv : v = x
              · subst hv; simp [hPx]
              · simp [hv]
            rw [heq]; exact length_filter_eq_one_of_nodup (verts n) (nodup_verts n) x (mem_verts x)
          rw [List.filter_cons]; simp only [hPx, ↓reduceIte, List.length_cons]; omega
    have hCnd : C.Nodup := nodup_of_inj_getElem C hC_inj
    rw [haux C hCnd]
    have hmap : C = (verts C.length).map (fun i => C[i.val]'i.isLt) := by
      apply List.ext_getElem
      · simp [length_verts]
      · intro i hi1 hi2; simp [verts]
    calc (C.filter P).length
        = (((verts C.length).map (fun i => C[i.val]'i.isLt)).filter P).length := by rw [← hmap]
      _ = ((verts C.length).filter (fun i => P (C[i.val]'i.isLt))).length := by
          rw [List.filter_map, List.length_map]; rfl
  have hdeg_inC : ∀ v : Fin n, inC v = true → degIn F inC v ≤ 2 := by
    intro v hv
    unfold degIn; rw [hcount_inC (fun w => F.adj v w)]
    obtain ⟨i0, hi0, hv_eq⟩ := List.mem_iff_getElem.mp (of_decide_eq_true hv)
    let p1 : Fin C.length := ⟨(i0 + 1) % C.length, Nat.mod_lt _ hC.pos⟩
    let p2 : Fin C.length := ⟨(i0 + C.length - 1) % C.length, Nat.mod_lt _ hC.pos⟩
    have hle := filter_length_le (verts C.length)
      (fun j => F.adj v (C[j.val]'j.isLt))
      (fun j => decide (j = p1) || decide (j = p2))
      (fun j _ hj => by
        rw [← hv_eq] at hj
        by_cases heq : j.val = i0
        · have : C[j.val]'j.isLt = C[i0]'hi0 := by congr 1
          rw [this, F.loopless] at hj; exact Bool.noConfusion hj
        · by_cases hlt : i0 < j.val
          · have hch := hno_chord i0 j.val hi0 j.isLt hlt hj
            rcases hch with hnext | ⟨h0, hlast⟩
            · have : j = p1 := Fin.ext (by dsimp [p1]; rw [← hnext, Nat.mod_eq_of_lt j.isLt])
              simp [this]
            · have : j = p2 := Fin.ext (by dsimp [p2]; rw [h0, hlast, Nat.zero_add, Nat.mod_eq_of_lt (by omega)])
              simp [this]
          · have hgt : j.val < i0 := by omega
            have hj' : F.adj (C[j.val]'j.isLt) (C[i0]'hi0) = true := by rw [F.symm]; exact hj
            have hch := hno_chord j.val i0 j.isLt hi0 hgt hj'
            rcases hch with hnext | ⟨h0, hlast⟩
            · have : j = p2 := Fin.ext (by
                dsimp [p2]
                have : i0 + C.length - 1 = j.val + C.length := by omega
                rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt])
              simp [this]
            · have : j = p1 := Fin.ext (by
                dsimp [p1]
                rw [h0, hlast, Nat.sub_add_cancel hC.pos, Nat.mod_self])
              simp [this])
    have hle2 : ((verts C.length).filter (fun j => decide (j = p1) || decide (j = p2))).length ≤ 2 := by
      have hp := filter_length_partition (verts C.length)
        (fun j => decide (j = p1) || decide (j = p2)) (fun j => decide (j = p1))
      have ha : ((verts C.length).filter (fun j => (decide (j = p1) || decide (j = p2)) && decide (j = p1))).length ≤ 1 := by
        have h := filter_length_le (verts C.length)
          (fun j => (decide (j = p1) || decide (j = p2)) && decide (j = p1))
          (fun j => decide (j = p1))
          (fun j _ hj => (Bool.and_eq_true _ _ |>.mp hj).2)
        rw [length_filter_eq_one_of_nodup (verts C.length) (nodup_verts _) p1 (mem_verts p1)] at h
        exact h
      have hb : ((verts C.length).filter (fun j => (decide (j = p1) || decide (j = p2)) && !decide (j = p1))).length ≤ 1 := by
        have h := filter_length_le (verts C.length)
          (fun j => (decide (j = p1) || decide (j = p2)) && !decide (j = p1))
          (fun j => decide (j = p2))
          (fun j _ hj => by
            simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq] at hj
            rcases hj.1 with h1 | h2
            · exact absurd h1 hj.2
            · exact decide_eq_true h2)
        rw [length_filter_eq_one_of_nodup (verts C.length) (nodup_verts _) p2 (mem_verts p2)] at h
        exact h
      omega
    omega
  have hdeg_outC : ∀ u : Fin n, outC u = true → degIn F inC u ≤ 2 := by
    intro u hu
    have hUu : U u = true := (Bool.and_eq_true _ _ |>.mp hu).1
    have hnotC : u ∉ C := by
      have h2 := (Bool.and_eq_true _ _ |>.mp hu).2; simp [inC] at h2; exact h2
    unfold degIn; rw [hcount_inC (fun w => F.adj u w)]
    by_cases hle2 : ((verts C.length).filter (fun i => F.adj u (C[i.val]'i.isLt))).length ≤ 2
    · exact hle2
    · exfalso
      have hsort : ∀ (l : List (Fin C.length)),
          l.Pairwise (fun a b => a.val < b.val) →
          l.length ≥ 3 →
          ∃ a b c : Fin C.length, a ∈ l ∧ b ∈ l ∧ c ∈ l ∧ a.val < b.val ∧ b.val < c.val := by
        intro l hpw hlen
        match l with
        | [] => simp at hlen
        | [_] => simp at hlen
        | [_, _] => simp at hlen
        | a :: b :: c :: rest =>
          rw [List.pairwise_cons] at hpw
          have hpw2 := hpw.2; rw [List.pairwise_cons] at hpw2
          exact ⟨a, b, c, by simp, by simp, by simp, hpw.1 b (by simp), hpw2.1 c (by simp)⟩
      have hpw_verts : (verts C.length).Pairwise (fun a b => a.val < b.val) := by
        unfold verts; rw [List.pairwise_iff_getElem]; intro i j hi hj hij; simp [hij]
      have hpw_filt := hpw_verts.filter (fun i => F.adj u (C[i.val]'i.isLt))
      obtain ⟨a, b, c, ha, hb, hc, hab, hbc⟩ := hsort _ hpw_filt (by omega)
      exact hno_three_nbrs u hUu hnotC a.val b.val c.val a.isLt b.isLt c.isLt hab hbc
        (List.mem_filter.mp ha).2 (List.mem_filter.mp hb).2 (List.mem_filter.mp hc).2
  -- Key Andrásfai–Erdős–Sós counting:
  -- d * L ≤ crossEdges F inC U = twoEdgesIn F inC + crossEdges F outC inC ≤ 2 * L + 2 * (|U| - L) = 2 * |U|!
  have hdisj : ∀ v, !(inC v && outC v) = true := by
    intro v; by_cases hi : inC v = true <;> simp [outC, hi]
  have hunion : ∀ v, U v = (inC v || outC v) := by
    intro v; dsimp [outC]
    cases hi : inC v
    · simp
    · simp [hinC_sub v hi]
  have hlb : crossEdges F inC U ≥ L * d := by
    rw [← hinC_card]
    exact crossEdges_le_sum_degIn F inC U d (fun u hu => hmin_deg u (hinC_sub u hu))
  have hsplit : crossEdges F inC U = twoEdgesIn F inC + crossEdges F outC inC := by
    rw [crossEdges_congr F (fun _ => rfl) hunion]
    rw [sum_degIn_union_disjoint F inC inC outC hdisj, crossEdges_self, crossEdges_symm F inC outC]
  have h1 : twoEdgesIn F inC ≤ 2 * L := by
    unfold twoEdgesIn
    have hle := sum_map_le ((verts n).filter inC) (degIn F inC) (fun _ => 2)
      (fun v hv => hdeg_inC v (List.mem_filter.mp hv).2)
    rw [sum_map_const] at hle
    change _ ≤ subsetCard inC * 2 at hle
    rw [hinC_card] at hle; omega
  have h2 : crossEdges F outC inC ≤ 2 * subsetCard outC := by
    unfold crossEdges
    have hle := sum_map_le (verts n) (fun u => if outC u then degIn F inC u else 0)
      (fun u => if outC u then 2 else 0) (fun u _ => by
        by_cases hu : outC u = true
        · simp [hu, hdeg_outC u hu]
        · have huf : outC u = false := by cases h : outC u; rfl; exact absurd h hu
          simp [huf])
    have hconst : ((verts n).map (fun u => if outC u then 2 else 0)).sum = 2 * subsetCard outC := by
      have hm : ((verts n).map (fun u => if outC u then 2 else 0)).sum =
                2 * ((verts n).map (fun u => if outC u then 1 else 0)).sum := by
        rw [← sum_map_mul_left]; apply sum_map_eq; intro u _; cases outC u <;> simp
      rw [hm, ← length_filter_eq_sum]; rfl
    omega
  have h5d : 5 * d ≤ L * d := Nat.mul_le_mul_right d hL5
  omega

/-- Predicate: subset `S` contains a complete `K₆` in graph `G`. -/
def HasK6In {n : Nat} (G : SGraph n) (S : Fin n → Bool) : Prop :=
  ∃ K : Fin n → Bool, (∀ v, K v = true → S v = true) ∧ subsetCard K = 6 ∧ edgesIn G.compl K = 0

/-- **Lemma 1 (`no_12_alpha_le_2_K6_free`):**
    In any balanced 6-coloring of `K₃₇`, every 12-vertex subset `R` with `α(G_c[R]) ≤ 2`
    must contain a complete `K₆`. -/
theorem no_12_alpha_le_2_K6_free (C : EdgeColoring (6 * 6 + 1) 6) (hbal : IsBalanced C)
    (c : Fin 6) (R : Fin (6 * 6 + 1) → Bool) (hRcard : subsetCard R = 12)
    (hα2 : ∀ I : Fin (6 * 6 + 1) → Bool, (∀ v, I v = true → R v = true) →
      IsIndep (colorClass C c) I → subsetCard I ≤ 2) :
    HasK6In (colorClass C c) R := by
  apply Classical.byContradiction
  intro hnoK6
  let G := colorClass C c
  let F := G.compl
  -- Step 1: F is triangle-free on R (a triangle in F is a 3-IS in G)
  have htf : IsTriangleFreeOn F R := by
    intro u v w hRu hRv hRw huv hvw
    by_cases huw : F.adj u w = true
    · exfalso
      have hne_uv : u ≠ v := of_decide_eq_true (Bool.and_eq_true _ _ |>.mp huv).1
      have hne_vw : v ≠ w := of_decide_eq_true (Bool.and_eq_true _ _ |>.mp hvw).1
      have hne_uw : u ≠ w := of_decide_eq_true (Bool.and_eq_true _ _ |>.mp huw).1
      have hGuv : G.adj u v = false := by
        have := (Bool.and_eq_true _ _ |>.mp huv).2; simpa using this
      have hGvw : G.adj v w = false := by
        have := (Bool.and_eq_true _ _ |>.mp hvw).2; simpa using this
      have hGuw : G.adj u w = false := by
        have := (Bool.and_eq_true _ _ |>.mp huw).2; simpa using this
      let I : Fin (6 * 6 + 1) → Bool := fun x => decide (x = u) || decide (x = v) || decide (x = w)
      have hIsub : ∀ x, I x = true → R x = true := by
        intro x hx
        simp only [I, Bool.or_eq_true, decide_eq_true_eq] at hx
        rcases hx with (rfl | rfl) | rfl <;> assumption
      have hIind : IsIndep G I := by
        intro x y hx hy
        simp only [I, Bool.or_eq_true, decide_eq_true_eq] at hx hy
        rcases hx with (rfl | rfl) | rfl <;> rcases hy with (rfl | rfl) | rfl
        · exact G.loopless _
        · exact hGuv
        · exact hGuw
        · rw [G.symm]; exact hGuv
        · exact G.loopless _
        · exact hGvw
        · rw [G.symm]; exact hGuw
        · rw [G.symm]; exact hGvw
        · exact G.loopless _
      have hIcard : subsetCard I = 3 := by
        unfold subsetCard
        have hp1 := filter_length_partition (verts (6 * 6 + 1)) I (fun x => decide (x = u))
        have h1 : ((verts (6 * 6 + 1)).filter (fun x => I x && decide (x = u))).length = 1 := by
          have heq : ((verts (6 * 6 + 1)).filter (fun x => I x && decide (x = u))).length =
                     ((verts (6 * 6 + 1)).filter (fun x => decide (x = u))).length := by
            apply filter_length_eq; intro x _
            by_cases hx : x = u
            · subst hx; simp [I]
            · simp [I, hx]
          rw [heq]; exact length_filter_eq_one_of_nodup _ (nodup_verts _) u (mem_verts u)
        have hp2 := filter_length_partition (verts (6 * 6 + 1)) (fun x => I x && !decide (x = u)) (fun x => decide (x = v))
        have h2 : ((verts (6 * 6 + 1)).filter (fun x => (I x && !decide (x = u)) && decide (x = v))).length = 1 := by
          have heq : ((verts (6 * 6 + 1)).filter (fun x => (I x && !decide (x = u)) && decide (x = v))).length =
                     ((verts (6 * 6 + 1)).filter (fun x => decide (x = v))).length := by
            apply filter_length_eq; intro x _
            by_cases hx : x = v
            · subst hx; simp [I, Ne.symm hne_uv]
            · simp [I, hx]
          rw [heq]; exact length_filter_eq_one_of_nodup _ (nodup_verts _) v (mem_verts v)
        have h3 : ((verts (6 * 6 + 1)).filter (fun x => (I x && !decide (x = u)) && !decide (x = v))).length = 1 := by
          have heq : ((verts (6 * 6 + 1)).filter (fun x => (I x && !decide (x = u)) && !decide (x = v))).length =
                     ((verts (6 * 6 + 1)).filter (fun x => decide (x = w))).length := by
            apply filter_length_eq; intro x _
            by_cases hx : x = w
            · subst hx; simp [I, Ne.symm hne_uw, Ne.symm hne_vw]
            · by_cases hxu : x = u
              · subst hxu; simp [I, hx]
              · by_cases hxv : x = v
                · subst hxv; simp [I, hx]
                · simp [I, hx, hxu, hxv]
          rw [heq]; exact length_filter_eq_one_of_nodup _ (nodup_verts _) w (mem_verts w)
        omega
      have := hα2 I hIsub hIind
      omega
    · cases h : F.adj u w; rfl; exact absurd h huw
  -- Step 2: Every independent set of F inside R has size ≤ 5 (else it's a K₆ in G[R])
  have hαF : ∀ K : Fin (6 * 6 + 1) → Bool, (∀ v, K v = true → R v = true) →
      IsIndep F K → subsetCard K ≤ 5 := by
    intro K hKsub hKind
    by_cases hle : subsetCard K ≤ 5
    · exact hle
    · exfalso
      obtain ⟨K6, hK6sub, hK6card⟩ := exists_sub_card K 6 (by omega)
      have hK6ind : IsIndep F K6 := isIndep_mono hK6sub hKind
      have hK6e0 : edgesIn F K6 = 0 := (isIndep_iff_edgesIn_zero F K6).mp hK6ind
      exact hnoK6 ⟨K6, fun v hv => hKsub v (hK6sub v hv), hK6card, hK6e0⟩
  -- Step 3: Every v ∈ R has degIn F R v ≤ 5 (since N_F(v) ∩ R is an IS in F)
  have hdeg_le5 : ∀ v : Fin (6 * 6 + 1), R v = true → degIn F R v ≤ 5 := by
    intro v hRv
    let Nv : Fin (6 * 6 + 1) → Bool := fun w => R w && F.adj v w
    have hNsub : ∀ w, Nv w = true → R w = true := fun w hw => (Bool.and_eq_true _ _ |>.mp hw).1
    have hNind : IsIndep F Nv := by
      intro x y hx hy
      have hx' := Bool.and_eq_true _ _ |>.mp hx
      have hy' := Bool.and_eq_true _ _ |>.mp hy
      have hfv := htf v x y hRv hx'.1 hy'.1 hx'.2
      by_cases hxy : F.adj x y = true
      · have := hfv hxy; rw [hy'.2] at this; exact Bool.noConfusion this
      · cases h : F.adj x y; rfl; exact absurd h hxy
    exact hαF Nv hNsub hNind
  -- Step 4: By multiscale_turan_complement (k = 1) on R (|R| = 12), twoEdgesIn F R ≥ 60
  have hms := multiscale_turan_complement C hbal c R 1
  have hte := two_mul_edgesIn F R
  have h2eF : twoEdgesIn F R ≥ 60 := by
    dsimp [F, G] at hte ⊢
    rw [hRcard, hte] at hms
    omega
  -- Step 5: Since ∑_{v ∈ R} degIn F R v ≥ 60 and each ≤ 5 (with |R| = 12), EVERY v ∈ R has degIn F R v = 5!
  have hdeg_eq5 : ∀ v : Fin (6 * 6 + 1), R v = true → degIn F R v ≥ 5 := by
    intro v hRv
    by_cases h5 : degIn F R v ≥ 5
    · exact h5
    · exfalso
      have hlt5 : degIn F R v ≤ 4 := by omega
      -- Sum over R is ≤ 4 + 5 * 11 = 59 < 60!
      have hsum_le : twoEdgesIn F R ≤
          ((verts (6 * 6 + 1)).map (fun u => if R u then (if u = v then 4 else 5) else 0)).sum := by
        unfold twoEdgesIn
        rw [sum_filter_eq_sum_ite]
        apply sum_map_le; intro u _
        by_cases hRu : R u = true
        · simp only [hRu, ↓reduceIte]
          by_cases huv : u = v
          · subst huv; simp [hlt5]
          · simp [huv, hdeg_le5 u hRu]
        · have hRuf : R u = false := by cases h : R u; rfl; exact absurd h hRu
          simp [hRuf]
      have hcalc : ((verts (6 * 6 + 1)).map (fun u => if R u then (if u = v then 4 else 5) else 0)).sum + 1 =
                   ((verts (6 * 6 + 1)).map (fun u => if R u then 5 else 0)).sum := by
        have hdiff : ((verts (6 * 6 + 1)).map (fun u => if R u then 5 else 0)).sum =
                     ((verts (6 * 6 + 1)).map (fun u => if R u then (if u = v then 4 else 5) else 0)).sum +
                     ((verts (6 * 6 + 1)).map (fun u => if u = v then 1 else 0)).sum := by
          rw [← sum_map_add]
          apply sum_map_eq; intro u _
          by_cases huv : u = v
          · subst huv; simp [hRv]
          · cases R u <;> simp [huv]
        have h1 : ((verts (6 * 6 + 1)).map (fun u => if u = v then 1 else 0)).sum = 1 := by
          have : ((verts (6 * 6 + 1)).map (fun u => if u = v then 1 else 0)).sum =
                 ((verts (6 * 6 + 1)).filter (fun u => decide (u = v))).length := by
            rw [length_filter_eq_sum]; apply sum_map_eq; intro u _; by_cases h : u = v <;> simp [h]
          rw [this]; exact length_filter_eq_one_of_nodup _ (nodup_verts _) v (mem_verts v)
        omega
      have h5R : ((verts (6 * 6 + 1)).map (fun u => if R u then 5 else 0)).sum = 60 := by
        have hm : ((verts (6 * 6 + 1)).map (fun u => if R u then 5 else 0)).sum =
                  5 * ((verts (6 * 6 + 1)).map (fun u => if R u then 1 else 0)).sum := by
          rw [← sum_map_mul_left]; apply sum_map_eq; intro u _; cases R u <;> simp
        rw [hm, ← length_filter_eq_sum]
        change 5 * subsetCard R = 60
        rw [hRcard]
      omega
  -- Step 6: By Andrásfai–Erdős–Sós (5 * 5 = 25 > 24 = 2 * 12), F is bipartite on R!
  have hbip : IsBipartiteOn F R :=
    andrasfai_erdos_sos_bipartite F R 5 htf hdeg_eq5 (by rw [hRcard]; omega)
  obtain ⟨col, hcol⟩ := hbip
  -- Larger color class in R has size ≥ 6 and is an IS in F!
  let side0 : Fin (6 * 6 + 1) → Bool := fun v => R v && !col v
  let side1 : Fin (6 * 6 + 1) → Bool := fun v => R v && col v
  have hpart := filter_length_partition (verts (6 * 6 + 1)) R col
  have hsum_sides : subsetCard side1 + subsetCard side0 = 12 := by
    unfold subsetCard side0 side1 at *; omega
  have hind0 : IsIndep F side0 := by
    intro u v hu hv
    have hu' := Bool.and_eq_true _ _ |>.mp hu
    have hv' := Bool.and_eq_true _ _ |>.mp hv
    by_cases hadj : F.adj u v = true
    · exfalso
      have hne := hcol u v hu'.1 hv'.1 hadj
      have hc0 : col u = false := by simpa using hu'.2
      have hc1 : col v = false := by simpa using hv'.2
      rw [hc0, hc1] at hne; exact hne rfl
    · cases h : F.adj u v; rfl; exact absurd h hadj
  have hind1 : IsIndep F side1 := by
    intro u v hu hv
    have hu' := Bool.and_eq_true _ _ |>.mp hu
    have hv' := Bool.and_eq_true _ _ |>.mp hv
    by_cases hadj : F.adj u v = true
    · exfalso
      have hne := hcol u v hu'.1 hv'.1 hadj
      rw [hu'.2, hv'.2] at hne; exact hne rfl
    · cases h : F.adj u v; rfl; exact absurd h hadj
  have h0le := hαF side0 (fun v hv => (Bool.and_eq_true _ _ |>.mp hv).1) hind0
  have h1le := hαF side1 (fun v hv => (Bool.and_eq_true _ _ |>.mp hv).1) hind1
  omega

/-! ## Section 2: Reusable `K₆`-Extension, Single-Vertex Peel, and 2-Matching Helpers -/

/-- **Rigid `K₆` Independent-Set Extension:**
    If `K ⊆ U` is a `K₆` in `G_c` and `I ⊆ U \ K` is an independent set with `|I| ≤ 5`,
    then `∃ u ∈ K` non-adjacent to all vertices of `I`, extending `I` to an IS of size `|I| + 1`. -/
theorem extend_indep_with_K6 (C : EdgeColoring (6 * 6 + 1) 6) (hbal : IsBalanced C)
    (c : Fin 6) (K I : Fin (6 * 6 + 1) → Bool)
    (hKcard : subsetCard K = 6) (hKclq : edgesIn (colorClass C c).compl K = 0)
    (hdisj : ∀ v, I v = true → K v = false)
    (hIind : IsIndep (colorClass C c) I) (hIcard : subsetCard I ≤ 5) :
    ∃ u : Fin (6 * 6 + 1), K u = true ∧
      (∀ w, I w = true → (colorClass C c).adj u w = false) ∧
      IsIndep (colorClass C c) (fun x => I x || decide (x = u)) ∧
      subsetCard (fun x => I x || decide (x = u)) = subsetCard I + 1 := by
  let G := colorClass C c
  -- Count vertices in K adjacent to at least one vertex of I: at most crossEdges G I K ≤ |I| * 1 ≤ 5 < 6!
  have hcross_le : crossEdges G I K ≤ subsetCard I := by
    unfold crossEdges
    have hle := sum_map_le (verts (6 * 6 + 1))
      (fun w => if I w then degIn G K w else 0)
      (fun w => if I w then 1 else 0)
      (fun w _ => by
        by_cases hIw : I w = true
        · simp only [hIw, ↓reduceIte]
          exact r6_rigid_K6 C hbal c K hKcard hKclq w (hdisj w hIw)
        · have hIwf : I w = false := by cases h : I w; rfl; exact absurd h hIw
          simp [hIwf])
    rw [← length_filter_eq_sum] at hle
    exact hle
  -- Therefore some u ∈ K has degIn G I u = 0!
  have hex_u : ∃ u : Fin (6 * 6 + 1), K u = true ∧ degIn G I u = 0 := by
    apply Classical.byContradiction
    intro hnone
    have hge1 : ∀ u : Fin (6 * 6 + 1), K u = true → degIn G I u ≥ 1 := by
      intro u hKu
      by_cases h0 : degIn G I u = 0
      · exact False.elim (hnone ⟨u, hKu, h0⟩)
      · omega
    have hlb := crossEdges_le_sum_degIn G K I 1 hge1
    rw [crossEdges_symm G K I, hKcard] at hlb
    omega
  obtain ⟨u, hKu, hdeg0⟩ := hex_u
  have hnotadj : ∀ w, I w = true → G.adj u w = false := by
    intro w hIw
    by_cases hadj : G.adj u w = true
    · exfalso
      have hmem : w ∈ (verts (6 * 6 + 1)).filter (fun x => I x && G.adj u x) :=
        List.mem_filter.mpr ⟨mem_verts w, by simp [hIw, hadj]⟩
      have hpos : degIn G I u ≥ 1 := by
        unfold degIn
        cases hf : (verts (6 * 6 + 1)).filter (fun x => I x && G.adj u x) with
        | nil => rw [hf] at hmem; cases hmem
        | cons _ _ => simp
      omega
    · cases h : G.adj u w; rfl; exact absurd h hadj
  have huNotI : I u = false := by
    by_cases h : I u = true
    · have := hdisj u h; rw [hKu] at this; exact Bool.noConfusion this
    · cases hi : I u; rfl; exact absurd hi h
  refine ⟨u, hKu, hnotadj, ?_, ?_⟩
  · intro x y hx hy
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hx hy
    rcases hx with hIx | rfl <;> rcases hy with hIy | rfl
    · exact hIind x y hIx hIy
    · rw [G.symm]; exact hnotadj x hIx
    · exact hnotadj y hIy
    · exact G.loopless _
  · unfold subsetCard
    have hp := filter_length_partition (verts (6 * 6 + 1)) (fun x => I x || decide (x = u)) (fun x => decide (x = u))
    have h1 : ((verts (6 * 6 + 1)).filter (fun x => (I x || decide (x = u)) && decide (x = u))).length = 1 := by
      have heq : ((verts (6 * 6 + 1)).filter (fun x => (I x || decide (x = u)) && decide (x = u))).length =
                 ((verts (6 * 6 + 1)).filter (fun x => decide (x = u))).length := by
        apply filter_length_eq; intro x _
        by_cases hx : x = u
        · subst hx; simp
        · simp [hx]
      rw [heq]; exact length_filter_eq_one_of_nodup _ (nodup_verts _) u (mem_verts u)
    have h2 : ((verts (6 * 6 + 1)).filter (fun x => (I x || decide (x = u)) && !decide (x = u))).length =
              ((verts (6 * 6 + 1)).filter I).length := by
      apply filter_length_eq; intro x _
      by_cases hx : x = u
      · subst hx; simp [huNotI]
      · simp [hx]
    omega

/-- Single-vertex neighborhood peel: splits `U` at a minimum-degree vertex `v ∈ U` into
    `B = N_{G[U]}[v]` and `A = U \ B`. -/
theorem peel_at_min_vertex {n : Nat} (G : SGraph n) (U : Fin n → Bool) (v : Fin n)
    (hvU : U v = true) (hvmin : ∀ u : Fin n, U u = true → degIn G U v ≤ degIn G U u) :
    let B : Fin n → Bool := fun w => U w && (decide (w = v) || G.adj v w)
    let A : Fin n → Bool := fun w => U w && !decide (w = v) && !G.adj v w
    let D : Nat := ((verts n).map (fun u => if B u then degIn G U u - degIn G U v else 0)).sum
    subsetCard B = degIn G U v + 1 ∧
    subsetCard A + subsetCard B = subsetCard U ∧
    (∀ w, !(A w && B w) = true) ∧
    (∀ w, U w = (A w || B w)) ∧
    crossEdges G A B = twoEdgesIn G.compl B + D ∧
    twoEdgesIn G U = twoEdgesIn G A + subsetCard B * (subsetCard B - 1) + twoEdgesIn G.compl B + 2 * D ∧
    (∀ k, (∀ I, (∀ w, I w = true → U w = true) → IsIndep G I → subsetCard I ≤ k + 1) →
          (∀ I, (∀ w, I w = true → A w = true) → IsIndep G I → subsetCard I ≤ k)) := by
  intro B A D
  have hBcard : subsetCard B = degIn G U v + 1 := by
    have hp := filter_length_partition (verts n) B (fun w => decide (w = v))
    have h1 : ((verts n).filter (fun w => B w && decide (w = v))).length = 1 := by
      have heq : ((verts n).filter (fun w => B w && decide (w = v))).length =
                 ((verts n).filter (fun w => decide (w = v))).length := by
        apply filter_length_eq; intro w _
        by_cases hw : w = v
        · subst hw; simp [B, hvU]
        · simp [B, hw]
      rw [heq]; exact length_filter_eq_one_of_nodup (verts n) (nodup_verts n) v (mem_verts v)
    have h2 : ((verts n).filter (fun w => B w && !decide (w = v))).length = degIn G U v := by
      unfold degIn; apply filter_length_eq; intro w _
      by_cases hw : w = v
      · subst hw; simp [B, G.loopless]
      · simp [B, hw]
    unfold subsetCard; omega
  have hdisj : ∀ w, !(A w && B w) = true := by
    intro w; by_cases hw : w = v <;> cases hU : U w <;> cases ha : G.adj v w <;> simp [A, B, hw, hU, ha]
  have hunion : ∀ w, U w = (A w || B w) := by
    intro w; by_cases hw : w = v
    · subst hw; cases hU : U w <;> simp [A, B, hU]
    · cases hU : U w <;> cases ha : G.adj v w <;> simp [A, B, hw, hU, ha]
  have hcard_sum : subsetCard A + subsetCard B = subsetCard U := by
    have hp := filter_length_partition (verts n) U B
    have h1 : ((verts n).filter (fun w => U w && B w)).length = subsetCard B := by
      unfold subsetCard; apply filter_length_eq; intro w _
      dsimp [B]; cases U w <;> simp
    have h2 : ((verts n).filter (fun w => U w && !B w)).length = subsetCard A := by
      unfold subsetCard; apply filter_length_eq; intro w _
      by_cases hw : w = v
      · subst hw; cases hU : U w <;> simp [A, B, hU]
      · cases hU : U w <;> cases ha : G.adj v w <;> simp [A, B, hw, hU, ha]
    unfold subsetCard at *; omega
  have hsumB : crossEdges G B U = twoEdgesIn G B + crossEdges G A B := by
    rw [crossEdges_congr G (fun _ => rfl) hunion]
    rw [sum_degIn_union_disjoint G B A B hdisj, crossEdges_self, crossEdges_symm G B A, Nat.add_comm]
  have hdef : crossEdges G B U = subsetCard B * (subsetCard B - 1) + D := by
    have hsub1 : subsetCard B - 1 = degIn G U v := by omega
    rw [hsub1]
    unfold crossEdges
    have h1 : subsetCard B * degIn G U v = ((verts n).map (fun u => if B u then degIn G U v else 0)).sum := by
      have h2 : ((verts n).map (fun u => if B u then degIn G U v else 0)).sum =
                degIn G U v * ((verts n).map (fun u => if B u then 1 else 0)).sum := by
        rw [← sum_map_mul_left]; apply sum_map_eq; intro u _; cases B u <;> simp
      rw [h2, ← length_filter_eq_sum, Nat.mul_comm]; rfl
    dsimp only [D]
    rw [h1, ← sum_map_add]
    apply sum_map_eq; intro u _
    by_cases hBu : B u = true
    · have hUu : U u = true := (Bool.and_eq_true _ _ |>.mp hBu).1
      have hge := hvmin u hUu
      simp only [hBu, ↓reduceIte]; omega
    · have hBuf : B u = false := by cases h : B u; rfl; exact absurd h hBu
      simp [hBuf]
  have hcompl := twoEdgesIn_add_compl G B
  have hcross_eq : crossEdges G A B = twoEdgesIn G.compl B + D := by omega
  have hU_eq : twoEdgesIn G U = twoEdgesIn G A + subsetCard B * (subsetCard B - 1) + twoEdgesIn G.compl B + 2 * D := by
    have hc : twoEdgesIn G U = twoEdgesIn G (fun w => A w || B w) := by
      rw [twoEdgesIn_eq_double_sum, twoEdgesIn_eq_double_sum]
      apply sum_map_eq; intro x _; apply sum_map_eq; intro y _; rw [hunion x, hunion y]
    rw [hc, twoEdgesIn_union_disjoint G A B hdisj]
    omega
  refine ⟨hBcard, hcard_sum, hdisj, hunion, hcross_eq, hU_eq, ?_⟩
  intro k hα I hIsub hIind
  let I' : Fin n → Bool := fun w => I w || decide (w = v)
  have hI'sub : ∀ w, I' w = true → U w = true := by
    intro w hw
    simp only [I', Bool.or_eq_true, decide_eq_true_eq] at hw
    rcases hw with hIw | rfl
    · exact (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp (hIsub w hIw)).1).1
    · exact hvU
  have hI'ind : IsIndep G I' := by
    intro x y hx hy
    simp only [I', Bool.or_eq_true, decide_eq_true_eq] at hx hy
    rcases hx with hIx | rfl <;> rcases hy with hIy | rfl
    · exact hIind x y hIx hIy
    · rw [G.symm]; have := (Bool.and_eq_true _ _ |>.mp (hIsub x hIx)).2; simpa using this
    · have := (Bool.and_eq_true _ _ |>.mp (hIsub y hIy)).2; simpa using this
    · exact G.loopless _
  have hvnotI : I v = false := by
    by_cases h : I v = true
    · have := (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp (hIsub v h)).1).2; simp at this
    · cases hi : I v; rfl; exact absurd hi h
  have hI'card : subsetCard I' = subsetCard I + 1 := by
    unfold subsetCard
    have hp := filter_length_partition (verts n) I' (fun w => decide (w = v))
    have h1 : ((verts n).filter (fun w => I' w && decide (w = v))).length = 1 := by
      have heq : ((verts n).filter (fun w => I' w && decide (w = v))).length =
                 ((verts n).filter (fun w => decide (w = v))).length := by
        apply filter_length_eq; intro w _
        by_cases hw : w = v
        · subst hw; simp [I']
        · simp [I', hw]
      rw [heq]; exact length_filter_eq_one_of_nodup (verts n) (nodup_verts n) v (mem_verts v)
    have h2 : ((verts n).filter (fun w => I' w && !decide (w = v))).length = ((verts n).filter I).length := by
      apply filter_length_eq; intro w _
      by_cases hw : w = v
      · subst hw; simp [I', hvnotI]
      · simp [I', hw]
    omega
  have := hα I' hI'sub hI'ind
  omega

/-- **2-Matching Lemma in `compl(B)`:**
    If `|B| = 7`, `edgesIn G.compl B ≥ 5`, and `B` contains NO `K₆` in `G`, then `G.compl`
    contains two vertex-disjoint edges `{a₁, b₁}` and `{a₂, b₂}` inside `B`. -/
theorem exists_two_matching_in_B {n : Nat} (G : SGraph n) (B : Fin n → Bool)
    (hBcard : subsetCard B = 7) (hm5 : twoEdgesIn G.compl B ≥ 10)
    (hnoK6 : ¬ HasK6In G B) :
    ∃ a1 b1 a2 b2 : Fin n,
      B a1 = true ∧ B b1 = true ∧ B a2 = true ∧ B b2 = true ∧
      a1 ≠ b1 ∧ a1 ≠ a2 ∧ a1 ≠ b2 ∧ b1 ≠ a2 ∧ b1 ≠ b2 ∧ a2 ≠ b2 ∧
      G.adj a1 b1 = false ∧ G.adj a2 b2 = false := by
  let F := G.compl
  -- Helper: if a subset T ⊆ B has size 6, it must have at least 1 edge of F (else it's a K₆!)
  have hex_edge_in : ∀ x : Fin n, B x = true →
      ∃ u v : Fin n, B u = true ∧ B v = true ∧ u ≠ x ∧ v ≠ x ∧ F.adj u v = true := by
    intro x hBx
    let T : Fin n → Bool := fun w => B w && !decide (w = x)
    have hTcard : subsetCard T = 6 := by
      unfold subsetCard
      have hp := filter_length_partition (verts n) B (fun w => decide (w = x))
      have h1 : ((verts n).filter (fun w => B w && decide (w = x))).length = 1 := by
        have heq : ((verts n).filter (fun w => B w && decide (w = x))).length =
                   ((verts n).filter (fun w => decide (w = x))).length := by
          apply filter_length_eq; intro w _
          by_cases hw : w = x
          · subst hw; simp [hBx]
          · simp [hw]
        rw [heq]; exact length_filter_eq_one_of_nodup (verts n) (nodup_verts n) x (mem_verts x)
      unfold subsetCard at hBcard; dsimp [T]; omega
    have hTe_pos : twoEdgesIn F T > 0 := by
      by_cases h0 : twoEdgesIn F T = 0
      · exfalso
        have he0 : edgesIn F T = 0 := by unfold edgesIn; omega
        exact hnoK6 ⟨T, fun w hw => (Bool.and_eq_true _ _ |>.mp hw).1, hTcard, he0⟩
      · omega
    -- Extract a pair (u, v) with T u ∧ T v ∧ F.adj u v
    apply Classical.byContradiction
    intro hnone
    have h0 : twoEdgesIn F T = 0 := by
      rw [twoEdgesIn_eq_double_sum]
      apply sum_map_eq_zero; intro u _
      apply sum_map_eq_zero; intro v _
      by_cases hcond : (T u && T v && F.adj u v) = true
      · exfalso
        have h1 := Bool.and_eq_true _ _ |>.mp hcond
        have h2 := Bool.and_eq_true _ _ |>.mp h1.1
        have hu := Bool.and_eq_true _ _ |>.mp h2.1
        have hv := Bool.and_eq_true _ _ |>.mp h2.2
        exact hnone ⟨u, v, hu.1, hv.1, by simpa using hu.2, by simpa using hv.2, h1.2⟩
      · have hcf : (T u && T v && F.adj u v) = false := by
          cases h : T u && T v && F.adj u v; rfl; exact absurd h hcond
        rw [hcf]; rfl
    omega
  -- Pick ANY edge (x, y) of F in B
  have hex_xy : ∃ x y : Fin n, B x = true ∧ B y = true ∧ F.adj x y = true := by
    apply Classical.byContradiction
    intro hnone
    have h0 : twoEdgesIn F B = 0 := by
      rw [twoEdgesIn_eq_double_sum]
      apply sum_map_eq_zero; intro u _
      apply sum_map_eq_zero; intro v _
      by_cases hc : (B u && B v && F.adj u v) = true
      · exfalso
        have h1 := Bool.and_eq_true _ _ |>.mp hc
        have h2 := Bool.and_eq_true _ _ |>.mp h1.1
        exact hnone ⟨u, v, h2.1, h2.2, h1.2⟩
      · have hcf : (B u && B v && F.adj u v) = false := by
          cases h : B u && B v && F.adj u v; rfl; exact absurd h hc
        rw [hcf]; rfl
    dsimp [F] at h0; omega
  obtain ⟨x, y, hBx, hBy, hFxy⟩ := hex_xy
  have hxy : x ≠ y := of_decide_eq_true (Bool.and_eq_true _ _ |>.mp hFxy).1
  obtain ⟨p, q, hBp, hBq, hpx, hqx, hFpq⟩ := hex_edge_in x hBx
  obtain ⟨r, s, hBr, hBs, hry, hsy, hFrs⟩ := hex_edge_in y hBy
  have hpq : p ≠ q := of_decide_eq_true (Bool.and_eq_true _ _ |>.mp hFpq).1
  have hrs : r ≠ s := of_decide_eq_true (Bool.and_eq_true _ _ |>.mp hFrs).1
  have to_G : ∀ u v, F.adj u v = true → G.adj u v = false := by
    intro u v h; have := (Bool.and_eq_true _ _ |>.mp h).2; simpa using this
  -- Helper: any triangle {a, b, c} in F[B] yields a 2-matching because twoEdgesIn F B ≥ 10 > 6
  have from_tri : ∀ a b c : Fin n,
      B a = true → B b = true → B c = true →
      a ≠ b → a ≠ c → b ≠ c →
      F.adj a b = true → F.adj a c = true → F.adj b c = true →
      ∃ a1 b1 a2 b2 : Fin n,
        B a1 = true ∧ B b1 = true ∧ B a2 = true ∧ B b2 = true ∧
        a1 ≠ b1 ∧ a1 ≠ a2 ∧ a1 ≠ b2 ∧ b1 ≠ a2 ∧ b1 ≠ b2 ∧ a2 ≠ b2 ∧
        G.adj a1 b1 = false ∧ G.adj a2 b2 = false := by
    intro a b c hBa hBb hBc hab hac hbc hFab hFac hFbc
    have hex_out : ∃ u v : Fin n, B u = true ∧ B v = true ∧ F.adj u v = true ∧
        (u ≠ a ∧ u ≠ b ∧ u ≠ c) := by
      apply Classical.byContradiction
      intro hnone
      let tri : Fin n → Bool := fun w => decide (w = a) || decide (w = b) || decide (w = c)
      have htri_le : subsetCard tri ≤ 3 := by
        unfold subsetCard
        have hp1 := filter_length_partition (verts n) tri (fun w => decide (w = a))
        have h1 : ((verts n).filter (fun w => tri w && decide (w = a))).length ≤ 1 := by
          have h := filter_length_le (verts n) (fun w => tri w && decide (w = a)) (fun w => decide (w = a))
            (fun w _ hw => (Bool.and_eq_true _ _ |>.mp hw).2)
          rw [length_filter_eq_one_of_nodup (verts n) (nodup_verts n) a (mem_verts a)] at h; exact h
        have hp2 := filter_length_partition (verts n) (fun w => tri w && !decide (w = a)) (fun w => decide (w = b))
        have h2 : ((verts n).filter (fun w => (tri w && !decide (w = a)) && decide (w = b))).length ≤ 1 := by
          have h := filter_length_le (verts n) (fun w => (tri w && !decide (w = a)) && decide (w = b))
            (fun w => decide (w = b)) (fun w _ hw => (Bool.and_eq_true _ _ |>.mp hw).2)
          rw [length_filter_eq_one_of_nodup (verts n) (nodup_verts n) b (mem_verts b)] at h; exact h
        have h3 : ((verts n).filter (fun w => (tri w && !decide (w = a)) && !decide (w = b))).length ≤ 1 := by
          have h := filter_length_le (verts n) (fun w => (tri w && !decide (w = a)) && !decide (w = b))
            (fun w => decide (w = c)) (fun w _ hw => by
              simp only [tri, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
                         decide_eq_true_eq, decide_eq_false_iff_not] at hw
              rcases hw.1.1 with (h' | h') | h'
              · exact absurd h' hw.1.2
              · exact absurd h' hw.2
              · exact decide_eq_true h')
          rw [length_filter_eq_one_of_nodup (verts n) (nodup_verts n) c (mem_verts c)] at h; exact h
        omega
      have hle_tri : twoEdgesIn F B ≤ twoEdgesIn F tri := by
        rw [twoEdgesIn_eq_double_sum, twoEdgesIn_eq_double_sum]
        apply sum_map_le; intro u _; apply sum_map_le; intro v _
        by_cases hc : (B u && B v && F.adj u v) = true
        · have h1 := Bool.and_eq_true _ _ |>.mp hc
          have h2 := Bool.and_eq_true _ _ |>.mp h1.1
          have htri_u : tri u = true := by
            apply Classical.byContradiction; intro hnu
            exact hnone ⟨u, v, h2.1, h2.2, h1.2, ⟨fun h => by subst h; simp [tri] at hnu,
              fun h => by subst h; simp [tri] at hnu, fun h => by subst h; simp [tri] at hnu⟩⟩
          have htri_v : tri v = true := by
            apply Classical.byContradiction; intro hnv
            exact hnone ⟨v, u, h2.2, h2.1, by rw [F.symm]; exact h1.2, ⟨fun h => by subst h; simp [tri] at hnv,
              fun h => by subst h; simp [tri] at hnv, fun h => by subst h; simp [tri] at hnv⟩⟩
          simp [h1.2, h2.1, h2.2, htri_u, htri_v]
        · have hcf : (B u && B v && F.adj u v) = false := by
            cases h : B u && B v && F.adj u v; rfl; exact absurd h hc
          rw [hcf]; simp
      have hcomp := twoEdgesIn_le_complete F tri
      have hmul : subsetCard tri * (subsetCard tri - 1) ≤ 6 := by
        have : subsetCard tri = 0 ∨ subsetCard tri = 1 ∨ subsetCard tri = 2 ∨ subsetCard tri = 3 := by omega
        rcases this with h | h | h | h <;> simp [h]
      dsimp [F] at hle_tri hcomp
      omega
    obtain ⟨u, v, hBu, hBv, hFuv, hua, hub, huc⟩ := hex_out
    have huv : u ≠ v := of_decide_eq_true (Bool.and_eq_true _ _ |>.mp hFuv).1
    by_cases hva : v = a
    · subst hva
      exact ⟨u, v, b, c, hBu, hBa, hBb, hBc, huv, hub, huc, hab, hac, hbc, to_G _ _ hFuv, to_G _ _ hFbc⟩
    · by_cases hvb : v = b
      · subst hvb
        exact ⟨u, v, a, c, hBu, hBb, hBa, hBc, huv, hua, huc, Ne.symm hab, hbc, hac, to_G _ _ hFuv, to_G _ _ hFac⟩
      · exact ⟨u, v, a, b, hBu, hBv, hBa, hBb, huv, hua, hub, hva, hvb, hab, to_G _ _ hFuv, to_G _ _ hFab⟩
  -- Normalize: we have edge (x, y), edge (p, q) missing x, edge (r, s) missing y.
  by_cases hpy : p = y
  · by_cases hrx : r = x
    · by_cases hsq : s = q
      · exact from_tri x y q hBx hBy hBq hxy (Ne.symm hqx) (hpy ▸ hpq) hFxy
          (hrx ▸ hsq ▸ hFrs) (hpy ▸ hFpq)
      · exact ⟨x, s, y, q, hBx, hBs, hBy, hBq, hrx ▸ hrs, hxy, Ne.symm hqx, hsy, hsq, hpy ▸ hpq,
               to_G _ _ (hrx ▸ hFrs), to_G _ _ (hpy ▸ hFpq)⟩
    · by_cases hsx : s = x
      · by_cases hrq : r = q
        · exact from_tri x y q hBx hBy hBq hxy (Ne.symm hqx) (hpy ▸ hpq) hFxy
            (by rw [F.symm]; exact hsx ▸ hrq ▸ hFrs) (hpy ▸ hFpq)
        · exact ⟨r, x, y, q, hBr, hBx, hBy, hBq, hsx ▸ hrs, hry, hrq, hxy, Ne.symm hqx, hpy ▸ hpq,
                 to_G _ _ (hsx ▸ hFrs), to_G _ _ (hpy ▸ hFpq)⟩
      · exact ⟨x, y, r, s, hBx, hBy, hBr, hBs, hxy, Ne.symm hrx, Ne.symm hsx, Ne.symm hry, Ne.symm hsy, hrs,
               to_G _ _ hFxy, to_G _ _ hFrs⟩
  · by_cases hqy : q = y
    · by_cases hrx : r = x
      · by_cases hsp : s = p
        · exact from_tri x y p hBx hBy hBp hxy (Ne.symm hpx) (Ne.symm (hqy ▸ hpq)) hFxy
            (hrx ▸ hsp ▸ hFrs) (by rw [F.symm]; exact hqy ▸ hFpq)
        · exact ⟨x, s, p, y, hBx, hBs, hBp, hBy, hrx ▸ hrs, Ne.symm hpx, hxy, hsp, hsy, hqy ▸ hpq,
                 to_G _ _ (hrx ▸ hFrs), to_G _ _ (hqy ▸ hFpq)⟩
      · by_cases hsx : s = x
        · by_cases hrp : r = p
          · exact from_tri x y p hBx hBy hBp hxy (Ne.symm hpx) (Ne.symm (hqy ▸ hpq)) hFxy
              (by rw [F.symm]; exact hsx ▸ hrp ▸ hFrs) (by rw [F.symm]; exact hqy ▸ hFpq)
          · exact ⟨r, x, p, y, hBr, hBx, hBp, hBy, hsx ▸ hrs, hrp, hry, Ne.symm hpx, hxy, hqy ▸ hpq,
                   to_G _ _ (hsx ▸ hFrs), to_G _ _ (hqy ▸ hFpq)⟩
        · exact ⟨x, y, r, s, hBx, hBy, hBr, hBs, hxy, Ne.symm hrx, Ne.symm hsx, Ne.symm hry, Ne.symm hsy, hrs,
                 to_G _ _ hFxy, to_G _ _ hFrs⟩
    · exact ⟨x, y, p, q, hBx, hBy, hBp, hBq, hxy, Ne.symm hpx, Ne.symm hqx, Ne.symm hpy, Ne.symm hqy, hpq,
             to_G _ _ hFxy, to_G _ _ hFpq⟩

/-! ## Section 3: Lemmas 2, 3, and 4 (`N = 19`, `18`, `25`) -/

/-- **Lemma 2 (`no_19_alpha_le_3`):**
    In any balanced 6-coloring of `K₃₇`, NO 19-vertex subset `U` in any color class `G_c`
    can have independence number `α(G_c[U]) ≤ 3`. -/
theorem no_19_alpha_le_3 (C : EdgeColoring (6 * 6 + 1) 6) (hbal : IsBalanced C)
    (c : Fin 6) (U : Fin (6 * 6 + 1) → Bool) (hUcard : subsetCard U = 19) :
    ¬ (∀ I : Fin (6 * 6 + 1) → Bool, (∀ v, I v = true → U v = true) →
        IsIndep (colorClass C c) I → subsetCard I ≤ 3) := by
  intro hα3
  let G := colorClass C c
  -- Step 1: U contains NO K₆
  have hnoK6 : ¬ HasK6In G U := by
    rintro ⟨K, hKsub, hKcard, hKclq⟩
    let W : Fin (6 * 6 + 1) → Bool := fun v => U v && !K v
    have hWcard : subsetCard W = 13 := by
      unfold subsetCard
      have hp := filter_length_partition (verts (6 * 6 + 1)) U K
      have h1 : ((verts (6 * 6 + 1)).filter (fun v => U v && K v)).length = 6 := by
        have heq : ((verts (6 * 6 + 1)).filter (fun v => U v && K v)).length = subsetCard K := by
          unfold subsetCard; apply filter_length_eq; intro v _
          cases h : K v
          · simp
          · simp [hKsub v h]
        rw [heq, hKcard]
      unfold subsetCard at hUcard
      change ((verts (6 * 6 + 1)).filter (fun v => U v && !K v)).length = 13
      omega
    have hnoα2 := no_2r_plus_1_alpha_le_2 (r := 6) (by omega) C hbal c W hWcard
    -- Therefore ∃ 3-IS I ⊆ W
    have hexI : ∃ I : Fin (6 * 6 + 1) → Bool, (∀ v, I v = true → W v = true) ∧
        IsIndep G I ∧ subsetCard I = 3 := by
      apply Classical.byContradiction
      intro hnone
      apply hnoα2
      intro I hIsub hIind
      by_cases hle2 : subsetCard I ≤ 2
      · exact hle2
      · exfalso
        obtain ⟨I3, hI3sub, hI3card⟩ := exists_sub_card I 3 (by omega)
        exact hnone ⟨I3, fun v hv => hIsub v (hI3sub v hv), isIndep_mono hI3sub hIind, hI3card⟩
    obtain ⟨I, hIsub, hIind, hIcard⟩ := hexI
    have hdisj : ∀ v, I v = true → K v = false := by
      intro v hv; have := (Bool.and_eq_true _ _ |>.mp (hIsub v hv)).2; simpa using this
    obtain ⟨u, hKu, _, hI'ind, hI'card⟩ := extend_indep_with_K6 C hbal c K I hKcard hKclq hdisj hIind (by omega)
    have hI'sub : ∀ x, (I x || decide (x = u)) = true → U x = true := by
      intro x hx
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hx
      rcases hx with hIx | rfl
      · exact (Bool.and_eq_true _ _ |>.mp (hIsub x hIx)).1
      · exact hKsub x hKu
    have := hα3 (fun x => I x || decide (x = u)) hI'sub hI'ind
    omega
  -- Step 2: By multiscale_turan_complement (k = 3), twoEdgesIn G U ≤ 132
  have hms := multiscale_turan_complement C hbal c U 3
  have hte := two_mul_edgesIn G.compl U
  have hcompl := twoEdgesIn_add_compl G U
  have h2eU : twoEdgesIn G U ≤ 132 := by
    dsimp [G] at hte hcompl ⊢
    rw [hUcard, hte] at hms
    rw [hUcard] at hcompl
    omega
  -- Step 3: Pick min-degree vertex v ∈ U ⇒ degIn G U v ≤ 6
  obtain ⟨v, hvU, hvmin⟩ := exists_min_degIn G U (by omega)
  have hdeg_le6 : degIn G U v ≤ 6 := by
    have hlb : crossEdges G U U ≥ 19 * degIn G U v := by
      have h := crossEdges_le_sum_degIn G U U (degIn G U v) hvmin
      rw [hUcard] at h; exact h
    rw [crossEdges_self] at hlb
    omega
  -- Step 4: Peel at v ⇒ A = U \ N[v] has |A| ≥ 12 and α(G[A]) ≤ 2 ⇒ contains K₆ by Lemma 1!
  obtain ⟨hBcard, hcard_sum, _, _, _, _, hαA⟩ := peel_at_min_vertex G U v hvU hvmin
  let A : Fin (6 * 6 + 1) → Bool := fun w => U w && !decide (w = v) && !G.adj v w
  let B : Fin (6 * 6 + 1) → Bool := fun w => U w && (decide (w = v) || G.adj v w)
  have hBc : subsetCard B = degIn G U v + 1 := hBcard
  have hcs : subsetCard A + subsetCard B = subsetCard U := hcard_sum
  have hAcard : subsetCard A ≥ 12 := by omega
  obtain ⟨R, hRsub, hRcard⟩ := exists_sub_card A 12 hAcard
  have hαR : ∀ I, (∀ w, I w = true → R w = true) → IsIndep G I → subsetCard I ≤ 2 :=
    fun I hIsub hIind => hαA 2 hα3 I (fun w hw => hRsub w (hIsub w hw)) hIind
  obtain ⟨K, hKsub, hKcard, hKclq⟩ := no_12_alpha_le_2_K6_free C hbal c R hRcard hαR
  exact hnoK6 ⟨K, fun w hw => (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp (hRsub w (hKsub w hw))).1).1,
               hKcard, hKclq⟩

/-- **Lemma 3 (`K6_free_18_edges_ge_54`):**
    Every `K₆`-free 18-vertex subset `A` of `G_c` with `α(G_c[A]) ≤ 3` has `twoEdgesIn G_c A ≥ 108`
    (i.e. `edgesIn G_c A ≥ 54`). -/
theorem K6_free_18_edges_ge_54 (C : EdgeColoring (6 * 6 + 1) 6) (hbal : IsBalanced C)
    (c : Fin 6) (A : Fin (6 * 6 + 1) → Bool) (hAcard : subsetCard A = 18)
    (hα3 : ∀ I, (∀ v, I v = true → A v = true) → IsIndep (colorClass C c) I → subsetCard I ≤ 3)
    (hnoK6 : ¬ HasK6In (colorClass C c) A) :
    twoEdgesIn (colorClass C c) A ≥ 108 := by
  apply Classical.byContradiction
  intro hlt
  let G := colorClass C c
  obtain ⟨w, hwA, hwmin⟩ := exists_min_degIn G A (by omega)
  have hdeg_le5 : degIn G A w ≤ 5 := by
    have hlb := crossEdges_le_sum_degIn G A A (degIn G A w) hwmin
    rw [crossEdges_self, hAcard] at hlb
    dsimp [G] at hlb ⊢; omega
  obtain ⟨hBcard, hcard_sum, _, _, _, _, hαA'⟩ := peel_at_min_vertex G A w hwA hwmin
  let A' : Fin (6 * 6 + 1) → Bool := fun x => A x && !decide (x = w) && !G.adj w x
  let B' : Fin (6 * 6 + 1) → Bool := fun x => A x && (decide (x = w) || G.adj w x)
  have hBc : subsetCard B' = degIn G A w + 1 := hBcard
  have hcs : subsetCard A' + subsetCard B' = subsetCard A := hcard_sum
  have hA'card : subsetCard A' ≥ 12 := by omega
  obtain ⟨R, hRsub, hRcard⟩ := exists_sub_card A' 12 hA'card
  have hαR : ∀ I, (∀ x, I x = true → R x = true) → IsIndep G I → subsetCard I ≤ 2 :=
    fun I hIsub hIind => hαA' 2 hα3 I (fun x hx => hRsub x (hIsub x hx)) hIind
  obtain ⟨K, hKsub, hKcard, hKclq⟩ := no_12_alpha_le_2_K6_free C hbal c R hRcard hαR
  exact hnoK6 ⟨K, fun x hx => (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp (hRsub x (hKsub x hx))).1).1,
               hKcard, hKclq⟩

/-- **Common-Non-Neighbor Bound:**
    If `x, y` are distinct non-adjacent vertices disjoint from `A`, and `R(x, y) = {w ∈ A : ¬adj x w ∧ ¬adj y w}`
    satisfies `|R(x, y)| ≤ M`, then `degIn G A x + degIn G A y ≥ |A| - M`. -/
theorem common_nonnbr_deg_sum {n : Nat} (G : SGraph n) (A : Fin n → Bool) (x y : Fin n) (M : Nat)
    (hR : subsetCard (fun w => A w && !G.adj x w && !G.adj y w) ≤ M) :
    degIn G A x + degIn G A y + M ≥ subsetCard A := by
  have hp1 := filter_length_partition (verts n) A (fun w => G.adj x w)
  have hp2 := filter_length_partition (verts n) (fun w => A w && !G.adj x w) (fun w => G.adj y w)
  have hle_y : ((verts n).filter (fun w => (A w && !G.adj x w) && G.adj y w)).length ≤
               ((verts n).filter (fun w => A w && G.adj y w)).length :=
    filter_length_le (verts n) (fun w => (A w && !G.adj x w) && G.adj y w) (fun w => A w && G.adj y w)
      (fun w _ hw => by simp only [Bool.and_eq_true] at hw ⊢; exact ⟨hw.1.1, hw.2⟩)
  unfold degIn subsetCard at *
  omega

/-- **Lemma 4 (`no_25_alpha_le_4_e_le_81`):**
    In any balanced 6-coloring of `K₃₇`, NO 25-vertex subset `U` of `G_c` with `α(G_c[U]) ≤ 4`
    can satisfy `twoEdgesIn G_c U ≤ 162` (i.e. `edgesIn G_c U ≤ 81`). -/
theorem no_25_alpha_le_4_e_le_81 (C : EdgeColoring (6 * 6 + 1) 6) (hbal : IsBalanced C)
    (c : Fin 6) (U : Fin (6 * 6 + 1) → Bool) (hUcard : subsetCard U = 25)
    (h2eU : twoEdgesIn (colorClass C c) U ≤ 162) :
    ¬ (∀ I : Fin (6 * 6 + 1) → Bool, (∀ v, I v = true → U v = true) →
        IsIndep (colorClass C c) I → subsetCard I ≤ 4) := by
  intro hα4
  let G := colorClass C c
  -- Step 1: U contains NO K₆ (by Lemma 2 + extend_indep_with_K6)
  have hnoK6 : ¬ HasK6In G U := by
    rintro ⟨K, hKsub, hKcard, hKclq⟩
    let W : Fin (6 * 6 + 1) → Bool := fun v => U v && !K v
    have hWcard : subsetCard W = 19 := by
      unfold subsetCard
      have hp := filter_length_partition (verts (6 * 6 + 1)) U K
      have h1 : ((verts (6 * 6 + 1)).filter (fun v => U v && K v)).length = 6 := by
        have heq : ((verts (6 * 6 + 1)).filter (fun v => U v && K v)).length = subsetCard K := by
          unfold subsetCard; apply filter_length_eq; intro v _
          cases h : K v
          · simp
          · simp [hKsub v h]
        rw [heq, hKcard]
      unfold subsetCard at hUcard
      change ((verts (6 * 6 + 1)).filter (fun v => U v && !K v)).length = 19
      omega
    have hnoα3 := no_19_alpha_le_3 C hbal c W hWcard
    have hexI : ∃ I : Fin (6 * 6 + 1) → Bool, (∀ v, I v = true → W v = true) ∧
        IsIndep G I ∧ subsetCard I = 4 := by
      apply Classical.byContradiction; intro hnone
      apply hnoα3; intro I hIsub hIind
      by_cases hle3 : subsetCard I ≤ 3
      · exact hle3
      · exfalso
        obtain ⟨I4, hI4sub, hI4card⟩ := exists_sub_card I 4 (by omega)
        exact hnone ⟨I4, fun v hv => hIsub v (hI4sub v hv), isIndep_mono hI4sub hIind, hI4card⟩
    obtain ⟨I, hIsub, hIind, hIcard⟩ := hexI
    have hdisj : ∀ v, I v = true → K v = false := by
      intro v hv; have := (Bool.and_eq_true _ _ |>.mp (hIsub v hv)).2; simpa using this
    obtain ⟨u, hKu, _, hI'ind, hI'card⟩ := extend_indep_with_K6 C hbal c K I hKcard hKclq hdisj hIind (by omega)
    have hI'sub : ∀ x, (I x || decide (x = u)) = true → U x = true := by
      intro x hx
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hx
      rcases hx with hIx | rfl
      · exact (Bool.and_eq_true _ _ |>.mp (hIsub x hIx)).1
      · exact hKsub x hKu
    have := hα4 (fun x => I x || decide (x = u)) hI'sub hI'ind
    omega
  -- Step 2: Pick min-degree vertex v ∈ U ⇒ degIn G U v = 6!
  obtain ⟨v, hvU, hvmin⟩ := exists_min_degIn G U (by omega)
  have hdeg_le6 : degIn G U v ≤ 6 := by
    have hlb := crossEdges_le_sum_degIn G U U (degIn G U v) hvmin
    rw [crossEdges_self, hUcard] at hlb
    dsimp [G] at hlb ⊢; omega
  obtain ⟨hBcard, hcard_sum, hdisjAB, hunionAB, hcross_eq, hU_eq, hαA⟩ := peel_at_min_vertex G U v hvU hvmin
  let B : Fin (6 * 6 + 1) → Bool := fun w => U w && (decide (w = v) || G.adj v w)
  let A : Fin (6 * 6 + 1) → Bool := fun w => U w && !decide (w = v) && !G.adj v w
  have hBc : subsetCard B = degIn G U v + 1 := hBcard
  have hcs : subsetCard A + subsetCard B = subsetCard U := hcard_sum
  have hdeg_eq6 : degIn G U v = 6 := by
    by_cases hle5 : degIn G U v ≤ 5
    · exfalso
      have hA19 : subsetCard A ≥ 19 := by omega
      obtain ⟨W19, hW19sub, hW19card⟩ := exists_sub_card A 19 hA19
      exact no_19_alpha_le_3 C hbal c W19 hW19card
        (fun I hIsub hIind => hαA 3 hα4 I (fun w hw => hW19sub w (hIsub w hw)) hIind)
    · omega
  have hBc7 : subsetCard B = 7 := by omega
  have hAc18 : subsetCard A = 18 := by omega
  -- Step 3: Lemma 3 on A (|A| = 18, K₆-free, α ≤ 3) gives twoEdgesIn G A ≥ 108!
  have hnoK6A : ¬ HasK6In G A := fun ⟨K, hKs, hKc, hKclq⟩ =>
    hnoK6 ⟨K, fun w hw => (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp (hKs w hw)).1).1, hKc, hKclq⟩
  have h2eA : twoEdgesIn G A ≥ 108 := K6_free_18_edges_ge_54 C hbal c A hAc18 (hαA 3 hα4) hnoK6A
  -- Step 4: multiscale_turan_complement (k = 1) on B (|B| = 7) gives twoEdgesIn G.compl B ≥ 10!
  have hmsB := multiscale_turan_complement C hbal c B 1
  have hteB := two_mul_edgesIn G.compl B
  have hmB10 : twoEdgesIn G.compl B ≥ 10 := by
    dsimp [G] at hteB ⊢; rw [hBc7, hteB] at hmsB; omega
  have hcross_le12 : crossEdges G A B ≤ 12 := by
    dsimp [G, A, B] at h2eA hBc7 hcross_eq hU_eq hmB10 ⊢
    rw [hBc7] at hU_eq
    omega
  -- Step 5: 2-matching {a1, b1}, {a2, b2} in G.compl[B]
  have hnoK6B : ¬ HasK6In G B := fun ⟨K, hKs, hKc, hKclq⟩ =>
    hnoK6 ⟨K, fun w hw => (Bool.and_eq_true _ _ |>.mp (hKs w hw)).1, hKc, hKclq⟩
  obtain ⟨a1, b1, a2, b2, hBa1, hBb1, hBa2, hBb2, h12, h13, h14, h23, h24, h34, hna1, hna2⟩ :=
    exists_two_matching_in_B G B hBc7 hmB10 hnoK6B
  -- Step 6: For any non-edge {x, y} in B, degIn G A x + degIn G A y ≥ 7 (by Lemma 1 on R(x, y))!
  have hpair_ge7 : ∀ x y : Fin (6 * 6 + 1), B x = true → B y = true → x ≠ y → G.adj x y = false →
      degIn G A x + degIn G A y ≥ 7 := by
    intro x y hBx hBy hxy hnxy
    let Rxy : Fin (6 * 6 + 1) → Bool := fun w => A w && !G.adj x w && !G.adj y w
    have hRle11 : subsetCard Rxy ≤ 11 := by
      by_cases h11 : subsetCard Rxy ≤ 11
      · exact h11
      · exfalso
        obtain ⟨R12, hR12sub, hR12card⟩ := exists_sub_card Rxy 12 (by omega)
        have hαR12 : ∀ I, (∀ w, I w = true → R12 w = true) → IsIndep G I → subsetCard I ≤ 2 := by
          intro I hIsub hIind
          let I' : Fin (6 * 6 + 1) → Bool := fun w => I w || decide (w = x) || decide (w = y)
          have hI_in_Rxy : ∀ w, I w = true → Rxy w = true := fun w hw => hR12sub w (hIsub w hw)
          have hI_not_x : I x = false := by
            by_cases h : I x = true
            · have hAx : A x = true := (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp (hI_in_Rxy x h)).1).1
              have := hdisjAB x; dsimp [A, B] at hAx hBx; simp [hAx, hBx] at this
            · cases hi : I x; rfl; exact absurd hi h
          have hI_not_y : I y = false := by
            by_cases h : I y = true
            · have hAy : A y = true := (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp (hI_in_Rxy y h)).1).1
              have := hdisjAB y; dsimp [A, B] at hAy hBy; simp [hAy, hBy] at this
            · cases hi : I y; rfl; exact absurd hi h
          have hI'sub : ∀ w, I' w = true → U w = true := by
            intro w hw
            simp only [I', Bool.or_eq_true, decide_eq_true_eq] at hw
            rcases hw with (hIw | hw) | hw
            · have hAw := (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp (hI_in_Rxy w hIw)).1).1
              rw [hunionAB w]; dsimp [A] at hAw; simp [hAw]
            · subst hw; rw [hunionAB w]; dsimp [B] at hBx; simp [hBx]
            · subst hw; rw [hunionAB w]; dsimp [B] at hBy; simp [hBy]
          have hI'ind : IsIndep G I' := by
            intro p q hp hq
            simp only [I', Bool.or_eq_true, decide_eq_true_eq] at hp hq
            rcases hp with (hIp | rfl) | rfl <;> rcases hq with (hIq | rfl) | rfl
            · exact hIind p q hIp hIq
            · rw [G.symm]; have := (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp (hI_in_Rxy p hIp)).1).2; simpa using this
            · rw [G.symm]; have := (Bool.and_eq_true _ _ |>.mp (hI_in_Rxy p hIp)).2; simpa using this
            · have := (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp (hI_in_Rxy q hIq)).1).2; simpa using this
            · exact G.loopless _
            · exact hnxy
            · have := (Bool.and_eq_true _ _ |>.mp (hI_in_Rxy q hIq)).2; simpa using this
            · rw [G.symm]; exact hnxy
            · exact G.loopless _
          have hI'card : subsetCard I' = subsetCard I + 2 := by
            unfold subsetCard
            have hp1 := filter_length_partition (verts (6 * 6 + 1)) I' (fun w => decide (w = x))
            have h1 : ((verts (6 * 6 + 1)).filter (fun w => I' w && decide (w = x))).length = 1 := by
              have heq : ((verts (6 * 6 + 1)).filter (fun w => I' w && decide (w = x))).length =
                         ((verts (6 * 6 + 1)).filter (fun w => decide (w = x))).length := by
                apply filter_length_eq; intro w _
                by_cases hw : w = x
                · subst hw; simp [I']
                · simp [I', hw]
              rw [heq]; exact length_filter_eq_one_of_nodup _ (nodup_verts _) x (mem_verts x)
            have hp2 := filter_length_partition (verts (6 * 6 + 1)) (fun w => I' w && !decide (w = x)) (fun w => decide (w = y))
            have h2 : ((verts (6 * 6 + 1)).filter (fun w => (I' w && !decide (w = x)) && decide (w = y))).length = 1 := by
              have heq : ((verts (6 * 6 + 1)).filter (fun w => (I' w && !decide (w = x)) && decide (w = y))).length =
                         ((verts (6 * 6 + 1)).filter (fun w => decide (w = y))).length := by
                apply filter_length_eq; intro w _
                by_cases hw : w = y
                · subst hw; simp [I', Ne.symm hxy]
                · simp [I', hw]
              rw [heq]; exact length_filter_eq_one_of_nodup _ (nodup_verts _) y (mem_verts y)
            have h3 : ((verts (6 * 6 + 1)).filter (fun w => (I' w && !decide (w = x)) && !decide (w = y))).length =
                      ((verts (6 * 6 + 1)).filter I).length := by
              apply filter_length_eq; intro w _
              by_cases hwx : w = x
              · subst hwx; simp [I', hI_not_x]
              · by_cases hwy : w = y
                · subst hwy; simp [I', hI_not_y]
                · simp [I', hwx, hwy]
            omega
          have := hα4 I' hI'sub hI'ind
          omega
        obtain ⟨K, hKsub, hKcard, hKclq⟩ := no_12_alpha_le_2_K6_free C hbal c R12 hR12card hαR12
        exact hnoK6 ⟨K, fun w hw => by
          have hAw := (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp (hR12sub w (hKsub w hw))).1).1
          rw [hunionAB w]; dsimp [A] at hAw; simp [hAw], hKcard, hKclq⟩
    have hsum := common_nonnbr_deg_sum G A x y 11 hRle11
    rw [hAc18] at hsum
    omega
  have hp1 := hpair_ge7 a1 b1 hBa1 hBb1 h12 hna1
  have hp2 := hpair_ge7 a2 b2 hBa2 hBb2 h34 hna2
  -- Sum over the 4 distinct vertices {a1, b1, a2, b2} ⊆ B is ≤ crossEdges G B A = crossEdges G A B ≤ 12!
  have h4le : degIn G A a1 + degIn G A b1 + degIn G A a2 + degIn G A b2 ≤ crossEdges G B A := by
    let f : Fin (6 * 6 + 1) → Nat := fun u => if B u then degIn G A u else 0
    have hsum_4 : ∀ (l : List (Fin (6 * 6 + 1))), l.Nodup →
        a1 ∈ l → b1 ∈ l → a2 ∈ l → b2 ∈ l →
        f a1 + f b1 + f a2 + f b2 ≤ (l.map f).sum := by
      intro l hnd ha1 hb1 ha2 hb2
      let p4 : Fin (6 * 6 + 1) → Bool := fun u =>
        decide (u = a1) || decide (u = b1) || decide (u = a2) || decide (u = b2)
      have hle_sum : ((l.filter p4).map f).sum ≤ (l.map f).sum := by
        rw [sum_filter_eq_sum_ite]
        apply sum_map_le; intro u _; by_cases h : p4 u = true <;> simp [h]
      have h4eq : ((l.filter p4).map f).sum = f a1 + f b1 + f a2 + f b2 := by
        rw [sum_filter_eq_sum_ite]
        have hsp : (l.map (fun u => if p4 u then f u else 0)).sum =
            (l.map (fun u => if u = a1 then f u else 0)).sum +
            (l.map (fun u => if u = b1 then f u else 0)).sum +
            (l.map (fun u => if u = a2 then f u else 0)).sum +
            (l.map (fun u => if u = b2 then f u else 0)).sum := by
          rw [← sum_map_add, ← sum_map_add, ← sum_map_add]
          apply sum_map_eq; intro u _
          by_cases h1 : u = a1
          · subst h1; simp [p4, h12, h13, h14]
          · by_cases h2 : u = b1
            · subst h2; simp [p4, Ne.symm h12, h23, h24]
            · by_cases h3 : u = a2
              · subst h3; simp [p4, Ne.symm h13, Ne.symm h23, h34]
              · by_cases h4 : u = b2
                · subst h4; simp [p4, Ne.symm h14, Ne.symm h24, Ne.symm h34]
                · simp [p4, h1, h2, h3, h4]
        have hsing : ∀ z : Fin (6 * 6 + 1), z ∈ l → (l.map (fun u => if u = z then f u else 0)).sum = f z := by
          intro z hz
          clear hle_sum hsp ha1 hb1 ha2 hb2
          induction l with
          | nil => cases hz
          | cons y ys ih =>
            rw [List.nodup_cons] at hnd
            rcases List.mem_cons.mp hz with rfl | hz'
            · simp only [List.map_cons, ↓reduceIte, List.sum_cons]
              have h0 : (ys.map (fun u => if u = z then f u else 0)).sum = 0 :=
                sum_map_eq_zero _ _ (fun w hw => by
                  have : w ≠ z := fun h => hnd.1 (h ▸ hw)
                  simp [this])
              omega
            · have hne : y ≠ z := fun h => hnd.1 (h ▸ hz')
              simp only [List.map_cons, hne, ↓reduceIte, List.sum_cons, Nat.zero_add]
              exact ih hnd.2 hz'
        rw [hsp, hsing a1 ha1, hsing b1 hb1, hsing a2 ha2, hsing b2 hb2]
      omega
    have h := hsum_4 (verts (6 * 6 + 1)) (nodup_verts _) (mem_verts a1) (mem_verts b1) (mem_verts a2) (mem_verts b2)
    dsimp [f] at h
    simp only [hBa1, hBb1, hBa2, hBb2, ↓reduceIte] at h
    exact h
  rw [crossEdges_symm G B A] at h4le
  omega

/-! ## Section 4: Lemmas 5, 6, 7, and 8 (`N = 24`, max-degree deletion, `N = 31`, `30`) -/

/-- Helper: deleting one vertex `u ∈ A` decreases `subsetCard A` by 1 and `twoEdgesIn G A` by `2 * degIn G A u`. -/
theorem erase_vertex_stats {n : Nat} (G : SGraph n) (A : Fin n → Bool) (u : Fin n) (hu : A u = true) :
    subsetCard (fun w => A w && !decide (w = u)) + 1 = subsetCard A ∧
    twoEdgesIn G (fun w => A w && !decide (w = u)) + 2 * degIn G A u = twoEdgesIn G A := by
  let A' : Fin n → Bool := fun w => A w && !decide (w = u)
  let S : Fin n → Bool := fun w => decide (w = u)
  have hdisj : ∀ w, !(A' w && S w) = true := by
    intro w; by_cases hw : w = u <;> simp [A', S, hw]
  have hunion : ∀ w, A w = (A' w || S w) := by
    intro w; by_cases hw : w = u
    · subst hw; simp [A', S, hu]
    · simp [A', S, hw]
  have hcard : subsetCard A' + 1 = subsetCard A := by
    have hp := filter_length_partition (verts n) A S
    have h1 : ((verts n).filter (fun w => A w && S w)).length = 1 := by
      have heq : ((verts n).filter (fun w => A w && S w)).length = ((verts n).filter S).length := by
        apply filter_length_eq; intro w _
        by_cases hw : w = u
        · subst hw; simp [S, hu]
        · simp [S, hw]
      rw [heq]; exact length_filter_eq_one_of_nodup (verts n) (nodup_verts n) u (mem_verts u)
    unfold subsetCard; dsimp [A', S] at *; omega
  have h2e : twoEdgesIn G A' + 2 * degIn G A u = twoEdgesIn G A := by
    have hsplit : twoEdgesIn G A = twoEdgesIn G A' + twoEdgesIn G S + 2 * crossEdges G A' S := by
      have h := twoEdgesIn_union_disjoint G A' S hdisj
      have hcongr : twoEdgesIn G A = twoEdgesIn G (fun w => A' w || S w) := by
        rw [twoEdgesIn_eq_double_sum, twoEdgesIn_eq_double_sum]
        apply sum_map_eq; intro x _; apply sum_map_eq; intro y _
        rw [hunion x, hunion y]
      rw [hcongr, h]
    have hS0 : twoEdgesIn G S = 0 := by
      rw [twoEdgesIn_eq_double_sum]
      apply sum_map_eq_zero; intro x _; apply sum_map_eq_zero; intro y _
      by_cases hx : x = u
      · subst hx
        by_cases hy : y = x
        · subst hy; simp [S, G.loopless]
        · simp [S, hy]
      · simp [S, hx]
    have hcross : crossEdges G A' S = degIn G A u := by
      rw [crossEdges_symm G A' S]
      unfold crossEdges
      have hsing : ∀ (l : List (Fin n)), l.Nodup → u ∈ l →
          (l.map (fun w => if S w = true then degIn G A' w else 0)).sum = degIn G A' u := by
        intro l hnd hum
        induction l with
        | nil => cases hum
        | cons y ys ih =>
          rw [List.nodup_cons] at hnd
          rcases List.mem_cons.mp hum with rfl | hum'
          · simp only [S, List.map_cons, decide_true, ↓reduceIte, List.sum_cons]
            have h0 : (ys.map (fun w => if decide (w = u) = true then degIn G A' w else 0)).sum = 0 :=
              sum_map_eq_zero _ _ (fun w hw => by
                have hne : w ≠ u := fun h => hnd.1 (h ▸ hw)
                simp [hne])
            omega
          · have hne : y ≠ u := fun h => hnd.1 (h ▸ hum')
            simp only [S, List.map_cons, hne, decide_false, Bool.false_eq_true, ↓reduceIte, List.sum_cons, Nat.zero_add]
            exact ih hnd.2 hum'
      rw [hsing (verts n) (nodup_verts n) (mem_verts u)]
      unfold degIn; apply filter_length_eq; intro w _
      by_cases hw : w = u
      · subst hw; simp [A', G.loopless]
      · simp [A', hw]
    omega
  exact ⟨hcard, h2e⟩

/-- Helper: every nonempty vertex subset has a maximum-degree vertex. -/
theorem exists_max_degIn {n : Nat} (G : SGraph n) (A : Fin n → Bool) (hA : subsetCard A ≥ 1) :
    ∃ u : Fin n, A u = true ∧ ∀ w : Fin n, A w = true → degIn G A w ≤ degIn G A u := by
  have haux : ∀ (l : List (Fin n)), (l.filter A).length ≥ 1 →
      ∃ u ∈ l, A u = true ∧ ∀ w ∈ l, A w = true → degIn G A w ≤ degIn G A u := by
    intro l
    induction l with
    | nil => intro h; simp at h
    | cons x xs ih =>
      intro hlen
      cases hAx : A x
      · simp [hAx] at hlen
        obtain ⟨u, hu, hAu, hmax⟩ := ih hlen
        refine ⟨u, List.mem_cons_of_mem _ hu, hAu, fun w hw hAw => ?_⟩
        rcases List.mem_cons.mp hw with rfl | hw'
        · simp [hAx] at hAw
        · exact hmax w hw' hAw
      · by_cases hxs : (xs.filter A).length ≥ 1
        · obtain ⟨u, hu, hAu, hmax⟩ := ih hxs
          by_cases hle : degIn G A x ≤ degIn G A u
          · refine ⟨u, List.mem_cons_of_mem _ hu, hAu, fun w hw hAw => ?_⟩
            rcases List.mem_cons.mp hw with rfl | hw'
            · exact hle
            · exact hmax w hw' hAw
          · refine ⟨x, List.mem_cons_self, hAx, fun w hw hAw => ?_⟩
            rcases List.mem_cons.mp hw with rfl | hw'
            · exact Nat.le_refl _
            · have := hmax w hw' hAw; omega
        · refine ⟨x, List.mem_cons_self, hAx, fun w hw hAw => ?_⟩
          rcases List.mem_cons.mp hw with rfl | hw'
          · exact Nat.le_refl _
          · exfalso
            have hmem : w ∈ xs.filter A := List.mem_filter.mpr ⟨hw', hAw⟩
            have hpos : (xs.filter A).length ≥ 1 := by
              cases hf : xs.filter A with
              | nil => rw [hf] at hmem; cases hmem
              | cons _ _ => simp
            omega
  obtain ⟨u, _, hAu, hmax⟩ := haux (verts n) hA
  exact ⟨u, hAu, fun w hAw => hmax w (mem_verts w) hAw⟩

/-- Helper: monotonicity of `twoEdgesIn` under subset inclusion. -/
theorem twoEdgesIn_mono {n : Nat} (G : SGraph n) {A' A : Fin n → Bool}
    (hsub : ∀ w, A' w = true → A w = true) :
    twoEdgesIn G A' ≤ twoEdgesIn G A := by
  rw [twoEdgesIn_eq_double_sum, twoEdgesIn_eq_double_sum]
  apply sum_map_le; intro u _; apply sum_map_le; intro v _
  by_cases h : (A' u && A' v && G.adj u v) = true
  · have h1 := Bool.and_eq_true _ _ |>.mp h
    have h2 := Bool.and_eq_true _ _ |>.mp h1.1
    simp [h1.2, h2.1, h2.2, hsub u h2.1, hsub v h2.2]
  · have hf : (A' u && A' v && G.adj u v) = false := by
      cases hc : A' u && A' v && G.adj u v; rfl; exact absurd hc h
    rw [hf]; simp

/-- Helper: sum of `degIn G A` over 4 distinct vertices in `B` is at most `crossEdges G A B`. -/
theorem sum_4_degIn_le_crossEdges {n : Nat} (G : SGraph n) (A B : Fin n → Bool)
    (a1 b1 a2 b2 : Fin n)
    (hBa1 : B a1 = true) (hBb1 : B b1 = true) (hBa2 : B a2 = true) (hBb2 : B b2 = true)
    (h12 : a1 ≠ b1) (h13 : a1 ≠ a2) (h14 : a1 ≠ b2)
    (h23 : b1 ≠ a2) (h24 : b1 ≠ b2) (h34 : a2 ≠ b2) :
    degIn G A a1 + degIn G A b1 + degIn G A a2 + degIn G A b2 ≤ crossEdges G A B := by
  rw [crossEdges_symm G A B]
  let f : Fin n → Nat := fun u => if B u then degIn G A u else 0
  have hsum_4 : ∀ (l : List (Fin n)), l.Nodup →
      a1 ∈ l → b1 ∈ l → a2 ∈ l → b2 ∈ l →
      f a1 + f b1 + f a2 + f b2 ≤ (l.map f).sum := by
    intro l hnd ha1 hb1 ha2 hb2
    let p4 : Fin n → Bool := fun u =>
      decide (u = a1) || decide (u = b1) || decide (u = a2) || decide (u = b2)
    have hle_sum : ((l.filter p4).map f).sum ≤ (l.map f).sum := by
      rw [sum_filter_eq_sum_ite]
      apply sum_map_le; intro u _; by_cases h : p4 u = true <;> simp [h]
    have h4eq : ((l.filter p4).map f).sum = f a1 + f b1 + f a2 + f b2 := by
      rw [sum_filter_eq_sum_ite]
      have hsp : (l.map (fun u => if p4 u then f u else 0)).sum =
          (l.map (fun u => if u = a1 then f u else 0)).sum +
          (l.map (fun u => if u = b1 then f u else 0)).sum +
          (l.map (fun u => if u = a2 then f u else 0)).sum +
          (l.map (fun u => if u = b2 then f u else 0)).sum := by
        rw [← sum_map_add, ← sum_map_add, ← sum_map_add]
        apply sum_map_eq; intro u _
        by_cases h1 : u = a1
        · subst h1; simp [p4, h12, h13, h14]
        · by_cases h2 : u = b1
          · subst h2; simp [p4, Ne.symm h12, h23, h24]
          · by_cases h3 : u = a2
            · subst h3; simp [p4, Ne.symm h13, Ne.symm h23, h34]
            · by_cases h4 : u = b2
              · subst h4; simp [p4, Ne.symm h14, Ne.symm h24, Ne.symm h34]
              · simp [p4, h1, h2, h3, h4]
      have hsing : ∀ z : Fin n, z ∈ l → (l.map (fun u => if u = z then f u else 0)).sum = f z := by
        intro z hz
        clear hle_sum hsp ha1 hb1 ha2 hb2
        induction l with
        | nil => cases hz
        | cons y ys ih =>
          rw [List.nodup_cons] at hnd
          rcases List.mem_cons.mp hz with rfl | hz'
          · simp only [List.map_cons, ↓reduceIte, List.sum_cons]
            have h0 : (ys.map (fun u => if u = z then f u else 0)).sum = 0 :=
              sum_map_eq_zero _ _ (fun w hw => by
                have : w ≠ z := fun h => hnd.1 (h ▸ hw)
                simp [this])
            omega
          · have hne : y ≠ z := fun h => hnd.1 (h ▸ hz')
            simp only [List.map_cons, hne, ↓reduceIte, List.sum_cons, Nat.zero_add]
            exact ih hnd.2 hz'
      rw [hsp, hsing a1 ha1, hsing b1 hb1, hsing a2 ha2, hsing b2 hb2]
    omega
  have h := hsum_4 (verts n) (nodup_verts n) (mem_verts a1) (mem_verts b1) (mem_verts a2) (mem_verts b2)
  dsimp [f] at h
  simp only [hBa1, hBb1, hBa2, hBb2, ↓reduceIte] at h
  exact h

/-- **Lemma 5 (`K6_free_24_edges_ge_70`):**
    Every `K₆`-free 24-vertex subset `A` of `G_c` with `α(G_c[A]) ≤ 4` has `twoEdgesIn G_c A ≥ 140`
    (i.e. `edgesIn G_c A ≥ 70`). -/
theorem K6_free_24_edges_ge_70 (C : EdgeColoring (6 * 6 + 1) 6) (hbal : IsBalanced C)
    (c : Fin 6) (A : Fin (6 * 6 + 1) → Bool) (hAcard : subsetCard A = 24)
    (hα4 : ∀ I, (∀ v, I v = true → A v = true) → IsIndep (colorClass C c) I → subsetCard I ≤ 4)
    (hnoK6 : ¬ HasK6In (colorClass C c) A) :
    twoEdgesIn (colorClass C c) A ≥ 140 := by
  apply Classical.byContradiction
  intro hlt
  let G := colorClass C c
  obtain ⟨w, hwA, hwmin⟩ := exists_min_degIn G A (by omega)
  have hdeg_le5 : degIn G A w ≤ 5 := by
    have hlb := crossEdges_le_sum_degIn G A A (degIn G A w) hwmin
    rw [crossEdges_self, hAcard] at hlb
    dsimp [G] at hlb ⊢; omega
  obtain ⟨hBcard, hcard_sum, _, _, _, hA_eq, hαA'⟩ := peel_at_min_vertex G A w hwA hwmin
  let Bw : Fin (6 * 6 + 1) → Bool := fun x => A x && (decide (x = w) || G.adj w x)
  let A' : Fin (6 * 6 + 1) → Bool := fun x => A x && !decide (x = w) && !G.adj w x
  have hBc : subsetCard Bw = degIn G A w + 1 := hBcard
  have hcs : subsetCard A' + subsetCard Bw = subsetCard A := hcard_sum
  have hdeg_eq5 : degIn G A w = 5 := by
    by_cases hle4 : degIn G A w ≤ 4
    · exfalso
      have hA'19 : subsetCard A' ≥ 19 := by omega
      obtain ⟨W19, hW19sub, hW19card⟩ := exists_sub_card A' 19 hA'19
      exact no_19_alpha_le_3 C hbal c W19 hW19card
        (fun I hIsub hIind => hαA' 3 hα4 I (fun x hx => hW19sub x (hIsub x hx)) hIind)
    · omega
  have hBc6 : subsetCard Bw = 6 := by omega
  have hA'18 : subsetCard A' = 18 := by omega
  -- Bw is NOT a K₆ (since A is K₆-free), hence edgesIn G.compl Bw ≥ 1 ⇒ twoEdgesIn G.compl Bw ≥ 2!
  have hcompl_ge2 : twoEdgesIn G.compl Bw ≥ 2 := by
    have hpar := two_mul_edgesIn G.compl Bw
    by_cases h0 : edgesIn G.compl Bw = 0
    · exfalso
      exact hnoK6 ⟨Bw, fun x hx => (Bool.and_eq_true _ _ |>.mp hx).1, hBc6, h0⟩
    · omega
  -- By Lemma 3 on A' (|A'| = 18, K₆-free, α ≤ 3), twoEdgesIn G A' ≥ 108!
  have hnoK6A' : ¬ HasK6In G A' := fun ⟨K, hKs, hKc, hKclq⟩ =>
    hnoK6 ⟨K, fun x hx => (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp (hKs x hx)).1).1, hKc, hKclq⟩
  have h2eA' : twoEdgesIn G A' ≥ 108 := K6_free_18_edges_ge_54 C hbal c A' hA'18 (hαA' 3 hα4) hnoK6A'
  dsimp [G, A', Bw] at h2eA' hBc6 hcompl_ge2 hA_eq
  rw [hBc6] at hA_eq
  omega

/-- **Lemma 6 (`exists_sub_card_twoEdges_le` — Max-Degree Deletion Helper):**
    If `|A| ≥ M`, `E2 + 1 > 5 * |A|`, and `twoEdgesIn G A ≤ E2 + 12 * (|A| - M)`,
    then `A` contains a subset `A'` of size `M` with `twoEdgesIn G A' ≤ E2`.
    (Repeatedly deletes a maximum-degree vertex of degree ≥ 6 while `twoEdgesIn > E2`.) -/
theorem exists_sub_card_twoEdges_le {n : Nat} (G : SGraph n) (M E2 : Nat) :
    ∀ t : Nat, ∀ A : Fin n → Bool,
      subsetCard A = M + t →
      E2 + 1 > 5 * subsetCard A →
      twoEdgesIn G A ≤ E2 + 12 * t →
      ∃ A' : Fin n → Bool, (∀ w, A' w = true → A w = true) ∧
        subsetCard A' = M ∧ twoEdgesIn G A' ≤ E2 := by
  intro t
  induction t with
  | zero =>
    intro A hAcard _ h2e
    exact ⟨A, fun _ h => h, by omega, by omega⟩
  | succ t ih =>
    intro A hAcard hthresh h2e
    by_cases hle : twoEdgesIn G A ≤ E2
    · obtain ⟨A', hA'sub, hA'card⟩ := exists_sub_card A M (by omega)
      exact ⟨A', hA'sub, hA'card, Nat.le_trans (twoEdgesIn_mono G hA'sub) hle⟩
    · -- Since twoEdgesIn G A ≥ E2 + 1 > 5 * |A|, max degree in A is ≥ 6!
      have hApos : subsetCard A ≥ 1 := by omega
      obtain ⟨u, huA, humax⟩ := exists_max_degIn G A hApos
      have hdeg_ge6 : degIn G A u ≥ 6 := by
        have hsum_le : twoEdgesIn G A ≤ subsetCard A * degIn G A u := by
          unfold twoEdgesIn
          have h := sum_map_le ((verts n).filter A) (degIn G A) (fun _ => degIn G A u)
            (fun w hw => humax w (List.mem_filter.mp hw).2)
          rw [sum_map_const] at h
          exact h
        by_cases hd5 : degIn G A u ≤ 5
        · have : subsetCard A * degIn G A u ≤ 5 * subsetCard A := by
            have := Nat.mul_le_mul_left (subsetCard A) hd5
            omega
          omega
        · omega
      let A1 : Fin n → Bool := fun w => A w && !decide (w = u)
      obtain ⟨hcard1, h2e1⟩ := erase_vertex_stats G A u huA
      have hA1card : subsetCard A1 = M + t := by dsimp [A1] at *; omega
      have hA1thresh : E2 + 1 > 5 * subsetCard A1 := by omega
      have hA1_2e : twoEdgesIn G A1 ≤ E2 + 12 * t := by dsimp [A1] at *; omega
      obtain ⟨A', hA'sub, hA'card, hA'2e⟩ := ih A1 hA1card hA1thresh hA1_2e
      exact ⟨A', fun w hw => (Bool.and_eq_true _ _ |>.mp (hA'sub w hw)).1, hA'card, hA'2e⟩

/-- **Lemma 7 (`no_31_alpha_le_5_e_le_96`):**
    In any balanced 6-coloring of `K₃₇`, NO 31-vertex subset `U` of `G_c` with `α(G_c[U]) ≤ 5`
    can satisfy `twoEdgesIn G_c U ≤ 192` (i.e. `edgesIn G_c U ≤ 96`). -/
theorem no_31_alpha_le_5_e_le_96 (C : EdgeColoring (6 * 6 + 1) 6) (hbal : IsBalanced C)
    (c : Fin 6) (U : Fin (6 * 6 + 1) → Bool) (hUcard : subsetCard U = 31)
    (h2eU : twoEdgesIn (colorClass C c) U ≤ 192) :
    ¬ (∀ I : Fin (6 * 6 + 1) → Bool, (∀ v, I v = true → U v = true) →
        IsIndep (colorClass C c) I → subsetCard I ≤ 5) := by
  intro hα5
  let G := colorClass C c
  -- Step 1: U contains NO K₆ (deleting K₆ leaves 25 vertices with twoEdgesIn ≤ 162, contradicting Lemma 4)
  have hnoK6 : ¬ HasK6In G U := by
    rintro ⟨K, hKsub, hKcard, hKclq⟩
    let W : Fin (6 * 6 + 1) → Bool := fun v => U v && !K v
    have hdisjKW : ∀ v, !(K v && W v) = true := by
      intro v; by_cases h : K v = true <;> simp [W, h]
    have hunionKW : ∀ v, U v = (K v || W v) := by
      intro v; cases hK : K v
      · simp [W, hK]
      · simp [W, hKsub v hK]
    have hWcard : subsetCard W = 25 := by
      unfold subsetCard
      have hp := filter_length_partition (verts (6 * 6 + 1)) U K
      have h1 : ((verts (6 * 6 + 1)).filter (fun v => U v && K v)).length = 6 := by
        have heq : ((verts (6 * 6 + 1)).filter (fun v => U v && K v)).length = subsetCard K := by
          unfold subsetCard; apply filter_length_eq; intro v _
          cases h : K v; simp; simp [hKsub v h]
        rw [heq, hKcard]
      unfold subsetCard at hUcard
      change ((verts (6 * 6 + 1)).filter (fun v => U v && !K v)).length = 25
      omega
    have h2eK : twoEdgesIn G K = 30 := by
      have hcomp := twoEdgesIn_add_compl G K
      have hte := two_mul_edgesIn G.compl K
      rw [hKcard] at hcomp
      rw [hKclq] at hte
      omega
    have h2eW : twoEdgesIn G W ≤ 162 := by
      have hsplit : twoEdgesIn G U = twoEdgesIn G K + twoEdgesIn G W + 2 * crossEdges G K W := by
        have h := twoEdgesIn_union_disjoint G K W hdisjKW
        have hcongr : twoEdgesIn G U = twoEdgesIn G (fun v => K v || W v) := by
          rw [twoEdgesIn_eq_double_sum, twoEdgesIn_eq_double_sum]
          apply sum_map_eq; intro x _; apply sum_map_eq; intro y _
          rw [hunionKW x, hunionKW y]
        rw [hcongr, h]
      dsimp [G] at hsplit h2eK ⊢; omega
    have hnoα4 := no_25_alpha_le_4_e_le_81 C hbal c W hWcard h2eW
    have hexI : ∃ I : Fin (6 * 6 + 1) → Bool, (∀ v, I v = true → W v = true) ∧
        IsIndep G I ∧ subsetCard I = 5 := by
      apply Classical.byContradiction; intro hnone
      apply hnoα4; intro I hIsub hIind
      by_cases hle4 : subsetCard I ≤ 4
      · exact hle4
      · exfalso
        obtain ⟨I5, hI5sub, hI5card⟩ := exists_sub_card I 5 (by omega)
        exact hnone ⟨I5, fun v hv => hIsub v (hI5sub v hv), isIndep_mono hI5sub hIind, hI5card⟩
    obtain ⟨I, hIsub, hIind, hIcard⟩ := hexI
    have hdisj : ∀ v, I v = true → K v = false := by
      intro v hv; have := (Bool.and_eq_true _ _ |>.mp (hIsub v hv)).2; simpa using this
    obtain ⟨u, hKu, _, hI'ind, hI'card⟩ := extend_indep_with_K6 C hbal c K I hKcard hKclq hdisj hIind (by omega)
    have hI'sub : ∀ x, (I x || decide (x = u)) = true → U x = true := by
      intro x hx
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hx
      rcases hx with hIx | rfl
      · exact (Bool.and_eq_true _ _ |>.mp (hIsub x hIx)).1
      · exact hKsub x hKu
    have := hα5 (fun x => I x || decide (x = u)) hI'sub hI'ind
    omega
  -- Step 2: Min-degree vertex v ∈ U has degIn G U v = 6!
  obtain ⟨v, hvU, hvmin⟩ := exists_min_degIn G U (by omega)
  have hdeg_le6 : degIn G U v ≤ 6 := by
    have hlb := crossEdges_le_sum_degIn G U U (degIn G U v) hvmin
    rw [crossEdges_self, hUcard] at hlb
    dsimp [G] at hlb ⊢; omega
  obtain ⟨hBcard, hcard_sum, hdisjAB, hunionAB, hcross_eq, hU_eq, hαA⟩ := peel_at_min_vertex G U v hvU hvmin
  let B : Fin (6 * 6 + 1) → Bool := fun w => U w && (decide (w = v) || G.adj v w)
  let A : Fin (6 * 6 + 1) → Bool := fun w => U w && !decide (w = v) && !G.adj v w
  have hBc : subsetCard B = degIn G U v + 1 := hBcard
  have hcs : subsetCard A + subsetCard B = subsetCard U := hcard_sum
  have hdeg_eq6 : degIn G U v = 6 := by
    by_cases hle5 : degIn G U v ≤ 5
    · exfalso
      -- |B| = b ∈ {1..6}, |A| = 31 - b ∈ {25..30}, twoEdgesIn G A ≤ 192 - b*(b-1) ≤ 162 + 12*(6 - b)!
      have hb_cases : subsetCard B = 1 ∨ subsetCard B = 2 ∨ subsetCard B = 3 ∨
                      subsetCard B = 4 ∨ subsetCard B = 5 ∨ subsetCard B = 6 := by omega
      have h2eA_ub : twoEdgesIn G A ≤ 162 + 12 * (subsetCard A - 25) := by
        have hmul_bound : subsetCard B * (subsetCard B - 1) + 12 * (subsetCard A - 25) ≥ 30 := by
          rcases hb_cases with h | h | h | h | h | h <;> (rw [h] at hcs ⊢; omega)
        dsimp [G, A, B] at hU_eq hBc hcs hmul_bound ⊢
        omega
      obtain ⟨A25, hA25sub, hA25card, hA25_2e⟩ :=
        exists_sub_card_twoEdges_le G 25 162 (subsetCard A - 25) A (by omega) (by omega) h2eA_ub
      exact no_25_alpha_le_4_e_le_81 C hbal c A25 hA25card hA25_2e
        (fun I hIsub hIind => hαA 4 hα5 I (fun w hw => hA25sub w (hIsub w hw)) hIind)
    · omega
  have hBc7 : subsetCard B = 7 := by omega
  have hAc24 : subsetCard A = 24 := by omega
  -- Step 3: Lemma 5 on A (|A| = 24, K₆-free, α ≤ 4) gives twoEdgesIn G A ≥ 140!
  have hnoK6A : ¬ HasK6In G A := fun ⟨K, hKs, hKc, hKclq⟩ =>
    hnoK6 ⟨K, fun w hw => (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp (hKs w hw)).1).1, hKc, hKclq⟩
  have h2eA : twoEdgesIn G A ≥ 140 := K6_free_24_edges_ge_70 C hbal c A hAc24 (hαA 4 hα5) hnoK6A
  -- Step 4: multiscale_turan_complement (k = 1) on B (|B| = 7) gives twoEdgesIn G.compl B ≥ 10!
  have hmsB := multiscale_turan_complement C hbal c B 1
  have hteB := two_mul_edgesIn G.compl B
  have hmB10 : twoEdgesIn G.compl B ≥ 10 := by
    dsimp [G] at hteB ⊢; rw [hBc7, hteB] at hmsB; omega
  -- From hU_eq: 192 ≥ 140 + 42 + twoEdgesIn G.compl B + 2 * D ⇒ twoEdgesIn G.compl B = 10, D = 0, crossEdges G A B = 10!
  have hcross_le10 : crossEdges G A B ≤ 10 := by
    dsimp [G, A, B] at h2eA hBc7 hcross_eq hU_eq hmB10 ⊢
    rw [hBc7] at hU_eq
    omega
  -- Step 5: 2-matching {a1, b1}, {a2, b2} in G.compl[B]
  have hnoK6B : ¬ HasK6In G B := fun ⟨K, hKs, hKc, hKclq⟩ =>
    hnoK6 ⟨K, fun w hw => (Bool.and_eq_true _ _ |>.mp (hKs w hw)).1, hKc, hKclq⟩
  obtain ⟨a1, b1, a2, b2, hBa1, hBb1, hBa2, hBb2, h12, h13, h14, h23, h24, h34, hna1, hna2⟩ :=
    exists_two_matching_in_B G B hBc7 hmB10 hnoK6B
  -- Step 6: For any non-edge {x, y} in B, R(x, y) ⊆ A has α ≤ 3, so |R(x, y)| ≤ 18 (Lemma 2),
  -- hence degIn G A x + degIn G A y ≥ 24 - 18 = 6!
  have hpair_ge6 : ∀ x y : Fin (6 * 6 + 1), B x = true → B y = true → x ≠ y → G.adj x y = false →
      degIn G A x + degIn G A y ≥ 6 := by
    intro x y hBx hBy hxy hnxy
    let Rxy : Fin (6 * 6 + 1) → Bool := fun w => A w && !G.adj x w && !G.adj y w
    have hRle18 : subsetCard Rxy ≤ 18 := by
      by_cases h18 : subsetCard Rxy ≤ 18
      · exact h18
      · exfalso
        obtain ⟨R19, hR19sub, hR19card⟩ := exists_sub_card Rxy 19 (by omega)
        apply no_19_alpha_le_3 C hbal c R19 hR19card
        intro I hIsub hIind
        let I' : Fin (6 * 6 + 1) → Bool := fun w => I w || decide (w = x) || decide (w = y)
        have hI_in_Rxy : ∀ w, I w = true → Rxy w = true := fun w hw => hR19sub w (hIsub w hw)
        have hI_not_x : I x = false := by
          by_cases h : I x = true
          · have hAx : A x = true := (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp (hI_in_Rxy x h)).1).1
            have := hdisjAB x; dsimp [A, B] at hAx hBx; simp [hAx, hBx] at this
          · cases hi : I x; rfl; exact absurd hi h
        have hI_not_y : I y = false := by
          by_cases h : I y = true
          · have hAy : A y = true := (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp (hI_in_Rxy y h)).1).1
            have := hdisjAB y; dsimp [A, B] at hAy hBy; simp [hAy, hBy] at this
          · cases hi : I y; rfl; exact absurd hi h
        have hI'sub : ∀ w, I' w = true → U w = true := by
          intro w hw
          simp only [I', Bool.or_eq_true, decide_eq_true_eq] at hw
          rcases hw with (hIw | hw) | hw
          · have hAw := (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp (hI_in_Rxy w hIw)).1).1
            rw [hunionAB w]; dsimp [A] at hAw; simp [hAw]
          · subst hw; rw [hunionAB w]; dsimp [B] at hBx; simp [hBx]
          · subst hw; rw [hunionAB w]; dsimp [B] at hBy; simp [hBy]
        have hI'ind : IsIndep G I' := by
          intro p q hp hq
          simp only [I', Bool.or_eq_true, decide_eq_true_eq] at hp hq
          rcases hp with (hIp | rfl) | rfl <;> rcases hq with (hIq | rfl) | rfl
          · exact hIind p q hIp hIq
          · rw [G.symm]; have := (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp (hI_in_Rxy p hIp)).1).2; simpa using this
          · rw [G.symm]; have := (Bool.and_eq_true _ _ |>.mp (hI_in_Rxy p hIp)).2; simpa using this
          · have := (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp (hI_in_Rxy q hIq)).1).2; simpa using this
          · exact G.loopless _
          · exact hnxy
          · have := (Bool.and_eq_true _ _ |>.mp (hI_in_Rxy q hIq)).2; simpa using this
          · rw [G.symm]; exact hnxy
          · exact G.loopless _
        have hI'card : subsetCard I' = subsetCard I + 2 := by
          unfold subsetCard
          have hp1 := filter_length_partition (verts (6 * 6 + 1)) I' (fun w => decide (w = x))
          have h1 : ((verts (6 * 6 + 1)).filter (fun w => I' w && decide (w = x))).length = 1 := by
            have heq : ((verts (6 * 6 + 1)).filter (fun w => I' w && decide (w = x))).length =
                       ((verts (6 * 6 + 1)).filter (fun w => decide (w = x))).length := by
              apply filter_length_eq; intro w _
              by_cases hw : w = x
              · subst hw; simp [I']
              · simp [I', hw]
            rw [heq]; exact length_filter_eq_one_of_nodup _ (nodup_verts _) x (mem_verts x)
          have hp2 := filter_length_partition (verts (6 * 6 + 1)) (fun w => I' w && !decide (w = x)) (fun w => decide (w = y))
          have h2 : ((verts (6 * 6 + 1)).filter (fun w => (I' w && !decide (w = x)) && decide (w = y))).length = 1 := by
            have heq : ((verts (6 * 6 + 1)).filter (fun w => (I' w && !decide (w = x)) && decide (w = y))).length =
                       ((verts (6 * 6 + 1)).filter (fun w => decide (w = y))).length := by
              apply filter_length_eq; intro w _
              by_cases hw : w = y
              · subst hw; simp [I', Ne.symm hxy]
              · simp [I', hw]
            rw [heq]; exact length_filter_eq_one_of_nodup _ (nodup_verts _) y (mem_verts y)
          have h3 : ((verts (6 * 6 + 1)).filter (fun w => (I' w && !decide (w = x)) && !decide (w = y))).length =
                    ((verts (6 * 6 + 1)).filter I).length := by
            apply filter_length_eq; intro w _
            by_cases hwx : w = x
            · subst hwx; simp [I', hI_not_x]
            · by_cases hwy : w = y
              · subst hwy; simp [I', hI_not_y]
              · simp [I', hwx, hwy]
          omega
        have := hα5 I' hI'sub hI'ind
        omega
    have hsum := common_nonnbr_deg_sum G A x y 18 hRle18
    rw [hAc24] at hsum
    omega
  have hp1 := hpair_ge6 a1 b1 hBa1 hBb1 h12 hna1
  have hp2 := hpair_ge6 a2 b2 hBa2 hBb2 h34 hna2
  have h4le := sum_4_degIn_le_crossEdges G A B a1 b1 a2 b2 hBa1 hBb1 hBa2 hBb2 h12 h13 h14 h23 h24 h34
  omega

/-- **Lemma 8 (`K6_free_30_edges_ge_86`):**
    Every `K₆`-free 30-vertex subset `A` of `G_c` with `α(G_c[A]) ≤ 5` has `twoEdgesIn G_c A ≥ 172`
    (i.e. `edgesIn G_c A ≥ 86`). -/
theorem K6_free_30_edges_ge_86 (C : EdgeColoring (6 * 6 + 1) 6) (hbal : IsBalanced C)
    (c : Fin 6) (A : Fin (6 * 6 + 1) → Bool) (hAcard : subsetCard A = 30)
    (hα5 : ∀ I, (∀ v, I v = true → A v = true) → IsIndep (colorClass C c) I → subsetCard I ≤ 5)
    (hnoK6 : ¬ HasK6In (colorClass C c) A) :
    twoEdgesIn (colorClass C c) A ≥ 172 := by
  apply Classical.byContradiction
  intro hlt
  let G := colorClass C c
  obtain ⟨w, hwA, hwmin⟩ := exists_min_degIn G A (by omega)
  have hdeg_le5 : degIn G A w ≤ 5 := by
    have hlb := crossEdges_le_sum_degIn G A A (degIn G A w) hwmin
    rw [crossEdges_self, hAcard] at hlb
    dsimp [G] at hlb ⊢; omega
  obtain ⟨hBcard, hcard_sum, _, _, _, hA_eq, hαA'⟩ := peel_at_min_vertex G A w hwA hwmin
  let Bw : Fin (6 * 6 + 1) → Bool := fun x => A x && (decide (x = w) || G.adj w x)
  let A' : Fin (6 * 6 + 1) → Bool := fun x => A x && !decide (x = w) && !G.adj w x
  have hBc : subsetCard Bw = degIn G A w + 1 := hBcard
  have hcs : subsetCard A' + subsetCard Bw = subsetCard A := hcard_sum
  have hdeg_eq5 : degIn G A w = 5 := by
    by_cases hle4 : degIn G A w ≤ 4
    · exfalso
      have hb_cases : subsetCard Bw = 1 ∨ subsetCard Bw = 2 ∨ subsetCard Bw = 3 ∨
                      subsetCard Bw = 4 ∨ subsetCard Bw = 5 := by omega
      have h2eA'_ub : twoEdgesIn G A' ≤ 162 + 12 * (subsetCard A' - 25) := by
        have hmul_bound : subsetCard Bw * (subsetCard Bw - 1) + 12 * (subsetCard A' - 25) ≥ 9 := by
          rcases hb_cases with h | h | h | h | h <;> (rw [h] at hcs ⊢; omega)
        dsimp [G, A', Bw] at hA_eq hBc hcs hmul_bound ⊢
        omega
      obtain ⟨A25, hA25sub, hA25card, hA25_2e⟩ :=
        exists_sub_card_twoEdges_le G 25 162 (subsetCard A' - 25) A' (by omega) (by omega) h2eA'_ub
      exact no_25_alpha_le_4_e_le_81 C hbal c A25 hA25card hA25_2e
        (fun I hIsub hIind => hαA' 4 hα5 I (fun x hx => hA25sub x (hIsub x hx)) hIind)
    · omega
  have hBc6 : subsetCard Bw = 6 := by omega
  have hA'24 : subsetCard A' = 24 := by omega
  -- Bw is NOT a K₆ ⇒ edgesIn G.compl Bw ≥ 1 ⇒ twoEdgesIn G.compl Bw ≥ 2!
  have hcompl_ge2 : twoEdgesIn G.compl Bw ≥ 2 := by
    have hpar := two_mul_edgesIn G.compl Bw
    by_cases h0 : edgesIn G.compl Bw = 0
    · exfalso
      exact hnoK6 ⟨Bw, fun x hx => (Bool.and_eq_true _ _ |>.mp hx).1, hBc6, h0⟩
    · omega
  -- Lemma 5 on A' (|A'| = 24, K₆-free, α ≤ 4) gives twoEdgesIn G A' ≥ 140!
  have hnoK6A' : ¬ HasK6In G A' := fun ⟨K, hKs, hKc, hKclq⟩ =>
    hnoK6 ⟨K, fun x hx => (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp (hKs x hx)).1).1, hKc, hKclq⟩
  have h2eA' : twoEdgesIn G A' ≥ 140 := K6_free_24_edges_ge_70 C hbal c A' hA'24 (hαA' 4 hα5) hnoK6A'
  dsimp [G, A', Bw] at h2eA' hBc6 hcompl_ge2 hA_eq
  rw [hBc6] at hA_eq
  omega

/-! ## Section 5: Main Theorem — Erdős Problem #617 at `r = 6` (`K₃₇`) -/

/-- Helper: if `subsetCard P ≥ 1`, there exists `v` with `P v = true`. -/
theorem exists_mem_of_subsetCard_pos {n : Nat} (P : Fin n → Bool) (hP : subsetCard P ≥ 1) :
    ∃ v : Fin n, P v = true := by
  apply Classical.byContradiction; intro hnone
  have h0 : subsetCard P = 0 := by
    unfold subsetCard
    have : (verts n).filter P = [] :=
      List.filter_eq_nil_iff.mpr (fun v _ => by
        cases h : P v
        · simp
        · exact absurd ⟨v, h⟩ hnone)
    rw [this]; rfl
  omega

/-- Helper: if `P ⊆ Q` and `subsetCard P = subsetCard Q`, then `∀ v, P v = Q v`. -/
theorem eq_of_sub_and_card_eq {n : Nat} (P Q : Fin n → Bool)
    (hsub : ∀ v, P v = true → Q v = true) (hcard : subsetCard P = subsetCard Q) :
    ∀ v, P v = Q v := by
  intro v
  cases hPv : P v
  · cases hQv : Q v
    · rfl
    · exfalso
      have hp := filter_length_partition (verts n) Q P
      have h1 : ((verts n).filter (fun w => Q w && P w)).length = subsetCard P := by
        unfold subsetCard; apply filter_length_eq; intro w _
        cases hPw : P w; simp; simp [hsub w hPw]
      have h2 : ((verts n).filter (fun w => Q w && !P w)).length ≥ 1 := by
        have hmem : v ∈ (verts n).filter (fun w => Q w && !P w) :=
          List.mem_filter.mpr ⟨mem_verts v, by simp [hQv, hPv]⟩
        cases hf : (verts n).filter (fun w => Q w && !P w) with
        | nil => rw [hf] at hmem; cases hmem
        | cons _ _ => simp
      unfold subsetCard at hcard h1; omega
  · exact (hsub v hPv).symm

/-- Helper: if `subsetCard P < subsetCard Q`, there exists `v` with `Q v = true ∧ P v = false`. -/
theorem exists_diff_of_card_lt {n : Nat} (P Q : Fin n → Bool)
    (hlt : subsetCard P < subsetCard Q) :
    ∃ v : Fin n, Q v = true ∧ P v = false := by
  apply Classical.byContradiction; intro hnone
  have hsub : ∀ v, Q v = true → P v = true := by
    intro v hQv
    cases hPv : P v
    · exact absurd ⟨v, hQv, hPv⟩ hnone
    · rfl
  have hle : subsetCard Q ≤ subsetCard P :=
    filter_length_le (verts n) Q P (fun v _ hQv => hsub v hQv)
  omega

/-- Helper: if `degIn G A u = 1`, `u` has a unique neighbor in `A`. -/
theorem unique_nbr_of_degIn_eq_one {n : Nat} (G : SGraph n) (A : Fin n → Bool) (u : Fin n)
    (hdeg : degIn G A u = 1) :
    ∃ z : Fin n, A z = true ∧ G.adj u z = true ∧
      ∀ w : Fin n, A w = true → G.adj u w = true → w = z := by
  have hpos : subsetCard (fun w => A w && G.adj u w) ≥ 1 := by
    unfold subsetCard; unfold degIn at hdeg; omega
  obtain ⟨z, hz⟩ := exists_mem_of_subsetCard_pos (fun w => A w && G.adj u w) hpos
  have hz1 := Bool.and_eq_true _ _ |>.mp hz
  refine ⟨z, hz1.1, hz1.2, fun w hAw hadj => ?_⟩
  apply Classical.byContradiction; intro hne
  have hle : subsetCard (fun x => decide (x = z) || decide (x = w)) ≤ degIn G A u := by
    unfold subsetCard degIn
    apply filter_length_le; intro x _ hx
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hx
    rcases hx with rfl | rfl
    · simp [hz1.1, hz1.2]
    · simp [hAw, hadj]
  have hcard2 : subsetCard (fun x => decide (x = z) || decide (x = w)) = 2 := by
    unfold subsetCard
    have hp := filter_length_partition (verts n) (fun x => decide (x = z) || decide (x = w)) (fun x => decide (x = z))
    have h1 : ((verts n).filter (fun x => (decide (x = z) || decide (x = w)) && decide (x = z))).length = 1 := by
      have heq : ((verts n).filter (fun x => (decide (x = z) || decide (x = w)) && decide (x = z))).length =
                 ((verts n).filter (fun x => decide (x = z))).length := by
        apply filter_length_eq; intro x _
        by_cases hx : x = z; subst hx; simp; simp [hx]
      rw [heq]; exact length_filter_eq_one_of_nodup _ (nodup_verts n) z (mem_verts z)
    have h2 : ((verts n).filter (fun x => (decide (x = z) || decide (x = w)) && !decide (x = z))).length = 1 := by
      have heq : ((verts n).filter (fun x => (decide (x = z) || decide (x = w)) && !decide (x = z))).length =
                 ((verts n).filter (fun x => decide (x = w))).length := by
        apply filter_length_eq; intro x _
        by_cases hx : x = w
        · subst hx; simp [hne]
        · by_cases hxz : x = z <;> simp [hx, hxz, Ne.symm hne]
      rw [heq]; exact length_filter_eq_one_of_nodup _ (nodup_verts n) w (mem_verts w)
    omega
  omega

/-- Helper: in a clique `K` (`edgesIn G.compl K = 0`), every pair of distinct vertices is adjacent,
    and every `u ∈ K` has `degIn G K u = subsetCard K - 1`. -/
theorem clique_adj_and_deg {n : Nat} (G : SGraph n) (K : Fin n → Bool)
    (hclq : edgesIn G.compl K = 0) :
    (∀ u v, K u = true → K v = true → u ≠ v → G.adj u v = true) ∧
    (∀ u, K u = true → degIn G K u + 1 = subsetCard K) := by
  have hadj : ∀ u v, K u = true → K v = true → u ≠ v → G.adj u v = true := by
    intro u v hKu hKv huv
    cases h : G.adj u v
    · exfalso
      have h0 : twoEdgesIn G.compl K = 0 := by
        have hte := two_mul_edgesIn G.compl K; omega
      have hpos : twoEdgesIn G.compl K ≥ 1 := by
        rw [twoEdgesIn_eq_double_sum]
        have hout : ∀ (l : List (Fin n)), u ∈ l →
            (l.map (fun x => ((verts n).map (fun y =>
              if (K x && K y && G.compl.adj x y) = true then 1 else 0)).sum)).sum ≥ 1 := by
          intro l hum
          induction l with
          | nil => cases hum
          | cons a as ih =>
            rcases List.mem_cons.mp hum with rfl | hum'
            · simp only [List.map_cons, List.sum_cons]
              have hinn : ∀ (ys : List (Fin n)), v ∈ ys →
                  (ys.map (fun y => if (K u && K y && G.compl.adj u y) = true then 1 else 0)).sum ≥ 1 := by
                intro ys hvm
                induction ys with
                | nil => cases hvm
                | cons b bs ihb =>
                  rcases List.mem_cons.mp hvm with rfl | hvm'
                  · simp only [List.map_cons, List.sum_cons]
                    have hc : (K u && K v && G.compl.adj u v) = true := by
                      simp [SGraph.compl, hKu, hKv, huv, h]
                    rw [hc]; simp
                  · simp only [List.map_cons, List.sum_cons]; have := ihb hvm'; omega
              have := hinn (verts n) (mem_verts v); omega
            · simp only [List.map_cons, List.sum_cons]; have := ih hum'; omega
        exact hout (verts n) (mem_verts u)
      omega
    · rfl
  refine ⟨hadj, fun u hKu => ?_⟩
  have hp := filter_length_partition (verts n) K (fun w => decide (w = u))
  have h1 : ((verts n).filter (fun w => K w && decide (w = u))).length = 1 := by
    have heq : ((verts n).filter (fun w => K w && decide (w = u))).length =
               ((verts n).filter (fun w => decide (w = u))).length := by
      apply filter_length_eq; intro w _
      by_cases hw : w = u; subst hw; simp [hKu]; simp [hw]
    rw [heq]; exact length_filter_eq_one_of_nodup _ (nodup_verts n) u (mem_verts u)
  have h2 : ((verts n).filter (fun w => K w && !decide (w = u))).length = degIn G K u := by
    unfold degIn; apply filter_length_eq; intro w _
    by_cases hw : w = u
    · subst hw; simp [G.loopless]
    · cases hKw : K w
      · simp
      · simp [hw, hadj u w hKu hKw (Ne.symm hw)]
  unfold subsetCard; omega

/-- Helper: `degIn G (A || B) u = degIn G A u + degIn G B u` for disjoint `A, B`. -/
theorem degIn_union_disjoint {n : Nat} (G : SGraph n) (A B : Fin n → Bool)
    (hdisj : ∀ w, !(A w && B w) = true) (u : Fin n) :
    degIn G (fun w => A w || B w) u = degIn G A u + degIn G B u := by
  unfold degIn
  have hp := filter_length_partition (verts n) (fun w => (A w || B w) && G.adj u w) A
  have h1 : ((verts n).filter (fun w => ((A w || B w) && G.adj u w) && A w)).length =
            ((verts n).filter (fun w => A w && G.adj u w)).length := by
    apply filter_length_eq; intro w _
    cases A w <;> cases B w <;> cases G.adj u w <;> rfl
  have h2 : ((verts n).filter (fun w => ((A w || B w) && G.adj u w) && !A w)).length =
            ((verts n).filter (fun w => B w && G.adj u w)).length := by
    apply filter_length_eq; intro w _
    have hd := hdisj w
    cases hAw : A w <;> cases hBw : B w <;> cases G.adj u w <;> simp [hAw, hBw] at hd ⊢
  dsimp only at *
  omega

/-- Helper: `crossEdges G A B = 0` iff no edge crosses between `A` and `B`. -/
theorem crossEdges_eq_zero_iff {n : Nat} (G : SGraph n) (A B : Fin n → Bool) :
    crossEdges G A B = 0 ↔ ∀ u v, A u = true → B v = true → G.adj u v = false := by
  constructor
  · intro h0 u v hAu hBv
    cases h : G.adj u v
    · rfl
    · exfalso
      have hpos : crossEdges G A B ≥ 1 := by
        rw [crossEdges_eq_double_sum]
        have hout : ∀ (l : List (Fin n)), u ∈ l →
            (l.map (fun x => ((verts n).map (fun y =>
              if (A x && B y && G.adj x y) = true then 1 else 0)).sum)).sum ≥ 1 := by
          intro l hum
          induction l with
          | nil => cases hum
          | cons a as ih =>
            rcases List.mem_cons.mp hum with rfl | hum'
            · simp only [List.map_cons, List.sum_cons]
              have hinn : ∀ (ys : List (Fin n)), v ∈ ys →
                  (ys.map (fun y => if (A u && B y && G.adj u y) = true then 1 else 0)).sum ≥ 1 := by
                intro ys hvm
                induction ys with
                | nil => cases hvm
                | cons b bs ihb =>
                  rcases List.mem_cons.mp hvm with rfl | hvm'
                  · simp only [List.map_cons, List.sum_cons]
                    have hc : (A u && B v && G.adj u v) = true := by simp [hAu, hBv, h]
                    rw [hc]; simp
                  · simp only [List.map_cons, List.sum_cons]; have := ihb hvm'; omega
              have := hinn (verts n) (mem_verts v); omega
            · simp only [List.map_cons, List.sum_cons]; have := ih hum'; omega
        exact hout (verts n) (mem_verts u)
      omega
  · intro hnone
    rw [crossEdges_eq_double_sum]
    apply sum_map_eq_zero; intro u _; apply sum_map_eq_zero; intro v _
    cases hAu : A u
    · simp
    · cases hBv : B v
      · simp
      · simp [hnone u v hAu hBv]

/-- **Main Theorem Step 3 (`K6_unique_nbr_IS`):**
    In a 6-regular color class `G = colorClass C c` of a balanced 6-coloring of `K₃₇`,
    for any complete `K₆` `K`, its external neighborhood `NK = {z ∉ K : degIn G K z = 1}`
    has size 6, forms a 6-independent set, matches `K` bijectively, and is the UNIQUE
    6-independent set in `V \ K`. -/
theorem K6_unique_nbr_IS (C : EdgeColoring (6 * 6 + 1) 6) (hbal : IsBalanced C) (c : Fin 6)
    (hreg : ∀ v, degIn (colorClass C c) (fun _ => true) v = 6)
    (K : Fin (6 * 6 + 1) → Bool) (hKcard : subsetCard K = 6)
    (hKclq : edgesIn (colorClass C c).compl K = 0) :
    let G := colorClass C c
    let W : Fin (6 * 6 + 1) → Bool := fun z => !K z
    let NK : Fin (6 * 6 + 1) → Bool := fun z => !K z && decide (degIn G K z = 1)
    (∀ u, K u = true → degIn G W u = 1) ∧
    subsetCard NK = 6 ∧
    crossEdges G K W = 6 ∧
    twoEdgesIn G W = 180 ∧
    IsIndep G NK ∧
    (∀ I : Fin (6 * 6 + 1) → Bool, (∀ w, I w = true → W w = true) →
      IsIndep G I → subsetCard I = 6 → ∀ w, I w = NK w) := by
  intro G W NK
  have hdisjKW : ∀ w, !(K w && W w) = true := by intro w; cases hK : K w <;> simp [W, hK]
  have hunionKW : ∀ w, (fun _ => true) w = (K w || W w) := by intro w; cases hK : K w <;> simp [W, hK]
  have ⟨_, hKdeg⟩ := clique_adj_and_deg G K hKclq
  -- 1. Every u ∈ K has degIn G W u = 1
  have hdegW : ∀ u, K u = true → degIn G W u = 1 := by
    intro u hKu
    have h6 := hreg u
    have hsp := degIn_union_disjoint G K W hdisjKW u
    have hcongr : degIn G (fun _ => true) u = degIn G (fun w => K w || W w) u := by
      unfold degIn; apply filter_length_eq; intro w _; rw [hunionKW w]
    have h5 := hKdeg u hKu
    dsimp [G] at hsp hcongr h5 ⊢
    rw [hcongr] at h6
    omega
  -- 2. crossEdges G K W = 6
  have hcross6 : crossEdges G K W = 6 := by
    unfold crossEdges
    have heq : ((verts (6 * 6 + 1)).map (fun u => if K u = true then degIn G W u else 0)).sum =
               ((verts (6 * 6 + 1)).map (fun u => if K u = true then 1 else 0)).sum := by
      apply sum_map_eq; intro u _
      by_cases hKu : K u = true
      · simp [hKu, hdegW u hKu]
      · simp [hKu]
    rw [heq, ← sum_filter_eq_sum_ite, sum_map_const, Nat.mul_one]
    exact hKcard
  -- 3. subsetCard NK = 6 (since every z ∈ W has degIn G K z ≤ 1 by r6_rigid_K6)
  have hNKcard : subsetCard NK = 6 := by
    have hsym := crossEdges_symm G K W
    rw [hcross6] at hsym
    have hcr : crossEdges G W K = subsetCard NK := by
      unfold crossEdges subsetCard
      rw [← Nat.mul_one ((verts (6 * 6 + 1)).filter NK).length,
          ← sum_map_const ((verts (6 * 6 + 1)).filter NK) 1,
          sum_filter_eq_sum_ite]
      apply sum_map_eq; intro z _
      cases hKz : K z
      · have hle1 : degIn G K z ≤ 1 := r6_rigid_K6 C hbal c K hKcard hKclq z hKz
        by_cases h1 : degIn G K z = 1
        · simp [W, NK, hKz, h1]
        · have h0 : degIn G K z = 0 := by omega
          simp [W, NK, hKz, h0]
      · simp [W, NK, hKz]
    omega
  -- 4. twoEdgesIn G W = 180
  have h2e_all : twoEdgesIn G (fun _ => true) = 222 := by
    unfold twoEdgesIn
    have hfilt : (verts (6 * 6 + 1)).filter (fun _ => true) = verts (6 * 6 + 1) := by
      induction (verts (6 * 6 + 1)) with
      | nil => rfl
      | cons x xs ih => simp [ih]
    rw [hfilt]
    have heq : ((verts (6 * 6 + 1)).map (degIn G (fun _ => true))).sum =
               ((verts (6 * 6 + 1)).map (fun _ => 6)).sum :=
      sum_map_eq _ _ _ (fun v _ => hreg v)
    rw [heq, sum_map_const, length_verts]
  have h2eK : twoEdgesIn G K = 30 := by
    have hcomp := twoEdgesIn_add_compl G K
    have hte := two_mul_edgesIn G.compl K
    rw [hKcard] at hcomp; rw [hKclq] at hte; omega
  have h2eW : twoEdgesIn G W = 180 := by
    have hsplit := twoEdgesIn_union_disjoint G K W hdisjKW
    have hcongr : twoEdgesIn G (fun _ => true) = twoEdgesIn G (fun w => K w || W w) := by
      rw [twoEdgesIn_eq_double_sum, twoEdgesIn_eq_double_sum]
      apply sum_map_eq; intro x _; apply sum_map_eq; intro y _
      cases hx : K x <;> cases hy : K y <;> simp [W, hx, hy]
    rw [← hcongr, h2e_all, h2eK, hcross6] at hsplit; omega
  -- 5. Uniqueness: any 6-IS I ⊆ W must equal NK!
  have huniq : ∀ I : Fin (6 * 6 + 1) → Bool, (∀ w, I w = true → W w = true) →
      IsIndep G I → subsetCard I = 6 → ∀ w, I w = NK w := by
    intro I hIsub hIind hIcard
    have hsub : ∀ z, NK z = true → I z = true := by
      intro z hNKz
      cases hIz : I z
      · exfalso
        have hNKz1 := Bool.and_eq_true _ _ |>.mp hNKz
        have hdegKz : degIn G K z = 1 := of_decide_eq_true hNKz1.2
        obtain ⟨u, hKu, hadj_zu, _⟩ := unique_nbr_of_degIn_eq_one G K z hdegKz
        obtain ⟨z', hWz', hadj_uz', huniq_u⟩ := unique_nbr_of_degIn_eq_one G W u (hdegW u hKu)
        have hzz' : z = z' := huniq_u z hNKz1.1 (by rw [G.symm]; exact hadj_zu)
        -- u has NO neighbor in I (since its unique neighbor in W is z' = z and I z = false)!
        let I' : Fin (6 * 6 + 1) → Bool := fun w => I w || decide (w = u)
        have hIu : I u = false := by
          cases hi : I u
          · rfl
          · have hWu := hIsub u hi; simp [W, hKu] at hWu
        have hI'ind : IsIndep G I' := by
          intro p q hp hq
          simp only [I', Bool.or_eq_true, decide_eq_true_eq] at hp hq
          rcases hp with hIp | rfl <;> rcases hq with hIq | rfl
          · exact hIind p q hIp hIq
          · cases ha : G.adj p q
            · rfl
            · exfalso
              have hpz' := huniq_u p (hIsub p hIp) (by rw [G.symm]; exact ha)
              subst hpz'; subst hzz'; simp [hIz] at hIp
          · cases ha : G.adj p q
            · rfl
            · exfalso
              have hqz' := huniq_u q (hIsub q hIq) ha
              subst hqz'; subst hzz'; simp [hIz] at hIq
          · exact G.loopless _
        have hI'card : subsetCard I' = 7 := by
          unfold subsetCard
          have hp := filter_length_partition (verts (6 * 6 + 1)) I' (fun w => decide (w = u))
          have h1 : ((verts (6 * 6 + 1)).filter (fun w => I' w && decide (w = u))).length = 1 := by
            have heq : ((verts (6 * 6 + 1)).filter (fun w => I' w && decide (w = u))).length =
                       ((verts (6 * 6 + 1)).filter (fun w => decide (w = u))).length := by
              apply filter_length_eq; intro w _
              by_cases hw : w = u; subst hw; simp [I']; simp [I', hw]
            rw [heq]; exact length_filter_eq_one_of_nodup _ (nodup_verts _) u (mem_verts u)
          have h2 : ((verts (6 * 6 + 1)).filter (fun w => I' w && !decide (w = u))).length = subsetCard I := by
            unfold subsetCard; apply filter_length_eq; intro w _
            by_cases hw : w = u; subst hw; simp [I', hIu]; simp [I', hw]
          omega
        have hle6 := isBalanced_indep_le C hbal c I' hI'ind
        omega
      · rfl
    exact fun w => (eq_of_sub_and_card_eq NK I hsub (by omega) w).symm
  -- 6. Existence of a 6-IS I0 ⊆ W via Lemma 7 (|W| = 31, twoEdgesIn G W = 180 ≤ 192) ⇒ IsIndep G NK!
  have hWcard : subsetCard W = 31 := by
    have hp := filter_length_partition (verts (6 * 6 + 1)) (fun _ => true) K
    have hall : ((verts (6 * 6 + 1)).filter (fun _ => true)).length = 37 := by
      have hfilt : (verts (6 * 6 + 1)).filter (fun _ => true) = verts (6 * 6 + 1) := by
        induction (verts (6 * 6 + 1)) with | nil => rfl | cons x xs ih => simp [ih]
      rw [hfilt, length_verts]
    have h1 : ((verts (6 * 6 + 1)).filter (fun x => true && K x)).length = 6 := by
      have heq : ((verts (6 * 6 + 1)).filter (fun x => true && K x)).length = subsetCard K := by
        unfold subsetCard; apply filter_length_eq; intro x _; simp
      rw [heq, hKcard]
    have h2 : ((verts (6 * 6 + 1)).filter (fun x => true && !K x)).length = subsetCard W := by
      unfold subsetCard; apply filter_length_eq; intro x _; simp [W]
    omega
  have hNK_ind : IsIndep G NK := by
    have hno5 := no_31_alpha_le_5_e_le_96 C hbal c W hWcard (by dsimp [G] at h2eW; omega)
    have hex6 : ∃ I : Fin (6 * 6 + 1) → Bool, (∀ w, I w = true → W w = true) ∧
        IsIndep G I ∧ subsetCard I = 6 := by
      apply Classical.byContradiction; intro hnone
      apply hno5; intro I hIsub hIind
      by_cases h5 : subsetCard I ≤ 5
      · exact h5
      · exfalso
        obtain ⟨I6, hI6sub, hI6card⟩ := exists_sub_card I 6 (by omega)
        exact hnone ⟨I6, fun w hw => hIsub w (hI6sub w hw), isIndep_mono hI6sub hIind, hI6card⟩
    obtain ⟨I0, hI0sub, hI0ind, hI0card⟩ := hex6
    have heq := huniq I0 hI0sub hI0ind hI0card
    intro u v hu hv
    rw [← heq u] at hu; rw [← heq v] at hv
    exact hI0ind u v hu hv
  exact ⟨hdegW, hNKcard, hcross6, h2eW, hNK_ind, huniq⟩

/-- **Main Theorem Step 4 (`no_disjoint_K6_zero_cross`):**
    In a 6-regular color class `G = colorClass C c` of a balanced 6-coloring of `K₃₇`,
    NO two vertex-disjoint `K₆`'s can have zero edges between them! -/
theorem no_disjoint_K6_zero_cross (C : EdgeColoring (6 * 6 + 1) 6) (hbal : IsBalanced C) (c : Fin 6)
    (hreg : ∀ v, degIn (colorClass C c) (fun _ => true) v = 6)
    (K1 K2 : Fin (6 * 6 + 1) → Bool)
    (hK1card : subsetCard K1 = 6) (hK1clq : edgesIn (colorClass C c).compl K1 = 0)
    (hK2card : subsetCard K2 = 6) (hK2clq : edgesIn (colorClass C c).compl K2 = 0)
    (hdisj : ∀ v, !(K1 v && K2 v) = true)
    (hzero : crossEdges (colorClass C c) K1 K2 = 0) : False := by
  let G := colorClass C c
  let NK1 : Fin (6 * 6 + 1) → Bool := fun z => !K1 z && decide (degIn G K1 z = 1)
  let NK2 : Fin (6 * 6 + 1) → Bool := fun z => !K2 z && decide (degIn G K2 z = 1)
  obtain ⟨hdegW1, hNK1card, hcr1, _, hNK1ind, _⟩ := K6_unique_nbr_IS C hbal c hreg K1 hK1card hK1clq
  obtain ⟨hdegW2, _, hcr2, _, _, huniq2⟩ := K6_unique_nbr_IS C hbal c hreg K2 hK2card hK2clq
  have hno_edge : ∀ u v, K1 u = true → K2 v = true → G.adj u v = false :=
    (crossEdges_eq_zero_iff G K1 K2).mp hzero
  -- NK1 is disjoint from K2 (any z ∈ NK1 has a neighbor in K1), so NK1 ⊆ !K2 ⇒ NK1 = NK2!
  have hNK1_sub_W2 : ∀ z, NK1 z = true → (!K2 z) = true := by
    intro z hNK1z
    cases hK2z : K2 z
    · rfl
    · exfalso
      have hdeg : degIn G K1 z = 1 := of_decide_eq_true (Bool.and_eq_true _ _ |>.mp hNK1z).2
      obtain ⟨u, hK1u, hadj, _⟩ := unique_nbr_of_degIn_eq_one G K1 z hdeg
      have hna := hno_edge u z hK1u hK2z
      rw [G.symm] at hadj; simp [hna] at hadj
  have hNK_eq : ∀ z, NK1 z = NK2 z := huniq2 NK1 hNK1_sub_W2 hNK1ind hNK1card
  -- Let R = V \ (K1 ∪ K2): |R| = 25 and twoEdgesIn G R = 138 ≤ 162!
  let K12 : Fin (6 * 6 + 1) → Bool := fun v => K1 v || K2 v
  let R : Fin (6 * 6 + 1) → Bool := fun v => !K1 v && !K2 v
  have hdisj12R : ∀ v, !(K12 v && R v) = true := by
    intro v; cases h1 : K1 v <;> cases h2 : K2 v <;> simp [K12, R, h1, h2]
  have hunion12R : ∀ v, (fun _ => true) v = (K12 v || R v) := by
    intro v; cases h1 : K1 v <;> cases h2 : K2 v <;> simp [K12, R, h1, h2]
  have hK12card : subsetCard K12 = 12 := by
    unfold subsetCard
    have hp := filter_length_partition (verts (6 * 6 + 1)) K12 K1
    have h1 : ((verts (6 * 6 + 1)).filter (fun v => K12 v && K1 v)).length = subsetCard K1 := by
      unfold subsetCard; apply filter_length_eq; intro v _; cases h1v : K1 v <;> simp [K12, h1v]
    have h2 : ((verts (6 * 6 + 1)).filter (fun v => K12 v && !K1 v)).length = subsetCard K2 := by
      unfold subsetCard; apply filter_length_eq; intro v _
      have hd := hdisj v; cases h1v : K1 v <;> cases h2v : K2 v <;> simp [K12, h1v, h2v] at hd ⊢
    omega
  have hRcard : subsetCard R = 25 := by
    have hp := filter_length_partition (verts (6 * 6 + 1)) (fun _ => true) K12
    have hall : ((verts (6 * 6 + 1)).filter (fun _ => true)).length = 37 := by
      have hfilt : (verts (6 * 6 + 1)).filter (fun _ => true) = verts (6 * 6 + 1) := by
        induction (verts (6 * 6 + 1)) with | nil => rfl | cons x xs ih => simp [ih]
      rw [hfilt, length_verts]
    have h1 : ((verts (6 * 6 + 1)).filter (fun v => true && K12 v)).length = 12 := by
      have heq : ((verts (6 * 6 + 1)).filter (fun v => true && K12 v)).length = subsetCard K12 := by
        unfold subsetCard; apply filter_length_eq; intro v _; simp
      rw [heq, hK12card]
    have h2 : ((verts (6 * 6 + 1)).filter (fun v => true && !K12 v)).length = subsetCard R := by
      unfold subsetCard; apply filter_length_eq; intro v _
      cases h1v : K1 v <;> cases h2v : K2 v <;> simp [K12, R, h1v, h2v]
    omega
  have h2e_all : twoEdgesIn G (fun _ => true) = 222 := by
    unfold twoEdgesIn
    have hfilt : (verts (6 * 6 + 1)).filter (fun _ => true) = verts (6 * 6 + 1) := by
      induction (verts (6 * 6 + 1)) with | nil => rfl | cons x xs ih => simp [ih]
    rw [hfilt]
    have heq : ((verts (6 * 6 + 1)).map (degIn G (fun _ => true))).sum =
               ((verts (6 * 6 + 1)).map (fun _ => 6)).sum :=
      sum_map_eq _ _ _ (fun v _ => hreg v)
    rw [heq, sum_map_const, length_verts]
  have h2eK1 : twoEdgesIn G K1 = 30 := by
    have hcomp := twoEdgesIn_add_compl G K1; have hte := two_mul_edgesIn G.compl K1
    rw [hK1card] at hcomp; rw [hK1clq] at hte; omega
  have h2eK2 : twoEdgesIn G K2 = 30 := by
    have hcomp := twoEdgesIn_add_compl G K2; have hte := two_mul_edgesIn G.compl K2
    rw [hK2card] at hcomp; rw [hK2clq] at hte; omega
  have h2eK12 : twoEdgesIn G K12 = 60 := by
    have h := twoEdgesIn_union_disjoint G K1 K2 hdisj
    dsimp [G, K12] at h h2eK1 h2eK2 hzero ⊢; omega
  have hcr1R : crossEdges G K1 R = 6 := by
    have hdisjK2R : ∀ v, !(K2 v && R v) = true := by intro v; cases h1 : K1 v <;> cases h2 : K2 v <;> simp [R, h1, h2]
    have hunion1 : ∀ v, (!K1 v) = (K2 v || R v) := by
      intro v; have hd := hdisj v; cases h1v : K1 v <;> cases h2v : K2 v <;> simp [R, h1v, h2v] at hd ⊢
    have h := sum_degIn_union_disjoint G K1 K2 R hdisjK2R
    rw [← crossEdges_congr G (fun _ => rfl) hunion1] at h
    dsimp [G] at h hcr1 hzero ⊢; omega
  have hcr2R : crossEdges G K2 R = 6 := by
    have hdisjK1R : ∀ v, !(K1 v && R v) = true := by intro v; cases h1 : K1 v <;> cases h2 : K2 v <;> simp [R, h1, h2]
    have hunion2 : ∀ v, (!K2 v) = (K1 v || R v) := by
      intro v; have hd := hdisj v; cases h1v : K1 v <;> cases h2v : K2 v <;> simp [R, h1v, h2v] at hd ⊢
    have h := sum_degIn_union_disjoint G K2 K1 R hdisjK1R
    rw [← crossEdges_congr G (fun _ => rfl) hunion2, crossEdges_symm G K2 K1] at h
    dsimp [G] at h hcr2 hzero ⊢; omega
  have hcr12R : crossEdges G K12 R = 12 := by
    rw [crossEdges_symm G K12 R]
    have h := sum_degIn_union_disjoint G R K1 K2 hdisj
    rw [crossEdges_symm G R K1, crossEdges_symm G R K2] at h
    change crossEdges G R (fun w => K1 w || K2 w) = 12
    rw [h]; omega
  have h2eR : twoEdgesIn G R = 138 := by
    have h := twoEdgesIn_union_disjoint G K12 R hdisj12R
    have hcongr : twoEdgesIn G (fun _ => true) = twoEdgesIn G (fun v => K12 v || R v) := by
      rw [twoEdgesIn_eq_double_sum, twoEdgesIn_eq_double_sum]
      apply sum_map_eq; intro x _; apply sum_map_eq; intro y _
      cases h1x : K1 x <;> cases h2x : K2 x <;> cases h1y : K1 y <;> cases h2y : K2 y <;>
        simp [K12, R, h1x, h2x, h1y, h2y]
    rw [← hcongr, h2e_all, h2eK12, hcr12R] at h; omega
  -- By Lemma 4 on R (|R| = 25, twoEdgesIn G R = 138 ≤ 162), R has a 5-IS J!
  have hno4 := no_25_alpha_le_4_e_le_81 C hbal c R hRcard (by dsimp [G] at h2eR; omega)
  have hex5 : ∃ J : Fin (6 * 6 + 1) → Bool, (∀ w, J w = true → R w = true) ∧
      IsIndep G J ∧ subsetCard J = 5 := by
    apply Classical.byContradiction; intro hnone
    apply hno4; intro J hJsub hJind
    by_cases h4 : subsetCard J ≤ 4
    · exact h4
    · exfalso
      obtain ⟨J5, hJ5sub, hJ5card⟩ := exists_sub_card J 5 (by omega)
      exact hnone ⟨J5, fun w hw => hJsub w (hJ5sub w hw), isIndep_mono hJ5sub hJind, hJ5card⟩
  obtain ⟨J, hJsub, hJind, hJcard⟩ := hex5
  -- Pick z ∈ NK1 \ J (since |J| = 5 < 6 = |NK1|)
  have hNK1c : subsetCard NK1 = 6 := hNK1card
  obtain ⟨z, hNK1z, hJz_false⟩ := exists_diff_of_card_lt J NK1 (by omega)
  have hNK2z : NK2 z = true := by rw [← hNK_eq z]; exact hNK1z
  have hdegK1z : degIn G K1 z = 1 := of_decide_eq_true (Bool.and_eq_true _ _ |>.mp hNK1z).2
  have hdegK2z : degIn G K2 z = 1 := of_decide_eq_true (Bool.and_eq_true _ _ |>.mp hNK2z).2
  obtain ⟨u1, hK1u1, hadj_zu1, _⟩ := unique_nbr_of_degIn_eq_one G K1 z hdegK1z
  obtain ⟨u2, hK2u2, hadj_zu2, _⟩ := unique_nbr_of_degIn_eq_one G K2 z hdegK2z
  obtain ⟨z1', _, _, huniq_u1⟩ := unique_nbr_of_degIn_eq_one G (fun w => !K1 w) u1 (hdegW1 u1 hK1u1)
  obtain ⟨z2', _, _, huniq_u2⟩ := unique_nbr_of_degIn_eq_one G (fun w => !K2 w) u2 (hdegW2 u2 hK2u2)
  have hzz1 : z = z1' := huniq_u1 z (Bool.and_eq_true _ _ |>.mp hNK1z).1 (by rw [G.symm]; exact hadj_zu1)
  have hzz2 : z = z2' := huniq_u2 z (Bool.and_eq_true _ _ |>.mp hNK2z).1 (by rw [G.symm]; exact hadj_zu2)
  have hu12 : u1 ≠ u2 := by
    intro heq; subst heq; have hd := hdisj u1; simp [hK1u1, hK2u2] at hd
  have hJu1 : J u1 = false := by
    cases hi : J u1; rfl
    have hRu1 := hJsub u1 hi; simp [R, hK1u1] at hRu1
  have hJu2 : J u2 = false := by
    cases hi : J u2; rfl
    have hRu2 := hJsub u2 hi; simp [R, hK2u2] at hRu2
  -- J ∪ {u1, u2} is a 7-IS in G!
  let J' : Fin (6 * 6 + 1) → Bool := fun w => J w || decide (w = u1) || decide (w = u2)
  have hJ'ind : IsIndep G J' := by
    intro p q hp hq
    simp only [J', Bool.or_eq_true, decide_eq_true_eq] at hp hq
    rcases hp with (hJp | rfl) | rfl <;> rcases hq with (hJq | rfl) | rfl
    · exact hJind p q hJp hJq
    · cases ha : G.adj p q
      · rfl
      · exfalso
        have hp1 := huniq_u1 p (Bool.and_eq_true _ _ |>.mp (hJsub p hJp)).1 (by rw [G.symm]; exact ha)
        subst hp1; subst hzz1; simp [hJz_false] at hJp
    · cases ha : G.adj p q
      · rfl
      · exfalso
        have hp2 := huniq_u2 p (Bool.and_eq_true _ _ |>.mp (hJsub p hJp)).2 (by rw [G.symm]; exact ha)
        subst hp2; subst hzz2; simp [hJz_false] at hJp
    · cases ha : G.adj p q
      · rfl
      · exfalso
        have hq1 := huniq_u1 q (Bool.and_eq_true _ _ |>.mp (hJsub q hJq)).1 ha
        subst hq1; subst hzz1; simp [hJz_false] at hJq
    · exact G.loopless _
    · exact hno_edge p q hK1u1 hK2u2
    · cases ha : G.adj p q
      · rfl
      · exfalso
        have hq2 := huniq_u2 q (Bool.and_eq_true _ _ |>.mp (hJsub q hJq)).2 ha
        subst hq2; subst hzz2; simp [hJz_false] at hJq
    · rw [G.symm]; exact hno_edge q p hK1u1 hK2u2
    · exact G.loopless _
  have hJ'card : subsetCard J' = 7 := by
    unfold subsetCard
    have hp1 := filter_length_partition (verts (6 * 6 + 1)) J' (fun w => decide (w = u1))
    have h1 : ((verts (6 * 6 + 1)).filter (fun w => J' w && decide (w = u1))).length = 1 := by
      have heq : ((verts (6 * 6 + 1)).filter (fun w => J' w && decide (w = u1))).length =
                 ((verts (6 * 6 + 1)).filter (fun w => decide (w = u1))).length := by
        apply filter_length_eq; intro w _
        by_cases hw : w = u1; subst hw; simp [J']; simp [J', hw]
      rw [heq]; exact length_filter_eq_one_of_nodup _ (nodup_verts _) u1 (mem_verts u1)
    have hp2 := filter_length_partition (verts (6 * 6 + 1)) (fun w => J' w && !decide (w = u1)) (fun w => decide (w = u2))
    have h2 : ((verts (6 * 6 + 1)).filter (fun w => (J' w && !decide (w = u1)) && decide (w = u2))).length = 1 := by
      have heq : ((verts (6 * 6 + 1)).filter (fun w => (J' w && !decide (w = u1)) && decide (w = u2))).length =
                 ((verts (6 * 6 + 1)).filter (fun w => decide (w = u2))).length := by
        apply filter_length_eq; intro w _
        by_cases hw : w = u2; subst hw; simp [J', Ne.symm hu12]; simp [J', hw]
      rw [heq]; exact length_filter_eq_one_of_nodup _ (nodup_verts _) u2 (mem_verts u2)
    have h3 : ((verts (6 * 6 + 1)).filter (fun w => (J' w && !decide (w = u1)) && !decide (w = u2))).length =
              subsetCard J := by
      unfold subsetCard; apply filter_length_eq; intro w _
      by_cases hw1 : w = u1
      · subst hw1; simp [J', hJu1]
      · by_cases hw2 : w = u2
        · subst hw2; simp [J', hJu2]
        · simp [J', hw1, hw2]
    omega
  have hle6 := isBalanced_indep_le C hbal c J' hJ'ind
  omega

/-- **MAIN THEOREM — Erdős Problem #617 for `r = 6` (`K₃₇`):**
    In any 6-coloring of the edges of `K₃₇`, there exists a 7-vertex subset whose induced
    subgraph misses at least one color (equivalently, no balanced 6-coloring of `K₃₇` exists). -/
theorem erdos617_r6 : ∀ C : EdgeColoring (6 * 6 + 1) 6, ¬ IsBalanced C := by
  intro C hbal
  -- Take the sparsest color class c: edges G ≤ 111, i.e., twoEdgesIn G allV ≤ 222
  obtain ⟨c, hedges_le⟩ := exists_sparsest_colorClass (r := 6) (by omega) C
  let G := colorClass C c
  let allV : Fin (6 * 6 + 1) → Bool := fun _ => true
  have hall_card : subsetCard allV = 37 := by
    unfold subsetCard
    have hfilt : (verts (6 * 6 + 1)).filter allV = verts (6 * 6 + 1) := by
      induction (verts (6 * 6 + 1)) with | nil => rfl | cons x xs ih => simp [allV, ih]
    rw [hfilt, length_verts]
  have h2e_all_le : twoEdgesIn G allV ≤ 222 := by
    have hte := two_mul_edges G
    unfold twoEdges at hte
    dsimp [G, allV] at hte ⊢
    omega
  have hα6 : ∀ I : Fin (6 * 6 + 1) → Bool, (∀ v, I v = true → allV v = true) →
      IsIndep G I → subsetCard I ≤ 6 :=
    fun I _ hIind => isBalanced_indep_le C hbal c I hIind
  -- Step 1: G is 6-regular (∀ v, degIn G allV v = 6) and twoEdgesIn G allV = 222!
  have hdeg_ge6 : ∀ v : Fin (6 * 6 + 1), degIn G allV v ≥ 6 := by
    apply Classical.byContradiction; intro hnot
    obtain ⟨v0, hv0all, hv0min⟩ := exists_min_degIn G allV (by omega)
    have hv0_le5 : degIn G allV v0 ≤ 5 := by
      apply Classical.byContradiction; intro hge6
      apply hnot; intro v
      have := hv0min v (by rfl); omega
    obtain ⟨hBcard, hcard_sum, _, _, _, hU_eq, hαA⟩ := peel_at_min_vertex G allV v0 hv0all hv0min
    let B : Fin (6 * 6 + 1) → Bool := fun w => allV w && (decide (w = v0) || G.adj v0 w)
    let A : Fin (6 * 6 + 1) → Bool := fun w => allV w && !decide (w = v0) && !G.adj v0 w
    have hBc : subsetCard B = degIn G allV v0 + 1 := hBcard
    have hcs : subsetCard A + subsetCard B = subsetCard allV := hcard_sum
    have hb_cases : subsetCard B = 1 ∨ subsetCard B = 2 ∨ subsetCard B = 3 ∨
                    subsetCard B = 4 ∨ subsetCard B = 5 ∨ subsetCard B = 6 := by omega
    have h2eA_ub : twoEdgesIn G A ≤ 192 + 12 * (subsetCard A - 31) := by
      have hmul_bound : subsetCard B * (subsetCard B - 1) + 12 * (subsetCard A - 31) ≥ 30 := by
        rcases hb_cases with h | h | h | h | h | h <;> (rw [h] at hcs ⊢; omega)
      dsimp [G, A, B] at hU_eq hBc hcs hmul_bound h2e_all_le ⊢
      omega
    obtain ⟨A31, hA31sub, hA31card, hA31_2e⟩ :=
      exists_sub_card_twoEdges_le G 31 192 (subsetCard A - 31) A (by omega) (by omega) h2eA_ub
    exact no_31_alpha_le_5_e_le_96 C hbal c A31 hA31card hA31_2e
      (fun I hIsub hIind => hαA 5 hα6 I (fun w hw => hA31sub w (hIsub w hw)) hIind)
  have hreg : ∀ v : Fin (6 * 6 + 1), degIn G allV v = 6 := by
    intro v
    by_cases h6 : degIn G allV v = 6
    · exact h6
    · exfalso
      have hv_ge7 : degIn G allV v ≥ 7 := by have := hdeg_ge6 v; omega
      have hsum_ge223 : twoEdgesIn G allV ≥ 223 := by
        unfold twoEdgesIn
        have hfilt : (verts (6 * 6 + 1)).filter allV = verts (6 * 6 + 1) := by
          induction (verts (6 * 6 + 1)) with | nil => rfl | cons x xs ih => simp [allV, ih]
        rw [hfilt]
        have haux : ∀ (l : List (Fin (6 * 6 + 1))), v ∈ l →
            (l.map (degIn G allV)).sum ≥ 6 * l.length + 1 := by
          intro l hvm
          induction l with
          | nil => cases hvm
          | cons y ys ih =>
            rcases List.mem_cons.mp hvm with rfl | hvm'
            · simp only [List.map_cons, List.sum_cons, List.length_cons]
              have hys : (ys.map (degIn G allV)).sum ≥ 6 * ys.length := by
                have h := sum_map_le ys (fun _ => 6) (degIn G allV) (fun w _ => hdeg_ge6 w)
                rw [sum_map_const] at h; omega
              omega
            · simp only [List.map_cons, List.sum_cons, List.length_cons]
              have hy := hdeg_ge6 y
              have hys := ih hvm'; omega
        have h := haux (verts (6 * 6 + 1)) (mem_verts v)
        rw [length_verts] at h; omega
      omega
  have h2e_all : twoEdgesIn G allV = 222 := by
    unfold twoEdgesIn
    have hfilt : (verts (6 * 6 + 1)).filter allV = verts (6 * 6 + 1) := by
      induction (verts (6 * 6 + 1)) with | nil => rfl | cons x xs ih => simp [allV, ih]
    rw [hfilt]
    have heq : ((verts (6 * 6 + 1)).map (degIn G allV)).sum = ((verts (6 * 6 + 1)).map (fun _ => 6)).sum :=
      sum_map_eq _ _ _ (fun v _ => hreg v)
    rw [heq, sum_map_const, length_verts]
  -- Step 2: G contains a K₆ (`K1`) (otherwise peeling at v = 0 leaves 30 vertices with ≤ 170, contradicting Lemma 8!)
  have hexK1 : HasK6In G allV := by
    apply Classical.byContradiction; intro hnoK6
    let v0 : Fin (6 * 6 + 1) := ⟨0, by omega⟩
    have hv0min : ∀ u, allV u = true → degIn G allV v0 ≤ degIn G allV u := by
      intro u _; rw [hreg v0, hreg u]; exact Nat.le_refl 6
    obtain ⟨hBcard, hcard_sum, _, _, _, hU_eq, hαA⟩ := peel_at_min_vertex G allV v0 rfl hv0min
    let B : Fin (6 * 6 + 1) → Bool := fun w => allV w && (decide (w = v0) || G.adj v0 w)
    let A : Fin (6 * 6 + 1) → Bool := fun w => allV w && !decide (w = v0) && !G.adj v0 w
    have hBc : subsetCard B = 7 := by
      have : subsetCard B = degIn G allV v0 + 1 := hBcard
      rw [hreg v0] at this; exact this
    have hcs : subsetCard A + subsetCard B = subsetCard allV := hcard_sum
    have hAc : subsetCard A = 30 := by omega
    have hmsB := multiscale_turan_complement C hbal c B 1
    have hteB := two_mul_edgesIn G.compl B
    have hmB10 : twoEdgesIn G.compl B ≥ 10 := by
      dsimp [G] at hteB ⊢; rw [hBc, hteB] at hmsB; omega
    have hnoK6A : ¬ HasK6In G A := fun ⟨K, _, hKc, hKclq⟩ => hnoK6 ⟨K, fun _ _ => rfl, hKc, hKclq⟩
    have h2eA : twoEdgesIn G A ≥ 172 := K6_free_30_edges_ge_86 C hbal c A hAc (hαA 5 hα6) hnoK6A
    dsimp [G, A, B] at h2eA hBc hmB10 hU_eq h2e_all
    rw [hBc] at hU_eq
    omega
  obtain ⟨K1, _, hK1card, hK1clq⟩ := hexK1
  -- Step 5: Construct a disjoint K₆ (`K2`) with crossEdges G K1 K2 = 1!
  let W1 : Fin (6 * 6 + 1) → Bool := fun z => !K1 z
  let NK1 : Fin (6 * 6 + 1) → Bool := fun z => !K1 z && decide (degIn G K1 z = 1)
  obtain ⟨hdegW1, hNK1card, hcr1, h2eW1, hNK1ind, huniq1⟩ := K6_unique_nbr_IS C hbal c hreg K1 hK1card hK1clq
  have hNK1c : subsetCard NK1 = 6 := hNK1card
  obtain ⟨z0, hNK1z0⟩ := exists_mem_of_subsetCard_pos NK1 (by omega)
  have hW1z0 : W1 z0 = true := (Bool.and_eq_true _ _ |>.mp hNK1z0).1
  have hdegK1z0 : degIn G K1 z0 = 1 := of_decide_eq_true (Bool.and_eq_true _ _ |>.mp hNK1z0).2
  have hdegW1z0 : degIn G W1 z0 = 5 := by
    have hdisj : ∀ w, !(K1 w && W1 w) = true := by intro w; cases h1 : K1 w <;> simp [W1, h1]
    have hunion : ∀ w, allV w = (K1 w || W1 w) := by intro w; cases h1 : K1 w <;> simp [allV, W1, h1]
    have hsp := degIn_union_disjoint G K1 W1 hdisj z0
    have hcongr : degIn G allV z0 = degIn G (fun w => K1 w || W1 w) z0 := by
      unfold degIn; apply filter_length_eq; intro w _; rw [hunion w]
    have h6 := hreg z0
    rw [hcongr] at h6
    omega
  let Wstar : Fin (6 * 6 + 1) → Bool := fun v => W1 v && !decide (v = z0)
  obtain ⟨hWstar_card', hWstar_2e'⟩ := erase_vertex_stats G W1 z0 hW1z0
  have hW1card : subsetCard W1 = 31 := by
    have hp := filter_length_partition (verts (6 * 6 + 1)) allV K1
    have h1 : ((verts (6 * 6 + 1)).filter (fun x => allV x && K1 x)).length = 6 := by
      have heq : ((verts (6 * 6 + 1)).filter (fun x => allV x && K1 x)).length = subsetCard K1 := by
        unfold subsetCard; apply filter_length_eq; intro x _; simp [allV]
      rw [heq, hK1card]
    have h2 : ((verts (6 * 6 + 1)).filter (fun x => allV x && !K1 x)).length = subsetCard W1 := by
      unfold subsetCard; apply filter_length_eq; intro x _; simp [allV, W1]
    unfold subsetCard at hall_card; omega
  have hWstar_card : subsetCard Wstar = 30 := by
    have hc : subsetCard Wstar + 1 = subsetCard W1 := hWstar_card'
    omega
  have hWstar_2e : twoEdgesIn G Wstar = 170 := by
    have h2e : twoEdgesIn G Wstar + 2 * degIn G W1 z0 = twoEdgesIn G W1 := hWstar_2e'
    have h180 : twoEdgesIn G W1 = 180 := h2eW1
    omega
  have hαWstar : ∀ I, (∀ v, I v = true → Wstar v = true) → IsIndep G I → subsetCard I ≤ 5 := by
    intro I hIsub hIind
    by_cases h5 : subsetCard I ≤ 5
    · exact h5
    · exfalso
      have hle6 := isBalanced_indep_le C hbal c I hIind
      have heq := huniq1 I (fun w hw => (Bool.and_eq_true _ _ |>.mp (hIsub w hw)).1) hIind (by omega)
      have hIz0 : I z0 = true := by rw [heq z0]; exact hNK1z0
      have hWz := hIsub z0 hIz0; simp [Wstar] at hWz
  have hexK2 : HasK6In G Wstar := by
    apply Classical.byContradiction; intro hnoK6
    have hge172 := K6_free_30_edges_ge_86 C hbal c Wstar hWstar_card hαWstar hnoK6
    dsimp [G] at hWstar_2e; omega
  obtain ⟨K2, hK2subWstar, hK2card, hK2clq⟩ := hexK2
  have hdisj12 : ∀ v, !(K1 v && K2 v) = true := by
    intro v
    cases h1 : K1 v
    · simp
    · cases h2 : K2 v
      · simp
      · exfalso
        have hWs := hK2subWstar v h2; simp [Wstar, W1, h1] at hWs
  -- By Step 4, crossEdges G K1 K2 ≥ 1, so ∃ uy ∈ K1, y ∈ K2 with G.adj uy y = true!
  have hcr12_pos : crossEdges G K1 K2 ≥ 1 := by
    by_cases h0 : crossEdges G K1 K2 = 0
    · exact absurd h0 (fun h => no_disjoint_K6_zero_cross C hbal c hreg K1 K2 hK1card hK1clq hK2card hK2clq hdisj12 h)
    · omega
  have hex_edge12 : ∃ uy y : Fin (6 * 6 + 1), K1 uy = true ∧ K2 y = true ∧ G.adj uy y = true := by
    apply Classical.byContradiction; intro hnone
    have h0 := (crossEdges_eq_zero_iff G K1 K2).mpr (fun u v h1 h2 => by
      cases ha : G.adj u v; rfl; exact absurd ⟨u, v, h1, h2, ha⟩ hnone)
    omega
  obtain ⟨uy, y, hK1uy, hK2y, hadj_uy_y⟩ := hex_edge12
  -- y is in NK1, uy is in NK2, and (uy, y) is the UNIQUE edge between K1 and K2!
  let W2 : Fin (6 * 6 + 1) → Bool := fun z => !K2 z
  let NK2 : Fin (6 * 6 + 1) → Bool := fun z => !K2 z && decide (degIn G K2 z = 1)
  obtain ⟨hdegW2, hNK2card, hcr2, _, hNK2ind, _⟩ := K6_unique_nbr_IS C hbal c hreg K2 hK2card hK2clq
  have ⟨hK1adj, _⟩ := clique_adj_and_deg G K1 hK1clq
  have ⟨hK2adj, hK2deg⟩ := clique_adj_and_deg G K2 hK2clq
  have hK1y_false : K1 y = false := by
    cases h : K1 y; rfl; have := hdisj12 y; simp [h, hK2y] at this
  have hK2uy_false : K2 uy = false := by
    cases h : K2 uy; rfl; have := hdisj12 uy; simp [hK1uy, h] at this
  have hdegK1y : degIn G K1 y = 1 := by
    have hle1 := r6_rigid_K6 C hbal c K1 hK1card hK1clq y hK1y_false
    have hge1 : degIn G K1 y ≥ 1 := by
      unfold degIn
      have hmem : uy ∈ (verts (6 * 6 + 1)).filter (fun w => K1 w && G.adj y w) :=
        List.mem_filter.mpr ⟨mem_verts uy, by rw [G.symm]; simp [hK1uy, hadj_uy_y]⟩
      cases hf : (verts (6 * 6 + 1)).filter (fun w => K1 w && G.adj y w) with
      | nil => rw [hf] at hmem; cases hmem
      | cons _ _ => simp
    dsimp [G] at hge1 ⊢; omega
  have hdegK2uy : degIn G K2 uy = 1 := by
    have hle1 := r6_rigid_K6 C hbal c K2 hK2card hK2clq uy hK2uy_false
    have hge1 : degIn G K2 uy ≥ 1 := by
      unfold degIn
      have hmem : y ∈ (verts (6 * 6 + 1)).filter (fun w => K2 w && G.adj uy w) :=
        List.mem_filter.mpr ⟨mem_verts y, by simp [hK2y, hadj_uy_y]⟩
      cases hf : (verts (6 * 6 + 1)).filter (fun w => K2 w && G.adj uy w) with
      | nil => rw [hf] at hmem; cases hmem
      | cons _ _ => simp
    dsimp [G] at hge1 ⊢; omega
  have hNK1y : NK1 y = true := by simp [NK1, hK1y_false, hdegK1y]
  have hNK2uy : NK2 uy = true := by simp [NK2, hK2uy_false, hdegK2uy]
  have hcr12_eq1 : crossEdges G K1 K2 = 1 := by
    rw [crossEdges_symm G K1 K2]
    unfold crossEdges
    have hsing : ∀ (l : List (Fin (6 * 6 + 1))), l.Nodup → y ∈ l →
        (l.map (fun w => if K2 w = true then degIn G K1 w else 0)).sum = 1 := by
      intro l hnd hym
      induction l with
      | nil => cases hym
      | cons a as ih =>
        rw [List.nodup_cons] at hnd
        rcases List.mem_cons.mp hym with rfl | hym'
        · simp only [List.map_cons, hK2y, ↓reduceIte, hdegK1y, List.sum_cons]
          have h0 : (as.map (fun w => if K2 w = true then degIn G K1 w else 0)).sum = 0 :=
            sum_map_eq_zero _ _ (fun w hw => by
              have hne : w ≠ y := fun h => hnd.1 (h ▸ hw)
              by_cases hK2w : K2 w = true
              · have hK1w_false : K1 w = false := by
                  cases h : K1 w; rfl; have := hdisj12 w; simp [h, hK2w] at this
                have hle1 := r6_rigid_K6 C hbal c K1 hK1card hK1clq w hK1w_false
                have hne1 : degIn G K1 w ≠ 1 := by
                  intro h1
                  have hNK1w : NK1 w = true := by simp [NK1, hK1w_false, h1]
                  have hna := hNK1ind y w hNK1y hNK1w
                  have ha := hK2adj y w hK2y hK2w (Ne.symm hne)
                  dsimp [G] at ha; rw [ha] at hna; exact Bool.noConfusion hna
                have hd0 : degIn G K1 w = 0 := by dsimp [G] at hne1 ⊢; omega
                simp [hK2w, hd0]
              · simp [hK2w])
          omega
        · have hne : a ≠ y := fun h => hnd.1 (h ▸ hym')
          have ha0 : (if K2 a = true then degIn G K1 a else 0) = 0 := by
            by_cases hK2a : K2 a = true
            · have hK1a_false : K1 a = false := by
                cases h : K1 a; rfl; have := hdisj12 a; simp [h, hK2a] at this
              have hle1 := r6_rigid_K6 C hbal c K1 hK1card hK1clq a hK1a_false
              have hne1 : degIn G K1 a ≠ 1 := by
                intro h1
                have hNK1a : NK1 a = true := by simp [NK1, hK1a_false, h1]
                have hna := hNK1ind y a hNK1y hNK1a
                have ha := hK2adj y a hK2y hK2a (Ne.symm hne)
                dsimp [G] at ha; rw [ha] at hna; exact Bool.noConfusion hna
              have hd0 : degIn G K1 a = 0 := by dsimp [G] at hne1 ⊢; omega
              simp [hK2a, hd0]
            · simp [hK2a]
          simp only [List.map_cons, ha0, List.sum_cons, Nat.zero_add]
          exact ih hnd.2 hym'
    exact hsing (verts (6 * 6 + 1)) (nodup_verts _) (mem_verts y)
  -- Step 6: On R = V \ (K1 ∪ K2) (|R| = 25, twoEdgesIn G R = 140 ≤ 162),
  --         show J = NK1 \ {y} = NK2 \ {uy} is the UNIQUE 5-IS in R, then delete z1 ∈ J
  --         to get U1 (|U1| = 24, α ≤ 4, twoEdgesIn = 132 < 140), find K3 ⊆ U1 by Lemma 5,
  --         and prove crossEdges G K1 K3 = 0, contradicting Step 4!
  let K12 : Fin (6 * 6 + 1) → Bool := fun v => K1 v || K2 v
  let R : Fin (6 * 6 + 1) → Bool := fun v => !K1 v && !K2 v
  have hdisj12R : ∀ v, !(K12 v && R v) = true := by
    intro v; cases h1 : K1 v <;> cases h2 : K2 v <;> simp [K12, R, h1, h2]
  have hunion12R : ∀ v, allV v = (K12 v || R v) := by
    intro v; cases h1 : K1 v <;> cases h2 : K2 v <;> simp [allV, K12, R, h1, h2]
  have hK12card : subsetCard K12 = 12 := by
    unfold subsetCard
    have hp := filter_length_partition (verts (6 * 6 + 1)) K12 K1
    have h1 : ((verts (6 * 6 + 1)).filter (fun v => K12 v && K1 v)).length = subsetCard K1 := by
      unfold subsetCard; apply filter_length_eq; intro v _; cases h1v : K1 v <;> simp [K12, h1v]
    have h2 : ((verts (6 * 6 + 1)).filter (fun v => K12 v && !K1 v)).length = subsetCard K2 := by
      unfold subsetCard; apply filter_length_eq; intro v _
      have hd := hdisj12 v; cases h1v : K1 v <;> cases h2v : K2 v <;> simp [K12, h1v, h2v] at hd ⊢
    omega
  have hRcard : subsetCard R = 25 := by
    have hp := filter_length_partition (verts (6 * 6 + 1)) allV K12
    have h1 : ((verts (6 * 6 + 1)).filter (fun v => allV v && K12 v)).length = 12 := by
      have heq : ((verts (6 * 6 + 1)).filter (fun v => allV v && K12 v)).length = subsetCard K12 := by
        unfold subsetCard; apply filter_length_eq; intro v _; simp [allV]
      rw [heq, hK12card]
    have h2 : ((verts (6 * 6 + 1)).filter (fun v => allV v && !K12 v)).length = subsetCard R := by
      unfold subsetCard; apply filter_length_eq; intro v _
      cases h1v : K1 v <;> cases h2v : K2 v <;> simp [allV, K12, R, h1v, h2v]
    unfold subsetCard at hall_card; omega
  have h2eK1 : twoEdgesIn G K1 = 30 := by
    have hcomp := twoEdgesIn_add_compl G K1; have hte := two_mul_edgesIn G.compl K1
    rw [hK1card] at hcomp; rw [hK1clq] at hte; omega
  have h2eK2 : twoEdgesIn G K2 = 30 := by
    have hcomp := twoEdgesIn_add_compl G K2; have hte := two_mul_edgesIn G.compl K2
    rw [hK2card] at hcomp; rw [hK2clq] at hte; omega
  have h2eK12 : twoEdgesIn G K12 = 62 := by
    have h := twoEdgesIn_union_disjoint G K1 K2 hdisj12
    dsimp [G, K12] at h h2eK1 h2eK2 hcr12_eq1 ⊢; omega
  have hcr1R : crossEdges G K1 R = 5 := by
    have hdisjK2R : ∀ v, !(K2 v && R v) = true := by intro v; cases h1 : K1 v <;> cases h2 : K2 v <;> simp [R, h1, h2]
    have hunion1 : ∀ v, W1 v = (K2 v || R v) := by
      intro v; have hd := hdisj12 v; cases h1v : K1 v <;> cases h2v : K2 v <;> simp [W1, R, h1v, h2v] at hd ⊢
    have h := sum_degIn_union_disjoint G K1 K2 R hdisjK2R
    rw [← crossEdges_congr G (fun _ => rfl) hunion1] at h
    dsimp [G, W1] at h hcr1 hcr12_eq1 ⊢; omega
  have hcr2R : crossEdges G K2 R = 5 := by
    have hdisjK1R : ∀ v, !(K1 v && R v) = true := by intro v; cases h1 : K1 v <;> cases h2 : K2 v <;> simp [R, h1, h2]
    have hunion2 : ∀ v, W2 v = (K1 v || R v) := by
      intro v; have hd := hdisj12 v; cases h1v : K1 v <;> cases h2v : K2 v <;> simp [W2, R, h1v, h2v] at hd ⊢
    have h := sum_degIn_union_disjoint G K2 K1 R hdisjK1R
    rw [← crossEdges_congr G (fun _ => rfl) hunion2, crossEdges_symm G K2 K1] at h
    dsimp [G, W2] at h hcr2 hcr12_eq1 ⊢; omega
  have hcr12R : crossEdges G K12 R = 10 := by
    rw [crossEdges_symm G K12 R]
    have h := sum_degIn_union_disjoint G R K1 K2 hdisj12
    rw [crossEdges_symm G R K1, crossEdges_symm G R K2] at h
    change crossEdges G R (fun w => K1 w || K2 w) = 10
    rw [h]; omega
  have h2eR : twoEdgesIn G R = 140 := by
    have h := twoEdgesIn_union_disjoint G K12 R hdisj12R
    have hcongr : twoEdgesIn G allV = twoEdgesIn G (fun v => K12 v || R v) := by
      rw [twoEdgesIn_eq_double_sum, twoEdgesIn_eq_double_sum]
      apply sum_map_eq; intro x _; apply sum_map_eq; intro y _
      cases h1x : K1 x <;> cases h2x : K2 x <;> cases h1y : K1 y <;> cases h2y : K2 y <;>
        simp [allV, K12, R, h1x, h2x, h1y, h2y]
    rw [← hcongr, h2e_all, h2eK12, hcr12R] at h; omega
  -- Define J1 = NK1 \ {y} and J2 = NK2 \ {uy}; both have size 5
  let J1 : Fin (6 * 6 + 1) → Bool := fun v => NK1 v && !decide (v = y)
  let J2 : Fin (6 * 6 + 1) → Bool := fun v => NK2 v && !decide (v = uy)
  have hNK2c : subsetCard NK2 = 6 := hNK2card
  have hJ1card : subsetCard J1 = 5 := by
    have ⟨hc, _⟩ := erase_vertex_stats G NK1 y hNK1y
    have hc' : subsetCard J1 + 1 = subsetCard NK1 := hc
    omega
  have hJ2card : subsetCard J2 = 5 := by
    have ⟨hc, _⟩ := erase_vertex_stats G NK2 uy hNK2uy
    have hc' : subsetCard J2 + 1 = subsetCard NK2 := hc
    omega
  -- Helper: y has degIn G R y = 0, and uy has degIn G R uy = 0!
  have hy_no_R : ∀ w, R w = true → G.adj y w = false := by
    have h5 : degIn G K2 y = 5 := by have := hK2deg y hK2y; omega
    have hsp1 := degIn_union_disjoint G K12 R hdisj12R y
    have hsp2 := degIn_union_disjoint G K1 K2 hdisj12 y
    have hcongr : degIn G allV y = degIn G (fun w => K12 w || R w) y := by
      unfold degIn; apply filter_length_eq; intro w _; rw [hunion12R w]
    have hdegRy0 : degIn G R y = 0 := by
      have h6 := hreg y
      rw [hcongr, hsp1] at h6
      have hk : degIn G K12 y = degIn G K1 y + degIn G K2 y := hsp2
      omega
    intro w hRw
    cases ha : G.adj y w
    · rfl
    · exfalso
      have hmem : w ∈ (verts (6 * 6 + 1)).filter (fun x => R x && G.adj y x) :=
        List.mem_filter.mpr ⟨mem_verts w, by simp [hRw, ha]⟩
      unfold degIn at hdegRy0
      cases hf : (verts (6 * 6 + 1)).filter (fun x => R x && G.adj y x) with
      | nil => rw [hf] at hmem; cases hmem
      | cons _ _ => rw [hf] at hdegRy0; simp at hdegRy0
  have huy_no_R : ∀ w, R w = true → G.adj uy w = false := by
    have ⟨_, hK1deg⟩ := clique_adj_and_deg G K1 hK1clq
    have h5 : degIn G K1 uy = 5 := by have := hK1deg uy hK1uy; omega
    have hsp1 := degIn_union_disjoint G K12 R hdisj12R uy
    have hsp2 := degIn_union_disjoint G K1 K2 hdisj12 uy
    have hcongr : degIn G allV uy = degIn G (fun w => K12 w || R w) uy := by
      unfold degIn; apply filter_length_eq; intro w _; rw [hunion12R w]
    have hdegRuy0 : degIn G R uy = 0 := by
      have h6 := hreg uy
      rw [hcongr, hsp1] at h6
      have hk : degIn G K12 uy = degIn G K1 uy + degIn G K2 uy := hsp2
      omega
    intro w hRw
    cases ha : G.adj uy w
    · rfl
    · exfalso
      have hmem : w ∈ (verts (6 * 6 + 1)).filter (fun x => R x && G.adj uy x) :=
        List.mem_filter.mpr ⟨mem_verts w, by simp [hRw, ha]⟩
      unfold degIn at hdegRuy0
      cases hf : (verts (6 * 6 + 1)).filter (fun x => R x && G.adj uy x) with
      | nil => rw [hf] at hmem; cases hmem
      | cons _ _ => rw [hf] at hdegRuy0; simp at hdegRuy0
  -- Any 5-IS I ⊆ R must satisfy I = J1 AND I = J2!
  have huniq_R_J1 : ∀ I : Fin (6 * 6 + 1) → Bool, (∀ w, I w = true → R w = true) →
      IsIndep G I → subsetCard I = 5 → ∀ w, I w = J1 w := by
    intro I hIsub hIind hIcard
    have hsub : ∀ z, J1 z = true → I z = true := by
      intro z hJ1z
      cases hIz : I z
      · exfalso
        have hJ1z' := Bool.and_eq_true _ _ |>.mp hJ1z
        have hNK1z := hJ1z'.1
        have hzy : z ≠ y := by simpa using hJ1z'.2
        have hdegK1z : degIn G K1 z = 1 := of_decide_eq_true (Bool.and_eq_true _ _ |>.mp hNK1z).2
        obtain ⟨u1, hK1u1, hadj_zu1, _⟩ := unique_nbr_of_degIn_eq_one G K1 z hdegK1z
        obtain ⟨z', _, _, huniq_u1⟩ := unique_nbr_of_degIn_eq_one G W1 u1 (hdegW1 u1 hK1u1)
        have hzz' : z = z' := huniq_u1 z (Bool.and_eq_true _ _ |>.mp hNK1z).1 (by rw [G.symm]; exact hadj_zu1)
        have hu1_ne_y : u1 ≠ y := fun h => by subst h; simp [hK1y_false] at hK1u1
        -- G.adj u1 y = false (since u1 ≠ uy, and uy is the unique neighbor of y in K1)
        have hna_u1_y : G.adj u1 y = false := by
          cases ha : G.adj u1 y
          · rfl
          · exfalso
            have hyz' := huniq_u1 y (by simp [W1, hK1y_false]) ha
            exact hzy (hzz'.trans hyz'.symm)
        have hIu1 : I u1 = false := by
          cases hi : I u1; rfl; have := hIsub u1 hi; simp [R, hK1u1] at this
        have hIy : I y = false := by
          cases hi : I y; rfl; have := hIsub y hi; simp [R, hK2y] at this
        -- I ∪ {u1, y} is a 7-IS!
        let I' : Fin (6 * 6 + 1) → Bool := fun w => I w || decide (w = u1) || decide (w = y)
        have hI'ind : IsIndep G I' := by
          intro p q hp hq
          simp only [I', Bool.or_eq_true, decide_eq_true_eq] at hp hq
          rcases hp with (hIp | rfl) | rfl <;> rcases hq with (hIq | rfl) | rfl
          · exact hIind p q hIp hIq
          · cases ha : G.adj p q
            · rfl
            · exfalso
              have hp1 := huniq_u1 p (Bool.and_eq_true _ _ |>.mp (hIsub p hIp)).1 (by rw [G.symm]; exact ha)
              subst hp1; subst hzz'; simp [hIz] at hIp
          · rw [G.symm]; exact hy_no_R p (hIsub p hIp)
          · cases ha : G.adj p q
            · rfl
            · exfalso
              have hq1 := huniq_u1 q (Bool.and_eq_true _ _ |>.mp (hIsub q hIq)).1 ha
              subst hq1; subst hzz'; simp [hIz] at hIq
          · exact G.loopless _
          · exact hna_u1_y
          · exact hy_no_R q (hIsub q hIq)
          · rw [G.symm]; exact hna_u1_y
          · exact G.loopless _
        have hI'card : subsetCard I' = 7 := by
          unfold subsetCard
          have hp1 := filter_length_partition (verts (6 * 6 + 1)) I' (fun w => decide (w = u1))
          have h1 : ((verts (6 * 6 + 1)).filter (fun w => I' w && decide (w = u1))).length = 1 := by
            have heq : ((verts (6 * 6 + 1)).filter (fun w => I' w && decide (w = u1))).length =
                       ((verts (6 * 6 + 1)).filter (fun w => decide (w = u1))).length := by
              apply filter_length_eq; intro w _
              by_cases hw : w = u1; subst hw; simp [I']; simp [I', hw]
            rw [heq]; exact length_filter_eq_one_of_nodup _ (nodup_verts _) u1 (mem_verts u1)
          have hp2 := filter_length_partition (verts (6 * 6 + 1)) (fun w => I' w && !decide (w = u1)) (fun w => decide (w = y))
          have h2 : ((verts (6 * 6 + 1)).filter (fun w => (I' w && !decide (w = u1)) && decide (w = y))).length = 1 := by
            have heq : ((verts (6 * 6 + 1)).filter (fun w => (I' w && !decide (w = u1)) && decide (w = y))).length =
                       ((verts (6 * 6 + 1)).filter (fun w => decide (w = y))).length := by
              apply filter_length_eq; intro w _
              by_cases hw : w = y; subst hw; simp [I', Ne.symm hu1_ne_y]; simp [I', hw]
            rw [heq]; exact length_filter_eq_one_of_nodup _ (nodup_verts _) y (mem_verts y)
          have h3 : ((verts (6 * 6 + 1)).filter (fun w => (I' w && !decide (w = u1)) && !decide (w = y))).length =
                    subsetCard I := by
            unfold subsetCard; apply filter_length_eq; intro w _
            by_cases hw1 : w = u1; subst hw1; simp [I', hIu1]
            by_cases hw2 : w = y; subst hw2; simp [I', hIy]
            simp [I', hw1, hw2]
          omega
        have hle6 := isBalanced_indep_le C hbal c I' hI'ind
        omega
      · rfl
    exact fun w => (eq_of_sub_and_card_eq J1 I hsub (by omega) w).symm
  have huniq_R_J2 : ∀ I : Fin (6 * 6 + 1) → Bool, (∀ w, I w = true → R w = true) →
      IsIndep G I → subsetCard I = 5 → ∀ w, I w = J2 w := by
    intro I hIsub hIind hIcard
    have hsub : ∀ z, J2 z = true → I z = true := by
      intro z hJ2z
      cases hIz : I z
      · exfalso
        have hJ2z' := Bool.and_eq_true _ _ |>.mp hJ2z
        have hNK2z := hJ2z'.1
        have hzuy : z ≠ uy := by simpa using hJ2z'.2
        have hdegK2z : degIn G K2 z = 1 := of_decide_eq_true (Bool.and_eq_true _ _ |>.mp hNK2z).2
        obtain ⟨u2, hK2u2, hadj_zu2, _⟩ := unique_nbr_of_degIn_eq_one G K2 z hdegK2z
        obtain ⟨z', _, _, huniq_u2⟩ := unique_nbr_of_degIn_eq_one G W2 u2 (hdegW2 u2 hK2u2)
        have hzz' : z = z' := huniq_u2 z (Bool.and_eq_true _ _ |>.mp hNK2z).1 (by rw [G.symm]; exact hadj_zu2)
        have hu2_ne_uy : u2 ≠ uy := fun h => by subst h; simp [hK2uy_false] at hK2u2
        have hna_u2_uy : G.adj u2 uy = false := by
          cases ha : G.adj u2 uy
          · rfl
          · exfalso
            have huyz' := huniq_u2 uy (by simp [W2, hK2uy_false]) ha
            exact hzuy (hzz'.trans huyz'.symm)
        have hIu2 : I u2 = false := by
          cases hi : I u2; rfl; have := hIsub u2 hi; simp [R, hK2u2] at this
        have hIuy : I uy = false := by
          cases hi : I uy; rfl; have := hIsub uy hi; simp [R, hK1uy] at this
        let I' : Fin (6 * 6 + 1) → Bool := fun w => I w || decide (w = u2) || decide (w = uy)
        have hI'ind : IsIndep G I' := by
          intro p q hp hq
          simp only [I', Bool.or_eq_true, decide_eq_true_eq] at hp hq
          rcases hp with (hIp | rfl) | rfl <;> rcases hq with (hIq | rfl) | rfl
          · exact hIind p q hIp hIq
          · cases ha : G.adj p q
            · rfl
            · exfalso
              have hp2 := huniq_u2 p (Bool.and_eq_true _ _ |>.mp (hIsub p hIp)).2 (by rw [G.symm]; exact ha)
              subst hp2; subst hzz'; simp [hIz] at hIp
          · rw [G.symm]; exact huy_no_R p (hIsub p hIp)
          · cases ha : G.adj p q
            · rfl
            · exfalso
              have hq2 := huniq_u2 q (Bool.and_eq_true _ _ |>.mp (hIsub q hIq)).2 ha
              subst hq2; subst hzz'; simp [hIz] at hIq
          · exact G.loopless _
          · exact hna_u2_uy
          · exact huy_no_R q (hIsub q hIq)
          · rw [G.symm]; exact hna_u2_uy
          · exact G.loopless _
        have hI'card : subsetCard I' = 7 := by
          unfold subsetCard
          have hp1 := filter_length_partition (verts (6 * 6 + 1)) I' (fun w => decide (w = u2))
          have h1 : ((verts (6 * 6 + 1)).filter (fun w => I' w && decide (w = u2))).length = 1 := by
            have heq : ((verts (6 * 6 + 1)).filter (fun w => I' w && decide (w = u2))).length =
                       ((verts (6 * 6 + 1)).filter (fun w => decide (w = u2))).length := by
              apply filter_length_eq; intro w _
              by_cases hw : w = u2; subst hw; simp [I']; simp [I', hw]
            rw [heq]; exact length_filter_eq_one_of_nodup _ (nodup_verts _) u2 (mem_verts u2)
          have hp2 := filter_length_partition (verts (6 * 6 + 1)) (fun w => I' w && !decide (w = u2)) (fun w => decide (w = uy))
          have h2 : ((verts (6 * 6 + 1)).filter (fun w => (I' w && !decide (w = u2)) && decide (w = uy))).length = 1 := by
            have heq : ((verts (6 * 6 + 1)).filter (fun w => (I' w && !decide (w = u2)) && decide (w = uy))).length =
                       ((verts (6 * 6 + 1)).filter (fun w => decide (w = uy))).length := by
              apply filter_length_eq; intro w _
              by_cases hw : w = uy; subst hw; simp [I', Ne.symm hu2_ne_uy]; simp [I', hw]
            rw [heq]; exact length_filter_eq_one_of_nodup _ (nodup_verts _) uy (mem_verts uy)
          have h3 : ((verts (6 * 6 + 1)).filter (fun w => (I' w && !decide (w = u2)) && !decide (w = uy))).length =
                    subsetCard I := by
            unfold subsetCard; apply filter_length_eq; intro w _
            by_cases hw1 : w = u2; subst hw1; simp [I', hIu2]
            by_cases hw2 : w = uy; subst hw2; simp [I', hIuy]
            simp [I', hw1, hw2]
          omega
        have hle6 := isBalanced_indep_le C hbal c I' hI'ind
        omega
      · rfl
    exact fun w => (eq_of_sub_and_card_eq J2 I hsub (by omega) w).symm
  -- Lemma 4 gives a 5-IS I0 ⊆ R ⇒ J1 = J2 and J1 ⊆ R!
  have hno4 := no_25_alpha_le_4_e_le_81 C hbal c R hRcard (by dsimp [G] at h2eR; omega)
  have hex5 : ∃ I0 : Fin (6 * 6 + 1) → Bool, (∀ w, I0 w = true → R w = true) ∧
      IsIndep G I0 ∧ subsetCard I0 = 5 := by
    apply Classical.byContradiction; intro hnone
    apply hno4; intro I hIsub hIind
    by_cases h4 : subsetCard I ≤ 4
    · exact h4
    · exfalso
      obtain ⟨I5, hI5sub, hI5card⟩ := exists_sub_card I 5 (by omega)
      exact hnone ⟨I5, fun w hw => hIsub w (hI5sub w hw), isIndep_mono hI5sub hIind, hI5card⟩
  obtain ⟨I0, hI0sub, hI0ind, hI0card⟩ := hex5
  have hI0_J1 := huniq_R_J1 I0 hI0sub hI0ind hI0card
  have hI0_J2 := huniq_R_J2 I0 hI0sub hI0ind hI0card
  have hJ1_eq_J2 : ∀ w, J1 w = J2 w := fun w => (hI0_J1 w).symm.trans (hI0_J2 w)
  -- Pick z1 ∈ J1 (|J1| = 5 ≥ 1), delete z1 from R to get U1 (|U1| = 24, α ≤ 4, twoEdgesIn = 132 < 140)!
  obtain ⟨z1, hJ1z1⟩ := exists_mem_of_subsetCard_pos J1 (by omega)
  have hRz1 : R z1 = true := hI0sub z1 (by rw [hI0_J1 z1]; exact hJ1z1)
  have hJ2z1 : J2 z1 = true := by rw [← hJ1_eq_J2 z1]; exact hJ1z1
  have hdegK1z1 : degIn G K1 z1 = 1 :=
    of_decide_eq_true (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp hJ1z1).1).2
  have hdegK2z1 : degIn G K2 z1 = 1 :=
    of_decide_eq_true (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp hJ2z1).1).2
  have hdegRz1 : degIn G R z1 = 4 := by
    have hsp1 := degIn_union_disjoint G K12 R hdisj12R z1
    have hsp2 := degIn_union_disjoint G K1 K2 hdisj12 z1
    have hcongr : degIn G allV z1 = degIn G (fun w => K12 w || R w) z1 := by
      unfold degIn; apply filter_length_eq; intro w _; rw [hunion12R w]
    have h6 := hreg z1
    rw [hcongr, hsp1] at h6
    have hk : degIn G K12 z1 = degIn G K1 z1 + degIn G K2 z1 := hsp2
    omega
  let U1 : Fin (6 * 6 + 1) → Bool := fun v => R v && !decide (v = z1)
  obtain ⟨hU1card', hU1_2e'⟩ := erase_vertex_stats G R z1 hRz1
  have hU1card : subsetCard U1 = 24 := by
    have hc : subsetCard U1 + 1 = subsetCard R := hU1card'
    omega
  have hU1_2e : twoEdgesIn G U1 = 132 := by
    have h2e : twoEdgesIn G U1 + 2 * degIn G R z1 = twoEdgesIn G R := hU1_2e'
    omega
  have hαU1 : ∀ I, (∀ v, I v = true → U1 v = true) → IsIndep G I → subsetCard I ≤ 4 := by
    intro I hIsub hIind
    by_cases h4 : subsetCard I ≤ 4
    · exact h4
    · exfalso
      obtain ⟨I5, hI5sub, hI5card⟩ := exists_sub_card I 5 (by omega)
      have heq := huniq_R_J1 I5 (fun w hw => (Bool.and_eq_true _ _ |>.mp (hIsub w (hI5sub w hw))).1)
        (isIndep_mono hI5sub hIind) hI5card
      have hI5z1 : I5 z1 = true := by rw [heq z1]; exact hJ1z1
      have hU1z1 := hIsub z1 (hI5sub z1 hI5z1); simp [U1] at hU1z1
  -- Lemma 5 gives a K₆ (`K3`) inside U1 ⊆ R!
  have hexK3 : HasK6In G U1 := by
    apply Classical.byContradiction; intro hnoK6
    have hge140 := K6_free_24_edges_ge_70 C hbal c U1 hU1card hαU1 hnoK6
    dsimp [G] at hU1_2e; omega
  obtain ⟨K3, hK3subU1, hK3card, hK3clq⟩ := hexK3
  have hK3subR : ∀ w, K3 w = true → R w = true :=
    fun w hw => (Bool.and_eq_true _ _ |>.mp (hK3subU1 w hw)).1
  have hdisj13 : ∀ v, !(K1 v && K3 v) = true := by
    intro v; cases h1 : K1 v; simp
    cases h3 : K3 v; simp
    exfalso; have := hK3subR v h3; simp [R, h1] at this
  -- Every w ∈ K3 has degIn G K1 w = 0 (else w ∈ J1 = J2 ⇒ degIn K1 + degIn K2 + degIn K3 = 1 + 1 + 5 = 7 > 6)!
  have hcr13_zero : crossEdges G K1 K3 = 0 := by
    rw [crossEdges_eq_zero_iff]
    intro u w hK1u hK3w
    cases ha : G.adj u w
    · rfl
    · exfalso
      have hRw := hK3subR w hK3w
      have hK1w_false : K1 w = false := by have := (Bool.and_eq_true _ _ |>.mp hRw).1; simpa using this
      have hK2w_false : K2 w = false := by have := (Bool.and_eq_true _ _ |>.mp hRw).2; simpa using this
      have hwy : w ≠ y := fun h => by subst h; simp [hK2y] at hK2w_false
      have hdegK1w : degIn G K1 w = 1 := by
        have hle1 := r6_rigid_K6 C hbal c K1 hK1card hK1clq w hK1w_false
        have hge1 : degIn G K1 w ≥ 1 := by
          unfold degIn
          have hmem : u ∈ (verts (6 * 6 + 1)).filter (fun x => K1 x && G.adj w x) :=
            List.mem_filter.mpr ⟨mem_verts u, by rw [G.symm]; simp [hK1u, ha]⟩
          cases hf : (verts (6 * 6 + 1)).filter (fun x => K1 x && G.adj w x) with
          | nil => rw [hf] at hmem; cases hmem
          | cons _ _ => simp
        dsimp [G] at hge1 ⊢; omega
      have hJ1w : J1 w = true := by simp [J1, NK1, hK1w_false, hdegK1w, hwy]
      have hJ2w : J2 w = true := by rw [← hJ1_eq_J2 w]; exact hJ1w
      have hdegK2w : degIn G K2 w = 1 :=
        of_decide_eq_true (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp hJ2w).1).2
      have ⟨_, hK3deg⟩ := clique_adj_and_deg G K3 hK3clq
      have hdegK3w : degIn G K3 w = 5 := by have := hK3deg w hK3w; omega
      -- Since K1, K2, K3 are pairwise disjoint, degIn G allV w ≥ degIn K1 + degIn K2 + degIn K3 = 7 > 6!
      have hdisj12_3 : ∀ x, !(K12 x && K3 x) = true := by
        intro x; cases h3 : K3 x
        · simp
        · have hRx := hK3subR x h3
          have h1f : K1 x = false := by have := (Bool.and_eq_true _ _ |>.mp hRx).1; simpa using this
          have h2f : K2 x = false := by have := (Bool.and_eq_true _ _ |>.mp hRx).2; simpa using this
          simp [K12, h1f, h2f]
      have hle_all : degIn G (fun x => K12 x || K3 x) w ≤ degIn G allV w :=
        filter_length_le (verts (6 * 6 + 1)) _ _ (fun x _ hx => by
          have := (Bool.and_eq_true _ _ |>.mp hx).2; simp [allV, this])
      have hsp1 := degIn_union_disjoint G K12 K3 hdisj12_3 w
      have hsp2 := degIn_union_disjoint G K1 K2 hdisj12 w
      have h6 := hreg w
      have hk : degIn G K12 w = degIn G K1 w + degIn G K2 w := hsp2
      rw [hsp1] at hle_all
      omega
  -- Contradiction with Step 4 (no two disjoint K₆'s have zero cross-edges)!
  exact no_disjoint_K6_zero_cross C hbal c hreg K1 K3 hK1card hK1clq hK3card hK3clq hdisj13 hcr13_zero

end Erdos617
