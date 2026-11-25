/-
  Erdős Problem #617 — Strengthened Füredi Peel Stability & Exact 2-Partition Reduction for r = 6 (K₃₇)
  Imports `Erdos617_r6`. Zero sorry, zero axiom, zero admit, zero native_decide.

  Main Results:
  1. `furedi_peel_stability`: Strengthened Füredi stability keeping the exact peel order
     `B_0, ..., B_{r-1}`, prefix independence bounds `α(G[S_j]) ≤ j + 1`, prefix minimum degrees
     `∀ u ∈ S_j, deg_{S_j}(u) ≥ s_j - 1`, exact step cross-edge identity
     `crossEdges G A_j B_j = twoEdgesIn G.compl B_j + peelDeficit G S part j`, and exact total identity
     `twoEdgesIn G S = ∑_j (s_j * (s_j - 1) + twoEdgesIn G.compl B_j + 2 * D_j)`.
  2. `furedi_peel_sparsest`: Application to the sparsest color class of any balanced r-coloring
     of `K_{r²+1}` (`r ≥ 3`).
  3. `r4_unique_partition`: Immediate corollary at `r = 4` (`K₁₇`) — forces the unique sorted
     partition `[5, 4, 4, 4]`.
  4. `r6_no_size_8_part` & `r6_exact_two_partitions`: At `r = 6` (`K₃₇`), eliminates all 6 tight
     partitions (overflow 3) via the exact imbalance identity, and eliminates `[8, 6, 6, 6, 6, 5]`
     across all 30 peel orderings via prefix clique/α≤2 bounds (`no_2r_plus_1_alpha_le_2`),
     prefix minimum-degree counting, and `multiscale_turan_complement` on `B_1 ∪ B_2`.
     Reduces ALL balanced 6-colorings of `K₃₇` to ONLY TWO sorted Füredi peel partitions:
       - `[7, 7, 6, 6, 6, 5]` (with `m_in + D_ex ≤ 14`, total slack `≤ 4`), or
       - `[7, 6, 6, 6, 6, 6]` (with `m_in + D_ex ≤ 15`, total slack `≤ 10`).
-/

import Erdos617_r6

namespace Erdos617

/-! ## Section 1: Cross-Edge Helpers -/

theorem sum_map_eq_zero {α : Type} (l : List α) (f : α → Nat) (h : ∀ x ∈ l, f x = 0) :
    (l.map f).sum = 0 := by
  rw [sum_map_eq l f (fun _ => 0) h, sum_map_const]
  simp

/-- Number of edges of `G` with one endpoint in `X` and the other in `Y` (counted once per ordered
    pair `(u, v) ∈ X × Y`). When `X` and `Y` are disjoint, this equals the number of edges between
    `X` and `Y`. -/
def crossEdges {n : Nat} (G : SGraph n) (X Y : Fin n → Bool) : Nat :=
  ((verts n).map (fun u => if X u then degIn G Y u else 0)).sum

theorem crossEdges_eq_double_sum {n : Nat} (G : SGraph n) (X Y : Fin n → Bool) :
    crossEdges G X Y =
      ((verts n).map (fun u => ((verts n).map (fun v => if X u && Y v && G.adj u v then 1 else 0)).sum)).sum := by
  unfold crossEdges degIn
  apply sum_map_eq; intro u _
  by_cases hX : X u = true
  · simp only [hX, ↓reduceIte, Bool.true_and]
    exact length_filter_eq_sum (verts n) (fun v => Y v && G.adj u v)
  · have hXf : X u = false := by cases h : X u; rfl; exact absurd h hX
    simp only [hXf, Bool.false_eq_true, ↓reduceIte, Bool.false_and]
    symm
    exact sum_map_eq_zero _ _ (fun _ _ => rfl)

theorem crossEdges_symm {n : Nat} (G : SGraph n) (X Y : Fin n → Bool) :
    crossEdges G X Y = crossEdges G Y X := by
  rw [crossEdges_eq_double_sum, crossEdges_eq_double_sum]
  rw [sum_swap]
  apply sum_map_eq; intro v _
  apply sum_map_eq; intro u _
  rw [G.symm u v]
  cases X u <;> cases Y v <;> cases G.adj v u <;> rfl

theorem crossEdges_add_compl {n : Nat} (G : SGraph n) (X Y : Fin n → Bool)
    (hdisj : ∀ v : Fin n, !(X v && Y v) = true) :
    crossEdges G X Y + crossEdges G.compl X Y = subsetCard X * subsetCard Y := by
  rw [crossEdges_eq_double_sum, crossEdges_eq_double_sum, ← sum_map_add]
  have h1 : ((verts n).map (fun u =>
      ((verts n).map (fun v => if X u && Y v && G.adj u v then 1 else 0)).sum +
      ((verts n).map (fun v => if X u && Y v && G.compl.adj u v then 1 else 0)).sum)).sum =
      ((verts n).map (fun u => if X u then subsetCard Y else 0)).sum := by
    apply sum_map_eq; intro u _
    rw [← sum_map_add]
    by_cases hX : X u = true
    · simp only [hX, ↓reduceIte, Bool.true_and]
      unfold subsetCard
      rw [length_filter_eq_sum]
      apply sum_map_eq; intro v _
      by_cases hY : Y v = true
      · have huv : u ≠ v := by
          intro heq; subst heq
          have := hdisj u; simp [hX, hY] at this
        cases hG : G.adj u v <;> simp [hY, SGraph.compl, huv, hG]
      · have hYf : Y v = false := by cases h : Y v; rfl; exact absurd h hY
        simp [hYf]
    · have hXf : X u = false := by cases h : X u; rfl; exact absurd h hX
      simp only [hXf, Bool.false_eq_true, ↓reduceIte, Bool.false_and]
      exact sum_map_eq_zero _ _ (fun _ _ => rfl)
  rw [h1]
  have h2 : ((verts n).map (fun u => if X u then subsetCard Y else 0)).sum =
            subsetCard Y * ((verts n).map (fun u => if X u then 1 else 0)).sum := by
    rw [← sum_map_mul_left]
    apply sum_map_eq; intro u _
    cases X u <;> simp
  rw [h2, ← length_filter_eq_sum, Nat.mul_comm]
  rfl

theorem twoEdgesIn_union_disjoint {n : Nat} (G : SGraph n) (A B : Fin n → Bool)
    (hdisj : ∀ v : Fin n, !(A v && B v) = true) :
    twoEdgesIn G (fun v => A v || B v) = twoEdgesIn G A + twoEdgesIn G B + 2 * crossEdges G A B := by
  have hAB : ∀ v : Fin n, A v = true → B v = false := by
    intro v hA; have := hdisj v; simp [hA] at this; exact this
  rw [twoEdgesIn_eq_double_sum, twoEdgesIn_eq_double_sum, twoEdgesIn_eq_double_sum]
  have h2c : 2 * crossEdges G A B = crossEdges G A B + crossEdges G B A := by
    rw [crossEdges_symm G B A]; omega
  rw [h2c, crossEdges_eq_double_sum, crossEdges_eq_double_sum]
  rw [← sum_map_add, ← sum_map_add, ← sum_map_add]
  apply sum_map_eq; intro u _
  rw [← sum_map_add, ← sum_map_add, ← sum_map_add]
  apply sum_map_eq; intro v _
  by_cases hAu : A u = true
  · have hBu := hAB u hAu
    by_cases hAv : A v = true
    · have hBv := hAB v hAv
      simp [hAu, hBu, hAv, hBv]
    · have hAvf : A v = false := by cases h : A v; rfl; exact absurd h hAv
      cases B v <;> simp [hAu, hBu, hAvf]
  · have hAuf : A u = false := by cases h : A u; rfl; exact absurd h hAu
    by_cases hBu : B u = true
    · by_cases hAv : A v = true
      · have hBv := hAB v hAv
        simp [hAuf, hBu, hAv, hBv]
      · have hAvf : A v = false := by cases h : A v; rfl; exact absurd h hAv
        cases B v <;> simp [hAuf, hBu, hAvf]
    · have hBuf : B u = false := by cases h : B u; rfl; exact absurd h hBu
      simp [hAuf, hBuf]

theorem sum_degIn_union_disjoint {n : Nat} (G : SGraph n) (X A B : Fin n → Bool)
    (hdisj : ∀ v : Fin n, !(A v && B v) = true) :
    crossEdges G X (fun v => A v || B v) = crossEdges G X A + crossEdges G X B := by
  rw [crossEdges_eq_double_sum, crossEdges_eq_double_sum, crossEdges_eq_double_sum, ← sum_map_add]
  apply sum_map_eq; intro u _
  rw [← sum_map_add]
  apply sum_map_eq; intro v _
  by_cases hAv : A v = true
  · have hBv : B v = false := by have := hdisj v; simp [hAv] at this; exact this
    simp [hAv, hBv]
  · have hAvf : A v = false := by cases h : A v; rfl; exact absurd h hAv
    cases B v <;> simp [hAvf]

theorem crossEdges_self {n : Nat} (G : SGraph n) (X : Fin n → Bool) :
    crossEdges G X X = twoEdgesIn G X := by
  rw [crossEdges_eq_double_sum, twoEdgesIn_eq_double_sum]

theorem crossEdges_congr {n : Nat} (G : SGraph n) {X X' Y Y' : Fin n → Bool}
    (hX : ∀ v, X v = X' v) (hY : ∀ v, Y v = Y' v) :
    crossEdges G X Y = crossEdges G X' Y' := by
  rw [crossEdges_eq_double_sum, crossEdges_eq_double_sum]
  apply sum_map_eq; intro u _
  apply sum_map_eq; intro v _
  rw [hX u, hY v]

theorem crossEdges_le_sum_degIn {n : Nat} (G : SGraph n) (X Y : Fin n → Bool) (d : Nat)
    (hmin : ∀ u : Fin n, X u = true → degIn G Y u ≥ d) :
    crossEdges G X Y ≥ subsetCard X * d := by
  unfold crossEdges
  have h1 : subsetCard X * d = ((verts n).map (fun u => if X u then d else 0)).sum := by
    have h2 : ((verts n).map (fun u => if X u then d else 0)).sum =
              d * ((verts n).map (fun u => if X u then 1 else 0)).sum := by
      rw [← sum_map_mul_left]
      apply sum_map_eq; intro u _; cases X u <;> simp
    rw [h2, ← length_filter_eq_sum, Nat.mul_comm]; rfl
  rw [h1]
  apply sum_map_le
  intro u _
  by_cases hX : X u = true
  · simp only [hX, ↓reduceIte]; exact hmin u hX
  · have hXf : X u = false := by cases h : X u; rfl; exact absurd h hX
    simp [hXf]

/-! ## Section 2: Strengthened Füredi Peel Stability -/

/-- The `j`-th peel part `B_j = {v ∈ S : part v = j}`. -/
def peelPart {n r : Nat} (S : Fin n → Bool) (part : Fin n → Fin r) (j : Fin r) : Fin n → Bool :=
  fun v => S v && decide (part v = j)

/-- The `j`-th peel prefix `S_j = {v ∈ S : part v ≤ j}`. -/
def peelPrefix {n r : Nat} (S : Fin n → Bool) (part : Fin n → Fin r) (j : Fin r) : Fin n → Bool :=
  fun v => S v && decide ((part v).val ≤ j.val)

/-- The strict prefix before `j`, `A_j = {v ∈ S : part v < j}`. -/
def peelPrev {n r : Nat} (S : Fin n → Bool) (part : Fin n → Fin r) (j : Fin r) : Fin n → Bool :=
  fun v => S v && decide ((part v).val < j.val)

/-- The step-`j` degree excess `D_j = ∑_{u ∈ B_j} (deg_{S_j}(u) - (|B_j| - 1))`. -/
def peelDeficit {n r : Nat} (G : SGraph n) (S : Fin n → Bool) (part : Fin n → Fin r) (j : Fin r) : Nat :=
  ((verts n).map (fun u =>
    if peelPart S part j u then
      degIn G (peelPrefix S part j) u - (subsetCard (peelPart S part j) - 1)
    else 0)).sum

/-- Core induction for Füredi's peel: constructs `part : Fin n → Fin r` whose prefixes satisfy
    `α(G[S_j]) ≤ j + 1` and minimum degree `∀ u ∈ S_j, deg_{S_j}(u) ≥ |B_j| - 1`. -/
theorem furedi_peel_exists {n : Nat} (G : SGraph n) (r : Nat) (hr : r ≥ 1) :
    ∀ S : Fin n → Bool,
      (∀ I : Fin n → Bool, (∀ v, I v = true → S v = true) → IsIndep G I → subsetCard I ≤ r) →
      ∃ part : Fin n → Fin r,
        (∀ j : Fin r, ∀ I : Fin n → Bool,
          (∀ v, I v = true → peelPrefix S part j v = true) → IsIndep G I → subsetCard I ≤ j.val + 1) ∧
        (∀ j : Fin r, ∀ u : Fin n,
          peelPrefix S part j u = true →
          degIn G (peelPrefix S part j) u ≥ subsetCard (peelPart S part j) - 1) := by
  induction r with
  | zero => omega
  | succ r0 ih =>
    intro S hα
    cases r0 with
    | zero =>
      -- Base case r = 1: S is a clique!
      refine ⟨fun _ => ⟨0, by omega⟩, ?_, ?_⟩
      · intro j I hIsub hIind
        have hj0 : j.val = 0 := by omega
        rw [hj0]
        apply hα I _ hIind
        intro v hv
        exact (Bool.and_eq_true _ _ |>.mp (hIsub v hv)).1
      · intro j u hu
        have hpref : ∀ x, peelPrefix S (fun _ => (⟨0, by omega⟩ : Fin 1)) j x = S x := by
          intro x; unfold peelPrefix; simp
        have hpart : ∀ x, peelPart S (fun _ => (⟨0, by omega⟩ : Fin 1)) j x = S x := by
          intro x; unfold peelPart
          have hj : j = ⟨0, by omega⟩ := Fin.ext (by omega)
          simp [hj]
        have huS : S u = true := by rw [← hpref u]; exact hu
        have hdeg_eq : degIn G (peelPrefix S (fun _ => (⟨0, by omega⟩ : Fin 1)) j) u = degIn G S u := by
          unfold degIn; apply filter_length_eq; intro x _; rw [hpref x]
        have hcard_eq : subsetCard (peelPart S (fun _ => (⟨0, by omega⟩ : Fin 1)) j) = subsetCard S := by
          unfold subsetCard; apply filter_length_eq; intro x _; exact hpart x
        rw [hdeg_eq, hcard_eq]
        -- Since α(G[S]) ≤ 1, every v ∈ S with v ≠ u is adjacent to u
        have hcompl0 : degIn G.compl S u = 0 := by
          unfold degIn
          rw [List.length_eq_zero_iff]
          rw [List.filter_eq_nil_iff]
          intro v _
          simp only [Bool.and_eq_true, SGraph.compl, decide_eq_true_eq, Bool.not_eq_true']
          intro ⟨hSv, huv, hnotadj⟩
          let I : Fin n → Bool := fun x => decide (x = u) || decide (x = v)
          have hIsub : ∀ x, I x = true → S x = true := by
            intro x hx
            simp only [I, Bool.or_eq_true, decide_eq_true_eq] at hx
            rcases hx with rfl | rfl
            · exact huS
            · exact hSv
          have hIind : IsIndep G I := by
            intro x y hx hy
            simp only [I, Bool.or_eq_true, decide_eq_true_eq] at hx hy
            rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
            · exact G.loopless _
            · exact hnotadj
            · rw [G.symm]; exact hnotadj
            · exact G.loopless _
          have hIcard : subsetCard I = 2 := by
            unfold subsetCard
            have hpart2 := filter_length_partition (verts n) I (fun x => decide (x = u))
            have h1 : ((verts n).filter (fun x => I x && decide (x = u))).length = 1 := by
              have : ((verts n).filter (fun x => I x && decide (x = u))).length =
                     ((verts n).filter (fun x => decide (x = u))).length := by
                apply filter_length_eq; intro x _
                by_cases hx : x = u
                · subst hx; simp [I]
                · simp [I, hx]
              rw [this]; exact length_filter_eq_one_of_nodup (verts n) (nodup_verts n) u (mem_verts u)
            have h2 : ((verts n).filter (fun x => I x && !decide (x = u))).length = 1 := by
              have : ((verts n).filter (fun x => I x && !decide (x = u))).length =
                     ((verts n).filter (fun x => decide (x = v))).length := by
                apply filter_length_eq; intro x _
                by_cases hx : x = v
                · subst hx; simp [I, Ne.symm huv]
                · by_cases hxu : x = u
                  · subst hxu; simp [I, hx]
                  · simp [I, hx, hxu]
              rw [this]; exact length_filter_eq_one_of_nodup (verts n) (nodup_verts n) v (mem_verts v)
            omega
          have hle := hα I hIsub hIind
          omega
        have hsum := degIn_add_compl G S u huS
        omega
    | succ r' =>
      -- Inductive step: r = (r' + 1) + 1 = r1 + 1
      let r1 := r' + 1
      by_cases hS0 : subsetCard S = 0
      · have hSfalse : ∀ v : Fin n, S v = false := by
          intro v
          by_cases hv : S v = true
          · have hpos : subsetCard S ≥ 1 := by
              unfold subsetCard
              have hmem : v ∈ (verts n).filter S := List.mem_filter.mpr ⟨mem_verts v, hv⟩
              cases hf : (verts n).filter S with
              | nil => rw [hf] at hmem; cases hmem
              | cons _ _ => simp
            omega
          · cases h : S v; rfl; exact absurd h hv
        refine ⟨fun _ => ⟨0, by omega⟩, ?_, ?_⟩
        · intro j I hIsub _
          have hIfalse : ∀ v, I v = false := by
            intro v
            by_cases hv : I v = true
            · have := (Bool.and_eq_true _ _ |>.mp (hIsub v hv)).1
              rw [hSfalse v] at this; cases this
            · cases h : I v; rfl; exact absurd h hv
          have : subsetCard I = 0 := by
            unfold subsetCard
            have : (verts n).filter I = [] := List.filter_eq_nil_iff.mpr (fun v _ => by simp [hIfalse v])
            simp [this]
          omega
        · intro j u hu
          have := (Bool.and_eq_true _ _ |>.mp hu).1
          rw [hSfalse u] at this; cases this
      · have hSpos : subsetCard S > 0 := by omega
        obtain ⟨v, hvS, hvmin⟩ := exists_min_degIn G S hSpos
        let A : Fin n → Bool := fun w => S w && !decide (w = v) && !G.adj v w
        let B : Fin n → Bool := fun w => S w && (decide (w = v) || G.adj v w)
        have hBcard : subsetCard B = degIn G S v + 1 := by
          have hpart := filter_length_partition (verts n) B (fun w => decide (w = v))
          have h1 : ((verts n).filter (fun w => B w && decide (w = v))).length = 1 := by
            have heq : ((verts n).filter (fun w => B w && decide (w = v))).length =
                       ((verts n).filter (fun w => decide (w = v))).length := by
              apply filter_length_eq; intro w _
              by_cases hw : w = v
              · subst hw; simp [B, hvS]
              · simp [B, hw]
            rw [heq]; exact length_filter_eq_one_of_nodup (verts n) (nodup_verts n) v (mem_verts v)
          have h2 : ((verts n).filter (fun w => B w && !decide (w = v))).length = degIn G S v := by
            unfold degIn
            apply filter_length_eq; intro w _
            by_cases hw : w = v
            · subst hw; simp [B, G.loopless]
            · simp [B, hw]
          unfold subsetCard; omega
        have hαA : ∀ I : Fin n → Bool, (∀ w, I w = true → A w = true) → IsIndep G I → subsetCard I ≤ r1 := by
          intro I hIsub hIind
          let I' : Fin n → Bool := fun w => I w || decide (w = v)
          have hI'sub : ∀ w, I' w = true → S w = true := by
            intro w hw
            simp only [I', Bool.or_eq_true, decide_eq_true_eq] at hw
            rcases hw with hIw | rfl
            · exact (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp (hIsub w hIw)).1).1
            · exact hvS
          have hI'ind : IsIndep G I' := by
            intro x y hx hy
            simp only [I', Bool.or_eq_true, decide_eq_true_eq] at hx hy
            rcases hx with hIx | rfl <;> rcases hy with hIy | rfl
            · exact hIind x y hIx hIy
            · rw [G.symm]
              have := (Bool.and_eq_true _ _ |>.mp (hIsub x hIx)).2
              simp at this; exact this
            · have := (Bool.and_eq_true _ _ |>.mp (hIsub y hIy)).2
              simp at this; exact this
            · exact G.loopless _
          have hvnotI : I v = false := by
            by_cases h : I v = true
            · have := (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp (hIsub v h)).1).2
              simp at this
            · cases hi : I v; rfl; exact absurd hi h
          have hI'card : subsetCard I' = subsetCard I + 1 := by
            unfold subsetCard
            have hpart := filter_length_partition (verts n) I' (fun w => decide (w = v))
            have h1 : ((verts n).filter (fun w => I' w && decide (w = v))).length = 1 := by
              have heq : ((verts n).filter (fun w => I' w && decide (w = v))).length =
                         ((verts n).filter (fun w => decide (w = v))).length := by
                apply filter_length_eq; intro w _
                by_cases hw : w = v
                · subst hw; simp [I']
                · simp [I', hw]
              rw [heq]; exact length_filter_eq_one_of_nodup (verts n) (nodup_verts n) v (mem_verts v)
            have h2 : ((verts n).filter (fun w => I' w && !decide (w = v))).length =
                      ((verts n).filter I).length := by
              apply filter_length_eq; intro w _
              by_cases hw : w = v
              · subst hw; simp [I', hvnotI]
              · simp [I', hw]
            omega
          have hle := hα I' hI'sub hI'ind
          omega
        obtain ⟨partA, hα_prefA, hmin_degA⟩ := ih (by omega) A hαA
        let part : Fin n → Fin (r1 + 1) :=
          fun w => if A w then ⟨(partA w).val, by omega⟩ else ⟨r1, by omega⟩
        have hpref_lt : ∀ j : Fin (r1 + 1), (hj : j.val < r1) → ∀ w : Fin n,
            peelPrefix S part j w = peelPrefix A partA ⟨j.val, hj⟩ w := by
          intro j hj w
          unfold peelPrefix
          dsimp [part]
          by_cases hAw : A w = true
          · have hSw : S w = true := (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp hAw).1).1
            simp [hAw, hSw]
          · have hAwf : A w = false := by cases h : A w; rfl; exact absurd h hAw
            have hnotle : ¬ (r1 ≤ j.val) := by omega
            simp [hAwf, hnotle]
        have hpart_lt : ∀ j : Fin (r1 + 1), (hj : j.val < r1) → ∀ w : Fin n,
            peelPart S part j w = peelPart A partA ⟨j.val, hj⟩ w := by
          intro j hj w
          unfold peelPart
          dsimp [part]
          by_cases hAw : A w = true
          · have hSw : S w = true := (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp hAw).1).1
            simp only [hAw, hSw, ↓reduceIte, Bool.true_and]
            by_cases hp : partA w = ⟨j.val, hj⟩
            · simp [hp]
            · have hne : (⟨(partA w).val, by omega⟩ : Fin (r1 + 1)) ≠ j := by
                intro h
                exact hp (Fin.ext (congrArg (fun a : Fin (r1 + 1) => a.val) h))
              simp [hp, hne]
          · have hAwf : A w = false := by cases h : A w; rfl; exact absurd h hAw
            have hne : (⟨r1, by omega⟩ : Fin (r1 + 1)) ≠ j := by
              intro h; have := congrArg (fun a : Fin (r1 + 1) => a.val) h; dsimp at this; omega
            simp [hAwf, hne]
        have hpref_last : ∀ j : Fin (r1 + 1), j.val = r1 → ∀ w : Fin n,
            peelPrefix S part j w = S w := by
          intro j hj w
          unfold peelPrefix
          have hle : (part w).val ≤ j.val := by omega
          simp [hle]
        have hpart_last : ∀ j : Fin (r1 + 1), j.val = r1 → ∀ w : Fin n,
            peelPart S part j w = B w := by
          intro j hj w
          unfold peelPart
          dsimp [part]
          by_cases hAw : A w = true
          · have hne : (⟨(partA w).val, by omega⟩ : Fin (r1 + 1)) ≠ j := by
              intro h; have := congrArg (fun a : Fin (r1 + 1) => a.val) h; dsimp at this; omega
            have hBw : B w = false := by
              have h1 := Bool.and_eq_true _ _ |>.mp hAw
              have h2 := Bool.and_eq_true _ _ |>.mp h1.1
              simp only [B, h2.1, Bool.true_and]
              have hn1 : ¬ (w = v) := by simpa using h2.2
              have hn2 : G.adj v w = false := by simpa using h1.2
              simp [hn1, hn2]
            simp [hAw, hne, hBw]
          · have hAwf : A w = false := by cases h : A w; rfl; exact absurd h hAw
            have heq : (⟨r1, by omega⟩ : Fin (r1 + 1)) = j := Fin.ext hj.symm
            simp only [hAwf, Bool.false_eq_true, ↓reduceIte, heq, decide_true, Bool.and_true]
            by_cases hSw : S w = true
            · simp only [B, hSw, Bool.true_and]
              by_cases hvw : w = v
              · simp [hvw]
              · by_cases hadj : G.adj v w = true
                · simp [hadj]
                · exfalso
                  have hadjf : G.adj v w = false := by cases h : G.adj v w; rfl; exact absurd h hadj
                  have : A w = true := by simp [A, hSw, hvw, hadjf]
                  rw [this] at hAwf; cases hAwf
            · have hSwf : S w = false := by cases h : S w; rfl; exact absurd h hSw
              simp [B, hSwf]
        refine ⟨part, ?_, ?_⟩
        · intro j I hIsub hIind
          by_cases hj : j.val < r1
          · apply hα_prefA ⟨j.val, hj⟩ I _ hIind
            intro w hw
            rw [← hpref_lt j hj w]
            exact hIsub w hw
          · have hjr : j.val = r1 := by omega
            rw [hjr]
            apply hα I _ hIind
            intro w hw
            rw [← hpref_last j hjr w]
            exact hIsub w hw
        · intro j u hu
          by_cases hj : j.val < r1
          · have hu' : peelPrefix A partA ⟨j.val, hj⟩ u = true := by
              rw [← hpref_lt j hj u]; exact hu
            have hdeg_eq : degIn G (peelPrefix S part j) u =
                           degIn G (peelPrefix A partA ⟨j.val, hj⟩) u := by
              unfold degIn; apply filter_length_eq; intro x _; rw [hpref_lt j hj x]
            have hcard_eq : subsetCard (peelPart S part j) =
                            subsetCard (peelPart A partA ⟨j.val, hj⟩) := by
              unfold subsetCard; apply filter_length_eq; intro x _; exact hpart_lt j hj x
            rw [hdeg_eq, hcard_eq]
            exact hmin_degA ⟨j.val, hj⟩ u hu'
          · have hjr : j.val = r1 := by omega
            have huS : S u = true := by rw [← hpref_last j hjr u]; exact hu
            have hdeg_eq : degIn G (peelPrefix S part j) u = degIn G S u := by
              unfold degIn; apply filter_length_eq; intro x _; rw [hpref_last j hjr x]
            have hcard_eq : subsetCard (peelPart S part j) = subsetCard B := by
              unfold subsetCard; apply filter_length_eq; intro x _; exact hpart_last j hjr x
            rw [hdeg_eq, hcard_eq, hBcard]
            have h3 := hvmin u huS
            omega

/-- From the prefix minimum-degree property of any peel partition, we get the exact cross-edge
    identity at step `j`: `crossEdges G A_j B_j = twoEdgesIn G.compl B_j + D_j`. -/
theorem peel_crossEdges_eq {n r : Nat} (G : SGraph n) (S : Fin n → Bool) (part : Fin n → Fin r) (j : Fin r)
    (hmin : ∀ u : Fin n, peelPrefix S part j u = true →
            degIn G (peelPrefix S part j) u ≥ subsetCard (peelPart S part j) - 1) :
    crossEdges G (peelPrev S part j) (peelPart S part j) =
      twoEdgesIn G.compl (peelPart S part j) + peelDeficit G S part j := by
  let A := peelPrev S part j
  let B := peelPart S part j
  let Sj := peelPrefix S part j
  have hdisj : ∀ v, !(A v && B v) = true := by
    intro v; dsimp [A, B, peelPrev, peelPart]
    by_cases h1 : (part v).val < j.val
    · have h2 : part v ≠ j := by intro h; rw [h] at h1; omega
      simp [h1, h2]
    · simp [h1]
  have hunion : ∀ v, Sj v = (A v || B v) := by
    intro v; dsimp [Sj, A, B, peelPrefix, peelPrev, peelPart]
    cases hSv : S v
    · simp
    · simp only [Bool.true_and]
      by_cases hlt : (part v).val < j.val
      · have hle : (part v).val ≤ j.val := by omega
        simp [hlt, hle]
      · by_cases heq : part v = j
        · simp [heq]
        · have hnotle : ¬ ((part v).val ≤ j.val) := by
            intro hle; apply heq; exact Fin.ext (by omega)
          simp [hlt, heq, hnotle]
  have hsumB : crossEdges G B Sj = twoEdgesIn G B + crossEdges G A B := by
    rw [crossEdges_congr G (fun _ => rfl) hunion]
    rw [sum_degIn_union_disjoint G B A B hdisj]
    rw [crossEdges_self, crossEdges_symm G B A, Nat.add_comm]
  have hdef : crossEdges G B Sj = subsetCard B * (subsetCard B - 1) + peelDeficit G S part j := by
    unfold crossEdges peelDeficit
    have h1 : subsetCard B * (subsetCard B - 1) =
              ((verts n).map (fun u => if B u then subsetCard B - 1 else 0)).sum := by
      have h2 : ((verts n).map (fun u => if B u then subsetCard B - 1 else 0)).sum =
                (subsetCard B - 1) * ((verts n).map (fun u => if B u then 1 else 0)).sum := by
        rw [← sum_map_mul_left]
        apply sum_map_eq; intro u _; cases B u <;> simp
      rw [h2, ← length_filter_eq_sum, Nat.mul_comm]; rfl
    rw [h1, ← sum_map_add]
    apply sum_map_eq; intro u _
    by_cases hBu : B u = true
    · have hSju : Sj u = true := by rw [hunion u]; simp [hBu]
      have hge := hmin u hSju
      dsimp [Sj, B] at hBu hge ⊢
      simp only [hBu, ↓reduceIte]
      omega
    · have hBuf : B u = false := by cases h : B u; rfl; exact absurd h hBu
      dsimp [B] at hBuf ⊢
      simp [hBuf]
  have hcompl := twoEdgesIn_add_compl G B
  dsimp [A, B, Sj] at hsumB hdef hcompl
  omega

/-- Exact step-`j` edge recurrence for a Füredi peel:
    `2 e(G[S_j]) = 2 e(G[A_j]) + s_j(s_j - 1) + 2 m_j + 2 D_j`. -/
theorem peel_step_twoEdgesIn {n r : Nat} (G : SGraph n) (S : Fin n → Bool) (part : Fin n → Fin r) (j : Fin r)
    (hmin : ∀ u : Fin n, peelPrefix S part j u = true →
            degIn G (peelPrefix S part j) u ≥ subsetCard (peelPart S part j) - 1) :
    twoEdgesIn G (peelPrefix S part j) =
      twoEdgesIn G (peelPrev S part j) +
      subsetCard (peelPart S part j) * (subsetCard (peelPart S part j) - 1) +
      twoEdgesIn G.compl (peelPart S part j) +
      2 * peelDeficit G S part j := by
  let A := peelPrev S part j
  let B := peelPart S part j
  let Sj := peelPrefix S part j
  have hdisj : ∀ v, !(A v && B v) = true := by
    intro v; dsimp [A, B, peelPrev, peelPart]
    by_cases h1 : (part v).val < j.val
    · have h2 : part v ≠ j := by intro h; rw [h] at h1; omega
      simp [h1, h2]
    · simp [h1]
  have hunion : ∀ v, Sj v = (A v || B v) := by
    intro v; dsimp [Sj, A, B, peelPrefix, peelPrev, peelPart]
    cases hSv : S v
    · simp
    · simp only [Bool.true_and]
      by_cases hlt : (part v).val < j.val
      · have hle : (part v).val ≤ j.val := by omega
        simp [hlt, hle]
      · by_cases heq : part v = j
        · simp [heq]
        · have hnotle : ¬ ((part v).val ≤ j.val) := by
            intro hle; apply heq; exact Fin.ext (by omega)
          simp [hlt, heq, hnotle]
  have hcongr : twoEdgesIn G Sj = twoEdgesIn G (fun v => A v || B v) := by
    rw [twoEdgesIn_eq_double_sum, twoEdgesIn_eq_double_sum]
    apply sum_map_eq; intro u _; apply sum_map_eq; intro v _; rw [hunion u, hunion v]
  rw [hcongr, twoEdgesIn_union_disjoint G A B hdisj]
  have hcross := peel_crossEdges_eq G S part j hmin
  have hcompl := twoEdgesIn_add_compl G B
  dsimp [A, B] at hcross hcompl ⊢
  omega

/-- Generic list-filter splitting lemma for `j.val < k' + 1` vs `j.val < k'` on `verts r`. -/
theorem filter_lt_succ_sum {r : Nat} (f : Fin r → Nat) (k' : Nat) (hk : k' < r) :
    (((verts r).filter (fun j => decide (j.val < k' + 1))).map f).sum =
    (((verts r).filter (fun j => decide (j.val < k'))).map f).sum + f ⟨k', hk⟩ := by
  let jk : Fin r := ⟨k', hk⟩
  have hgen : ∀ l : List (Fin r), l.Nodup → jk ∈ l →
      ((l.filter (fun j => decide (j.val < k' + 1))).map f).sum =
      ((l.filter (fun j => decide (j.val < k'))).map f).sum + f jk := by
    intro l hnd hmem
    induction l with
    | nil => cases hmem
    | cons x xs ihl =>
      rw [List.nodup_cons] at hnd
      rcases List.mem_cons.mp hmem with hxeq | hmem'
      · subst hxeq
        have hlt1 : decide (jk.val < k' + 1) = true := by dsimp [jk]; simp
        have hlt0 : decide (jk.val < k') = false := by dsimp [jk]; simp
        have hfilt : xs.filter (fun j => decide (j.val < k' + 1)) =
                     xs.filter (fun j => decide (j.val < k')) := by
          apply List.filter_congr
          intro y hy
          have hne : y ≠ jk := fun h => hnd.1 (h ▸ hy)
          have hvalne : y.val ≠ k' := fun hv => hne (Fin.ext hv)
          by_cases h : y.val < k'
          · have h' : y.val < k' + 1 := by omega
            simp [h, h']
          · have h' : ¬ (y.val < k' + 1) := by omega
            simp [h, h']
        rw [List.filter_cons, List.filter_cons, hlt1, hlt0, hfilt]
        simp only [↓reduceIte, Bool.false_eq_true, List.map_cons, List.sum_cons]
        omega
      · have hne : x ≠ jk := fun h => hnd.1 (h ▸ hmem')
        have hvalne : x.val ≠ k' := fun hv => hne (Fin.ext hv)
        have heq : decide (x.val < k' + 1) = decide (x.val < k') := by
          by_cases h : x.val < k'
          · have h' : x.val < k' + 1 := by omega
            simp [h, h']
          · have h' : ¬ (x.val < k' + 1) := by omega
            simp [h, h']
        simp only [List.filter_cons, heq]
        cases decide (x.val < k')
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact ihl hnd.2 hmem'
        · simp only [↓reduceIte, List.map_cons, List.sum_cons]
          rw [ihl hnd.2 hmem']; omega
  exact hgen (verts r) (nodup_verts r) (mem_verts jk)

/-- Prefix telescoping sum: for every `k ≤ r`,
    `twoEdgesIn G {v ∈ S : part v < k} = ∑_{j < k} (s_j(s_j - 1) + 2 m_j + 2 D_j)`. -/
theorem peel_prefix_sum {n r : Nat} (G : SGraph n) (S : Fin n → Bool) (part : Fin n → Fin r)
    (hmin : ∀ j : Fin r, ∀ u : Fin n, peelPrefix S part j u = true →
            degIn G (peelPrefix S part j) u ≥ subsetCard (peelPart S part j) - 1) :
    ∀ k : Nat, (hk : k ≤ r) →
      twoEdgesIn G (fun v => S v && decide ((part v).val < k)) =
        (((verts r).filter (fun j => decide (j.val < k))).map
          (fun j => subsetCard (peelPart S part j) * (subsetCard (peelPart S part j) - 1) +
                    twoEdgesIn G.compl (peelPart S part j) +
                    2 * peelDeficit G S part j)).sum := by
  intro k
  induction k with
  | zero =>
    intro _
    have h0 : twoEdgesIn G (fun v => S v && decide ((part v).val < 0)) = 0 := by
      rw [twoEdgesIn_eq_double_sum]
      exact sum_map_eq_zero _ _ (fun _ _ => sum_map_eq_zero _ _ (fun _ _ => by simp))
    have hf : (verts r).filter (fun j => decide (j.val < 0)) = [] :=
      List.filter_eq_nil_iff.mpr (fun _ _ => by simp)
    rw [h0, hf]; simp
  | succ k' ih =>
    intro hk
    let jk : Fin r := ⟨k', by omega⟩
    have hstep := peel_step_twoEdgesIn G S part jk (hmin jk)
    have hpref_eq : twoEdgesIn G (fun v => S v && decide ((part v).val < k' + 1)) =
                    twoEdgesIn G (peelPrefix S part jk) := by
      rw [twoEdgesIn_eq_double_sum, twoEdgesIn_eq_double_sum]
      apply sum_map_eq; intro u _; apply sum_map_eq; intro v _
      unfold peelPrefix
      have h1 : decide ((part u).val < k' + 1) = decide ((part u).val ≤ jk.val) := by
        dsimp [jk]; by_cases h : (part u).val ≤ k' <;> simp [h, Nat.lt_succ_iff]
      have h2 : decide ((part v).val < k' + 1) = decide ((part v).val ≤ jk.val) := by
        dsimp [jk]; by_cases h : (part v).val ≤ k' <;> simp [h, Nat.lt_succ_iff]
      rw [h1, h2]
    have hprev_eq : twoEdgesIn G (peelPrev S part jk) =
                    twoEdgesIn G (fun v => S v && decide ((part v).val < k')) := rfl
    rw [hpref_eq, hstep, hprev_eq, ih (by omega)]
    have hsp := filter_lt_succ_sum (fun j =>
      subsetCard (peelPart S part j) * (subsetCard (peelPart S part j) - 1) +
      twoEdgesIn G.compl (peelPart S part j) +
      2 * peelDeficit G S part j) k' (by omega)
    dsimp only [jk]
    omega

/-- **Theorem P1 (`furedi_peel_stability`):**
    Strengthened Füredi stability with exact peel structure, exact step cross-edges, and exact
    imbalance + missing-edge + degree-deficit decomposition. -/
theorem furedi_peel_stability {n : Nat} (G : SGraph n) (S : Fin n → Bool) (r : Nat) (hr : r ≥ 1)
    (hα : ∀ I : Fin n → Bool, (∀ v, I v = true → S v = true) → IsIndep G I → subsetCard I ≤ r) :
    ∃ part : Fin n → Fin r,
      (∀ j : Fin r, ∀ I : Fin n → Bool,
        (∀ v, I v = true → peelPrefix S part j v = true) → IsIndep G I → subsetCard I ≤ j.val + 1) ∧
      (∀ j : Fin r, ∀ u : Fin n,
        peelPrefix S part j u = true →
        degIn G (peelPrefix S part j) u ≥ subsetCard (peelPart S part j) - 1) ∧
      (∀ j : Fin r,
        crossEdges G (peelPrev S part j) (peelPart S part j) =
          twoEdgesIn G.compl (peelPart S part j) + peelDeficit G S part j) ∧
      (∀ j : Fin r,
        twoEdgesIn G (peelPrefix S part j) =
          twoEdgesIn G (peelPrev S part j) +
          subsetCard (peelPart S part j) * (subsetCard (peelPart S part j) - 1) +
          twoEdgesIn G.compl (peelPart S part j) +
          2 * peelDeficit G S part j) ∧
      twoEdgesIn G S =
        ((verts r).map (fun j =>
          subsetCard (peelPart S part j) * (subsetCard (peelPart S part j) - 1) +
          twoEdgesIn G.compl (peelPart S part j) +
          2 * peelDeficit G S part j)).sum := by
  obtain ⟨part, hαp, hmin⟩ := furedi_peel_exists G r hr S hα
  refine ⟨part, hαp, hmin,
    fun j => peel_crossEdges_eq G S part j (hmin j),
    fun j => peel_step_twoEdgesIn G S part j (hmin j), ?_⟩
  have htot := peel_prefix_sum G S part hmin r (Nat.le_refl r)
  have h1 : twoEdgesIn G (fun v => S v && decide ((part v).val < r)) = twoEdgesIn G S := by
    rw [twoEdgesIn_eq_double_sum, twoEdgesIn_eq_double_sum]
    apply sum_map_eq; intro u _; apply sum_map_eq; intro v _
    simp [(part u).isLt, (part v).isLt]
  have h2 : (verts r).filter (fun j => decide (j.val < r)) = verts r := by
    have : ∀ l : List (Fin r), l.filter (fun j => decide (j.val < r)) = l := by
      intro l; induction l with
      | nil => rfl
      | cons x xs _ => simp
    exact this (verts r)
  rw [h1, h2] at htot
  exact htot

/-! ## Section 3: Sparsest-Color Füredi Peel & r = 4 Unique Partition -/

/-- **Theorem P2 (`furedi_peel_sparsest`):**
    For every `r ≥ 3`, in any balanced `r`-coloring of `K_{r²+1}`, there exists a sparsest color
    class `c` (`edges G ≤ r * (r² + 1) / 2`) and a Füredi peel `part : Fin (r²+1) → Fin r` with:
    - exact imbalance + missing-edge + degree-deficit identity `∑ (s_j(s_j-1) + 2 m_j + 2 D_j) = 2 e(G) ≤ r(r²+1)`,
    - per-part multi-scale lower bound `2 m_j ≥ 2(r - 1)(s_j - r)`,
    - prefix independence `α(G[S_j]) ≤ j + 1` and prefix min-degree `≥ s_j - 1`. -/
theorem furedi_peel_sparsest {r : Nat} (hr : r ≥ 3)
    (C : EdgeColoring (r * r + 1) r) (hbal : IsBalanced C) :
    ∃ (c : Fin r) (part : Fin (r * r + 1) → Fin r),
      let G := colorClass C c
      let allV : Fin (r * r + 1) → Bool := fun _ => true
      edges G ≤ r * (r * r + 1) / 2 ∧
      twoEdgesIn G allV ≤ r * (r * r + 1) ∧
      (∀ j : Fin r, ∀ I : Fin (r * r + 1) → Bool,
        (∀ v, I v = true → peelPrefix allV part j v = true) → IsIndep G I → subsetCard I ≤ j.val + 1) ∧
      (∀ j : Fin r, ∀ u : Fin (r * r + 1),
        peelPrefix allV part j u = true →
        degIn G (peelPrefix allV part j) u ≥ subsetCard (peelPart allV part j) - 1) ∧
      (∀ j : Fin r,
        crossEdges G (peelPrev allV part j) (peelPart allV part j) =
          twoEdgesIn G.compl (peelPart allV part j) + peelDeficit G allV part j) ∧
      (∀ j : Fin r,
        twoEdgesIn G (peelPrefix allV part j) =
          twoEdgesIn G (peelPrev allV part j) +
          subsetCard (peelPart allV part j) * (subsetCard (peelPart allV part j) - 1) +
          twoEdgesIn G.compl (peelPart allV part j) +
          2 * peelDeficit G allV part j) ∧
      twoEdgesIn G allV =
        ((verts r).map (fun j =>
          subsetCard (peelPart allV part j) * (subsetCard (peelPart allV part j) - 1) +
          twoEdgesIn G.compl (peelPart allV part j) +
          2 * peelDeficit G allV part j)).sum ∧
      (∀ j : Fin r, twoEdgesIn G.compl (peelPart allV part j) ≥
                    2 * (r - 1) * (subsetCard (peelPart allV part j) - r)) := by
  obtain ⟨c, hsparse⟩ := exists_sparsest_colorClass (by omega) C
  let G := colorClass C c
  let allV : Fin (r * r + 1) → Bool := fun _ => true
  have hαG : ∀ I : Fin (r * r + 1) → Bool,
      (∀ v, I v = true → allV v = true) → IsIndep G I → subsetCard I ≤ r :=
    fun I _ hI => isBalanced_indep_le C hbal c I hI
  obtain ⟨part, hαp, hmin, hcross, hstep, htot⟩ := furedi_peel_stability G allV r (by omega) hαG
  have h2e : twoEdgesIn G allV ≤ r * (r * r + 1) := by
    have h1 : twoEdgesIn G allV = 2 * edges G := (two_mul_edges G).symm
    have h2 : 2 * (r * (r * r + 1) / 2) ≤ r * (r * r + 1) := Nat.mul_div_le _ 2
    dsimp [G] at h1 ⊢
    rw [h1]
    omega
  have hper : ∀ j : Fin r, twoEdgesIn G.compl (peelPart allV part j) ≥
      2 * (r - 1) * (subsetCard (peelPart allV part j) - r) := by
    intro j
    have hms := multiscale_turan_complement C hbal c (peelPart allV part j) 1
    have hte := two_mul_edgesIn G.compl (peelPart allV part j)
    dsimp [G] at hte ⊢
    by_cases hs : subsetCard (peelPart allV part j) ≥ r
    · have hsub : 2 * (r - 1) * (subsetCard (peelPart allV part j) - r) +
                  2 * (r - 1) * r = 2 * (r - 1) * subsetCard (peelPart allV part j) := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hs]
      have h12 : (r - 1) * (1 * (1 + 1) * r) = 2 * (r - 1) * r := by
        have h2 : 1 * (1 + 1) = 2 := rfl
        rw [h2, ← Nat.mul_assoc, Nat.mul_comm (r - 1) 2]
      have h21 : 2 * (r - 1) * 1 * subsetCard (peelPart allV part j) =
                 2 * (r - 1) * subsetCard (peelPart allV part j) := by simp
      rw [hte, h12, h21] at hms
      omega
    · have : subsetCard (peelPart allV part j) - r = 0 := by omega
      rw [this]; simp
  exact ⟨c, part, hsparse, h2e, hαp, hmin, hcross, hstep, htot, hper⟩

/-- **Corollary (`r4_unique_partition`):**
    At `r = 4` (`K₁₇`), the strengthened Füredi peel immediately forces the **unique** sorted
    partition `[5, 4, 4, 4]` for the sparsest color class! -/
theorem r4_unique_partition (C : EdgeColoring (4 * 4 + 1) 4) (hbal : IsBalanced C) :
    ∃ (c : Fin 4) (part : Fin (4 * 4 + 1) → Fin 4),
      let allV : Fin (4 * 4 + 1) → Bool := fun _ => true
      let sizes := (verts 4).map (fun j => subsetCard (peelPart allV part j))
      edges (colorClass C c) ≤ 34 ∧ sortDesc sizes = [5, 4, 4, 4] := by
  obtain ⟨c, part, hsparse, h2e, _, _, _, _, htot, hper⟩ := furedi_peel_sparsest (r := 4) (by omega) C hbal
  refine ⟨c, part, hsparse, ?_⟩
  let allV : Fin (4 * 4 + 1) → Bool := fun _ => true
  let sizes := (verts 4).map (fun j => subsetCard (peelPart allV part j))
  have hineq : ((verts 4).map (fun j =>
      subsetCard (peelPart allV part j) * (subsetCard (peelPart allV part j) - 1) +
      6 * (subsetCard (peelPart allV part j) - 4))).sum ≤ 68 := by
    have hle : ((verts 4).map (fun j =>
        subsetCard (peelPart allV part j) * (subsetCard (peelPart allV part j) - 1) +
        6 * (subsetCard (peelPart allV part j) - 4))).sum ≤
        ((verts 4).map (fun j =>
        subsetCard (peelPart allV part j) * (subsetCard (peelPart allV part j) - 1) +
        twoEdgesIn (colorClass C c).compl (peelPart allV part j) +
        2 * peelDeficit (colorClass C c) allV part j)).sum := by
      apply sum_map_le; intro j _
      have := hper j
      dsimp [allV] at this ⊢
      omega
    dsimp [allV] at hle
    rw [← htot] at hle
    exact Nat.le_trans hle h2e
  have hlen : (sortDesc sizes).length = 4 := by
    rw [sortDesc_length]; dsimp [sizes]; simp [length_verts]
  have hsum : (sortDesc sizes).sum = 17 := by
    rw [sortDesc_sum]; dsimp [sizes]
    have h := subsetCard_partition_fin allV part
    rw [subsetCard_true] at h
    exact h
  have hineq' : ((sortDesc sizes).map (fun x => x * (x - 1) + 6 * (x - 4))).sum ≤ 68 := by
    rw [sortDesc_map_sum]; dsimp [sizes]; rw [List.map_map]; exact hineq
  have hpw := sortDesc_sorted sizes
  match hsd : sortDesc sizes with
  | [a, b, c', d] =>
    rw [hsd] at hsum hineq' hpw
    simp only [List.sum_cons, List.sum_nil, Nat.add_zero, List.map_cons, List.map_nil] at hsum hineq'
    rw [List.pairwise_cons] at hpw
    have hpw2 := hpw.2; rw [List.pairwise_cons] at hpw2
    have hpw3 := hpw2.2; rw [List.pairwise_cons] at hpw3
    have hord : a ≥ b ∧ b ≥ c' ∧ c' ≥ d :=
      ⟨hpw.1 b (by simp), hpw2.1 c' (by simp), hpw3.1 d (by simp)⟩
    have ha5 : a = 5 := by
      by_cases ha6 : a ≥ 6
      · have hb := pair_linear_envelope b 3
        have hc := pair_linear_envelope c' 3
        have hd := pair_linear_envelope d 3
        have hae := pair_linear_envelope a 5
        omega
      · omega
    subst ha5
    have hb4 : b = 4 := by
      by_cases hb5 : b ≥ 5
      · have hc := pair_linear_envelope c' 3
        have hd := pair_linear_envelope d 3
        have hbe := pair_linear_envelope b 4
        omega
      · omega
    subst hb4
    have hcd : c' = 4 ∧ d = 4 := by omega
    rcases hcd with ⟨rfl, rfl⟩
    rfl
  | [] => simp [hsd] at hlen
  | [_] => simp [hsd] at hlen
  | [_, _] => simp [hsd] at hlen
  | [_, _, _] => simp [hsd] at hlen
  | _ :: _ :: _ :: _ :: _ :: _ => simp [hsd] at hlen

/-! ## Section 4: r = 6 Elimination of All 6 Tight Partitions (Down to 3) -/

/-- Exact list of the 3 partitions surviving the strengthened Füredi imbalance bound at `r = 6`. -/
def threeR6Partitions : List (List Nat) :=
  [ [8, 6, 6, 6, 6, 5],
    [7, 7, 6, 6, 6, 5],
    [7, 6, 6, 6, 6, 6] ]

theorem classify_6tuple_imbalance (a b c d e f : Nat)
    (hord : a ≥ b ∧ b ≥ c ∧ c ≥ d ∧ d ≥ e ∧ e ≥ f)
    (hsum : a + b + c + d + e + f = 37)
    (himb : a * (a - 1) + 10 * (a - 6) +
            (b * (b - 1) + 10 * (b - 6)) +
            (c * (c - 1) + 10 * (c - 6)) +
            (d * (d - 1) + 10 * (d - 6)) +
            (e * (e - 1) + 10 * (e - 6)) +
            (f * (f - 1) + 10 * (f - 6)) ≤ 222) :
    [a, b, c, d, e, f] ∈ threeR6Partitions := by
  have ha6 := pair_linear_envelope a 6
  have hb6 := pair_linear_envelope b 6
  have hc6 := pair_linear_envelope c 6
  have hd6 := pair_linear_envelope d 6
  have he6 := pair_linear_envelope e 6
  have hf6 := pair_linear_envelope f 6
  have h1 := classify_6tuple_overflow3 a b c d e f hord hsum (by omega)
  simp only [validR6Partitions, List.mem_cons, List.not_mem_nil, or_false] at h1
  rcases h1 with h | h | h | h | h | h | h | h | h
  · simp only [List.cons.injEq, and_true] at h
    rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩; omega
  · simp only [List.cons.injEq, and_true] at h
    rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩; omega
  · simp only [List.cons.injEq, and_true] at h
    rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩; omega
  · simp only [List.cons.injEq, and_true] at h
    rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩; omega
  · simp only [List.cons.injEq, and_true] at h
    rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩; simp [threeR6Partitions]
  · simp only [List.cons.injEq, and_true] at h
    rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩; omega
  · simp only [List.cons.injEq, and_true] at h
    rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩; omega
  · simp only [List.cons.injEq, and_true] at h
    rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩; simp [threeR6Partitions]
  · simp only [List.cons.injEq, and_true] at h
    rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩; simp [threeR6Partitions]

/-! ## Section 5: Elimination of `[8, 6, 6, 6, 6, 5]` Across All 30 Peel Orderings -/

theorem mem_insertDesc (x y : Nat) (l : List Nat) :
    y ∈ insertDesc x l ↔ y = x ∨ y ∈ l := by
  induction l with
  | nil => simp [insertDesc]
  | cons a as ih =>
    unfold insertDesc
    split
    · simp [List.mem_cons]
    · simp only [List.mem_cons, ih]
      constructor
      · intro h; rcases h with rfl | rfl | h'
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr h')
      · intro h; rcases h with rfl | h'
        · exact Or.inr (Or.inl rfl)
        · rcases h' with rfl | h''
          · exact Or.inl rfl
          · exact Or.inr (Or.inr h'')

theorem mem_sortDesc (y : Nat) (l : List Nat) :
    y ∈ sortDesc l ↔ y ∈ l := by
  induction l with
  | nil => simp [sortDesc]
  | cons x xs ih =>
    simp only [sortDesc, mem_insertDesc, ih, List.mem_cons]

theorem sum_verts_6 (f : Fin 6 → Nat) :
    ((verts 6).map f).sum =
      f (0 : Fin 6) + f (1 : Fin 6) + f (2 : Fin 6) +
      f (3 : Fin 6) + f (4 : Fin 6) + f (5 : Fin 6) := by
  have h : verts 6 = [(0 : Fin 6), (1 : Fin 6), (2 : Fin 6),
                      (3 : Fin 6), (4 : Fin 6), (5 : Fin 6)] := by decide
  rw [h]; simp; omega

theorem verts_6_lt_2 :
    (verts 6).filter (fun j => decide (j.val < 2)) = [(0 : Fin 6), (1 : Fin 6)] := by decide

theorem verts_6_lt_3 :
    (verts 6).filter (fun j => decide (j.val < 3)) = [(0 : Fin 6), (1 : Fin 6), (2 : Fin 6)] := by decide

theorem verts_6_lt_4 :
    (verts 6).filter (fun j => decide (j.val < 4)) =
      [(0 : Fin 6), (1 : Fin 6), (2 : Fin 6), (3 : Fin 6)] := by decide

theorem subsetCard_peelPrev_sum {n r : Nat} (S : Fin n → Bool) (part : Fin n → Fin r)
    (k : Nat) (hk : k ≤ r) :
    subsetCard (fun v => S v && decide ((part v).val < k)) =
      (((verts r).filter (fun j => decide (j.val < k))).map (fun j => subsetCard (peelPart S part j))).sum := by
  induction k with
  | zero =>
    have h0 : subsetCard (fun v => S v && decide ((part v).val < 0)) = 0 := by
      unfold subsetCard
      have : (verts n).filter (fun v => S v && decide ((part v).val < 0)) = [] :=
        List.filter_eq_nil_iff.mpr (fun _ _ => by simp)
      rw [this]; rfl
    have hf : (verts r).filter (fun j => decide (j.val < 0)) = [] :=
      List.filter_eq_nil_iff.mpr (fun _ _ => by simp)
    rw [h0, hf]; simp
  | succ k' ih =>
    let jk : Fin r := ⟨k', by omega⟩
    have hpart := filter_length_partition (verts n)
      (fun v => S v && decide ((part v).val < k' + 1))
      (fun v => decide (part v = jk))
    have h1 : ((verts n).filter (fun v => (S v && decide ((part v).val < k' + 1)) && decide (part v = jk))).length =
              subsetCard (peelPart S part jk) := by
      unfold subsetCard peelPart
      apply filter_length_eq; intro v _
      by_cases hp : part v = jk
      · simp [hp, jk]
      · simp [hp]
    have h2 : ((verts n).filter (fun v => (S v && decide ((part v).val < k' + 1)) && !decide (part v = jk))).length =
              subsetCard (fun v => S v && decide ((part v).val < k')) := by
      unfold subsetCard
      apply filter_length_eq; intro v _
      by_cases hp : part v = jk
      · simp [hp, jk]
      · have hvalne : (part v).val ≠ k' := fun hv => hp (Fin.ext hv)
        have heq : decide ((part v).val < k' + 1) = decide ((part v).val < k') := by
          by_cases h : (part v).val < k'
          · have h' : (part v).val < k' + 1 := by omega
            simp [h, h']
          · have h' : ¬ ((part v).val < k' + 1) := by omega
            simp [h, h']
        simp [hp, heq]
    have hstep : subsetCard (fun v => S v && decide ((part v).val < k' + 1)) =
                 subsetCard (fun v => S v && decide ((part v).val < k')) + subsetCard (peelPart S part jk) := by
      unfold subsetCard at *; omega
    rw [hstep, ih (by omega)]
    rw [filter_lt_succ_sum (fun j => subsetCard (peelPart S part j)) k' (by omega)]

/-- **Theorem P3 (`r6_no_size_8_part`):**
    In any Füredi peel of a sparsest color class at `r = 6`, the sorted partition CANNOT be
    `[8, 6, 6, 6, 6, 5]`. Every one of the 30 peel orderings is refuted. -/
theorem r6_no_size_8_part (C : EdgeColoring (6 * 6 + 1) 6) (hbal : IsBalanced C)
    (c : Fin 6) (part : Fin (6 * 6 + 1) → Fin 6)
    (h2e : twoEdgesIn (colorClass C c) (fun _ => true) ≤ 222)
    (hαp : ∀ j : Fin 6, ∀ I : Fin (6 * 6 + 1) → Bool,
      (∀ v, I v = true → peelPrefix (fun _ => true) part j v = true) →
      IsIndep (colorClass C c) I → subsetCard I ≤ j.val + 1)
    (hmin : ∀ j : Fin 6, ∀ u : Fin (6 * 6 + 1),
      peelPrefix (fun _ => true) part j u = true →
      degIn (colorClass C c) (peelPrefix (fun _ => true) part j) u ≥
        subsetCard (peelPart (fun _ => true) part j) - 1)
    (hcross : ∀ j : Fin 6,
      crossEdges (colorClass C c) (peelPrev (fun _ => true) part j) (peelPart (fun _ => true) part j) =
        twoEdgesIn (colorClass C c).compl (peelPart (fun _ => true) part j) +
        peelDeficit (colorClass C c) (fun _ => true) part j)
    (htot : twoEdgesIn (colorClass C c) (fun _ => true) =
      ((verts 6).map (fun j =>
        subsetCard (peelPart (fun _ => true) part j) *
          (subsetCard (peelPart (fun _ => true) part j) - 1) +
        twoEdgesIn (colorClass C c).compl (peelPart (fun _ => true) part j) +
        2 * peelDeficit (colorClass C c) (fun _ => true) part j)).sum)
    (hper : ∀ j : Fin 6, twoEdgesIn (colorClass C c).compl (peelPart (fun _ => true) part j) ≥
      10 * (subsetCard (peelPart (fun _ => true) part j) - 6))
    (hsd : sortDesc ((verts 6).map (fun j => subsetCard (peelPart (fun _ => true) part j))) =
           [8, 6, 6, 6, 6, 5]) : False := by
  let G := colorClass C c
  let allV : Fin (6 * 6 + 1) → Bool := fun _ => true
  let s : Fin 6 → Nat := fun j => subsetCard (peelPart allV part j)
  let m2 : Fin 6 → Nat := fun j => twoEdgesIn G.compl (peelPart allV part j)
  let D : Fin 6 → Nat := fun j => peelDeficit G allV part j
  let sizes := (verts 6).map s
  have hsum_ss : ((verts 6).map (fun j => s j * (s j - 1))).sum = 196 := by
    have h1 := sortDesc_map_sum (fun x => x * (x - 1)) sizes
    rw [hsd] at h1
    dsimp [sizes] at h1
    rw [List.map_map] at h1
    have h2 : ((verts 6).map ((fun x => x * (x - 1)) ∘ s)).sum =
              ((verts 6).map (fun j => s j * (s j - 1))).sum := rfl
    rw [h2] at h1
    simpa using h1.symm
  have hbudget : ((verts 6).map (fun j => m2 j + 2 * D j)).sum ≤ 26 := by
    have hsplit : ((verts 6).map (fun j => s j * (s j - 1) + m2 j + 2 * D j)).sum =
                  ((verts 6).map (fun j => s j * (s j - 1))).sum +
                  ((verts 6).map (fun j => m2 j + 2 * D j)).sum := by
      rw [← sum_map_add]
      apply sum_map_eq; intro j _; omega
    have ht' : twoEdgesIn G allV = ((verts 6).map (fun j => s j * (s j - 1) + m2 j + 2 * D j)).sum := htot
    have h2e' : twoEdgesIn G allV ≤ 222 := h2e
    omega
  have hall_mem : ∀ j : Fin 6, s j = 8 ∨ s j = 6 ∨ s j = 5 := by
    intro j
    have hm : s j ∈ sizes := List.mem_map.mpr ⟨j, mem_verts j, rfl⟩
    have hm' : s j ∈ sortDesc sizes := (mem_sortDesc (s j) sizes).mpr hm
    rw [hsd] at hm'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm'
    rcases hm' with h | h | h | h | h | h <;> simp [h]
  have hex8 : ∃ j8 : Fin 6, s j8 = 8 := by
    have hm : 8 ∈ sortDesc sizes := by rw [hsd]; simp
    have hm' : 8 ∈ sizes := (mem_sortDesc 8 sizes).mp hm
    obtain ⟨j8, _, hj8⟩ := List.mem_map.mp hm'
    exact ⟨j8, hj8⟩
  obtain ⟨j8, hj8⟩ := hex8
  have hsum_all : s (0 : Fin 6) + s (1 : Fin 6) + s (2 : Fin 6) +
                  s (3 : Fin 6) + s (4 : Fin 6) + s (5 : Fin 6) = 37 := by
    have h1 := sortDesc_sum sizes
    rw [hsd] at h1
    dsimp [sizes] at h1
    rw [sum_verts_6] at h1
    simpa using h1.symm
  have hbud6 : (m2 (0 : Fin 6) + 2 * D (0 : Fin 6)) +
               (m2 (1 : Fin 6) + 2 * D (1 : Fin 6)) +
               (m2 (2 : Fin 6) + 2 * D (2 : Fin 6)) +
               (m2 (3 : Fin 6) + 2 * D (3 : Fin 6)) +
               (m2 (4 : Fin 6) + 2 * D (4 : Fin 6)) +
               (m2 (5 : Fin 6) + 2 * D (5 : Fin 6)) ≤ 26 := by
    rw [← sum_verts_6 (fun j => m2 j + 2 * D j)]; exact hbudget
  have hss6 : s (0 : Fin 6) * (s (0 : Fin 6) - 1) +
              s (1 : Fin 6) * (s (1 : Fin 6) - 1) +
              s (2 : Fin 6) * (s (2 : Fin 6) - 1) +
              s (3 : Fin 6) * (s (3 : Fin 6) - 1) +
              s (4 : Fin 6) * (s (4 : Fin 6) - 1) +
              s (5 : Fin 6) * (s (5 : Fin 6) - 1) = 196 := by
    rw [← sum_verts_6 (fun k => s k * (s k - 1))]; exact hsum_ss
  have hlin : ∀ k : Fin 6, s k * (s k - 1) + 30 ≥ 10 * s k := fun k => by
    rcases hall_mem k with h | h | h <;> simp [h]
  -- Helper: any j ≠ j8 has s j ∈ {5, 6}, hence s j * (s j - 1) + 12 ≤ 7 * s j
  have hgap : ∀ j : Fin 6, j ≠ j8 → s j * (s j - 1) + 12 ≤ 7 * s j := by
    intro j hne
    rcases hall_mem j with hj8' | h6 | h5
    · exfalso
      have hl0 := hlin (0 : Fin 6); have hl1 := hlin (1 : Fin 6); have hl2 := hlin (2 : Fin 6)
      have hl3 := hlin (3 : Fin 6); have hl4 := hlin (4 : Fin 6); have hl5 := hlin (5 : Fin 6)
      have hj_cases : ∀ x : Fin 6, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 := by
        intro x; rcases x with ⟨v, hv⟩
        have : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 := by omega
        rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
      rcases hj_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases hj_cases j8 with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact hne rfl | (rw [hj8, hj8'] at hss6 hsum_all; omega)
    · rw [h6]; omega
    · rw [h5]; omega
  have hagg : 7 * subsetCard (peelPrev allV part j8) ≤
      twoEdgesIn G (peelPrev allV part j8) + crossEdges G (peelPrev allV part j8) (peelPart allV part j8) := by
    let A := peelPrev allV part j8
    let B := peelPart allV part j8
    let Sj := peelPrefix allV part j8
    have hdisj : ∀ v, !(A v && B v) = true := by
      intro v; dsimp [A, B, peelPrev, peelPart]
      by_cases h1 : (part v).val < j8.val
      · have h2 : part v ≠ j8 := by intro h; rw [h] at h1; omega
        simp [h1, h2]
      · simp [h1]
    have hunion : ∀ v, Sj v = (A v || B v) := by
      intro v; dsimp [Sj, A, B, peelPrefix, peelPrev, peelPart]
      simp only [allV, Bool.true_and]
      by_cases hlt : (part v).val < j8.val
      · have hle : (part v).val ≤ j8.val := by omega
        simp [hlt, hle]
      · by_cases heq : part v = j8
        · simp [heq]
        · have hnotle : ¬ ((part v).val ≤ j8.val) := by
            intro hle; apply heq; exact Fin.ext (by omega)
          simp [hlt, heq, hnotle]
    have hlb : crossEdges G A Sj ≥ subsetCard A * 7 := by
      apply crossEdges_le_sum_degIn
      intro u hu
      have hSju : Sj u = true := by rw [hunion u]; simp [hu]
      have hm := hmin j8 u hSju
      dsimp [s, G, allV, Sj] at hj8 hm ⊢
      omega
    have hsp : crossEdges G A Sj = twoEdgesIn G A + crossEdges G A B := by
      rw [crossEdges_congr G (fun _ => rfl) hunion]
      rw [sum_degIn_union_disjoint G A A B hdisj, crossEdges_self]
    dsimp [A, B, Sj] at hlb hsp
    omega
  have hj8_cases : j8 = (0 : Fin 6) ∨ j8 = (1 : Fin 6) ∨ j8 = (2 : Fin 6) ∨
                   j8 = (3 : Fin 6) ∨ j8 = (4 : Fin 6) ∨ j8 = (5 : Fin 6) := by
    rcases j8 with ⟨v, hv⟩
    have : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  rcases hj8_cases with rfl | rfl | rfl | rfl | rfl | rfl
  · -- Case j8 = 0: B_0 has α ≤ 1 ⇒ m2 0 = 0, contradicting m2 0 ≥ 20
    have hm20 : m2 (0 : Fin 6) ≥ 20 := by
      have hp0 := hper (0 : Fin 6)
      dsimp [m2, s, G, allV] at hj8 hp0 ⊢
      omega
    have h0 : m2 (0 : Fin 6) = 0 := by
      dsimp [m2]
      rw [twoEdgesIn_eq_double_sum]
      apply sum_map_eq_zero; intro u _
      apply sum_map_eq_zero; intro v _
      by_cases hcond : (peelPart allV part (0 : Fin 6) u &&
                        peelPart allV part (0 : Fin 6) v && G.compl.adj u v) = true
      · exfalso
        have h1 := Bool.and_eq_true _ _ |>.mp hcond
        have h2 := Bool.and_eq_true _ _ |>.mp h1.1
        have hcomp := h1.2
        simp only [SGraph.compl, Bool.and_eq_true, Bool.not_eq_true'] at hcomp
        have huv : u ≠ v := of_decide_eq_true hcomp.1
        let I : Fin (6 * 6 + 1) → Bool := fun x => decide (x = u) || decide (x = v)
        have hIsub : ∀ x, I x = true → peelPrefix allV part (0 : Fin 6) x = true := by
          intro x hx
          simp only [I, Bool.or_eq_true, decide_eq_true_eq] at hx
          unfold peelPrefix
          rcases hx with rfl | rfl
          · have hp := (Bool.and_eq_true _ _ |>.mp h2.1).2
            simp only [decide_eq_true_eq] at hp
            simp [allV, hp]
          · have hp := (Bool.and_eq_true _ _ |>.mp h2.2).2
            simp only [decide_eq_true_eq] at hp
            simp [allV, hp]
        have hIind : IsIndep G I := by
          intro x y hx hy
          simp only [I, Bool.or_eq_true, decide_eq_true_eq] at hx hy
          rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
          · exact G.loopless _
          · exact hcomp.2
          · rw [G.symm]; exact hcomp.2
          · exact G.loopless _
        have hIcard : subsetCard I = 2 := by
          unfold subsetCard
          have hp2 := filter_length_partition (verts (6 * 6 + 1)) I (fun x => decide (x = u))
          have ha1 : ((verts (6 * 6 + 1)).filter (fun x => I x && decide (x = u))).length = 1 := by
            have heq : ((verts (6 * 6 + 1)).filter (fun x => I x && decide (x = u))).length =
                       ((verts (6 * 6 + 1)).filter (fun x => decide (x = u))).length := by
              apply filter_length_eq; intro x _
              by_cases hx : x = u
              · subst hx; simp [I]
              · simp [I, hx]
            rw [heq]; exact length_filter_eq_one_of_nodup _ (nodup_verts _) u (mem_verts u)
          have ha2 : ((verts (6 * 6 + 1)).filter (fun x => I x && !decide (x = u))).length = 1 := by
            have heq : ((verts (6 * 6 + 1)).filter (fun x => I x && !decide (x = u))).length =
                       ((verts (6 * 6 + 1)).filter (fun x => decide (x = v))).length := by
              apply filter_length_eq; intro x _
              by_cases hx : x = v
              · subst hx; simp [I, Ne.symm huv]
              · by_cases hxu : x = u
                · subst hxu; simp [I, hx]
                · simp [I, hx, hxu]
            rw [heq]; exact length_filter_eq_one_of_nodup _ (nodup_verts _) v (mem_verts v)
          omega
        have hle := hαp (0 : Fin 6) I hIsub hIind
        change subsetCard I ≤ 1 at hle
        omega
      · have hcf : (peelPart allV part (0 : Fin 6) u &&
                    peelPart allV part (0 : Fin 6) v && G.compl.adj u v) = false := by
          cases h : peelPart allV part (0 : Fin 6) u &&
                    peelPart allV part (0 : Fin 6) v && G.compl.adj u v
          · rfl
          · exact absurd h hcond
        rw [hcf]; rfl
    omega
  · -- Case j8 = 1: |S_1| = s_0 + s_1 ≥ 13 and α(G[S_1]) ≤ 2, contradicting no_2r_plus_1_alpha_le_2
    have hs0 : s (0 : Fin 6) ≥ 5 := by
      rcases hall_mem (0 : Fin 6) with h | h | h <;> omega
    have hS1card : subsetCard (peelPrefix allV part (1 : Fin 6)) =
                   s (0 : Fin 6) + s (1 : Fin 6) := by
      have heq : subsetCard (peelPrefix allV part (1 : Fin 6)) =
                 subsetCard (fun v => allV v && decide ((part v).val < 2)) := by
        unfold subsetCard peelPrefix
        apply filter_length_eq; intro v _
        have : decide ((part v).val ≤ (1 : Fin 6).val) = decide ((part v).val < 2) := by
          by_cases h : (part v).val ≤ 1 <;> simp [h, Nat.lt_succ_iff]
        rw [this]
      rw [heq, subsetCard_peelPrev_sum allV part 2 (by omega), verts_6_lt_2]
      simp [s]
    obtain ⟨U, hUsub, hUcard⟩ := exists_sub_card (peelPrefix allV part (1 : Fin 6)) 13 (by omega)
    exact no_2r_plus_1_alpha_le_2 (r := 6) (by omega) C hbal c U hUcard (fun I hIsub hIind =>
      hαp (1 : Fin 6) I (fun v hv => hUsub v (hIsub v hv)) hIind)
  · -- Case j8 = 2: s_2 = 8
    have hAcard : subsetCard (peelPrev allV part (2 : Fin 6)) = s (0 : Fin 6) + s (1 : Fin 6) := by
      have h := subsetCard_peelPrev_sum allV part 2 (by omega)
      rw [verts_6_lt_2] at h
      change subsetCard (fun v => allV v && decide ((part v).val < 2)) = s (0 : Fin 6) + s (1 : Fin 6)
      rw [h]; simp [s]
    have hAedges : twoEdgesIn G (peelPrev allV part (2 : Fin 6)) =
                   (s (0 : Fin 6) * (s (0 : Fin 6) - 1) + m2 (0 : Fin 6) + 2 * D (0 : Fin 6)) +
                   (s (1 : Fin 6) * (s (1 : Fin 6) - 1) + m2 (1 : Fin 6) + 2 * D (1 : Fin 6)) := by
      have h := peel_prefix_sum G allV part hmin 2 (by omega)
      rw [verts_6_lt_2] at h
      change twoEdgesIn G (fun v => allV v && decide ((part v).val < 2)) = _
      rw [h]; simp [s, m2, D]
    have hcr2 : crossEdges G (peelPrev allV part (2 : Fin 6)) (peelPart allV part (2 : Fin 6)) =
                m2 (2 : Fin 6) + D (2 : Fin 6) := hcross (2 : Fin 6)
    have hge5 : ∀ j : Fin 6, s j ≥ 5 := fun j => by rcases hall_mem j with h | h | h <;> omega
    have hg0 := hgap (0 : Fin 6) (by decide)
    have hg1 := hgap (1 : Fin 6) (by decide)
    have hs0_cases : s (0 : Fin 6) = 5 ∨ s (0 : Fin 6) = 6 := by
      have := hge5 (0 : Fin 6)
      rcases hall_mem (0 : Fin 6) with h8 | h6 | h5
      · rw [h8] at hg0; omega
      · exact Or.inr h6
      · exact Or.inl h5
    have hs1_cases : s (1 : Fin 6) = 5 ∨ s (1 : Fin 6) = 6 := by
      have := hge5 (1 : Fin 6)
      rcases hall_mem (1 : Fin 6) with h8 | h6 | h5
      · rw [h8] at hg1; omega
      · exact Or.inr h6
      · exact Or.inl h5
    rcases hs0_cases with hs0 | hs0 <;> rcases hs1_cases with hs1 | hs1
    · rw [hAcard, hAedges, hcr2, hs0, hs1] at hagg; omega
    · rw [hAcard, hAedges, hcr2, hs0, hs1] at hagg; omega
    · rw [hAcard, hAedges, hcr2, hs0, hs1] at hagg; omega
    · -- Unique subcase (s_0, s_1, s_2) = (6, 6, 8)
      let B1 := peelPart allV part (1 : Fin 6)
      let B2 := peelPart allV part (2 : Fin 6)
      let S1 := peelPrefix allV part (1 : Fin 6)
      let S2 := peelPrefix allV part (2 : Fin 6)
      have hdisj12 : ∀ v, !(S1 v && B2 v) = true := by
        intro v; dsimp [S1, B2, peelPrefix, peelPart]
        by_cases h1 : (part v).val ≤ 1
        · have h2 : part v ≠ (2 : Fin 6) := by
            intro h; have hv : (part v).val = 2 := congrArg Fin.val h; omega
          simp [h1, h2]
        · simp [h1]
      have hunion12 : ∀ v, S2 v = (S1 v || B2 v) := by
        intro v; dsimp [S2, S1, B2, peelPrefix, peelPart, allV]
        simp only [Bool.true_and]
        by_cases h1 : (part v).val ≤ 1
        · have h2 : (part v).val ≤ 2 := by omega
          simp [h1, h2]
        · by_cases h2 : part v = (2 : Fin 6)
          · simp [h2]
          · have hnotle : ¬ ((part v).val ≤ 2) := by
              intro hle; apply h2; exact Fin.ext (by omega)
            simp [h1, h2, hnotle]
      have hB1_S2 : crossEdges G B1 S2 ≥ 42 := by
        have h := crossEdges_le_sum_degIn G B1 S2 7 (fun u hu => by
          have hS2u : S2 u = true := by
            dsimp [B1, S2, peelPart, peelPrefix] at hu ⊢
            have hp := (Bool.and_eq_true _ _ |>.mp hu).2
            simp only [decide_eq_true_eq] at hp
            simp [allV, hp]
          have hm := hmin (2 : Fin 6) u hS2u
          dsimp [s, G, allV, S2] at hj8 hm ⊢
          omega)
        have hB1c : subsetCard B1 = 6 := hs1
        rw [hB1c] at h; exact h
      have hB1_split : crossEdges G B1 S2 = crossEdges G B1 S1 + crossEdges G B1 B2 := by
        rw [crossEdges_congr G (fun _ => rfl) hunion12]
        exact sum_degIn_union_disjoint G B1 S1 B2 hdisj12
      have hB1_S1 : crossEdges G B1 S1 = 30 + D (1 : Fin 6) := by
        let A1 := peelPrev allV part (1 : Fin 6)
        have hdisjA1 : ∀ v, !(A1 v && B1 v) = true := by
          intro v; dsimp [A1, B1, peelPrev, peelPart]
          by_cases h1 : (part v).val < 1
          · have h2 : part v ≠ (1 : Fin 6) := by
              intro h; have hv : (part v).val = 1 := congrArg Fin.val h; omega
            simp [h1, h2]
          · simp [h1]
        have hunionA1 : ∀ v, S1 v = (A1 v || B1 v) := by
          intro v; dsimp [S1, A1, B1, peelPrefix, peelPrev, peelPart, allV]
          simp only [Bool.true_and]
          by_cases h1 : (part v).val < 1
          · have h2 : (part v).val ≤ 1 := by omega
            simp [h1, h2]
          · by_cases h2 : part v = (1 : Fin 6)
            · simp [h2]
            · have hnotle : ¬ ((part v).val ≤ 1) := by
                intro hle; apply h2; exact Fin.ext (by omega)
              simp [h1, h2, hnotle]
        rw [crossEdges_congr G (fun _ => rfl) hunionA1]
        rw [sum_degIn_union_disjoint G B1 A1 B1 hdisjA1, crossEdges_self, crossEdges_symm G B1 A1]
        have hcr1 : crossEdges G A1 B1 = m2 (1 : Fin 6) + D (1 : Fin 6) := hcross (1 : Fin 6)
        have hcm1 := twoEdgesIn_add_compl G B1
        have hB1c : subsetCard B1 = 6 := hs1
        have hm2_1 : twoEdgesIn G.compl B1 = m2 (1 : Fin 6) := rfl
        rw [hB1c, hm2_1] at hcm1
        omega
      let U : Fin (6 * 6 + 1) → Bool := fun v => B1 v || B2 v
      have hdisjB12 : ∀ v, !(B1 v && B2 v) = true := by
        intro v; dsimp [B1, B2, peelPart]
        by_cases h1 : part v = (1 : Fin 6)
        · simp [h1]
        · simp [h1]
      have hUcard : subsetCard U = 14 := by
        have hpartU := filter_length_partition (verts (6 * 6 + 1)) U B1
        have h1 : ((verts (6 * 6 + 1)).filter (fun v => U v && B1 v)).length = subsetCard B1 := by
          unfold subsetCard; apply filter_length_eq; intro v _
          dsimp [U]; cases B1 v <;> simp
        have h2 : ((verts (6 * 6 + 1)).filter (fun v => U v && !B1 v)).length = subsetCard B2 := by
          unfold subsetCard; apply filter_length_eq; intro v _
          dsimp [U]
          by_cases hB1 : B1 v = true
          · have hB2 : B2 v = false := by have := hdisjB12 v; simp [hB1] at this; exact this
            simp [hB1, hB2]
          · have hB1f : B1 v = false := by cases h : B1 v; rfl; exact absurd h hB1
            simp [hB1f]
        have hB1c : subsetCard B1 = 6 := hs1
        have hB2c : subsetCard B2 = 8 := hj8
        change ((verts (6 * 6 + 1)).filter U).length = 14
        omega
      have hms := multiscale_turan_complement C hbal c U 2
      have hte := two_mul_edgesIn G.compl U
      dsimp [G] at hte
      have hU2 : twoEdgesIn G.compl U ≥ 100 := by
        rw [hUcard, hte] at hms
        dsimp [G]; omega
      have hUdec := twoEdgesIn_union_disjoint G.compl B1 B2 hdisjB12
      have hcr_cm := crossEdges_add_compl G B1 B2 hdisjB12
      have hB1c : subsetCard B1 = 6 := hs1
      have hB2c : subsetCard B2 = 8 := hj8
      have hm2_1 : twoEdgesIn G.compl B1 = m2 (1 : Fin 6) := rfl
      have hm2_2 : twoEdgesIn G.compl B2 = m2 (2 : Fin 6) := rfl
      rw [hB1c, hB2c] at hcr_cm
      rw [hm2_1, hm2_2] at hUdec
      change twoEdgesIn G.compl (fun v => B1 v || B2 v) ≥ 100 at hU2
      omega
  · -- Case j8 = 3
    have hAcard : subsetCard (peelPrev allV part (3 : Fin 6)) =
                  s (0 : Fin 6) + s (1 : Fin 6) + s (2 : Fin 6) := by
      have h := subsetCard_peelPrev_sum allV part 3 (by omega)
      rw [verts_6_lt_3] at h
      change subsetCard (fun v => allV v && decide ((part v).val < 3)) = _
      rw [h]; simp [s]; omega
    have hAedges : twoEdgesIn G (peelPrev allV part (3 : Fin 6)) =
                   (s (0 : Fin 6) * (s (0 : Fin 6) - 1) + m2 (0 : Fin 6) + 2 * D (0 : Fin 6)) +
                   (s (1 : Fin 6) * (s (1 : Fin 6) - 1) + m2 (1 : Fin 6) + 2 * D (1 : Fin 6)) +
                   (s (2 : Fin 6) * (s (2 : Fin 6) - 1) + m2 (2 : Fin 6) + 2 * D (2 : Fin 6)) := by
      have h := peel_prefix_sum G allV part hmin 3 (by omega)
      rw [verts_6_lt_3] at h
      change twoEdgesIn G (fun v => allV v && decide ((part v).val < 3)) = _
      rw [h]; simp [s, m2, D]; omega
    have hcr3 : crossEdges G (peelPrev allV part (3 : Fin 6)) (peelPart allV part (3 : Fin 6)) =
                m2 (3 : Fin 6) + D (3 : Fin 6) := hcross (3 : Fin 6)
    have hg0 := hgap (0 : Fin 6) (by decide)
    have hg1 := hgap (1 : Fin 6) (by decide)
    have hg2 := hgap (2 : Fin 6) (by decide)
    rw [hAcard, hAedges, hcr3] at hagg
    omega
  · -- Case j8 = 4
    have hAcard : subsetCard (peelPrev allV part (4 : Fin 6)) =
                  s (0 : Fin 6) + s (1 : Fin 6) + s (2 : Fin 6) + s (3 : Fin 6) := by
      have h := subsetCard_peelPrev_sum allV part 4 (by omega)
      rw [verts_6_lt_4] at h
      change subsetCard (fun v => allV v && decide ((part v).val < 4)) = _
      rw [h]; simp [s]; omega
    have hAedges : twoEdgesIn G (peelPrev allV part (4 : Fin 6)) =
                   (s (0 : Fin 6) * (s (0 : Fin 6) - 1) + m2 (0 : Fin 6) + 2 * D (0 : Fin 6)) +
                   (s (1 : Fin 6) * (s (1 : Fin 6) - 1) + m2 (1 : Fin 6) + 2 * D (1 : Fin 6)) +
                   (s (2 : Fin 6) * (s (2 : Fin 6) - 1) + m2 (2 : Fin 6) + 2 * D (2 : Fin 6)) +
                   (s (3 : Fin 6) * (s (3 : Fin 6) - 1) + m2 (3 : Fin 6) + 2 * D (3 : Fin 6)) := by
      have h := peel_prefix_sum G allV part hmin 4 (by omega)
      rw [verts_6_lt_4] at h
      change twoEdgesIn G (fun v => allV v && decide ((part v).val < 4)) = _
      rw [h]; simp [s, m2, D]; omega
    have hcr4 : crossEdges G (peelPrev allV part (4 : Fin 6)) (peelPart allV part (4 : Fin 6)) =
                m2 (4 : Fin 6) + D (4 : Fin 6) := hcross (4 : Fin 6)
    have hg0 := hgap (0 : Fin 6) (by decide)
    have hg1 := hgap (1 : Fin 6) (by decide)
    have hg2 := hgap (2 : Fin 6) (by decide)
    have hg3 := hgap (3 : Fin 6) (by decide)
    rw [hAcard, hAedges, hcr4] at hagg
    omega
  · -- Case j8 = 5: every vertex u ∈ K₃₇ has deg G u ≥ 7 ⇒ 2 e(G) ≥ 259 > 222
    have hS5 : ∀ v : Fin (6 * 6 + 1), peelPrefix allV part (5 : Fin 6) v = true := by
      intro v; unfold peelPrefix; have := (part v).isLt; simp [allV]; omega
    have hlb : crossEdges G allV allV ≥ 37 * 7 := by
      have h := crossEdges_le_sum_degIn G allV allV 7 (fun u _ => by
        have hm := hmin (5 : Fin 6) u (hS5 u)
        have hdeq : degIn G (peelPrefix allV part (5 : Fin 6)) u = degIn G allV u := by
          unfold degIn; apply filter_length_eq; intro x _; rw [hS5 x]
        dsimp [G, allV, s] at hj8 hm hdeq ⊢
        rw [hdeq] at hm
        omega)
      rw [subsetCard_true] at h
      exact h
    rw [crossEdges_self] at hlb
    have h2e' : twoEdgesIn G allV ≤ 222 := h2e
    omega

/-! ## Section 6: Exact 2-Partition Theorem for r = 6 (K₃₇) -/

/-- **Theorem P4 (`r6_exact_two_partitions`):**
    In ANY balanced 6-coloring of `K₃₇`, there exists a sparsest color class `c : Fin 6`
    (`edges G ≤ 111`) and a Füredi peel `part : Fin 37 → Fin 6` such that:
    1. `|{v : deg G v ≤ 5}| ≤ 18` and `|{v : deg G v ≥ 6}| ≥ 19`,
    2. Exact imbalance + missing-edge + degree-deficit identity:
       `∑_j (s_j(s_j - 1) + 2 m_j + 2 D_j) = twoEdges G ≤ 222`,
    3. Every part satisfies `edgesIn G.compl B_j ≥ 5 * (s_j - 6)`,
    4. The sorted part sizes `sortDesc sizes` are **EITHER**:
       - `[7, 7, 6, 6, 6, 5]` (imbalance `Δ = 1`, `m_in + D_ex ≤ 14`, total slack `≤ 4`), **OR**
       - `[7, 6, 6, 6, 6, 6]` (imbalance `Δ = 0`, `m_in + D_ex ≤ 15`, total slack `≤ 10`). -/
theorem r6_exact_two_partitions (C : EdgeColoring (6 * 6 + 1) 6) (hbal : IsBalanced C) :
    ∃ (c : Fin 6) (part : Fin (6 * 6 + 1) → Fin 6),
      let G := colorClass C c
      let allV : Fin (6 * 6 + 1) → Bool := fun _ => true
      let sizes := (verts 6).map (fun j => subsetCard (peelPart allV part j))
      edges G ≤ 111 ∧
      subsetCard (fun v => decide (deg G v ≤ 5)) ≤ 18 ∧
      subsetCard (fun v => decide (deg G v ≥ 6)) ≥ 19 ∧
      (∀ j : Fin 6, edgesIn G.compl (peelPart allV part j) ≥
                    5 * (subsetCard (peelPart allV part j) - 6)) ∧
      twoEdgesIn G allV =
        ((verts 6).map (fun j =>
          subsetCard (peelPart allV part j) * (subsetCard (peelPart allV part j) - 1) +
          twoEdgesIn G.compl (peelPart allV part j) +
          2 * peelDeficit G allV part j)).sum ∧
      ((sortDesc sizes = [7, 7, 6, 6, 6, 5] ∧
        ((verts 6).map (fun j => twoEdgesIn G.compl (peelPart allV part j) +
                                 2 * peelDeficit G allV part j)).sum ≤ 28) ∨
       (sortDesc sizes = [7, 6, 6, 6, 6, 6] ∧
        ((verts 6).map (fun j => twoEdgesIn G.compl (peelPart allV part j) +
                                 2 * peelDeficit G allV part j)).sum ≤ 30)) := by
  obtain ⟨c, part, hsparse, h2e, hαp, hmin, hcross, _, htot, hper⟩ :=
    furedi_peel_sparsest (r := 6) (by omega) C hbal
  have hlow := r6_low_degree_card_le_18 C hbal c
  let G := colorClass C c
  let allV : Fin (6 * 6 + 1) → Bool := fun _ => true
  let s : Fin 6 → Nat := fun j => subsetCard (peelPart allV part j)
  let sizes := (verts 6).map s
  have hper_e : ∀ j : Fin 6, edgesIn G.compl (peelPart allV part j) ≥ 5 * (s j - 6) := by
    intro j
    have h1 := hper j
    have h2 := two_mul_edgesIn G.compl (peelPart allV part j)
    dsimp [G, allV, s] at h1 h2 ⊢
    omega
  have himb_sum : ((verts 6).map (fun j => s j * (s j - 1) + 10 * (s j - 6))).sum ≤ 222 := by
    have hle : ((verts 6).map (fun j => s j * (s j - 1) + 10 * (s j - 6))).sum ≤
               ((verts 6).map (fun j =>
                 s j * (s j - 1) + twoEdgesIn G.compl (peelPart allV part j) +
                 2 * peelDeficit G allV part j)).sum := by
      apply sum_map_le; intro j _
      have h1 := hper j
      dsimp [G, allV, s] at h1 ⊢
      omega
    have ht' : twoEdgesIn G allV =
               ((verts 6).map (fun j =>
                 s j * (s j - 1) + twoEdgesIn G.compl (peelPart allV part j) +
                 2 * peelDeficit G allV part j)).sum := htot
    have h2e' : twoEdgesIn G allV ≤ 222 := h2e
    omega
  have hlen : (sortDesc sizes).length = 6 := by
    rw [sortDesc_length]; dsimp [sizes]; simp [length_verts]
  have hsum : (sortDesc sizes).sum = 37 := by
    rw [sortDesc_sum]; dsimp [sizes]
    have h := subsetCard_partition_fin allV part
    rw [subsetCard_true] at h
    exact h
  have himb' : ((sortDesc sizes).map (fun x => x * (x - 1) + 10 * (x - 6))).sum ≤ 222 := by
    rw [sortDesc_map_sum]; dsimp [sizes]; rw [List.map_map]; exact himb_sum
  have hpw := sortDesc_sorted sizes
  have hmem3 : sortDesc sizes ∈ threeR6Partitions := by
    match hsd : sortDesc sizes with
    | [a, b, c', d, e, f] =>
      rw [hsd] at hsum himb' hpw
      simp only [List.sum_cons, List.sum_nil, Nat.add_zero, List.map_cons, List.map_nil] at hsum himb'
      rw [List.pairwise_cons] at hpw
      have hpw2 := hpw.2; rw [List.pairwise_cons] at hpw2
      have hpw3 := hpw2.2; rw [List.pairwise_cons] at hpw3
      have hpw4 := hpw3.2; rw [List.pairwise_cons] at hpw4
      have hpw5 := hpw4.2; rw [List.pairwise_cons] at hpw5
      exact classify_6tuple_imbalance a b c' d e f
        ⟨hpw.1 b (by simp), hpw2.1 c' (by simp), hpw3.1 d (by simp), hpw4.1 e (by simp), hpw5.1 f (by simp)⟩
        (by omega) (by omega)
    | [] => simp [hsd] at hlen
    | [_] => simp [hsd] at hlen
    | [_, _] => simp [hsd] at hlen
    | [_, _, _] => simp [hsd] at hlen
    | [_, _, _, _] => simp [hsd] at hlen
    | [_, _, _, _, _] => simp [hsd] at hlen
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => simp [hsd] at hlen
  have hsplit_tot : ((verts 6).map (fun j => s j * (s j - 1))).sum +
                    ((verts 6).map (fun j => twoEdgesIn G.compl (peelPart allV part j) +
                                             2 * peelDeficit G allV part j)).sum ≤ 222 := by
    have hs1 : ((verts 6).map (fun j =>
        s j * (s j - 1) + twoEdgesIn G.compl (peelPart allV part j) +
        2 * peelDeficit G allV part j)).sum =
        ((verts 6).map (fun j => s j * (s j - 1))).sum +
        ((verts 6).map (fun j => twoEdgesIn G.compl (peelPart allV part j) +
                                 2 * peelDeficit G allV part j)).sum := by
      rw [← sum_map_add]; apply sum_map_eq; intro j _; omega
    have ht' : twoEdgesIn G allV =
        ((verts 6).map (fun j =>
          s j * (s j - 1) + twoEdgesIn G.compl (peelPart allV part j) +
          2 * peelDeficit G allV part j)).sum := htot
    have h2e' : twoEdgesIn G allV ≤ 222 := h2e
    omega
  refine ⟨c, part, hsparse, hlow.1, hlow.2, hper_e, htot, ?_⟩
  simp only [threeR6Partitions, List.mem_cons, List.not_mem_nil, or_false] at hmem3
  rcases hmem3 with h8 | h77 | h7
  · exact False.elim (r6_no_size_8_part C hbal c part h2e hαp hmin hcross htot hper h8)
  · left
    have hss : ((verts 6).map (fun j => s j * (s j - 1))).sum = 194 := by
      have h1 := sortDesc_map_sum (fun x => x * (x - 1)) sizes
      rw [h77] at h1; dsimp [sizes] at h1; rw [List.map_map] at h1
      have h2 : ((verts 6).map ((fun x => x * (x - 1)) ∘ s)).sum =
                ((verts 6).map (fun j => s j * (s j - 1))).sum := rfl
      rw [h2] at h1
      simpa using h1.symm
    have hbd : ((verts 6).map (fun j => twoEdgesIn G.compl (peelPart allV part j) +
                                        2 * peelDeficit G allV part j)).sum ≤ 28 := by omega
    exact ⟨h77, hbd⟩
  · right
    have hss : ((verts 6).map (fun j => s j * (s j - 1))).sum = 192 := by
      have h1 := sortDesc_map_sum (fun x => x * (x - 1)) sizes
      rw [h7] at h1; dsimp [sizes] at h1; rw [List.map_map] at h1
      have h2 : ((verts 6).map ((fun x => x * (x - 1)) ∘ s)).sum =
                ((verts 6).map (fun j => s j * (s j - 1))).sum := rfl
      rw [h2] at h1
      simpa using h1.symm
    have hbd : ((verts 6).map (fun j => twoEdgesIn G.compl (peelPart allV part j) +
                                        2 * peelDeficit G allV part j)).sum ≤ 30 := by omega
    exact ⟨h7, hbd⟩

end Erdos617
