/-
  Erdős Problem #617 (Erdős–Gyárfás Balanced Coloring Conjecture)
  Verified Lean 4 Formalization (zero sorry, zero axiom, zero admit, standalone Lean 4.37)

  Contents:
  1. Core finite simple graph combinatorics on `Fin n` (relativized to vertex subsets `S : Fin n → Bool`).
  2. Theorem A (`turan_linear_envelope`): Exact linear envelope of Turán's theorem:
       α(G[S]) ≤ r  →  ∀ k, 2 * e(G[S]) + k * (k + 1) * r ≥ 2 * k * |S|.
  3. Theorem B (`single_graph_relaxation_fails`): Complete disproof of the Xia–Szeider
     single-graph relaxation for r = 7 and all r ≥ 9 (via balanced C₅-blowup ⊔ (r-2) K_r
     for r ∈ {7, 9} ∪ {r ≥ 11}, and And₃-blowup ⊔ 8 K₁₀ for r = 10).
  4. Theorem C (`multiscale_turan_complement`): Multi-scale Turán-complement lower bound
     for every color class in a balanced r-coloring of K_{r²+1}.
  5. Theorem D (`non_bipartite_mantel`): Elementary proof that every triangle-free,
     non-bipartite graph on m ≥ 5 vertices has 4 * e ≤ (m - 1)² + 4.
  6. Theorem E (`no_2r_plus_1_alpha_le_2`, `indep_r_minus_2_degree_sum`, `low_degree_alpha_bound`):
     For all r ≥ 4, in any balanced r-coloring of K_{r²+1}:
       - No color class contains a (2r+1)-subset with independence number ≤ 2
         (ruling out every k = 2 single-graph witness from extending to a full r-coloring).
       - Every (r-2)-independent set I has |N[I]| ≥ (r-1)² and ∑_{v ∈ I} d(v) ≥ (r-2)(r-1) + 1.
       - The set of vertices of degree ≤ r - 1 has independence number ≤ r - 3.
-/

namespace Erdos617

/-! ## Section 1: Core Graph & List Combinatorics -/

structure SGraph (n : Nat) where
  adj : Fin n → Fin n → Bool
  symm : ∀ u v, adj u v = adj v u
  loopless : ∀ u, adj u u = false

def SGraph.compl {n : Nat} (G : SGraph n) : SGraph n where
  adj u v := decide (u ≠ v) && !G.adj u v
  symm u v := by
    rw [G.symm u v]
    by_cases h : u = v
    · subst h; simp
    · have h' : v ≠ u := Ne.symm h
      simp [h, h']
  loopless u := by simp

def verts (n : Nat) : List (Fin n) := List.finRange n

def subsetCard {n : Nat} (S : Fin n → Bool) : Nat :=
  ((verts n).filter S).length

def degIn {n : Nat} (G : SGraph n) (S : Fin n → Bool) (u : Fin n) : Nat :=
  ((verts n).filter (fun v => S v && G.adj u v)).length

def twoEdgesIn {n : Nat} (G : SGraph n) (S : Fin n → Bool) : Nat :=
  (((verts n).filter S).map (degIn G S)).sum

def edgesIn {n : Nat} (G : SGraph n) (S : Fin n → Bool) : Nat :=
  twoEdgesIn G S / 2

def deg {n : Nat} (G : SGraph n) (u : Fin n) : Nat :=
  degIn G (fun _ => true) u

def twoEdges {n : Nat} (G : SGraph n) : Nat :=
  twoEdgesIn G (fun _ => true)

def edges {n : Nat} (G : SGraph n) : Nat :=
  edgesIn G (fun _ => true)

def IsIndep {n : Nat} (G : SGraph n) (S : Fin n → Bool) : Prop :=
  ∀ u v, S u = true → S v = true → G.adj u v = false

structure EdgeColoring (n r : Nat) where
  col : Fin n → Fin n → Fin r
  symm : ∀ u v, col u v = col v u

def colorClass {n r : Nat} (C : EdgeColoring n r) (c : Fin r) : SGraph n where
  adj u v := decide (u ≠ v ∧ C.col u v = c)
  symm u v := by
    rw [C.symm u v]
    by_cases h : u = v
    · subst h; simp
    · have h' : v ≠ u := Ne.symm h
      simp [h, h']
  loopless u := by simp

def IsBalanced {r : Nat} (C : EdgeColoring (r * r + 1) r) : Prop :=
  ∀ (c : Fin r) (S : Fin (r * r + 1) → Bool),
    subsetCard S = r + 1 → edgesIn (colorClass C c) S ≥ 1

def SatisfiesSingleGraphRelaxation (r : Nat) (G : SGraph (r * r + 1)) : Prop :=
  edges G ≤ r * (r * r + 1) / 2 ∧
  ∀ S : Fin (r * r + 1) → Bool, subsetCard S = r + 1 →
    1 ≤ edgesIn G S ∧ edgesIn G S ≤ r * (r - 1) / 2 + 1

/-! ### Helper Lemmas on Lists and Sums -/

theorem nodup_filter {α : Type} (p : α → Bool) {l : List α} (h : l.Nodup) : (l.filter p).Nodup := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.nodup_cons] at h
    cases hp : p x
    · simp [hp, ih h.2]
    · simp only [List.filter_cons, hp, ↓reduceIte, List.nodup_cons]
      exact ⟨fun hm => h.1 (List.mem_filter.mp hm).1, ih h.2⟩

theorem mul_pred_even (r : Nat) : r * (r - 1) % 2 = 0 := by
  cases r with
  | zero => simp
  | succ k =>
    simp only [Nat.add_sub_cancel]
    have : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases this with h | h
    · obtain ⟨m, hm⟩ : ∃ m, k = 2 * m := ⟨k / 2, by omega⟩
      rw [hm]; have : (2 * m + 1) * (2 * m) = 2 * ((2 * m + 1) * m) := by
        rw [Nat.mul_comm (2 * m + 1) (2 * m), Nat.mul_assoc, Nat.mul_comm m (2 * m + 1)]
      omega
    · obtain ⟨m, hm⟩ : ∃ m, k = 2 * m + 1 := ⟨k / 2, by omega⟩
      rw [hm]; have : (2 * m + 1 + 1) * (2 * m + 1) = 2 * ((m + 1) * (2 * m + 1)) := by
        have h1 : 2 * m + 1 + 1 = 2 * (m + 1) := by omega
        rw [h1, Nat.mul_assoc]
      omega

theorem le_sum_of_mem {a : Nat} {l : List Nat} (h : a ∈ l) : a ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h'
    · omega
    · have := ih h'; omega

theorem sum_map_add {α : Type} (l : List α) (f g : α → Nat) :
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [List.map, List.sum_cons, ih]; omega

theorem sum_map_le {α : Type} (l : List α) (f g : α → Nat) (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    have hx := h x (by simp)
    have hxs := ih (fun y hy => h y (by simp [hy]))
    omega

theorem sum_map_eq {α : Type} (l : List α) (f g : α → Nat) (h : ∀ x ∈ l, f x = g x) :
    (l.map f).sum = (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

theorem sum_map_const {α : Type} (l : List α) (c : Nat) :
    (l.map (fun _ => c)).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

theorem sum_map_mul_left {α : Type} (l : List α) (c : Nat) (f : α → Nat) :
    (l.map (fun x => c * f x)).sum = c * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]

theorem length_filter_eq_sum {α : Type} (l : List α) (p : α → Bool) :
    (l.filter p).length = (l.map (fun x => if p x then 1 else 0)).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    cases h : p x <;> simp [h, ih] <;> omega

theorem sum_filter_eq_sum_ite {α : Type} (l : List α) (p : α → Bool) (f : α → Nat) :
    ((l.filter p).map f).sum = (l.map (fun x => if p x then f x else 0)).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    cases h : p x <;> simp [h, ih]

theorem sum_swap {α β : Type} (la : List α) (lb : List β) (f : α → β → Nat) :
    (la.map (fun a => (lb.map (fun b => f a b)).sum)).sum =
    (lb.map (fun b => (la.map (fun a => f a b)).sum)).sum := by
  induction la with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    symm
    rw [sum_map_const, Nat.mul_zero]
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    rw [← sum_map_add]

theorem filter_length_partition {α : Type} (l : List α) (p q : α → Bool) :
    (l.filter p).length = (l.filter (fun x => p x && q x)).length +
                          (l.filter (fun x => p x && !q x)).length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    cases hp : p x <;> cases hq : q x <;> simp [hp, hq, ih] <;> omega

theorem filter_length_le {α : Type} (l : List α) (p q : α → Bool)
    (h : ∀ x ∈ l, p x = true → q x = true) :
    (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hxs := ih (fun y hy => h y (by simp [hy]))
    cases hp : p x
    · cases hq : q x <;> simp [hp, hq] <;> omega
    · have hq := h x (by simp) hp
      simp [hp, hq]
      omega

theorem filter_length_eq {α : Type} (l : List α) (p q : α → Bool)
    (h : ∀ x ∈ l, p x = q x) :
    (l.filter p).length = (l.filter q).length := by
  have h1 := filter_length_le l p q (fun x hx hp => by rw [← h x hx]; exact hp)
  have h2 := filter_length_le l q p (fun x hx hq => by rw [h x hx]; exact hq)
  omega

theorem length_filter_eq_one_of_nodup {α : Type} [DecidableEq α] (l : List α)
    (hnd : l.Nodup) (a : α) (ha : a ∈ l) :
    (l.filter (fun x => decide (x = a))).length = 1 := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    rw [List.nodup_cons] at hnd
    rcases List.mem_cons.mp ha with rfl | hmem
    · have h0 : (xs.filter (fun y => decide (y = a))).length = 0 := by
        rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
        intro y hy
        simp
        intro heq; subst heq; exact hnd.1 hy
      simp [h0]
    · have hne : x ≠ a := fun heq => hnd.1 (heq ▸ hmem)
      simp [hne, ih hnd.2 hmem]

theorem mem_verts {n : Nat} (u : Fin n) : u ∈ verts n := List.mem_finRange u

theorem nodup_verts (n : Nat) : (verts n).Nodup := List.nodup_finRange n

theorem length_verts (n : Nat) : (verts n).length = n := List.length_finRange

theorem filter_true_eq {α : Type} (l : List α) : l.filter (fun _ => true) = l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem subsetCard_true (n : Nat) : subsetCard (fun _ : Fin n => true) = n := by
  unfold subsetCard
  rw [filter_true_eq, length_verts]

theorem subsetCard_singleton {n : Nat} (u : Fin n) :
    subsetCard (fun v => decide (v = u)) = 1 := by
  unfold subsetCard
  exact length_filter_eq_one_of_nodup (verts n) (nodup_verts n) u (mem_verts u)

theorem twoEdgesIn_eq_double_sum {n : Nat} (G : SGraph n) (S : Fin n → Bool) :
    twoEdgesIn G S =
      ((verts n).map (fun u => ((verts n).map (fun v =>
        if S u && S v && G.adj u v then 1 else 0)).sum)).sum := by
  unfold twoEdgesIn degIn
  rw [sum_filter_eq_sum_ite]
  apply sum_map_eq
  intro u _
  cases hSu : S u
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_and]
    symm
    rw [sum_map_const, Nat.mul_zero]
  · simp only [↓reduceIte, Bool.true_and]
    exact length_filter_eq_sum (verts n) (fun v => S v && G.adj u v)

/-- Evenness of `twoEdgesIn`: every undirected edge is counted twice (for `(u, v)` and `(v, u)`). -/
theorem twoEdgesIn_even {n : Nat} (G : SGraph n) (S : Fin n → Bool) :
    twoEdgesIn G S % 2 = 0 := by
  rw [twoEdgesIn_eq_double_sum]
  -- Split into u.val < v.val and v.val < u.val; diagonal u = v is 0 by loopless.
  let ltSum := ((verts n).map (fun u => ((verts n).map (fun v =>
    if S u && S v && G.adj u v && decide (u.val < v.val) then 1 else 0)).sum)).sum
  let gtSum := ((verts n).map (fun u => ((verts n).map (fun v =>
    if S u && S v && G.adj u v && decide (v.val < u.val) then 1 else 0)).sum)).sum
  have hsplit : ((verts n).map (fun u => ((verts n).map (fun v =>
      if S u && S v && G.adj u v then 1 else 0)).sum)).sum = ltSum + gtSum := by
    dsimp [ltSum, gtSum]
    rw [← sum_map_add]
    apply sum_map_eq; intro u _
    rw [← sum_map_add]
    apply sum_map_eq; intro v _
    by_cases hlt : u.val < v.val
    · have hgt : ¬ (v.val < u.val) := by omega
      cases (S u && S v && G.adj u v) <;> simp [hlt, hgt]
    · by_cases hgt : v.val < u.val
      · cases (S u && S v && G.adj u v) <;> simp [hlt, hgt]
      · have heq : u = v := Fin.ext (by omega)
        subst heq
        simp [G.loopless u]
  have heq_sym : ltSum = gtSum := by
    dsimp [ltSum, gtSum]
    rw [sum_swap (verts n) (verts n)]
    apply sum_map_eq; intro v _
    apply sum_map_eq; intro u _
    rw [G.symm u v]
    cases S u <;> cases S v <;> cases G.adj v u <;> simp
  rw [hsplit, heq_sym]
  omega

theorem two_mul_edgesIn {n : Nat} (G : SGraph n) (S : Fin n → Bool) :
    2 * edgesIn G S = twoEdgesIn G S := by
  unfold edgesIn
  have h := twoEdgesIn_even G S
  omega

theorem two_mul_edges {n : Nat} (G : SGraph n) :
    2 * edges G = twoEdges G :=
  two_mul_edgesIn G (fun _ => true)

theorem degIn_add_compl {n : Nat} (G : SGraph n) (S : Fin n → Bool) (u : Fin n) (hSu : S u = true) :
    degIn G S u + degIn G.compl S u = subsetCard S - 1 := by
  unfold degIn subsetCard SGraph.compl
  have hpart := filter_length_partition (verts n) S (fun v => decide (v = u))
  have h1 : ((verts n).filter (fun v => S v && decide (v = u))).length = 1 := by
    have heq : ((verts n).filter (fun v => S v && decide (v = u))).length =
               ((verts n).filter (fun v => decide (v = u))).length := by
      apply filter_length_eq; intro v _
      by_cases hv : v = u
      · subst hv; simp [hSu]
      · simp [hv]
    rw [heq]
    exact length_filter_eq_one_of_nodup (verts n) (nodup_verts n) u (mem_verts u)
  have h2 := filter_length_partition (verts n) (fun v => S v && !decide (v = u)) (fun v => G.adj u v)
  have ha : ((verts n).filter (fun v => S v && G.adj u v)).length =
            ((verts n).filter (fun v => (S v && !decide (v = u)) && G.adj u v)).length := by
    apply filter_length_eq; intro v _
    by_cases hv : v = u
    · rw [hv]; simp [G.loopless u]
    · simp [hv]
  have hb : ((verts n).filter (fun v => S v && (decide (u ≠ v) && !G.adj u v))).length =
            ((verts n).filter (fun v => (S v && !decide (v = u)) && !G.adj u v)).length := by
    apply filter_length_eq; intro v _
    by_cases hv : v = u
    · subst hv; simp
    · have hv' : u ≠ v := Ne.symm hv
      simp [hv, hv']
  rw [ha, hb]
  omega

theorem twoEdgesIn_add_compl {n : Nat} (G : SGraph n) (S : Fin n → Bool) :
    twoEdgesIn G S + twoEdgesIn G.compl S = subsetCard S * (subsetCard S - 1) := by
  unfold twoEdgesIn
  rw [← sum_map_add]
  have h := sum_map_eq ((verts n).filter S)
    (fun u => degIn G S u + degIn G.compl S u)
    (fun _ => subsetCard S - 1)
    (fun u hu => degIn_add_compl G S u (List.mem_filter.mp hu).2)
  rw [h, sum_map_const]
  rfl

theorem edgesIn_add_compl {n : Nat} (G : SGraph n) (S : Fin n → Bool) :
    2 * edgesIn G S + 2 * edgesIn G.compl S = subsetCard S * (subsetCard S - 1) := by
  rw [two_mul_edgesIn, two_mul_edgesIn, twoEdgesIn_add_compl]

theorem twoEdgesIn_le_complete {n : Nat} (G : SGraph n) (S : Fin n → Bool) :
    twoEdgesIn G S ≤ subsetCard S * (subsetCard S - 1) := by
  have h := twoEdgesIn_add_compl G S
  omega

theorem isIndep_iff_twoEdgesIn_zero {n : Nat} (G : SGraph n) (S : Fin n → Bool) :
    IsIndep G S ↔ twoEdgesIn G S = 0 := by
  constructor
  · intro hind
    rw [twoEdgesIn_eq_double_sum]
    have h0 : ∀ u ∈ verts n, ((verts n).map (fun v =>
        if S u && S v && G.adj u v then 1 else 0)).sum = 0 := by
      intro u _
      have h1 : ∀ v ∈ verts n, (if S u && S v && G.adj u v then 1 else 0) = 0 := by
        intro v _
        cases hSu : S u
        · simp
        · cases hSv : S v
          · simp
          · simp [hind u v hSu hSv]
      rw [sum_map_eq (verts n) _ (fun _ => 0) h1, sum_map_const, Nat.mul_zero]
    rw [sum_map_eq (verts n) _ (fun _ => 0) h0, sum_map_const, Nat.mul_zero]
  · intro hzero u v hSu hSv
    rw [twoEdgesIn_eq_double_sum] at hzero
    cases hadj' : G.adj u v
    · rfl
    · exfalso
      have hpos : 1 ≤ ((verts n).map (fun u' => ((verts n).map (fun v' =>
          if S u' && S v' && G.adj u' v' then 1 else 0)).sum)).sum := by
        have hinner : 1 ≤ ((verts n).map (fun v' =>
            if S u && S v' && G.adj u v' then 1 else 0)).sum := by
          have hmem : (1 : Nat) ∈ (verts n).map (fun v' =>
              if S u && S v' && G.adj u v' then 1 else 0) := by
            refine List.mem_map.mpr ⟨v, mem_verts v, ?_⟩
            simp [hSu, hSv, hadj']
          exact le_sum_of_mem hmem
        have hmem2 : ((verts n).map (fun v' =>
              if S u && S v' && G.adj u v' then 1 else 0)).sum ∈
            (verts n).map (fun u' => ((verts n).map (fun v' =>
              if S u' && S v' && G.adj u' v' then 1 else 0)).sum) :=
          List.mem_map.mpr ⟨u, mem_verts u, rfl⟩
        have hle := le_sum_of_mem hmem2
        omega
      omega

theorem isIndep_iff_edgesIn_zero {n : Nat} (G : SGraph n) (S : Fin n → Bool) :
    IsIndep G S ↔ edgesIn G S = 0 := by
  rw [isIndep_iff_twoEdgesIn_zero]
  have h := two_mul_edgesIn G S
  omega

/-! ## Section 2: Theorem A — Exact Linear Envelope of Turán's Theorem -/

theorem exists_min_degIn {n : Nat} (G : SGraph n) (S : Fin n → Bool) (hne : subsetCard S > 0) :
    ∃ v : Fin n, S v = true ∧ ∀ u : Fin n, S u = true → degIn G S v ≤ degIn G S u := by
  have hlen : ((verts n).filter S).length > 0 := hne
  have aux : ∀ (l : List (Fin n)), l.length > 0 →
      ∃ v ∈ l, ∀ u ∈ l, degIn G S v ≤ degIn G S u := by
    intro l
    induction l with
    | nil => intro h; simp at h
    | cons x xs ih =>
      intro _
      cases xs with
      | nil => exact ⟨x, by simp, fun u hu => by simp at hu; subst hu; exact Nat.le_refl _⟩
      | cons y ys =>
        obtain ⟨m, hm, hmin⟩ := ih (by simp)
        by_cases hxm : degIn G S x ≤ degIn G S m
        · refine ⟨x, by simp, fun u hu => ?_⟩
          rcases List.mem_cons.mp hu with rfl | hu'
          · exact Nat.le_refl _
          · exact Nat.le_trans hxm (hmin u hu')
        · refine ⟨m, by simp [hm], fun u hu => ?_⟩
          rcases List.mem_cons.mp hu with rfl | hu'
          · omega
          · exact hmin u hu'
  obtain ⟨v, hv, hmin⟩ := aux ((verts n).filter S) hlen
  refine ⟨v, (List.mem_filter.mp hv).2, fun u hu => hmin u ?_⟩
  exact List.mem_filter.mpr ⟨mem_verts u, hu⟩

/-- Removing `N_S[v]` from `S` decreases `twoEdgesIn` by at least `∑_{u ∈ N_S[v]} degIn G S u`. -/
theorem twoEdgesIn_remove_closedNbr {n : Nat} (G : SGraph n) (S : Fin n → Bool) (v : Fin n)
    (hSv : S v = true) :
    let Nv : Fin n → Bool := fun u => S u && (decide (u = v) || G.adj v u)
    let R  : Fin n → Bool := fun u => S u && !(decide (u = v) || G.adj v u)
    subsetCard S = subsetCard Nv + subsetCard R ∧
    subsetCard Nv = degIn G S v + 1 ∧
    twoEdgesIn G S ≥ twoEdgesIn G R + (((verts n).filter Nv).map (degIn G S)).sum := by
  intro Nv R
  refine ⟨?_, ?_, ?_⟩
  · unfold subsetCard
    exact filter_length_partition (verts n) S (fun u => decide (u = v) || G.adj v u)
  · unfold subsetCard degIn
    have hpart := filter_length_partition (verts n) Nv (fun u => decide (u = v))
    have h1 : ((verts n).filter (fun u => Nv u && decide (u = v))).length = 1 := by
      have heq : ((verts n).filter (fun u => Nv u && decide (u = v))).length =
                 ((verts n).filter (fun u => decide (u = v))).length := by
        apply filter_length_eq; intro u _
        by_cases hu : u = v
        · subst hu; simp [Nv, hSv]
        · simp [hu]
      rw [heq]
      exact length_filter_eq_one_of_nodup (verts n) (nodup_verts n) v (mem_verts v)
    have h2 : ((verts n).filter (fun u => Nv u && !decide (u = v))).length =
              ((verts n).filter (fun u => S u && G.adj v u)).length := by
      apply filter_length_eq; intro u _
      by_cases hu : u = v
      · rw [hu]; simp [Nv, G.loopless v]
      · simp [Nv, hu]
    omega
  · unfold twoEdgesIn
    rw [sum_filter_eq_sum_ite (verts n) S,
        sum_filter_eq_sum_ite (verts n) R,
        sum_filter_eq_sum_ite (verts n) Nv]
    rw [← sum_map_add]
    apply sum_map_le
    intro u _
    by_cases hSu : S u = true
    · by_cases hin : (decide (u = v) || G.adj v u) = true
      · simp only [Nv, R, hSu, hin, Bool.not_true, Bool.and_false, Bool.and_true, ↓reduceIte,
                   Bool.false_eq_true, Nat.zero_add, Nat.le_refl]
      · have hin' : (decide (u = v) || G.adj v u) = false := by
          cases h : (decide (u = v) || G.adj v u)
          · rfl
          · exact absurd h hin
        simp only [hSu, Nv, R, hin', Bool.and_false, Bool.not_false, Bool.and_true, ↓reduceIte,
                   Bool.false_eq_true, Nat.add_zero]
        unfold degIn
        apply filter_length_le
        intro w _ hw
        simp only [Bool.and_eq_true] at hw ⊢
        exact ⟨hw.1.1, hw.2⟩
    · have hSu' : S u = false := by
        cases h : S u
        · rfl
        · exact absurd h hSu
      simp [hSu', Nv, R]

/-- **Theorem A (Exact Linear Envelope of Turán's Theorem):**
    If `G` restricted to `S` has independence number at most `r`, then for every `k : Nat`,
    `2 * edgesIn G S + k * (k + 1) * r ≥ 2 * k * subsetCard S`. -/
theorem turan_linear_envelope {n : Nat} (G : SGraph n) (S : Fin n → Bool) (r k : Nat)
    (hα : ∀ I : Fin n → Bool, (∀ v, I v = true → S v = true) → IsIndep G I → subsetCard I ≤ r) :
    2 * edgesIn G S + k * (k + 1) * r ≥ 2 * k * subsetCard S := by
  rw [two_mul_edgesIn]
  induction r generalizing S with
  | zero =>
    have h0 : subsetCard S = 0 := by
      cases hsc : subsetCard S with
      | zero => rfl
      | succ m =>
        exfalso
        have hpos : subsetCard S > 0 := by omega
        obtain ⟨v, hSv, _⟩ := exists_min_degIn G S hpos
        let I : Fin n → Bool := fun u => decide (u = v)
        have hsub : ∀ u, I u = true → S u = true := by
          intro u hu; simp [I] at hu; subst hu; exact hSv
        have hind : IsIndep G I := by
          intro a b ha hb; simp [I] at ha hb; rw [ha, hb]; exact G.loopless v
        have hle := hα I hsub hind
        rw [subsetCard_singleton] at hle
        omega
    rw [h0]; omega
  | succ r ih =>
    by_cases h0 : subsetCard S = 0
    · rw [h0]; omega
    · have hpos : subsetCard S > 0 := by omega
      obtain ⟨v, hSv, hmin⟩ := exists_min_degIn G S hpos
      let δ := degIn G S v
      let Nv : Fin n → Bool := fun u => S u && (decide (u = v) || G.adj v u)
      let R  : Fin n → Bool := fun u => S u && !(decide (u = v) || G.adj v u)
      obtain ⟨hcard, hNv, hedges⟩ := twoEdgesIn_remove_closedNbr G S v hSv
      -- Every independent set I in R extends with v to an independent set in S, so |I| ≤ r.
      have hαR : ∀ I : Fin n → Bool, (∀ u, I u = true → R u = true) → IsIndep G I →
          subsetCard I ≤ r := by
        intro I hsub hind
        let I' : Fin n → Bool := fun u => I u || decide (u = v)
        have hvnotI : I v = false := by
          cases hIv : I v
          · rfl
          · have hRv := hsub v hIv
            simp [R] at hRv
        have hsub' : ∀ u, I' u = true → S u = true := by
          intro u hu
          simp [I'] at hu
          rcases hu with hIu | rfl
          · exact (Bool.and_eq_true _ _ |>.mp (hsub u hIu)).1
          · exact hSv
        have hind' : IsIndep G I' := by
          intro a b ha hb
          simp [I'] at ha hb
          rcases ha with hIa | rfl <;> rcases hb with hIb | rfl
          · exact hind a b hIa hIb
          · have hRa := hsub a hIa
            simp [R] at hRa
            rw [G.symm]; exact hRa.2.2
          · have hRb := hsub b hIb
            simp [R] at hRb
            exact hRb.2.2
          · exact G.loopless _
        have hcardI' : subsetCard I' = subsetCard I + 1 := by
          unfold subsetCard
          have hp := filter_length_partition (verts n) I' (fun u => decide (u = v))
          have h1 : ((verts n).filter (fun u => I' u && decide (u = v))).length = 1 := by
            have heq : ((verts n).filter (fun u => I' u && decide (u = v))).length =
                       ((verts n).filter (fun u => decide (u = v))).length := by
              apply filter_length_eq; intro u _
              by_cases hu : u = v
              · subst hu; simp [I']
              · simp [hu]
            rw [heq]
            exact length_filter_eq_one_of_nodup (verts n) (nodup_verts n) v (mem_verts v)
          have h2 : ((verts n).filter (fun u => I' u && !decide (u = v))).length =
                    ((verts n).filter I).length := by
            apply filter_length_eq; intro u _
            by_cases hu : u = v
            · subst hu; simp [hvnotI]
            · simp [I', hu]
          omega
        have hle := hα I' hsub' hind'
        omega
      have hih := ih R hαR
      -- Lower bound on the removed degree sum: ∑_{u ∈ Nv} degIn G S u ≥ (δ + 1) * δ
      have hdegsum : (((verts n).filter Nv).map (degIn G S)).sum ≥ (δ + 1) * δ := by
        have hle := sum_map_le ((verts n).filter Nv) (fun _ => δ) (degIn G S)
          (fun u hu => hmin u (Bool.and_eq_true _ _ |>.mp (List.mem_filter.mp hu).2).1)
        rw [sum_map_const] at hle
        change subsetCard Nv * δ ≤ _ at hle
        rw [hNv] at hle
        exact hle
      -- Pure integer algebra: (δ - k) * (δ - k + 1) ≥ 0
      -- i.e. (δ + 1) * δ + k * (k + 1) ≥ 2 * k * (δ + 1)
      have hquad : (δ + 1) * δ + k * (k + 1) ≥ 2 * k * (δ + 1) := by
        have aux : ∀ a b : Nat, (a + 1) * a + b * (b + 1) ≥ 2 * b * (a + 1) := by
          intro a b
          by_cases hba : b ≤ a
          · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hba
            have hcomm : b * d = d * b := Nat.mul_comm b d
            have h2a : 2 * b * b = 2 * (b * b) := Nat.mul_assoc 2 b b
            have h2d : 2 * b * d = 2 * (b * d) := Nat.mul_assoc 2 b d
            have hexp : (b + d + 1) * (b + d) + b * (b + 1) = 2 * b * (b + d + 1) + d * (d + 1) := by
              simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
              omega
            omega
          · have hab : a + 1 ≤ b := by omega
            obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
            have hcomm : a * d = d * a := Nat.mul_comm a d
            have h2a : 2 * a * a = 2 * (a * a) := Nat.mul_assoc 2 a a
            have h2d : 2 * d * a = 2 * (d * a) := Nat.mul_assoc 2 d a
            have hexp : (a + 1) * a + (a + 1 + d) * (a + 1 + d + 1) =
                        2 * (a + 1 + d) * (a + 1) + d * (d + 1) := by
              simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
              omega
            omega
        exact aux δ k
      have hmul : k * (k + 1) * (r + 1) = k * (k + 1) * r + k * (k + 1) := Nat.mul_succ _ _
      have hmul2 : 2 * k * subsetCard S = 2 * k * (δ + 1) + 2 * k * subsetCard R := by
        rw [hcard, hNv, Nat.mul_add]
      have hedges' : twoEdgesIn G S ≥ twoEdgesIn G R + (((verts n).filter Nv).map (degIn G S)).sum := hedges
      omega

/-! ## Section 3: Theorem B — Failure of the Xia–Szeider Single-Graph Relaxation -/

/-! ### Disjoint-Union and Convexity Helpers -/

theorem sum_mul_pred_le (ys : List Nat) :
    (ys.map (fun y => y * (y - 1))).sum ≤ ys.sum * (ys.sum - 1) := by
  induction ys with
  | nil => simp
  | cons y rest ih =>
    simp only [List.map_cons, List.sum_cons]
    have hstep : ∀ a b : Nat, a * (a - 1) + b * (b - 1) ≤ (a + b) * (a + b - 1) := by
      intro a b
      cases a with
      | zero => simp
      | succ a' =>
        cases b with
        | zero => simp
        | succ b' =>
          simp only [Nat.add_sub_cancel]
          have hsub : a' + 1 + (b' + 1) - 1 = a' + b' + 1 := by omega
          rw [hsub]
          have h1 : (a' + 1) * a' + (b' + 1) * b' + 2 * (a' + 1) * (b' + 1) =
                    (a' + 1 + (b' + 1)) * (a' + b' + 1) := by
            simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
            have hc : a' * b' = b' * a' := Nat.mul_comm a' b'
            have h2 : 2 * a' * b' = 2 * (a' * b') := Nat.mul_assoc 2 a' b'
            omega
          omega
    have hs := hstep y rest.sum
    omega

theorem pair_mul_pred_le (a b r : Nat) (ha : a ≤ r) (hb : b ≤ r) (hsum : a + b ≤ r + 1) :
    a * (a - 1) + b * (b - 1) ≤ r * (r - 1) := by
  cases a with
  | zero =>
    simp only [Nat.zero_mul, Nat.zero_add]
    exact Nat.mul_le_mul hb (Nat.sub_le_sub_right hb 1)
  | succ a' =>
    cases b with
    | zero =>
      simp only [Nat.zero_mul, Nat.add_zero]
      exact Nat.mul_le_mul ha (Nat.sub_le_sub_right ha 1)
    | succ b' =>
      simp only [Nat.add_sub_cancel]
      have hs : a' + b' + 1 ≤ r := by omega
      have hid : (a' + 1) * a' + (b' + 1) * b' + 2 * a' * b' = (a' + b' + 1) * (a' + b') := by
        simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]
        have hc : a' * b' = b' * a' := Nat.mul_comm a' b'
        have h2 : 2 * a' * b' = 2 * (a' * b') := Nat.mul_assoc 2 a' b'
        omega
      have hle : (a' + b' + 1) * (a' + b') ≤ r * (r - 1) :=
        Nat.mul_le_mul hs (by omega)
      omega

theorem disjoint_union_convexity (xs : List Nat) (r : Nat)
    (hle : ∀ x ∈ xs, x ≤ r) (hsum : xs.sum ≤ r + 1) :
    (xs.map (fun x => x * (x - 1))).sum ≤ r * (r - 1) := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    simp only [List.map_cons, List.sum_cons] at hsum ⊢
    have hx : x ≤ r := hle x (by simp)
    have hrest : ∀ y ∈ rest, y ≤ r := fun y hy => hle y (by simp [hy])
    by_cases hbr : rest.sum ≤ r
    · have h1 := sum_mul_pred_le rest
      have h2 := pair_mul_pred_le x rest.sum r hx hbr hsum
      omega
    · have hx0 : x = 0 := by omega
      have hsum' : rest.sum ≤ r + 1 := by omega
      have hih := ih hrest hsum'
      rw [hx0]
      simp [hih]

theorem subsetCard_partition_fin {n m : Nat} (S : Fin n → Bool) (comp : Fin n → Fin m) :
    ((verts m).map (fun j => subsetCard (fun v => S v && decide (comp v = j)))).sum =
    subsetCard S := by
  unfold subsetCard
  have h1 : ∀ j ∈ verts m, ((verts n).filter (fun v => S v && decide (comp v = j))).length =
      ((verts n).map (fun v => if S v && decide (comp v = j) then 1 else 0)).sum :=
    fun j _ => length_filter_eq_sum (verts n) _
  rw [sum_map_eq (verts m) _ _ h1, sum_swap (verts m) (verts n)]
  rw [length_filter_eq_sum (verts n) S]
  apply sum_map_eq; intro v _
  cases hSv : S v
  · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rw [sum_map_const, Nat.mul_zero]
  · simp only [Bool.true_and, ↓reduceIte]
    have h2 : ((verts m).map (fun j => if decide (comp v = j) then 1 else 0)).sum =
              ((verts m).filter (fun j => decide (j = comp v))).length := by
      rw [length_filter_eq_sum]
      apply sum_map_eq; intro j _
      by_cases h : j = comp v
      · subst h; simp
      · have h' : comp v ≠ j := Ne.symm h
        simp [h, h']
    rw [h2]
    exact length_filter_eq_one_of_nodup (verts m) (nodup_verts m) (comp v) (mem_verts (comp v))

theorem twoEdgesIn_partition_fin {n m : Nat} (G : SGraph n) (S : Fin n → Bool) (comp : Fin n → Fin m)
    (hdisj : ∀ u v, G.adj u v = true → comp u = comp v) :
    twoEdgesIn G S =
      ((verts m).map (fun j => twoEdgesIn G (fun v => S v && decide (comp v = j)))).sum := by
  rw [twoEdgesIn_eq_double_sum]
  have h1 : ∀ j ∈ verts m, twoEdgesIn G (fun v => S v && decide (comp v = j)) =
      ((verts n).map (fun u => ((verts n).map (fun v =>
        if (S u && decide (comp u = j)) && (S v && decide (comp v = j)) && G.adj u v
        then 1 else 0)).sum)).sum :=
    fun j _ => twoEdgesIn_eq_double_sum G _
  rw [sum_map_eq (verts m) _ _ h1, sum_swap (verts m) (verts n)]
  apply sum_map_eq; intro u _
  rw [sum_swap (verts m) (verts n)]
  apply sum_map_eq; intro v _
  cases hSu : S u
  · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    symm; rw [sum_map_const, Nat.mul_zero]
  · cases hSv : S v
    · simp only [Bool.true_and, Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      symm; rw [sum_map_const, Nat.mul_zero]
    · cases hadj : G.adj u v
      · simp only [Bool.true_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        symm; rw [sum_map_const, Nat.mul_zero]
      · simp only [Bool.true_and, Bool.and_true, ↓reduceIte]
        have hce : comp u = comp v := hdisj u v hadj
        symm
        have h2 : ((verts m).map (fun j =>
            if decide (comp u = j) && decide (comp v = j) then 1 else 0)).sum =
            ((verts m).filter (fun j => decide (j = comp u))).length := by
          rw [length_filter_eq_sum]
          apply sum_map_eq; intro j _
          rw [← hce]
          by_cases h : j = comp u
          · subst h; simp
          · have h' : comp u ≠ j := Ne.symm h
            simp [h, h']
        rw [h2]
        exact length_filter_eq_one_of_nodup (verts m) (nodup_verts m) (comp u) (mem_verts (comp u))

/-! ### Integer Convexity Minimum of the C₅ Quadratic Form -/

def c5Q (x0 x1 x2 x3 x4 : Nat) : Nat :=
  x0 * x1 + x1 * x2 + x2 * x3 + x3 * x4 + x4 * x0

theorem c5Q_rot (x0 x1 x2 x3 x4 : Nat) :
    c5Q x0 x1 x2 x3 x4 = c5Q x1 x2 x3 x4 x0 := by
  unfold c5Q; omega

theorem c5Q_shift_adj (x0 x1 x2 x3 x4 M : Nat)
    (h0l : 0 < x0) (h0u : x0 < M) (h1l : 0 < x1) (h1u : x1 < M) :
    let d1 := min x0 (M - x1)
    let d2 := min (M - x0) x1
    c5Q (x0 - d1) (x1 + d1) x2 x3 x4 ≤ c5Q x0 x1 x2 x3 x4 ∨
    c5Q (x0 + d2) (x1 - d2) x2 x3 x4 ≤ c5Q x0 x1 x2 x3 x4 := by
  intro d1 d2
  have hd1_pos : d1 ≥ 1 := by dsimp [d1]; omega
  have hd2_pos : d2 ≥ 1 := by dsimp [d2]; omega
  have hd1_le : d1 ≤ x0 := Nat.min_le_left _ _
  have hd2_le : d2 ≤ x1 := Nat.min_le_right _ _
  obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_le hd1_le
  obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le hd2_le
  -- Prove weighted concavity: d2 * Q(x0-d1, x1+d1) + d1 * Q(x0+d2, x1-d2) ≤ (d1 + d2) * Q(x0, x1)
  have hconc : d2 * c5Q (x0 - d1) (x1 + d1) x2 x3 x4 +
               d1 * c5Q (x0 + d2) (x1 - d2) x2 x3 x4 ≤
               (d1 + d2) * c5Q x0 x1 x2 x3 x4 := by
    have hx0 : x0 - d1 = a := by omega
    have hx1 : x1 - d2 = b := by omega
    rw [hx0, hx1, ha, hb]
    unfold c5Q
    -- Expand cleanly term-by-term:
    -- 1. First term: d2 * (a * (d2 + b + d1)) + d1 * ((d1 + a + d2) * b) + (d1+d2)*d1*d2 = (d1+d2)*((d1+a)*(d2+b))
    have ht1 : d2 * (a * (d2 + b + d1)) + d1 * ((d1 + a + d2) * b) ≤
               (d1 + d2) * ((d1 + a) * (d2 + b)) := by
      have hid : d2 * (a * (d2 + b + d1)) + d1 * ((d1 + a + d2) * b) + (d1 + d2) * (d1 * d2) =
                 (d1 + d2) * ((d1 + a) * (d2 + b)) := by
        simp only [Nat.add_mul, Nat.mul_add]
        -- Normalize every 3-factor product to sorted order
        have p1 : d2 * (a * d2) = a * (d2 * d2) := by rw [← Nat.mul_assoc, Nat.mul_comm d2 a, Nat.mul_assoc]
        have p2 : d2 * (a * b) = a * (b * d2) := by rw [← Nat.mul_assoc, Nat.mul_comm d2 a, Nat.mul_assoc, Nat.mul_comm d2 b]
        have p3 : d2 * (a * d1) = a * (d1 * d2) := by rw [← Nat.mul_assoc, Nat.mul_comm d2 a, Nat.mul_assoc, Nat.mul_comm d2 d1]
        have p4 : d1 * (d1 * b) = b * (d1 * d1) := by rw [← Nat.mul_assoc, Nat.mul_comm (d1 * d1) b]
        have p5 : d1 * (a * b) = a * (b * d1) := by rw [← Nat.mul_assoc, Nat.mul_comm d1 a, Nat.mul_assoc, Nat.mul_comm d1 b]
        have p6 : d1 * (d2 * b) = b * (d1 * d2) := by rw [← Nat.mul_assoc, Nat.mul_comm (d1 * d2) b]
        have p7 : d1 * (d1 * d2) = d1 * (d1 * d2) := rfl
        have p8 : d2 * (d1 * d2) = d1 * (d2 * d2) := by rw [← Nat.mul_assoc, Nat.mul_comm d2 d1, Nat.mul_assoc]
        have q1 : d1 * (d1 * d2) = d1 * (d1 * d2) := rfl
        have q2 : d1 * (d1 * b) = b * (d1 * d1) := p4
        have q3 : d1 * (a * d2) = a * (d1 * d2) := by rw [← Nat.mul_assoc, Nat.mul_comm d1 a, Nat.mul_assoc]
        have q4 : d1 * (a * b) = a * (b * d1) := p5
        have q5 : d2 * (d1 * d2) = d1 * (d2 * d2) := p8
        have q6 : d2 * (d1 * b) = b * (d1 * d2) := by rw [← Nat.mul_assoc, Nat.mul_comm d2 d1, Nat.mul_comm (d1 * d2) b]
        have q7 : d2 * (a * d2) = a * (d2 * d2) := p1
        have q8 : d2 * (a * b) = a * (b * d2) := p2
        omega
      omega
    -- 2. Linear terms in x1*x2: d2*((d2+b+d1)*x2) + d1*(b*x2) = (d1+d2)*((d2+b)*x2)
    have ht2 : d2 * ((d2 + b + d1) * x2) + d1 * (b * x2) =
               (d1 + d2) * ((d2 + b) * x2) := by
      simp only [Nat.add_mul, Nat.mul_add]
      have h1 : d2 * (d2 * x2) = d2 * (d2 * x2) := rfl
      have h2 : d2 * (b * x2) = d2 * (b * x2) := rfl
      have h3 : d2 * (d1 * x2) = d1 * (d2 * x2) := by rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_comm d2 d1]
      omega
    -- 3. Constant terms x2*x3 + x3*x4
    have ht3 : d2 * (x2 * x3) + d1 * (x2 * x3) = (d1 + d2) * (x2 * x3) := by
      rw [Nat.add_mul, Nat.add_comm]
    have ht4 : d2 * (x3 * x4) + d1 * (x3 * x4) = (d1 + d2) * (x3 * x4) := by
      rw [Nat.add_mul, Nat.add_comm]
    -- 4. Linear terms in x4*x0: d2*(x4*a) + d1*(x4*(d1+a+d2)) = (d1+d2)*(x4*(d1+a))
    have ht5 : d2 * (x4 * a) + d1 * (x4 * (d1 + a + d2)) =
               (d1 + d2) * (x4 * (d1 + a)) := by
      simp only [Nat.add_mul, Nat.mul_add]
      have h1 : d1 * (x4 * d2) = d2 * (x4 * d1) := by
        rw [← Nat.mul_assoc, Nat.mul_comm d1 x4, Nat.mul_assoc, Nat.mul_comm d1 d2, ← Nat.mul_assoc, Nat.mul_comm x4 d2, Nat.mul_assoc]
      omega
    have hdist : ∀ k p1 p2 p3 p4 p5 : Nat,
        k * (p1 + p2 + p3 + p4 + p5) = k * p1 + k * p2 + k * p3 + k * p4 + k * p5 := by
      intro k p1 p2 p3 p4 p5
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_add]
    rw [hdist d2, hdist d1, hdist (d1 + d2)]
    omega
  by_cases h : c5Q (x0 - d1) (x1 + d1) x2 x3 x4 ≤ c5Q x0 x1 x2 x3 x4
  · exact Or.inl h
  · right
    by_cases h2 : c5Q (x0 + d2) (x1 - d2) x2 x3 x4 ≤ c5Q x0 x1 x2 x3 x4
    · exact h2
    · exfalso
      have hlt1 : c5Q x0 x1 x2 x3 x4 + 1 ≤ c5Q (x0 - d1) (x1 + d1) x2 x3 x4 := by omega
      have hlt2 : c5Q x0 x1 x2 x3 x4 + 1 ≤ c5Q (x0 + d2) (x1 - d2) x2 x3 x4 := by omega
      have hm1 := Nat.mul_le_mul_left d2 hlt1
      have hm2 := Nat.mul_le_mul_left d1 hlt2
      have hsum : (d1 + d2) * (c5Q x0 x1 x2 x3 x4 + 1) =
                  d2 * (c5Q x0 x1 x2 x3 x4 + 1) + d1 * (c5Q x0 x1 x2 x3 x4 + 1) := by
        rw [Nat.add_mul, Nat.add_comm]
      have hstrict : (d1 + d2) * c5Q x0 x1 x2 x3 x4 + (d1 + d2) =
                     (d1 + d2) * (c5Q x0 x1 x2 x3 x4 + 1) := by rw [Nat.mul_succ]
      omega

theorem c5Q_shift_nonadj (x0 x1 x2 x3 x4 M : Nat)
    (h0l : 0 < x0) (h0u : x0 < M) (h2l : 0 < x2) (h2u : x2 < M) :
    let d1 := min x0 (M - x2)
    let d2 := min (M - x0) x2
    c5Q (x0 - d1) x1 (x2 + d1) x3 x4 ≤ c5Q x0 x1 x2 x3 x4 ∨
    c5Q (x0 + d2) x1 (x2 - d2) x3 x4 ≤ c5Q x0 x1 x2 x3 x4 := by
  intro d1 d2
  have hd1_pos : d1 ≥ 1 := by dsimp [d1]; omega
  have hd2_pos : d2 ≥ 1 := by dsimp [d2]; omega
  have hd1_le : d1 ≤ x0 := Nat.min_le_left _ _
  have hd2_le : d2 ≤ x2 := Nat.min_le_right _ _
  obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_le hd1_le
  obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le hd2_le
  have hconc : d2 * c5Q (x0 - d1) x1 (x2 + d1) x3 x4 +
               d1 * c5Q (x0 + d2) x1 (x2 - d2) x3 x4 =
               (d1 + d2) * c5Q x0 x1 x2 x3 x4 := by
    have hx0 : x0 - d1 = a := by omega
    have hx2 : x2 - d2 = b := by omega
    rw [hx0, hx2, ha, hb]
    unfold c5Q
    have ht1 : d2 * (a * x1) + d1 * ((d1 + a + d2) * x1) = (d1 + d2) * ((d1 + a) * x1) := by
      simp only [Nat.add_mul, Nat.mul_add]
      have h1 : d1 * (d2 * x1) = d2 * (d1 * x1) := by rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_comm d1 d2]
      omega
    have ht2 : d2 * (x1 * (d2 + b + d1)) + d1 * (x1 * b) = (d1 + d2) * (x1 * (d2 + b)) := by
      simp only [Nat.add_mul, Nat.mul_add]
      have h1 : d2 * (x1 * d1) = d1 * (x1 * d2) := by
        rw [← Nat.mul_assoc, Nat.mul_comm d2 x1, Nat.mul_assoc, Nat.mul_comm d2 d1, ← Nat.mul_assoc, Nat.mul_comm x1 d1, Nat.mul_assoc]
      omega
    have ht3 : d2 * ((d2 + b + d1) * x3) + d1 * (b * x3) = (d1 + d2) * ((d2 + b) * x3) := by
      simp only [Nat.add_mul, Nat.mul_add]
      have h1 : d2 * (d1 * x3) = d1 * (d2 * x3) := by rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_comm d2 d1]
      omega
    have ht4 : d2 * (x3 * x4) + d1 * (x3 * x4) = (d1 + d2) * (x3 * x4) := by
      rw [Nat.add_mul, Nat.add_comm]
    have ht5 : d2 * (x4 * a) + d1 * (x4 * (d1 + a + d2)) = (d1 + d2) * (x4 * (d1 + a)) := by
      simp only [Nat.add_mul, Nat.mul_add]
      have h1 : d1 * (x4 * d2) = d2 * (x4 * d1) := by
        rw [← Nat.mul_assoc, Nat.mul_comm d1 x4, Nat.mul_assoc, Nat.mul_comm d1 d2, ← Nat.mul_assoc, Nat.mul_comm x4 d2, Nat.mul_assoc]
      omega
    have hdist : ∀ k p1 p2 p3 p4 p5 : Nat,
        k * (p1 + p2 + p3 + p4 + p5) = k * p1 + k * p2 + k * p3 + k * p4 + k * p5 := by
      intro k p1 p2 p3 p4 p5
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_add]
    rw [hdist d2, hdist d1, hdist (d1 + d2)]
    omega
  by_cases h : c5Q (x0 - d1) x1 (x2 + d1) x3 x4 ≤ c5Q x0 x1 x2 x3 x4
  · exact Or.inl h
  · right
    by_cases h2 : c5Q (x0 + d2) x1 (x2 - d2) x3 x4 ≤ c5Q x0 x1 x2 x3 x4
    · exact h2
    · exfalso
      have hlt1 : c5Q x0 x1 x2 x3 x4 + 1 ≤ c5Q (x0 - d1) x1 (x2 + d1) x3 x4 := by omega
      have hlt2 : c5Q x0 x1 x2 x3 x4 + 1 ≤ c5Q (x0 + d2) x1 (x2 - d2) x3 x4 := by omega
      have hm1 := Nat.mul_le_mul_left d2 hlt1
      have hm2 := Nat.mul_le_mul_left d1 hlt2
      have hsum : (d1 + d2) * (c5Q x0 x1 x2 x3 x4 + 1) =
                  d2 * (c5Q x0 x1 x2 x3 x4 + 1) + d1 * (c5Q x0 x1 x2 x3 x4 + 1) := by
        rw [Nat.add_mul, Nat.add_comm]
      have hstrict : (d1 + d2) * c5Q x0 x1 x2 x3 x4 + (d1 + d2) =
                     (d1 + d2) * (c5Q x0 x1 x2 x3 x4 + 1) := by rw [Nat.mul_succ]
      omega

def isInt (M x : Nat) : Nat := if 0 < x && x < M then 1 else 0

theorem isInt_le_one (M x : Nat) : isInt M x ≤ 1 := by
  unfold isInt; split <;> omega

theorem isInt_eq_zero_of_zero (M : Nat) : isInt M 0 = 0 := by
  unfold isInt; simp

theorem isInt_eq_zero_of_eq (M : Nat) : isInt M M = 0 := by
  unfold isInt; simp

theorem isInt_eq_one {M x : Nat} (h0 : 0 < x) (hM : x < M) : isInt M x = 1 := by
  unfold isInt; simp [h0, hM]

def intCnt (M x0 x1 x2 x3 x4 : Nat) : Nat :=
  isInt M x0 + isInt M x1 + isInt M x2 + isInt M x3 + isInt M x4

theorem c5Q_extreme (x0 x1 x2 x3 x4 M s : Nat)
    (h0 : x0 ≤ M) (h1 : x1 ≤ M) (h2 : x2 ≤ M) (h3 : x3 ≤ M) (h4 : x4 ≤ M)
    (hsum : x0 + x1 + x2 + x3 + x4 = s)
    (hlo : 2 * M ≤ s) (hhi : s ≤ 3 * M)
    (hext : intCnt M x0 x1 x2 x3 x4 ≤ 1) :
    c5Q x0 x1 x2 x3 x4 ≥ M * (s - 2 * M) := by
  -- Helper: if some coordinate is M and another non-adjacent or adjacent coordinate is M,
  -- then any remaining mass t = s - 2*M sits adjacent to at least one M.
  have hge_adj : ∀ a b c d e : Nat, a = M → b = M → a + b + c + d + e = s →
      c5Q a b c d e ≥ M * (s - 2 * M) := by
    intro a b c d e ha hb _
    unfold c5Q
    rw [ha, hb]
    have hle : s - 2 * M ≤ M := by omega
    have hmul := Nat.mul_le_mul_left M hle
    omega
  have hge_nonadj : ∀ a b c d e : Nat, a = M → c = M → a + b + c + d + e = s →
      c5Q a b c d e ≥ M * (s - 2 * M) := by
    intro a b c d e ha hc hs
    unfold c5Q
    rw [ha, hc]
    have ht : b + d + e = s - 2 * M := by omega
    have hmul : M * (b + d + e) = M * b + M * d + M * e := by
      simp only [Nat.mul_add]
    have hbm : M * b = M * b := rfl
    have hdm : M * d = M * d := rfl
    have hem : M * e = e * M := Nat.mul_comm M e
    rw [← ht, hmul]
    omega
  -- Check which of x0..x4 equal M; there must be at least 2 (otherwise sum < 2*M ≤ s).
  by_cases e0 : x0 = M
  · by_cases e1 : x1 = M
    · exact hge_adj x0 x1 x2 x3 x4 e0 e1 hsum
    · by_cases e2 : x2 = M
      · exact hge_nonadj x0 x1 x2 x3 x4 e0 e2 hsum
      · by_cases e3 : x3 = M
        · rw [c5Q_rot, c5Q_rot, c5Q_rot]
          exact hge_nonadj x3 x4 x0 x1 x2 e3 e0 (by omega)
        · by_cases e4 : x4 = M
          · rw [c5Q_rot, c5Q_rot, c5Q_rot, c5Q_rot]
            exact hge_adj x4 x0 x1 x2 x3 e4 e0 (by omega)
          · exfalso
            unfold intCnt isInt at hext
            have : x1 = 0 ∨ (0 < x1 ∧ x1 < M) := by omega
            have : x2 = 0 ∨ (0 < x2 ∧ x2 < M) := by omega
            have : x3 = 0 ∨ (0 < x3 ∧ x3 < M) := by omega
            have : x4 = 0 ∨ (0 < x4 ∧ x4 < M) := by omega
            rcases ‹x1 = 0 ∨ _› with h1' | ⟨_, _⟩ <;>
            rcases ‹x2 = 0 ∨ _› with h2' | ⟨_, _⟩ <;>
            rcases ‹x3 = 0 ∨ _› with h3' | ⟨_, _⟩ <;>
            rcases ‹x4 = 0 ∨ _› with h4' | ⟨_, _⟩ <;>
            simp_all <;> omega
  · by_cases e1 : x1 = M
    · by_cases e2 : x2 = M
      · rw [c5Q_rot]; exact hge_adj x1 x2 x3 x4 x0 e1 e2 (by omega)
      · by_cases e3 : x3 = M
        · rw [c5Q_rot]; exact hge_nonadj x1 x2 x3 x4 x0 e1 e3 (by omega)
        · by_cases e4 : x4 = M
          · rw [c5Q_rot, c5Q_rot, c5Q_rot, c5Q_rot]
            exact hge_nonadj x4 x0 x1 x2 x3 e4 e1 (by omega)
          · exfalso
            unfold intCnt isInt at hext
            have : x0 = 0 ∨ (0 < x0 ∧ x0 < M) := by omega
            have : x2 = 0 ∨ (0 < x2 ∧ x2 < M) := by omega
            have : x3 = 0 ∨ (0 < x3 ∧ x3 < M) := by omega
            have : x4 = 0 ∨ (0 < x4 ∧ x4 < M) := by omega
            rcases ‹x0 = 0 ∨ _› with h0' | ⟨_, _⟩ <;>
            rcases ‹x2 = 0 ∨ _› with h2' | ⟨_, _⟩ <;>
            rcases ‹x3 = 0 ∨ _› with h3' | ⟨_, _⟩ <;>
            rcases ‹x4 = 0 ∨ _› with h4' | ⟨_, _⟩ <;>
            simp_all <;> omega
    · by_cases e2 : x2 = M
      · by_cases e3 : x3 = M
        · rw [c5Q_rot, c5Q_rot]; exact hge_adj x2 x3 x4 x0 x1 e2 e3 (by omega)
        · by_cases e4 : x4 = M
          · rw [c5Q_rot, c5Q_rot]; exact hge_nonadj x2 x3 x4 x0 x1 e2 e4 (by omega)
          · exfalso
            unfold intCnt isInt at hext
            have : x0 = 0 ∨ (0 < x0 ∧ x0 < M) := by omega
            have : x1 = 0 ∨ (0 < x1 ∧ x1 < M) := by omega
            have : x3 = 0 ∨ (0 < x3 ∧ x3 < M) := by omega
            have : x4 = 0 ∨ (0 < x4 ∧ x4 < M) := by omega
            rcases ‹x0 = 0 ∨ _› with h0' | ⟨_, _⟩ <;>
            rcases ‹x1 = 0 ∨ _› with h1' | ⟨_, _⟩ <;>
            rcases ‹x3 = 0 ∨ _› with h3' | ⟨_, _⟩ <;>
            rcases ‹x4 = 0 ∨ _› with h4' | ⟨_, _⟩ <;>
            simp_all <;> omega
      · by_cases e3 : x3 = M
        · by_cases e4 : x4 = M
          · rw [c5Q_rot, c5Q_rot, c5Q_rot]; exact hge_adj x3 x4 x0 x1 x2 e3 e4 (by omega)
          · exfalso
            unfold intCnt isInt at hext
            have : x0 = 0 ∨ (0 < x0 ∧ x0 < M) := by omega
            have : x1 = 0 ∨ (0 < x1 ∧ x1 < M) := by omega
            have : x2 = 0 ∨ (0 < x2 ∧ x2 < M) := by omega
            have : x4 = 0 ∨ (0 < x4 ∧ x4 < M) := by omega
            rcases ‹x0 = 0 ∨ _› with h0' | ⟨_, _⟩ <;>
            rcases ‹x1 = 0 ∨ _› with h1' | ⟨_, _⟩ <;>
            rcases ‹x2 = 0 ∨ _› with h2' | ⟨_, _⟩ <;>
            rcases ‹x4 = 0 ∨ _› with h4' | ⟨_, _⟩ <;>
            simp_all <;> omega
        · exfalso
          -- At most x4 = M, so at most 1 coordinate equals M and at most 1 is interior
          unfold intCnt isInt at hext
          have : x0 = 0 ∨ (0 < x0 ∧ x0 < M) := by omega
          have : x1 = 0 ∨ (0 < x1 ∧ x1 < M) := by omega
          have : x2 = 0 ∨ (0 < x2 ∧ x2 < M) := by omega
          have : x3 = 0 ∨ (0 < x3 ∧ x3 < M) := by omega
          rcases ‹x0 = 0 ∨ _› with h0' | ⟨_, _⟩ <;>
          rcases ‹x1 = 0 ∨ _› with h1' | ⟨_, _⟩ <;>
          rcases ‹x2 = 0 ∨ _› with h2' | ⟨_, _⟩ <;>
          rcases ‹x3 = 0 ∨ _› with h3' | ⟨_, _⟩ <;>
          simp_all <;> omega

theorem c5Q_min_aux (k : Nat) :
    ∀ x0 x1 x2 x3 x4 M s : Nat,
      intCnt M x0 x1 x2 x3 x4 ≤ k →
      x0 ≤ M → x1 ≤ M → x2 ≤ M → x3 ≤ M → x4 ≤ M →
      x0 + x1 + x2 + x3 + x4 = s →
      2 * M ≤ s → s ≤ 3 * M →
      c5Q x0 x1 x2 x3 x4 ≥ M * (s - 2 * M) := by
  induction k with
  | zero =>
    intro x0 x1 x2 x3 x4 M s hk h0 h1 h2 h3 h4 hsum hlo hhi
    exact c5Q_extreme x0 x1 x2 x3 x4 M s h0 h1 h2 h3 h4 hsum hlo hhi (by omega)
  | succ k ih =>
    intro x0 x1 x2 x3 x4 M s hk h0 h1 h2 h3 h4 hsum hlo hhi
    by_cases hext : intCnt M x0 x1 x2 x3 x4 ≤ 1
    · exact c5Q_extreme x0 x1 x2 x3 x4 M s h0 h1 h2 h3 h4 hsum hlo hhi hext
    · -- Helper to reduce an adjacent pair (a, b) with 0 < a < M and 0 < b < M
      have stepAdj : ∀ a b c d e : Nat,
          intCnt M a b c d e ≤ k + 1 →
          0 < a → a < M → 0 < b → b < M →
          c ≤ M → d ≤ M → e ≤ M →
          a + b + c + d + e = s →
          c5Q a b c d e ≥ M * (s - 2 * M) := by
        intro a b c d e hcnt ha0 haM hb0 hbM hc hd he hs
        have hsh := c5Q_shift_adj a b c d e M ha0 haM hb0 hbM
        dsimp only at hsh
        let d1 := min a (M - b)
        let d2 := min (M - a) b
        have hia := isInt_eq_one ha0 haM
        have hib := isInt_eq_one hb0 hbM
        rcases hsh with hleft | hright
        · have hcnt' : intCnt M (a - d1) (b + d1) c d e ≤ k := by
            unfold intCnt at hcnt ⊢
            have h1 := isInt_le_one M (a - d1)
            have h2 := isInt_le_one M (b + d1)
            have hor : a - d1 = 0 ∨ b + d1 = M := by dsimp [d1]; omega
            rcases hor with h' | h'
            · rw [h', isInt_eq_zero_of_zero]; omega
            · rw [h', isInt_eq_zero_of_eq]; omega
          have hih := ih (a - d1) (b + d1) c d e M s hcnt'
            (by dsimp [d1]; omega) (by dsimp [d1]; omega) hc hd he
            (by dsimp [d1]; omega) hlo hhi
          exact Nat.le_trans hih hleft
        · have hcnt' : intCnt M (a + d2) (b - d2) c d e ≤ k := by
            unfold intCnt at hcnt ⊢
            have h1 := isInt_le_one M (a + d2)
            have h2 := isInt_le_one M (b - d2)
            have hor : a + d2 = M ∨ b - d2 = 0 := by dsimp [d2]; omega
            rcases hor with h' | h'
            · rw [h', isInt_eq_zero_of_eq]; omega
            · rw [h', isInt_eq_zero_of_zero]; omega
          have hih := ih (a + d2) (b - d2) c d e M s hcnt'
            (by dsimp [d2]; omega) (by dsimp [d2]; omega) hc hd he
            (by dsimp [d2]; omega) hlo hhi
          exact Nat.le_trans hih hright
      have stepNonAdj : ∀ a b c d e : Nat,
          intCnt M a b c d e ≤ k + 1 →
          0 < a → a < M → 0 < c → c < M →
          b ≤ M → d ≤ M → e ≤ M →
          a + b + c + d + e = s →
          c5Q a b c d e ≥ M * (s - 2 * M) := by
        intro a b c d e hcnt ha0 haM hc0 hcM hb hd he hs
        have hsh := c5Q_shift_nonadj a b c d e M ha0 haM hc0 hcM
        dsimp only at hsh
        let d1 := min a (M - c)
        let d2 := min (M - a) c
        have hia := isInt_eq_one ha0 haM
        have hic := isInt_eq_one hc0 hcM
        rcases hsh with hleft | hright
        · have hcnt' : intCnt M (a - d1) b (c + d1) d e ≤ k := by
            unfold intCnt at hcnt ⊢
            have h1 := isInt_le_one M (a - d1)
            have h2 := isInt_le_one M (c + d1)
            have hor : a - d1 = 0 ∨ c + d1 = M := by dsimp [d1]; omega
            rcases hor with h' | h'
            · rw [h', isInt_eq_zero_of_zero]; omega
            · rw [h', isInt_eq_zero_of_eq]; omega
          have hih := ih (a - d1) b (c + d1) d e M s hcnt'
            (by dsimp [d1]; omega) hb (by dsimp [d1]; omega) hd he
            (by dsimp [d1]; omega) hlo hhi
          exact Nat.le_trans hih hleft
        · have hcnt' : intCnt M (a + d2) b (c - d2) d e ≤ k := by
            unfold intCnt at hcnt ⊢
            have h1 := isInt_le_one M (a + d2)
            have h2 := isInt_le_one M (c - d2)
            have hor : a + d2 = M ∨ c - d2 = 0 := by dsimp [d2]; omega
            rcases hor with h' | h'
            · rw [h', isInt_eq_zero_of_eq]; omega
            · rw [h', isInt_eq_zero_of_zero]; omega
          have hih := ih (a + d2) b (c - d2) d e M s hcnt'
            (by dsimp [d2]; omega) hb (by dsimp [d2]; omega) hd he
            (by dsimp [d2]; omega) hlo hhi
          exact Nat.le_trans hih hright
      have hrotCnt : ∀ a b c d e : Nat, intCnt M a b c d e = intCnt M b c d e a := by
        intro a b c d e; unfold intCnt; omega
      -- Since intCnt ≥ 2, find two interior coordinates!
      by_cases i0 : 0 < x0 ∧ x0 < M
      · by_cases i1 : 0 < x1 ∧ x1 < M
        · exact stepAdj x0 x1 x2 x3 x4 hk i0.1 i0.2 i1.1 i1.2 h2 h3 h4 hsum
        · by_cases i2 : 0 < x2 ∧ x2 < M
          · exact stepNonAdj x0 x1 x2 x3 x4 hk i0.1 i0.2 i2.1 i2.2 h1 h3 h4 hsum
          · by_cases i3 : 0 < x3 ∧ x3 < M
            · rw [c5Q_rot, c5Q_rot, c5Q_rot]
              exact stepNonAdj x3 x4 x0 x1 x2 (by rw [← hrotCnt, ← hrotCnt, ← hrotCnt]; exact hk)
                i3.1 i3.2 i0.1 i0.2 h4 h1 h2 (by omega)
            · by_cases i4 : 0 < x4 ∧ x4 < M
              · rw [c5Q_rot, c5Q_rot, c5Q_rot, c5Q_rot]
                exact stepAdj x4 x0 x1 x2 x3 (by rw [← hrotCnt, ← hrotCnt, ← hrotCnt, ← hrotCnt]; exact hk)
                  i4.1 i4.2 i0.1 i0.2 h1 h2 h3 (by omega)
              · exfalso; unfold intCnt isInt at hext; simp_all
      · by_cases i1 : 0 < x1 ∧ x1 < M
        · by_cases i2 : 0 < x2 ∧ x2 < M
          · rw [c5Q_rot]
            exact stepAdj x1 x2 x3 x4 x0 (by rw [← hrotCnt]; exact hk)
              i1.1 i1.2 i2.1 i2.2 h3 h4 h0 (by omega)
          · by_cases i3 : 0 < x3 ∧ x3 < M
            · rw [c5Q_rot]
              exact stepNonAdj x1 x2 x3 x4 x0 (by rw [← hrotCnt]; exact hk)
                i1.1 i1.2 i3.1 i3.2 h2 h4 h0 (by omega)
            · by_cases i4 : 0 < x4 ∧ x4 < M
              · rw [c5Q_rot, c5Q_rot, c5Q_rot, c5Q_rot]
                exact stepNonAdj x4 x0 x1 x2 x3 (by rw [← hrotCnt, ← hrotCnt, ← hrotCnt, ← hrotCnt]; exact hk)
                  i4.1 i4.2 i1.1 i1.2 h0 h2 h3 (by omega)
              · exfalso; unfold intCnt isInt at hext; simp_all
        · by_cases i2 : 0 < x2 ∧ x2 < M
          · by_cases i3 : 0 < x3 ∧ x3 < M
            · rw [c5Q_rot, c5Q_rot]
              exact stepAdj x2 x3 x4 x0 x1 (by rw [← hrotCnt, ← hrotCnt]; exact hk)
                i2.1 i2.2 i3.1 i3.2 h4 h0 h1 (by omega)
            · by_cases i4 : 0 < x4 ∧ x4 < M
              · rw [c5Q_rot, c5Q_rot]
                exact stepNonAdj x2 x3 x4 x0 x1 (by rw [← hrotCnt, ← hrotCnt]; exact hk)
                  i2.1 i2.2 i4.1 i4.2 h3 h0 h1 (by omega)
              · exfalso; unfold intCnt isInt at hext; simp_all
          · by_cases i3 : 0 < x3 ∧ x3 < M
            · by_cases i4 : 0 < x4 ∧ x4 < M
              · rw [c5Q_rot, c5Q_rot, c5Q_rot]
                exact stepAdj x3 x4 x0 x1 x2 (by rw [← hrotCnt, ← hrotCnt, ← hrotCnt]; exact hk)
                  i3.1 i3.2 i4.1 i4.2 h0 h1 h2 (by omega)
              · exfalso; unfold intCnt isInt at hext; simp_all
            · exfalso
              unfold intCnt isInt at hext
              have h4le : (if 0 < x4 && x4 < M then 1 else 0) ≤ 1 := by split <;> omega
              simp_all
              omega

theorem c5Q_min (x0 x1 x2 x3 x4 M s : Nat)
    (h0 : x0 ≤ M) (h1 : x1 ≤ M) (h2 : x2 ≤ M) (h3 : x3 ≤ M) (h4 : x4 ≤ M)
    (hsum : x0 + x1 + x2 + x3 + x4 = s)
    (hlo : 2 * M ≤ s) (hhi : s ≤ 3 * M) :
    c5Q x0 x1 x2 x3 x4 ≥ M * (s - 2 * M) :=
  c5Q_min_aux (intCnt M x0 x1 x2 x3 x4) x0 x1 x2 x3 x4 M s (Nat.le_refl _) h0 h1 h2 h3 h4 hsum hlo hhi

/-! ### Explicit Single-Graph Counterexample `witnessGraph r` for `r = 7, 9` and `r ≥ 11` -/

def c5Adj (a b : Nat) : Bool :=
  (a + 1) % 5 == b % 5 || (b + 1) % 5 == a % 5

theorem c5Adj_symm (a b : Nat) : c5Adj a b = c5Adj b a := by
  unfold c5Adj; exact Bool.or_comm _ _

theorem c5Adj_irrefl (a : Nat) : c5Adj a a = false := by
  unfold c5Adj; simp; omega

theorem c5Adj_triangle_free (a b c : Nat)
    (hab : c5Adj a b = true) (hbc : c5Adj b c = true) (hac : c5Adj a c = true) : False := by
  unfold c5Adj at hab hbc hac
  simp only [Bool.or_eq_true, beq_iff_eq] at hab hbc hac
  omega

def witnessGraph (r : Nat) : SGraph (r * r + 1) where
  adj u v :=
    if u.val < 2 * r + 1 && v.val < 2 * r + 1 then
      decide (u ≠ v) && !c5Adj u.val v.val
    else if u.val ≥ 2 * r + 1 && v.val ≥ 2 * r + 1 then
      decide (u ≠ v) && decide ((u.val - (2 * r + 1)) / r = (v.val - (2 * r + 1)) / r)
    else
      false
  symm u v := by
    by_cases hu : u.val < 2 * r + 1 <;> by_cases hv : v.val < 2 * r + 1
    · simp only [hu, hv, decide_true, Bool.and_true, ↓reduceIte]
      rw [c5Adj_symm u.val v.val]
      by_cases heq : u = v
      · subst heq; simp
      · have heq' : v ≠ u := Ne.symm heq
        simp [heq, heq']
    · have hv' : v.val ≥ 2 * r + 1 := by omega
      have hu' : ¬ (u.val ≥ 2 * r + 1) := by omega
      simp [hu, hv, hu', hv']
    · have hu' : u.val ≥ 2 * r + 1 := by omega
      have hv' : ¬ (v.val ≥ 2 * r + 1) := by omega
      simp [hu, hv, hu', hv']
    · have hu' : u.val ≥ 2 * r + 1 := by omega
      have hv' : v.val ≥ 2 * r + 1 := by omega
      simp only [hu, hv, hu', hv', decide_false, decide_true, Bool.and_false, Bool.and_true,
                 Bool.false_eq_true, ↓reduceIte]
      by_cases heq : u = v
      · subst heq; simp
      · have heq' : v ≠ u := Ne.symm heq
        simp [heq, heq', eq_comm]
  loopless u := by
    by_cases hu : u.val < 2 * r + 1
    · simp [hu]
    · have hu' : u.val ≥ 2 * r + 1 := by omega
      simp [hu, hu']

def wComp (r : Nat) (hr : r ≥ 3) (v : Fin (r * r + 1)) : Fin (r - 1) :=
  if h : v.val < 2 * r + 1 then
    ⟨0, by omega⟩
  else
    ⟨1 + (v.val - (2 * r + 1)) / r, by
      have hv : v.val < r * r + 1 := v.isLt
      have hsub : v.val - (2 * r + 1) < r * (r - 2) := by
        have hmul : (r - 2) * r + 2 * r = r * r := by
          have : (r - 2) + 2 = r := by omega
          rw [← Nat.add_mul, this]
        have hc : r * (r - 2) = (r - 2) * r := Nat.mul_comm _ _
        omega
      have hdiv : (v.val - (2 * r + 1)) / r < r - 2 :=
        Nat.div_lt_of_lt_mul hsub
      omega⟩

theorem wComp_eq_zero_iff (r : Nat) (hr : r ≥ 3) (v : Fin (r * r + 1)) :
    (wComp r hr v).val = 0 ↔ v.val < 2 * r + 1 := by
  unfold wComp
  by_cases hv : v.val < 2 * r + 1
  · simp [hv]
  · simp only [hv, ↓reduceDIte, iff_false]
    intro h
    have h1 : 1 + (v.val - (2 * r + 1)) / r = 0 := h
    exact Nat.succ_ne_zero ((v.val - (2 * r + 1)) / r) (by rw [Nat.succ_eq_add_one, Nat.add_comm]; exact h1)

theorem witnessGraph_disj (r : Nat) (hr : r ≥ 3) (u v : Fin (r * r + 1))
    (hadj : (witnessGraph r).adj u v = true) : wComp r hr u = wComp r hr v := by
  unfold witnessGraph at hadj
  dsimp only at hadj
  unfold wComp
  by_cases hu : u.val < 2 * r + 1 <;> by_cases hv : v.val < 2 * r + 1
  · simp [hu, hv]
  · simp [hu, hv, (show ¬ (u.val ≥ 2 * r + 1) by omega)] at hadj
  · simp [hu, hv, (show ¬ (v.val ≥ 2 * r + 1) by omega)] at hadj
  · have hu' : u.val ≥ 2 * r + 1 := by omega
    have hv' : v.val ≥ 2 * r + 1 := by omega
    simp only [hu, hv, hu', hv', decide_false, decide_true, Bool.and_false, Bool.and_true,
               Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hadj
    simp only [hu, hv, ↓reduceDIte, Fin.mk.injEq]
    omega

/-! ### Counting Residues and Ranges on `Fin n` -/

theorem length_filter_range_fin {n : Nat} (a b : Nat) (hab : a ≤ b) (hbn : b ≤ n) :
    ((verts n).filter (fun v => decide (a ≤ v.val ∧ v.val < b))).length = b - a := by
  -- Use bijection with List.range via List.finRange_eq_pmap_range / direct induction on b - a
  have aux : ∀ k : Nat, ∀ a : Nat, a + k ≤ n →
      ((verts n).filter (fun v => decide (a ≤ v.val ∧ v.val < a + k))).length = k := by
    intro k
    induction k with
    | zero =>
      intro a _
      have h0 : ((verts n).filter (fun v => decide (a ≤ v.val ∧ v.val < a + 0))).length =
                ((verts n).filter (fun _ => false)).length := by
        apply filter_length_eq; intro v _; simp
      rw [h0]
      simp
    | succ k ih =>
      intro a hak
      let x : Fin n := ⟨a + k, by omega⟩
      have hp := filter_length_partition (verts n)
        (fun v => decide (a ≤ v.val ∧ v.val < a + (k + 1))) (fun v => decide (v = x))
      have h1 : ((verts n).filter (fun v => decide (a ≤ v.val ∧ v.val < a + (k + 1)) && decide (v = x))).length = 1 := by
        have heq : ((verts n).filter (fun v => decide (a ≤ v.val ∧ v.val < a + (k + 1)) && decide (v = x))).length =
                   ((verts n).filter (fun v => decide (v = x))).length := by
          apply filter_length_eq; intro v _
          by_cases hv : v = x
          · subst hv; simp [x]
          · simp [hv]
        rw [heq]
        exact length_filter_eq_one_of_nodup (verts n) (nodup_verts n) x (mem_verts x)
      have h2 : ((verts n).filter (fun v => decide (a ≤ v.val ∧ v.val < a + (k + 1)) && !decide (v = x))).length =
                ((verts n).filter (fun v => decide (a ≤ v.val ∧ v.val < a + k))).length := by
        apply filter_length_eq; intro v _
        by_cases hv : v = x
        · subst hv; simp [x]
        · have hvne : v.val ≠ a + k := fun heq => hv (Fin.ext heq)
          by_cases h1' : a ≤ v.val ∧ v.val < a + k
          · have h2' : a ≤ v.val ∧ v.val < a + (k + 1) := by omega
            simp [hv, h1', h2']
          · have h2' : ¬ (a ≤ v.val ∧ v.val < a + (k + 1)) := by omega
            simp [hv, h1', h2']
      have hih := ih a (by omega)
      omega
  have := aux (b - a) a (by omega)
  have heq : a + (b - a) = b := by omega
  rw [heq] at this
  exact this

theorem count_mod5_lt {n : Nat} (m i : Nat) (hm : m ≤ n) (hi : i < 5) :
    ((verts n).filter (fun v => decide (v.val < m) && decide (v.val % 5 = i))).length =
    m / 5 + if i < m % 5 then 1 else 0 := by
  induction m with
  | zero =>
    have h0 : ((verts n).filter (fun v => decide (v.val < 0) && decide (v.val % 5 = i))).length =
              ((verts n).filter (fun _ => false)).length := by
      apply filter_length_eq; intro v _; simp
    rw [h0]; simp
  | succ m ih =>
    let x : Fin n := ⟨m, by omega⟩
    have hp := filter_length_partition (verts n)
      (fun v => decide (v.val < m + 1) && decide (v.val % 5 = i)) (fun v => decide (v = x))
    have h2 : ((verts n).filter (fun v => (decide (v.val < m + 1) && decide (v.val % 5 = i)) && !decide (v = x))).length =
              ((verts n).filter (fun v => decide (v.val < m) && decide (v.val % 5 = i))).length := by
      apply filter_length_eq; intro v _
      by_cases hv : v = x
      · subst hv; simp [x]
      · have hvne : v.val ≠ m := fun heq => hv (Fin.ext heq)
        by_cases hlt : v.val < m
        · have hlt' : v.val < m + 1 := by omega
          simp [hv, hlt, hlt']
        · have hlt' : ¬ (v.val < m + 1) := by omega
          simp [hv, hlt, hlt']
    have hih := ih (by omega)
    by_cases hmi : m % 5 = i
    · have h1 : ((verts n).filter (fun v => (decide (v.val < m + 1) && decide (v.val % 5 = i)) && decide (v = x))).length = 1 := by
        have heq : ((verts n).filter (fun v => (decide (v.val < m + 1) && decide (v.val % 5 = i)) && decide (v = x))).length =
                   ((verts n).filter (fun v => decide (v = x))).length := by
          apply filter_length_eq; intro v _
          by_cases hv : v = x
          · subst hv; simp [x, hmi]
          · simp [hv]
        rw [heq]
        exact length_filter_eq_one_of_nodup (verts n) (nodup_verts n) x (mem_verts x)
      rw [hp, h1, h2, hih]
      split <;> split <;> omega
    · have h1 : ((verts n).filter (fun v => (decide (v.val < m + 1) && decide (v.val % 5 = i)) && decide (v = x))).length = 0 := by
        have heq : ((verts n).filter (fun v => (decide (v.val < m + 1) && decide (v.val % 5 = i)) && decide (v = x))).length =
                   ((verts n).filter (fun _ => false)).length := by
          apply filter_length_eq; intro v _
          by_cases hv : v = x
          · subst hv; simp [x, hmi]
          · simp [hv]
        rw [heq]; simp
      rw [hp, h1, h2, hih]
      split <;> split <;> omega

/-! ### Exact Edge Count of `witnessGraph r` inside `V(H)` -/

theorem twoEdgesIn_witness_H_compl (r : Nat) (S : Fin (r * r + 1) → Bool)
    (hS : ∀ v, S v = true → v.val < 2 * r + 1) :
    let x := fun i : Nat => subsetCard (fun v => S v && decide (v.val % 5 = i))
    twoEdgesIn (witnessGraph r).compl S = 2 * c5Q (x 0) (x 1) (x 2) (x 3) (x 4) := by
  intro x
  rw [twoEdgesIn_eq_double_sum]
  -- Helper: count pairs (u, v) in S with u % 5 = a and v % 5 = b equals x a * x b
  have hprod : ∀ a b : Nat,
      ((verts (r * r + 1)).map (fun u => ((verts (r * r + 1)).map (fun v =>
        if S u && decide (u.val % 5 = a) && (S v && decide (v.val % 5 = b)) then 1 else 0)).sum)).sum =
      x a * x b := by
    intro a b
    have hinner : ∀ u ∈ verts (r * r + 1),
        ((verts (r * r + 1)).map (fun v =>
          if S u && decide (u.val % 5 = a) && (S v && decide (v.val % 5 = b)) then 1 else 0)).sum =
        if S u && decide (u.val % 5 = a) then x b else 0 := by
      intro u _
      cases hu : (S u && decide (u.val % 5 = a))
      · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        rw [sum_map_const, Nat.mul_zero]
      · simp only [Bool.true_and, ↓reduceIte]
        dsimp [x, subsetCard]
        rw [length_filter_eq_sum]
    rw [sum_map_eq (verts (r * r + 1)) _ _ hinner]
    rw [← sum_filter_eq_sum_ite, sum_map_const]
    rfl
  -- For u, v in S, (witnessGraph r).compl.adj u v = c5Adj u.val v.val
  have hadj_eq : ∀ u v : Fin (r * r + 1), S u = true → S v = true →
      (witnessGraph r).compl.adj u v = c5Adj u.val v.val := by
    intro u v hSu hSv
    have hu := hS u hSu
    have hv := hS v hSv
    unfold SGraph.compl witnessGraph
    simp only [hu, hv, decide_true, Bool.and_true, ↓reduceIte]
    by_cases huv : u = v
    · subst huv; simp [c5Adj_irrefl]
    · simp [huv]
  -- Pointwise decomposition of `if S u && S v && c5Adj u.val v.val then 1 else 0` into 10 residue pairs
  have hpt : ∀ u v : Fin (r * r + 1),
      (if S u && S v && (witnessGraph r).compl.adj u v then 1 else 0) =
      (if S u && decide (u.val % 5 = 0) && (S v && decide (v.val % 5 = 1)) then 1 else 0) +
      (if S u && decide (u.val % 5 = 1) && (S v && decide (v.val % 5 = 0)) then 1 else 0) +
      (if S u && decide (u.val % 5 = 1) && (S v && decide (v.val % 5 = 2)) then 1 else 0) +
      (if S u && decide (u.val % 5 = 2) && (S v && decide (v.val % 5 = 1)) then 1 else 0) +
      (if S u && decide (u.val % 5 = 2) && (S v && decide (v.val % 5 = 3)) then 1 else 0) +
      (if S u && decide (u.val % 5 = 3) && (S v && decide (v.val % 5 = 2)) then 1 else 0) +
      (if S u && decide (u.val % 5 = 3) && (S v && decide (v.val % 5 = 4)) then 1 else 0) +
      (if S u && decide (u.val % 5 = 4) && (S v && decide (v.val % 5 = 3)) then 1 else 0) +
      (if S u && decide (u.val % 5 = 4) && (S v && decide (v.val % 5 = 0)) then 1 else 0) +
      (if S u && decide (u.val % 5 = 0) && (S v && decide (v.val % 5 = 4)) then 1 else 0) := by
    intro u v
    cases hSu : S u
    · simp
    · cases hSv : S v
      · simp
      · rw [hadj_eq u v hSu hSv]
        simp only [Bool.true_and]
        unfold c5Adj
        have hu5 : u.val % 5 < 5 := Nat.mod_lt _ (by omega)
        have hv5 : v.val % 5 < 5 := Nat.mod_lt _ (by omega)
        have h1 : (u.val + 1) % 5 = (u.val % 5 + 1) % 5 := by omega
        have h2 : (v.val + 1) % 5 = (v.val % 5 + 1) % 5 := by omega
        rw [h1, h2]
        have hfin : ∀ a b : Fin 5,
            (if ((a.val + 1) % 5 == b.val || (b.val + 1) % 5 == a.val) = true then 1 else 0) =
            (if decide (a.val = 0) && decide (b.val = 1) then 1 else 0) +
            (if decide (a.val = 1) && decide (b.val = 0) then 1 else 0) +
            (if decide (a.val = 1) && decide (b.val = 2) then 1 else 0) +
            (if decide (a.val = 2) && decide (b.val = 1) then 1 else 0) +
            (if decide (a.val = 2) && decide (b.val = 3) then 1 else 0) +
            (if decide (a.val = 3) && decide (b.val = 2) then 1 else 0) +
            (if decide (a.val = 3) && decide (b.val = 4) then 1 else 0) +
            (if decide (a.val = 4) && decide (b.val = 3) then 1 else 0) +
            (if decide (a.val = 4) && decide (b.val = 0) then 1 else 0) +
            (if decide (a.val = 0) && decide (b.val = 4) then 1 else 0) := by decide
        have hinst := hfin ⟨u.val % 5, hu5⟩ ⟨v.val % 5, hv5⟩
        simpa only [Nat.mod_eq_of_lt hu5, Nat.mod_eq_of_lt hv5] using hinst
  have hsum_eq :
      ((verts (r * r + 1)).map (fun u => ((verts (r * r + 1)).map (fun v =>
        if S u && S v && (witnessGraph r).compl.adj u v then 1 else 0)).sum)).sum =
      x 0 * x 1 + x 1 * x 0 + x 1 * x 2 + x 2 * x 1 + x 2 * x 3 +
      x 3 * x 2 + x 3 * x 4 + x 4 * x 3 + x 4 * x 0 + x 0 * x 4 := by
    have hstep := sum_map_eq (verts (r * r + 1))
      (fun u => ((verts (r * r + 1)).map (fun v =>
        if S u && S v && (witnessGraph r).compl.adj u v then 1 else 0)).sum)
      (fun u => ((verts (r * r + 1)).map (fun v =>
        (if S u && decide (u.val % 5 = 0) && (S v && decide (v.val % 5 = 1)) then 1 else 0) +
        (if S u && decide (u.val % 5 = 1) && (S v && decide (v.val % 5 = 0)) then 1 else 0) +
        (if S u && decide (u.val % 5 = 1) && (S v && decide (v.val % 5 = 2)) then 1 else 0) +
        (if S u && decide (u.val % 5 = 2) && (S v && decide (v.val % 5 = 1)) then 1 else 0) +
        (if S u && decide (u.val % 5 = 2) && (S v && decide (v.val % 5 = 3)) then 1 else 0) +
        (if S u && decide (u.val % 5 = 3) && (S v && decide (v.val % 5 = 2)) then 1 else 0) +
        (if S u && decide (u.val % 5 = 3) && (S v && decide (v.val % 5 = 4)) then 1 else 0) +
        (if S u && decide (u.val % 5 = 4) && (S v && decide (v.val % 5 = 3)) then 1 else 0) +
        (if S u && decide (u.val % 5 = 4) && (S v && decide (v.val % 5 = 0)) then 1 else 0) +
        (if S u && decide (u.val % 5 = 0) && (S v && decide (v.val % 5 = 4)) then 1 else 0))).sum)
      (fun u _ => sum_map_eq (verts (r * r + 1)) _ _ (fun v _ => hpt u v))
    rw [hstep]
    simp only [sum_map_add, hprod]
  rw [hsum_eq]
  unfold c5Q
  have c01 := Nat.mul_comm (x 1) (x 0)
  have c12 := Nat.mul_comm (x 2) (x 1)
  have c23 := Nat.mul_comm (x 3) (x 2)
  have c34 := Nat.mul_comm (x 4) (x 3)
  have c40 := Nat.mul_comm (x 0) (x 4)
  omega

theorem subsetCard_mod5_sum {n : Nat} (S : Fin n → Bool) :
    subsetCard (fun v => S v && decide (v.val % 5 = 0)) +
    subsetCard (fun v => S v && decide (v.val % 5 = 1)) +
    subsetCard (fun v => S v && decide (v.val % 5 = 2)) +
    subsetCard (fun v => S v && decide (v.val % 5 = 3)) +
    subsetCard (fun v => S v && decide (v.val % 5 = 4)) = subsetCard S := by
  have h := subsetCard_partition_fin S (fun v : Fin n => (⟨v.val % 5, Nat.mod_lt _ (by omega)⟩ : Fin 5))
  have h5 : verts 5 = [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩] := by decide
  rw [h5] at h
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at h
  have heq : ∀ (i : Nat) (hi : i < 5),
      subsetCard (fun v => S v && decide ((⟨v.val % 5, Nat.mod_lt _ (by omega)⟩ : Fin 5) = ⟨i, hi⟩)) =
      subsetCard (fun v => S v && decide (v.val % 5 = i)) := by
    intro i hi
    unfold subsetCard
    apply filter_length_eq; intro v _
    simp [Fin.ext_iff]
  rw [heq 0 (by omega), heq 1 (by omega), heq 2 (by omega), heq 3 (by omega), heq 4 (by omega)] at h
  omega

theorem witness_comp_card (r : Nat) (hr : r ≥ 3) (j : Fin (r - 1)) :
    subsetCard (fun v => decide (wComp r hr v = j)) =
    if j.val = 0 then 2 * r + 1 else r := by
  unfold subsetCard
  by_cases hj : j.val = 0
  · simp only [hj, ↓reduceIte]
    have heq : ((verts (r * r + 1)).filter (fun v => decide (wComp r hr v = j))).length =
               ((verts (r * r + 1)).filter (fun v => decide (0 ≤ v.val ∧ v.val < 2 * r + 1))).length := by
      apply filter_length_eq; intro v _
      by_cases hv : v.val < 2 * r + 1
      · unfold wComp
        have hj0 : (⟨0, by omega⟩ : Fin (r - 1)) = j := Fin.ext (by simp [hj])
        simp [hv, hj0]
      · have hne : wComp r hr v ≠ j := by
          intro h
          have hv0 : (wComp r hr v).val = 0 := by rw [h, hj]
          exact hv ((wComp_eq_zero_iff r hr v).mp hv0)
        rw [decide_eq_false hne, decide_eq_false (by omega)]
    rw [heq]
    have h2r : 2 * r + 1 ≤ r * r + 1 := by
      have : 2 * r ≤ r * r := Nat.mul_le_mul_right r (by omega)
      omega
    have := length_filter_range_fin (n := r * r + 1) 0 (2 * r + 1) (by omega) h2r
    omega
  · simp only [hj, ↓reduceIte]
    let a := 2 * r + 1 + (j.val - 1) * r
    let b := 2 * r + 1 + j.val * r
    have hmul_j : (j.val - 1) * r + r = j.val * r := by
      have h1 : j.val - 1 + 1 = j.val := by omega
      calc (j.val - 1) * r + r = (j.val - 1) * r + 1 * r := by rw [Nat.one_mul]
        _ = (j.val - 1 + 1) * r := (Nat.add_mul _ _ _).symm
        _ = j.val * r := by rw [h1]
    have hbn : b ≤ r * r + 1 := by
      have hj1 : j.val ≤ r - 2 := by omega
      have hmul : j.val * r ≤ (r - 2) * r := Nat.mul_le_mul_right r hj1
      have htot : (r - 2) * r + 2 * r = r * r := by
        have : (r - 2) + 2 = r := by omega
        rw [← Nat.add_mul, this]
      dsimp [b]; omega
    have hab : a ≤ b := by dsimp [a, b]; omega
    have hba : b - a = r := by dsimp [a, b]; omega
    have heq : ((verts (r * r + 1)).filter (fun v => decide (wComp r hr v = j))).length =
               ((verts (r * r + 1)).filter (fun v => decide (a ≤ v.val ∧ v.val < b))).length := by
      apply filter_length_eq; intro v _
      by_cases hv : v.val < 2 * r + 1
      · unfold wComp
        have hne : (⟨0, by omega⟩ : Fin (r - 1)) ≠ j := by
          intro h; have := congrArg Fin.val h; dsimp at this; omega
        have hnot : ¬ (a ≤ v.val ∧ v.val < b) := by dsimp [a, b]; omega
        simp [hv, hne, hnot]
      · have hval : (wComp r hr v).val = 1 + (v.val - (2 * r + 1)) / r := by
          unfold wComp; simp [hv]
        have hiff : (wComp r hr v).val = j.val ↔ a ≤ v.val ∧ v.val < b := by
          rw [hval]
          constructor
          · intro h
            have hq : (v.val - (2 * r + 1)) / r = j.val - 1 := by omega
            have hdm := Nat.div_add_mod (v.val - (2 * r + 1)) r
            have hmlt := Nat.mod_lt (v.val - (2 * r + 1)) (by omega : 0 < r)
            have hcomm : r * (j.val - 1) = (j.val - 1) * r := Nat.mul_comm _ _
            rw [hq, hcomm] at hdm
            dsimp [a, b]; omega
          · intro ⟨hla, hlb⟩
            have hlo : (j.val - 1) * r ≤ v.val - (2 * r + 1) := by dsimp [a] at hla; omega
            have hdiv1 : j.val - 1 ≤ (v.val - (2 * r + 1)) / r := by
              rw [Nat.le_div_iff_mul_le (by omega)]; exact hlo
            have hdiv2 : (v.val - (2 * r + 1)) / r < j.val := by
              rw [Nat.div_lt_iff_lt_mul (by omega)]; dsimp [b] at hlb; omega
            omega
        by_cases hcond : a ≤ v.val ∧ v.val < b
        · have heq' : wComp r hr v = j := Fin.ext (hiff.mpr hcond)
          rw [decide_eq_true heq', decide_eq_true hcond]
        · have hne' : wComp r hr v ≠ j := fun h => hcond (hiff.mp (congrArg Fin.val h))
          rw [decide_eq_false hne', decide_eq_false hcond]
    rw [heq, length_filter_range_fin a b hab hbn, hba]

theorem c5Q_balanced_lb (q t : Nat) (ht : t < 5) :
    5 * c5Q (q + if 0 < t then 1 else 0) (q + if 1 < t then 1 else 0)
            (q + if 2 < t then 1 else 0) (q + if 3 < t then 1 else 0)
            (q + if 4 < t then 1 else 0) + 1 ≥ (5 * q + t) * (5 * q + t) := by
  have h5q : 5 * q * (5 * q) = 25 * (q * q) := by
    rw [Nat.mul_assoc 5 q (5 * q), ← Nat.mul_assoc q 5 q, Nat.mul_comm q 5,
        Nat.mul_assoc 5 q q, ← Nat.mul_assoc 5 5 (q * q)]
  have h5q1 : 5 * q * 1 = 5 * q := Nat.mul_one _
  have h5q2 : 5 * q * 2 = 10 * q := by rw [Nat.mul_assoc, Nat.mul_comm q 2, ← Nat.mul_assoc]
  have h5q3 : 5 * q * 3 = 15 * q := by rw [Nat.mul_assoc, Nat.mul_comm q 3, ← Nat.mul_assoc]
  have h5q4 : 5 * q * 4 = 20 * q := by rw [Nat.mul_assoc, Nat.mul_comm q 4, ← Nat.mul_assoc]
  have h15q : 1 * (5 * q) = 5 * q := Nat.one_mul _
  have h25q : 2 * (5 * q) = 10 * q := by rw [← Nat.mul_assoc]
  have h35q : 3 * (5 * q) = 15 * q := by rw [← Nat.mul_assoc]
  have h45q : 4 * (5 * q) = 20 * q := by rw [← Nat.mul_assoc]
  match t, ht with
  | 0, _ =>
    simp [c5Q, Nat.mul_add]; omega
  | 1, _ =>
    simp [c5Q, Nat.add_mul, Nat.mul_add]; omega
  | 2, _ =>
    simp [c5Q, Nat.add_mul, Nat.mul_add]; omega
  | 3, _ =>
    simp [c5Q, Nat.add_mul, Nat.mul_add]; omega
  | 4, _ =>
    simp [c5Q, Nat.add_mul, Nat.mul_add]; omega

theorem witness_edges_le (r : Nat) (hr : r ≥ 3) :
    edges (witnessGraph r) ≤ r * (r * r + 1) / 2 := by
  have h2e : twoEdges (witnessGraph r) ≤ r * (r * r + 1) := by
    unfold twoEdges
    rw [twoEdgesIn_partition_fin (witnessGraph r) (fun _ => true) (wComp r hr) (witnessGraph_disj r hr)]
    -- Separate j = 0 (H) and j > 0 (r - 2 cliques of size r)
    have hsplit :
        ((verts (r - 1)).map (fun j => twoEdgesIn (witnessGraph r) (fun v => true && decide (wComp r hr v = j)))).sum =
        twoEdgesIn (witnessGraph r) (fun v => decide (wComp r hr v = ⟨0, by omega⟩)) +
        ((verts (r - 1)).map (fun j =>
          if j.val = 0 then 0 else twoEdgesIn (witnessGraph r) (fun v => decide (wComp r hr v = j)))).sum := by
      have h1 : ∀ j ∈ verts (r - 1),
          twoEdgesIn (witnessGraph r) (fun v => true && decide (wComp r hr v = j)) =
          (if j = ⟨0, by omega⟩ then twoEdgesIn (witnessGraph r) (fun v => decide (wComp r hr v = ⟨0, by omega⟩)) else 0) +
          (if j.val = 0 then 0 else twoEdgesIn (witnessGraph r) (fun v => decide (wComp r hr v = j))) := by
        intro j _
        by_cases hj : j.val = 0
        · have hj0 : j = ⟨0, by omega⟩ := Fin.ext hj
          rw [hj0]; simp
        · have hjne : j ≠ ⟨0, by omega⟩ := fun h => hj (congrArg Fin.val h)
          simp [hj, hjne]
      rw [sum_map_eq (verts (r - 1)) _ _ h1, sum_map_add]
      have hzero :
          ((verts (r - 1)).map (fun j =>
            if j = ⟨0, by omega⟩ then twoEdgesIn (witnessGraph r) (fun v => decide (wComp r hr v = ⟨0, by omega⟩)) else 0)).sum =
          twoEdgesIn (witnessGraph r) (fun v => decide (wComp r hr v = ⟨0, by omega⟩)) := by
        have hrew : ((verts (r - 1)).map (fun j =>
            if j = ⟨0, by omega⟩ then twoEdgesIn (witnessGraph r) (fun v => decide (wComp r hr v = ⟨0, by omega⟩)) else 0)).sum =
            ((verts (r - 1)).map (fun j =>
            if decide (j = ⟨0, by omega⟩) then twoEdgesIn (witnessGraph r) (fun v => decide (wComp r hr v = ⟨0, by omega⟩)) else 0)).sum := by
          apply sum_map_eq; intro j _; simp
        rw [hrew, ← sum_filter_eq_sum_ite, sum_map_const]
        have hlen := length_filter_eq_one_of_nodup (verts (r - 1)) (nodup_verts (r - 1)) ⟨0, by omega⟩ (mem_verts _)
        rw [hlen, Nat.one_mul]
      rw [hzero]
    rw [hsplit]
    -- Bound the clique components (j ≠ 0): each has size r, so twoEdgesIn ≤ r * (r - 1)
    have hclq : ((verts (r - 1)).map (fun j =>
        if j.val = 0 then 0 else twoEdgesIn (witnessGraph r) (fun v => decide (wComp r hr v = j)))).sum ≤
        (r - 2) * (r * (r - 1)) := by
      have hle := sum_map_le (verts (r - 1))
        (fun j => if j.val = 0 then 0 else twoEdgesIn (witnessGraph r) (fun v => decide (wComp r hr v = j)))
        (fun j => if j.val = 0 then 0 else r * (r - 1))
        (fun j _ => by
          by_cases hj : j.val = 0
          · simp [hj]
          · simp only [hj, ↓reduceIte]
            have hle' := twoEdgesIn_le_complete (witnessGraph r) (fun v => decide (wComp r hr v = j))
            rw [witness_comp_card r hr j] at hle'
            simp only [hj, ↓reduceIte] at hle'
            exact hle')
      have hconst : ((verts (r - 1)).map (fun j => if j.val = 0 then 0 else r * (r - 1))).sum =
          (r - 2) * (r * (r - 1)) := by
        have hrew : ((verts (r - 1)).map (fun j => if j.val = 0 then 0 else r * (r - 1))).sum =
            ((verts (r - 1)).map (fun j => if !(decide (j = ⟨0, by omega⟩)) then r * (r - 1) else 0)).sum := by
          apply sum_map_eq; intro j _
          by_cases hj : j.val = 0
          · have hj0 : j = ⟨0, by omega⟩ := Fin.ext hj; rw [hj0]; simp
          · have hjne : j ≠ ⟨0, by omega⟩ := fun h => hj (congrArg Fin.val h); simp [hj, hjne]
        rw [hrew, ← sum_filter_eq_sum_ite, sum_map_const]
        have hp := filter_length_partition (verts (r - 1)) (fun _ => true) (fun j => decide (j = ⟨0, by omega⟩))
        rw [filter_true_eq, length_verts] at hp
        have h1 : ((verts (r - 1)).filter (fun j => true && decide (j = ⟨0, by omega⟩))).length = 1 :=
          length_filter_eq_one_of_nodup (verts (r - 1)) (nodup_verts (r - 1)) ⟨0, by omega⟩ (mem_verts _)
        have h2 : ((verts (r - 1)).filter (fun j => true && !decide (j = ⟨0, by omega⟩))).length =
                  ((verts (r - 1)).filter (fun j => !decide (j = ⟨0, by omega⟩))).length := rfl
        have hcnt : ((verts (r - 1)).filter (fun j => !decide (j = ⟨0, by omega⟩))).length = r - 2 := by omega
        rw [hcnt]
      omega
    -- Bound the H component (j = 0): twoEdgesIn H + 2 * c5Q(a0..a4) = (2r+1)*(2r)
    let SH : Fin (r * r + 1) → Bool := fun v => decide (wComp r hr v = ⟨0, by omega⟩)
    have hSH_iff : ∀ v : Fin (r * r + 1), SH v = decide (v.val < 2 * r + 1) := by
      intro v
      dsimp [SH]
      by_cases hv : v.val < 2 * r + 1
      · unfold wComp; simp [hv]
      · have hne : wComp r hr v ≠ ⟨0, by omega⟩ := by
          intro h
          have hv0 : (wComp r hr v).val = 0 := congrArg Fin.val h
          exact hv ((wComp_eq_zero_iff r hr v).mp hv0)
        rw [decide_eq_false hne, decide_eq_false hv]
    have hSH_sub : ∀ v, SH v = true → v.val < 2 * r + 1 := by
      intro v hv; rw [hSH_iff] at hv; exact of_decide_eq_true hv
    have hHadd := twoEdgesIn_add_compl (witnessGraph r) SH
    have hHcard : subsetCard SH = 2 * r + 1 := by
      have := witness_comp_card r hr ⟨0, by omega⟩
      simpa [SH] using this
    rw [hHcard] at hHadd
    have hHc := twoEdgesIn_witness_H_compl r SH hSH_sub
    dsimp only at hHc
    -- Compute a_i = (2*r+1)/5 + (if i < (2*r+1)%5 then 1 else 0)
    have h2rn : 2 * r + 1 ≤ r * r + 1 := by
      have : 2 * r ≤ r * r := Nat.mul_le_mul_right r (by omega)
      omega
    have ha : ∀ i, i < 5 →
        subsetCard (fun v => SH v && decide (v.val % 5 = i)) =
        (2 * r + 1) / 5 + if i < (2 * r + 1) % 5 then 1 else 0 := by
      intro i hi
      unfold subsetCard
      have heq : ((verts (r * r + 1)).filter (fun v => SH v && decide (v.val % 5 = i))).length =
                 ((verts (r * r + 1)).filter (fun v => decide (v.val < 2 * r + 1) && decide (v.val % 5 = i))).length := by
        apply filter_length_eq; intro v _; rw [hSH_iff]
      rw [heq]
      exact count_mod5_lt (2 * r + 1) i h2rn hi
    rw [ha 0 (by omega), ha 1 (by omega), ha 2 (by omega), ha 3 (by omega), ha 4 (by omega)] at hHc
    -- Show 5 * c5Q(a0..a4) ≥ 4 * r * r + 4 * r, hence 2 * c5Q ≥ r * (r + 3)
    have hQlb : 2 * c5Q ((2 * r + 1) / 5 + if 0 < (2 * r + 1) % 5 then 1 else 0)
                        ((2 * r + 1) / 5 + if 1 < (2 * r + 1) % 5 then 1 else 0)
                        ((2 * r + 1) / 5 + if 2 < (2 * r + 1) % 5 then 1 else 0)
                        ((2 * r + 1) / 5 + if 3 < (2 * r + 1) % 5 then 1 else 0)
                        ((2 * r + 1) / 5 + if 4 < (2 * r + 1) % 5 then 1 else 0) ≥ r * (r + 3) := by
      let q := (2 * r + 1) / 5
      let t := (2 * r + 1) % 5
      have hqt : 5 * q + t = 2 * r + 1 := by dsimp [q, t]; omega
      have ht5 : t < 5 := Nat.mod_lt _ (by omega)
      have h5Q := c5Q_balanced_lb q t ht5
      rw [hqt] at h5Q
      have hexp1 : (2 * r + 1) * (2 * r + 1) = 4 * (r * r) + 4 * r + 1 := by
        simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
        have : 2 * r * (2 * r) = 4 * (r * r) := by
          rw [Nat.mul_assoc 2 r (2 * r), ← Nat.mul_assoc r 2 r, Nat.mul_comm r 2,
              Nat.mul_assoc 2 r r, ← Nat.mul_assoc 2 2 (r * r)]
        omega
      have hexp2 : r * (r + 3) = r * r + 3 * r := by rw [Nat.mul_add, Nat.mul_comm r 3]
      have h3r : 3 * (r * r) ≥ 7 * r := by
        have h1 : 3 * r ≤ r * r := Nat.mul_le_mul_right r hr
        omega
      dsimp [q, t] at h5Q
      omega
    -- Final sum: twoEdgesIn H + (r-2)*r*(r-1) ≤ r*(r*r + 1)
    have hHbound : twoEdgesIn (witnessGraph r) SH + r * (r + 3) ≤ (2 * r + 1) * (2 * r) := by
      have hsub : 2 * r + 1 - 1 = 2 * r := by omega
      rw [hsub] at hHadd
      omega
    have halg : (2 * r + 1) * (2 * r) + (r - 2) * (r * (r - 1)) = r * (r * r + 1) + r * (r + 3) := by
      have hr_aux : ∀ k : Nat, (2 * (k + 3) + 1) * (2 * (k + 3)) + (k + 1) * ((k + 3) * (k + 2)) =
          (k + 3) * ((k + 3) * (k + 3) + 1) + (k + 3) * (k + 3 + 3) := by
        intro k
        have hc : ∀ a b : Nat, a * b = b * a := Nat.mul_comm
        have ha' : ∀ a b c : Nat, a * b * c = a * (b * c) := Nat.mul_assoc
        simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
        have p1 : (2 * k) * (2 * k) = 4 * (k * k) := by rw [ha', ← ha' k 2 k, hc k 2, ha', ← ha' 2 2]
        have p3 : k * (k * 2) = 2 * (k * k) := by rw [hc k 2, ← ha', hc k 2, ha']
        have p4 : k * (3 * k) = 3 * (k * k) := by rw [← ha', hc k 3, ha']
        have p6 : 2 * k * 6 = 12 * k := by rw [ha', hc k 6, ← ha']
        have p7 : 6 * (2 * k) = 12 * k := by rw [← ha']
        have p8 : k * (3 * 2) = 6 * k := by rw [hc]
        have p9 : 3 * (k * 2) = 6 * k := by rw [hc k 2, ← ha']
        have p10 : 3 * (3 * k) = 9 * k := by rw [← ha']
        have p11 : k * (k * 3) = 3 * (k * k) := by rw [hc k 3, ← ha', hc k 3, ha']
        have p12 : 3 * (k * 3) = 9 * k := by rw [hc k 3, ← ha']
        have p13 : k * 2 = 2 * k := hc k 2
        have p14 : k * 3 = 3 * k := hc k 3
        have p15 : k * 6 = 6 * k := hc k 6
        omega
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hr
      have hk' : r = k + 3 := by omega
      have h1 : r - 2 = k + 1 := by omega
      have h2 : r - 1 = k + 2 := by omega
      rw [h1, h2, hk']
      exact hr_aux k
    have hHbound' : twoEdgesIn (witnessGraph r) (fun v => decide (wComp r hr v = ⟨0, by omega⟩)) + r * (r + 3) ≤
        (2 * r + 1) * (2 * r) := hHbound
    omega
  have := two_mul_edges (witnessGraph r)
  omega

/-- Any independent set in `witnessGraph r` has size at most `r`. -/
theorem witness_indep_le (r : Nat) (hr : r ≥ 3) (S : Fin (r * r + 1) → Bool)
    (hind : IsIndep (witnessGraph r) S) : subsetCard S ≤ r := by
  rw [← subsetCard_partition_fin S (wComp r hr)]
  -- Helper: if a predicate P on Fin n has subsetCard P ≥ 2, there exist u ≠ v with P u = true ∧ P v = true
  have exists_two : ∀ (P : Fin (r * r + 1) → Bool), subsetCard P ≥ 2 →
      ∃ u v, u ≠ v ∧ P u = true ∧ P v = true := by
    intro P hP
    unfold subsetCard at hP
    have hnd : ((verts (r * r + 1)).filter P).Nodup := nodup_filter P (nodup_verts _)
    match hfilt : (verts (r * r + 1)).filter P with
    | [] => simp [hfilt] at hP
    | [_] => simp [hfilt] at hP
    | u :: v :: rest =>
      rw [hfilt] at hnd
      rw [List.nodup_cons] at hnd
      have huv : u ≠ v := fun heq => hnd.1 (heq ▸ by simp)
      have hu : u ∈ (verts (r * r + 1)).filter P := by rw [hfilt]; simp
      have hv : v ∈ (verts (r * r + 1)).filter P := by rw [hfilt]; simp
      exact ⟨u, v, huv, (List.mem_filter.mp hu).2, (List.mem_filter.mp hv).2⟩
  have exists_three : ∀ (P : Fin (r * r + 1) → Bool), subsetCard P ≥ 3 →
      ∃ u v w, u ≠ v ∧ v ≠ w ∧ u ≠ w ∧ P u = true ∧ P v = true ∧ P w = true := by
    intro P hP
    unfold subsetCard at hP
    have hnd : ((verts (r * r + 1)).filter P).Nodup := nodup_filter P (nodup_verts _)
    match hfilt : (verts (r * r + 1)).filter P with
    | [] => simp [hfilt] at hP
    | [_] => simp [hfilt] at hP
    | [_, _] => simp [hfilt] at hP
    | u :: v :: w :: rest =>
      rw [hfilt] at hnd
      rw [List.nodup_cons] at hnd
      have hnd2 := hnd.2
      rw [List.nodup_cons] at hnd2
      have huv : u ≠ v := fun heq => hnd.1 (heq ▸ by simp)
      have huw : u ≠ w := fun heq => hnd.1 (heq ▸ by simp)
      have hvw : v ≠ w := fun heq => hnd2.1 (heq ▸ by simp)
      have hu : u ∈ (verts (r * r + 1)).filter P := by rw [hfilt]; simp
      have hv : v ∈ (verts (r * r + 1)).filter P := by rw [hfilt]; simp
      have hw : w ∈ (verts (r * r + 1)).filter P := by rw [hfilt]; simp
      exact ⟨u, v, w, huv, hvw, huw, (List.mem_filter.mp hu).2, (List.mem_filter.mp hv).2, (List.mem_filter.mp hw).2⟩
  -- Each component j gets ≤ (if j.val = 0 then 2 else 1) vertices of S
  have hcomp_le : ∀ j ∈ verts (r - 1),
      subsetCard (fun v => S v && decide (wComp r hr v = j)) ≤ if j.val = 0 then 2 else 1 := by
    intro j _
    by_cases hj : j.val = 0
    · simp only [hj, ↓reduceIte]
      by_cases h3 : subsetCard (fun v => S v && decide (wComp r hr v = j)) ≥ 3
      · exfalso
        obtain ⟨u, v, w, huv, hvw, huw, hu, hv, hw⟩ := exists_three _ h3
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hu hv hw
        have hlt : ∀ x : Fin (r * r + 1), wComp r hr x = j → x.val < 2 * r + 1 := by
          intro x hx
          exact (wComp_eq_zero_iff r hr x).mp (by rw [hx, hj])
        have hult := hlt u hu.2; have hvlt := hlt v hv.2; have hwlt := hlt w hw.2
        have hnon : ∀ a b : Fin (r * r + 1), S a = true → S b = true → a ≠ b →
            a.val < 2 * r + 1 → b.val < 2 * r + 1 → c5Adj a.val b.val = true := by
          intro a b hSa hSb hne ha hb
          have hf := hind a b hSa hSb
          unfold witnessGraph at hf
          simp only [ha, hb, decide_true, Bool.and_true, ↓reduceIte] at hf
          rw [decide_eq_true hne, Bool.true_and] at hf
          cases hc : c5Adj a.val b.val
          · simp [hc] at hf
          · rfl
        exact c5Adj_triangle_free u.val v.val w.val
          (hnon u v hu.1 hv.1 huv hult hvlt)
          (hnon v w hv.1 hw.1 hvw hvlt hwlt)
          (hnon u w hu.1 hw.1 huw hult hwlt)
      · omega
    · simp only [hj, ↓reduceIte]
      by_cases h2 : subsetCard (fun v => S v && decide (wComp r hr v = j)) ≥ 2
      · exfalso
        obtain ⟨u, v, huv, hu, hv⟩ := exists_two _ h2
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hu hv
        have hge : ∀ x : Fin (r * r + 1), wComp r hr x = j →
            x.val ≥ 2 * r + 1 ∧ 1 + (x.val - (2 * r + 1)) / r = j.val := by
          intro x hx
          unfold wComp at hx
          by_cases hlt : x.val < 2 * r + 1
          · exfalso
            simp only [hlt, ↓reduceDIte] at hx
            have := congrArg Fin.val hx; dsimp at this; omega
          · simp only [hlt, ↓reduceDIte] at hx
            have := congrArg Fin.val hx; dsimp at this
            exact ⟨by omega, this⟩
        have ⟨huge, hudiv⟩ := hge u hu.2
        have ⟨hvge, hvdiv⟩ := hge v hv.2
        have hf := hind u v hu.1 hv.1
        unfold witnessGraph at hf
        have hnotu : ¬ (u.val < 2 * r + 1) := by omega
        have hnotv : ¬ (v.val < 2 * r + 1) := by omega
        have hdiv_eq : (u.val - (2 * r + 1)) / r = (v.val - (2 * r + 1)) / r := by omega
        simp only [hnotu, hnotv, huge, hvge, decide_false, decide_true, Bool.and_false, Bool.and_true,
                   Bool.false_eq_true, ↓reduceIte, hdiv_eq] at hf
        rw [decide_eq_true huv] at hf
        exact Bool.noConfusion hf
      · omega
  have hsum_le := sum_map_le (verts (r - 1)) _ (fun j => if j.val = 0 then 2 else 1) hcomp_le
  have hsum_eq : ((verts (r - 1)).map (fun j => if j.val = 0 then 2 else 1)).sum = r := by
    have hrew : ∀ j ∈ verts (r - 1),
        (if j.val = 0 then 2 else 1) = (if decide (j = ⟨0, by omega⟩) then 1 else 0) + 1 := by
      intro j _
      by_cases hj : j.val = 0
      · have hj0 : j = ⟨0, by omega⟩ := Fin.ext hj; rw [hj0]; simp
      · have hjne : j ≠ ⟨0, by omega⟩ := fun h => hj (congrArg Fin.val h); simp [hj, hjne]
    rw [sum_map_eq (verts (r - 1)) _ _ hrew, sum_map_add, sum_map_const, length_verts]
    rw [← sum_filter_eq_sum_ite, sum_map_const]
    have h1 := length_filter_eq_one_of_nodup (verts (r - 1)) (nodup_verts (r - 1)) ⟨0, by omega⟩ (mem_verts _)
    rw [h1]; omega
  omega

/-- Arithmetic lower bound `M * (r + 1 - 2 * M) ≥ r - 1` for `M = (2 * r + 5) / 5`
    whenever `r = 7 ∨ r = 9 ∨ r ≥ 11`. -/
theorem c5_margin_bound (r : Nat) (hr : r = 7 ∨ r = 9 ∨ r ≥ 11) :
    let M := (2 * r + 5) / 5
    2 * M ≤ r + 1 ∧ r + 1 ≤ 3 * M ∧ M * (r + 1 - 2 * M) ≥ r - 1 := by
  intro M
  have hlo : 2 * M ≤ r + 1 := by dsimp [M]; omega
  have hhi : r + 1 ≤ 3 * M := by dsimp [M]; omega
  refine ⟨hlo, hhi, ?_⟩
  rcases hr with rfl | rfl | hr11
  · decide
  · decide
  · let k := r / 5
    let rem := r % 5
    have hkr : 5 * k + rem = r := by dsimp [k, rem]; omega
    have hrem : rem = 0 ∨ rem = 1 ∨ rem = 2 ∨ rem = 3 ∨ rem = 4 := by dsimp [rem]; omega
    rcases hrem with h0 | h1 | h2 | h3 | h4
    · have hk : k ≥ 3 := by omega
      have hM : M = 2 * k + 1 := by dsimp [M]; omega
      rw [hM]
      have hsub : r + 1 - 2 * (2 * k + 1) = k - 1 := by omega
      rw [hsub]
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hk
      have hk' : k = 3 + d := by omega
      have hsub2 : k - 1 = d + 2 := by omega
      rw [hsub2, hk']
      have : (2 * (3 + d) + 1) * (d + 2) = 2 * (d * d) + 11 * d + 14 := by
        simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]
        have : 2 * d * d = 2 * (d * d) := Nat.mul_assoc 2 d d
        have : 2 * d * 2 = 4 * d := by rw [Nat.mul_assoc, Nat.mul_comm d 2, ← Nat.mul_assoc]
        omega
      omega
    · have hk : k ≥ 2 := by omega
      have hM : M = 2 * k + 1 := by dsimp [M]; omega
      rw [hM]
      have hsub : r + 1 - 2 * (2 * k + 1) = k := by omega
      rw [hsub]
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hk
      have hk' : k = 2 + d := by omega
      rw [hk']
      have : (2 * (2 + d) + 1) * (2 + d) = 2 * (d * d) + 9 * d + 10 := by
        simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]
        have : 2 * d * d = 2 * (d * d) := Nat.mul_assoc 2 d d
        have : 2 * d * 2 = 4 * d := by rw [Nat.mul_assoc, Nat.mul_comm d 2, ← Nat.mul_assoc]
        omega
      omega
    · have hk : k ≥ 2 := by omega
      have hM : M = 2 * k + 1 := by dsimp [M]; omega
      rw [hM]
      have hsub : r + 1 - 2 * (2 * k + 1) = k + 1 := by omega
      rw [hsub]
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hk
      have hk' : k = 2 + d := by omega
      rw [hk']
      have : (2 * (2 + d) + 1) * (2 + d + 1) = 2 * (d * d) + 11 * d + 15 := by
        simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
        have : 2 * d * d = 2 * (d * d) := Nat.mul_assoc 2 d d
        have : 2 * d * 2 = 4 * d := by rw [Nat.mul_assoc, Nat.mul_comm d 2, ← Nat.mul_assoc]
        omega
      omega
    · have hk : k ≥ 2 := by omega
      have hM : M = 2 * k + 2 := by dsimp [M]; omega
      rw [hM]
      have hsub : r + 1 - 2 * (2 * k + 2) = k := by omega
      rw [hsub]
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hk
      have hk' : k = 2 + d := by omega
      rw [hk']
      have : (2 * (2 + d) + 2) * (2 + d) = 2 * (d * d) + 10 * d + 12 := by
        simp only [Nat.add_mul, Nat.mul_add]
        have : 2 * d * d = 2 * (d * d) := Nat.mul_assoc 2 d d
        have : 2 * d * 2 = 4 * d := by rw [Nat.mul_assoc, Nat.mul_comm d 2, ← Nat.mul_assoc]
        omega
      omega
    · have hk : k ≥ 2 := by omega
      have hM : M = 2 * k + 2 := by dsimp [M]; omega
      rw [hM]
      have hsub : r + 1 - 2 * (2 * k + 2) = k + 1 := by omega
      rw [hsub]
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hk
      have hk' : k = 2 + d := by omega
      rw [hk']
      have : (2 * (2 + d) + 2) * (2 + d + 1) = 2 * (d * d) + 12 * d + 18 := by
        simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
        have : 2 * d * d = 2 * (d * d) := Nat.mul_assoc 2 d d
        have : 2 * d * 2 = 4 * d := by rw [Nat.mul_assoc, Nat.mul_comm d 2, ← Nat.mul_assoc]
        omega
      omega

/-- **Theorem B (Failure of the Xia–Szeider Single-Graph Relaxation for `r = 7, 9` and all `r ≥ 11`):**
    The explicit graph `witnessGraph r = complement(C₅[a₀..a₄]) ⊔ (r - 2) K_r` satisfies
    all conditions of the single-graph relaxation on `K_{r²+1}`. -/
theorem single_graph_relaxation_fails_c5 (r : Nat) (hr : r = 7 ∨ r = 9 ∨ r ≥ 11) :
    SatisfiesSingleGraphRelaxation r (witnessGraph r) := by
  have hr3 : r ≥ 3 := by omega
  have heven := mul_pred_even r
  refine ⟨witness_edges_le r hr3, ?_⟩
  intro S hScard
  refine ⟨?_, ?_⟩
  · cases h0 : edgesIn (witnessGraph r) S with
    | zero =>
      exfalso
      have hind := (isIndep_iff_edgesIn_zero (witnessGraph r) S).mpr h0
      have hle := witness_indep_le r hr3 S hind
      omega
    | succ m => omega
  · by_cases hsubH : ∀ v : Fin (r * r + 1), S v = true → v.val < 2 * r + 1
    · have hadd := twoEdgesIn_add_compl (witnessGraph r) S
      rw [hScard] at hadd
      have hc := twoEdgesIn_witness_H_compl r S hsubH
      dsimp only at hc
      let x := fun i : Nat => subsetCard (fun v => S v && decide (v.val % 5 = i))
      have hsumx : x 0 + x 1 + x 2 + x 3 + x 4 = r + 1 := by
        have := subsetCard_mod5_sum S
        dsimp [x]; omega
      let M := (2 * r + 5) / 5
      have h2rn : 2 * r + 1 ≤ r * r + 1 := by
        have : 2 * r ≤ r * r := Nat.mul_le_mul_right r (by omega)
        omega
      have hxM : ∀ i, i < 5 → x i ≤ M := by
        intro i hi
        have hle : x i ≤ ((verts (r * r + 1)).filter (fun v => decide (v.val < 2 * r + 1) && decide (v.val % 5 = i))).length := by
          dsimp [x, subsetCard]
          apply filter_length_le; intro v _ hv
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hv ⊢
          exact ⟨hsubH v hv.1, hv.2⟩
        rw [count_mod5_lt (2 * r + 1) i h2rn hi] at hle
        dsimp [M]
        split at hle <;> omega
      obtain ⟨hlo, hhi, hmarg⟩ := c5_margin_bound r hr
      have hQ := c5Q_min (x 0) (x 1) (x 2) (x 3) (x 4) M (r + 1)
        (hxM 0 (by omega)) (hxM 1 (by omega)) (hxM 2 (by omega)) (hxM 3 (by omega)) (hxM 4 (by omega))
        hsumx hlo hhi
      dsimp only [x, M] at hQ
      have h2e := two_mul_edgesIn (witnessGraph r) S
      have hprod_eq : (r + 1) * (r + 1 - 1) = r * (r - 1) + 2 * r := by
        have h1 : r + 1 - 1 = r := by omega
        rw [h1, Nat.add_mul, Nat.one_mul]
        have h2 : r * (r - 1) + r = r * r := by
          rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
        omega
      omega
    · -- Case 2: S ⊄ V(H), so every component gets ≤ r vertices of S
      have hex : ∃ v : Fin (r * r + 1), S v = true ∧ v.val ≥ 2 * r + 1 := by
        -- S is finite and decidable, so find an element where S v ∧ !(v.val < 2*r+1)
        have hne : ((verts (r * r + 1)).filter (fun v => S v && !decide (v.val < 2 * r + 1))).length > 0 := by
          cases hlen : ((verts (r * r + 1)).filter (fun v => S v && !decide (v.val < 2 * r + 1))).length with
          | zero =>
            exfalso
            apply hsubH
            intro v hSv
            have hnil := List.filter_eq_nil_iff.mp (List.length_eq_zero_iff.mp hlen)
            have hf := hnil v (mem_verts v)
            by_cases hlt : v.val < 2 * r + 1
            · exact hlt
            · simp [hSv, hlt] at hf
          | succ _ => omega
        match hfilt : (verts (r * r + 1)).filter (fun v => S v && !decide (v.val < 2 * r + 1)) with
        | [] => simp [hfilt] at hne
        | v :: _ =>
          have hv : v ∈ (verts (r * r + 1)).filter (fun v => S v && !decide (v.val < 2 * r + 1)) := by
            rw [hfilt]; simp
          have hmem := (List.mem_filter.mp hv).2
          simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hmem
          exact ⟨v, hmem.1, by omega⟩
      obtain ⟨v0, hSv0, hv0ge⟩ := hex
      have h2e := two_mul_edgesIn (witnessGraph r) S
      rw [twoEdgesIn_partition_fin (witnessGraph r) S (wComp r hr3) (witnessGraph_disj r hr3)] at h2e
      let sizes := (verts (r - 1)).map (fun j => subsetCard (fun v => S v && decide (wComp r hr3 v = j)))
      have hsum_s : sizes.sum = r + 1 := by
        dsimp [sizes]
        rw [subsetCard_partition_fin S (wComp r hr3), hScard]
      have hle_s : ∀ x ∈ sizes, x ≤ r := by
        intro x hx
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
        by_cases hj : j.val = 0
        · have hp := filter_length_partition (verts (r * r + 1)) S (fun v => decide (wComp r hr3 v = j))
          have hmiss : ((verts (r * r + 1)).filter (fun v => S v && !decide (wComp r hr3 v = j))).length ≥ 1 := by
            have hne : wComp r hr3 v0 ≠ j := by
              intro heq
              have hv0 : (wComp r hr3 v0).val = 0 := by rw [heq, hj]
              have hlt := (wComp_eq_zero_iff r hr3 v0).mp hv0
              omega
            have h1 : ((verts (r * r + 1)).filter (fun v => decide (v = v0))).length = 1 :=
              length_filter_eq_one_of_nodup (verts (r * r + 1)) (nodup_verts _) v0 (mem_verts v0)
            have hle' := filter_length_le (verts (r * r + 1))
              (fun v => decide (v = v0)) (fun v => S v && !decide (wComp r hr3 v = j))
              (fun v _ hv => by
                have heq : v = v0 := of_decide_eq_true hv
                subst heq; simp [hSv0, hne])
            omega
          unfold subsetCard at hScard ⊢
          omega
        · have hle' : subsetCard (fun v => S v && decide (wComp r hr3 v = j)) ≤
                      subsetCard (fun v => decide (wComp r hr3 v = j)) := by
            unfold subsetCard
            apply filter_length_le; intro v _ hv
            exact (Bool.and_eq_true _ _ |>.mp hv).2
          rw [witness_comp_card r hr3 j] at hle'
          simp only [hj, ↓reduceIte] at hle'
          exact hle'
      have hconv := disjoint_union_convexity sizes r hle_s (by omega)
      have hle_e : ((verts (r - 1)).map (fun j => twoEdgesIn (witnessGraph r) (fun v => S v && decide (wComp r hr3 v = j)))).sum ≤
          (sizes.map (fun x => x * (x - 1))).sum := by
        dsimp [sizes]
        rw [List.map_map]
        apply sum_map_le
        intro j _
        exact twoEdgesIn_le_complete (witnessGraph r) (fun v => S v && decide (wComp r hr3 v = j))
      omega

/-! ## Section 4: Theorem C — Multi-Scale Turán-Complement Necessary Condition -/

/-- Any subset `S` of size ≥ `k` contains a subset `T ⊆ S` of exact size `k`. -/
theorem exists_sub_card {n : Nat} (S : Fin n → Bool) (k : Nat) (hk : k ≤ subsetCard S) :
    ∃ T : Fin n → Bool, (∀ v, T v = true → S v = true) ∧ subsetCard T = k := by
  -- Induction on `d = subsetCard S - k`
  have aux : ∀ d : Nat, ∀ S : Fin n → Bool, subsetCard S = k + d →
      ∃ T : Fin n → Bool, (∀ v, T v = true → S v = true) ∧ subsetCard T = k := by
    intro d
    induction d with
    | zero =>
      intro S hS
      exact ⟨S, fun _ h => h, by omega⟩
    | succ d ih =>
      intro S hS
      have hpos : ((verts n).filter S).length > 0 := by unfold subsetCard at hS; omega
      match hfilt : (verts n).filter S with
      | [] => simp [hfilt] at hpos
      | v0 :: _ =>
        have hv0 : v0 ∈ (verts n).filter S := by rw [hfilt]; simp
        have hSv0 : S v0 = true := (List.mem_filter.mp hv0).2
        let S' : Fin n → Bool := fun v => S v && !decide (v = v0)
        have hp := filter_length_partition (verts n) S (fun v => decide (v = v0))
        have h1 : ((verts n).filter (fun v => S v && decide (v = v0))).length = 1 := by
          have heq : ((verts n).filter (fun v => S v && decide (v = v0))).length =
                     ((verts n).filter (fun v => decide (v = v0))).length := by
            apply filter_length_eq; intro v _
            by_cases hv : v = v0
            · subst hv; simp [hSv0]
            · simp [hv]
          rw [heq]
          exact length_filter_eq_one_of_nodup (verts n) (nodup_verts n) v0 (mem_verts v0)
        have hcard' : subsetCard S' = k + d := by
          unfold subsetCard at hS ⊢
          dsimp [S']
          omega
        obtain ⟨T, hTsub, hTcard⟩ := ih S' hcard'
        refine ⟨T, fun v hv => (Bool.and_eq_true _ _ |>.mp (hTsub v hv)).1, hTcard⟩
  exact aux (subsetCard S - k) S (by omega)

theorem isIndep_mono {n : Nat} {G : SGraph n} {S T : Fin n → Bool}
    (hsub : ∀ v, T v = true → S v = true) (hind : IsIndep G S) : IsIndep G T :=
  fun u v hu hv => hind u v (hsub u hu) (hsub v hv)

theorem isBalanced_indep_le {r : Nat} (C : EdgeColoring (r * r + 1) r)
    (hbal : IsBalanced C) (c : Fin r) (I : Fin (r * r + 1) → Bool)
    (hind : IsIndep (colorClass C c) I) : subsetCard I ≤ r := by
  by_cases hle : subsetCard I ≤ r
  · exact hle
  · exfalso
    obtain ⟨S, hsub, hScard⟩ := exists_sub_card I (r + 1) (by omega)
    have hindS : IsIndep (colorClass C c) S := isIndep_mono hsub hind
    have h0 : edgesIn (colorClass C c) S = 0 := (isIndep_iff_edgesIn_zero _ _).mp hindS
    have h1 := hbal c S hScard
    omega

theorem twoEdgesIn_compl_eq_sum_other_colors {n r : Nat} (C : EdgeColoring n r)
    (c : Fin r) (U : Fin n → Bool) :
    twoEdgesIn (colorClass C c).compl U =
      (((verts r).filter (fun c' => !decide (c' = c))).map
        (fun c' => twoEdgesIn (colorClass C c') U)).sum := by
  rw [twoEdgesIn_eq_double_sum]
  rw [sum_filter_eq_sum_ite]
  have hrew : ∀ c' ∈ verts r,
      (if !decide (c' = c) then twoEdgesIn (colorClass C c') U else 0) =
      ((verts n).map (fun u => ((verts n).map (fun v =>
        if U u && U v && decide (u ≠ v) && decide (C.col u v = c') && !decide (c' = c)
        then 1 else 0)).sum)).sum := by
    intro c' _
    by_cases hc' : c' = c
    · subst hc'
      simp only [decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.and_false]
      symm
      have hz : ∀ u ∈ verts n, ((verts n).map (fun _ => (0 : Nat))).sum = 0 := by
        intro u _; rw [sum_map_const, Nat.mul_zero]
      rw [sum_map_eq (verts n) _ (fun _ => 0) hz, sum_map_const, Nat.mul_zero]
    · simp only [hc', decide_false, Bool.not_false, ↓reduceIte, Bool.and_true]
      rw [twoEdgesIn_eq_double_sum]
      apply sum_map_eq; intro u _
      apply sum_map_eq; intro v _
      unfold colorClass
      by_cases h1 : U u = true ∧ U v = true ∧ u ≠ v ∧ C.col u v = c'
      · simp [h1.1, h1.2.1, h1.2.2.1, h1.2.2.2]
      · cases hUu : U u <;> cases hUv : U v <;> by_cases huv : u = v <;> by_cases hcol : C.col u v = c' <;>
        simp_all
  rw [sum_map_eq (verts r) _ _ hrew, sum_swap (verts r) (verts n)]
  apply sum_map_eq; intro u _
  rw [sum_swap (verts r) (verts n)]
  apply sum_map_eq; intro v _
  cases hUu : U u
  · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    symm; rw [sum_map_const, Nat.mul_zero]
  · cases hUv : U v
    · simp only [Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      symm; rw [sum_map_const, Nat.mul_zero]
    · by_cases huv : u = v
      · subst huv
        simp only [Bool.true_and, ne_eq, not_true_eq_false, decide_false, Bool.false_and,
                   Bool.and_false, Bool.false_eq_true, ↓reduceIte, (colorClass C c).compl.loopless]
        symm; rw [sum_map_const, Nat.mul_zero]
      · by_cases hcol : C.col u v = c
        · have hadj : (colorClass C c).compl.adj u v = false := by
            unfold SGraph.compl colorClass; simp [huv, hcol]
          simp only [hadj, Bool.true_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          symm
          have hz : ∀ c' ∈ verts r,
              (if decide (u ≠ v) && decide (C.col u v = c') && !decide (c' = c) then 1 else 0) = 0 := by
            intro c' _
            by_cases hc' : c' = c
            · subst hc'; simp
            · have hne : C.col u v ≠ c' := by rw [hcol]; exact Ne.symm hc'
              simp [hne]
          rw [sum_map_eq (verts r) _ (fun _ => 0) hz, sum_map_const, Nat.mul_zero]
        · have hadj : (colorClass C c).compl.adj u v = true := by
            unfold SGraph.compl colorClass; simp [huv, hcol]
          simp only [hadj, Bool.true_and, Bool.and_true, ↓reduceIte]
          symm
          have h1 : ((verts r).map (fun c' =>
              if decide (u ≠ v) && decide (C.col u v = c') && !decide (c' = c) then 1 else 0)).sum =
              ((verts r).filter (fun c' => decide (c' = C.col u v))).length := by
            rw [length_filter_eq_sum]
            apply sum_map_eq; intro c' _
            by_cases hc' : c' = C.col u v
            · subst hc'; simp [huv, hcol]
            · have hne : C.col u v ≠ c' := Ne.symm hc'
              simp [hc', hne]
          rw [h1]
          exact length_filter_eq_one_of_nodup (verts r) (nodup_verts r) (C.col u v) (mem_verts _)

/-- **Theorem C (Multi-Scale Turán-Complement Bound for Erdős #617):**
    In any balanced `r`-coloring of `K_{r²+1}`, for every color `c`, every subset `U`,
    and every `k : Nat`,
      `2 * edgesIn (colorClass C c).compl U + (r - 1) * (k * (k + 1) * r) ≥ 2 * (r - 1) * k * |U|`. -/
theorem multiscale_turan_complement {r : Nat} (C : EdgeColoring (r * r + 1) r)
    (hbal : IsBalanced C) (c : Fin r) (U : Fin (r * r + 1) → Bool) (k : Nat) :
    2 * edgesIn (colorClass C c).compl U + (r - 1) * (k * (k + 1) * r) ≥
      2 * (r - 1) * k * subsetCard U := by
  rw [two_mul_edgesIn, twoEdgesIn_compl_eq_sum_other_colors C c U]
  let others := (verts r).filter (fun c' => !decide (c' = c))
  have hlen : others.length = r - 1 := by
    have hp := filter_length_partition (verts r) (fun _ => true) (fun c' => decide (c' = c))
    rw [filter_true_eq, length_verts] at hp
    have h1 : ((verts r).filter (fun c' => true && decide (c' = c))).length = 1 :=
      length_filter_eq_one_of_nodup (verts r) (nodup_verts r) c (mem_verts c)
    have h2 : ((verts r).filter (fun c' => true && !decide (c' = c))).length = others.length := rfl
    have hr1 : r ≥ 1 := Nat.pos_of_ne_zero (fun h => by subst h; exact Fin.elim0 c)
    omega
  have hper : ∀ c' ∈ others,
      2 * k * subsetCard U ≤ twoEdgesIn (colorClass C c') U + k * (k + 1) * r := by
    intro c' _
    have ht := turan_linear_envelope (colorClass C c') U r k
      (fun I _ hind => isBalanced_indep_le C hbal c' I hind)
    rw [two_mul_edgesIn] at ht
    exact ht
  have hsum := sum_map_le others (fun _ => 2 * k * subsetCard U)
    (fun c' => twoEdgesIn (colorClass C c') U + k * (k + 1) * r) hper
  rw [sum_map_const, sum_map_add, sum_map_const, hlen] at hsum
  have hlhs' : (r - 1) * (2 * k * subsetCard U) = 2 * (r - 1) * k * subsetCard U := by
    calc (r - 1) * (2 * k * subsetCard U)
        = (r - 1) * (2 * k) * subsetCard U := (Nat.mul_assoc _ _ _).symm
      _ = ((r - 1) * 2 * k) * subsetCard U := by rw [← Nat.mul_assoc (r - 1) 2 k]
      _ = (2 * (r - 1) * k) * subsetCard U := by rw [Nat.mul_comm (r - 1) 2]
  rw [hlhs'] at hsum
  exact hsum

/-- Corollary of Theorem C at `|U| = 2*r + 1, k = 2`: `edgesIn (colorClass C c).compl U ≥ (r - 1) * (r + 2)`. -/
theorem multiscale_2r_plus_1 {r : Nat} (C : EdgeColoring (r * r + 1) r)
    (hbal : IsBalanced C) (c : Fin r) (U : Fin (r * r + 1) → Bool)
    (hcard : subsetCard U = 2 * r + 1) :
    edgesIn (colorClass C c).compl U ≥ (r - 1) * (r + 2) := by
  have h := multiscale_turan_complement C hbal c U 2
  rw [hcard] at h
  have h1 : 2 * (r - 1) * 2 * (2 * r + 1) = (r - 1) * (6 * r) + 2 * ((r - 1) * (r + 2)) := by
    have hmul : 2 * (r - 1) * 2 = (r - 1) * 4 := by
      rw [Nat.mul_comm 2 (r - 1), Nat.mul_assoc]
    rw [hmul, Nat.mul_assoc (r - 1) 4 (2 * r + 1)]
    have h2 : 2 * ((r - 1) * (r + 2)) = (r - 1) * (2 * (r + 2)) := by
      rw [← Nat.mul_assoc, Nat.mul_comm 2 (r - 1), Nat.mul_assoc]
    rw [h2, ← Nat.mul_add]
    congr 1
    omega
  have h2 : (r - 1) * (2 * (2 + 1) * r) = (r - 1) * (6 * r) := by rfl
  omega

/-- Corollary of Theorem C at `|S| = r + 1, k = 1`: `edgesIn (colorClass C c).compl S ≥ r - 1`. -/
theorem balanced_compl_r_plus_1 {r : Nat} (C : EdgeColoring (r * r + 1) r)
    (hbal : IsBalanced C) (c : Fin r) (S : Fin (r * r + 1) → Bool)
    (hcard : subsetCard S = r + 1) :
    edgesIn (colorClass C c).compl S ≥ r - 1 := by
  have h := multiscale_turan_complement C hbal c S 1
  rw [hcard] at h
  have h1 : 2 * (r - 1) * 1 * (r + 1) = (r - 1) * (2 * r) + 2 * (r - 1) := by
    calc 2 * (r - 1) * 1 * (r + 1)
        = (r - 1) * (2 * (r + 1)) := by rw [Nat.mul_one, Nat.mul_comm 2 (r - 1), Nat.mul_assoc]
      _ = (r - 1) * (2 * r + 2) := by rw [Nat.mul_add, Nat.mul_one]
      _ = (r - 1) * (2 * r) + (r - 1) * 2 := Nat.mul_add _ _ _
      _ = (r - 1) * (2 * r) + 2 * (r - 1) := by rw [Nat.mul_comm (r - 1) 2]
  have h2 : (r - 1) * (1 * (1 + 1) * r) = (r - 1) * (2 * r) := by rfl
  omega

/-! ## Section 5: Theorem D — Elementary Proof of the Non-Bipartite Mantel Theorem -/

def IsTriangleFreeOn {n : Nat} (F : SGraph n) (U : Fin n → Bool) : Prop :=
  ∀ u v w, U u = true → U v = true → U w = true →
    F.adj u v = true → F.adj v w = true → F.adj u w = false

def IsBipartiteOn {n : Nat} (F : SGraph n) (U : Fin n → Bool) : Prop :=
  ∃ side : Fin n → Bool, ∀ u v, U u = true → U v = true →
    F.adj u v = true → side u ≠ side v

/-! ### Mantel's Theorem via Cauchy–Schwarz on `Nat` -/

theorem two_mul_le_sq_add_sq (a b : Nat) : 2 * a * b ≤ a * a + b * b := by
  by_cases h : a ≤ b
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have hexp : a * a + (a + d) * (a + d) = 2 * a * (a + d) + d * d := by
      simp only [Nat.add_mul, Nat.mul_add]
      have hc : a * d = d * a := Nat.mul_comm a d
      have h2a : 2 * a * a = 2 * (a * a) := Nat.mul_assoc 2 a a
      have h2d : 2 * a * d = 2 * (a * d) := Nat.mul_assoc 2 a d
      omega
    omega
  · have hba : b ≤ a := by omega
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hba
    have hexp : (b + d) * (b + d) + b * b = 2 * (b + d) * b + d * d := by
      simp only [Nat.add_mul, Nat.mul_add]
      have hc : b * d = d * b := Nat.mul_comm b d
      have h2b : 2 * b * b = 2 * (b * b) := Nat.mul_assoc 2 b b
      have h2d : 2 * d * b = 2 * (d * b) := Nat.mul_assoc 2 d b
      omega
    omega

theorem cauchy_schwarz_nat {α : Type} (l : List α) (f : α → Nat) :
    (l.map f).sum * (l.map f).sum ≤ l.length * (l.map (fun x => f x * f x)).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    let S1 := (xs.map f).sum
    let S2 := (xs.map (fun y => f y * f y)).sum
    have hcross : 2 * f x * S1 ≤ xs.length * (f x * f x) + S2 := by
      have hle := sum_map_le xs (fun y => 2 * f x * f y) (fun y => f x * f x + f y * f y)
        (fun y _ => two_mul_le_sq_add_sq (f x) (f y))
      rw [sum_map_mul_left, sum_map_add, sum_map_const] at hle
      exact hle
    have hlhs : (f x + S1) * (f x + S1) = f x * f x + 2 * f x * S1 + S1 * S1 := by
      simp only [Nat.add_mul, Nat.mul_add]
      have hc : f x * S1 = S1 * f x := Nat.mul_comm _ _
      have h2 : 2 * f x * S1 = 2 * (f x * S1) := Nat.mul_assoc 2 (f x) S1
      omega
    have hrhs : (xs.length + 1) * (f x * f x + S2) =
        f x * f x + (xs.length * (f x * f x) + S2) + xs.length * S2 := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]
      omega
    change S1 * S1 ≤ xs.length * S2 at ih
    rw [hlhs, hrhs]
    omega

theorem mantel_on {n : Nat} (F : SGraph n) (U : Fin n → Bool)
    (htf : IsTriangleFreeOn F U) :
    4 * edgesIn F U ≤ subsetCard U * subsetCard U := by
  have h2e := two_mul_edgesIn F U
  -- For any edge (u, v) in U, N_U(u) and N_U(v) are disjoint, so degIn u + degIn v ≤ subsetCard U
  have hdeg_adj : ∀ u v : Fin n, U u = true → U v = true → F.adj u v = true →
      degIn F U u + degIn F U v ≤ subsetCard U := by
    intro u v hUu hUv hadj
    unfold degIn subsetCard
    have hp := filter_length_partition (verts n) U (fun w => F.adj u w)
    have hsub : ((verts n).filter (fun w => U w && F.adj v w)).length ≤
                ((verts n).filter (fun w => U w && !F.adj u w)).length := by
      apply filter_length_le; intro w _ hw
      simp only [Bool.and_eq_true] at hw ⊢
      refine ⟨hw.1, ?_⟩
      have hf : F.adj u w = false := htf u v w hUu hUv hw.1 hadj hw.2
      simp [hf]
    omega
  -- Sum (degIn u + degIn v) over all ordered adjacent pairs (u, v) in U
  let d := degIn F U
  let m := subsetCard U
  have hsum_le :
      ((verts n).map (fun u => ((verts n).map (fun v =>
        if U u && U v && F.adj u v then d u + d v else 0)).sum)).sum ≤
      ((verts n).map (fun u => ((verts n).map (fun v =>
        if U u && U v && F.adj u v then m else 0)).sum)).sum := by
    apply sum_map_le; intro u _
    apply sum_map_le; intro v _
    cases hUu : U u
    · simp
    · cases hUv : U v
      · simp
      · cases hadj : F.adj u v
        · simp
        · simp only [Bool.true_and, ↓reduceIte]
          exact hdeg_adj u v hUu hUv hadj
  -- Evaluate RHS = m * twoEdgesIn F U
  have hrhs :
      ((verts n).map (fun u => ((verts n).map (fun v =>
        if U u && U v && F.adj u v then m else 0)).sum)).sum = m * twoEdgesIn F U := by
    rw [twoEdgesIn_eq_double_sum, ← sum_map_mul_left]
    apply sum_map_eq; intro u _
    rw [← sum_map_mul_left]
    apply sum_map_eq; intro v _
    split <;> simp
  -- Evaluate LHS = 2 * ∑_{u ∈ U} (d u)^2
  have hlhs_part :
      ((verts n).map (fun u => ((verts n).map (fun v =>
        if U u && U v && F.adj u v then d u else 0)).sum)).sum =
      (((verts n).filter U).map (fun u => d u * d u)).sum := by
    rw [sum_filter_eq_sum_ite]
    apply sum_map_eq; intro u _
    cases hUu : U u
    · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      rw [sum_map_const, Nat.mul_zero]
    · simp only [Bool.true_and, ↓reduceIte]
      have h1 : ((verts n).map (fun v => if U v && F.adj u v then d u else 0)).sum =
                (((verts n).filter (fun v => U v && F.adj u v)).map (fun _ => d u)).sum :=
        (sum_filter_eq_sum_ite (verts n) (fun v => U v && F.adj u v) (fun _ => d u)).symm
      rw [h1, sum_map_const]
      rfl
  have hlhs :
      ((verts n).map (fun u => ((verts n).map (fun v =>
        if U u && U v && F.adj u v then d u + d v else 0)).sum)).sum =
      2 * (((verts n).filter U).map (fun u => d u * d u)).sum := by
    have hsplit :
        ((verts n).map (fun u => ((verts n).map (fun v =>
          if U u && U v && F.adj u v then d u + d v else 0)).sum)).sum =
        ((verts n).map (fun u => ((verts n).map (fun v =>
          if U u && U v && F.adj u v then d u else 0)).sum)).sum +
        ((verts n).map (fun u => ((verts n).map (fun v =>
          if U u && U v && F.adj u v then d v else 0)).sum)).sum := by
      rw [← sum_map_add]
      apply sum_map_eq; intro u _
      rw [← sum_map_add]
      apply sum_map_eq; intro v _
      split <;> simp
    have hsym :
        ((verts n).map (fun u => ((verts n).map (fun v =>
          if U u && U v && F.adj u v then d v else 0)).sum)).sum =
        ((verts n).map (fun u => ((verts n).map (fun v =>
          if U u && U v && F.adj u v then d u else 0)).sum)).sum := by
      rw [sum_swap (verts n) (verts n)]
      apply sum_map_eq; intro v _
      apply sum_map_eq; intro u _
      rw [F.symm u v]
      cases U u <;> cases U v <;> cases F.adj v u <;> simp
    rw [hsplit, hsym, hlhs_part]
    omega
  rw [hlhs, hrhs] at hsum_le
  -- Apply Cauchy–Schwarz: (twoEdgesIn F U)^2 ≤ m * ∑_{u ∈ U} (d u)^2
  have hcs := cauchy_schwarz_nat ((verts n).filter U) d
  have hlen : ((verts n).filter U).length = m := rfl
  have hsumd : (((verts n).filter U).map d).sum = twoEdgesIn F U := rfl
  rw [hlen, hsumd] at hcs
  have hmul := Nat.mul_le_mul_left m hsum_le
  have h2cs : 2 * (twoEdgesIn F U * twoEdgesIn F U) ≤ m * (2 * (((verts n).filter U).map (fun u => d u * d u)).sum) := by
    have h1 : m * (2 * (((verts n).filter U).map (fun u => d u * d u)).sum) =
              2 * (m * (((verts n).filter U).map (fun u => d u * d u)).sum) := by
      rw [← Nat.mul_assoc, Nat.mul_comm m 2, Nat.mul_assoc]
    rw [h1]
    exact Nat.mul_le_mul_left 2 hcs
  have hchain : (2 * twoEdgesIn F U) * twoEdgesIn F U ≤ (m * m) * twoEdgesIn F U := by
    have ha : (2 * twoEdgesIn F U) * twoEdgesIn F U = 2 * (twoEdgesIn F U * twoEdgesIn F U) := Nat.mul_assoc _ _ _
    have hb : (m * m) * twoEdgesIn F U = m * (m * twoEdgesIn F U) := Nat.mul_assoc _ _ _
    rw [ha, hb]
    exact Nat.le_trans h2cs hmul
  by_cases hz : twoEdgesIn F U = 0
  · omega
  · have hpos : 0 < twoEdgesIn F U := by omega
    have hcancel := Nat.le_of_mul_le_mul_right hchain hpos
    dsimp [m] at hcancel
    omega

/-! ### Walks, Odd Cycles, and Bipartiteness Characterization -/

inductive Reach {n : Nat} (F : SGraph n) (U : Fin n → Bool) : Nat → Fin n → Fin n → Prop where
  | zero {u : Fin n} (hu : U u = true) : Reach F U 0 u u
  | step {k : Nat} {u v w : Fin n} (hu : U u = true) (hadj : F.adj u v = true)
      (hrest : Reach F U k v w) : Reach F U (k + 1) u w

theorem Reach.mem_left {n : Nat} {F : SGraph n} {U : Fin n → Bool} {k : Nat} {u v : Fin n}
    (h : Reach F U k u v) : U u = true := by
  cases h with
  | zero hu => exact hu
  | step hu _ _ => exact hu

theorem Reach.mem_right {n : Nat} {F : SGraph n} {U : Fin n → Bool} {k : Nat} {u v : Fin n}
    (h : Reach F U k u v) : U v = true := by
  induction h with
  | zero hu => exact hu
  | step _ _ _ ih => exact ih

theorem Reach.trans {n : Nat} {F : SGraph n} {U : Fin n → Bool} {k1 k2 : Nat} {u v w : Fin n}
    (h1 : Reach F U k1 u v) (h2 : Reach F U k2 v w) : Reach F U (k1 + k2) u w := by
  induction h1 with
  | zero _ => simpa using h2
  | step hu hadj _ ih =>
    simpa [Nat.succ_add] using Reach.step hu hadj (ih h2)

theorem Reach.symm {n : Nat} {F : SGraph n} {U : Fin n → Bool} {k : Nat} {u v : Fin n}
    (h : Reach F U k u v) : Reach F U k v u := by
  induction h with
  | zero hu => exact Reach.zero hu
  | step hu hadj hrest ih =>
    have h1 : Reach F U 1 _ _ := Reach.step hrest.mem_left (by rw [F.symm]; exact hadj) (Reach.zero hu)
    exact ih.trans h1

/-- If `F[U]` has no closed odd walk, then `F[U]` is bipartite. -/
theorem bipartite_of_no_odd_closed_walk {n : Nat} (F : SGraph n) (U : Fin n → Bool)
    (hno : ∀ k u, k % 2 = 1 → ¬ Reach F U k u u) : IsBipartiteOn F U := by
  -- Canonical root of each vertex v ∈ U: first vertex r in `verts n` reachable from v
  let canReach : Fin n → Fin n → Bool :=
    fun r v => @decide (∃ k, Reach F U k r v) (Classical.propDecidable _)
  let rootList : Fin n → List (Fin n) := fun v => (verts n).filter (fun r => canReach r v)
  let side : Fin n → Bool := fun v =>
    match (rootList v).head? with
    | none => false
    | some r => @decide (∃ k, k % 2 = 1 ∧ Reach F U k r v) (Classical.propDecidable _)
  refine ⟨side, ?_⟩
  intro u v hUu hUv hadj
  -- Same connected component => identical rootList
  have hrl : rootList u = rootList v := by
    dsimp [rootList]
    have aux : ∀ l : List (Fin n),
        l.filter (fun r => canReach r u) = l.filter (fun r => canReach r v) := by
      intro l
      induction l with
      | nil => rfl
      | cons r rs ih =>
        have hiff : (∃ k, Reach F U k r u) ↔ (∃ k, Reach F U k r v) := by
          constructor
          · rintro ⟨k, hk⟩
            exact ⟨k + 1, hk.trans (Reach.step hUu hadj (Reach.zero hUv))⟩
          · rintro ⟨k, hk⟩
            exact ⟨k + 1, hk.trans (Reach.step hUv (by rw [F.symm]; exact hadj) (Reach.zero hUu))⟩
        have hbeq : canReach r u = canReach r v := by
          dsimp [canReach]
          by_cases h1 : ∃ k, Reach F U k r u
          · have h2 := hiff.mp h1
            simp [h1, h2]
          · have h2 : ¬ ∃ k, Reach F U k r v := fun h => h1 (hiff.mpr h)
            simp [h1, h2]
        simp [List.filter_cons, hbeq, ih]
    exact aux (verts n)
  -- rootList u is non-empty since u ∈ rootList u
  have hu_mem : u ∈ rootList u := by
    dsimp [rootList, canReach]
    refine List.mem_filter.mpr ⟨mem_verts u, ?_⟩
    have h0 : ∃ k, Reach F U k u u := ⟨0, Reach.zero hUu⟩
    simp [h0]
  match hhd : (rootList u).head? with
  | none =>
    have hnil : rootList u = [] := List.head?_eq_none_iff.mp hhd
    rw [hnil] at hu_mem; simp at hu_mem
  | some r =>
    have hr_mem : r ∈ rootList u := List.mem_of_head? hhd
    have hr_reach : ∃ k, Reach F U k r u := by
      have hcr := (List.mem_filter.mp hr_mem).2
      dsimp [canReach] at hcr
      exact @of_decide_eq_true _ (Classical.propDecidable _) hcr
    have hside_u : side u = @decide (∃ k, k % 2 = 1 ∧ Reach F U k r u) (Classical.propDecidable _) := by
      dsimp [side]; rw [hhd]
    have hside_v : side v = @decide (∃ k, k % 2 = 1 ∧ Reach F U k r v) (Classical.propDecidable _) := by
      dsimp [side]; rw [← hrl, hhd]
    intro heq
    rw [hside_u, hside_v] at heq
    by_cases hodd_u : ∃ k, k % 2 = 1 ∧ Reach F U k r u
    · have hodd_v : ∃ k, k % 2 = 1 ∧ Reach F U k r v := by
        have h1 : @decide (∃ k, k % 2 = 1 ∧ Reach F U k r u) (Classical.propDecidable _) = true :=
          @decide_eq_true _ (Classical.propDecidable _) hodd_u
        rw [h1] at heq
        exact @of_decide_eq_true _ (Classical.propDecidable _) heq.symm
      obtain ⟨a, ha, hra⟩ := hodd_u
      obtain ⟨b, hb, hrb⟩ := hodd_v
      have hclosed : Reach F U (a + 1 + b) r r :=
        (hra.trans (Reach.step hUu hadj (Reach.zero hUv))).trans hrb.symm
      exact hno (a + 1 + b) r (by omega) hclosed
    · have hodd_v : ¬ ∃ k, k % 2 = 1 ∧ Reach F U k r v := by
        have h1 : @decide (∃ k, k % 2 = 1 ∧ Reach F U k r u) (Classical.propDecidable _) = false :=
          @decide_eq_false _ (Classical.propDecidable _) hodd_u
        rw [h1] at heq
        intro hv
        have h2 : @decide (∃ k, k % 2 = 1 ∧ Reach F U k r v) (Classical.propDecidable _) = true :=
          @decide_eq_true _ (Classical.propDecidable _) hv
        rw [h2] at heq
        exact Bool.noConfusion heq
      obtain ⟨k, hkr⟩ := hr_reach
      have hkeven : k % 2 = 0 := by
        cases hmod : k % 2 with
        | zero => rfl
        | succ m =>
          have h1 : k % 2 = 1 := by omega
          exact absurd ⟨k, h1, hkr⟩ hodd_u
      have hkv : Reach F U (k + 1) r v := hkr.trans (Reach.step hUu hadj (Reach.zero hUv))
      exact hodd_v ⟨k + 1, by omega, hkv⟩

theorem not_bipartite_exists_min_odd_walk {n : Nat} (F : SGraph n) (U : Fin n → Bool)
    (hnb : ¬ IsBipartiteOn F U) :
    ∃ L u, L % 2 = 1 ∧ Reach F U L u u ∧
      (∀ k v, k % 2 = 1 → Reach F U k v v → L ≤ k) := by
  have hex : ∃ k, k % 2 = 1 ∧ ∃ u, Reach F U k u u := by
    apply Classical.byContradiction
    intro hno
    apply hnb
    apply bipartite_of_no_odd_closed_walk
    intro k u hk hru
    exact hno ⟨k, hk, u, hru⟩
  -- Well-founded minimization on Nat
  have aux : ∀ m : Nat, (∃ k, k ≤ m ∧ k % 2 = 1 ∧ ∃ u, Reach F U k u u) →
      ∃ L u, L % 2 = 1 ∧ Reach F U L u u ∧ (∀ k v, k % 2 = 1 → Reach F U k v v → L ≤ k) := by
    intro m
    induction m with
    | zero =>
      rintro ⟨k, hk0, hkod, _⟩; omega
    | succ m ih =>
      intro h
      by_cases hprev : ∃ k, k ≤ m ∧ k % 2 = 1 ∧ ∃ u, Reach F U k u u
      · exact ih hprev
      · obtain ⟨k, hkle, hkod, u, hru⟩ := h
        have hkeq : k = m + 1 := by
          by_cases hlt : k ≤ m
          · exact absurd ⟨k, hlt, hkod, u, hru⟩ hprev
          · omega
        subst hkeq
        refine ⟨m + 1, u, hkod, hru, ?_⟩
        intro k' v hk' hrv
        by_cases hlt : k' ≤ m
        · exact absurd ⟨k', hlt, hk', v, hrv⟩ hprev
        · omega
  obtain ⟨k, hk, u, hru⟩ := hex
  exact aux k ⟨k, Nat.le_refl k, hk, u, hru⟩

/-- Convert a `Reach F U k u v` proof into an explicit vertex list of length `k + 1`. -/
theorem reach_to_path {n : Nat} {F : SGraph n} {U : Fin n → Bool} {k : Nat} {u v : Fin n}
    (h : Reach F U k u v) :
    ∃ l : List (Fin n),
      l.length = k + 1 ∧
      (∀ x ∈ l, U x = true) ∧
      l[0]? = some u ∧
      l[k]? = some v ∧
      ∀ i (_hi : i < k),
        ∃ a b, l[i]? = some a ∧ l[i + 1]? = some b ∧ F.adj a b = true := by
  induction h with
  | @zero u hu =>
    refine ⟨[u], rfl, ?_, rfl, rfl, fun i hi => by omega⟩
    intro x hx; simp at hx; subst hx; exact hu
  | @step k u v w hu hadj hrest ih =>
    obtain ⟨l, hlen, hmem, hl0, hlk, hstep⟩ := ih
    refine ⟨u :: l, by simp [hlen], ?_, rfl, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hu
      · exact hmem x hx'
    · simpa using hlk
    · intro i hi
      cases i with
      | zero =>
        exact ⟨u, v, rfl, by simpa using hl0, hadj⟩
      | succ i' =>
        obtain ⟨a, b, ha, hb, hab⟩ := hstep i' (by omega)
        exact ⟨a, b, by simpa using ha, by simpa using hb, hab⟩

/-- A closed walk `C : List (Fin n)` of length `L ≥ 1` in `F[U]`. -/
structure ClosedWalk {n : Nat} (F : SGraph n) (U : Fin n → Bool) (C : List (Fin n)) : Prop where
  pos : C.length ≥ 1
  mem_U : ∀ x ∈ C, U x = true
  adj_next : ∀ i (hi : i < C.length),
    F.adj (C[i]'hi) (C[(i + 1) % C.length]'(Nat.mod_lt _ (by omega))) = true

theorem reach_closed_to_walk {n : Nat} {F : SGraph n} {U : Fin n → Bool} {L : Nat} {u : Fin n}
    (hL : L ≥ 1) (hr : Reach F U L u u) :
    ∃ C : List (Fin n), ClosedWalk F U C ∧ C.length = L := by
  obtain ⟨l, hlen, hmem, hl0, hlL, hstep⟩ := reach_to_path hr
  let C := l.take L
  have hClen : C.length = L := by
    dsimp [C]; rw [List.length_take]; omega
  refine ⟨C, ⟨by omega, ?_, ?_⟩, hClen⟩
  · intro x hx
    exact hmem x (List.mem_of_mem_take hx)
  · intro i hi
    have hiL : i < L := by omega
    obtain ⟨a, b, ha, hb, hab⟩ := hstep i hiL
    have hCi : C[i]'hi = a := by
      have hget : C[i]? = some a := by
        dsimp [C]; rw [List.getElem?_take_of_lt hiL]; exact ha
      rw [List.getElem?_eq_getElem hi] at hget
      exact Option.some.inj hget
    have hCnext : C[(i + 1) % C.length]'(Nat.mod_lt _ (by omega)) = b := by
      by_cases hlast : i + 1 < L
      · have hmod : (i + 1) % C.length = i + 1 := by rw [hClen]; exact Nat.mod_eq_of_lt hlast
        have hget : C[(i + 1) % C.length]? = some b := by
          rw [hmod]; dsimp [C]; rw [List.getElem?_take_of_lt hlast]; exact hb
        rw [List.getElem?_eq_getElem (Nat.mod_lt _ (by omega))] at hget
        exact Option.some.inj hget
      · have heq : i + 1 = L := by omega
        have hmod : (i + 1) % C.length = 0 := by rw [hClen, heq, Nat.mod_self]
        have hbu : b = u := by
          rw [heq] at hb; rw [hb] at hlL; exact Option.some.inj hlL
        have hget : C[(i + 1) % C.length]? = some u := by
          rw [hmod]; dsimp [C]; rw [List.getElem?_take_of_lt (by omega)]; exact hl0
        rw [List.getElem?_eq_getElem (Nat.mod_lt _ (by omega))] at hget
        rw [hbu]; exact Option.some.inj hget
    rw [hCi, hCnext]
    exact hab

/-- Along a `ClosedWalk`, moving forward `d` steps yields a `Reach` of length `d`. -/
theorem ClosedWalk.reach_steps {n : Nat} {F : SGraph n} {U : Fin n → Bool} {C : List (Fin n)}
    (hC : ClosedWalk F U C) :
    ∀ d i, Reach F U d (C[i % C.length]'(Nat.mod_lt _ hC.pos))
                       (C[(i + d) % C.length]'(Nat.mod_lt _ hC.pos)) := by
  intro d
  induction d with
  | zero =>
    intro i
    simpa using Reach.zero (hC.mem_U _ (List.getElem_mem _))
  | succ d ih =>
    intro i
    have h1 := hC.adj_next (i % C.length) (Nat.mod_lt _ hC.pos)
    have hmod1 : (i % C.length + 1) % C.length = (i + 1) % C.length := by
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have h2 : F.adj (C[i % C.length]'(Nat.mod_lt _ hC.pos))
                    (C[(i + 1) % C.length]'(Nat.mod_lt _ hC.pos)) = true := by
      simpa [hmod1] using h1
    have hrest := ih (i + 1)
    have hmod2 : (i + 1 + d) % C.length = (i + (d + 1)) % C.length := by
      have : i + 1 + d = i + (d + 1) := by omega
      rw [this]
    have hres := Reach.step (hC.mem_U _ (List.getElem_mem _)) h2 hrest
    simpa [hmod2] using hres

theorem ClosedWalk.reach_arc_fwd {n : Nat} {F : SGraph n} {U : Fin n → Bool} {C : List (Fin n)}
    (hC : ClosedWalk F U C) {i j : Nat} (hi : i < C.length) (hj : j < C.length) (hij : i ≤ j) :
    Reach F U (j - i) (C[i]'hi) (C[j]'hj) := by
  have h := hC.reach_steps (j - i) i
  have h1 : i % C.length = i := Nat.mod_eq_of_lt hi
  have h2 : (i + (j - i)) % C.length = j := by
    have : i + (j - i) = j := by omega
    rw [this, Nat.mod_eq_of_lt hj]
  simpa [h1, h2] using h

theorem ClosedWalk.reach_arc_bwd {n : Nat} {F : SGraph n} {U : Fin n → Bool} {C : List (Fin n)}
    (hC : ClosedWalk F U C) {i j : Nat} (hi : i < C.length) (hj : j < C.length) (hij : i ≤ j) :
    Reach F U (C.length - (j - i)) (C[j]'hj) (C[i]'hi) := by
  have h := hC.reach_steps (C.length - (j - i)) j
  have h1 : j % C.length = j := Nat.mod_eq_of_lt hj
  have h2 : (j + (C.length - (j - i))) % C.length = i := by
    have : j + (C.length - (j - i)) = i + C.length := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
  simpa [h1, h2] using h

theorem nodup_of_inj_getElem {α : Type} (l : List α)
    (hinj : ∀ i j (hi : i < l.length) (hj : j < l.length), l[i]'hi = l[j]'hj → i = j) :
    l.Nodup := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.nodup_cons]
    refine ⟨?_, ih (fun i j hi hj heq => ?_)⟩
    · intro hmem
      obtain ⟨idx, hidx, hget⟩ := List.mem_iff_getElem.mp hmem
      have h0 : (x :: xs)[0]'(by simp) = (x :: xs)[idx + 1]'(by simp [hidx]) := hget.symm
      have := hinj 0 (idx + 1) (by simp) (by simp [hidx]) h0
      omega
    · have h1 : (x :: xs)[i + 1]'(by simp [hi]) = (x :: xs)[j + 1]'(by simp [hj]) := heq
      have := hinj (i + 1) (j + 1) (by simp [hi]) (by simp [hj]) h1
      omega

/-- **Theorem D (Non-Bipartite Mantel Theorem):**
    Every triangle-free, non-bipartite graph `F` on a subset `U` of size `m ≥ 5` satisfies
    `4 * edgesIn F U ≤ (m - 1)² + 4`. -/
theorem non_bipartite_mantel {n : Nat} (F : SGraph n) (U : Fin n → Bool)
    (htf : IsTriangleFreeOn F U) (hnb : ¬ IsBipartiteOn F U) (hm5 : subsetCard U ≥ 5) :
    4 * edgesIn F U ≤ (subsetCard U - 1) * (subsetCard U - 1) + 4 := by
  obtain ⟨L, u0, hLodd, hru0, hmin⟩ := not_bipartite_exists_min_odd_walk F U hnb
  have hLpos : L ≥ 1 := by omega
  obtain ⟨C, hC, hCL⟩ := reach_closed_to_walk hLpos hru0
  -- Step 1: L ≥ 5 (cannot be 1 by loopless, cannot be 3 by triangle-free)
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
  -- Step 2: C is Nodup (simple odd cycle)
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
  -- Step 3: No chords in C
  have hno_chord : ∀ i j (hi : i < C.length) (hj : j < C.length), i < j →
      F.adj (C[i]'hi) (C[j]'hj) = true → j = i + 1 ∨ (i = 0 ∧ j = C.length - 1) := by
    intro i j hi hj hij hadj
    by_cases h1 : j = i + 1
    · exact Or.inl h1
    · by_cases h2 : i = 0 ∧ j = C.length - 1
      · exact Or.inr h2
      · exfalso
        have hgap1 : j - i ≥ 2 := by omega
        have hgap2 : C.length - (j - i) ≥ 2 := by omega
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
  -- Step 4: Every vertex u ∈ U \ C has at most 2 neighbors in C
  have hno_three_nbrs : ∀ u : Fin n, U u = true → u ∉ C →
      ∀ i j k (hi : i < C.length) (hj : j < C.length) (hk : k < C.length),
      i < j → j < k →
      F.adj u (C[i]'hi) = true → F.adj u (C[j]'hj) = true → F.adj u (C[k]'hk) = true → False := by
    intro u hUu _ i j k hi hj hk hij hjk hai haj hak
    -- By triangle-freeness, u cannot be adjacent to two consecutive vertices of C
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
    -- Build 3 closed walks through u of lengths (j-i)+2, (k-j)+2, (L-(k-i))+2 (all ≤ L - 2!)
    have hwalk_arc : ∀ d (a b : Fin n), F.adj u a = true → F.adj u b = true →
        Reach F U d a b → Reach F U (d + 2) u u := by
      intro d a b hua hub hrab
      have h1 : Reach F U (d + 1) a u :=
        hrab.trans (Reach.step hrab.mem_right (by rw [F.symm]; exact hub) (Reach.zero hUu))
      exact Reach.step hUu hua h1
    have hw1 := hwalk_arc (j - i) _ _ hai haj (hC.reach_arc_fwd hi hj (by omega))
    have hw2 := hwalk_arc (k - j) _ _ haj hak (hC.reach_arc_fwd hj hk (by omega))
    have hw3 := hwalk_arc (C.length - (k - i)) _ _ hak hai (hC.reach_arc_bwd hi hk (by omega))
    by_cases o1 : (j - i + 2) % 2 = 1
    · have := hmin _ u o1 hw1; omega
    · by_cases o2 : (k - j + 2) % 2 = 1
      · have := hmin _ u o2 hw2; omega
      · have o3 : (C.length - (k - i) + 2) % 2 = 1 := by omega
        have := hmin _ u o3 hw3; omega
  -- Step 5: Partition U into inC and outC, bound edges in each part!
  let inC : Fin n → Bool := fun v => decide (v ∈ C)
  let outC : Fin n → Bool := fun v => U v && !inC v
  have hinC_sub : ∀ v, inC v = true → U v = true := fun v hv => hC.mem_U v (of_decide_eq_true hv)
  -- Helper: mapping `i : Fin C.length ↦ C[i]` gives bijection with `inC`
  have hinC_card : subsetCard inC = L := by
    unfold subsetCard
    have hCnd : C.Nodup := nodup_of_inj_getElem C hC_inj
    have haux : ∀ l : List (Fin n), l.Nodup →
        ((verts n).filter (fun v => decide (v ∈ l))).length = l.length := by
      intro l
      induction l with
      | nil => intro _; simp
      | cons x xs ih =>
        intro hnd
        rw [List.nodup_cons] at hnd
        have hp := filter_length_partition (verts n) (fun v => decide (v ∈ x :: xs)) (fun v => decide (v = x))
        have h1 : ((verts n).filter (fun v => decide (v ∈ x :: xs) && decide (v = x))).length = 1 := by
          have heq : ((verts n).filter (fun v => decide (v ∈ x :: xs) && decide (v = x))).length =
                     ((verts n).filter (fun v => decide (v = x))).length := by
            apply filter_length_eq; intro v _
            by_cases hv : v = x
            · subst hv; simp
            · simp [hv]
          rw [heq]
          exact length_filter_eq_one_of_nodup (verts n) (nodup_verts n) x (mem_verts x)
        have h2 : ((verts n).filter (fun v => decide (v ∈ x :: xs) && !decide (v = x))).length =
                  ((verts n).filter (fun v => decide (v ∈ xs))).length := by
          apply filter_length_eq; intro v _
          by_cases hv : v = x
          · subst hv; simp [hnd.1]
          · simp [hv]
        have hih := ih hnd.2
        simp only [List.length_cons]
        omega
    rw [← hCL]
    exact haux C hCnd
  have hU_part : subsetCard U = L + subsetCard outC := by
    unfold subsetCard
    have hp := filter_length_partition (verts n) U inC
    have h1 : ((verts n).filter (fun v => U v && inC v)).length = subsetCard inC := by
      unfold subsetCard
      apply filter_length_eq; intro v _
      cases h : inC v
      · simp
      · simp [hinC_sub v h]
    rw [h1, hinC_card] at hp
    exact hp
  have hL_le_m : L ≤ subsetCard U := by omega
  -- Helper: count vertices in `inC` satisfying a predicate `P` equals count of indices `i : Fin C.length` with `P C[i]`
  have hcount_inC : ∀ P : Fin n → Bool,
      ((verts n).filter (fun v => inC v && P v)).length =
      ((verts C.length).filter (fun i => P (C[i.val]'i.isLt))).length := by
    intro P
    have haux : ∀ l : List (Fin n), l.Nodup →
        ((verts n).filter (fun v => decide (v ∈ l) && P v)).length = (l.filter P).length := by
      intro l
      induction l with
      | nil => intro _; simp
      | cons x xs ih =>
        intro hnd
        rw [List.nodup_cons] at hnd
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
            rw [heq]
            exact length_filter_eq_one_of_nodup (verts n) (nodup_verts n) x (mem_verts x)
          rw [List.filter_cons]; simp only [hPx, ↓reduceIte, List.length_cons]; omega
    have hCnd : C.Nodup := nodup_of_inj_getElem C hC_inj
    rw [haux C hCnd]
    have hmap : C = (verts C.length).map (fun i => C[i.val]'i.isLt) := by
      apply List.ext_getElem
      · simp [length_verts]
      · intro i hi1 hi2
        simp [verts]
    calc (C.filter P).length
        = (((verts C.length).map (fun i => C[i.val]'i.isLt)).filter P).length := by rw [← hmap]
      _ = ((verts C.length).filter (fun i => P (C[i.val]'i.isLt))).length := by
          rw [List.filter_map, List.length_map]; rfl
  -- Bound degIn F inC v ≤ 2 for v ∈ C (from hno_chord)
  have hdeg_inC : ∀ v : Fin n, inC v = true → degIn F inC v ≤ 2 := by
    intro v hv
    unfold degIn
    rw [hcount_inC (fun w => F.adj v w)]
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
  -- Bound degIn F inC u ≤ 2 for u ∈ outC (from hno_three_nbrs)
  have hdeg_outC : ∀ u : Fin n, outC u = true → degIn F inC u ≤ 2 := by
    intro u hu
    have hUu : U u = true := (Bool.and_eq_true _ _ |>.mp hu).1
    have hnotC : u ∉ C := by
      have h2 := (Bool.and_eq_true _ _ |>.mp hu).2
      simp [inC] at h2
      exact h2
    unfold degIn
    rw [hcount_inC (fun w => F.adj u w)]
    by_cases hle2 : ((verts C.length).filter (fun i => F.adj u (C[i.val]'i.isLt))).length ≤ 2
    · exact hle2
    · exfalso
      -- The filtered list of `verts C.length` is strictly increasing (since finRange is strictly increasing!)
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
          have hpw2 := hpw.2
          rw [List.pairwise_cons] at hpw2
          exact ⟨a, b, c, by simp, by simp, by simp, hpw.1 b (by simp), hpw2.1 c (by simp)⟩
      have hpw_verts : (verts C.length).Pairwise (fun a b => a.val < b.val) := by
        unfold verts
        rw [List.pairwise_iff_getElem]
        intro i j hi hj hij
        simp [hij]
      have hpw_filt := hpw_verts.filter (fun i => F.adj u (C[i.val]'i.isLt))
      obtain ⟨a, b, c, ha, hb, hc, hab, hbc⟩ := hsort _ hpw_filt (by omega)
      exact hno_three_nbrs u hUu hnotC a.val b.val c.val a.isLt b.isLt c.isLt hab hbc
        (List.mem_filter.mp ha).2 (List.mem_filter.mp hb).2 (List.mem_filter.mp hc).2
  -- Split twoEdgesIn F U = twoEdgesIn F inC + 2 * cross + twoEdgesIn F outC
  let cross := (((verts n).filter outC).map (degIn F inC)).sum
  have hsplit_e : twoEdgesIn F U = twoEdgesIn F inC + 2 * cross + twoEdgesIn F outC := by
    have hpart_deg : ∀ x : Fin n, degIn F U x = degIn F inC x + degIn F outC x := by
      intro x
      unfold degIn
      have hp := filter_length_partition (verts n) (fun v => U v && F.adj x v) inC
      have h1 : ((verts n).filter (fun v => (U v && F.adj x v) && inC v)).length =
                ((verts n).filter (fun v => inC v && F.adj x v)).length := by
        apply filter_length_eq; intro v _
        cases h : inC v
        · simp
        · simp [hinC_sub v h]
      have h2 : ((verts n).filter (fun v => (U v && F.adj x v) && !inC v)).length =
                ((verts n).filter (fun v => outC v && F.adj x v)).length := by
        apply filter_length_eq; intro v _
        dsimp [outC]; cases U v <;> cases inC v <;> cases F.adj x v <;> simp
      omega
    have hsplit_u : twoEdgesIn F U =
        (((verts n).filter inC).map (degIn F U)).sum + (((verts n).filter outC).map (degIn F U)).sum := by
      unfold twoEdgesIn
      rw [sum_filter_eq_sum_ite, sum_filter_eq_sum_ite, sum_filter_eq_sum_ite, ← sum_map_add]
      apply sum_map_eq; intro u _
      dsimp [outC]
      by_cases hi : inC u = true
      · have hUu := hinC_sub u hi
        simp [hUu, hi]
      · have hi' : inC u = false := by cases h : inC u; rfl; exact absurd h hi
        by_cases hUu : U u = true
        · simp [hUu, hi']
        · have hUu' : U u = false := by cases h : U u; rfl; exact absurd h hUu
          simp [hUu', hi']
    have hsym_cross : (((verts n).filter inC).map (degIn F outC)).sum = cross := by
      dsimp [cross]
      unfold degIn
      rw [sum_filter_eq_sum_ite, sum_filter_eq_sum_ite]
      have h1 : ∀ u ∈ verts n,
          (if inC u then ((verts n).filter (fun v => outC v && F.adj u v)).length else 0) =
          ((verts n).map (fun v => if inC u && outC v && F.adj u v then 1 else 0)).sum := by
        intro u _
        cases hi : inC u
        · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]; symm; rw [sum_map_const, Nat.mul_zero]
        · simp only [Bool.true_and, ↓reduceIte]; exact length_filter_eq_sum (verts n) _
      have h2 : ∀ u ∈ verts n,
          (if outC u then ((verts n).filter (fun v => inC v && F.adj u v)).length else 0) =
          ((verts n).map (fun v => if outC u && inC v && F.adj u v then 1 else 0)).sum := by
        intro u _
        cases ho : outC u
        · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]; symm; rw [sum_map_const, Nat.mul_zero]
        · simp only [Bool.true_and, ↓reduceIte]; exact length_filter_eq_sum (verts n) _
      rw [sum_map_eq (verts n) _ _ h1, sum_map_eq (verts n) _ _ h2, sum_swap (verts n) (verts n)]
      apply sum_map_eq; intro v _
      apply sum_map_eq; intro u _
      rw [F.symm u v]
      cases inC u <;> cases outC v <;> cases F.adj v u <;> simp
    have hin_eq : (((verts n).filter inC).map (degIn F U)).sum = twoEdgesIn F inC + cross := by
      rw [sum_map_eq _ _ (fun x => degIn F inC x + degIn F outC x) (fun x _ => hpart_deg x),
          sum_map_add, hsym_cross]
      rfl
    have hout_eq : (((verts n).filter outC).map (degIn F U)).sum = cross + twoEdgesIn F outC := by
      rw [sum_map_eq _ _ (fun x => degIn F inC x + degIn F outC x) (fun x _ => hpart_deg x),
          sum_map_add]
      rfl
    rw [hsplit_u, hin_eq, hout_eq]
    omega
  -- Bound each of the 3 pieces:
  have h1_inC : twoEdgesIn F inC ≤ 2 * L := by
    unfold twoEdgesIn
    have hle := sum_map_le ((verts n).filter inC) (degIn F inC) (fun _ => 2)
      (fun v hv => hdeg_inC v (List.mem_filter.mp hv).2)
    rw [sum_map_const] at hle
    change _ ≤ subsetCard inC * 2 at hle
    rw [hinC_card] at hle
    omega
  have h2_cross : cross ≤ 2 * subsetCard outC := by
    dsimp [cross]
    have hle := sum_map_le ((verts n).filter outC) (degIn F inC) (fun _ => 2)
      (fun u hu => hdeg_outC u (List.mem_filter.mp hu).2)
    rw [sum_map_const] at hle
    change _ ≤ subsetCard outC * 2 at hle
    omega
  have h3_outC : 2 * twoEdgesIn F outC ≤ subsetCard outC * subsetCard outC := by
    have htf_out : IsTriangleFreeOn F outC := fun u v w hu hv hw =>
      htf u v w (Bool.and_eq_true _ _ |>.mp hu).1 (Bool.and_eq_true _ _ |>.mp hv).1 (Bool.and_eq_true _ _ |>.mp hw).1
    have hm := mantel_on F outC htf_out
    have h2e := two_mul_edgesIn F outC
    omega
  -- Final algebraic assembly:
  -- 4 * edgesIn F U = 2 * twoEdgesIn F U ≤ 4*L + 8*(m-L) + (m-L)^2
  -- and (m - 1)^2 + 4 = 4*L + 8*(m-L) + (m-L)^2 + (L - 5) * (2*m - L - 1)!
  have h2eU := two_mul_edgesIn F U
  let k := subsetCard outC
  let d := L - 5
  have hL_eq : L = d + 5 := by dsimp [d]; omega
  have hm_eq : subsetCard U = d + 5 + k := by dsimp [k]; omega
  have halg : 4 * (d + 5) + 8 * k + k * k + d * (d + 2 * k + 4) =
      (d + 4 + k) * (d + 4 + k) + 4 := by
    simp only [Nat.add_mul, Nat.mul_add]
    have hdk : d * k = k * d := Nat.mul_comm d k
    have h2dk : d * (2 * k) = 2 * (d * k) := by rw [← Nat.mul_assoc, Nat.mul_comm d 2, Nat.mul_assoc]
    have hd4 : d * 4 = 4 * d := Nat.mul_comm d 4
    have hk4 : k * 4 = 4 * k := Nat.mul_comm k 4
    omega
  have hm1 : subsetCard U - 1 = d + 4 + k := by omega
  rw [hm1]
  have hcomb : 2 * twoEdgesIn F U ≤ 4 * (d + 5) + 8 * k + k * k := by
    dsimp [k]; omega
  omega

/-! ## Section 6: Theorem E — Multi-Color Obstructions for Erdős #617 (`r ≥ 4`) -/

/-- **Theorem E1 (No `(2r+1)`-Subset with Independence Number `≤ 2`):**
    For every `r ≥ 4`, in any balanced `r`-edge-coloring `C` of `K_{r²+1}`,
    no color class `G_c` can contain a `(2r+1)`-vertex subset `U` with `α(G_c[U]) ≤ 2`.
    In particular, none of the `k = 2` single-graph witnesses from Theorem B can ever
    occur as a color class in a balanced `r`-coloring of `K_{r²+1}`. -/
theorem no_2r_plus_1_alpha_le_2 {r : Nat} (hr : r ≥ 4) (C : EdgeColoring (r * r + 1) r)
    (hbal : IsBalanced C) (c : Fin r) (U : Fin (r * r + 1) → Bool)
    (hUcard : subsetCard U = 2 * r + 1) :
    ¬ (∀ I : Fin (r * r + 1) → Bool, (∀ v, I v = true → U v = true) →
        IsIndep (colorClass C c) I → subsetCard I ≤ 2) := by
  intro hα2
  let G := colorClass C c
  let F := G.compl
  -- Step 1: F[U] is triangle-free (a triangle in F[U] is a 3-IS in G[U])
  have htf : IsTriangleFreeOn F U := by
    intro u v w hUu hUv hUw huv hvw
    cases huw : F.adj u w
    · rfl
    · exfalso
      -- {u, v, w} are pairwise distinct and pairwise non-adjacent in G
      have hne_uv : u ≠ v := by
        unfold F SGraph.compl at huv; simp only [Bool.and_eq_true, decide_eq_true_eq] at huv; exact huv.1
      have hne_vw : v ≠ w := by
        unfold F SGraph.compl at hvw; simp only [Bool.and_eq_true, decide_eq_true_eq] at hvw; exact hvw.1
      have hne_uw : u ≠ w := by
        unfold F SGraph.compl at huw; simp only [Bool.and_eq_true, decide_eq_true_eq] at huw; exact huw.1
      have hGuv : G.adj u v = false := by
        unfold F SGraph.compl at huv; simp at huv; exact huv.2
      have hGvw : G.adj v w = false := by
        unfold F SGraph.compl at hvw; simp at hvw; exact hvw.2
      have hGuw : G.adj u w = false := by
        unfold F SGraph.compl at huw; simp at huw; exact huw.2
      let I : Fin (r * r + 1) → Bool := fun x => decide (x = u) || decide (x = v) || decide (x = w)
      have hIsub : ∀ x, I x = true → U x = true := by
        intro x hx; simp [I] at hx
        rcases hx with (rfl | rfl) | rfl <;> assumption
      have hIind : IsIndep G I := by
        intro a b ha hb; simp [I] at ha hb
        rcases ha with (rfl | rfl) | rfl <;> rcases hb with (rfl | rfl) | rfl
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
        have hp1 := filter_length_partition (verts (r * r + 1)) I (fun x => decide (x = u))
        have h1 : ((verts (r * r + 1)).filter (fun x => I x && decide (x = u))).length = 1 := by
          have heq : ((verts (r * r + 1)).filter (fun x => I x && decide (x = u))).length =
                     ((verts (r * r + 1)).filter (fun x => decide (x = u))).length := by
            apply filter_length_eq; intro x _
            by_cases hx : x = u <;> simp [I, hx]
          rw [heq]; exact length_filter_eq_one_of_nodup (verts _) (nodup_verts _) u (mem_verts u)
        let I2 : Fin (r * r + 1) → Bool := fun x => I x && !decide (x = u)
        have hp2 := filter_length_partition (verts (r * r + 1)) I2 (fun x => decide (x = v))
        have h2 : ((verts (r * r + 1)).filter (fun x => I2 x && decide (x = v))).length = 1 := by
          have heq : ((verts (r * r + 1)).filter (fun x => I2 x && decide (x = v))).length =
                     ((verts (r * r + 1)).filter (fun x => decide (x = v))).length := by
            apply filter_length_eq; intro x _
            by_cases hx : x = v
            · subst hx; simp [I2, I, Ne.symm hne_uv]
            · simp [hx]
          rw [heq]; exact length_filter_eq_one_of_nodup (verts _) (nodup_verts _) v (mem_verts v)
        have h3 : ((verts (r * r + 1)).filter (fun x => I2 x && !decide (x = v))).length = 1 := by
          have heq : ((verts (r * r + 1)).filter (fun x => I2 x && !decide (x = v))).length =
                     ((verts (r * r + 1)).filter (fun x => decide (x = w))).length := by
            apply filter_length_eq; intro x _
            by_cases hx : x = w
            · subst hx; simp [I2, I, Ne.symm hne_uw, Ne.symm hne_vw]
            · by_cases hxu : x = u
              · subst hxu; simp [I2, hx]
              · by_cases hxv : x = v
                · subst hxv; simp [I2, hx]
                · simp [I2, I, hx, hxu, hxv]
          rw [heq]; exact length_filter_eq_one_of_nodup (verts _) (nodup_verts _) w (mem_verts w)
        dsimp [I2] at hp2 h2 h3
        omega
      have hle := hα2 I hIsub hIind
      omega
  -- Step 2: By Theorem C, edgesIn F U ≥ (r - 1) * (r + 2)
  have hlb := multiscale_2r_plus_1 C hbal c U hUcard
  -- Step 3: F[U] must be bipartite (otherwise Theorem D gives edgesIn F U ≤ r² + 1 < (r-1)*(r+2))
  have hbip : IsBipartiteOn F U := by
    apply Classical.byContradiction
    intro hnb
    have hub := non_bipartite_mantel F U htf hnb (by omega)
    rw [hUcard] at hub
    dsimp [F, G] at hub
    have h1 : 2 * r * (2 * r) + 4 = 4 * (r * r + 1) := by
      have : 2 * r * (2 * r) = 4 * (r * r) := by
        rw [Nat.mul_assoc 2 r (2 * r), ← Nat.mul_assoc r 2 r, Nat.mul_comm r 2,
            Nat.mul_assoc 2 r r, ← Nat.mul_assoc 2 2 (r * r)]
      omega
    have h2 : (r - 1) * (r + 2) = r * r + r - 2 := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
      have : 4 + k - 1 = k + 3 := by omega
      rw [this]
      simp only [Nat.add_mul, Nat.mul_add]
      have : k * 4 = 4 * k := Nat.mul_comm k 4
      have : k * 2 = 2 * k := Nat.mul_comm k 2
      omega
    rw [h1] at hub
    rw [h2] at hlb
    omega
  -- Step 4: Bipartite F[U] has an independent set A of size ≥ r + 1, contradicting balanced_compl_r_plus_1
  obtain ⟨side, hside⟩ := hbip
  let A0 : Fin (r * r + 1) → Bool := fun v => U v && side v
  let A1 : Fin (r * r + 1) → Bool := fun v => U v && !side v
  have hpart : subsetCard U = subsetCard A0 + subsetCard A1 := by
    unfold subsetCard; exact filter_length_partition (verts _) U side
  have hindA0 : IsIndep F A0 := by
    intro u v hu hv
    simp only [A0, Bool.and_eq_true] at hu hv
    cases hadj : F.adj u v
    · rfl
    · exfalso; exact hside u v hu.1 hv.1 hadj (by rw [hu.2, hv.2])
  have hindA1 : IsIndep F A1 := by
    intro u v hu hv
    simp only [A1, Bool.and_eq_true, Bool.not_eq_true'] at hu hv
    cases hadj : F.adj u v
    · rfl
    · exfalso; exact hside u v hu.1 hv.1 hadj (by rw [hu.2, hv.2])
  have hcontra : ∀ A : Fin (r * r + 1) → Bool, IsIndep F A → subsetCard A ≥ r + 1 → False := by
    intro A hindA hge
    obtain ⟨S, hsub, hScard⟩ := exists_sub_card A (r + 1) hge
    have hindS : IsIndep F S := isIndep_mono hsub hindA
    have h0 : edgesIn F S = 0 := (isIndep_iff_edgesIn_zero F S).mp hindS
    dsimp [F, G] at h0
    have hge1 := balanced_compl_r_plus_1 C hbal c S hScard
    omega
  by_cases hA0 : subsetCard A0 ≥ r + 1
  · exact hcontra A0 hindA0 hA0
  · exact hcontra A1 hindA1 (by omega)

/-- Closed neighborhood of a subset `I` in `G`. -/
def closedNbr {n : Nat} (G : SGraph n) (I : Fin n → Bool) (v : Fin n) : Bool :=
  I v || ((verts n).any (fun u => I u && G.adj u v))

theorem closedNbr_true_iff {n : Nat} (G : SGraph n) (I : Fin n → Bool) (v : Fin n) :
    closedNbr G I v = true ↔ I v = true ∨ ∃ u : Fin n, I u = true ∧ G.adj u v = true := by
  unfold closedNbr
  simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro (h | ⟨u, _, hIu, hadj⟩)
    · exact Or.inl h
    · exact Or.inr ⟨u, hIu, hadj⟩
  · rintro (h | ⟨u, hIu, hadj⟩)
    · exact Or.inl h
    · exact Or.inr ⟨u, mem_verts u, hIu, hadj⟩

/-- Union bound: `|N_G[I]| ≤ ∑_{u ∈ I} (deg G u + 1)`. -/
theorem subsetCard_closedNbr_le {n : Nat} (G : SGraph n) (I : Fin n → Bool) :
    subsetCard (closedNbr G I) ≤ (((verts n).filter I).map (fun u => deg G u + 1)).sum := by
  unfold subsetCard
  rw [length_filter_eq_sum, sum_filter_eq_sum_ite]
  have h1 : ∀ u ∈ verts n,
      (if I u then deg G u + 1 else 0) =
      ((verts n).map (fun v => if I u && (decide (v = u) || G.adj u v) then 1 else 0)).sum := by
    intro u _
    cases hIu : I u
    · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]; symm; rw [sum_map_const, Nat.mul_zero]
    · simp only [Bool.true_and, ↓reduceIte]
      rw [← length_filter_eq_sum]
      have hp := filter_length_partition (verts n) (fun v => decide (v = u) || G.adj u v) (fun v => decide (v = u))
      have ha : ((verts n).filter (fun v => (decide (v = u) || G.adj u v) && decide (v = u))).length = 1 := by
        have heq : ((verts n).filter (fun v => (decide (v = u) || G.adj u v) && decide (v = u))).length =
                   ((verts n).filter (fun v => decide (v = u))).length := by
          apply filter_length_eq; intro v _; by_cases hv : v = u <;> simp [hv]
        rw [heq]; exact length_filter_eq_one_of_nodup (verts n) (nodup_verts n) u (mem_verts u)
      have hb : ((verts n).filter (fun v => (decide (v = u) || G.adj u v) && !decide (v = u))).length = deg G u := by
        unfold deg degIn
        apply filter_length_eq; intro v _
        by_cases hv : v = u
        · rw [hv]; simp [G.loopless u]
        · simp [hv]
      omega
  rw [sum_map_eq (verts n) _ _ h1, sum_swap (verts n) (verts n)]
  apply sum_map_le; intro v _
  cases hcn : closedNbr G I v
  · simp
  · simp only [↓reduceIte]
    rcases (closedNbr_true_iff G I v).mp hcn with hIv | ⟨u, hIu, hadj⟩
    · have hmem : (1 : Nat) ∈ (verts n).map (fun u => if I u && (decide (v = u) || G.adj u v) then 1 else 0) :=
        List.mem_map.mpr ⟨v, mem_verts v, by simp [hIv]⟩
      exact le_sum_of_mem hmem
    · have hmem : (1 : Nat) ∈ (verts n).map (fun u => if I u && (decide (v = u) || G.adj u v) then 1 else 0) :=
        List.mem_map.mpr ⟨u, mem_verts u, by simp [hIu, hadj]⟩
      exact le_sum_of_mem hmem

/-- **Theorem E2 (Closed-Neighborhood and Degree-Sum Bound on `(r-2)`-Independent Sets):**
    For `r ≥ 4`, in any balanced `r`-coloring of `K_{r²+1}`, every `(r-2)`-independent set `I`
    in any color class `G_c` satisfies:
      1. `|N_{G_c}[I]| ≥ (r - 1)²`,
      2. `∑_{u ∈ I} deg(G_c, u) ≥ (r - 2) * (r - 1) + 1`. -/
theorem indep_r_minus_2_bounds {r : Nat} (hr : r ≥ 4) (C : EdgeColoring (r * r + 1) r)
    (hbal : IsBalanced C) (c : Fin r) (I : Fin (r * r + 1) → Bool)
    (hind : IsIndep (colorClass C c) I) (hIcard : subsetCard I = r - 2) :
    subsetCard (closedNbr (colorClass C c) I) ≥ (r - 1) * (r - 1) ∧
    (((verts (r * r + 1)).filter I).map (deg (colorClass C c))).sum ≥ (r - 2) * (r - 1) + 1 := by
  let G := colorClass C c
  let R : Fin (r * r + 1) → Bool := fun v => !closedNbr G I v
  -- Any independent set J ⊆ R has size ≤ 2 (else I ∪ J is an independent set of size > r!)
  have hαR : ∀ J : Fin (r * r + 1) → Bool, (∀ v, J v = true → R v = true) →
      IsIndep G J → subsetCard J ≤ 2 := by
    intro J hJsub hJind
    -- I and J are disjoint since J ⊆ R = !closedNbr G I
    let IJ : Fin (r * r + 1) → Bool := fun v => I v || J v
    have hdisj : ∀ v, I v = true → J v = false := by
      intro v hIv
      cases hJv : J v
      · rfl
      · exfalso
        have hRv := hJsub v hJv
        have hcn : closedNbr G I v = true := (closedNbr_true_iff G I v).mpr (Or.inl hIv)
        simp [R, hcn] at hRv
    have hIJcard : subsetCard IJ = subsetCard I + subsetCard J := by
      unfold subsetCard
      have hp := filter_length_partition (verts _) IJ I
      have h1 : ((verts _).filter (fun v => IJ v && I v)).length = ((verts _).filter I).length := by
        apply filter_length_eq; intro v _; cases hIv : I v <;> simp [IJ, hIv]
      have h2 : ((verts _).filter (fun v => IJ v && !I v)).length = ((verts _).filter J).length := by
        apply filter_length_eq; intro v _
        cases hIv : I v
        · simp [IJ, hIv]
        · simp [IJ, hIv, hdisj v hIv]
      omega
    have hIJind : IsIndep G IJ := by
      intro u v hu hv
      simp only [IJ, Bool.or_eq_true] at hu hv
      rcases hu with hIu | hJu <;> rcases hv with hIv | hJv
      · exact hind u v hIu hIv
      · have hRv := hJsub v hJv
        cases hadj : G.adj u v
        · rfl
        · exfalso
          have hcn : closedNbr G I v = true := (closedNbr_true_iff G I v).mpr (Or.inr ⟨u, hIu, hadj⟩)
          simp [R, hcn] at hRv
      · have hRu := hJsub u hJu
        cases hadj : G.adj u v
        · rfl
        · exfalso
          have hcn : closedNbr G I u = true :=
            (closedNbr_true_iff G I u).mpr (Or.inr ⟨v, hIv, by rw [G.symm]; exact hadj⟩)
          simp [R, hcn] at hRu
      · exact hJind u v hJu hJv
    have hle := isBalanced_indep_le C hbal c IJ hIJind
    omega
  -- Therefore |R| ≤ 2*r (else take a (2*r+1)-subset U ⊆ R, contradicting Theorem E1!)
  have hRle : subsetCard R ≤ 2 * r := by
    by_cases hle : subsetCard R ≤ 2 * r
    · exact hle
    · exfalso
      obtain ⟨U, hUsub, hUcard⟩ := exists_sub_card R (2 * r + 1) (by omega)
      exact no_2r_plus_1_alpha_le_2 hr C hbal c U hUcard
        (fun J hJU hJind => hαR J (fun v hv => hUsub v (hJU v hv)) hJind)
  -- |N[I]| + |R| = r² + 1 => |N[I]| ≥ r² + 1 - 2*r = (r - 1)²
  have htot : subsetCard (closedNbr G I) + subsetCard R = r * r + 1 := by
    have hp := filter_length_partition (verts (r * r + 1)) (fun _ => true) (closedNbr G I)
    rw [filter_true_eq, length_verts] at hp
    have h1 : ((verts (r * r + 1)).filter (fun v => true && closedNbr G I v)).length = subsetCard (closedNbr G I) := rfl
    have h2 : ((verts (r * r + 1)).filter (fun v => true && !closedNbr G I v)).length = subsetCard R := rfl
    omega
  have hsq : (r - 1) * (r - 1) + 2 * r = r * r + 1 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
    have : 4 + k - 1 = k + 3 := by omega
    rw [this]
    simp only [Nat.add_mul, Nat.mul_add]
    have : k * 4 = 4 * k := Nat.mul_comm k 4
    have : k * 3 = 3 * k := Nat.mul_comm k 3
    omega
  have hNge : subsetCard (closedNbr G I) ≥ (r - 1) * (r - 1) := by omega
  refine ⟨hNge, ?_⟩
  have hub := subsetCard_closedNbr_le G I
  rw [sum_map_add, sum_map_const] at hub
  change subsetCard (closedNbr G I) ≤ (((verts (r * r + 1)).filter I).map (deg G)).sum + subsetCard I * 1 at hub
  rw [hIcard, Nat.mul_one] at hub
  dsimp [G] at hub hNge
  have hmul : (r - 1) * (r - 1) = (r - 2) * (r - 1) + (r - 1) := by
    have h1 : r - 1 = (r - 2) + 1 := by omega
    have h2 : ((r - 2) + 1) * (r - 1) = (r - 2) * (r - 1) + (r - 1) := by
      rw [Nat.add_mul, Nat.one_mul]
    rw [← h1] at h2
    exact h2
  omega

/-- **Theorem E3 (Low-Degree Independence Bound):**
    For every `r ≥ 4`, in any balanced `r`-coloring of `K_{r²+1}`, the set of vertices of
    degree `≤ r - 1` in any color class `G_c` has independence number at most `r - 3`. -/
theorem low_degree_alpha_bound {r : Nat} (hr : r ≥ 4) (C : EdgeColoring (r * r + 1) r)
    (hbal : IsBalanced C) (c : Fin r) (I : Fin (r * r + 1) → Bool)
    (hind : IsIndep (colorClass C c) I)
    (hlow : ∀ v, I v = true → deg (colorClass C c) v ≤ r - 1) :
    subsetCard I ≤ r - 3 := by
  by_cases hle : subsetCard I ≤ r - 3
  · exact hle
  · exfalso
    obtain ⟨I', hsub, hcard⟩ := exists_sub_card I (r - 2) (by omega)
    have hind' : IsIndep (colorClass C c) I' := isIndep_mono hsub hind
    have ⟨_, hsum_lb⟩ := indep_r_minus_2_bounds hr C hbal c I' hind' hcard
    have hsum_ub : (((verts (r * r + 1)).filter I').map (deg (colorClass C c))).sum ≤ (r - 2) * (r - 1) := by
      have h := sum_map_le ((verts (r * r + 1)).filter I') (deg (colorClass C c)) (fun _ => r - 1)
        (fun v hv => hlow v (hsub v (List.mem_filter.mp hv).2))
      rw [sum_map_const] at h
      change _ ≤ subsetCard I' * (r - 1) at h
      rw [hcard] at h
      exact h
    omega

end Erdos617
