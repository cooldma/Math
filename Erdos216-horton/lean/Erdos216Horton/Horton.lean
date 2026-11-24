import Mathlib

/-!
# Horton sets: no empty convex 7-gon (Erdős Problem 216)

Erdős asked whether, for every `k`, there is a number `g(k)` such that any `g(k)` points in
general position in the plane contain an *empty* convex `k`-gon (one whose convex hull contains
no other point of the set).  Horton (1983) showed the answer is **no** for `k = 7`: there are
arbitrarily large sets in general position with no empty convex heptagon.

This file formalizes Horton's construction and proof.

## Setup

Points are `(i, f i)` for `i < 2^K`, and `O f i j k` is the orientation determinant.  A height
function `f` is *Horton* at level `K + 1` if its even-indexed and odd-indexed halves are Horton at
level `K` and one half lies "deep below" the other: every line through two points of the low half
passes below every point of the high half, and every line through two points of the high half
passes above every point of the low half.

## Proof

* `no_open_cup`: a Horton set contains no *open* 4-cup (four points forming a convex chain seen
  from below, with no point of the set above the chain inside its `x`-range).
* `bad`: every 7 points of a Horton set either fail to be in convex position or have another
  point of the set inside their convex hull.  The points in the low half form a cup, and those in
  the high half form a cap; one half contains at least 4 of them, giving an open 4-cup (or 4-cap)
  in a smaller Horton set.
* `exists_horton`: Horton sets of every size `2^K` exist.

The final statements are `Erdos216.horton` and `Erdos216.erdos_216`.
-/

namespace Horton

noncomputable section

/-- Orientation of `(i, f i), (j, f j), (k, f k)`; positive iff they turn counterclockwise. -/
def O (f : ℕ → ℝ) (i j k : ℕ) : ℝ :=
  ((j : ℝ) - i) * (f k - f i) - (f j - f i) * ((k : ℝ) - i)

lemma O_swap (f : ℕ → ℝ) (i j k : ℕ) : O f j i k = -O f i j k := by unfold O; ring
lemma O_swap23 (f : ℕ → ℝ) (i j k : ℕ) : O f i k j = -O f i j k := by unfold O; ring
lemma O_cyc (f : ℕ → ℝ) (i j k : ℕ) : O f j k i = O f i j k := by unfold O; ring
lemma O_neg (f : ℕ → ℝ) (i j k : ℕ) : O (fun t => -f t) i j k = -O f i j k := by unfold O; ring
lemma O_add (f : ℕ → ℝ) (c : ℝ) (i j k : ℕ) : O (fun t => f t + c) i j k = O f i j k := by
  unfold O; ring

lemma O_sub (f : ℕ → ℝ) (e i j k : ℕ) :
    O f (2 * i + e) (2 * j + e) (2 * k + e) = 2 * O (fun t => f (2 * t + e)) i j k := by
  unfold O; push_cast; ring

lemma O_sub' (f : ℕ → ℝ) {e x y z : ℕ} (hx : x % 2 = e) (hy : y % 2 = e) (hz : z % 2 = e) :
    O f x y z = 2 * O (fun t => f (2 * t + e)) (x / 2) (y / 2) (z / 2) := by
  have he : e < 2 := by omega
  obtain ⟨a, rfl⟩ : ∃ a, x = 2 * a + e := ⟨x / 2, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, y = 2 * b + e := ⟨y / 2, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, z = 2 * c + e := ⟨z / 2, by omega⟩
  rw [show (2 * a + e) / 2 = a by omega, show (2 * b + e) / 2 = b by omega,
    show (2 * c + e) / 2 = c by omega]
  exact O_sub f e a b c

/-- The points of parity `lo` lie deep below the points of parity `hi`. -/
def DB (K : ℕ) (f : ℕ → ℝ) (lo hi : ℕ) : Prop :=
  ∀ i j m, i < j → j < 2 ^ K → m < 2 ^ K →
    0 < O f (2 * i + lo) (2 * j + lo) (2 * m + hi) ∧
      O f (2 * i + hi) (2 * j + hi) (2 * m + lo) < 0

/-- `IsHorton K f`: the points `(i, f i)`, `i < 2^K`, form a Horton set. -/
def IsHorton : ℕ → (ℕ → ℝ) → Prop
  | 0, _ => True
  | K + 1, f => IsHorton K (fun i => f (2 * i + 0)) ∧ IsHorton K (fun i => f (2 * i + 1)) ∧
      (DB K f 0 1 ∨ DB K f 1 0)

lemma DB.above {K : ℕ} {f : ℕ → ℝ} {lo hi : ℕ} (h : DB K f lo hi) {x y z : ℕ} (hxy : x < y)
    (hy : y < 2 ^ (K + 1)) (hz : z < 2 ^ (K + 1)) (hx2 : x % 2 = lo) (hy2 : y % 2 = lo)
    (hz2 : z % 2 = hi) : 0 < O f x y z := by
  rw [pow_succ] at hy hz
  have := (h (x / 2) (y / 2) (z / 2) (by omega) (by omega) (by omega)).1
  rwa [show 2 * (x / 2) + lo = x by omega, show 2 * (y / 2) + lo = y by omega,
    show 2 * (z / 2) + hi = z by omega] at this

lemma DB.below {K : ℕ} {f : ℕ → ℝ} {lo hi : ℕ} (h : DB K f lo hi) {x y z : ℕ} (hxy : x < y)
    (hy : y < 2 ^ (K + 1)) (hz : z < 2 ^ (K + 1)) (hx2 : x % 2 = hi) (hy2 : y % 2 = hi)
    (hz2 : z % 2 = lo) : O f x y z < 0 := by
  rw [pow_succ] at hy hz
  have := (h (x / 2) (y / 2) (z / 2) (by omega) (by omega) (by omega)).2
  rwa [show 2 * (x / 2) + hi = x by omega, show 2 * (y / 2) + hi = y by omega,
    show 2 * (z / 2) + lo = z by omega] at this

lemma DB_neg {K : ℕ} {f : ℕ → ℝ} {lo hi : ℕ} (h : DB K f lo hi) :
    DB K (fun t => -f t) hi lo := by
  intro i j m hij hj hm
  obtain ⟨h1, h2⟩ := h i j m hij hj hm
  rw [O_neg, O_neg]
  constructor <;> linarith

lemma DB_add {K : ℕ} {f : ℕ → ℝ} {lo hi : ℕ} (h : DB K f lo hi) (c : ℝ) :
    DB K (fun t => f t + c) lo hi := by
  intro i j m hij hj hm
  rw [O_add, O_add]
  exact h i j m hij hj hm

lemma Horton_neg : ∀ (K : ℕ) (f : ℕ → ℝ), IsHorton K f → IsHorton K (fun t => -f t) := by
  intro K
  induction K with
  | zero => intro f _; trivial
  | succ K ih =>
    intro f h
    obtain ⟨h0, h1, hd⟩ := h
    exact ⟨ih _ h0, ih _ h1, hd.elim (fun d => Or.inr (DB_neg d)) (fun d => Or.inl (DB_neg d))⟩

lemma Horton_add : ∀ (K : ℕ) (f : ℕ → ℝ), IsHorton K f → ∀ c : ℝ, IsHorton K (fun t => f t + c) := by
  intro K
  induction K with
  | zero => intro f _ _; trivial
  | succ K ih =>
    intro f h c
    obtain ⟨h0, h1, hd⟩ := h
    exact ⟨ih _ h0 c, ih _ h1 c, hd.elim (fun d => Or.inl (DB_add d c))
      (fun d => Or.inr (DB_add d c))⟩

lemma Horton_sub {K : ℕ} {f : ℕ → ℝ} {e : ℕ} (he : e < 2) (h : IsHorton (K + 1) f) :
    IsHorton K (fun i => f (2 * i + e)) := by
  interval_cases e
  · exact h.1
  · exact h.2.1

/-! ### General position -/

lemma pair_ne {K : ℕ} {f : ℕ → ℝ} {lo hi : ℕ} (hd : DB K f lo hi) (hlh : lo + hi = 1)
    {s t r : ℕ} (hst : s < t) (ht : t < 2 ^ (K + 1)) (hr : r < 2 ^ (K + 1))
    (hp : s % 2 = t % 2) (hq : r % 2 ≠ s % 2) : O f s t r ≠ 0 := by
  rcases (show s % 2 = lo ∨ s % 2 = hi by omega) with h | h
  · exact (hd.above hst ht hr h (by omega) (by omega)).ne'
  · exact (hd.below hst ht hr h (by omega) (by omega)).ne

lemma gp_lt : ∀ (K : ℕ) (f : ℕ → ℝ), IsHorton K f →
    ∀ x y z, x < y → y < z → z < 2 ^ K → O f x y z ≠ 0 := by
  intro K
  induction K with
  | zero => intro f _ x y z h1 h2 h3; simp at h3; omega
  | succ K ih =>
    intro f hf x y z hxy hyz hz
    by_cases hsame : x % 2 = y % 2 ∧ y % 2 = z % 2
    · rw [O_sub' f (e := x % 2) rfl hsame.1.symm (hsame.1.trans hsame.2).symm]
      have hp : 2 ^ (K + 1) = 2 * 2 ^ K := by ring
      exact mul_ne_zero two_ne_zero
        (ih _ (Horton_sub (Nat.mod_lt _ two_pos) hf) _ _ _ (by omega) (by omega) (by omega))
    · obtain ⟨-, -, hd⟩ := hf
      obtain ⟨lo, hi, hlh, hd⟩ : ∃ lo hi, lo + hi = 1 ∧ DB K f lo hi := by
        rcases hd with hd | hd
        exacts [⟨0, 1, rfl, hd⟩, ⟨1, 0, rfl, hd⟩]
      by_cases hxy2 : x % 2 = y % 2
      · exact pair_ne hd hlh hxy (by omega) hz hxy2 (by omega)
      by_cases hxz2 : x % 2 = z % 2
      · have := pair_ne (s := x) (t := z) (r := y) hd hlh (by omega) hz (by omega) hxz2
          (by omega)
        intro h0; apply this; rw [O_swap23 f x y z, h0, neg_zero]
      · have := pair_ne (s := y) (t := z) (r := x) hd hlh hyz hz (by omega) (by omega)
          (by omega)
        rwa [O_cyc f x y z] at this

lemma gp {K : ℕ} {f : ℕ → ℝ} (hf : IsHorton K f) :
    ∀ x y z, x < 2 ^ K → y < 2 ^ K → z < 2 ^ K → x ≠ y → y ≠ z → x ≠ z → O f x y z ≠ 0 := by
  intro x y z hx hy hz hxy hyz hxz h0
  have i1 := O_cyc f x y z
  have i2 := O_cyc f y z x
  have i3 := O_swap f x y z
  have i4 := O_swap f z x y
  have i5 := O_swap f y z x
  rcases Nat.lt_or_gt_of_ne hxy with h1 | h1 <;> rcases Nat.lt_or_gt_of_ne hyz with h2 | h2 <;>
    rcases Nat.lt_or_gt_of_ne hxz with h3 | h3
  all_goals first
    | omega
    | exact gp_lt K f hf x y z (by omega) (by omega) (by omega) (by linarith)
    | exact gp_lt K f hf x z y (by omega) (by omega) (by omega) (by linarith)
    | exact gp_lt K f hf y x z (by omega) (by omega) (by omega) (by linarith)
    | exact gp_lt K f hf y z x (by omega) (by omega) (by omega) (by linarith)
    | exact gp_lt K f hf z x y (by omega) (by omega) (by omega) (by linarith)
    | exact gp_lt K f hf z y x (by omega) (by omega) (by omega) (by linarith)

/-! ### No open 4-cups -/

/-- `a < b < c < d` form a cup (convex chain seen from below) with no point of the set above
the chain within its `x`-range. -/
def OpenCup (K : ℕ) (f : ℕ → ℝ) (a b c d : ℕ) : Prop :=
  a < b ∧ b < c ∧ c < d ∧ d < 2 ^ K ∧
  0 < O f a b c ∧ 0 < O f a b d ∧ 0 < O f a c d ∧ 0 < O f b c d ∧
  (∀ p, a < p → p < b → O f a b p < 0) ∧ (∀ p, b < p → p < c → O f b c p < 0) ∧
  (∀ p, c < p → p < d → O f c d p < 0)

lemma sub_open {K : ℕ} {f : ℕ → ℝ} {a b c d e : ℕ} (h : OpenCup (K + 1) f a b c d)
    (ha : a % 2 = e) (hb : b % 2 = e) (hc : c % 2 = e) (hd : d % 2 = e) :
    OpenCup K (fun t => f (2 * t + e)) (a / 2) (b / 2) (c / 2) (d / 2) := by
  obtain ⟨hab, hbc, hcd, hdK, o1, o2, o3, o4, p1, p2, p3⟩ := h
  rw [pow_succ] at hdK
  have key := fun x y z (hx : x % 2 = e) (hy : y % 2 = e) (hz : z % 2 = e) => O_sub' f hx hy hz
  refine ⟨by omega, by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := key a b c ha hb hc; linarith
  · have := key a b d ha hb hd; linarith
  · have := key a c d ha hc hd; linarith
  · have := key b c d hb hc hd; linarith
  · intro p h1 h2
    have := p1 (2 * p + e) (by omega) (by omega)
    have h3 := key a b (2 * p + e) ha hb (by omega)
    rw [show (2 * p + e) / 2 = p by omega] at h3
    linarith
  · intro p h1 h2
    have := p2 (2 * p + e) (by omega) (by omega)
    have h3 := key b c (2 * p + e) hb hc (by omega)
    rw [show (2 * p + e) / 2 = p by omega] at h3
    linarith
  · intro p h1 h2
    have := p3 (2 * p + e) (by omega) (by omega)
    have h3 := key c d (2 * p + e) hc hd (by omega)
    rw [show (2 * p + e) / 2 = p by omega] at h3
    linarith

/-- In an open 4-cup of a set whose `lo` half is deep below its `hi` half, all four points
lie in the `hi` half. -/
lemma all_hi {K : ℕ} {f : ℕ → ℝ} {lo hi a b c d : ℕ} (hd : DB K f lo hi) (hlh : lo + hi = 1)
    (h : OpenCup (K + 1) f a b c d) :
    a % 2 = hi ∧ b % 2 = hi ∧ c % 2 = hi ∧ d % 2 = hi := by
  obtain ⟨hab, hbc, hcd, hdK, o1, o2, o3, o4, p1, p2, p3⟩ := h
  have tri : ∀ x y z, x < y → y < z → z < 2 ^ (K + 1) → 0 < O f x y z →
      ¬(x % 2 = lo ∧ y % 2 = hi ∧ z % 2 = lo) ∧ ¬(x % 2 = hi ∧ y % 2 = hi ∧ z % 2 = lo) ∧
        ¬(x % 2 = lo ∧ y % 2 = hi ∧ z % 2 = hi) := by
    intro x y z hxy hyz hz ho
    refine ⟨fun ⟨h1, h2, h3⟩ => ?_, fun ⟨h1, h2, h3⟩ => ?_, fun ⟨h1, h2, h3⟩ => ?_⟩
    · have := hd.above (show x < z by omega) hz (by omega) h1 h3 h2
      linarith [O_swap23 f x y z]
    · have := hd.below hxy (by omega) hz h1 h2 h3
      linarith
    · have := hd.below hyz hz (by omega) h2 h3 h1
      linarith [O_cyc f x y z]
  have cons : ∀ x y, x < y → y < 2 ^ (K + 1) → (∀ p, x < p → p < y → O f x y p < 0) →
      ¬(x % 2 = lo ∧ y % 2 = lo) := by
    rintro x y hxy hy hop ⟨h1, h2⟩
    have := hd.above hxy hy (show x + 1 < 2 ^ (K + 1) by omega) h1 h2 (by omega)
    have := hop (x + 1) (by omega) (by omega)
    linarith
  have t1 := tri a b c hab hbc (by omega) o1
  have t2 := tri a b d hab (by omega) hdK o2
  have t3 := tri a c d (by omega) hcd hdK o3
  have t4 := tri b c d hbc hcd hdK o4
  have c1 := cons a b hab (by omega) p1
  have c2 := cons b c hbc (by omega) p2
  have c3 := cons c d hcd hdK p3
  have pa : a % 2 = lo ∨ a % 2 = hi := by omega
  have pb : b % 2 = lo ∨ b % 2 = hi := by omega
  have pc : c % 2 = lo ∨ c % 2 = hi := by omega
  have pd : d % 2 = lo ∨ d % 2 = hi := by omega
  clear o1 o2 o3 o4 p1 p2 p3 tri cons
  rcases pa with ha | ha <;> rcases pb with hb | hb <;> rcases pc with hc | hc <;>
    rcases pd with hd' | hd'
  all_goals first
    | exact ⟨ha, hb, hc, hd'⟩
    | exact (c1 ⟨ha, hb⟩).elim
    | exact (c2 ⟨hb, hc⟩).elim
    | exact (c3 ⟨hc, hd'⟩).elim
    | exact (t1.1 ⟨ha, hb, hc⟩).elim
    | exact (t1.2.1 ⟨ha, hb, hc⟩).elim
    | exact (t1.2.2 ⟨ha, hb, hc⟩).elim
    | exact (t2.1 ⟨ha, hb, hd'⟩).elim
    | exact (t2.2.1 ⟨ha, hb, hd'⟩).elim
    | exact (t2.2.2 ⟨ha, hb, hd'⟩).elim
    | exact (t3.1 ⟨ha, hc, hd'⟩).elim
    | exact (t3.2.1 ⟨ha, hc, hd'⟩).elim
    | exact (t3.2.2 ⟨ha, hc, hd'⟩).elim
    | exact (t4.1 ⟨hb, hc, hd'⟩).elim
    | exact (t4.2.1 ⟨hb, hc, hd'⟩).elim
    | exact (t4.2.2 ⟨hb, hc, hd'⟩).elim

theorem no_open_cup : ∀ (K : ℕ) (f : ℕ → ℝ), IsHorton K f → ∀ a b c d, ¬OpenCup K f a b c d := by
  intro K
  induction K with
  | zero =>
    intro f _ a b c d h
    obtain ⟨h1, h2, h3, h4, -⟩ := h
    simp at h4; omega
  | succ K ih =>
    intro f hf a b c d h
    obtain ⟨h0, h1, hdb⟩ := hf
    have go : ∀ lo hi, lo + hi = 1 → DB K f lo hi → IsHorton K (fun t => f (2 * t + hi)) →
        False := by
      intro lo hi hlh hd hH
      obtain ⟨pa, pb, pc, pd⟩ := all_hi hd hlh h
      exact ih _ hH _ _ _ _ (sub_open h pa pb pc pd)
    rcases hdb with hd | hd
    · exact go 0 1 rfl hd h1
    · exact go 1 0 rfl hd h0

/-! ### No empty convex 7-gon -/

/-- `p` lies strictly inside the counterclockwise triangle `u v w`. -/
def Tri (f : ℕ → ℝ) (p u v w : ℕ) : Prop :=
  0 < O f u v p ∧ 0 < O f v w p ∧ 0 < O f w u p

/-- Either some point of `X` lies inside a triangle of three others (so `X` is not in convex
position), or some other point of the set lies inside a triangle on `X` (so `X` is not empty). -/
def Bad (K : ℕ) (f : ℕ → ℝ) (X : Finset ℕ) : Prop :=
  (∃ x ∈ X, ∃ u ∈ X, ∃ v ∈ X, ∃ w ∈ X, u ≠ x ∧ v ≠ x ∧ w ≠ x ∧ Tri f x u v w) ∨
  (∃ p, p < 2 ^ K ∧ p ∉ X ∧ ∃ u ∈ X, ∃ v ∈ X, ∃ w ∈ X, Tri f p u v w)

lemma Tri_neg {f : ℕ → ℝ} {p u v w : ℕ} (h : Tri (fun t => -f t) p u v w) : Tri f p w v u := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [O_neg] at h1 h2 h3
  refine ⟨?_, ?_, ?_⟩
  · linarith [O_swap f v w p]
  · linarith [O_swap f u v p]
  · linarith [O_swap f w u p]

lemma Bad_neg {K : ℕ} {f : ℕ → ℝ} {X : Finset ℕ} (h : Bad K (fun t => -f t) X) : Bad K f X := by
  rcases h with ⟨x, hx, u, hu, v, hv, w, hw, h1, h2, h3, ht⟩ | ⟨p, hp, hpX, u, hu, v, hv, w, hw, ht⟩
  · exact Or.inl ⟨x, hx, w, hw, v, hv, u, hu, h3, h2, h1, Tri_neg ht⟩
  · exact Or.inr ⟨p, hp, hpX, w, hw, v, hv, u, hu, Tri_neg ht⟩

lemma Tri_sub' {f : ℕ → ℝ} {e p u v w : ℕ}
    (h : Tri (fun t => f (2 * t + e)) (p / 2) (u / 2) (v / 2) (w / 2))
    (hp : p % 2 = e) (hu : u % 2 = e) (hv : v % 2 = e) (hw : w % 2 = e) : Tri f p u v w := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [O_sub' f hu hv hp]; linarith
  · rw [O_sub' f hv hw hp]; linarith
  · rw [O_sub' f hw hu hp]; linarith

lemma Bad_lift {K : ℕ} {f : ℕ → ℝ} {X : Finset ℕ} {e : ℕ} (he : e < 2)
    (hX : ∀ x ∈ X, x % 2 = e) (h : Bad K (fun t => f (2 * t + e)) (X.image (· / 2))) :
    Bad (K + 1) f X := by
  rcases h with ⟨x', hx', u', hu', v', hv', w', hw', h1, h2, h3, ht⟩ |
      ⟨p', hp', hpX', u', hu', v', hv', w', hw', ht⟩
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hx'
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hu'
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hv'
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hw'
    refine Or.inl ⟨x, hx, u, hu, v, hv, w, hw, fun h => h1 (by rw [h]), fun h => h2 (by rw [h]),
      fun h => h3 (by rw [h]), Tri_sub' ht (hX x hx) (hX u hu) (hX v hv) (hX w hw)⟩
  · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hu'
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hv'
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hw'
    refine Or.inr ⟨2 * p' + e, by rw [pow_succ]; omega, fun hpX => hpX' ?_, u, hu, v, hv, w, hw,
      Tri_sub' (by rwa [show (2 * p' + e) / 2 = p' by omega]) (by omega)
        (hX u hu) (hX v hv) (hX w hw)⟩
    exact Finset.mem_image.2 ⟨_, hpX, by omega⟩

/-- The mixed case: the low half contains at least 4 points of `X` and the high half at least
one. -/
lemma mixed {K : ℕ} {f : ℕ → ℝ} {lo hi : ℕ} (hd : DB K f lo hi) (hlh : lo + hi = 1)
    (hH : IsHorton K (fun t => f (2 * t + lo)))
    (hgp : ∀ x y z, x < 2 ^ (K + 1) → y < 2 ^ (K + 1) → z < 2 ^ (K + 1) → x ≠ y → y ≠ z →
      x ≠ z → O f x y z ≠ 0)
    (X : Finset ℕ) (hX : ∀ x ∈ X, x < 2 ^ (K + 1))
    (hA : 4 ≤ (X.filter (fun x => x % 2 = lo)).card) (hB : ∃ b ∈ X, b % 2 = hi) :
    Bad (K + 1) f X := by
  by_contra hbad
  have n1 : ∀ x ∈ X, ∀ u ∈ X, ∀ v ∈ X, ∀ w ∈ X, u ≠ x → v ≠ x → w ≠ x → ¬Tri f x u v w :=
    fun x hx u hu v hv w hw h1 h2 h3 ht =>
      hbad (Or.inl ⟨x, hx, u, hu, v, hv, w, hw, h1, h2, h3, ht⟩)
  have n2 : ∀ p, p < 2 ^ (K + 1) → p ∉ X → ∀ u ∈ X, ∀ v ∈ X, ∀ w ∈ X, ¬Tri f p u v w :=
    fun p hp hpX u hu v hv w hw ht => hbad (Or.inr ⟨p, hp, hpX, u, hu, v, hv, w, hw, ht⟩)
  obtain ⟨b, hbX, hb⟩ := hB
  have hbK := hX b hbX
  set A := X.filter (fun x => x % 2 = lo) with hAdef
  have memA : ∀ x, x ∈ A ↔ x ∈ X ∧ x % 2 = lo := fun x => Finset.mem_filter
  -- the low points of `X` form a cup
  have cupA : ∀ u ∈ A, ∀ v ∈ A, ∀ w ∈ A, u < v → v < w → 0 < O f u v w := by
    intro u hu v hv w hw huv hvw
    rw [memA] at hu hv hw
    by_contra hneg
    have hne := hgp u v w (hX u hu.1) (hX v hv.1) (hX w hw.1) (by omega) (by omega) (by omega)
    have hlt : O f u v w < 0 := lt_of_le_of_ne (not_lt.1 hneg) hne
    have a1 := hd.above huv (hX v hv.1) hbK hu.2 hv.2 hb
    have a2 := hd.above hvw (hX w hw.1) hbK hv.2 hw.2 hb
    refine n1 v hv.1 u hu.1 w hw.1 b hbX (by omega) (by omega) (by omega) ⟨?_, ?_, ?_⟩
    · linarith [O_swap23 f u v w]
    · linarith [O_cyc f v w b]
    · linarith [O_cyc f b u v]
  -- consecutive low points have no low point above them
  set g : ℕ → ℝ := fun t => f (2 * t + lo) with hg
  have hopen : ∀ x ∈ A, ∀ y ∈ A, x < y → ∀ p', x / 2 < p' → p' < y / 2 →
      O g (x / 2) (y / 2) p' < 0 := by
    intro x hx y hy hxy p' h1 h2
    rw [memA] at hx hy
    by_contra hge
    have hpx : x < 2 * p' + lo := by omega
    have hpy : 2 * p' + lo < y := by omega
    have hp : 2 * p' + lo < 2 ^ (K + 1) := lt_trans hpy (hX y hy.1)
    have e1 := O_sub' f hx.2 hy.2 (show (2 * p' + lo) % 2 = lo by omega)
    rw [show (2 * p' + lo) / 2 = p' by omega] at e1
    have hne := hgp x y (2 * p' + lo) (hX x hx.1) (hX y hy.1) hp (by omega) (by omega)
      (by omega)
    have hpos : 0 < O f x y (2 * p' + lo) := by
      rcases lt_or_gt_of_ne hne with h | h
      · exfalso; rw [e1] at h; exact hge (by linarith)
      · exact h
    by_cases hpX : 2 * p' + lo ∈ X
    · have := cupA x ((memA x).2 hx) (2 * p' + lo) ((memA _).2 ⟨hpX, by omega⟩) y
        ((memA y).2 hy) hpx hpy
      linarith [O_swap23 f x y (2 * p' + lo)]
    · have a1 := hd.above hpx hp hbK hx.2 (by omega) hb
      have a2 := hd.above hpy (hX y hy.1) hbK (by omega) hy.2 hb
      exact n2 _ hp hpX x hx.1 y hy.1 b hbX
        ⟨hpos, by linarith [O_cyc f (2 * p' + lo) y b], by linarith [O_cyc f b x (2 * p' + lo)]⟩
  -- four low points give an open 4-cup in the low half
  have hAc : 4 ≤ A.card := hA
  set emb := A.orderEmbOfFin rfl
  have mem : ∀ i, emb i ∈ A := fun i => A.orderEmbOfFin_mem rfl i
  have mono : StrictMono emb := emb.strictMono
  let c : ℕ → ℕ := fun i => if h : i < A.card then emb ⟨i, h⟩ else 0
  have cmem : ∀ i, i < 4 → c i ∈ A := fun i hi => by
    simp only [c, dif_pos (show i < A.card by omega)]; exact mem _
  have cmono : ∀ i j, i < j → j < 4 → c i < c j := fun i j hij hj => by
    simp only [c, dif_pos (show i < A.card by omega), dif_pos (show j < A.card by omega)]
    exact mono (Fin.mk_lt_mk.2 hij)
  have par : ∀ i, i < 4 → c i % 2 = lo := fun i hi => ((memA _).1 (cmem i hi)).2
  have key := fun x y z (hx : x % 2 = lo) (hy : y % 2 = lo) (hz : z % 2 = lo) =>
    O_sub' f hx hy hz
  have hcup : ∀ i j k, i < j → j < k → k < 4 → 0 < O g (c i / 2) (c j / 2) (c k / 2) := by
    intro i j k hij hjk hk
    have := cupA _ (cmem i (by omega)) _ (cmem j (by omega)) _ (cmem k hk)
      (cmono i j hij (by omega)) (cmono j k hjk hk)
    rw [key _ _ _ (par i (by omega)) (par j (by omega)) (par k hk)] at this
    linarith
  have h01 := cmono 0 1 (by norm_num) (by norm_num)
  have h12 := cmono 1 2 (by norm_num) (by norm_num)
  have h23 := cmono 2 3 (by norm_num) (by norm_num)
  have p0 := par 0 (by norm_num)
  have p1 := par 1 (by norm_num)
  have p2 := par 2 (by norm_num)
  have p3 := par 3 (by norm_num)
  have h3K := hX _ ((memA _).1 (cmem 3 (by norm_num))).1
  rw [pow_succ] at h3K
  exact no_open_cup K g hH (c 0 / 2) (c 1 / 2) (c 2 / 2) (c 3 / 2)
    ⟨by omega, by omega, by omega, by omega,
      hcup 0 1 2 (by norm_num) (by norm_num) (by norm_num),
      hcup 0 1 3 (by norm_num) (by norm_num) (by norm_num),
      hcup 0 2 3 (by norm_num) (by norm_num) (by norm_num),
      hcup 1 2 3 (by norm_num) (by norm_num) (by norm_num),
      hopen _ (cmem 0 (by norm_num)) _ (cmem 1 (by norm_num)) h01,
      hopen _ (cmem 1 (by norm_num)) _ (cmem 2 (by norm_num)) h12,
      hopen _ (cmem 2 (by norm_num)) _ (cmem 3 (by norm_num)) h23⟩

theorem bad : ∀ (K : ℕ) (f : ℕ → ℝ), IsHorton K f → ∀ X : Finset ℕ,
    (∀ x ∈ X, x < 2 ^ K) → 7 ≤ X.card → Bad K f X := by
  intro K
  induction K with
  | zero =>
    intro f _ X hX hc
    exfalso
    have hsub : X ⊆ {0} := fun x hx => by
      have := hX x hx; simp at this ⊢; omega
    have := Finset.card_le_card hsub
    simp at this; omega
  | succ K ih =>
    intro f hf X hX hc
    have hgp := gp hf
    by_cases hsame : ∃ e, e < 2 ∧ ∀ x ∈ X, x % 2 = e
    · obtain ⟨e, he, hXe⟩ := hsame
      apply Bad_lift he hXe
      apply ih _ (Horton_sub he hf)
      · intro x' hx'
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hx'
        have := hX x hx; rw [pow_succ] at this; omega
      · rw [Finset.card_image_of_injOn]
        · exact hc
        · intro x hx y hy hxy
          have := hXe x hx; have := hXe y hy
          simp only at hxy; omega
    · push Not at hsame
      obtain ⟨x0, hx0, h0⟩ := hsame 0 (by norm_num)
      obtain ⟨x1, hx1, h1⟩ := hsame 1 (by norm_num)
      have hsplit : (X.filter (fun x => x % 2 = 0)).card +
          (X.filter (fun x => x % 2 = 1)).card = X.card := by
        rw [← Finset.card_filter_add_card_filter_not (s := X) (fun x => x % 2 = 0)]
        congr 2
        exact Finset.filter_congr (fun x _ => by omega)
      have hH0 := Horton_sub (e := 0) (by norm_num) hf
      have hH1 := Horton_sub (e := 1) (by norm_num) hf
      have hgpn := gp (Horton_neg _ _ hf)
      obtain ⟨-, -, hdb⟩ := hf
      rcases hdb with hd | hd
      · by_cases h4 : 4 ≤ (X.filter (fun x => x % 2 = 0)).card
        · exact mixed hd rfl hH0 hgp X hX h4 ⟨x0, hx0, by omega⟩
        · exact Bad_neg (mixed (DB_neg hd) rfl (Horton_neg _ _ hH1) hgpn X hX (by omega)
            ⟨x1, hx1, by omega⟩)
      · by_cases h4 : 4 ≤ (X.filter (fun x => x % 2 = 1)).card
        · exact mixed hd rfl hH1 hgp X hX h4 ⟨x1, hx1, by omega⟩
        · exact Bad_neg (mixed (DB_neg hd) rfl (Horton_neg _ _ hH0) hgpn X hX (by omega)
            ⟨x0, hx0, by omega⟩)

/-! ### Existence of Horton sets -/

lemma exists_horton : ∀ K : ℕ, ∃ f : ℕ → ℝ, ∃ B : ℝ, 0 ≤ B ∧ (∀ i, 0 ≤ f i ∧ f i ≤ B) ∧
    IsHorton K f := by
  intro K
  induction K with
  | zero => exact ⟨fun _ => 0, 0, le_rfl, fun _ => ⟨le_rfl, le_rfl⟩, trivial⟩
  | succ K ih =>
    obtain ⟨f, B, hB, hfB, hH⟩ := ih
    obtain ⟨T, hT⟩ : ∃ T : ℝ, T = 2 ^ K := ⟨_, rfl⟩
    have hT1 : 1 ≤ T := by rw [hT]; exact one_le_pow₀ (by norm_num)
    obtain ⟨D, hD⟩ : ∃ D : ℝ, D = (B + 1) * (8 * T) := ⟨_, rfl⟩
    have hD0 : 0 ≤ D := by rw [hD]; positivity
    have hBT : 0 ≤ B * (T - 1) := mul_nonneg hB (by linarith)
    let g : ℕ → ℝ := fun i => if i % 2 = 0 then f (i / 2) else f (i / 2) + D
    have g0 : ∀ i, g (2 * i + 0) = f i := fun i => by
      simp only [g, show (2 * i + 0) % 2 = 0 by omega, show (2 * i + 0) / 2 = i by omega,
        ite_true]
    have g1 : ∀ i, g (2 * i + 1) = f i + D := fun i => by
      simp only [g, show (2 * i + 1) % 2 = 1 by omega, show (2 * i + 1) / 2 = i by omega]
      simp
    refine ⟨g, B + D, by positivity, fun i => ?_, ?_, ?_, Or.inl ?_⟩
    · simp only [g]
      have := hfB (i / 2)
      split_ifs <;> constructor <;> linarith
    · have : (fun i => g (2 * i + 0)) = f := funext g0
      rw [this]; exact hH
    · have : (fun i => g (2 * i + 1)) = fun i => f i + D := funext g1
      rw [this]; exact Horton_add _ _ hH D
    · intro i j m hij hj hm
      have hcast : ∀ n : ℕ, n < 2 ^ K → (n : ℝ) + 1 ≤ T := fun n hn => by
        have := (Nat.cast_le (α := ℝ)).2 (Nat.succ_le_of_lt hn)
        push_cast at this; rw [hT]; exact this
      have hi1 := hcast i (by omega)
      have hj1 := hcast j hj
      have hm1 := hcast m hm
      have hij' : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
      have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
      have fi := hfB i
      have fj := hfB j
      have fm := hfB m
      have hfji : |f j - f i| ≤ B := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
      constructor
      · have e : O g (2 * i + 0) (2 * j + 0) (2 * m + 1) =
            (2 * (j : ℝ) - 2 * i) * (f m + D - f i) - (f j - f i) * (2 * m + 1 - 2 * i) := by
          unfold O; rw [g0, g0, g1]; push_cast; ring
        have k1 : 2 * (D - B) ≤ (2 * (j : ℝ) - 2 * i) * (f m + D - f i) :=
          mul_le_mul (by linarith) (by linarith) (by nlinarith) (by linarith)
        have k2 : (f j - f i) * (2 * m + 1 - 2 * i) ≤ B * (2 * T) := by
          refine le_trans (le_abs_self _) ?_
          rw [abs_mul]
          exact mul_le_mul hfji (abs_le.2 ⟨by linarith, by linarith⟩) (abs_nonneg _) hB
        rw [e, hD] at *; nlinarith
      · have e : O g (2 * i + 1) (2 * j + 1) (2 * m + 0) =
            -((2 * (j : ℝ) - 2 * i) * (f i + D - f m)) - (f j - f i) * (2 * m - 2 * i - 1) := by
          unfold O; rw [g1, g1, g0]; push_cast; ring
        have k1 : 2 * (D - B) ≤ (2 * (j : ℝ) - 2 * i) * (f i + D - f m) :=
          mul_le_mul (by linarith) (by linarith) (by nlinarith) (by linarith)
        have k2 : -(B * (2 * T)) ≤ (f j - f i) * (2 * m - 2 * i - 1) := by
          refine le_trans ?_ (neg_abs_le _)
          rw [abs_mul, neg_le_neg_iff]
          exact mul_le_mul hfji (abs_le.2 ⟨by linarith, by linarith⟩) (abs_nonneg _) hB
        rw [e, hD] at *; nlinarith

/-! ### From orientations to convex hulls -/

/-- The point `(i, f i)` of the plane. -/
def pt (f : ℕ → ℝ) (i : ℕ) : ℝ × ℝ := ((i : ℝ), f i)

lemma pt_inj (f : ℕ → ℝ) : Function.Injective (pt f) := fun i j h => by
  have := congrArg Prod.fst h
  simpa [pt] using this

lemma tri_mem (f : ℕ → ℝ) {p u v w : ℕ} (h : Tri f p u v w) :
    pt f p ∈ convexHull ℝ ({pt f u, pt f v, pt f w} : Set (ℝ × ℝ)) := by
  obtain ⟨h1, h2, h3⟩ := h
  set S := O f v w p + O f w u p + O f u v p with hSdef
  have hS : 0 < S := by linarith
  have hx : (p : ℝ) * S = O f v w p * u + O f w u p * v + O f u v p * w := by
    rw [hSdef]; unfold O; ring
  have hy : f p * S = O f v w p * f u + O f w u p * f v + O f u v p * f w := by
    rw [hSdef]; unfold O; ring
  have hmem := (convex_convexHull ℝ ({pt f u, pt f v, pt f w} : Set (ℝ × ℝ))).sum_mem
    (t := Finset.univ) (w := ![O f v w p / S, O f w u p / S, O f u v p / S])
    (z := ![pt f u, pt f v, pt f w])
    (by intro i _; fin_cases i <;> simp <;> positivity)
    (by simp [Fin.sum_univ_three]; field_simp; linarith)
    (by intro i _; fin_cases i <;> simp <;> apply subset_convexHull <;> simp)
  convert hmem using 1
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, pt, Prod.smul_mk, smul_eq_mul,
    Prod.mk_add_mk]
  ext
  · simp only
    rw [show O f v w p / S * u + O f w u p / S * v + O f u v p / S * w =
      (O f v w p * u + O f w u p * v + O f u v p * w) / S by ring, eq_div_iff hS.ne', hx]
  · simp only
    rw [show O f v w p / S * f u + O f w u p / S * f v + O f u v p / S * f w =
      (O f v w p * f u + O f w u p * f v + O f u v p * f w) / S by ring, eq_div_iff hS.ne', hy]

lemma tri_lt {f : ℕ → ℝ} {p u v w N : ℕ} (h : Tri f p u v w) (hu : u < N) (hv : v < N)
    (hw : w < N) : p < N := by
  obtain ⟨h1, h2, h3⟩ := h
  have key : (p : ℝ) * (O f v w p + O f w u p + O f u v p) =
      O f v w p * u + O f w u p * v + O f u v p * w := by unfold O; ring
  by_contra hpN
  push Not at hpN
  have hN : (N : ℝ) ≤ p := by exact_mod_cast hpN
  have hu' : (u : ℝ) < N := by exact_mod_cast hu
  have hv' : (v : ℝ) < N := by exact_mod_cast hv
  have hw' : (w : ℝ) < N := by exact_mod_cast hw
  have e1 : O f v w p * u < O f v w p * p := mul_lt_mul_of_pos_left (by linarith) h2
  have e2 : O f w u p * v < O f w u p * p := mul_lt_mul_of_pos_left (by linarith) h3
  have e3 : O f u v p * w < O f u v p * p := mul_lt_mul_of_pos_left (by linarith) h1
  linarith

lemma O_eq_zero_of_collinear (f : ℕ → ℝ) {i j k : ℕ}
    (h : Collinear ℝ ({pt f i, pt f j, pt f k} : Set (ℝ × ℝ))) : O f i j k = 0 := by
  rw [collinear_iff_of_mem (Set.mem_insert _ _)] at h
  obtain ⟨v, hv⟩ := h
  obtain ⟨a, ha⟩ := hv (pt f j) (by simp)
  obtain ⟨b, hb⟩ := hv (pt f k) (by simp)
  have hj1 := congrArg Prod.fst ha
  have hj2 := congrArg Prod.snd ha
  have hk1 := congrArg Prod.fst hb
  have hk2 := congrArg Prod.snd hb
  simp only [pt, vadd_eq_add, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] at hj1 hj2 hk1 hk2
  unfold O
  rw [hj1, hj2, hk1, hk2]
  ring

end

end Horton

namespace Erdos216

open Horton

/-- No three points of `S` are collinear. -/
def GeneralPosition (S : Finset (ℝ × ℝ)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → p ≠ r → q ≠ r →
    ¬Collinear ℝ ({p, q, r} : Set (ℝ × ℝ))

/-- `S` contains an empty convex `k`-gon: `k` points in convex position whose convex hull
contains no other point of `S`. -/
def HasEmptyConvexPolygon (k : ℕ) (S : Finset (ℝ × ℝ)) : Prop :=
  ∃ T ⊆ S, T.card = k ∧ ConvexIndependent ℝ ((↑) : ↥(T : Set (ℝ × ℝ)) → ℝ × ℝ) ∧
    ∀ p ∈ S, p ∉ T → p ∉ convexHull ℝ (T : Set (ℝ × ℝ))

/-- An empty convex `k`-gon contains an empty convex `j`-gon for every `j ≤ k`
(take any `j` of its vertices). -/
lemma HasEmptyConvexPolygon.of_le {j k : ℕ} {S : Finset (ℝ × ℝ)} (hjk : j ≤ k)
    (h : HasEmptyConvexPolygon k S) : HasEmptyConvexPolygon j S := by
  classical
  obtain ⟨T, hTS, hcard, hconv, hempty⟩ := h
  obtain ⟨T', hT'T, hT'card⟩ := Finset.exists_subset_card_eq (show j ≤ T.card by omega)
  have hsub : (T' : Set (ℝ × ℝ)) ⊆ T := Finset.coe_subset.2 hT'T
  rw [convexIndependent_set_iff_notMem_convexHull_sdiff] at hconv
  refine ⟨T', hT'T.trans hTS, hT'card, ?_, ?_⟩
  · rw [convexIndependent_set_iff_notMem_convexHull_sdiff]
    intro x hx hxh
    exact hconv x (hsub hx) (convexHull_mono (Set.diff_subset_diff_left hsub) hxh)
  · intro p hp hpT' hph
    by_cases hpT : p ∈ T
    · refine hconv p hpT (convexHull_mono ?_ hph)
      intro y hy
      refine ⟨hsub hy, fun h => hpT' ?_⟩
      rw [Set.mem_singleton_iff.1 h] at hy
      exact hy
    · exact hempty p hp hpT (convexHull_mono hsub hph)

/-- **Horton (1983).** For every `N` there is a set of exactly `N` points in general position
with no empty convex heptagon. -/
theorem horton (N : ℕ) : ∃ S : Finset (ℝ × ℝ), S.card = N ∧ GeneralPosition S ∧
    ¬HasEmptyConvexPolygon 7 S := by
  obtain ⟨f, B, -, -, hH⟩ := exists_horton N
  have hN : ∀ i, i < N → i < 2 ^ N := fun i hi => lt_trans hi Nat.lt_two_pow_self
  refine ⟨(Finset.range N).image (pt f), ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ (pt_inj f), Finset.card_range]
  · intro p hp q hq r hr hpq hpr hqr hcol
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hq
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hr
    rw [Finset.mem_range] at hi hj hk
    exact gp hH i j k (hN i hi) (hN j hj) (hN k hk) (fun h => hpq (by rw [h]))
      (fun h => hqr (by rw [h])) (fun h => hpr (by rw [h])) (O_eq_zero_of_collinear f hcol)
  · rintro ⟨T, hTS, hcard, hconv, hempty⟩
    classical
    set X := (Finset.range N).filter (fun i => pt f i ∈ T) with hXdef
    have hXT : X.image (pt f) = T := by
      ext q
      constructor
      · intro hq
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hq
        exact (Finset.mem_filter.1 hi).2
      · intro hq
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 (hTS hq)
        exact Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨hi, hq⟩, rfl⟩
    have hXcard : X.card = 7 := by
      rw [← hcard, ← hXT, Finset.card_image_of_injective _ (pt_inj f)]
    have hXN : ∀ x ∈ X, x < N := fun x hx => Finset.mem_range.1 (Finset.mem_filter.1 hx).1
    have hXT' : ∀ x ∈ X, pt f x ∈ T := fun x hx => (Finset.mem_filter.1 hx).2
    rcases bad N f hH X (fun x hx => hN x (hXN x hx)) (by omega) with
      ⟨x, hx, u, hu, v, hv, w, hw, hux, hvx, hwx, ht⟩ | ⟨p, -, hpX, u, hu, v, hv, w, hw, ht⟩
    · rw [convexIndependent_set_iff_notMem_convexHull_sdiff] at hconv
      apply hconv (pt f x) (hXT' x hx)
      refine convexHull_mono ?_ (tri_mem f ht)
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact ⟨hXT' u hu, fun h => hux (pt_inj f h)⟩
      · exact ⟨hXT' v hv, fun h => hvx (pt_inj f h)⟩
      · exact ⟨hXT' w hw, fun h => hwx (pt_inj f h)⟩
    · have hpN : p < N := tri_lt ht (hXN u hu) (hXN v hv) (hXN w hw)
      refine hempty (pt f p) (Finset.mem_image.2 ⟨p, Finset.mem_range.2 hpN, rfl⟩)
        (fun h => hpX (Finset.mem_filter.2 ⟨Finset.mem_range.2 hpN, h⟩)) ?_
      refine convexHull_mono ?_ (tri_mem f ht)
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact hXT' u hu
      · exact hXT' v hv
      · exact hXT' w hw

/-- **Erdős Problem 216 (answer: no).** It is not true that for every `k` some number `g` of
points in general position forces an empty convex `k`-gon; it already fails for `k = 7`. -/
theorem erdos_216 :
    ¬∀ k : ℕ, ∃ g : ℕ, ∀ S : Finset (ℝ × ℝ), S.card = g → GeneralPosition S →
      HasEmptyConvexPolygon k S := by
  intro h
  obtain ⟨g, hg⟩ := h 7
  obtain ⟨S, hS, hgp, hno⟩ := horton g
  exact hno (hg S hS hgp)

/-- The same with "at least `g` points". -/
theorem erdos_216' :
    ¬∀ k : ℕ, ∃ g : ℕ, ∀ S : Finset (ℝ × ℝ), g ≤ S.card → GeneralPosition S →
      HasEmptyConvexPolygon k S := by
  intro h
  obtain ⟨g, hg⟩ := h 7
  obtain ⟨S, hS, hgp, hno⟩ := horton g
  exact hno (hg S hS.ge hgp)

/-- Horton sets have no empty convex `k`-gon for any `k ≥ 7`: `g(k) = ∞` for all `k ≥ 7`. -/
theorem horton_ge {k : ℕ} (hk : 7 ≤ k) (N : ℕ) : ∃ S : Finset (ℝ × ℝ), S.card = N ∧
    GeneralPosition S ∧ ¬HasEmptyConvexPolygon k S := by
  obtain ⟨S, hS, hgp, hno⟩ := horton N
  exact ⟨S, hS, hgp, fun h => hno (h.of_le hk)⟩

/-- For every `k ≥ 7`, no number of points in general position forces an empty convex
`k`-gon. -/
theorem no_g_of_ge_seven {k : ℕ} (hk : 7 ≤ k) :
    ¬∃ g : ℕ, ∀ S : Finset (ℝ × ℝ), g ≤ S.card → GeneralPosition S →
      HasEmptyConvexPolygon k S := by
  rintro ⟨g, hg⟩
  obtain ⟨S, hS, hgp, hno⟩ := horton_ge hk g
  exact hno (hg S hS.ge hgp)

end Erdos216
