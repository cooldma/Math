import Mathlib

/-!
# Blumenthal's problem for `2^n` points (Erdős Problem 504)

Let `α_N` be the supremum of all `α ∈ [0, π]` such that every set of `N` points in the plane
contains three distinct points `x, z, y` with `∠ x z y ≥ α`.  Erdős and Szekeres (1960) proved
`α_{2^n} = π (1 - 1/n)`.  This file proves this for `n ≥ 3`, in exactly the form stated in
`FormalConjectures/ErdosProblems/504.lean` (`Erdos504.erdos_504`).

## Lower bound (any `2^n` points have an angle `≥ π(1 - 1/n)`)

Suppose every angle is `< β = π - π/n`.  Fix an offset direction `s`.  For distinct `p, q`
exactly one of the directions `q - p`, `p - q` lies in the half-turn `[s, s + π)`; cut that
half-turn into `n` sectors of width `π/n` and colour the ordered pair accordingly.  If
`u → v` and `v → w` have the same colour then `∠ u v w > β`, so no monochromatic 2-paths
exist.  Labelling each vertex by the set of colours of its in-edges is then injective, hence
(by counting, `2^n` points and `2^n` labels) bijective.  Choosing a vertex `a` with no
in-edges and rotating `s` to the extreme out-direction of `a`, then rotating `s` back by
`π/n`, shows that `a` has an out-edge in the last sector, and that edge forms an angle
`≥ β` with the extreme one.

## Upper bound (a configuration with all angles `< β + ε`)

`P(e) = ∑_{m ∈ e} L^{-m} e^{iπm/n}` for `e ⊆ {0,…,n-1}` with `L` large.
-/

open Real EuclideanGeometry

namespace Blumenthal

noncomputable section

/-! ### Directions -/

/-- The direction of `q - p`, measured from the offset `s` and normalised into `[0, 2π)`. -/
def r (s : ℝ) (p q : ℂ) : ℝ := toIcoMod two_pi_pos 0 (Complex.arg (q - p) - s)

lemma r_nonneg (s : ℝ) (p q : ℂ) : 0 ≤ r s p q := (toIcoMod_mem_Ico' two_pi_pos _).1

lemma r_lt (s : ℝ) (p q : ℂ) : r s p q < 2 * π := by
  have := (toIcoMod_mem_Ico' two_pi_pos (Complex.arg (q - p) - s)).2
  exact this

lemma r_congr (s : ℝ) (p q : ℂ) :
    ∃ k : ℤ, Complex.arg (q - p) - s = r s p q + k * (2 * π) := by
  obtain ⟨-, k, hk⟩ := (toIcoMod_eq_iff two_pi_pos (a := 0) (b := Complex.arg (q - p) - s)
    (c := r s p q)).1 rfl
  exact ⟨k, by rw [hk, zsmul_eq_mul]⟩

lemma mod_unique {t t' : ℝ} (k : ℤ) (h0 : 0 ≤ t) (h1 : t < 2 * π) (h0' : 0 ≤ t')
    (h1' : t' < 2 * π) (h : t = t' + k * (2 * π)) : t = t' := by
  have hk1 : (k : ℝ) < 1 := by
    by_contra hc; push Not at hc; nlinarith [pi_pos]
  have hk2 : (-1 : ℝ) < k := by
    by_contra hc; push Not at hc; nlinarith [pi_pos]
  have hk : k = 0 := by
    have a : k < 1 := by exact_mod_cast hk1
    have b : -1 < k := by exact_mod_cast hk2
    omega
  subst hk; simpa using h

lemma arg_swap {p q : ℂ} (h : p ≠ q) :
    ∃ k : ℤ, Complex.arg (p - q) = Complex.arg (q - p) + π + k * (2 * π) := by
  have h1 := Complex.arg_neg_coe_angle (sub_ne_zero.2 h.symm)
  rw [neg_sub, ← Real.Angle.coe_add, Real.Angle.angle_eq_iff_two_pi_dvd_sub] at h1
  obtain ⟨k, hk⟩ := h1
  exact ⟨k, by linarith⟩

lemma r_swap (s : ℝ) {p q : ℂ} (h : p ≠ q) :
    (r s p q < π ∧ r s q p = r s p q + π) ∨ (π ≤ r s p q ∧ r s q p = r s p q - π) := by
  obtain ⟨k, hk⟩ := arg_swap h
  obtain ⟨k1, hk1⟩ := r_congr s p q
  obtain ⟨k2, hk2⟩ := r_congr s q p
  have h0 := r_nonneg s p q; have h1 := r_lt s p q
  have h0' := r_nonneg s q p; have h1' := r_lt s q p
  rcases lt_or_ge (r s p q) π with hlt | hge
  · left
    refine ⟨hlt, mod_unique (k + k1 - k2) h0' h1' (by linarith) (by linarith) ?_⟩
    push_cast; linarith
  · right
    refine ⟨hge, mod_unique (k + k1 - k2 + 1) h0' h1' (by linarith) (by linarith) ?_⟩
    push_cast; linarith

lemma not_both (s : ℝ) {p q : ℂ} (h : p ≠ q) (h1 : r s p q < π) (h2 : r s q p < π) : False := by
  rcases r_swap s h with ⟨-, h'⟩ | ⟨h', -⟩
  · linarith [r_nonneg s p q]
  · linarith

lemma r_shift (s : ℝ) {n : ℕ} (hn : 0 < n) (p q : ℂ) :
    (r s p q < 2 * π - π / n ∧ r (s - π / n) p q = r s p q + π / n) ∨
    (2 * π - π / n ≤ r s p q ∧ r (s - π / n) p q = r s p q + π / n - 2 * π) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < π / n := div_pos pi_pos (by linarith)
  have hd2 : π / n ≤ π := div_le_self pi_pos.le hn'
  obtain ⟨k1, hk1⟩ := r_congr s p q
  obtain ⟨k2, hk2⟩ := r_congr (s - π / n) p q
  have h0 := r_nonneg s p q; have h1 := r_lt s p q
  have h0' := r_nonneg (s - π / n) p q; have h1' := r_lt (s - π / n) p q
  rcases lt_or_ge (r s p q) (2 * π - π / n) with hlt | hge
  · left
    refine ⟨hlt, mod_unique (k1 - k2) h0' h1' (by linarith) (by linarith) ?_⟩
    push_cast; linarith
  · right
    refine ⟨hge, mod_unique (k1 - k2 + 1) h0' h1' (by linarith) (by linarith [pi_pos]) ?_⟩
    push_cast; linarith

/-! ### Angles in terms of directions -/

lemma angle_complex {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    InnerProductGeometry.angle x y = arccos (cos (Complex.arg x - Complex.arg y)) := by
  rw [Complex.angle_eq_abs_arg hx hy]
  have h := congrArg Real.Angle.cos (Complex.arg_div_coe_angle hx hy)
  rw [← Real.Angle.coe_sub, Real.Angle.cos_coe, Real.Angle.cos_coe] at h
  rw [← h, ← Real.cos_abs, arccos_cos (abs_nonneg _) (Complex.abs_arg_le_pi _)]

lemma angle_eq_r (s : ℝ) {x z y : ℂ} (hx : x ≠ z) (hy : y ≠ z) :
    EuclideanGeometry.angle x z y = arccos (cos (r s z x - r s z y)) := by
  rw [EuclideanGeometry.angle, vsub_eq_sub, vsub_eq_sub,
    angle_complex (sub_ne_zero.2 hx) (sub_ne_zero.2 hy)]
  obtain ⟨k1, hk1⟩ := r_congr s z x
  obtain ⟨k2, hk2⟩ := r_congr s z y
  have : Complex.arg (x - z) - Complex.arg (y - z) =
      (r s z x - r s z y) + ((k1 - k2 : ℤ) : ℝ) * (2 * π) := by
    push_cast; linarith
  rw [this, cos_add_int_mul_two_pi]

lemma big_angle {n : ℕ} (hn : 0 < n) {t : ℝ} (h1 : π - π / n ≤ t) (h2 : t ≤ π + π / n) :
    (1 - 1 / (n : ℝ)) * π ≤ arccos (cos t) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < π / n := div_pos pi_pos (by linarith)
  have hd2 : π / n ≤ π := div_le_self pi_pos.le hn'
  have hβ : (1 - 1 / (n : ℝ)) * π = π - π / n := by ring
  rw [hβ]
  have hc : cos t ≤ cos (π - π / n) := by
    rw [cos_pi_sub]
    have : cos t = -cos (t - π) := by rw [cos_sub_pi]; ring
    rw [this, neg_le_neg_iff, ← Real.cos_abs (t - π)]
    apply cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hd2
    rw [abs_le]; constructor <;> linarith
  calc π - π / n = arccos (cos (π - π / n)) := (arccos_cos (by linarith) (by linarith)).symm
    _ ≤ arccos (cos t) := arccos_le_arccos hc

/-! ### Sectors and labels -/

/-- `t` lies in the `k`-th of the `n` sectors of width `π/n` that tile `[0, π)`. -/
def Sec (n k : ℕ) (t : ℝ) : Prop := k < n ∧ k * (π / n) ≤ t ∧ t < (k + 1) * (π / n)

lemma exists_sec {n : ℕ} (hn : 0 < n) {t : ℝ} (h0 : 0 ≤ t) (h1 : t < π) : ∃ k, Sec n k t := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : 0 < π / n := div_pos pi_pos hn'
  have hπ : (n : ℝ) * (π / n) = π := by field_simp
  refine ⟨⌊t / (π / n)⌋₊, ?_, ?_, ?_⟩
  · rw [Nat.floor_lt (div_nonneg h0 hd.le), div_lt_iff₀ hd]; linarith
  · have := Nat.floor_le (div_nonneg h0 hd.le); rwa [le_div_iff₀ hd] at this
  · have := Nat.lt_floor_add_one (t / (π / n)); rwa [div_lt_iff₀ hd] at this

lemma Sec.lt_pi {n k : ℕ} {t : ℝ} (h : Sec n k t) : t < π := by
  obtain ⟨hk, -, h2⟩ := h
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hk' : ((k : ℝ) + 1) ≤ n := by exact_mod_cast hk
  have hπ : (n : ℝ) * (π / n) = π := by field_simp
  have : ((k : ℝ) + 1) * (π / n) ≤ n * (π / n) := by gcongr
  linarith

lemma sec_last {n : ℕ} (hn : 0 < n) {t : ℝ} (h1 : π - π / n ≤ t) (h2 : t < π) :
    Sec n (n - 1) t := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : ((n - 1 : ℕ) : ℝ) = n - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hπ : (n : ℝ) * (π / n) = π := by field_simp
  refine ⟨by omega, ?_, ?_⟩
  · rw [hc]; linarith [show ((n : ℝ) - 1) * (π / n) = n * (π / n) - π / n by ring]
  · rw [hc]; linarith [show ((n : ℝ) - 1 + 1) * (π / n) = n * (π / n) by ring]

lemma sec_shift_succ {s : ℝ} {n j : ℕ} (hn : 0 < n) {p q : ℂ}
    (h : Sec n (j + 1) (r (s - π / n) p q)) : Sec n j (r s p q) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : 0 < π / n := div_pos pi_pos hn'
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  obtain ⟨hk, a, b⟩ := h
  push_cast at a b
  have h1 := r_lt s p q
  rcases r_shift s hn p q with ⟨-, he⟩ | ⟨-, he⟩
  · rw [he] at a b
    refine ⟨by omega, ?_, ?_⟩ <;> nlinarith
  · rw [he] at a b
    exfalso; nlinarith

lemma sec_shift_zero {s : ℝ} {n : ℕ} (hn : 0 < n) {p q : ℂ}
    (h : Sec n 0 (r (s - π / n) p q)) : 2 * π - π / n ≤ r s p q := by
  obtain ⟨-, a, b⟩ := h
  push_cast at a b
  rcases r_shift s hn p q with ⟨-, he⟩ | ⟨hge, -⟩
  · rw [he] at b; linarith [r_nonneg s p q]
  · exact hge

/-- No two angles are `≥ π(1 - 1/n)`. -/
def NoBig (n : ℕ) (S : Finset ℂ) : Prop :=
  ∀ x ∈ S, ∀ z ∈ S, ∀ y ∈ S, x ≠ z → y ≠ z → x ≠ y →
    EuclideanGeometry.angle x z y < (1 - 1 / (n : ℝ)) * π

lemma two_path {n : ℕ} {S : Finset ℂ} (H : NoBig n S) {s : ℝ} {k : ℕ} {u v w : ℂ}
    (hu : u ∈ S) (hv : v ∈ S) (hw : w ∈ S) (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (h1 : Sec n k (r s u v)) (h2 : Sec n k (r s v w)) : False := by
  have hn : 0 < n := by have := h1.1; omega
  have hA := H u hu v hv w hw huv hvw.symm huw
  rw [angle_eq_r s huv hvw.symm] at hA
  have hvu : r s v u = r s u v + π := by
    rcases r_swap s huv with h | h
    · exact h.2
    · exact absurd h.1 (not_le.2 h1.lt_pi)
  obtain ⟨-, a1, a2⟩ := h1
  obtain ⟨-, b1, b2⟩ := h2
  have hd : ((k : ℝ) + 1) * (π / n) = k * (π / n) + π / n := by ring
  exact absurd hA (not_lt.2 (big_angle hn (by rw [hvu]; linarith) (by rw [hvu]; linarith)))

open Classical in
/-- The label of `v`: the set of colours of edges coming into `v`. -/
def lab (n : ℕ) (S : Finset ℂ) (s : ℝ) (v : ℂ) : Finset (Fin n) :=
  Finset.univ.filter (fun k => ∃ u ∈ S, u ≠ v ∧ Sec n k (r s u v))

lemma mem_lab {n : ℕ} {S : Finset ℂ} {s : ℝ} {v : ℂ} {k : Fin n} :
    k ∈ lab n S s v ↔ ∃ u ∈ S, u ≠ v ∧ Sec n k (r s u v) := by
  simp [lab]

lemma lab_ne {n : ℕ} {S : Finset ℂ} (H : NoBig n S) (hn : 0 < n) (s : ℝ) {v w : ℂ}
    (hv : v ∈ S) (hw : w ∈ S) (hne : v ≠ w) (hlt : r s v w < π) :
    lab n S s v ≠ lab n S s w := by
  obtain ⟨k, hk⟩ := exists_sec hn (r_nonneg s v w) hlt
  intro heq
  have hkw : (⟨k, hk.1⟩ : Fin n) ∈ lab n S s w := mem_lab.2 ⟨v, hv, hne, hk⟩
  rw [← heq, mem_lab] at hkw
  obtain ⟨u, hu, huv, hu'⟩ := hkw
  have huw : u ≠ w := by
    intro h; subst h; exact not_both s hne hlt hu'.lt_pi
  exact two_path H hu hv hw huv hne huw hu' hk

lemma lab_injOn {n : ℕ} {S : Finset ℂ} (H : NoBig n S) (hn : 0 < n) (s : ℝ) :
    Set.InjOn (lab n S s) S := by
  intro v hv w hw heq
  by_contra hne
  rcases r_swap s hne with ⟨h, -⟩ | ⟨-, h'⟩
  · exact lab_ne H hn s hv hw hne h heq
  · exact lab_ne H hn s hw hv (Ne.symm hne) (by rw [h']; linarith [r_lt s v w]) heq.symm

lemma lab_surj {n : ℕ} {S : Finset ℂ} (H : NoBig n S) (hn : 0 < n) (hcard : S.card = 2 ^ n)
    (s : ℝ) (L : Finset (Fin n)) : ∃ v ∈ S, lab n S s v = L := by
  classical
  have h1 : (S.image (lab n S s)).card = 2 ^ n := by
    rw [Finset.card_image_of_injOn (lab_injOn H hn s), hcard]
  have h2 : S.image (lab n S s) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [h1]; simp
  have : L ∈ S.image (lab n S s) := by rw [h2]; exact Finset.mem_univ _
  simpa using this

/-! ### The lower bound -/

theorem lower {n : ℕ} (hn : 2 ≤ n) {S : Finset ℂ} (hcard : S.card = 2 ^ n) :
    ∃ x ∈ S, ∃ z ∈ S, ∃ y ∈ S, x ≠ z ∧ y ≠ z ∧ x ≠ y ∧
      (1 - 1 / (n : ℝ)) * π ≤ EuclideanGeometry.angle x z y := by
  by_contra hcon
  have H : NoBig n S := by
    intro x hx z hz y hy hxz hyz hxy
    by_contra hle; push Not at hle
    exact hcon ⟨x, hx, z, hz, y, hy, hxz, hyz, hxy, hle⟩
  have hn0 : 0 < n := by omega
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < π / n := div_pos pi_pos (by linarith)
  have hdpi : π / n ≤ π / 2 := div_le_div_of_nonneg_left pi_pos.le two_pos hnR
  -- a vertex with no in-edges for the offset `0`
  obtain ⟨a, ha, hla⟩ := lab_surj H hn0 hcard 0 ∅
  have hout0 : ∀ u ∈ S, u ≠ a → r 0 a u < π := by
    intro u hu hua
    by_contra hge; push Not at hge
    rcases r_swap 0 hua.symm with ⟨h, -⟩ | ⟨-, h⟩
    · linarith
    · obtain ⟨k, hk⟩ := exists_sec hn0 (r_nonneg 0 u a) (by rw [h]; linarith [r_lt 0 a u])
      have : (⟨k, hk.1⟩ : Fin n) ∈ lab n S 0 a := mem_lab.2 ⟨u, hu, hua, hk⟩
      rw [hla] at this; simp at this
  -- the extreme out-direction of `a`
  have hne : (S.erase a).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem ha, hcard]
    exact Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))
  obtain ⟨u1, hu1, hmin⟩ := (S.erase a).exists_min_image (r 0 a) hne
  rw [Finset.mem_erase] at hu1
  obtain ⟨m, hm⟩ : ∃ m, m = r 0 a u1 := ⟨_, rfl⟩
  have hrs : ∀ u ∈ S, u ≠ a → r m a u = r 0 a u - m := by
    intro u hu hua
    obtain ⟨k1, hk1⟩ := r_congr 0 a u
    obtain ⟨k2, hk2⟩ := r_congr m a u
    have := hmin u (Finset.mem_erase.2 ⟨hua, hu⟩)
    have := hout0 u hu hua
    have := r_nonneg 0 a u1
    refine mod_unique (k1 - k2) (r_nonneg _ _ _) (r_lt _ _ _) (by linarith) (by linarith) ?_
    push_cast; linarith
  have hout : ∀ u ∈ S, u ≠ a → r m a u < π := fun u hu hua => by
    rw [hrs u hu hua]; linarith [hout0 u hu hua, r_nonneg 0 a u1]
  have hu1z : r m a u1 = 0 := by rw [hrs u1 hu1.2 hu1.1, hm, sub_self]
  have hlab_a : lab n S m a = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro k hk
    obtain ⟨u, hu, hua, hsec⟩ := mem_lab.1 hk
    exact not_both m hua.symm (hout u hu hua) hsec.lt_pi
  -- `a` has an out-edge in the last sector
  have hexists : ∃ u ∈ S, u ≠ a ∧ π - π / n ≤ r m a u := by
    by_contra hno
    push Not at hno
    obtain ⟨b, hb, hlb⟩ := lab_surj H hn0 hcard m {⟨n - 1, by omega⟩}
    have hlab_b' : lab n S (m - π / n) b = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro k hk
      obtain ⟨u, hu, hub, hsec⟩ := mem_lab.1 hk
      rcases k with ⟨_ | j, hj⟩
      · change Sec n 0 _ at hsec
        have h2 := sec_shift_zero hn0 hsec
        have hbu : Sec n (n - 1) (r m b u) := by
          rcases r_swap m hub with ⟨h, -⟩ | ⟨-, h⟩
          · exfalso; linarith
          · exact sec_last hn0 (by rw [h]; linarith) (by rw [h]; linarith [r_lt m u b])
        have : (⟨n - 1, by omega⟩ : Fin n) ∈ lab n S m b := by
          rw [hlb]; exact Finset.mem_singleton_self _
        obtain ⟨w, hw, hwb, hw'⟩ := mem_lab.1 this
        have hwu : w ≠ u := by
          intro h; subst h; exact not_both m hwb hw'.lt_pi hbu.lt_pi
        exact two_path H hw hb hu hwb (Ne.symm hub) hwu hw' hbu
      · change Sec n (j + 1) _ at hsec
        have h2 := sec_shift_succ hn0 hsec
        have : (⟨j, by omega⟩ : Fin n) ∈ lab n S m b := mem_lab.2 ⟨u, hu, hub, h2⟩
        rw [hlb, Finset.mem_singleton, Fin.mk.injEq] at this
        omega
    have hlab_a' : lab n S (m - π / n) a = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro k hk
      obtain ⟨u, hu, hua, hsec⟩ := mem_lab.1 hk
      rcases k with ⟨_ | j, hj⟩
      · change Sec n 0 _ at hsec
        have h2 := sec_shift_zero hn0 hsec
        rcases r_swap m hua with ⟨h, -⟩ | ⟨-, h⟩
        · linarith
        · linarith [hno u hu hua]
      · change Sec n (j + 1) _ at hsec
        have h2 := sec_shift_succ hn0 hsec
        have : (⟨j, by omega⟩ : Fin n) ∈ lab n S m a := mem_lab.2 ⟨u, hu, hua, h2⟩
        rw [hlab_a] at this; simp at this
    have hab : a = b := lab_injOn H hn0 (m - π / n) ha hb (by rw [hlab_a', hlab_b'])
    subst hab
    rw [hlab_a] at hlb
    exact (Finset.singleton_nonempty _).ne_empty hlb.symm
  obtain ⟨u, hu, hua, hbig⟩ := hexists
  have hu1u : u ≠ u1 := by
    intro h; subst h; rw [hu1z] at hbig; linarith
  refine hcon ⟨u, hu, a, ha, u1, hu1.2, hua, hu1.1, hu1u, ?_⟩
  rw [angle_eq_r m hua hu1.1, hu1z, sub_zero]
  exact big_angle hn0 hbig (by linarith [hout u hu hua])

/-! ### The upper bound -/

/-- `uu n i = e^{iπ i/n}`. -/
def uu (n : ℕ) (i : Fin n) : ℂ := Complex.exp (((i : ℕ) * π / n : ℝ) * Complex.I)

lemma uu_norm (n : ℕ) (i : Fin n) : ‖uu n i‖ = 1 := Complex.norm_exp_ofReal_mul_I _

lemma uu_ne (n : ℕ) (i : Fin n) : uu n i ≠ 0 := Complex.exp_ne_zero _

lemma angle_uu {n : ℕ} (i j : Fin n) :
    InnerProductGeometry.angle (uu n i) (uu n j) = |((i : ℕ) : ℝ) - (j : ℕ)| * (π / n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast i.pos
  have hd : 0 < π / n := div_pos pi_pos hn'
  have hi : ((i : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
  have hj : ((j : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast j.isLt
  have hi0 : (0 : ℝ) ≤ (i : ℕ) := Nat.cast_nonneg _
  have hj0 : (0 : ℝ) ≤ (j : ℕ) := Nat.cast_nonneg _
  have e : ((i : ℕ) : ℝ) * π / n - ((j : ℕ) : ℝ) * π / n =
      (((i : ℕ) : ℝ) - (j : ℕ)) * (π / n) := by ring
  have hπ : (n : ℝ) * (π / n) = π := by field_simp
  have hlt : |((i : ℕ) : ℝ) - (j : ℕ)| * (π / n) < π := by
    have : |((i : ℕ) : ℝ) - (j : ℕ)| < n := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
    calc _ < (n : ℝ) * (π / n) := mul_lt_mul_of_pos_right this hd
      _ = π := hπ
  have habs : |(((i : ℕ) : ℝ) - (j : ℕ)) * (π / n)| = |((i : ℕ) : ℝ) - (j : ℕ)| * (π / n) := by
    rw [abs_mul, abs_of_pos hd]
  rw [uu, uu, Complex.angle_exp_exp, e]
  rw [(toIocMod_eq_self two_pi_pos).2, habs]
  rw [← habs] at hlt
  obtain ⟨h1, h2⟩ := abs_lt.1 hlt
  constructor <;> linarith

/-- The base directions `± e^{iπ i/n}`. -/
def bv (n : ℕ) (σ : Bool) (i : Fin n) : ℂ := if σ then -uu n i else uu n i

lemma bv_norm (n : ℕ) (σ : Bool) (i : Fin n) : ‖bv n σ i‖ = 1 := by
  unfold bv; split_ifs <;> simp [uu_norm]

lemma bv_ne (n : ℕ) (σ : Bool) (i : Fin n) : bv n σ i ≠ 0 := by
  intro h; have := bv_norm n σ i; rw [h, norm_zero] at this; exact zero_ne_one this

lemma angle_bv_le {n : ℕ} (σ τ : Bool) (i j : Fin n) (h : i = j → σ = τ) :
    InnerProductGeometry.angle (bv n σ i) (bv n τ j) ≤ (1 - 1 / (n : ℝ)) * π := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast i.pos
  have hd : 0 < π / n := div_pos pi_pos hn'
  have hβ : (1 - 1 / (n : ℝ)) * π = π - π / n := by field_simp
  have hπ : (n : ℝ) * (π / n) = π := by field_simp
  rw [hβ]
  by_cases hij : i = j
  · subst hij
    obtain rfl := h rfl
    have h1 : π / n ≤ π := div_le_self pi_pos.le (by exact_mod_cast i.pos)
    cases σ <;> simp [bv, InnerProductGeometry.angle_neg_neg,
      InnerProductGeometry.angle_self (uu_ne n i)] <;> linarith
  · have hi : ((i : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
    have hj : ((j : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast j.isLt
    have hi0 : (0 : ℝ) ≤ (i : ℕ) := Nat.cast_nonneg _
    have hj0 : (0 : ℝ) ≤ (j : ℕ) := Nat.cast_nonneg _
    have hne : (i : ℕ) ≠ j := fun h' => hij (Fin.ext h')
    have h1 : 1 ≤ |((i : ℕ) : ℝ) - (j : ℕ)| := by
      rcases Nat.lt_or_gt_of_ne hne with h' | h'
      · have : ((i : ℕ) : ℝ) + 1 ≤ (j : ℕ) := by exact_mod_cast h'
        rw [abs_sub_comm]; exact le_abs.2 (Or.inl (by linarith))
      · have : ((j : ℕ) : ℝ) + 1 ≤ (i : ℕ) := by exact_mod_cast h'
        exact le_abs.2 (Or.inl (by linarith))
    have h2 : |((i : ℕ) : ℝ) - (j : ℕ)| ≤ n - 1 := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
    have k1 : π / n ≤ InnerProductGeometry.angle (uu n i) (uu n j) := by
      rw [angle_uu]; nlinarith
    have k2 : InnerProductGeometry.angle (uu n i) (uu n j) ≤ π - π / n := by
      rw [angle_uu]; nlinarith
    cases σ <;> cases τ <;> simp only [bv, Bool.false_eq_true, ↓reduceIte,
      InnerProductGeometry.angle_neg_left, InnerProductGeometry.angle_neg_right] <;> linarith

lemma perturb (n : ℕ) {ε : ℝ} (hε : 0 < ε) : ∃ ρ > 0, ∀ (σ τ : Bool) (i j : Fin n) (η₁ η₂ : ℂ),
    ‖η₁‖ < ρ → ‖η₂‖ < ρ →
    InnerProductGeometry.angle (bv n σ i + η₁) (bv n τ j + η₂) <
      InnerProductGeometry.angle (bv n σ i) (bv n τ j) + ε := by
  have h : ∀ t : Bool × Fin n × Bool × Fin n, ∀ᶠ η : ℂ × ℂ in nhds 0,
      InnerProductGeometry.angle (bv n t.1 t.2.1 + η.1) (bv n t.2.2.1 t.2.2.2 + η.2) <
      InnerProductGeometry.angle (bv n t.1 t.2.1) (bv n t.2.2.1 t.2.2.2) + ε := by
    rintro ⟨σ, i, τ, j⟩
    have hc : ContinuousAt (fun η : ℂ × ℂ =>
        InnerProductGeometry.angle (bv n σ i + η.1) (bv n τ j + η.2)) 0 := by
      have := InnerProductGeometry.continuousAt_angle
        (x := (bv n σ i + (0 : ℂ × ℂ).1, bv n τ j + (0 : ℂ × ℂ).2))
        (by simpa using bv_ne n σ i) (by simpa using bv_ne n τ j)
      exact this.comp (f := fun η : ℂ × ℂ => (bv n σ i + η.1, bv n τ j + η.2)) (by fun_prop)
    have h0 : (fun η : ℂ × ℂ =>
        InnerProductGeometry.angle (bv n σ i + η.1) (bv n τ j + η.2)) 0 <
        InnerProductGeometry.angle (bv n σ i) (bv n τ j) + ε := by
      simp only [Prod.fst_zero, Prod.snd_zero, add_zero]; linarith
    exact hc.eventually (gt_mem_nhds h0)
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1 (Filter.eventually_all.2 h)
  refine ⟨ρ, hρ, fun σ τ i j η₁ η₂ h1 h2 => ?_⟩
  have hdist : dist (η₁, η₂) (0 : ℂ × ℂ) < ρ := by
    simpa [Prod.dist_eq] using max_lt h1 h2
  exact hball hdist (σ, i, τ, j)

/-- The scaled vectors `L^{-m} e^{iπ m/n}`. -/
def cc (n : ℕ) (L : ℝ) (m : Fin n) : ℂ := ((L⁻¹ ^ (m : ℕ) : ℝ) : ℂ) * uu n m

/-- The point `P(e) = ∑_{m ∈ e} L^{-m} e^{iπ m/n}`. -/
def P (n : ℕ) (L : ℝ) (e : Fin n → Bool) : ℂ := ∑ m, if e m then cc n L m else 0

/-- Coefficient of `cc m` in `P e' - P e`. -/
def dd {n : ℕ} (e e' : Fin n → Bool) (m : Fin n) : ℂ :=
  (if e' m then 1 else 0) - (if e m then 1 else 0)

lemma P_sub (n : ℕ) (L : ℝ) (e e' : Fin n → Bool) :
    P n L e' - P n L e = ∑ m, dd e e' m * cc n L m := by
  rw [P, P, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [dd]; split_ifs <;> ring

lemma first_diff {n : ℕ} {e e' : Fin n → Bool} (h : e ≠ e') :
    ∃ i, e i ≠ e' i ∧ ∀ m < i, e m = e' m := by
  classical
  have hne : (Finset.univ.filter (fun m => e m ≠ e' m)).Nonempty := by
    obtain ⟨m, hm⟩ := Function.ne_iff.1 h
    exact ⟨m, by simp [hm]⟩
  obtain ⟨i, hi, hmin⟩ := (Finset.univ.filter (fun m => e m ≠ e' m)).exists_min_image id hne
  refine ⟨i, (Finset.mem_filter.1 hi).2, fun m hm => ?_⟩
  by_contra hc
  exact absurd hm (not_lt.2 (hmin m (by simp [hc])))

lemma decomp {n : ℕ} {L : ℝ} (hL : 1 ≤ L) {e e' : Fin n → Bool} {i : Fin n}
    (hi : e i ≠ e' i) (hlt : ∀ m < i, e m = e' m) :
    ∃ η : ℂ, ‖η‖ ≤ n * L⁻¹ ∧
      P n L e' - P n L e = ((L⁻¹ ^ (i : ℕ) : ℝ) : ℂ) * (bv n (e i) i + η) := by
  have hL0 : 0 ≤ L⁻¹ := inv_nonneg.2 (by linarith)
  have hL1 : L⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hL
  refine ⟨∑ m, if i < m then dd e e' m * ((L⁻¹ ^ ((m : ℕ) - i) : ℝ) : ℂ) * uu n m else 0,
    ?_, ?_⟩
  · calc _ ≤ ∑ m : Fin n,
          ‖if i < m then dd e e' m * ((L⁻¹ ^ ((m : ℕ) - i) : ℝ) : ℂ) * uu n m else 0‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _m : Fin n, L⁻¹ := by
        apply Finset.sum_le_sum; intro m _
        split_ifs with h
        · have hd : ‖dd e e' m‖ ≤ 1 := by simp only [dd]; split_ifs <;> norm_num
          have hm : (i : ℕ) < m := h
          have hp : L⁻¹ ^ ((m : ℕ) - i) ≤ L⁻¹ := by
            calc L⁻¹ ^ ((m : ℕ) - i) ≤ L⁻¹ ^ 1 := pow_le_pow_of_le_one hL0 hL1 (by omega)
              _ = L⁻¹ := pow_one _
          rw [norm_mul, norm_mul, uu_norm, mul_one, Complex.norm_real,
            Real.norm_of_nonneg (pow_nonneg hL0 _)]
          calc ‖dd e e' m‖ * L⁻¹ ^ ((m : ℕ) - i) ≤ 1 * L⁻¹ :=
                mul_le_mul hd hp (pow_nonneg hL0 _) zero_le_one
            _ = L⁻¹ := one_mul _
        · simp [hL0]
      _ = n * L⁻¹ := by simp
  · have key : ∀ m, dd e e' m * cc n L m = ((L⁻¹ ^ (i : ℕ) : ℝ) : ℂ) *
        ((if m = i then bv n (e i) i else 0) +
          (if i < m then dd e e' m * ((L⁻¹ ^ ((m : ℕ) - i) : ℝ) : ℂ) * uu n m else 0)) := by
      intro m
      rcases lt_trichotomy m i with h | h | h
      · have := hlt m h
        simp [dd, this, ne_of_lt h, not_lt.2 h.le]
      · subst h
        cases h1 : e m <;> cases h2 : e' m <;> simp [dd, cc, bv, h1, h2] at hi ⊢
      · have hm : (i : ℕ) < m := h
        simp only [ne_of_gt h, h, ↓reduceIte, zero_add, cc]
        have : (L⁻¹ ^ (m : ℕ) : ℝ) = L⁻¹ ^ (i : ℕ) * L⁻¹ ^ ((m : ℕ) - i) := by
          rw [← pow_add, Nat.add_sub_cancel' hm.le]
        rw [this]; push_cast; ring
    rw [P_sub, Finset.sum_congr rfl (fun m _ => key m), ← Finset.mul_sum,
      Finset.sum_add_distrib]
    simp

theorem upper {n : ℕ} (hn : 2 ≤ n) {α : ℝ} (hα : (1 - 1 / (n : ℝ)) * π < α) :
    ∃ S : Finset ℂ, S.card = 2 ^ n ∧ ∀ x ∈ S, ∀ z ∈ S, ∀ y ∈ S, x ≠ z → y ≠ z →
      EuclideanGeometry.angle x z y < α := by
  obtain ⟨ρ, hρ, hpert⟩ := perturb n (sub_pos.2 hα)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = n * (ρ⁻¹ + 1) + 1 := ⟨_, rfl⟩
  have hnρ : 0 ≤ (n : ℝ) * (ρ⁻¹ + 1) := by positivity
  have hL1 : 1 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hsmall1 : (n : ℝ) * L⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one hLpos]; nlinarith [inv_pos.2 hρ]
  have hsmall2 : (n : ℝ) * L⁻¹ < ρ := by
    rw [← div_eq_mul_inv, div_lt_iff₀ hLpos]
    have : ρ * L = n + ρ * n + ρ := by rw [hLdef]; field_simp
    nlinarith
  have hpow : ∀ k : ℕ, 0 < L⁻¹ ^ k := fun k => pow_pos (inv_pos.2 hLpos) k
  have hinj : Function.Injective (P n L) := by
    intro e e' heq
    by_contra hne
    obtain ⟨i, hi, hlt⟩ := first_diff hne
    obtain ⟨η, hη, hP⟩ := decomp hL1 hi hlt
    rw [heq, sub_self] at hP
    have hc : ((L⁻¹ ^ (i : ℕ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hpow _).ne'
    have hz := (mul_eq_zero.1 hP.symm).resolve_left hc
    have hb : bv n (e i) i = -η := eq_neg_of_add_eq_zero_left hz
    have := bv_norm n (e i) i
    rw [hb, norm_neg] at this
    linarith
  refine ⟨Finset.univ.image (P n L), ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj]; simp
  · intro x hx z hz y hy hxz hyz
    obtain ⟨e', -, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.1 hz
    obtain ⟨e'', -, rfl⟩ := Finset.mem_image.1 hy
    have h1 : e ≠ e' := fun h => hxz (by rw [h])
    have h2 : e ≠ e'' := fun h => hyz (by rw [h])
    obtain ⟨i, hi, hlti⟩ := first_diff h1
    obtain ⟨j, hj, hltj⟩ := first_diff h2
    obtain ⟨η1, hη1, hP1⟩ := decomp hL1 hi hlti
    obtain ⟨η2, hη2, hP2⟩ := decomp hL1 hj hltj
    rw [EuclideanGeometry.angle, vsub_eq_sub, vsub_eq_sub, hP1, hP2, ← Complex.real_smul,
      ← Complex.real_smul, InnerProductGeometry.angle_smul_left_of_pos _ _ (hpow _),
      InnerProductGeometry.angle_smul_right_of_pos _ _ (hpow _)]
    have := hpert (e i) (e j) i j η1 η2 (by linarith) (by linarith)
    have hb := angle_bv_le (n := n) (e i) (e j) i j (fun h => by rw [h])
    linarith

end

end Blumenthal

namespace Erdos504

open Real EuclideanGeometry

/--
The minimax angle `α_N`: the supremum of all `α ∈ [0, π]` such that every set of `N` points of
the plane contains three pairwise distinct points `x, z, y` with `∠ x z y ≥ α` (angle taken at
the middle point `z`).  (Copied verbatim from `FormalConjectures/ErdosProblems/504.lean`.)
-/
noncomputable def minimaxAngle (N : ℕ) : ℝ :=
  sSup {α : ℝ | α ∈ Set.Icc 0 π ∧
    ∀ S : Finset ℂ, S.card = N →
      ∃ x ∈ S, ∃ z ∈ S, ∃ y ∈ S, x ≠ z ∧ y ≠ z ∧ x ≠ y ∧
        α ≤ EuclideanGeometry.angle x z y}

/-- **Erdős–Szekeres (1960).** For `n ≥ 3`, `α_{2^n} = π (1 - 1/n)`. -/
theorem erdos_504 {n : ℕ} (hn : 3 ≤ n) :
    minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π := by
  have hn2 : 2 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hmem : (1 - 1 / (n : ℝ)) * π ∈ {α : ℝ | α ∈ Set.Icc 0 π ∧
      ∀ S : Finset ℂ, S.card = 2 ^ n →
        ∃ x ∈ S, ∃ z ∈ S, ∃ y ∈ S, x ≠ z ∧ y ≠ z ∧ x ≠ y ∧
          α ≤ EuclideanGeometry.angle x z y} := by
    refine ⟨⟨?_, ?_⟩, fun S hS => Blumenthal.lower hn2 hS⟩
    · have : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hnR
      nlinarith [pi_pos]
    · have : 0 ≤ 1 / (n : ℝ) := by positivity
      nlinarith [pi_pos]
  unfold minimaxAngle
  apply le_antisymm
  · apply csSup_le ⟨_, hmem⟩
    intro α hα
    by_contra hlt
    push Not at hlt
    obtain ⟨S, hS, hang⟩ := Blumenthal.upper hn2 hlt
    obtain ⟨x, hx, z, hz, y, hy, hxz, hyz, -, hle⟩ := hα.2 S hS
    linarith [hang x hx z hz y hy hxz hyz]
  · exact le_csSup ⟨π, fun α hα => hα.1.2⟩ hmem

end Erdos504
