import Mathlib

/-!
# Parity of OEIS A000139 (Bala's conjecture)

`A000139 n = 2 * (3n)! / ((2n+1)! * (n+1)!)`
(rooted non-separable planar maps with `n` edges; also 2-stack-sortable permutations).

**Conjecture** (Peter Bala, OEIS A000139, Jul 24 2025; the same statement for
A007226 = (2n+1)·A000139, Mar 13 2023): `a(n)` is odd iff `n` is a term of A022341,
the *odd fibbinary numbers*: odd numbers whose binary expansion has no two adjacent 1s.

This file proves it (`A000139_odd_iff`).

Proof idea.  Let `s(m)` be the binary digit sum.  By Legendre, `v₂(m!) = m - s(m)`, so
`v₂(a(n)) = s(n) + s(n+1) - s(3n)`.  Since `s(x+y) ≤ s(x)+s(y)`, with equality iff
`x` and `y` have disjoint binary supports, a short case analysis on `n mod 4` shows
`s(3n) = s(n) + s(n+1)` exactly for odd fibbinary `n`.
-/

open Nat

namespace A000139

/-- OEIS A000139: `a(n) = 2*(3n)! / ((2n+1)! (n+1)!)`. -/
def a (n : ℕ) : ℕ := 2 * (3 * n)! / ((2 * n + 1)! * (n + 1)!)

/-- `n` is an odd fibbinary number (OEIS A022341): `n` is odd and no two adjacent bits
of `n` are both `1`. -/
def IsOddFibbinary (n : ℕ) : Prop :=
  n % 2 = 1 ∧ ∀ i, ¬ (n.testBit i = true ∧ n.testBit (i + 1) = true)

/-! ### Binary digit sums -/

/-- Binary digit sum. -/
def s (n : ℕ) : ℕ := (Nat.digits 2 n).sum

lemma s_zero : s 0 = 0 := by simp [s]

lemma s_rec (n : ℕ) : s n = n % 2 + s (n / 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [s]
  · rw [s, Nat.digits_def' (by norm_num) hn, List.sum_cons]; rfl

lemma s_double (n : ℕ) : s (2 * n) = s n := by
  rw [s_rec, show 2 * n % 2 = 0 by omega, show 2 * n / 2 = n by omega, zero_add]

lemma s_double_add_one (n : ℕ) : s (2 * n + 1) = s n + 1 := by
  rw [s_rec, show (2 * n + 1) % 2 = 1 by omega, show (2 * n + 1) / 2 = n by omega, add_comm]

lemma s_succ_le (n : ℕ) : s (n + 1) ≤ s n + 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [s_rec (n + 1), s_rec n]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have : (n + 1) / 2 = n / 2 := by omega
      rw [this]; omega
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp at h
      have h1 : (n + 1) / 2 = n / 2 + 1 := by omega
      have := ih (n / 2) (by omega)
      rw [h1]; omega

/-- Two numbers have disjoint binary supports. -/
def Disj (x y : ℕ) : Prop := ∀ i, ¬ (x.testBit i = true ∧ y.testBit i = true)

lemma disj_iff (x y : ℕ) :
    Disj x y ↔ ¬ (x % 2 = 1 ∧ y % 2 = 1) ∧ Disj (x / 2) (y / 2) := by
  constructor
  · intro h
    refine ⟨fun hc => h 0 (by simp [Nat.testBit_zero, hc.1, hc.2]), fun i hi => h (i + 1) ?_⟩
    rwa [Nat.testBit_succ, Nat.testBit_succ]
  · rintro ⟨h0, h⟩ i
    cases i with
    | zero => simpa [Nat.testBit_zero] using h0
    | succ i => rw [Nat.testBit_succ, Nat.testBit_succ]; exact h i

/-- Subadditivity of the binary digit sum, with the equality case. -/
theorem s_add (x y : ℕ) : s (x + y) ≤ s x + s y ∧ (s (x + y) = s x + s y ↔ Disj x y) := by
  induction x using Nat.strong_induction_on generalizing y with
  | _ x ih =>
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · refine ⟨by simp [s_zero], ?_⟩
      simp only [s_zero, zero_add, true_iff]
      intro i; simp
    have ihx := ih (x / 2) (by omega)
    rw [disj_iff, s_rec (x + y), s_rec x, s_rec y]
    by_cases hb : x % 2 = 1 ∧ y % 2 = 1
    · -- both odd: a carry occurs, strict inequality
      have e1 : (x + y) % 2 = 0 := by omega
      have e2 : (x + y) / 2 = x / 2 + (y / 2 + 1) := by omega
      rw [e1, e2]
      have h1 := (ihx (y / 2 + 1)).1
      have h2 := s_succ_le (y / 2)
      refine ⟨by omega, ?_⟩
      constructor
      · intro h; omega
      · rintro ⟨h, -⟩; exact absurd hb h
    · have e1 : (x + y) % 2 = x % 2 + y % 2 := by omega
      have e2 : (x + y) / 2 = x / 2 + y / 2 := by omega
      rw [e1, e2]
      obtain ⟨h1, h2⟩ := ihx (y / 2)
      refine ⟨by omega, ?_⟩
      rw [← h2]
      constructor
      · intro h; exact ⟨hb, by omega⟩
      · rintro ⟨-, h⟩; omega

lemma s_add_le (x y : ℕ) : s (x + y) ≤ s x + s y := (s_add x y).1

/-- No two adjacent 1-bits. -/
def NoAdj (n : ℕ) : Prop := ∀ i, ¬ (n.testBit i = true ∧ n.testBit (i + 1) = true)

lemma disj_double_iff (j : ℕ) : Disj j (2 * j) ↔ NoAdj j := by
  constructor
  · intro h i hi
    apply h (i + 1)
    refine ⟨hi.2, ?_⟩
    rw [Nat.testBit_succ, show 2 * j / 2 = j by omega]; exact hi.1
  · intro h i hi
    cases i with
    | zero =>
      have : (2 * j) % 2 = 0 := by omega
      simp [Nat.testBit_zero, this] at hi
    | succ i =>
      rw [Nat.testBit_succ (2 * j), show 2 * j / 2 = j by omega] at hi
      exact h i ⟨hi.2, hi.1⟩

/-- The combinatorial heart: `s(3n) = s(n) + s(n+1)` iff `n` is an odd fibbinary number. -/
theorem key (n : ℕ) : s (3 * n) = s n + s (n + 1) ↔ IsOddFibbinary n := by
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn
  · -- n even: strict inequality
    have h1 : s (n + 1) = s n + 1 := by
      rw [s_rec (n + 1), s_rec n, show (n + 1) / 2 = n / 2 by omega]; omega
    have h2 : s (3 * n) ≤ s n + s n := by
      have := s_add_le n (2 * n)
      rw [s_double, show n + 2 * n = 3 * n by ring] at this; exact this
    constructor
    · intro h; omega
    · rintro ⟨h, -⟩; omega
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
    have hs1 : s (2 * m + 1) = s m + 1 := s_double_add_one m
    have hs2 : s (2 * m + 1 + 1) = s (m + 1) := by
      rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring, s_double]
    have hs3 : s (3 * (2 * m + 1)) = s (3 * m + 1) + 1 := by
      rw [s_rec]; rw [show 3 * (2 * m + 1) % 2 = 1 by omega,
        show 3 * (2 * m + 1) / 2 = 3 * m + 1 by omega]; omega
    rw [hs1, hs2, hs3]
    rcases Nat.mod_two_eq_zero_or_one m with hm | hm
    · -- n = 4j + 1
      obtain ⟨j, rfl⟩ : ∃ j, m = 2 * j := ⟨m / 2, by omega⟩
      have t1 : s (3 * (2 * j) + 1) = s (3 * j) + 1 := by
        rw [s_rec]; rw [show (3 * (2 * j) + 1) % 2 = 1 by omega,
          show (3 * (2 * j) + 1) / 2 = 3 * j by omega]; omega
      have t2 : s (2 * j + 1) = s j + 1 := s_double_add_one j
      rw [t1, t2, s_double]
      have e := (s_add j (2 * j)).2
      rw [s_double, show j + 2 * j = 3 * j by ring, disj_double_iff] at e
      have : s (3 * j) + 1 + 1 = s j + 1 + (s j + 1) ↔ s (3 * j) = s j + s j := by omega
      rw [this, e]
      -- NoAdj j ↔ IsOddFibbinary (4j+1)
      unfold IsOddFibbinary NoAdj
      have b0 : ∀ i, (2 * (2 * j) + 1).testBit (i + 2) = j.testBit i := by
        intro i
        rw [Nat.testBit_succ, Nat.testBit_succ,
          show (2 * (2 * j) + 1) / 2 / 2 = j by omega]
      have b1 : (2 * (2 * j) + 1).testBit 1 = false := by
        rw [Nat.testBit_succ, show (2 * (2 * j) + 1) / 2 = 2 * j by omega,
          Nat.testBit_zero]; simp
      constructor
      · intro h
        refine ⟨by omega, fun i hi => ?_⟩
        match i, hi with
        | 0, hi => rw [b1] at hi; simp at hi
        | 1, hi => rw [b1] at hi; simp at hi
        | i + 2, hi =>
          rw [b0, show i + 2 + 1 = (i + 1) + 2 by ring, b0] at hi; exact h i hi
      · rintro ⟨-, h⟩ i hi
        apply h (i + 2)
        rw [b0, show i + 2 + 1 = (i + 1) + 2 by ring, b0]; exact hi
    · -- n = 4j + 3: never
      obtain ⟨j, rfl⟩ : ∃ j, m = 2 * j + 1 := ⟨m / 2, by omega⟩
      have t1 : s (3 * (2 * j + 1) + 1) = s (3 * j + 2) := by
        rw [show 3 * (2 * j + 1) + 1 = 2 * (3 * j + 2) by ring, s_double]
      have t2 : s (2 * j + 1) = s j + 1 := s_double_add_one j
      have t3 : s (2 * j + 1 + 1) = s (j + 1) := by
        rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, s_double]
      have t4 : s (3 * j + 2) ≤ s j + s (j + 1) := by
        have := s_add_le j (2 * (j + 1))
        rw [s_double, show j + 2 * (j + 1) = 3 * j + 2 by ring] at this; exact this
      rw [t1, t2, t3]
      constructor
      · intro h; omega
      · rintro ⟨-, h⟩
        exfalso; apply h 0
        constructor
        · rw [Nat.testBit_zero]; simp
        · rw [Nat.testBit_succ, Nat.testBit_zero]; simp; omega

/-! ### Legendre's formula and the valuation of `a(n)` -/

/-- Legendre for `p = 2`: `v₂(m!) + s(m) = m`. -/
lemma legendre (m : ℕ) : multiplicity 2 m ! + s m = m := by
  have h := Nat.Prime.sub_one_mul_multiplicity_factorial (n := m) Nat.prime_two
  have hle : s m ≤ m := Nat.digit_sum_le 2 m
  simp only [show (2 : ℕ) - 1 = 1 from rfl, one_mul] at h
  unfold s at hle ⊢; omega

/-- `(n+1)(2n+1) ∣ 2·C(3n, n)`. -/
lemma dvd_two_choose (n : ℕ) : (n + 1) * (2 * n + 1) ∣ 2 * (3 * n).choose n := by
  have hA : (2 * n + 1) ∣ (3 * n).choose n := by
    -- C(3n, n-1)·(2n+1) = C(3n, n)·n  (for n ≥ 1)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have e := Nat.choose_succ_right_eq (3 * (k + 1)) k
    rw [show 3 * (k + 1) - k = 2 * (k + 1) + 1 by omega] at e
    have hc : Nat.Coprime (2 * (k + 1) + 1) (k + 1) := by
      rw [Nat.coprime_comm, Nat.Coprime, show 2 * (k + 1) + 1 = 1 + (k + 1) * 2 by ring,
        Nat.gcd_add_mul_left_right]; simp
    exact hc.dvd_of_dvd_mul_right ⟨(3 * (k + 1)).choose k, by rw [e]; ring⟩
  have hB : (n + 1) ∣ 2 * (3 * n).choose n := by
    -- C(3n, n+1)·(n+1) = C(3n, n)·2n
    have e := Nat.choose_succ_right_eq (3 * n) n
    rw [show 3 * n - n = 2 * n by omega] at e
    have hc : Nat.Coprime (n + 1) n := by
      rw [Nat.Coprime, Nat.gcd_comm]; simp
    have : (n + 1) ∣ n * (2 * (3 * n).choose n) := ⟨(3 * n).choose (n + 1), by linarith⟩
    exact hc.dvd_of_dvd_mul_left this
  have hc : Nat.Coprime (n + 1) (2 * n + 1) := by
    rw [Nat.Coprime, show 2 * n + 1 = n + (n + 1) * 1 by ring, Nat.gcd_add_mul_left_right]
    simp
  exact hc.mul_dvd_of_dvd_of_dvd hB (hA.mul_left 2)

/-- `a(n)` is an exact quotient: `(2n+1)! (n+1)! · a(n) = 2 (3n)!`. -/
lemma a_mul (n : ℕ) : (2 * n + 1)! * (n + 1)! * a n = 2 * (3 * n)! := by
  obtain ⟨q, hq⟩ := dvd_two_choose n
  have hf : (3 * n).choose n * n ! * (2 * n)! = (3 * n)! := by
    have := Nat.choose_mul_factorial_mul_factorial (show n ≤ 3 * n by omega)
    rwa [show 3 * n - n = 2 * n by omega] at this
  have hN : 2 * (3 * n)! = (2 * n + 1)! * (n + 1)! * q := by
    rw [← hf, Nat.factorial_succ (2 * n), Nat.factorial_succ n]
    calc 2 * ((3 * n).choose n * n ! * (2 * n)!)
        = (2 * (3 * n).choose n) * n ! * (2 * n)! := by ring
      _ = _ := by rw [hq]; ring
  have hD : 0 < (2 * n + 1)! * (n + 1)! := by positivity
  unfold a
  rw [hN, Nat.mul_div_cancel_left _ hD]

/-- **Bala's conjecture (OEIS A000139).** `a(n)` is odd iff `n` is an odd fibbinary number
(OEIS A022341). -/
theorem A000139_odd_iff (n : ℕ) : Odd (a n) ↔ IsOddFibbinary n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmul := a_mul n
  have ha0 : a n ≠ 0 := by
    intro h; rw [h, mul_zero] at hmul; have := Nat.factorial_pos (3 * n); omega
  have hv := congrArg (multiplicity 2) hmul
  rw [Nat.multiplicity_mul (by positivity) ha0, Nat.multiplicity_mul (by positivity)
      (by positivity), Nat.multiplicity_mul (by norm_num) (by positivity),
      Nat.multiplicity_self (by norm_num : 1 < 2)] at hv
  have l1 := legendre (2 * n + 1)
  have l2 := legendre (n + 1)
  have l3 := legendre (3 * n)
  have hs : s (2 * n + 1) = s n + 1 := s_double_add_one n
  have hodd : Odd (a n) ↔ multiplicity 2 (a n) = 0 := by
    rw [multiplicity_eq_zero (Nat.finiteMultiplicity_iff.2 ⟨by norm_num, Nat.pos_of_ne_zero ha0⟩),
      Nat.two_dvd_ne_zero, Nat.odd_iff]
  rw [hodd, ← key]
  omega

end A000139
