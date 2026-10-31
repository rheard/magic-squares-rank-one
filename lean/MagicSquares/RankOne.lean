import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import MagicSquares.Basic

/-!
# Rank-one exclusion for magic squares of squares

This file formalizes the note *Magic squares of squares and elliptic divisibility sequences: the
rank-one case*.

Write a magic square of squares in Lucas form
```
E+a     E-a-b   E+b
E-a+b   E       E+a-b
E-b     E+a+b   E-a
```
and `b = n k²`. Each of the three `b`-progressions `E+αa-b, E+αa, E+αa+b` (`α ∈ {-1, 0, 1}`) gives a
point `P_α` on the congruent number curve `E_n : y² = x³ - n²x` with `x(P_α) = (E+αa)/k²`, so that
`x(P_{-1}) + x(P_1) = 2 x(P_0)` (Robertson, 1996). The main results are:

* `RankOne.xc_add_ne_two_mul` (**Lemma 3.1**): on a Weierstrass curve with integer coefficients, if
  `Q` has primitive divisors and the integers `m₁, m₂, m₃` are nonzero with distinct absolute values,
  then `x(m₁Q) + x(m₃Q) ≠ 2 x(m₂Q)`.
* `RankOne.ThreeProgressions.two_le_finrank` (**Theorem 1.1**): the three points generate a subgroup
  of `E_n(ℚ)` of rank at least two.
* `MagicSquareOfSquares.rank_two_of_antidiagonal` and `MagicSquareOfSquares.rank_two_of_diagonal`
  (**Corollary 1.2**): if a diagonal of a magic square of squares has common difference `n k²`, then
  `E_n(ℚ)` contains two `ℤ`-linearly independent points.

Two published theorems are used. They enter as the hypotheses `PrimitiveDivisorTheorem n` and
`TorsionTheorem n`, not as axioms, so `#print axioms` shows only Lean's standard axioms. Everything
else, including the group-law computations, is proved here.
-/

namespace MagicSquares.RankOne

open WeierstrassCurve WeierstrassCurve.Affine

/-! ### The curves `y² = x³ + Dx` -/

/-- The curve `W_D : y² = x³ + D x` over `ℚ`. -/
def W (D : ℚ) : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := D
  a₆ := 0

/-- The congruent number curve `E_n : y² = x³ - n² x`. -/
abbrev E (n : ℤ) : WeierstrassCurve ℚ := W (-(n : ℚ) ^ 2)

lemma W_Δ (D : ℚ) : (W D).Δ = -64 * D ^ 3 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, W]
  ring

lemma equation_W {D x y : ℚ} : (W D).toAffine.Equation x y ↔ y ^ 2 = x ^ 3 + D * x := by
  rw [equation_iff]
  simp only [W]
  constructor <;> intro h <;> linear_combination h

lemma negY_W (D x y : ℚ) : (W D).toAffine.negY x y = -y := by
  simp only [negY, W]
  ring

/-- The affine point `(x, y)` of `W_D`, for `D ≠ 0`. -/
def pt {D : ℚ} (hD : D ≠ 0) {x y : ℚ} (h : y ^ 2 = x ^ 3 + D * x) : (W D).toAffine.Point :=
  .some x y <| (equation_iff_nonsingular_of_Δ_ne_zero <| by
    rw [W_Δ]; exact mul_ne_zero (by norm_num) (pow_ne_zero 3 hD)).mp (equation_W.mpr h)

lemma pt_ne_zero {D : ℚ} (hD : D ≠ 0) {x y : ℚ} (h : y ^ 2 = x ^ 3 + D * x) : pt hD h ≠ 0 :=
  Point.some_ne_zero _

/-- The `x`-coordinate of a point of a Weierstrass curve `C` over `ℚ`, with the convention
`x(O) = 0`. -/
def xc {C : WeierstrassCurve ℚ} : C.toAffine.Point → ℚ
  | .zero => 0
  | .some x _ _ => x

@[simp]
lemma xc_zero {C : WeierstrassCurve ℚ} : xc (0 : C.toAffine.Point) = 0 :=
  rfl

@[simp]
lemma xc_some {C : WeierstrassCurve ℚ} {x y : ℚ} (h : C.toAffine.Nonsingular x y) :
    xc (.some x y h : C.toAffine.Point) = x :=
  rfl

lemma xc_pt {D : ℚ} (hD : D ≠ 0) {x y : ℚ} (h : y ^ 2 = x ^ 3 + D * x) : xc (pt hD h) = x :=
  rfl

@[simp]
lemma xc_neg {C : WeierstrassCurve ℚ} (P : C.toAffine.Point) : xc (-P) = xc P := by
  cases P <;> rfl

/-- `x(mP) = x(|m|P)`. -/
lemma xc_zsmul {C : WeierstrassCurve ℚ} (m : ℤ) (P : C.toAffine.Point) :
    xc (m • P) = xc (m.natAbs • P) := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · simp
  · simp

/-- The `x`-coordinate of a double is a square: `x(2R) = ((x² - D) / 2y)²`. -/
lemma isSquare_xc_two_nsmul {D : ℚ} (R : (W D).toAffine.Point) : IsSquare (xc (2 • R)) := by
  rw [two_nsmul]
  rcases R with _ | ⟨x, y, h⟩
  · exact ⟨0, by rw [mul_zero]; rfl⟩
  by_cases hy : y = (W D).toAffine.negY x y
  · rw [Point.add_self_of_Y_eq hy]
    exact ⟨0, by rw [mul_zero]; rfl⟩
  have heq := equation_W.mp h.1
  have hy0 : y ≠ 0 := fun h0 => hy (by rw [negY_W, h0, neg_zero])
  rw [Point.add_self_of_Y_ne hy, xc_some, slope_of_Y_ne rfl hy, negY_W,
    show y - -y = 2 * y by ring]
  refine ⟨(x ^ 2 - D) / (2 * y), ?_⟩
  simp only [addX, W]
  field_simp
  linear_combination (-8 * x) * heq

/-! ### Weierstrass equations with integer coefficients -/

/-- The Weierstrass equation `C : y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` has integer coefficients. -/
def HasIntCoeffs (C : WeierstrassCurve ℚ) : Prop :=
  ∃ a₁ a₂ a₃ a₄ a₆ : ℤ, C = ⟨a₁, a₂, a₃, a₄, a₆⟩

lemma hasIntCoeffs_E (n : ℤ) : HasIntCoeffs (E n) :=
  ⟨0, 0, 0, -n ^ 2, 0, by simp [E, W]⟩

/-! ### Valuations -/

section Valuation

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- A prime divides the denominator of `q` exactly when `q` has negative `ℓ`-adic valuation. -/
lemma dvd_den_iff (q : ℚ) : ℓ ∣ q.den ↔ padicValRat ℓ q < 0 := by
  rw [padicValRat_def]
  constructor
  · intro h
    have hnum : ¬ (ℓ : ℤ) ∣ q.num := fun hn => hℓ.out.one_lt.ne'
      ((Nat.Coprime.coprime_dvd_left (Int.natCast_dvd.mp hn) q.reduced).eq_one_of_dvd h)
    rw [padicValInt.eq_zero_of_not_dvd hnum]
    have := one_le_padicValNat_of_dvd q.den_nz h
    omega
  · intro h
    by_contra hd
    rw [padicValNat.eq_zero_of_not_dvd hd] at h
    omega

/-- `v(q + r) = v(q)` when `v(q) < v(r)` or `r = 0`. -/
lemma padicValRat_add_eq_left {q r : ℚ} (hq : q ≠ 0)
    (hlt : r ≠ 0 → padicValRat ℓ q < padicValRat ℓ r) :
    padicValRat ℓ (q + r) = padicValRat ℓ q := by
  rcases eq_or_ne r 0 with rfl | hr
  · rw [add_zero]
  have hqr := hlt hr
  have hsum : q + r ≠ 0 := fun hs => by
    rw [eq_neg_of_add_eq_zero_right hs, padicValRat.neg] at hqr
    exact lt_irrefl _ hqr
  exact padicValRat.add_eq_of_lt hsum hq hr hqr

/-- Lower bounds `c ≤ 0` for valuations pass to sums (also when the sum is `0`). -/
lemma le_padicValRat_add {c : ℤ} (hc : c ≤ 0) {q r : ℚ} (hq : c ≤ padicValRat ℓ q)
    (hr : c ≤ padicValRat ℓ r) : c ≤ padicValRat ℓ (q + r) := by
  rcases eq_or_ne (q + r) 0 with h | h
  · rw [h, padicValRat.zero]
    exact hc
  · exact (le_min hq hr).trans (padicValRat.min_le_padicValRat_add h)

omit hℓ in
/-- An integer has valuation at least `c` for every `c ≤ 0`. -/
lemma le_padicValRat_intCast {c : ℤ} (hc : c ≤ 0) (z : ℤ) : c ≤ padicValRat ℓ z := by
  rw [padicValRat.of_int]
  have : (0 : ℤ) ≤ (padicValInt ℓ z : ℤ) := by positivity
  omega

/-- Lower bounds `c ≤ 0` for valuations pass to integer multiples. -/
lemma le_padicValRat_intCast_mul {c : ℤ} (hc : c ≤ 0) (z : ℤ) {q : ℚ}
    (hq : c ≤ padicValRat ℓ q) : c ≤ padicValRat ℓ (z * q) := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [Int.cast_zero, zero_mul, padicValRat.zero]
    exact hc
  rcases eq_or_ne q 0 with rfl | hq0
  · rw [mul_zero, padicValRat.zero]
    exact hc
  rw [padicValRat.mul (by exact_mod_cast hz) hq0, padicValRat.of_int]
  have : (0 : ℤ) ≤ (padicValInt ℓ z : ℤ) := by positivity
  omega

/-- On a Weierstrass equation with integer coefficients, a negative valuation of `x` is even, so it
is at most `-2`. If `v(x) = -t < 0`, the right-hand side has valuation `-3t`. This forces
`v(y) < -t`, and then `y²` dominates the left-hand side, so `2 v(y) = -3t`. -/
lemma padicValRat_le_of_weierstrass {a₁ a₂ a₃ a₄ a₆ : ℤ} {x y : ℚ}
    (h : y ^ 2 + a₁ * x * y + a₃ * y = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆)
    (hv : padicValRat ℓ x < 0) : padicValRat ℓ x ≤ -2 := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hv
  have hc : padicValRat ℓ x ≤ 0 := hv.le
  have hc2 : 2 * padicValRat ℓ x ≤ 0 := by omega
  have hx2 : padicValRat ℓ (x ^ 2) = 2 * padicValRat ℓ x := by simp
  have hx3 : padicValRat ℓ (x ^ 3) = 3 * padicValRat ℓ x := by simp
  -- The right-hand side has valuation `3 v(x)`.
  have hrest : 2 * padicValRat ℓ x ≤ padicValRat ℓ (a₂ * x ^ 2 + a₄ * x + a₆) :=
    le_padicValRat_add hc2
      (le_padicValRat_add hc2 (le_padicValRat_intCast_mul hc2 a₂ hx2.ge)
        (le_padicValRat_intCast_mul hc2 a₄ (by omega : 2 * padicValRat ℓ x ≤ padicValRat ℓ x)))
      (le_padicValRat_intCast hc2 a₆)
  have hR : padicValRat ℓ (x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆) = 3 * padicValRat ℓ x := by
    have := padicValRat_add_eq_left (ℓ := ℓ) (q := x ^ 3) (r := a₂ * x ^ 2 + a₄ * x + a₆)
      (pow_ne_zero 3 hx0) (fun _ => by omega)
    rw [show x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆ = x ^ 3 + (a₂ * x ^ 2 + a₄ * x + a₆) by ring, this, hx3]
  have hR0 : x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆ ≠ 0 := by
    intro h0
    rw [h0, padicValRat.zero] at hR
    omega
  -- The left-hand side is `y (y + (a₁ x + a₃))`.
  rw [show y ^ 2 + a₁ * x * y + a₃ * y = y * (y + (a₁ * x + a₃)) by ring] at h
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hR0 (by rw [← h]; ring)
  have hz0 : y + (a₁ * x + a₃) ≠ 0 := by
    intro h0
    exact hR0 (by rw [← h, h0, mul_zero])
  have hL := congrArg (padicValRat ℓ) h
  rw [padicValRat.mul hy0 hz0, hR] at hL
  have hlin : padicValRat ℓ x ≤ padicValRat ℓ (a₁ * x + a₃) :=
    le_padicValRat_add hc (le_padicValRat_intCast_mul hc a₁ le_rfl) (le_padicValRat_intCast hc a₃)
  by_cases hy : padicValRat ℓ x ≤ padicValRat ℓ y
  · -- Then the left-hand side has valuation `≥ 2 v(x) > 3 v(x)`.
    have := le_padicValRat_add hc hy hlin
    omega
  · -- Then `v(y + (a₁ x + a₃)) = v(y)`, so `2 v(y) = 3 v(x)` and `v(x)` is even.
    have := padicValRat_add_eq_left (ℓ := ℓ) (q := y) (r := a₁ * x + a₃) hy0 (fun _ => by omega)
    rw [this] at hL
    omega

/-- On a Weierstrass equation with integer coefficients, the `x`-coordinate of a point has
valuation `≥ 0` or `≤ -2`. -/
lemma padicValRat_xc_le {C : WeierstrassCurve ℚ} (hC : HasIntCoeffs C) (P : C.toAffine.Point)
    (hv : padicValRat ℓ (xc P) < 0) : padicValRat ℓ (xc P) ≤ -2 := by
  obtain ⟨a₁, a₂, a₃, a₄, a₆, rfl⟩ := hC
  rcases P with _ | ⟨x, y, h⟩
  · simp [xc] at hv
  · exact padicValRat_le_of_weierstrass ((equation_iff x y).mp h.1) hv

omit hℓ in
lemma padicValRat_two_eq : padicValRat ℓ 2 = padicValNat ℓ 2 := by
  exact_mod_cast padicValRat.of_nat (p := ℓ) (n := 2)

lemma padicValRat_two_le : padicValRat ℓ 2 ≤ 1 := by
  rw [padicValRat_two_eq]
  rcases eq_or_ne ℓ 2 with rfl | hne
  · simp
  · rw [padicValNat.eq_zero_of_not_dvd fun hd =>
      hne ((Nat.prime_dvd_prime_iff_eq hℓ.out Nat.prime_two).mp hd)]
    norm_num

lemma padicValRat_add_nonneg {q r : ℚ} (hq : 0 ≤ padicValRat ℓ q) (hr : 0 ≤ padicValRat ℓ r) :
    0 ≤ padicValRat ℓ (q + r) := by
  rcases eq_or_ne (q + r) 0 with h | h
  · rw [h, padicValRat.zero]
  · exact (le_min hq hr).trans (padicValRat.min_le_padicValRat_add h)

lemma padicValRat_two_mul_nonneg {q : ℚ} (hq : 0 ≤ padicValRat ℓ q) :
    0 ≤ padicValRat ℓ (2 * q) := by
  rcases eq_or_ne q 0 with rfl | h
  · simp
  · rw [padicValRat.mul two_ne_zero h, padicValRat_two_eq]
    omega

end Valuation

/-! ### Primitive divisors and Lemma 3.1 -/

/-- Every term `B_M(Q)` with `M ≥ 3` of the elliptic divisibility sequence of `Q` has a primitive
divisor. Here `x(mQ) = A_m / B_m²` in lowest terms, so a prime divides `B_m` exactly when it divides
the denominator of `x(mQ)`. -/
def HasPrimitiveDivisors {C : WeierstrassCurve ℚ} (Q : C.toAffine.Point) : Prop :=
  ∀ M : ℕ, 3 ≤ M → ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ (xc (M • Q)).den ∧
    ∀ m : ℕ, 1 ≤ m → m < M → ¬ ℓ ∣ (xc (m • Q)).den

/-- A primitive divisor `ℓ` of `B_M` gives `v_ℓ(x(MQ)) ≤ -2` and `v_ℓ(x(iQ)) ≥ 0` for `i < M`. -/
lemma HasPrimitiveDivisors.valuations {C : WeierstrassCurve ℚ} (hC : HasIntCoeffs C)
    {Q : C.toAffine.Point} (hQ : HasPrimitiveDivisors Q) {M i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j)
    (hij : i ≠ j) (hiM : i < M) (hjM : j < M) :
    ∃ ℓ : ℕ, ∃ _ : Fact ℓ.Prime, padicValRat ℓ (xc (M • Q)) ≤ -2 ∧
      0 ≤ padicValRat ℓ (xc (i • Q)) ∧ 0 ≤ padicValRat ℓ (xc (j • Q)) := by
  obtain ⟨ℓ, hℓ, hM, hlt⟩ := hQ M (by omega)
  have := Fact.mk hℓ
  refine ⟨ℓ, this, padicValRat_xc_le hC _ ((dvd_den_iff _).mp hM), ?_, ?_⟩
  · exact not_lt.mp fun h => hlt i hi hiM ((dvd_den_iff _).mpr h)
  · exact not_lt.mp fun h => hlt j hj hjM ((dvd_den_iff _).mpr h)

/-- Lemma 3.1 for positive indices. -/
theorem xc_add_ne_two_mul_nat {C : WeierstrassCurve ℚ} (hC : HasIntCoeffs C)
    {Q : C.toAffine.Point} (hQ : HasPrimitiveDivisors Q) {a b c : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hc : 1 ≤ c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    xc (a • Q) + xc (c • Q) ≠ 2 * xc (b • Q) := by
  intro hap
  obtain ⟨hab', hcb'⟩ | ⟨hba', hca'⟩ | ⟨hac', hbc'⟩ :
      (a < b ∧ c < b) ∨ (b < a ∧ c < a) ∨ (a < c ∧ b < c) := by omega
  · -- The largest index is in the middle: `2 x(bQ)` has negative valuation, the left side does not.
    obtain ⟨ℓ, _, hM, hva, hvc⟩ := hQ.valuations hC ha hc hac hab' hcb'
    have hb0 : xc (b • Q) ≠ 0 := by
      intro h0
      rw [h0, padicValRat.zero] at hM
      omega
    have h := padicValRat_add_nonneg hva hvc
    rw [hap, padicValRat.mul two_ne_zero hb0] at h
    have := padicValRat_two_le (ℓ := ℓ)
    omega
  · -- The largest index is first: `x(aQ) = 2 x(bQ) - x(cQ)` would have valuation `≥ 0`.
    obtain ⟨ℓ, _, hM, hvb, hvc⟩ := hQ.valuations hC hb hc hbc hba' hca'
    have h := padicValRat_add_nonneg (padicValRat_two_mul_nonneg hvb)
      (by rwa [padicValRat.neg] : 0 ≤ padicValRat ℓ (-xc (c • Q)))
    rw [show 2 * xc (b • Q) + -xc (c • Q) = xc (a • Q) by linarith] at h
    omega
  · -- The largest index is last: `x(cQ) = 2 x(bQ) - x(aQ)` would have valuation `≥ 0`.
    obtain ⟨ℓ, _, hM, hva, hvb⟩ := hQ.valuations hC ha hb hab hac' hbc'
    have h := padicValRat_add_nonneg (padicValRat_two_mul_nonneg hvb)
      (by rwa [padicValRat.neg] : 0 ≤ padicValRat ℓ (-xc (a • Q)))
    rw [show 2 * xc (b • Q) + -xc (a • Q) = xc (c • Q) by linarith] at h
    omega

/-- **Lemma 3.1.** Let `Q` be a point, with primitive divisors, of a Weierstrass curve with integer
coefficients, and let `m₁, m₂, m₃` be nonzero integers with pairwise distinct absolute values. Then
`x(m₁Q) + x(m₃Q) ≠ 2 x(m₂Q)`. -/
theorem xc_add_ne_two_mul {C : WeierstrassCurve ℚ} (hC : HasIntCoeffs C) {Q : C.toAffine.Point}
    (hQ : HasPrimitiveDivisors Q) {m₁ m₂ m₃ : ℤ} (h₁ : m₁ ≠ 0) (h₂ : m₂ ≠ 0) (h₃ : m₃ ≠ 0)
    (h₁₂ : m₁.natAbs ≠ m₂.natAbs) (h₁₃ : m₁.natAbs ≠ m₃.natAbs) (h₂₃ : m₂.natAbs ≠ m₃.natAbs) :
    xc (m₁ • Q) + xc (m₃ • Q) ≠ 2 * xc (m₂ • Q) := by
  rw [xc_zsmul m₁, xc_zsmul m₂, xc_zsmul m₃]
  exact xc_add_ne_two_mul_nat hC hQ (Int.natAbs_pos.mpr h₁) (Int.natAbs_pos.mpr h₂)
    (Int.natAbs_pos.mpr h₃) h₁₂ h₁₃ h₂₃

/-! ### The two cited theorems -/

/-- **The primitive divisor theorem of Voutier–Yabuta, as corrected by Verzobio** (Theorem 2.2 of
the note), for `E_n`: every non-torsion point `Q ∈ E_n(ℚ)` whose `x`-coordinate is a square has
primitive divisors. It applies when `n` is squarefree, because then `-n²` is fourth-power-free and
`y² = x³ - n²x` is a minimal model (Lemma 2.1(d) of the note).

* P. Voutier and M. Yabuta, *Primitive divisors of certain elliptic divisibility sequences*,
  Acta Arith. 151 (2012), 165–190.
* M. Verzobio, *Primitive divisors of elliptic divisibility sequences for elliptic curves with
  j = 1728*, Acta Arith. 198 (2021); arXiv:2001.09634. -/
def PrimitiveDivisorTheorem (n : ℤ) : Prop :=
  ∀ Q : (E n).toAffine.Point, addOrderOf Q = 0 → IsSquare (xc Q) → HasPrimitiveDivisors Q

/-- **The torsion subgroup of `E_n(ℚ)` is `E_n[2]`** (Lemma 2.1(a) of the note): every point of
finite order has order dividing two. This is classical for every `n ≠ 0`; see N. Koblitz,
*Introduction to Elliptic Curves and Modular Forms*, 2nd ed., Ch. I, §9. -/
def TorsionTheorem (n : ℤ) : Prop :=
  ∀ P : (E n).toAffine.Point, IsOfFinAddOrder P → 2 • P = 0

/-! ### Halving on `E_n` (Lemma 2.1(b)) -/

lemma neg_sq_ne_zero {n : ℤ} (hn : n ≠ 0) : -(n : ℚ) ^ 2 ≠ 0 :=
  neg_ne_zero.mpr (pow_ne_zero 2 (by exact_mod_cast hn))

section Halving

variable {n : ℤ} {r₁ r₂ r₃ : ℚ}

lemma half_eq (h₂ : r₂ ^ 2 = r₁ ^ 2 - n) (h₃ : r₃ ^ 2 = r₁ ^ 2 + n) :
    ((r₁ + r₂) * (r₁ + r₃) * (r₂ + r₃)) ^ 2 =
      ((r₁ + r₂) * (r₁ + r₃)) ^ 3 + -(n : ℚ) ^ 2 * ((r₁ + r₂) * (r₁ + r₃)) := by
  linear_combination ((r₁ + r₂) * (r₁ + r₃) * ((r₁ + r₂) * (r₁ + r₃) + n)) * h₂ +
    ((r₁ + r₂) * (r₁ + r₃) * ((r₁ + r₂) * (r₂ + r₃))) * h₃

lemma full_eq (h₂ : r₂ ^ 2 = r₁ ^ 2 - n) (h₃ : r₃ ^ 2 = r₁ ^ 2 + n) :
    (r₁ * r₂ * r₃) ^ 2 = (r₁ ^ 2) ^ 3 + -(n : ℚ) ^ 2 * r₁ ^ 2 := by
  linear_combination (r₁ ^ 2 * r₃ ^ 2) * h₂ + (r₁ ^ 2 * (r₁ ^ 2 - n)) * h₃

/-- The point `(r₁², r₁r₂r₃)` of `E_n`, where `r₁², r₂² = r₁² - n` and `r₃² = r₁² + n` are the
three squares of a progression with common difference `n`. -/
def fullPt (hn : n ≠ 0) (h₂ : r₂ ^ 2 = r₁ ^ 2 - n) (h₃ : r₃ ^ 2 = r₁ ^ 2 + n) :
    (E n).toAffine.Point :=
  pt (neg_sq_ne_zero hn) (full_eq h₂ h₃)

/-- The point `((r₁+r₂)(r₁+r₃), (r₁+r₂)(r₁+r₃)(r₂+r₃))` of `E_n`, a half of `fullPt`. -/
def halfPt (hn : n ≠ 0) (h₂ : r₂ ^ 2 = r₁ ^ 2 - n) (h₃ : r₃ ^ 2 = r₁ ^ 2 + n) :
    (E n).toAffine.Point :=
  pt (neg_sq_ne_zero hn) (half_eq h₂ h₃)

/-- **Halving.** `2 · halfPt = fullPt`: the tangent at `halfPt` has slope `r₁ + r₂ + r₃`. -/
theorem two_nsmul_halfPt (hn : n ≠ 0) (h₂ : r₂ ^ 2 = r₁ ^ 2 - n) (h₃ : r₃ ^ 2 = r₁ ^ 2 + n) :
    2 • halfPt hn h₂ h₃ = fullPt hn h₂ h₃ := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  have h12 : r₁ + r₂ ≠ 0 := fun h => hn' (by linear_combination h₂ - (r₂ - r₁) * h)
  have h13 : r₁ + r₃ ≠ 0 := fun h => hn' (by linear_combination -h₃ + (r₃ - r₁) * h)
  have h23 : r₂ + r₃ ≠ 0 := fun h => hn' (by linear_combination (h₂ - h₃ + (r₃ - r₂) * h) / 2)
  have hy : (r₁ + r₂) * (r₁ + r₃) * (r₂ + r₃) ≠ 0 := mul_ne_zero (mul_ne_zero h12 h13) h23
  have hy' : (r₁ + r₂) * (r₁ + r₃) * (r₂ + r₃) ≠ (E n).toAffine.negY ((r₁ + r₂) * (r₁ + r₃))
      ((r₁ + r₂) * (r₁ + r₃) * (r₂ + r₃)) := by
    rw [negY_W]
    intro h
    exact hy (by linarith)
  have hden : (r₁ + r₂) * (r₁ + r₃) * (r₂ + r₃) - (E n).toAffine.negY ((r₁ + r₂) * (r₁ + r₃))
      ((r₁ + r₂) * (r₁ + r₃) * (r₂ + r₃)) ≠ 0 := sub_ne_zero.mpr hy'
  have hslope : (E n).toAffine.slope ((r₁ + r₂) * (r₁ + r₃)) ((r₁ + r₂) * (r₁ + r₃))
      ((r₁ + r₂) * (r₁ + r₃) * (r₂ + r₃)) ((r₁ + r₂) * (r₁ + r₃) * (r₂ + r₃)) = r₁ + r₂ + r₃ := by
    rw [slope_of_Y_ne rfl hy', div_eq_iff hden]
    simp only [negY, W]
    linear_combination (-2 * ((r₁ + r₂) * (r₁ + r₃)) - r₃ ^ 2 + r₁ ^ 2) * h₂ +
      (-2 * ((r₁ + r₂) * (r₁ + r₃)) + n) * h₃
  simp only [halfPt, fullPt, pt]
  rw [two_nsmul, Point.add_self_of_Y_ne hy', Point.some.injEq, hslope]
  simp only [addY, negAddY, addX, negY, W]
  constructor
  · linear_combination h₂ + h₃
  · linear_combination (-(r₁ + r₂ + r₃)) * h₂ + (-(r₁ + r₂ + r₃)) * h₃

/-- Example 1.3 of the note: the progression `1, 25, 49` has common difference `24 = 6 · 2²`.
Dividing by `2²` gives the point of `E_6` with `x = 25/4`, and its half has `x = 18`:
`(25/4, 35/8) = 2 · (18, 72)`. -/
example : xc (halfPt (n := 6) (r₁ := 5 / 2) (r₂ := 1 / 2) (r₃ := 7 / 2) (by norm_num) (by norm_num)
      (by norm_num)) = 18 ∧
    xc (fullPt (n := 6) (r₁ := 5 / 2) (r₂ := 1 / 2) (r₃ := 7 / 2) (by norm_num) (by norm_num)
      (by norm_num)) = 25 / 4 := by
  constructor <;> norm_num [halfPt, fullPt, xc_pt]

end Halving

/-! ### Three progressions of squares: Theorem 1.1 -/

/-- Three arithmetic progressions of integer squares `u i², v i², w i²` (`i = 0, 1, 2`), each with
common difference `n k²`, whose middle terms `c - s, c, c + s` are themselves in arithmetic
progression with nonzero step `s`. In a magic square of squares the three `b`-progressions have this
shape with `s = a`, and the three `a`-progressions have it with `s = b`. -/
structure ThreeProgressions (n : ℤ) where
  /-- `n k²` is the common difference of each progression -/
  k : ℤ
  /-- the middle term of the middle progression -/
  c : ℤ
  /-- the step between consecutive middle terms -/
  s : ℤ
  /-- square roots of the first terms -/
  u : Fin 3 → ℤ
  /-- square roots of the middle terms -/
  v : Fin 3 → ℤ
  /-- square roots of the last terms -/
  w : Fin 3 → ℤ
  hn : n ≠ 0
  hk : k ≠ 0
  hs : s ≠ 0
  hv₀ : v 0 ^ 2 = c - s
  hv₁ : v 1 ^ 2 = c
  hv₂ : v 2 ^ 2 = c + s
  hu : ∀ i, u i ^ 2 = v i ^ 2 - n * k ^ 2
  hw : ∀ i, w i ^ 2 = v i ^ 2 + n * k ^ 2

namespace ThreeProgressions

variable {n : ℤ} (T : ThreeProgressions n)

lemma h₂ (i : Fin 3) : ((T.u i : ℚ) / T.k) ^ 2 = ((T.v i : ℚ) / T.k) ^ 2 - n := by
  have hk : (T.k : ℚ) ≠ 0 := by exact_mod_cast T.hk
  have h : (T.u i : ℚ) ^ 2 = (T.v i : ℚ) ^ 2 - n * (T.k : ℚ) ^ 2 := by exact_mod_cast T.hu i
  field_simp
  linear_combination h

lemma h₃ (i : Fin 3) : ((T.w i : ℚ) / T.k) ^ 2 = ((T.v i : ℚ) / T.k) ^ 2 + n := by
  have hk : (T.k : ℚ) ≠ 0 := by exact_mod_cast T.hk
  have h : (T.w i : ℚ) ^ 2 = (T.v i : ℚ) ^ 2 + n * (T.k : ℚ) ^ 2 := by exact_mod_cast T.hw i
  field_simp
  linear_combination h

/-- Robertson's point `P_i = (v_i² / k², u_i v_i w_i / k³)` on `E_n`. -/
def P (i : Fin 3) : (E n).toAffine.Point :=
  fullPt T.hn (T.h₂ i) (T.h₃ i)

/-- A point `R_i` with `2 R_i = P_i`. -/
def R (i : Fin 3) : (E n).toAffine.Point :=
  halfPt T.hn (T.h₂ i) (T.h₃ i)

lemma two_nsmul_R (i : Fin 3) : 2 • T.R i = T.P i :=
  two_nsmul_halfPt _ _ _

lemma xc_P (i : Fin 3) : xc (T.P i) = ((T.v i : ℚ) / T.k) ^ 2 :=
  rfl

lemma P_ne_zero (i : Fin 3) : T.P i ≠ 0 :=
  pt_ne_zero (neg_sq_ne_zero T.hn) (full_eq (T.h₂ i) (T.h₃ i))

/-- Robertson's observation: `x(P_0) + x(P_2) = 2 x(P_1)`. -/
lemma xc_P_ap : xc (T.P 0) + xc (T.P 2) = 2 * xc (T.P 1) := by
  have h₀ : (T.v 0 : ℚ) ^ 2 = T.c - T.s := by exact_mod_cast T.hv₀
  have h₁ : (T.v 1 : ℚ) ^ 2 = T.c := by exact_mod_cast T.hv₁
  have h₂ : (T.v 2 : ℚ) ^ 2 = T.c + T.s := by exact_mod_cast T.hv₂
  rw [xc_P, xc_P, xc_P, div_pow, div_pow, div_pow, h₀, h₁, h₂, ← add_div, mul_div_assoc']
  congr 1
  ring

lemma v_sq_eq_of_xc_eq {i j : Fin 3} (h : xc (T.P i) = xc (T.P j)) : T.v i ^ 2 = T.v j ^ 2 := by
  have hk : (T.k : ℚ) ≠ 0 := by exact_mod_cast T.hk
  rw [xc_P, xc_P, div_pow, div_pow, div_left_inj' (pow_ne_zero 2 hk)] at h
  exact_mod_cast h

lemma xc_P_ne_01 : xc (T.P 0) ≠ xc (T.P 1) := fun h => by
  have := T.v_sq_eq_of_xc_eq h
  rw [T.hv₀, T.hv₁] at this
  exact T.hs (by linarith)

lemma xc_P_ne_02 : xc (T.P 0) ≠ xc (T.P 2) := fun h => by
  have := T.v_sq_eq_of_xc_eq h
  rw [T.hv₀, T.hv₂] at this
  exact T.hs (by linarith)

lemma xc_P_ne_12 : xc (T.P 1) ≠ xc (T.P 2) := fun h => by
  have := T.v_sq_eq_of_xc_eq h
  rw [T.hv₁, T.hv₂] at this
  exact T.hs (by linarith)

/-- The subgroup `Γ = ⟨P_0, P_1, P_2⟩` of `E_n(ℚ)`. -/
def Γ : AddSubgroup (E n).toAffine.Point :=
  AddSubgroup.closure (Set.range T.P)

lemma P_mem (i : Fin 3) : T.P i ∈ T.Γ :=
  AddSubgroup.subset_closure ⟨i, rfl⟩

/-- `Γ ⊆ 2 E_n(ℚ)`. -/
lemma exists_two_nsmul {G : (E n).toAffine.Point} (hG : G ∈ T.Γ) : ∃ R, G = 2 • R := by
  induction hG using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨T.R i, (T.two_nsmul_R i).symm⟩
  | zero => exact ⟨0, (smul_zero 2).symm⟩
  | add x y _ _ hx hy =>
    obtain ⟨R, rfl⟩ := hx
    obtain ⟨R', rfl⟩ := hy
    exact ⟨R + R', (smul_add 2 R R').symm⟩
  | neg x _ hx =>
    obtain ⟨R, rfl⟩ := hx
    exact ⟨-R, (smul_neg 2 R).symm⟩

/-- `Γ` is torsion-free, because `2 E_n(ℚ)` is (Lemma 2.1(c)). -/
lemma eq_zero_of_isOfFinAddOrder (htors : TorsionTheorem n) {G : (E n).toAffine.Point}
    (hG : G ∈ T.Γ) (hfin : IsOfFinAddOrder G) : G = 0 := by
  obtain ⟨R, rfl⟩ := T.exists_two_nsmul hG
  exact htors R (hfin.of_nsmul two_ne_zero)

/-- The heart of Theorem 1.1: `P_0, P_1, P_2` are not all multiples of one point of `Γ`. -/
theorem not_forall_zsmul (hPD : PrimitiveDivisorTheorem n) (htors : TorsionTheorem n) :
    ¬ ∃ G ∈ T.Γ, ∀ i, ∃ m : ℤ, T.P i = m • G := by
  rintro ⟨G, hG, hm⟩
  choose m hm using hm
  -- `G ∈ Γ ⊆ 2 E_n(ℚ)`, so `x(G)` is a square.
  obtain ⟨R, rfl⟩ := T.exists_two_nsmul hG
  -- `G` has infinite order, since `P_1 = m_1 G` does.
  have hord : addOrderOf (2 • R) = 0 := by
    rw [addOrderOf_eq_zero_iff]
    intro hfin
    exact T.P_ne_zero 1 (T.eq_zero_of_isOfFinAddOrder htors (T.P_mem 1) (by rw [hm 1]; exact hfin.zsmul))
  have hQ := hPD _ hord (isSquare_xc_two_nsmul R)
  have hm0 (i : Fin 3) : m i ≠ 0 := fun h => T.P_ne_zero i (by rw [hm i, h, zero_zsmul])
  have habs {i j : Fin 3} (hne : xc (T.P i) ≠ xc (T.P j)) : (m i).natAbs ≠ (m j).natAbs :=
    fun h => hne (by rw [hm i, hm j, xc_zsmul, xc_zsmul (m j), h])
  apply xc_add_ne_two_mul (hasIntCoeffs_E n) hQ (hm0 0) (hm0 1) (hm0 2)
    (habs T.xc_P_ne_01) (habs T.xc_P_ne_02) (habs T.xc_P_ne_12)
  rw [← hm 0, ← hm 1, ← hm 2]
  exact T.xc_P_ap

lemma isAddTorsionFree (htors : TorsionTheorem n) : IsAddTorsionFree T.Γ := by
  refine ⟨fun k hk a b hab => Subtype.ext ?_⟩
  have h : k • ((a : (E n).toAffine.Point) - b) = 0 := by
    have hab' : k • (a : (E n).toAffine.Point) = k • (b : (E n).toAffine.Point) := by
      exact_mod_cast congrArg Subtype.val hab
    rw [nsmul_sub, hab', sub_self]
  have hfin : IsOfFinAddOrder ((a : (E n).toAffine.Point) - b) :=
    isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨k, Nat.pos_of_ne_zero hk, h⟩
  exact sub_eq_zero.mp (T.eq_zero_of_isOfFinAddOrder htors (T.Γ.sub_mem a.2 b.2) hfin)

lemma finite : Module.Finite ℤ T.Γ := by
  rw [Module.Finite.iff_addGroup_fg, AddGroup.fg_iff_addSubgroup_fg]
  exact ⟨Finset.univ.image T.P, by rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]; rfl⟩

/-- `Γ` is free of rank at least two. -/
theorem exists_basis (hPD : PrimitiveDivisorTheorem n) (htors : TorsionTheorem n) :
    ∃ d : ℕ, 2 ≤ d ∧ Nonempty (Module.Basis (Fin d) ℤ T.Γ) := by
  have := T.isAddTorsionFree htors
  have := T.finite
  obtain ⟨d, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := T.Γ)
  refine ⟨d, ?_, ⟨b⟩⟩
  obtain rfl | rfl | hd : d = 0 ∨ d = 1 ∨ 2 ≤ d := by omega
  · -- Rank zero: `Γ = 0`, but `P_1 ≠ 0`.
    exfalso
    have h := b.sum_repr ⟨T.P 1, T.P_mem 1⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at h
    exact T.P_ne_zero 1 (congrArg Subtype.val h.symm)
  · -- Rank one: `Γ` is generated by `b 0`.
    exfalso
    refine T.not_forall_zsmul hPD htors ⟨b 0, (b 0).2, fun i => ⟨b.repr ⟨T.P i, T.P_mem i⟩ 0, ?_⟩⟩
    have h := b.sum_repr ⟨T.P i, T.P_mem i⟩
    rw [Fin.sum_univ_one] at h
    have h' := congrArg Subtype.val h
    push_cast at h'
    exact h'.symm
  · exact hd

/-- **Theorem 1.1.** The points `P_0, P_1, P_2` generate a subgroup of `E_n(ℚ)` of rank at least
two. -/
theorem two_le_finrank (hPD : PrimitiveDivisorTheorem n) (htors : TorsionTheorem n) :
    2 ≤ Module.finrank ℤ T.Γ := by
  obtain ⟨d, hd, ⟨b⟩⟩ := T.exists_basis hPD htors
  rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  exact hd

include T in
/-- `E_n(ℚ)` contains two `ℤ`-linearly independent points, so `rank E_n(ℚ) ≥ 2`. -/
theorem exists_linearIndependent (hPD : PrimitiveDivisorTheorem n) (htors : TorsionTheorem n) :
    ∃ P Q : (E n).toAffine.Point, LinearIndependent ℤ ![P, Q] := by
  obtain ⟨d, hd, ⟨b⟩⟩ := T.exists_basis hPD htors
  have hij : (⟨0, by omega⟩ : Fin d) ≠ ⟨1, by omega⟩ := by simp
  refine ⟨b ⟨0, by omega⟩, b ⟨1, by omega⟩, LinearIndependent.pair_iff.mpr fun s t hst => ?_⟩
  have h : s • b ⟨0, by omega⟩ + t • b ⟨1, by omega⟩ = 0 := Subtype.ext (by push_cast; exact hst)
  have h₀ := congrArg (fun x => b.repr x ⟨0, by omega⟩) h
  have h₁ := congrArg (fun x => b.repr x ⟨1, by omega⟩) h
  simp [hij, hij.symm] at h₀ h₁
  exact ⟨h₀, h₁⟩

end ThreeProgressions

end MagicSquares.RankOne

/-! ### Magic squares of squares: Corollary 1.2 -/

namespace MagicSquares.MagicSquareOfSquares

open RankOne

variable (M : MagicSquareOfSquares)

lemma a_ne_zero : M.a ≠ 0 := fun h =>
  M.sq_ne (by decide : ((0 : Fin 3), (0 : Fin 3)) ≠ (1, 1)) (by simp only [a, e] at h; linarith)

lemma b_ne_zero : M.b ≠ 0 := fun h =>
  M.sq_ne (by decide : ((0 : Fin 3), (2 : Fin 3)) ≠ (1, 1)) (by simp only [b, e] at h; linarith)

/-- The three `b`-progressions of `M`: the anti-diagonal `(E-b, E, E+b)` and its two broken
parallels, where `b = n k²`. -/
def bProgressions {n k : ℤ} (hk : k ≠ 0) (hb : M.b = n * k ^ 2) : ThreeProgressions n where
  k := k
  c := M.e ^ 2
  s := M.a
  u := ![M.r 0 1, M.r 2 0, M.r 1 2]
  v := ![M.r 2 2, M.r 1 1, M.r 0 0]
  w := ![M.r 1 0, M.r 0 2, M.r 2 1]
  hn := by rintro rfl; exact M.b_ne_zero (by simpa using hb)
  hk := hk
  hs := M.a_ne_zero
  hv₀ := by simpa using M.lucas.2.2.2.2.2
  hv₁ := by simp [e]
  hv₂ := by simp [a]
  hu := by
    obtain ⟨h01, -, h12, h20, -, h22⟩ := M.lucas
    have ha' : M.a = M.r 0 0 ^ 2 - M.e ^ 2 := rfl
    have he : M.e ^ 2 = M.r 1 1 ^ 2 := rfl
    intro i
    rw [← hb]
    fin_cases i <;> simp <;> linarith
  hw := by
    obtain ⟨-, h10, -, -, h21, h22⟩ := M.lucas
    have ha' : M.a = M.r 0 0 ^ 2 - M.e ^ 2 := rfl
    have hb' : M.b = M.r 0 2 ^ 2 - M.e ^ 2 := rfl
    have he : M.e ^ 2 = M.r 1 1 ^ 2 := rfl
    intro i
    rw [← hb]
    fin_cases i <;> simp <;> linarith

/-- The three `a`-progressions of `M`: the main diagonal `(E-a, E, E+a)` and its two broken
parallels, where `a = n k²`. -/
def aProgressions {n k : ℤ} (hk : k ≠ 0) (ha : M.a = n * k ^ 2) : ThreeProgressions n where
  k := k
  c := M.e ^ 2
  s := M.b
  u := ![M.r 0 1, M.r 2 2, M.r 1 0]
  v := ![M.r 2 0, M.r 1 1, M.r 0 2]
  w := ![M.r 1 2, M.r 0 0, M.r 2 1]
  hn := by rintro rfl; exact M.a_ne_zero (by simpa using ha)
  hk := hk
  hs := M.b_ne_zero
  hv₀ := by simpa using M.lucas.2.2.2.1
  hv₁ := by simp [e]
  hv₂ := by simp [b]
  hu := by
    obtain ⟨h01, h10, -, h20, -, h22⟩ := M.lucas
    have hb' : M.b = M.r 0 2 ^ 2 - M.e ^ 2 := rfl
    have he : M.e ^ 2 = M.r 1 1 ^ 2 := rfl
    intro i
    rw [← ha]
    fin_cases i <;> simp <;> linarith
  hw := by
    obtain ⟨-, -, h12, h20, h21, -⟩ := M.lucas
    have ha' : M.a = M.r 0 0 ^ 2 - M.e ^ 2 := rfl
    have hb' : M.b = M.r 0 2 ^ 2 - M.e ^ 2 := rfl
    have he : M.e ^ 2 = M.r 1 1 ^ 2 := rfl
    intro i
    rw [← ha]
    fin_cases i <;> simp <;> linarith

/-- **Theorem 1.1** for a magic square of squares: if `b = n k²`, the three points that the
`b`-progressions give on `E_n` generate a subgroup of rank at least two. -/
theorem two_le_finrank_b {n k : ℤ} (hk : k ≠ 0) (hb : M.b = n * k ^ 2)
    (hPD : PrimitiveDivisorTheorem n) (htors : TorsionTheorem n) :
    2 ≤ Module.finrank ℤ (M.bProgressions hk hb).Γ :=
  (M.bProgressions hk hb).two_le_finrank hPD htors

/-- **Theorem 1.1** for the `a`-progressions. -/
theorem two_le_finrank_a {n k : ℤ} (hk : k ≠ 0) (ha : M.a = n * k ^ 2)
    (hPD : PrimitiveDivisorTheorem n) (htors : TorsionTheorem n) :
    2 ≤ Module.finrank ℤ (M.aProgressions hk ha).Γ :=
  (M.aProgressions hk ha).two_le_finrank hPD htors

/-- **Corollary 1.2**, anti-diagonal. If the anti-diagonal `(E+b, E, E-b)` of a magic square of
squares has common difference `b = n k²`, then `E_n(ℚ)` has rank at least two. -/
theorem rank_two_of_antidiagonal {n k : ℤ} (hk : k ≠ 0) (hb : M.b = n * k ^ 2)
    (hPD : PrimitiveDivisorTheorem n) (htors : TorsionTheorem n) :
    ∃ P Q : (E n).toAffine.Point, LinearIndependent ℤ ![P, Q] :=
  (M.bProgressions hk hb).exists_linearIndependent hPD htors

/-- **Corollary 1.2**, main diagonal. If the main diagonal `(E+a, E, E-a)` has common difference
`a = n k²`, then `E_n(ℚ)` has rank at least two. -/
theorem rank_two_of_diagonal {n k : ℤ} (hk : k ≠ 0) (ha : M.a = n * k ^ 2)
    (hPD : PrimitiveDivisorTheorem n) (htors : TorsionTheorem n) :
    ∃ P Q : (E n).toAffine.Point, LinearIndependent ℤ ![P, Q] :=
  (M.aProgressions hk ha).exists_linearIndependent hPD htors

end MagicSquares.MagicSquareOfSquares
