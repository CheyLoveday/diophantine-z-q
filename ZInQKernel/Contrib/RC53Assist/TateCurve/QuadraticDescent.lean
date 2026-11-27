import ZInQKernel.Contrib.RC53Assist.GlobalTrace.CoinvariantReadings

/-!
# Quadratic signs between Weierstrass isomorphisms

For a curve with nonzero `c₄` and `c₆` in characteristic zero, any two
Weierstrass isomorphisms to the same curve differ by identity or inversion.
The proof compares the fourth and sixth powers of their scaling coefficients,
then the `b₂`, `a₁`, and `a₃` transformation formulas.

Reference: Silverman, *The Arithmetic of Elliptic Curves*, III.1 and III.10.
The algebraic argument below is proved and consumes no automorphism print.
-/

noncomputable section

set_option maxHeartbeats 800000

namespace ZInQ.Contrib.RC53Assist.TateCurve

open WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical

section Isomorphisms

variable {F : Type*} [Field F] [CharZero F]
variable (E E' : WeierstrassCurve F)
variable (C D : VariableChange F) (hC : C • E = E') (hD : D • E = E')

include hC hD in
/-- **PROVED**: two isomorphisms of a curve with `c₄c₆ ≠ 0` have the
same squared scaling coefficient. Locator: the transformation laws for
`c₄` and `c₆`. -/
theorem isomorphism_scaling_square (h4 : E.c₄ ≠ 0) (h6 : E.c₆ ≠ 0) :
    (C.u : F) ^ 2 = (D.u : F) ^ 2 := by
  have hc4 : (C.u : F) ^ 4 * E'.c₄ = E.c₄ := by
    rw [← hC, variableChange_c₄, ← mul_assoc, ← mul_pow,
      Units.mul_inv, one_pow, one_mul]
  have hd4 : (D.u : F) ^ 4 * E'.c₄ = E.c₄ := by
    rw [← hD, variableChange_c₄, ← mul_assoc, ← mul_pow,
      Units.mul_inv, one_pow, one_mul]
  have hc6 : (C.u : F) ^ 6 * E'.c₆ = E.c₆ := by
    rw [← hC, variableChange_c₆, ← mul_assoc, ← mul_pow,
      Units.mul_inv, one_pow, one_mul]
  have hd6 : (D.u : F) ^ 6 * E'.c₆ = E.c₆ := by
    rw [← hD, variableChange_c₆, ← mul_assoc, ← mul_pow,
      Units.mul_inv, one_pow, one_mul]
  have h4' : E'.c₄ ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hc4
    exact h4 hc4.symm
  have h6' : E'.c₆ ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hc6
    exact h6 hc6.symm
  have hu4 := mul_right_cancel₀ h4' (hc4.trans hd4.symm)
  have hu6 := mul_right_cancel₀ h6' (hc6.trans hd6.symm)
  apply mul_right_cancel₀ (pow_ne_zero 4 C.u.ne_zero)
  calc
    (C.u : F) ^ 2 * (C.u : F) ^ 4 = (C.u : F) ^ 6 := by ring
    _ = (D.u : F) ^ 6 := hu6
    _ = (D.u : F) ^ 2 * (C.u : F) ^ 4 := by rw [hu4]; ring

include hC hD in
/-- **PROVED**: the complete coefficient alternatives for two isomorphisms
of a curve with `c₄c₆ ≠ 0`. The second alternative is exactly inversion on
the point group, expressed in Weierstrass coordinates.
Locator: the `b₂`, `a₁`, and `a₃` transformation formulas. -/
theorem isomorphism_coefficient_alternatives (h4 : E.c₄ ≠ 0) (h6 : E.c₆ ≠ 0) :
    (D.u = C.u ∧ D.r = C.r ∧ D.s = C.s ∧ D.t = C.t) ∨
    ((D.u : F) = -(C.u : F) ∧ D.r = C.r ∧
      D.s = -C.s - E.a₁ ∧ D.t = -C.t - C.r * E.a₁ - E.a₃) := by
  have hu2 := isomorphism_scaling_square E E' C D hC hD h4 h6
  have hc2 : (C.u : F) ^ 2 * E'.b₂ = E.b₂ + 12 * C.r := by
    rw [← hC, variableChange_b₂, ← mul_assoc, ← mul_pow,
      Units.mul_inv, one_pow, one_mul]
  have hd2 : (D.u : F) ^ 2 * E'.b₂ = E.b₂ + 12 * D.r := by
    rw [← hD, variableChange_b₂, ← mul_assoc, ← mul_pow,
      Units.mul_inv, one_pow, one_mul]
  have hr : D.r = C.r := by
    rw [hu2] at hc2
    linear_combination (hc2 - hd2) / 12
  have hc1 : (C.u : F) * E'.a₁ = E.a₁ + 2 * C.s := by
    rw [← hC, variableChange_a₁, ← mul_assoc, Units.mul_inv, one_mul]
  have hd1 : (D.u : F) * E'.a₁ = E.a₁ + 2 * D.s := by
    rw [← hD, variableChange_a₁, ← mul_assoc, Units.mul_inv, one_mul]
  have hc3 : (C.u : F) ^ 3 * E'.a₃ = E.a₃ + C.r * E.a₁ + 2 * C.t := by
    rw [← hC, variableChange_a₃, ← mul_assoc, ← mul_pow,
      Units.mul_inv, one_pow, one_mul]
  have hd3 : (D.u : F) ^ 3 * E'.a₃ = E.a₃ + D.r * E.a₁ + 2 * D.t := by
    rw [← hD, variableChange_a₃, ← mul_assoc, ← mul_pow,
      Units.mul_inv, one_pow, one_mul]
  have hprod : ((D.u : F) - C.u) * ((D.u : F) + C.u) = 0 := by
    linear_combination -hu2
  rcases mul_eq_zero.mp hprod with hpos | hneg
  · have hu : (D.u : F) = C.u := sub_eq_zero.mp hpos
    have hs : D.s = C.s := by rw [hu] at hd1; linear_combination (hc1 - hd1) / 2
    have ht : D.t = C.t := by rw [hu, hr] at hd3; linear_combination (hc3 - hd3) / 2
    exact Or.inl ⟨Units.ext hu, hr, hs, ht⟩
  · have hu : (D.u : F) = -(C.u : F) := add_eq_zero_iff_eq_neg.mp hneg
    have hs : D.s = -C.s - E.a₁ := by
      rw [hu, neg_mul] at hd1
      linear_combination -(hc1 + hd1) / 2
    have ht : D.t = -C.t - C.r * E.a₁ - E.a₃ := by
      rw [hu, hr] at hd3
      have hneg3 : (-(C.u : F)) ^ 3 = -(C.u : F) ^ 3 := by ring
      rw [hneg3, neg_mul] at hd3
      linear_combination -(hc3 + hd3) / 2
    exact Or.inr ⟨hu, hr, hs, ht⟩

/-- **PROVED DEFINITION**: the actual group isomorphism on points from a
Weierstrass change of variables. Locator: the coordinate-change point map. -/
def pointsOfVariableChange (E E' : WeierstrassCurve F) (C : VariableChange F)
    (hC : C • E = E') : E'.toAffine.Point ≃+ E.toAffine.Point :=
  (AddEquiv.cast (M := fun W : WeierstrassCurve F => W.toAffine.Point) hC.symm).trans
    (Point.addEquivVariableChange E C)

/-- **PROVED**: equal variable changes give equal point isomorphisms,
including the proof-dependent casts. Locator: proof irrelevance. -/
theorem pointsOfVariableChange_congr (A B : VariableChange F)
    (hA : A • E = E') (hB : B • E = E') (hAB : A = B) (P : E'.toAffine.Point) :
    pointsOfVariableChange E E' A hA P = pointsOfVariableChange E E' B hB P := by
  subst B
  rfl

/-- **PROVED**: the coefficients of inversion act as inversion on every
point. Locator: the Weierstrass point coordinate formulas. -/
theorem pointsOfVariableChange_negative
    (hu : (D.u : F) = -(C.u : F)) (hr : D.r = C.r)
    (hs : D.s = -C.s - E.a₁) (ht : D.t = -C.t - C.r * E.a₁ - E.a₃)
    (P : E'.toAffine.Point) :
    pointsOfVariableChange E E' D hD P = -pointsOfVariableChange E E' C hC P := by
  rcases P with _ | ⟨x, y, h⟩
  · simp only [← Point.zero_def, map_zero, neg_zero]
  · simp only [pointsOfVariableChange, AddEquiv.trans_apply]
    rw [AddEquiv.cast_apply hD.symm, Point.cast_some hD.symm,
      AddEquiv.cast_apply hC.symm, Point.cast_some hC.symm]
    simp only [Point.coe_addEquivVariableChange, Point.equivVariableChange_some,
      Point.neg_some, Point.some.injEq]
    constructor
    · simp only [hu, hr]; ring
    · simp only [hu, hs, ht, negY]; ring

/-- **PROVED**: the coefficient alternatives give identity or inversion
on every point, not merely on an unrelated abstract vector space.
Locator: `isomorphism_coefficient_alternatives` and the point coordinates. -/
theorem isomorphism_point_sign (h4 : E.c₄ ≠ 0) (h6 : E.c₆ ≠ 0) :
    (∀ P, pointsOfVariableChange E E' D hD P =
      pointsOfVariableChange E E' C hC P) ∨
    (∀ P, pointsOfVariableChange E E' D hD P =
      -pointsOfVariableChange E E' C hC P) := by
  rcases isomorphism_coefficient_alternatives E E' C D hC hD h4 h6 with
    ⟨hu, hr, hs, ht⟩ | ⟨hu, hr, hs, ht⟩
  · have hDC : D = C := by ext <;> simp only [hu, hr, hs, ht]
    subst D
    exact Or.inl fun _ => rfl
  · right
    intro P
    rcases P with _ | ⟨x, y, h⟩
    · simp only [← Point.zero_def, map_zero, neg_zero]
    · simp only [pointsOfVariableChange, AddEquiv.trans_apply]
      rw [AddEquiv.cast_apply hD.symm, Point.cast_some hD.symm,
        AddEquiv.cast_apply hC.symm, Point.cast_some hC.symm]
      simp only [Point.coe_addEquivVariableChange, Point.equivVariableChange_some,
        Point.neg_some, Point.some.injEq]
      constructor
      · simp only [hu, hr]; ring
      · simp only [hu, hr, hs, ht, negY]; ring

end Isomorphisms

end ZInQ.Contrib.RC53Assist.TateCurve
