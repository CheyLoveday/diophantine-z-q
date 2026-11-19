/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import ZInQKernel.Contrib.TauCeti.FieldTheory.FunctionField.Elliptic.Basic
import ZInQKernel.Contrib.TauCeti.FieldTheory.FunctionField.Place.Map
import ZInQKernel.Contrib.TauCeti.FieldTheory.FunctionField.RiemannRoch.RatFunc
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Singular
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Eval
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.GeneratedByY
import Mathlib.Tactic.LinearCombination

/-!
# A Weierstrass model from Riemann–Roch

A genus-one function field with exact constants and a rational place has coordinate functions
with sole poles of orders two and three, satisfying a Weierstrass equation and generating the
field. Over a perfect constant field the equation has nonzero discriminant. Evaluation then
identifies the given field with the function field of the Weierstrass curve.

Thus the function-field form of S2b is proved over `ℚ`. Perfectness is essential for the
nonsingularity step as stated: a regular genus-one curve over an imperfect field need not be
geometrically smooth. The coordinate equation and function-field isomorphism do not require
perfectness.

Mathematical locator: Silverman, *The Arithmetic of Elliptic Curves*, second edition,
Proposition III.3.1, using Riemann–Roch in Chapter II, Section 5. No printed theorem is assumed.

The proofs are adapted from the public Tau Ceti repository, revision `5a01f5fe3621`,
Apache-2.0, with declaration names confined to this contribution:
* `FieldTheory/FunctionField/Elliptic/Weierstrass/Equation.lean`;
* `FieldTheory/FunctionField/Elliptic/Nonsingular.lean`;
* `FieldTheory/FunctionField/Consequences/GenusZero.lean`,
  `genus_eq_zero_of_adjoin_eq_top`;
* `AlgebraicGeometry/EllipticCurve/Affine/FunctionField/Lift.lean`.
Only the parts needed for the existence theorem are included.
-/

set_option maxHeartbeats 800000

noncomputable section

namespace ZInQ.Contrib.RC53Assist.InvariantDifferential

open TauCeti AlgebraicGeometry WeierstrassCurve Polynomial
open scoped IntermediateField

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- STRUCTURE. Weierstrass coordinates at a place have sole poles of orders two and three
and satisfy a Weierstrass equation. Locator: Silverman, Proposition III.3.1;
Tau Ceti, `Elliptic/Weierstrass/Equation.lean`, `Place.IsWeierstrassCoordinates`. -/
structure WeierstrassCoordinates (P : Place k F) (W : WeierstrassCurve k) (x y : F) : Prop where
  /-- FIELD. The first coordinate has order `-2` at the base place.
  Locator: Silverman, Proposition III.3.1, the choice from `L(2O)`. -/
  ord_x : P.ord x = -2
  /-- FIELD. The first coordinate is regular away from the base place.
  Locator: Silverman, Proposition III.3.1, membership in `L(2O)`. -/
  ord_x_nonneg : ∀ Q : Place k F, Q ≠ P → 0 ≤ Q.ord x
  /-- FIELD. The second coordinate has order `-3` at the base place.
  Locator: Silverman, Proposition III.3.1, the choice from `L(3O)`. -/
  ord_y : P.ord y = -3
  /-- FIELD. The second coordinate is regular away from the base place.
  Locator: Silverman, Proposition III.3.1, membership in `L(3O)`. -/
  ord_y_nonneg : ∀ Q : Place k F, Q ≠ P → 0 ≤ Q.ord y
  /-- FIELD. The two coordinates satisfy the equation of the curve over the function field.
  Locator: Silverman, Proposition III.3.1, the relation in `L(6O)`. -/
  equation : (W.baseChange F).toAffine.Equation x y

namespace WeierstrassCoordinates

variable {P : Place k F} {W : WeierstrassCurve k} {x y : F}
  (h : WeierstrassCoordinates P W x y)
include h

/-- THEOREM (proved). The first coordinate is nonzero because it has a pole.
Locator: Tau Ceti, `Elliptic/Weierstrass/Equation.lean`, `IsWeierstrassCoordinates.x_ne_zero`. -/
theorem x_ne_zero : x ≠ 0 := fun hx ↦ by simpa [hx] using h.ord_x

/-- THEOREM (proved). The second coordinate is nonzero because it has a pole.
Locator: Tau Ceti, `Elliptic/Weierstrass/Equation.lean`, `IsWeierstrassCoordinates.y_ne_zero`. -/
theorem y_ne_zero : y ≠ 0 := fun hy ↦ by simpa [hy] using h.ord_y

/-- THEOREM (proved). The first coordinate is transcendental over the constants.
Locator: Tau Ceti, `Elliptic/Weierstrass/Equation.lean`, `IsWeierstrassCoordinates.transcendental_x`. -/
theorem transcendental_x : Transcendental k x :=
  P.transcendental_of_ord_ne_zero (by rw [h.ord_x]; decide)

/-- THEOREM (proved). The second coordinate is transcendental over the constants.
Locator: Tau Ceti, `Elliptic/Weierstrass/Equation.lean`, `IsWeierstrassCoordinates.transcendental_y`. -/
theorem transcendental_y : Transcendental k y :=
  P.transcendental_of_ord_ne_zero (by rw [h.ord_y]; decide)

/-- THEOREM (proved). The first coordinate has pole divisor `2P`.
Locator: Tau Ceti, `Elliptic/Weierstrass/Equation.lean`, `IsWeierstrassCoordinates.poles_x`. -/
theorem poles_x (hF : IsFunctionField k F) :
    Divisor.poles hF (Units.mk0 x h.x_ne_zero) = (2 : ℤ) • WeilDivisor.ofPoint P :=
  Divisor.poles_eq_natCast_zsmul_ofPoint_of_ord_eq_neg hF (n := 2) h.ord_x h.ord_x_nonneg

/-- THEOREM (proved). The second coordinate has pole divisor `3P`.
Locator: Tau Ceti, `Elliptic/Weierstrass/Equation.lean`, `IsWeierstrassCoordinates.poles_y`. -/
theorem poles_y (hF : IsFunctionField k F) :
    Divisor.poles hF (Units.mk0 y h.y_ne_zero) = (3 : ℤ) • WeilDivisor.ofPoint P :=
  Divisor.poles_eq_natCast_zsmul_ofPoint_of_ord_eq_neg hF (n := 3) h.ord_y h.ord_y_nonneg

/-- THEOREM (proved). The first coordinate generates a rational subfield of index two.
Locator: Tau Ceti, `Elliptic/Weierstrass/Equation.lean`,
`IsWeierstrassCoordinates.finrank_adjoin_x_eq_two`. -/
theorem finrank_adjoin_x_eq_two (hF : IsFunctionField k F) (hP : P.degree = 1) :
    Module.finrank k⟮x⟯ F = 2 := by
  rw [Place.finrank_adjoin_eq_mul_degree_of_ord_eq_neg hF (n := 2) two_ne_zero h.ord_x
    h.ord_x_nonneg, hP, mul_one]

/-- THEOREM (proved). The second coordinate generates a rational subfield of index three.
Locator: Tau Ceti, `Elliptic/Weierstrass/Equation.lean`,
`IsWeierstrassCoordinates.finrank_adjoin_y_eq_three`. -/
theorem finrank_adjoin_y_eq_three (hF : IsFunctionField k F) (hP : P.degree = 1) :
    Module.finrank k⟮y⟯ F = 3 := by
  rw [Place.finrank_adjoin_eq_mul_degree_of_ord_eq_neg hF (n := 3) three_ne_zero h.ord_y
    h.ord_y_nonneg, hP, mul_one]

/-- THEOREM (proved). The coordinate functions generate the full field: the remaining index
divides both two and three. Locator: Tau Ceti, `Elliptic/Weierstrass/Equation.lean`,
`IsWeierstrassCoordinates.adjoin_eq_top`; Silverman, Proposition III.3.1. -/
theorem adjoin_eq_top (hF : IsFunctionField k F) (hP : P.degree = 1) : k⟮x, y⟯ = ⊤ := by
  have _ : FiniteDimensional k⟮x⟯ F := hF.finiteDimensional_adjoin h.transcendental_x
  have _ : FiniteDimensional k⟮y⟯ F := hF.finiteDimensional_adjoin h.transcendental_y
  have hx : k⟮x⟯ ≤ k⟮x, y⟯ :=
    IntermediateField.adjoin.mono _ _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
  have hy : k⟮y⟯ ≤ k⟮x, y⟯ :=
    IntermediateField.adjoin.mono _ _ _
      (Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem _ rfl))
  have h2 := IntermediateField.finrank_dvd_of_le_left hx
  have h3 := IntermediateField.finrank_dvd_of_le_left hy
  rw [h.finrank_adjoin_x_eq_two hF hP] at h2
  rw [h.finrank_adjoin_y_eq_three hF hP] at h3
  exact IntermediateField.finrank_eq_one_iff_eq_top.mp
    (Nat.eq_one_of_dvd_coprimes (by decide) h2 h3)

end WeierstrassCoordinates

/-- THEOREM (proved). The six monomials form a basis of `L(6P)`; the expansion of `y²` has
nonzero `x³` coefficient. Locator: Silverman, Proposition III.3.1;
Tau Ceti, `Elliptic/Weierstrass/Equation.lean`, `exists_sq_eq_sum_smul_of_genus_eq_one`. -/
private theorem exists_cubic_relation (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hg : genus k F = 1) {P : Place k F} (hP : P.degree = 1)
    {x y : F} (hx0 : x ≠ 0) (hxP : P.ord x = -2) (hxQ : ∀ Q : Place k F, Q ≠ P → 0 ≤ Q.ord x)
    (hy0 : y ≠ 0) (hyP : P.ord y = -3) (hyQ : ∀ Q : Place k F, Q ≠ P → 0 ≤ Q.ord y) :
    ∃ c : Fin 6 → k, c 5 ≠ 0 ∧ ∑ i, c i • ![1, x, y, x ^ 2, x * y, x ^ 3] i = y ^ 2 := by
  classical
  set v : Fin 6 → F := ![1, x, y, x ^ 2, x * y, x ^ 3] with hv
  have hv0 : ∀ i, v i ≠ 0 := by
    intro i
    fin_cases i <;> simp [hv, hx0, hy0]
  have hvP : ∀ i, P.ord (v i) = ![0, -2, -3, -4, -5, -6] i := by
    intro i
    fin_cases i <;> simp [hv, P.ord_mul hx0 hy0, P.ord_pow, hxP, hyP]
  have hvQ : ∀ Q : Place k F, Q ≠ P → ∀ i, 0 ≤ Q.ord (v i) := by
    intro Q hQ i
    have hx := hxQ Q hQ
    have hy := hyQ Q hQ
    fin_cases i <;> simp [hv, Q.ord_mul hx0 hy0, Q.ord_pow] <;> omega
  have hmem : ∀ i, v i ∈ riemannRochSpace ((6 : ℤ) • WeilDivisor.ofPoint P) := fun i ↦
    (mem_riemannRochSpace_zsmul_ofPoint_iff (hv0 i)).mpr
      ⟨by rw [hvP i]; fin_cases i <;> simp, fun Q hQ ↦ hvQ Q hQ i⟩
  have hmem5 : ∀ i, i ≠ 5 → v i ∈ riemannRochSpace ((5 : ℤ) • WeilDivisor.ofPoint P) :=
    fun i hi ↦ (mem_riemannRochSpace_zsmul_ofPoint_iff (hv0 i)).mpr
      ⟨by rw [hvP i]; fin_cases i <;> simp_all, fun Q hQ ↦ hvQ Q hQ i⟩
  have hdim : Module.finrank k (riemannRochSpace ((6 : ℤ) • WeilDivisor.ofPoint P)) = 6 := by
    have := Divisor.dim_natCast_zsmul_ofPoint_of_genus_eq_one hF hex hg (P := P) (n := 6)
      (by norm_num)
    rw [hP, mul_one] at this
    simpa [Divisor.dim_def] using this
  have hli : LinearIndependent k v :=
    P.linearIndependent_of_injective_ord hv0 (by rw [funext hvP]; decide)
  set v' : Fin 6 → riemannRochSpace ((6 : ℤ) • WeilDivisor.ofPoint P) := fun i ↦ ⟨v i, hmem i⟩
    with hv'
  have hli' : LinearIndependent k v' :=
    LinearIndependent.of_comp (riemannRochSpace ((6 : ℤ) • WeilDivisor.ofPoint P)).subtype hli
  have _ := finiteDimensional_riemannRochSpace hF ((6 : ℤ) • WeilDivisor.ofPoint P)
  have hspan : Submodule.span k (Set.range v') = ⊤ :=
    hli'.span_eq_top_of_card_eq_finrank' (by simp [hdim])
  have hy2 : y ^ 2 ∈ riemannRochSpace ((6 : ℤ) • WeilDivisor.ofPoint P) :=
    (mem_riemannRochSpace_zsmul_ofPoint_iff (pow_ne_zero 2 hy0)).mpr
      ⟨by rw [P.ord_pow, hyP]; norm_num, fun Q hQ ↦ by
        rw [Q.ord_pow]
        have := hyQ Q hQ
        omega⟩
  have hy2' : (⟨y ^ 2, hy2⟩ : riemannRochSpace _) ∈ Submodule.span k (Set.range v') :=
    hspan ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp hy2'
  have hrel : ∑ i, c i • v i = y ^ 2 := by
    have := congrArg Subtype.val hc
    simpa [hv'] using this
  refine ⟨c, fun h5 ↦ ?_, hrel⟩
  have hmem' : y ^ 2 ∈ riemannRochSpace ((5 : ℤ) • WeilDivisor.ofPoint P) := by
    rw [← hrel, ← Finset.sum_erase Finset.univ (a := 5) (by simp [h5])]
    exact Submodule.sum_mem _ fun i hi ↦
      Submodule.smul_mem _ _ (hmem5 i (Finset.ne_of_mem_erase hi))
  have := ((mem_riemannRochSpace_zsmul_ofPoint_iff (pow_ne_zero 2 hy0)).mp hmem').1
  rw [P.ord_pow, hyP] at this
  norm_num at this

/-- THEOREM (proved, S2b coordinates). Riemann–Roch constructs Weierstrass coordinates at
any rational place of a genus-one function field with exact constants.
Locator: Silverman, Proposition III.3.1; Tau Ceti, `Elliptic/Weierstrass/Equation.lean`,
`exists_isWeierstrassCoordinates_of_genus_eq_one`. -/
theorem exists_weierstrassCoordinates_of_genus_eq_one (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hg : genus k F = 1) {P : Place k F} (hP : P.degree = 1) :
    ∃ (W : WeierstrassCurve k) (x y : F), WeierstrassCoordinates P W x y := by
  obtain ⟨x, hx0, hxP, hxQ⟩ :=
    P.exists_ord_eq_neg_and_forall_ne_ord_nonneg hF hex (n := 2) (by omega)
  obtain ⟨y, hy0, hyP, hyQ⟩ :=
    P.exists_ord_eq_neg_and_forall_ne_ord_nonneg hF hex (n := 3) (by omega)
  have hxP' : P.ord x = -2 := by simpa using hxP
  have hyP' : P.ord y = -3 := by simpa using hyP
  obtain ⟨c, hc5, hrel⟩ :=
    exists_cubic_relation hF hex hg hP hx0 hxP' hxQ hy0 hyP' hyQ
  simp only [Fin.sum_univ_six, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Algebra.smul_def, mul_one] at hrel
  have hc5' : algebraMap k F (c 5) ≠ 0 := (_root_.map_ne_zero _).mpr hc5
  refine ⟨⟨-c 4, c 3, -(c 5 * c 2), c 5 * c 1, c 5 ^ 2 * c 0⟩, algebraMap k F (c 5) * x,
    algebraMap k F (c 5) * y, ?_, fun Q hQ ↦ ?_, ?_, fun Q hQ ↦ ?_, ?_⟩
  · rw [P.ord_mul hc5' hx0, P.ord_algebraMap, hxP', zero_add]
  · rw [Q.ord_mul hc5' hx0, Q.ord_algebraMap, zero_add]
    exact hxQ Q hQ
  · rw [P.ord_mul hc5' hy0, P.ord_algebraMap, hyP', zero_add]
  · rw [Q.ord_mul hc5' hy0, Q.ord_algebraMap, zero_add]
    exact hyQ Q hQ
  · rw [Affine.equation_iff]
    simp only [baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, map_neg, map_mul, map_pow]
    linear_combination -(algebraMap k F (c 5)) ^ 2 * hrel

/-! ## A rational singular point forces genus zero -/

/-- THEOREM (proved). A field generated by a single transcendental element has genus zero.
Locator: Tau Ceti, `Consequences/GenusZero.lean`, `genus_eq_zero_of_adjoin_eq_top`.
The proof uses the dimension growth of powers and high-degree Riemann–Roch. -/
private theorem genus_zero_of_single_generator {x : F} (hx : Transcendental k x)
    (htop : k⟮x⟯ = (⊤ : IntermediateField k F)) : genus k F = 0 := by
  have hx0 : x ≠ 0 := fun h ↦ hx (h ▸ isAlgebraic_zero)
  have hfinrank : Module.finrank k⟮x⟯ F = 1 :=
    IntermediateField.finrank_eq_one_iff_eq_top.mpr (by simpa using htop)
  have hfd : FiniteDimensional k⟮x⟯ F := Module.finite_of_finrank_pos (by omega)
  have hF : IsFunctionField k F := hx.isFunctionField_adjoin.finite_extension
  let e : RatFunc k ≃ₐ[k] F :=
    (RatFunc.algEquivOfTranscendental x hx).trans
      ((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv)
  have hex : IsIntegrallyClosedIn k F := by
    refine isIntegrallyClosedIn_iff_forall_isAlgebraic.mpr fun y hy ↦ ?_
    obtain ⟨c, hc⟩ := isIntegrallyClosedIn_iff_forall_isAlgebraic.mp
      (isIntegrallyClosedIn_ratFunc (k := k)) (e.symm y) (hy.algHom e.symm.toAlgHom)
    exact ⟨c, by rw [← e.commutes c, hc, e.apply_symm_apply]⟩
  have hpoles : Divisor.degree (Divisor.poles hF (Units.mk0 x hx0)) = 1 := by
    rw [Divisor.degree_poles hF (Units.mk0 x hx0) hx]
    exact_mod_cast hfinrank
  set l : ℕ := 2 * genus k F with hl
  have hlow := Divisor.succ_le_dim_nsmul_poles hF (Units.mk0 x hx0) hx l
  have hdeg : Divisor.degree (l • Divisor.poles hF (Units.mk0 x hx0)) = (l : ℤ) := by
    rw [map_nsmul, hpoles, nsmul_eq_mul, mul_one]
  have heq := Divisor.dim_eq_degree_add_one_sub_genus_of_two_mul_genus_sub_one_le_degree hF hex
    (D := l • Divisor.poles hF (Units.mk0 x hx0)) (by rw [hdeg, hl]; omega)
  rw [hdeg] at heq
  omega

namespace WeierstrassCoordinates

variable {P : Place k F} {W : WeierstrassCurve k} {x y : F}
  (h : WeierstrassCoordinates P W x y)
include h

/-- THEOREM (proved). The slope from a rational singular point generates the function field.
Locator: Silverman, Proposition III.1.4; Tau Ceti, `Elliptic/Nonsingular.lean`,
`IsWeierstrassCoordinates.adjoin_div_eq_top_of_isSingular`. -/
theorem singular_slope_generates (hF : IsFunctionField k F) (hP : P.degree = 1)
    {x₀ y₀ : k} (hs : W.toAffine.IsSingular x₀ y₀) :
    k⟮(y - algebraMap k F y₀) / (x - algebraMap k F x₀)⟯ = ⊤ := by
  set X := x - algebraMap k F x₀ with hXdef
  set z := (y - algebraMap k F y₀) / X
  have hX0 : X ≠ 0 := sub_ne_zero.mpr fun hx ↦
    h.transcendental_x (hx ▸ isAlgebraic_algebraMap x₀)
  have hY : y - algebraMap k F y₀ = z * X := (div_mul_cancel₀ _ hX0).symm
  have hXz : X = z ^ 2 + algebraMap k F W.a₁ * z - algebraMap k F (3 * x₀ + W.a₂) := by
    have key := (Affine.equation_iff_of_isSingular (hs.map (algebraMap k F)) x y).mp h.equation
    simp only [Affine.map, map_a₁, map_a₂, ← map_ofNat (algebraMap k F) 3, ← map_mul,
      ← map_add] at key
    rw [← hXdef, hY] at key
    have hz : X ^ 2 * (X - (z ^ 2 + algebraMap k F W.a₁ * z -
        algebraMap k F (3 * x₀ + W.a₂))) = 0 := by
      linear_combination -key
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (pow_ne_zero 2 hX0))
  set K := k⟮z⟯
  have hz : z ∈ K := IntermediateField.mem_adjoin_simple_self k z
  have hXK : X ∈ K := by
    rw [hXz]
    exact K.sub_mem (K.add_mem (pow_mem hz 2) (K.mul_mem (K.algebraMap_mem _) hz))
      (K.algebraMap_mem _)
  have hxK : x ∈ K := by
    have hx : x = X + algebraMap k F x₀ := (sub_add_cancel x _).symm
    rw [hx]
    exact K.add_mem hXK (K.algebraMap_mem x₀)
  have hyK : y ∈ K := by
    have hy : y = z * X + algebraMap k F y₀ := eq_add_of_sub_eq hY
    rw [hy]
    exact K.add_mem (K.mul_mem hz hXK) (K.algebraMap_mem y₀)
  rw [eq_top_iff, ← h.adjoin_eq_top hF hP, IntermediateField.adjoin_le_iff]
  exact Set.insert_subset_iff.mpr ⟨hxK, Set.singleton_subset_iff.mpr hyK⟩

/-- THEOREM (proved). The generating slope from a rational singular point is transcendental.
Locator: Tau Ceti, `Elliptic/Nonsingular.lean`,
`IsWeierstrassCoordinates.transcendental_div_of_isSingular`. -/
theorem singular_slope_transcendental (hF : IsFunctionField k F) (hP : P.degree = 1)
    {x₀ y₀ : k} (hs : W.toAffine.IsSingular x₀ y₀) :
    Transcendental k ((y - algebraMap k F y₀) / (x - algebraMap k F x₀)) := by
  set z := (y - algebraMap k F y₀) / (x - algebraMap k F x₀)
  have htop : k⟮z⟯ = ⊤ := h.singular_slope_generates hF hP hs
  refine fun hz ↦ h.transcendental_x ?_
  have := IntermediateField.isAlgebraic_adjoin_simple hz.isIntegral
  have hx : x ∈ k⟮z⟯ := htop ▸ IntermediateField.mem_top
  exact (Algebra.IsAlgebraic.isAlgebraic (⟨x, hx⟩ : k⟮z⟯)).algHom k⟮z⟯.val

/-- THEOREM (proved). A rational singular point would force genus zero.
Locator: Silverman, Proposition III.1.4; Tau Ceti, `Elliptic/Nonsingular.lean`,
`IsWeierstrassCoordinates.genus_eq_zero_of_isSingular`. -/
theorem genus_zero_of_singular (hF : IsFunctionField k F) (hP : P.degree = 1)
    {x₀ y₀ : k} (hs : W.toAffine.IsSingular x₀ y₀) : genus k F = 0 :=
  genus_zero_of_single_generator (h.singular_slope_transcendental hF hP hs)
    (h.singular_slope_generates hF hP hs)

/-- THEOREM (proved, S2b nonsingularity). Over perfect constants, positive genus rules out
zero discriminant. Locator: Silverman, Propositions III.1.4 and III.3.1;
Tau Ceti, `Elliptic/Nonsingular.lean`, `IsWeierstrassCoordinates.isElliptic`. -/
theorem isElliptic [PerfectField k] (hF : IsFunctionField k F) (hP : P.degree = 1)
    (hg : genus k F ≠ 0) : W.IsElliptic := by
  rw [isElliptic_iff, isUnit_iff_ne_zero]
  intro hΔ
  obtain ⟨x₀, y₀, hs⟩ := Affine.exists_isSingular_of_Δ_eq_zero W.toAffine hΔ
  exact hg (h.genus_zero_of_singular hF hP hs)

end WeierstrassCoordinates

/-! ## Evaluation gives the function-field isomorphism -/

variable {W : WeierstrassCurve.Affine k} {x y : F}

/-- THEOREM (proved). Evaluation of the coordinate ring is injective when the first
coordinate is transcendental. Locator: Tau Ceti, `Affine/FunctionField/Lift.lean`,
`evalAlgHom_injective`. -/
private theorem evaluation_injective (h : (W⁄F).toAffine.Equation x y)
    (hx : Transcendental k x) : Function.Injective (Affine.CoordinateRing.evalAlgHom h) :=
  Affine.CoordinateRing.algHom_injective _ <| by
    rwa [Affine.CoordinateRing.mk, AdjoinRoot.mk_C, Affine.CoordinateRing.evalAlgHom_of_X]

/-- DEFINITION. A transcendental solution defines an embedding of the Weierstrass function
field into the given field. Locator: Tau Ceti, `Affine/FunctionField/Lift.lean`,
`functionFieldLift`. -/
def weierstrassFieldLift (h : (W⁄F).toAffine.Equation x y)
    (hx : Transcendental k x) : W.FunctionField →ₐ[k] F :=
  IsFractionRing.liftAlgHom (evaluation_injective h hx)

/-- THEOREM (proved). The lifted embedding restricts to evaluation on the coordinate ring.
Locator: Tau Ceti, `Affine/FunctionField/Lift.lean`, `functionFieldLift_algebraMap`. -/
theorem weierstrassFieldLift_algebraMap (h : (W⁄F).toAffine.Equation x y)
    (hx : Transcendental k x) (z : W.CoordinateRing) :
    weierstrassFieldLift h hx (algebraMap W.CoordinateRing W.FunctionField z) =
      Affine.CoordinateRing.evalAlgHom h z := by
  simp [weierstrassFieldLift, IsFractionRing.liftAlgHom_apply]

/-- THEOREM (proved). The lifted embedding takes the generic first coordinate to `x`.
Locator: Tau Ceti, `Affine/FunctionField/Lift.lean`, `functionFieldLift_genericX`. -/
theorem weierstrassFieldLift_genericX (h : (W⁄F).toAffine.Equation x y)
    (hx : Transcendental k x) : weierstrassFieldLift h hx W.genericX = x := by
  rw [Affine.genericX_def, weierstrassFieldLift_algebraMap, Affine.CoordinateRing.mk,
    AdjoinRoot.mk_C, Affine.CoordinateRing.evalAlgHom_of_X]

/-- THEOREM (proved). The lifted embedding takes the generic second coordinate to `y`.
Locator: Tau Ceti, `Affine/FunctionField/Lift.lean`, `functionFieldLift_genericY`. -/
theorem weierstrassFieldLift_genericY (h : (W⁄F).toAffine.Equation x y)
    (hx : Transcendental k x) : weierstrassFieldLift h hx W.genericY = y := by
  rw [Affine.genericY_def, weierstrassFieldLift_algebraMap, Affine.CoordinateRing.mk,
    AdjoinRoot.mk_X, Affine.CoordinateRing.evalAlgHom_root]

/-- THEOREM (proved). The image of the lifted embedding is the field generated by `x` and `y`.
Locator: Tau Ceti, `Affine/FunctionField/Lift.lean`, `fieldRange_functionFieldLift`. -/
theorem weierstrassFieldLift_fieldRange (h : (W⁄F).toAffine.Equation x y)
    (hx : Transcendental k x) : (weierstrassFieldLift h hx).fieldRange = k⟮x, y⟯ := by
  rw [Affine.fieldRange_eq_adjoin_genericX_genericY, weierstrassFieldLift_genericX,
    weierstrassFieldLift_genericY]

/-- DEFINITION. When the coordinate functions generate the field, evaluation is a
constant-field algebra isomorphism. Locator: Tau Ceti, `Affine/FunctionField/Lift.lean`,
`functionFieldEquivOfAdjoinEqTop`. -/
def weierstrassFieldEquiv (h : (W⁄F).toAffine.Equation x y)
    (hx : Transcendental k x) (hxy : k⟮x, y⟯ = ⊤) : W.FunctionField ≃ₐ[k] F :=
  AlgEquiv.ofBijective (weierstrassFieldLift h hx)
    ⟨(weierstrassFieldLift h hx).toRingHom.injective, fun z ↦ by
      have hz : z ∈ (weierstrassFieldLift h hx).fieldRange := by
        rw [weierstrassFieldLift_fieldRange, hxy]
        trivial
      exact hz⟩

/-- THEOREM (proved). The function-field isomorphism takes the generic first coordinate to `x`.
Locator: Tau Ceti, `Affine/FunctionField/Lift.lean`, `functionFieldLift_genericX`
and `functionFieldEquivOfAdjoinEqTop`. -/
theorem weierstrassFieldEquiv_genericX (h : (W⁄F).toAffine.Equation x y)
    (hx : Transcendental k x) (hxy : k⟮x, y⟯ = ⊤) :
    weierstrassFieldEquiv h hx hxy W.genericX = x :=
  weierstrassFieldLift_genericX h hx

/-- THEOREM (proved). The function-field isomorphism takes the generic second coordinate to `y`.
Locator: Tau Ceti, `Affine/FunctionField/Lift.lean`, `functionFieldLift_genericY`
and `functionFieldEquivOfAdjoinEqTop`. -/
theorem weierstrassFieldEquiv_genericY (h : (W⁄F).toAffine.Equation x y)
    (hx : Transcendental k x) (hxy : k⟮x, y⟯ = ⊤) :
    weierstrassFieldEquiv h hx hxy W.genericY = y :=
  weierstrassFieldLift_genericY h hx

/-! ## The existence statements -/

/-- THEOREM (proved, S2b over arbitrary constants). Every genus-one function field with exact
constants and a rational place is the function field of a Weierstrass equation. This statement
does not assert nonzero discriminant. Locator: Silverman, Proposition III.3.1;
`exists_weierstrassCoordinates_of_genus_eq_one` and `weierstrassFieldEquiv` in this file. -/
theorem exists_weierstrassEquation_of_genus_eq_one (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hg : genus k F = 1) {P : Place k F} (hP : P.degree = 1) :
    ∃ W : WeierstrassCurve.Affine k, Nonempty (W.FunctionField ≃ₐ[k] F) := by
  obtain ⟨W, x, y, h⟩ := exists_weierstrassCoordinates_of_genus_eq_one hF hex hg hP
  exact ⟨W.toAffine, ⟨weierstrassFieldEquiv h.equation h.transcendental_x
    (h.adjoin_eq_top hF hP)⟩⟩

/-- THEOREM (proved, S2b over perfect constants). Riemann–Roch produces a Weierstrass curve
with nonzero discriminant and a constant-field algebra isomorphism of function fields.
The isomorphism's coordinate functions have the prescribed sole poles of orders two and three.
Locator: Silverman, Proposition III.3.1. -/
theorem exists_weierstrassModel_of_genus_eq_one [PerfectField k] (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hg : genus k F = 1) {P : Place k F} (hP : P.degree = 1) :
    ∃ W : WeierstrassCurve.Affine k, W.IsElliptic ∧
      ∃ e : W.FunctionField ≃ₐ[k] F,
        P.ord (e W.genericX) = -2 ∧ P.ord (e W.genericY) = -3 ∧
        (∀ Q : Place k F, Q ≠ P → 0 ≤ Q.ord (e W.genericX)) ∧
        (∀ Q : Place k F, Q ≠ P → 0 ≤ Q.ord (e W.genericY)) := by
  obtain ⟨W, x, y, h⟩ := exists_weierstrassCoordinates_of_genus_eq_one hF hex hg hP
  have hW : W.IsElliptic := h.isElliptic hF hP (by omega)
  let e := weierstrassFieldEquiv h.equation h.transcendental_x (h.adjoin_eq_top hF hP)
  refine ⟨W.toAffine, hW, e, ?_⟩
  simpa only [e, weierstrassFieldEquiv_genericX, weierstrassFieldEquiv_genericY] using
    And.intro h.ord_x (And.intro h.ord_y (And.intro h.ord_x_nonneg h.ord_y_nonneg))

/-- THEOREM (proved, S2b). An elliptic function field over perfect exact constants is the
function field of a nonsingular Weierstrass curve. In particular this applies over `ℚ`.
Locator: Silverman, Proposition III.3.1; the degree-one-place dictionary
`TauCeti.IsEllipticFunctionField.exists_place_degree_eq_one`. -/
theorem exists_weierstrassModel [PerfectField k] (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (he : IsEllipticFunctionField k F) :
    ∃ W : WeierstrassCurve.Affine k, W.IsElliptic ∧ Nonempty (W.FunctionField ≃ₐ[k] F) := by
  obtain ⟨P, hP⟩ := he.exists_place_degree_eq_one hF hex
  obtain ⟨W, hW, e, _⟩ := exists_weierstrassModel_of_genus_eq_one hF hex he.genus_eq_one hP
  exact ⟨W, hW, ⟨e⟩⟩

/-- THEOREM (proved, S2b over `ℚ`). Every elliptic function field over the rational numbers,
with exact constant field, has a nonsingular Weierstrass model over the rational numbers.
Locator: Silverman, Proposition III.3.1; `exists_weierstrassModel` in this file. -/
theorem s2b_rational {L : Type*} [Field L] [Algebra ℚ L]
    (hL : IsFunctionField ℚ L) (hex : IsIntegrallyClosedIn ℚ L)
    (he : IsEllipticFunctionField ℚ L) :
    ∃ W : WeierstrassCurve.Affine ℚ, W.IsElliptic ∧ Nonempty (W.FunctionField ≃ₐ[ℚ] L) :=
  exists_weierstrassModel hL hex he

end ZInQ.Contrib.RC53Assist.InvariantDifferential
