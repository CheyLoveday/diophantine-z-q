import ZInQKernel.Contrib.RC53Assist.IsogenyScheme.ProjectiveModel

/-!
# The projective Weierstrass model over an arbitrary field

For a Weierstrass curve `E` over an arbitrary field `K` this file constructs the projective
model `X = Proj A`, `A = K[X, Y, Z] ⧸ (Y²Z + a₁XYZ + a₃YZ² - X³ - a₂X²Z - a₄XZ² - a₆Z³)`,
graded by total degree, and proves:

* `X` is integral and proper over `Spec A₀`, `A₀ ≅ K` (`isIntegral_proj`, `isProper_proj`);
* the chart `D₊(Z)` is the affine curve (`affineEquivZChart`), and the function field of `X` is
  the function field of the curve (`projFunctionFieldEquiv`), by dehomogenization on germs;
* the point `O = [0 : 1 : 0]` (`pointO`) is the only point whose local ring is dominated by the
  place at infinity (`eq_pointO_of_dominated`), and its local ring is the valuation ring of that
  place, a discrete valuation ring (`isDiscreteValuationRing_stalk_pointO`).

Mathematical locator: Silverman, *The Arithmetic of Elliptic Curves*, second edition, I.1–I.2,
II.1–II.2 and III.1. The statements and proofs are those of the rational-number version in the
module `ZInQKernel.Contrib.RC53Assist.IsogenyScheme.ProjectiveModel` (same declaration names,
namespace `ZInQ.Contrib.RC53Assist.IsogenyScheme`), with the base field `ℚ` replaced by `K`.
The only mathematical changes in the proofs are at the steps where the rational version used
that every ring homomorphism out of `ℚ` is unique; here the corresponding compatibilities of the
`K`-algebra structures are proved (`algebraMap_zChartConst`, `affineToZChart_algebraMap`,
`zChartToFunctionField_zChartConst`, `dehomogenization_algebraMap`). The general lemmas
`eval₂_mul_left_of_isHomogeneous` and `exp_neg_lt_one` are reused from that module. Its
isogeny and pointed-morphism parts are not needed and are not reproduced. The curve need not
be elliptic.

**Classification.** Definitions and PROVED statements. No input is assumed.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.S2aNumberField

open AlgebraicGeometry CategoryTheory HomogeneousLocalization WeierstrassCurve MvPolynomial
open ZInQ.Contrib.RC53Assist.IsogenyScheme (eval₂_mul_left_of_isHomogeneous exp_neg_lt_one)

open scoped RatFunc

variable {K : Type} [Field K] (E : WeierstrassCurve K)

section Dehomogenization

/-- Theorem (proved): the classes of the coordinates have degree `1 • 1`, the degree in which
`HomogeneousLocalization.Away.mk` reads numerators over a single power of a coordinate
(`WeierstrassCurve.Projective.coord_mem_grading`). -/
theorem coord_mem_grading_smul (i : Fin 3) :
    E.toProjective.coord i ∈ E.toProjective.grading (1 • 1) := by
  simpa using E.toProjective.coord_mem_grading i

/-- Theorem (proved): **the generic point `[x : y : 1]` lies on the projective curve** over the
function field (Silverman, III.1; from `WeierstrassCurve.Affine.equation_genericX_genericY` and
`WeierstrassCurve.Projective.equation_some`). -/
theorem equation_genericPoint :
    (E.toProjective.map (algebraMap K E.toAffine.FunctionField)).Equation
      ![E.toAffine.genericX, E.toAffine.genericY, 1] := by
  rw [Projective.equation_some]
  exact E.toAffine.equation_genericX_genericY

/-- Definition: **dehomogenization** `A → K(E)`, `X ↦ x`, `Y ↦ y`, `Z ↦ 1`, the evaluation of the
homogeneous coordinate ring at the generic point (`WeierstrassCurve.Projective.evalHom`;
Silverman, III.1). -/
def dehomogenization : E.toProjective.CoordinateRing →+* E.toAffine.FunctionField :=
  E.toProjective.evalHom (algebraMap K _) (equation_genericPoint E)

/-- Theorem (proved): dehomogenization of the class of a polynomial `p` is `p(x, y, 1)`
(Silverman, I.2, III.1). -/
theorem dehomogenization_mk (p : MvPolynomial (Fin 3) K) :
    dehomogenization E (Ideal.Quotient.mk _ p) =
      eval₂ (algebraMap K _) ![E.toAffine.genericX, E.toAffine.genericY, 1] p :=
  E.toProjective.evalHom_mk _ _ p

/-- Theorem (proved): dehomogenization of the coordinates is `[x, y, 1]` (Silverman, I.2, III.1). -/
theorem dehomogenization_coord (i : Fin 3) :
    dehomogenization E (E.toProjective.coord i) =
      ![E.toAffine.genericX, E.toAffine.genericY, 1] i :=
  congrFun (E.toProjective.evalHom_comp_coord (algebraMap K _) (equation_genericPoint E)) i

/-- Theorem (proved): dehomogenization sends `Z` to the unit `1` (Silverman, I.2, III.1). -/
theorem isUnit_dehomogenization_Z : IsUnit (dehomogenization E (E.toProjective.coord 2)) := by
  rw [dehomogenization_coord]; simp

/-- Theorem (proved): the class of a polynomial in the homogeneous coordinate ring is its
evaluation at the coordinate classes (`MvPolynomial.mk_eq_eval₂`) (Silverman, I.2, III.1). -/
theorem mk_eq_eval₂_coord (p : MvPolynomial (Fin 3) K) :
    Ideal.Quotient.mk (Ideal.span {E.toProjective.polynomial}) p =
      eval₂ (algebraMap K E.toProjective.CoordinateRing) E.toProjective.coord p :=
  congrFun (MvPolynomial.mk_eq_eval₂ (Ideal.span {E.toProjective.polynomial})) p

/-- Theorem (proved): constants dehomogenize to constants
(`WeierstrassCurve.Projective.evalHom_comp_algebraMap`; Silverman, II.1). -/
theorem dehomogenization_algebraMap (c : K) :
    dehomogenization E (algebraMap K _ c) = algebraMap K E.toAffine.FunctionField c :=
  RingHom.congr_fun (E.toProjective.evalHom_comp_algebraMap _ (equation_genericPoint E)) c

end Dehomogenization

section ZChart

/-- Definition: the ring `A_(Z)` of degree-zero fractions `a / Zⁿ`, the coordinate ring of the
chart `D₊(Z)` (`HomogeneousLocalization.Away`; Silverman, III.1). -/
abbrev ZChart : Type := HomogeneousLocalization.Away E.toProjective.grading (E.toProjective.coord 2)

/-- Definition: the localization `A[1/Z]` containing the chart ring (Silverman, I.1, III.1). -/
abbrev ZLocalization : Type := Localization.Away (E.toProjective.coord 2)

/-- Definition: the chart ring maps to the function field by dehomogenization,
`a / Zⁿ ↦ a(x, y, 1)` (`IsLocalization.Away.lift`). -/
def zChartToFunctionField : ZChart E →+* E.toAffine.FunctionField :=
  (IsLocalization.Away.lift (E.toProjective.coord 2) (isUnit_dehomogenization_Z E)).comp
    (algebraMap (ZChart E) (ZLocalization E))

/-- Theorem (proved): `a / Zⁿ ↦ a(x, y, 1)` (Silverman, I.1, III.1). -/
theorem zChartToFunctionField_mk (n : ℕ) (a : E.toProjective.CoordinateRing) (ha) :
    zChartToFunctionField E (Away.mk _ (E.toProjective.coord_mem_grading 2) n a ha) =
      dehomogenization E a := by
  simp only [zChartToFunctionField, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    Away.val_mk]
  rw [Localization.mk_eq_mk']
  unfold IsLocalization.Away.lift
  rw [IsLocalization.lift_mk'_spec]
  simp [map_pow, dehomogenization_coord]

/-- Definition: the chart coordinate `X / Z` (Silverman, I.1, III.1). -/
def zChartX : ZChart E :=
  Away.mk _ (E.toProjective.coord_mem_grading 2) 1 _ (coord_mem_grading_smul E 0)

/-- Definition: the chart coordinate `Y / Z` (Silverman, I.1, III.1). -/
def zChartY : ZChart E :=
  Away.mk _ (E.toProjective.coord_mem_grading 2) 1 _ (coord_mem_grading_smul E 1)

/-- Definition: `Z¹` as an element of the localizing submonoid (Silverman, I.1, III.1). -/
def zPowerOne : Submonoid.powers (E.toProjective.coord 2) := ⟨E.toProjective.coord 2 ^ 1, 1, rfl⟩

/-- Definition: the inverse `1 / Z` in `A[1/Z]` (Silverman, I.1, III.1). -/
def zInv : ZLocalization E := Localization.mk 1 (zPowerOne E)

/-- Theorem (proved): `(1 / Z) · a = a / Z` (Silverman, I.1, III.1). -/
theorem zInv_mul (a : E.toProjective.CoordinateRing) :
    zInv E * algebraMap _ (ZLocalization E) a = Localization.mk a (zPowerOne E) := by
  rw [zInv, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul, one_mul, mul_one]

/-- Theorem (proved): `(1 / Z) · Z = 1` (Silverman, I.1, III.1). -/
theorem zInv_mul_Z : zInv E * algebraMap _ (ZLocalization E) (E.toProjective.coord 2) = 1 := by
  rw [zInv_mul]
  have h := Localization.mk_self (zPowerOne E)
  rwa [show ((zPowerOne E : Submonoid.powers _) : E.toProjective.CoordinateRing) =
    E.toProjective.coord 2 from pow_one _] at h

/-- Theorem (proved): `(1 / Z)ⁿ · a = a / Zⁿ` (Silverman, I.1, III.1). -/
theorem zInv_pow_mul (n : ℕ) (a : E.toProjective.CoordinateRing) :
    zInv E ^ n * algebraMap _ (ZLocalization E) a =
      Localization.mk a (⟨E.toProjective.coord 2 ^ n, n, rfl⟩ : Submonoid.powers _) := by
  rw [zInv, ← Localization.mk_one_eq_algebraMap, Localization.mk_pow, Localization.mk_mul, one_pow,
    one_mul]
  congr 1
  apply Subtype.ext
  simp [zPowerOne]

/-- Theorem (proved): `X / Z` in `A[1/Z]` (Silverman, I.1, III.1). -/
theorem val_zChartX :
    (zChartX E).val = zInv E * algebraMap _ (ZLocalization E) (E.toProjective.coord 0) := by
  rw [zInv_mul]; rfl

/-- Theorem (proved): `Y / Z` in `A[1/Z]` (Silverman, I.1, III.1). -/
theorem val_zChartY :
    (zChartY E).val = zInv E * algebraMap _ (ZLocalization E) (E.toProjective.coord 1) := by
  rw [zInv_mul]; rfl

/-- Theorem (proved): evaluation at the coordinate classes in `A[1/Z]` is the class
(Silverman, I.1, III.1). -/
theorem eval₂_coord_zLocalization (p : MvPolynomial (Fin 3) K) :
    eval₂ (algebraMap K (ZLocalization E))
        (fun i => algebraMap _ (ZLocalization E) (E.toProjective.coord i)) p =
      algebraMap _ (ZLocalization E)
        (Ideal.Quotient.mk (Ideal.span {E.toProjective.polynomial}) p) := by
  have hc : (algebraMap E.toProjective.CoordinateRing (ZLocalization E)).comp (algebraMap K _) =
      algebraMap K (ZLocalization E) :=
    (IsScalarTower.algebraMap_eq K E.toProjective.CoordinateRing (ZLocalization E)).symm
  rw [mk_eq_eval₂_coord, eval₂_comp_left, hc]
  rfl

/-- Theorem (proved): **`(X/Z, Y/Z)` satisfies the affine Weierstrass equation** in `A[1/Z]`:
the projective equation holds at the coordinate classes and is invariant under the unit `1/Z`
(`WeierstrassCurve.Projective.equation_smul`; Silverman, III.1). -/
theorem equation_zLocalization :
    (E.toAffine⁄(ZLocalization E)).toAffine.Equation (zChartX E).val (zChartY E).val := by
  have h0 : (E.toProjective.map (algebraMap K (ZLocalization E))).Equation
      (algebraMap _ (ZLocalization E) ∘ E.toProjective.coord) := by
    rw [Projective.equation_map_iff_aeval]
    have h1 := (Projective.equation_map_iff_aeval E.toProjective E.toProjective.coord).mp
      E.toProjective.equation_coord
    rw [aeval_def] at h1 ⊢
    have hc : (algebraMap E.toProjective.CoordinateRing (ZLocalization E)).comp
        (algebraMap K _) = algebraMap K (ZLocalization E) :=
      (IsScalarTower.algebraMap_eq K E.toProjective.CoordinateRing (ZLocalization E)).symm
    calc eval₂ (algebraMap K (ZLocalization E))
          (algebraMap _ (ZLocalization E) ∘ E.toProjective.coord) E.toProjective.polynomial
        = eval₂ ((algebraMap E.toProjective.CoordinateRing (ZLocalization E)).comp
            (algebraMap K _)) (algebraMap _ (ZLocalization E) ∘ E.toProjective.coord)
            E.toProjective.polynomial := by
          rw [hc]
      _ = algebraMap _ (ZLocalization E) (eval₂ (algebraMap K _) E.toProjective.coord
            E.toProjective.polynomial) := (eval₂_comp_left _ _ _ _).symm
      _ = 0 := by rw [h1, map_zero]
  have hu : IsUnit (zInv E) := IsUnit.of_mul_eq_one _ (zInv_mul_Z E)
  have h2 := (Projective.equation_smul _ hu).mpr h0
  rw [Projective.smul_fin3] at h2
  have h3 : ![zInv E * (algebraMap _ (ZLocalization E) ∘ E.toProjective.coord) 0,
      zInv E * (algebraMap _ (ZLocalization E) ∘ E.toProjective.coord) 1,
      zInv E * (algebraMap _ (ZLocalization E) ∘ E.toProjective.coord) 2] =
      ![(zChartX E).val, (zChartY E).val, 1] := by
    simp only [Function.comp_apply, val_zChartX, val_zChartY, zInv_mul_Z]
  rw [h3, Projective.equation_some] at h2
  exact h2

/-- Definition: the constants `K → A_(Z)`, through the degree-zero part `A₀`
(Silverman, I.1, III.1). -/
def zChartConst : K →+* ZChart E :=
  (algebraMap (E.toProjective.grading 0) (ZChart E)).comp (algebraMap K (E.toProjective.grading 0))

/-- Theorem (proved): the chart constants are the constants of `A[1/Z]`; this replaces the
uniqueness of ring maps out of `ℚ` used over the rationals (Silverman, I.1, III.1). -/
theorem algebraMap_zChartConst :
    (algebraMap (ZChart E) (ZLocalization E)).comp (zChartConst E) =
      algebraMap K (ZLocalization E) := by
  ext c
  change (algebraMap (ZChart E) (ZLocalization E))
      ((algebraMap (E.toProjective.grading 0) (ZChart E))
        (algebraMap K (E.toProjective.grading 0) c)) = _
  rw [HomogeneousLocalization.algebraMap_eq, HomogeneousLocalization.algebraMap_apply]
  change Localization.mk _ 1 = _
  rw [Localization.mk_one_eq_algebraMap,
    IsScalarTower.algebraMap_apply K E.toProjective.CoordinateRing (ZLocalization E)]
  rfl

/-- Theorem (proved): `Y/Z` is a root of the Weierstrass polynomial over `K[X/Z]` in `A_(Z)`
(Silverman, I.1, III.1). -/
theorem root_zChart :
    Polynomial.eval₂ (Polynomial.eval₂RingHom (zChartConst E) (zChartX E)) (zChartY E)
      E.toAffine.polynomial = 0 := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers (E.toProjective.coord 2))
  have hv : (algebraMap (ZChart E) (ZLocalization E)).comp
      (Polynomial.eval₂RingHom (zChartConst E) (zChartX E)) =
      Polynomial.eval₂RingHom (algebraMap K (ZLocalization E)) (zChartX E).val := by
    apply Polynomial.ringHom_ext
    · intro q
      have hq : (algebraMap (ZChart E) (ZLocalization E)).comp (zChartConst E) =
          algebraMap K (ZLocalization E) := algebraMap_zChartConst E
      simpa using RingHom.congr_fun hq q
    · simp
  rw [val_zero]
  change algebraMap (ZChart E) (ZLocalization E) _ = 0
  rw [Polynomial.hom_eval₂, hv]
  have h := equation_zLocalization E
  dsimp only [Affine.Equation, Affine.baseChange, WeierstrassCurve.baseChange] at h
  rw [Affine.map_polynomial, ← Polynomial.eval₂_eval₂RingHom_apply] at h
  exact h

/-- Definition: **the affine coordinate ring maps to the chart ring**, `x ↦ X/Z`, `y ↦ Y/Z`
(`AdjoinRoot.lift`; Silverman, III.1). -/
def affineToZChart : E.toAffine.CoordinateRing →+* ZChart E :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom (zChartConst E) (zChartX E)) (zChartY E)
    (root_zChart E)

/-- Theorem (proved): `x ↦ X/Z` (Silverman, I.1, III.1). -/
theorem affineToZChart_of_X :
    affineToZChart E (AdjoinRoot.of E.toAffine.polynomial Polynomial.X) = zChartX E := by
  simp [affineToZChart]

/-- Theorem (proved): `y ↦ Y/Z` (Silverman, I.1, III.1). -/
theorem affineToZChart_root :
    affineToZChart E (AdjoinRoot.root E.toAffine.polynomial) = zChartY E := by
  simp [affineToZChart]

/-- Theorem (proved): constants go to the chart constants (Silverman, I.1, III.1). -/
theorem affineToZChart_algebraMap (c : K) :
    affineToZChart E (algebraMap K E.toAffine.CoordinateRing c) = zChartConst E c := by
  rw [IsScalarTower.algebraMap_apply K (Polynomial K) E.toAffine.CoordinateRing,
    AdjoinRoot.algebraMap_eq, affineToZChart, AdjoinRoot.lift_of, Polynomial.algebraMap_eq,
    Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]

/-- Theorem (proved): the chart constants dehomogenize to the constants of the function field
(Silverman, I.1, III.1). -/
theorem zChartToFunctionField_zChartConst (c : K) :
    zChartToFunctionField E (zChartConst E c) = algebraMap K E.toAffine.FunctionField c := by
  have h1 : algebraMap (ZChart E) (ZLocalization E) (zChartConst E c) =
      algebraMap E.toProjective.CoordinateRing (ZLocalization E)
        (algebraMap K E.toProjective.CoordinateRing c) := by
    rw [← RingHom.comp_apply, algebraMap_zChartConst,
      IsScalarTower.algebraMap_apply K E.toProjective.CoordinateRing (ZLocalization E)]
  rw [zChartToFunctionField, RingHom.comp_apply, h1, IsLocalization.Away.lift_eq]
  exact dehomogenization_algebraMap E c

/-- Theorem (proved): `X/Z ↦ x` in the function field (Silverman, I.1, III.1). -/
theorem zChartToFunctionField_zChartX :
    zChartToFunctionField E (zChartX E) = E.toAffine.genericX := by
  rw [zChartX, zChartToFunctionField_mk, dehomogenization_coord]; rfl

/-- Theorem (proved): `Y/Z ↦ y` in the function field (Silverman, I.1, III.1). -/
theorem zChartToFunctionField_zChartY :
    zChartToFunctionField E (zChartY E) = E.toAffine.genericY := by
  rw [zChartY, zChartToFunctionField_mk, dehomogenization_coord]; rfl

/-- Theorem (proved): dehomogenization after `affineToZChart` is the inclusion of the affine
coordinate ring into its fraction field (`WeierstrassCurve.Affine.CoordinateRing.ringHom_ext`). -/
theorem zChartToFunctionField_comp_affineToZChart :
    (zChartToFunctionField E).comp (affineToZChart E) =
      algebraMap E.toAffine.CoordinateRing E.toAffine.FunctionField := by
  apply Affine.CoordinateRing.ringHom_ext
  · intro a
    rw [RingHom.comp_apply, affineToZChart_algebraMap, zChartToFunctionField_zChartConst,
      ← IsScalarTower.algebraMap_apply]
  · rw [RingHom.comp_apply, affineToZChart_of_X, zChartToFunctionField_zChartX,
      Affine.genericX_def, AdjoinRoot.mk_C]
  · rw [RingHom.comp_apply, affineToZChart_root, zChartToFunctionField_zChartY,
      Affine.genericY_def, AdjoinRoot.mk_X]

/-- Theorem (proved): `affineToZChart` is injective (Silverman, I.1, III.1). -/
theorem affineToZChart_injective : Function.Injective (affineToZChart E) := by
  intro r s h
  apply IsFractionRing.injective E.toAffine.CoordinateRing E.toAffine.FunctionField
  rw [← zChartToFunctionField_comp_affineToZChart, RingHom.comp_apply, RingHom.comp_apply, h]

/-- Definition: dehomogenization of a polynomial into the affine coordinate ring,
`p ↦ p(x, y, 1)` (Silverman, I.1, III.1). -/
def dehomogenizeAffine (p : MvPolynomial (Fin 3) K) : E.toAffine.CoordinateRing :=
  eval₂ (algebraMap K _) ![AdjoinRoot.of E.toAffine.polynomial Polynomial.X,
    AdjoinRoot.root E.toAffine.polynomial, 1] p

/-- Theorem (proved): **a form of degree `n` over `Zⁿ` is its dehomogenization**:
`affineToZChart (p(x, y, 1)) = p / Zⁿ` (homogeneous scaling by `1/Z`) (Silverman, I.1, III.1). -/
theorem affineToZChart_dehomogenizeAffine {p : MvPolynomial (Fin 3) K} {n : ℕ}
    (hp : p.IsHomogeneous n)
    (h : Ideal.Quotient.mk _ p ∈ E.toProjective.grading (n • 1)) :
    affineToZChart E (dehomogenizeAffine E p) =
      Away.mk _ (E.toProjective.coord_mem_grading 2) n _ h := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers (E.toProjective.coord 2))
  change algebraMap (ZChart E) (ZLocalization E) (affineToZChart E (dehomogenizeAffine E p)) = _
  rw [Away.val_mk, dehomogenizeAffine, ← RingHom.comp_apply, eval₂_comp_left]
  have hc : ((algebraMap (ZChart E) (ZLocalization E)).comp (affineToZChart E)).comp
      (algebraMap K _) = algebraMap K (ZLocalization E) := by
    ext c
    rw [RingHom.comp_apply, RingHom.comp_apply, affineToZChart_algebraMap, ← RingHom.comp_apply,
      algebraMap_zChartConst]
  have hv : (⇑((algebraMap (ZChart E) (ZLocalization E)).comp (affineToZChart E)) ∘
      ![AdjoinRoot.of E.toAffine.polynomial Polynomial.X, AdjoinRoot.root E.toAffine.polynomial,
        1]) = fun i => zInv E * algebraMap _ (ZLocalization E) (E.toProjective.coord i) := by
    funext i
    fin_cases i
    · simp [affineToZChart_of_X, ← val_zChartX]
    · simp [affineToZChart_root, ← val_zChartY]
    · simp [zInv_mul_Z]
  rw [hc, hv, eval₂_mul_left_of_isHomogeneous _ hp, eval₂_coord_zLocalization, zInv_pow_mul]

/-- Theorem (proved): `affineToZChart` is surjective: every `a / Zⁿ` is a dehomogenization
(Silverman, I.1, III.1). -/
theorem affineToZChart_surjective : Function.Surjective (affineToZChart E) := by
  intro t
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective _ (E.toProjective.coord_mem_grading 2) t
  obtain ⟨p, hp, rfl⟩ := E.toProjective.mem_grading_iff.mp ha
  rw [show n • (1 : ℕ) = n by simp] at hp
  exact ⟨dehomogenizeAffine E p, affineToZChart_dehomogenizeAffine E hp ha⟩

/-- Definition: **the chart `D₊(Z)` is the affine Weierstrass curve**, the ring isomorphism
`K[x, y] ⧸ (W(x, y)) ≃+* A_(Z)` (Silverman, III.1). -/
def affineEquivZChart : E.toAffine.CoordinateRing ≃+* ZChart E :=
  RingEquiv.ofBijective (affineToZChart E) ⟨affineToZChart_injective E, affineToZChart_surjective E⟩

/-- Theorem (proved): dehomogenization of the chart is the inclusion, read through
`affineEquivZChart` (Silverman, I.1, III.1). -/
theorem zChartToFunctionField_eq (t : ZChart E) :
    zChartToFunctionField E t =
      algebraMap _ E.toAffine.FunctionField ((affineEquivZChart E).symm t) := by
  conv_lhs => rw [← (affineEquivZChart E).apply_symm_apply t]
  exact RingHom.congr_fun (zChartToFunctionField_comp_affineToZChart E) _

/-- Instance: the chart ring is a domain (it is the affine coordinate ring)
(Silverman, I.1, III.1). -/
instance : IsDomain (ZChart E) :=
  MulEquiv.isDomain E.toAffine.CoordinateRing (affineEquivZChart E).symm.toMulEquiv

/-- Theorem (proved): `Z ≠ 0` in the homogeneous coordinate ring
(`WeierstrassCurve.Projective.coord_two_mem_nonZeroDivisors`). -/
theorem coord_two_ne_zero : E.toProjective.coord 2 ≠ 0 :=
  nonZeroDivisors.ne_zero E.toProjective.coord_two_mem_nonZeroDivisors

/-- Theorem (proved): `Zⁿ ≠ 0` (Silverman, I.1, III.1). -/
theorem coord_two_pow_ne_zero (n : ℕ) : E.toProjective.coord 2 ^ n ≠ 0 :=
  pow_ne_zero n (coord_two_ne_zero E)

/-- Theorem (proved): `a / Zⁿ ≠ 0` when `a ≠ 0` (Silverman, I.1, III.1). -/
theorem awayMk_ne_zero (n : ℕ) {a : E.toProjective.CoordinateRing} (ha) (h0 : a ≠ 0) :
    Away.mk _ (E.toProjective.coord_mem_grading 2) n a ha ≠ 0 := by
  intro h
  have h' := congrArg HomogeneousLocalization.val h
  rw [Away.val_mk, val_zero, Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff] at h'
  obtain ⟨⟨m, k, rfl⟩, hm⟩ := h'
  exact h0 ((mul_eq_zero.mp hm).resolve_left (coord_two_pow_ne_zero E k))

end ZChart

section FractionField

variable {E} {P : Ideal E.toProjective.CoordinateRing} [P.IsPrime]

/-- Theorem (proved): at the zero ideal, powers of `Z` are invertible (Silverman, I.2). -/
theorem powers_le_primeCompl (hP : P = ⊥) :
    Submonoid.powers (E.toProjective.coord 2) ≤ P.primeCompl := by
  rw [Submonoid.powers_le]
  subst hP
  exact coord_two_ne_zero E

/-- Definition: the algebra structure `A_(Z) → A_(P)` (homogeneous localizations,
`HomogeneousLocalization.mapId`), used at the zero ideal `P = ⊥`. -/
@[instance_reducible]
def zChartAlgebra (hP : P = ⊥) : Algebra (ZChart E) (AtPrime E.toProjective.grading P) :=
  (mapId E.toProjective.grading (powers_le_primeCompl hP)).toAlgebra

/-- Theorem (proved): **the homogeneous localization at the zero ideal is the fraction field of
the chart ring** `A_(Z)`: a degree-zero fraction `a / b` is `(a / Zⁿ) / (b / Zⁿ)`
(Silverman, I.2). -/
theorem isFractionRing_zChart (hP : P = ⊥) :
    @IsFractionRing (ZChart E) _ (AtPrime E.toProjective.grading P) _ (zChartAlgebra hP) := by
  let := zChartAlgebra hP
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨y, hy⟩
    obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective _ (E.toProjective.coord_mem_grading 2) y
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact nonZeroDivisors.ne_zero hy (by ext; simp [Localization.mk_zero])
    rw [← isUnit_iff_isUnit_val]
    change IsUnit (Localization.mk a _)
    rw [Localization.mk_eq_mk', IsLocalization.AtPrime.isUnit_mk'_iff]
    subst hP
    exact ha0
  · intro z
    obtain ⟨⟨i, ⟨a, ha⟩, ⟨b, hb⟩, hbP⟩, rfl⟩ := HomogeneousLocalization.mk_surjective z
    have hb0 : b ≠ 0 := by
      rintro rfl
      subst hP
      exact hbP rfl
    have ha' : a ∈ E.toProjective.grading (i • 1) := by simpa using ha
    have hb' : b ∈ E.toProjective.grading (i • 1) := by simpa using hb
    refine ⟨⟨Away.mk _ (E.toProjective.coord_mem_grading 2) i a ha',
      ⟨Away.mk _ (E.toProjective.coord_mem_grading 2) i b hb',
        mem_nonZeroDivisors_of_ne_zero (awayMk_ne_zero E i hb' hb0)⟩⟩, ?_⟩
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_mul]
    change _ * Localization.mk b _ = Localization.mk a _
    rw [HomogeneousLocalization.val_mk, Localization.mk_mul, Localization.mk_eq_mk_iff,
      Localization.r_iff_exists]
    exact ⟨1, by simp only [Submonoid.coe_mul]; ring⟩
  · intro x y hxy
    refine ⟨1, ?_⟩
    simp only [OneMemClass.coe_one, one_mul]
    obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective _ (E.toProjective.coord_mem_grading 2) x
    obtain ⟨m, c, hc, rfl⟩ := Away.mk_surjective _ (E.toProjective.coord_mem_grading 2) y
    have h' := congrArg HomogeneousLocalization.val hxy
    change Localization.mk a _ = Localization.mk c _ at h'
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists] at h'
    obtain ⟨⟨u, hu⟩, hu'⟩ := h'
    have hu0 : u ≠ 0 := by
      rintro rfl
      subst hP
      exact hu rfl
    apply HomogeneousLocalization.val_injective
    rw [Away.val_mk, Away.val_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simpa using mul_left_cancel₀ hu0 hu'⟩

/-- Theorem (proved): in `A_(P)`, `(a / b) · (b / Zⁱ) = a / Zⁱ` (Silverman, I.2). -/
theorem mk_mul_mapId (hP : P = ⊥) (i : ℕ) (a b : E.toProjective.grading i)
    (hb : (b : E.toProjective.CoordinateRing) ∈ P.primeCompl)
    (ha' : (a : E.toProjective.CoordinateRing) ∈ E.toProjective.grading (i • 1))
    (hb' : (b : E.toProjective.CoordinateRing) ∈ E.toProjective.grading (i • 1)) :
    HomogeneousLocalization.mk ⟨i, a, b, hb⟩ *
        mapId _ (powers_le_primeCompl hP) (Away.mk _ (E.toProjective.coord_mem_grading 2) i b hb') =
      mapId _ (powers_le_primeCompl hP)
        (Away.mk _ (E.toProjective.coord_mem_grading 2) i a ha') := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul]
  change _ * Localization.mk (b : E.toProjective.CoordinateRing) _ =
    Localization.mk (a : E.toProjective.CoordinateRing) _
  rw [HomogeneousLocalization.val_mk, Localization.mk_mul, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  exact ⟨1, by simp only [Submonoid.coe_mul]; ring⟩

variable (E) in
/-- Definition: **the homogeneous localization at the zero ideal is the function field**,
`A_(⊥) ≃+* K(E)`, from `affineEquivZChart` and `isFractionRing_zChart`
(`IsFractionRing.ringEquivOfRingEquiv`; Silverman, II.1). -/
def atPrimeEquivFunctionField (hP : P = ⊥) :
    AtPrime E.toProjective.grading P ≃+* E.toAffine.FunctionField :=
  letI := zChartAlgebra hP
  haveI := isFractionRing_zChart hP
  IsFractionRing.ringEquivOfRingEquiv (affineEquivZChart E).symm

/-- Theorem (proved): on the chart ring, the identification is dehomogenization (Silverman, I.2). -/
theorem atPrimeEquivFunctionField_mapId (hP : P = ⊥) (t : ZChart E) :
    atPrimeEquivFunctionField E hP (mapId _ (powers_le_primeCompl hP) t) =
      zChartToFunctionField E t := by
  let := zChartAlgebra hP
  have := isFractionRing_zChart hP
  rw [zChartToFunctionField_eq]
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap (affineEquivZChart E).symm t

/-- Theorem (proved): dehomogenization is injective on the chart ring (Silverman, I.2). -/
theorem zChartToFunctionField_ne_zero {t : ZChart E} (ht : t ≠ 0) :
    zChartToFunctionField E t ≠ 0 := by
  rw [zChartToFunctionField_eq]
  exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
    ((map_ne_zero_iff _ (affineEquivZChart E).symm.injective).mpr ht)

/-- Theorem (proved): **a nonzero form has nonzero dehomogenization** (Silverman, I.2). -/
theorem dehomogenization_ne_zero {i : ℕ} {b : E.toProjective.CoordinateRing}
    (hb : b ∈ E.toProjective.grading i) (h0 : b ≠ 0) : dehomogenization E b ≠ 0 := by
  have hb' : b ∈ E.toProjective.grading (i • 1) := by simpa using hb
  rw [← zChartToFunctionField_mk E i b hb']
  exact zChartToFunctionField_ne_zero (awayMk_ne_zero E i hb' h0)

/-- Theorem (proved): **the identification is dehomogenization of fractions**,
`a / b ↦ a(x, y, 1) / b(x, y, 1)` for forms `a, b` of equal degree (Silverman, I.2). -/
theorem atPrimeEquivFunctionField_mk (hP : P = ⊥) (i : ℕ) (a b : E.toProjective.grading i)
    (hb : (b : E.toProjective.CoordinateRing) ∈ P.primeCompl) :
    atPrimeEquivFunctionField E hP (HomogeneousLocalization.mk ⟨i, a, b, hb⟩) =
      dehomogenization E a / dehomogenization E b := by
  have ha' : (a : E.toProjective.CoordinateRing) ∈ E.toProjective.grading (i • 1) := by
    simp
  have hb' : (b : E.toProjective.CoordinateRing) ∈ E.toProjective.grading (i • 1) := by
    simp
  have hb0 : (b : E.toProjective.CoordinateRing) ≠ 0 := by
    rintro h
    subst hP
    exact hb h
  have h := congrArg (atPrimeEquivFunctionField E hP) (mk_mul_mapId hP i a b hb ha' hb')
  rw [map_mul, atPrimeEquivFunctionField_mapId, atPrimeEquivFunctionField_mapId,
    zChartToFunctionField_mk, zChartToFunctionField_mk] at h
  rw [eq_div_iff (dehomogenization_ne_zero b.2 hb0), h]

/-- Theorem (proved): the identification on a fraction with a power of a single form `f` as
denominator, `a / fⁿ ↦ a(x, y, 1) / f(x, y, 1)ⁿ` (Silverman, I.2). -/
theorem atPrimeEquivFunctionField_mapId_awayMk (hP : P = ⊥) {f : E.toProjective.CoordinateRing}
    {d : ℕ} (hf : f ∈ E.toProjective.grading d) (h : Submonoid.powers f ≤ P.primeCompl) (n : ℕ)
    (a : E.toProjective.CoordinateRing) (ha : a ∈ E.toProjective.grading (n • d)) :
    atPrimeEquivFunctionField E hP (mapId _ h (Away.mk _ hf n a ha)) =
      dehomogenization E a / dehomogenization E f ^ n :=
  (atPrimeEquivFunctionField_mk hP (n • d) ⟨a, ha⟩ ⟨f ^ n, SetLike.pow_mem_graded n hf⟩
    (h ⟨n, rfl⟩)).trans (by rw [map_pow])

end FractionField

section Scheme

/-- Instance: points of the projective model carry their homogeneous prime ideals
(`ProjectiveSpectrum.isPrime`). -/
instance isPrime_point (x : Proj E.toProjective.grading) :
    x.asHomogeneousIdeal.toIdeal.IsPrime :=
  x.isPrime

/-- Definition: **the generic point** of the projective model, the zero ideal of the domain `A`
(relevant because `Z ≠ 0` has degree one) (Silverman, I.2; `AlgebraicGeometry.Proj`). -/
def projGenericPoint : Proj E.toProjective.grading :=
  ProjectiveSpectrum.mk ⊥ (by simpa using Ideal.isPrime_bot) fun h => by
    have hZ : E.toProjective.coord 2 ∈ HomogeneousIdeal.irrelevant E.toProjective.grading := by
      rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply]
      exact DirectSum.decompose_of_mem_ne _ (E.toProjective.coord_mem_grading 2) one_ne_zero
    have h' := h hZ
    rw [← HomogeneousIdeal.mem_iff, HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot] at h'
    exact coord_two_ne_zero E h'

/-- Theorem (proved): the zero ideal specializes to every point, so it is a generic point of the
whole model (`ProjectiveSpectrum.le_iff_mem_closure`). -/
theorem isGenericPoint_projGenericPoint : IsGenericPoint (projGenericPoint E) Set.univ := by
  rw [isGenericPoint_def]
  refine Set.eq_univ_of_forall fun y => ?_
  exact (ProjectiveSpectrum.le_iff_mem_closure E.toProjective.grading (projGenericPoint E) y).mp
    ((ProjectiveSpectrum.as_ideal_le_as_ideal _ _ _).mp
      (show ⊥ ≤ y.asHomogeneousIdeal from bot_le))

/-- Instance (R1): **the projective model is irreducible**
(Silverman, I.2; `AlgebraicGeometry.Proj`). -/
instance irreducibleSpace_proj : IrreducibleSpace (Proj E.toProjective.grading) :=
  (irreducibleSpace_def _).mpr (by simpa using (isGenericPoint_projGenericPoint E).isIrreducible)

/-- Theorem (proved): the generic point of the projective model is the zero ideal
(Silverman, I.2; `AlgebraicGeometry.Proj`). -/
theorem genericPoint_proj : genericPoint (Proj E.toProjective.grading) = projGenericPoint E :=
  (genericPoint_spec _).eq (isGenericPoint_projGenericPoint E)

/-- Theorem (proved): the homogeneous prime ideal of the generic point is `⊥`
(Silverman, I.2; `AlgebraicGeometry.Proj`). -/
theorem genericPoint_proj_ideal :
    (genericPoint (Proj E.toProjective.grading)).asHomogeneousIdeal.toIdeal = ⊥ := by
  rw [genericPoint_proj]; rfl

/-- Instance (R1): **the projective model is reduced**: its stalks are homogeneous
localizations of the domain `A`, which embed in ordinary localizations (`Proj.stalkIso'`). -/
instance isReduced_proj : IsReduced (Proj E.toProjective.grading) := by
  refine @isReduced_of_isReduced_stalk _ fun x => ?_
  have : IsDomain (AtPrime E.toProjective.grading x.asHomogeneousIdeal.toIdeal) :=
    Function.Injective.isDomain (algebraMap (AtPrime E.toProjective.grading
      x.asHomogeneousIdeal.toIdeal) (Localization x.asHomogeneousIdeal.toIdeal.primeCompl))
      (HomogeneousLocalization.val_injective _)
  exact isReduced_of_injective (Proj.stalkIso' E.toProjective.grading x)
    (Proj.stalkIso' E.toProjective.grading x).injective

/-- Instance (R1): **the projective model is integral**
(Silverman, I.2; `AlgebraicGeometry.Proj`). -/
instance isIntegral_proj : IsIntegral (Proj E.toProjective.grading) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

/-- Theorem (proved, R1): **the projective model is proper** over `Spec A₀`, where `A₀ ≅ K`
(`WeierstrassCurve.Projective.gradingZeroEquiv`); from Mathlib's properness of `Proj` of a graded
ring of finite type over its degree-zero part. -/
theorem isProper_proj : IsProper (Proj.toSpecZero E.toProjective.grading) :=
  inferInstance

/-- Definition (R2): **the function field of the projective model is the function field of the
curve**: the generic stalk is the homogeneous localization at `⊥` (`Proj.stalkIso`), which is
`K(E)` (`atPrimeEquivFunctionField`). -/
def projFunctionFieldEquiv :
    (Proj E.toProjective.grading).functionField ≃+* E.toAffine.FunctionField :=
  (Proj.stalkIso E.toProjective.grading (genericPoint _)).commRingCatIsoToRingEquiv.trans
    (atPrimeEquivFunctionField E (genericPoint_proj_ideal E))

/-- Theorem (proved): the generic point lies in every nonempty open of the projective model
(Silverman, I.2; `AlgebraicGeometry.Proj`). -/
theorem genericPoint_mem (U : (Proj E.toProjective.grading).Opens) [h : Nonempty U] :
    genericPoint (Proj E.toProjective.grading) ∈ U :=
  ((genericPoint_spec (Proj E.toProjective.grading)).mem_open_set_iff U.isOpen).mpr
    (by simpa using h)

/-- Theorem (proved, R2): **the identification on a germ**: a section `s`, read in the function
field, is its value at the generic point followed by `atPrimeEquivFunctionField`
(`Proj.stalkIso'_germ`). -/
theorem projFunctionFieldEquiv_germ (U : (Proj E.toProjective.grading).Opens) [Nonempty U]
    (s : Γ(Proj E.toProjective.grading, U)) :
    projFunctionFieldEquiv E ((Proj E.toProjective.grading).germToFunctionField U s) =
      atPrimeEquivFunctionField E (genericPoint_proj_ideal E)
        (s.1 ⟨genericPoint (Proj E.toProjective.grading), genericPoint_mem E U⟩) := by
  change atPrimeEquivFunctionField E _ (Proj.stalkIso' _ _ _) = _
  exact congrArg _ (Proj.stalkIso'_germ E.toProjective.grading U _ (genericPoint_mem E U) s)

end Scheme

section PointO

/-- Definition (R4): **the point `O = [0 : 1 : 0]`** of the projective model: the homogeneous core
of the kernel of evaluation at `(0, 1, 0)` (`WeierstrassCurve.Projective.evalZero`,
`Ideal.IsPrime.homogeneousCore`), relevant because `Y ↦ 1` (Silverman, III.1). -/
def pointO : Proj E.toProjective.grading :=
  ProjectiveSpectrum.mk
    ((RingHom.ker E.toProjective.evalZero).homogeneousCore E.toProjective.grading)
    (RingHom.ker_isPrime _).homogeneousCore fun h => by
      have hY : E.toProjective.coord 1 ∈ HomogeneousIdeal.irrelevant E.toProjective.grading := by
        rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply]
        exact DirectSum.decompose_of_mem_ne _ (E.toProjective.coord_mem_grading 1) one_ne_zero
      have h' := Ideal.toIdeal_homogeneousCore_le _ _ (h hY)
      rw [RingHom.mem_ker, Projective.evalZero_mk] at h'
      simp at h'

/-- Theorem (proved): a form lies in the ideal of `O` exactly when it vanishes at `(0, 1, 0)`
(Silverman, III.1). -/
theorem mem_pointO_iff {n : ℕ} {a : E.toProjective.CoordinateRing}
    (ha : a ∈ E.toProjective.grading n) :
    a ∈ (pointO E).asHomogeneousIdeal ↔ E.toProjective.evalZero a = 0 :=
  ⟨fun h => Ideal.toIdeal_homogeneousCore_le _ _ h,
    fun h => Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨n, ha⟩ h⟩

/-- Theorem (proved): the coordinates at `(0, 1, 0)` (Silverman, III.1). -/
theorem evalZero_coord (i : Fin 3) :
    E.toProjective.evalZero (E.toProjective.coord i) = ![0, 1, 0] i := by
  rw [Projective.evalZero_mk, MvPolynomial.eval_X]

end PointO

section Valuation

/-- Theorem (proved): `v_∞(y) = exp 3` (`WeierstrassCurve.Affine.infinityPlace.mk_Y`;
Silverman, III.1). -/
theorem infinityPlace_genericY :
    Affine.infinityPlace E.toAffine E.toAffine.genericY = WithZero.exp 3 := by
  rw [Affine.genericY_def]; exact Affine.infinityPlace.mk_Y _

/-- Theorem (proved): `v_∞(x) = exp 2` (`WeierstrassCurve.Affine.infinityPlace.X`). -/
theorem infinityPlace_genericX :
    Affine.infinityPlace E.toAffine E.toAffine.genericX = WithZero.exp 2 := by
  rw [Affine.genericX_eq_algebraMap,
    IsScalarTower.algebraMap_apply (Polynomial K) E.toAffine.CoordinateRing]
  exact Affine.infinityPlace.X _

/-- Theorem (proved): `y ≠ 0` in the function field (Silverman, II.1, III.1). -/
theorem genericY_ne_zero : E.toAffine.genericY ≠ 0 := fun h => by
  have := infinityPlace_genericY E
  rw [h, map_zero] at this
  exact WithZero.exp_ne_zero this.symm

/-- Theorem (proved): `v_∞(x / y) = exp (-1)` (Silverman, II.1, III.1). -/
theorem infinityPlace_X_div_Y :
    Affine.infinityPlace E.toAffine (E.toAffine.genericX / E.toAffine.genericY) =
      WithZero.exp (-1) := by
  rw [map_div₀, infinityPlace_genericX, infinityPlace_genericY, ← WithZero.exp_sub]
  norm_num

/-- Theorem (proved): `v_∞(1 / y) = exp (-3)` (Silverman, II.1, III.1). -/
theorem infinityPlace_inv_Y :
    Affine.infinityPlace E.toAffine E.toAffine.genericY⁻¹ = WithZero.exp (-3) := by
  rw [map_inv₀, infinityPlace_genericY, ← WithZero.exp_neg]

/-- Definition: the coordinates of the chart `D₊(Y)` in the function field,
`[X/Y, 1, Z/Y] = [x/y, 1, 1/y]` (Silverman, II.1, III.1). -/
abbrev yChartVec : Fin 3 → E.toAffine.FunctionField :=
  ![E.toAffine.genericX / E.toAffine.genericY, 1, E.toAffine.genericY⁻¹]

/-- Theorem (proved): the `D₊(Y)` coordinates are integral at infinity (Silverman, II.1, III.1). -/
theorem infinityPlace_yChartVec_le (i : Fin 3) :
    Affine.infinityPlace E.toAffine (yChartVec E i) ≤ 1 := by
  fin_cases i
  · exact (infinityPlace_X_div_Y E ▸ exp_neg_lt_one one_pos).le
  · simp
  · exact (infinityPlace_inv_Y E ▸ exp_neg_lt_one (by norm_num : (0 : ℤ) < 3)).le

/-- Theorem (proved): the `D₊(Y)` coordinates reduce at infinity to the coordinates `(0, 1, 0)`
of `O` (Silverman, II.1, III.1). -/
theorem infinityPlace_yChartVec_sub_lt (i : Fin 3) :
    Affine.infinityPlace E.toAffine (yChartVec E i - algebraMap K _ (![0, 1, 0] i)) < 1 := by
  fin_cases i
  · show Affine.infinityPlace E.toAffine (E.toAffine.genericX / E.toAffine.genericY -
      algebraMap K _ 0) < 1
    rw [map_zero, sub_zero, infinityPlace_X_div_Y]
    exact exp_neg_lt_one one_pos
  · simp
  · show Affine.infinityPlace E.toAffine (E.toAffine.genericY⁻¹ - algebraMap K _ 0) < 1
    rw [map_zero, sub_zero, infinityPlace_inv_Y]
    exact exp_neg_lt_one (by norm_num : (0 : ℤ) < 3)

/-- Theorem (proved): **reduction at infinity on the chart `D₊(Y)`**: for every polynomial `p`,
`v_∞(p(x/y, 1, 1/y) - p(0, 1, 0)) < 1` (Silverman, II.1, III.1). -/
theorem infinityPlace_eval_sub_lt_one (p : MvPolynomial (Fin 3) K) :
    Affine.infinityPlace E.toAffine (eval₂ (algebraMap K _) (yChartVec E) p -
      algebraMap K _ (eval ![0, 1, 0] p)) < 1 := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    rw [eval₂_add, eval_add, map_add,
      show ∀ a b c d : E.toAffine.FunctionField, a + b - (c + d) = (a - c) + (b - d) by
        intros; ring]
    exact Valuation.map_add_lt _ hp hq
  | mul_X p n hp =>
    rw [eval₂_mul, eval₂_X, eval_mul, eval_X, map_mul,
      show ∀ a b c d : E.toAffine.FunctionField, a * b - c * d = (a - c) * b + c * (b - d) by
        intros; ring]
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]
      exact mul_lt_one_of_lt_of_le hp (infinityPlace_yChartVec_le E n)
    · rw [map_mul, mul_comm]
      exact mul_lt_one_of_lt_of_le (infinityPlace_yChartVec_sub_lt E n)
        (Valuation.IsTrivialOn.valuation_algebraMap_le_one _ _)

/-- Theorem (proved): **a form of degree `n` over `yⁿ` reduces at infinity to its value at `O`**:
`v_∞(a(x, y, 1) / yⁿ - a(0, 1, 0)) < 1` (homogeneous scaling by `1/y`) (Silverman, II.1, III.1). -/
theorem infinityPlace_dehomogenization_div_sub_lt_one {n : ℕ} {a : E.toProjective.CoordinateRing}
    (ha : a ∈ E.toProjective.grading n) :
    Affine.infinityPlace E.toAffine (dehomogenization E a / E.toAffine.genericY ^ n -
      algebraMap K _ (E.toProjective.evalZero a)) < 1 := by
  obtain ⟨p, hp, rfl⟩ := E.toProjective.mem_grading_iff.mp ha
  rw [dehomogenization_mk, Projective.evalZero_mk]
  have hv : yChartVec E = fun i => E.toAffine.genericY⁻¹ *
      ![E.toAffine.genericX, E.toAffine.genericY, 1] i := by
    funext i
    fin_cases i
    · show E.toAffine.genericX / E.toAffine.genericY =
        E.toAffine.genericY⁻¹ * E.toAffine.genericX
      rw [div_eq_inv_mul]
    · show (1 : E.toAffine.FunctionField) = E.toAffine.genericY⁻¹ * E.toAffine.genericY
      rw [inv_mul_cancel₀ (genericY_ne_zero E)]
    · show E.toAffine.genericY⁻¹ = E.toAffine.genericY⁻¹ * 1
      rw [mul_one]
  have h := infinityPlace_eval_sub_lt_one E p
  rw [hv, eval₂_mul_left_of_isHomogeneous _ hp, inv_pow, ← div_eq_inv_mul] at h
  exact h

/-- Theorem (proved): a form of degree `n` has `v_∞(a(x, y, 1) / yⁿ) ≤ 1`
(Silverman, II.1, III.1). -/
theorem infinityPlace_dehomogenization_div_le_one {n : ℕ} {a : E.toProjective.CoordinateRing}
    (ha : a ∈ E.toProjective.grading n) :
    Affine.infinityPlace E.toAffine (dehomogenization E a / E.toAffine.genericY ^ n) ≤ 1 := by
  rw [← sub_add_cancel (dehomogenization E a / E.toAffine.genericY ^ n)
    (algebraMap K _ (E.toProjective.evalZero a))]
  exact Valuation.map_add_le _ (infinityPlace_dehomogenization_div_sub_lt_one E ha).le
    (Valuation.IsTrivialOn.valuation_algebraMap_le_one _ _)

/-- Theorem (proved): a form vanishing at `O` has `v_∞(a(x, y, 1) / yⁿ) < 1`
(Silverman, II.1, III.1). -/
theorem infinityPlace_dehomogenization_div_lt_one {n : ℕ} {a : E.toProjective.CoordinateRing}
    (ha : a ∈ E.toProjective.grading n) (h0 : E.toProjective.evalZero a = 0) :
    Affine.infinityPlace E.toAffine (dehomogenization E a / E.toAffine.genericY ^ n) < 1 := by
  simpa [h0] using infinityPlace_dehomogenization_div_sub_lt_one E ha

/-- Theorem (proved): a form not vanishing at `O` has `v_∞(b(x, y, 1) / yⁿ) = 1`
(Silverman, II.1, III.1). -/
theorem infinityPlace_dehomogenization_div_eq_one {n : ℕ} {b : E.toProjective.CoordinateRing}
    (hb : b ∈ E.toProjective.grading n) (h1 : E.toProjective.evalZero b ≠ 0) :
    Affine.infinityPlace E.toAffine (dehomogenization E b / E.toAffine.genericY ^ n) = 1 := by
  have h := infinityPlace_dehomogenization_div_sub_lt_one E hb
  have hc : Affine.infinityPlace E.toAffine (algebraMap K _ (E.toProjective.evalZero b)) = 1 :=
    Valuation.IsTrivialOn.eq_one (v := Affine.infinityPlace E.toAffine) _ h1
  rw [← sub_add_cancel (dehomogenization E b / E.toAffine.genericY ^ n)
    (algebraMap K _ (E.toProjective.evalZero b)), Valuation.map_add_eq_of_lt_right, hc]
  rwa [hc]

/-- Theorem (proved): **a fraction of forms regular at `O` is integral at infinity**:
`v_∞(a(x, y, 1) / b(x, y, 1)) ≤ 1` when `b(0, 1, 0) ≠ 0` (Silverman, II.1, III.1). -/
theorem infinityPlace_div_le_one {n : ℕ} {a b : E.toProjective.CoordinateRing}
    (ha : a ∈ E.toProjective.grading n) (hb : b ∈ E.toProjective.grading n)
    (h1 : E.toProjective.evalZero b ≠ 0) :
    Affine.infinityPlace E.toAffine (dehomogenization E a / dehomogenization E b) ≤ 1 := by
  rw [← div_div_div_cancel_right₀ (pow_ne_zero n (genericY_ne_zero E)), map_div₀,
    infinityPlace_dehomogenization_div_eq_one E hb h1, div_one]
  exact infinityPlace_dehomogenization_div_le_one E ha

/-- Theorem (proved): **a fraction of forms vanishing at `O` lies in the maximal ideal at
infinity**: `v_∞(a(x, y, 1) / b(x, y, 1)) < 1` when `a(0, 1, 0) = 0 ≠ b(0, 1, 0)`
(Silverman, II.1, III.1). -/
theorem infinityPlace_div_lt_one {n : ℕ} {a b : E.toProjective.CoordinateRing}
    (ha : a ∈ E.toProjective.grading n) (hb : b ∈ E.toProjective.grading n)
    (h0 : E.toProjective.evalZero a = 0) (h1 : E.toProjective.evalZero b ≠ 0) :
    Affine.infinityPlace E.toAffine (dehomogenization E a / dehomogenization E b) < 1 := by
  rw [← div_div_div_cancel_right₀ (pow_ne_zero n (genericY_ne_zero E)), map_div₀,
    infinityPlace_dehomogenization_div_eq_one E hb h1, div_one]
  exact infinityPlace_dehomogenization_div_lt_one E ha h0

end Valuation

section Stalk

/-- Theorem (proved, R4): **the place at infinity dominates the local ring at `O`, on sections**:
a section `t` over an open `V ∋ O`, read in the function field, has `v_∞ ≤ 1`; if its germ at
`O` lies in the maximal ideal, then `v_∞ < 1` (Silverman, II.1). -/
theorem infinityPlace_germ_pointO (V : (Proj E.toProjective.grading).Opens) [Nonempty V]
    (hO : pointO E ∈ V) (t : Γ(Proj E.toProjective.grading, V)) :
    Affine.infinityPlace E.toAffine
        (projFunctionFieldEquiv E ((Proj E.toProjective.grading).germToFunctionField V t)) ≤ 1 ∧
      ((Proj E.toProjective.grading).presheaf.germ V (pointO E) hO t ∈
          IsLocalRing.maximalIdeal ((Proj E.toProjective.grading).presheaf.stalk (pointO E)) →
        Affine.infinityPlace E.toAffine
          (projFunctionFieldEquiv E ((Proj E.toProjective.grading).germToFunctionField V t)) <
            1) := by
  obtain ⟨W, hOW, iWV, n, a, b, hbW, htW⟩ := t.2 ⟨pointO E, hO⟩
  have hηW : genericPoint (Proj E.toProjective.grading) ∈ W :=
    @genericPoint_mem K _ E W ⟨⟨_, hOW⟩⟩
  have hb0 : E.toProjective.evalZero b ≠ 0 := fun h =>
    hbW ⟨pointO E, hOW⟩ ((mem_pointO_iff E b.2).mpr h)
  have hval : projFunctionFieldEquiv E ((Proj E.toProjective.grading).germToFunctionField V t) =
      dehomogenization E a / dehomogenization E b := by
    rw [projFunctionFieldEquiv_germ, show t.1 ⟨genericPoint (Proj E.toProjective.grading),
      genericPoint_mem E V⟩ = HomogeneousLocalization.mk ⟨n, a, b, hbW ⟨_, hηW⟩⟩ from
      htW ⟨_, hηW⟩]
    exact atPrimeEquivFunctionField_mk (genericPoint_proj_ideal E) n a b (hbW ⟨_, hηW⟩)
  refine ⟨hval ▸ infinityPlace_div_le_one E a.2 b.2 hb0, fun ht => ?_⟩
  have h1 : Proj.stalkIso' E.toProjective.grading (pointO E)
      ((Proj E.toProjective.grading).presheaf.germ V (pointO E) hO t) =
      HomogeneousLocalization.mk ⟨n, a, b, hbW ⟨pointO E, hOW⟩⟩ :=
    (Proj.stalkIso'_germ _ V _ hO t).trans (htW ⟨pointO E, hOW⟩)
  have hnu : ¬ IsUnit (HomogeneousLocalization.mk ⟨n, a, b, hbW ⟨pointO E, hOW⟩⟩ :
      AtPrime E.toProjective.grading (pointO E).asHomogeneousIdeal.toIdeal) := by
    rw [← h1]
    intro hu
    exact (IsLocalRing.mem_maximalIdeal _).mp ht
      ((isUnit_map_iff (Proj.stalkIso' E.toProjective.grading (pointO E)) _).mp hu)
  have ha0 : E.toProjective.evalZero a = 0 := by
    rw [← mem_pointO_iff E a.2]
    by_contra hna
    apply hnu
    rw [← isUnit_iff_isUnit_val, val_mk, Localization.mk_eq_mk',
      IsLocalization.AtPrime.isUnit_mk'_iff]
    exact hna
  exact hval ▸ infinityPlace_div_lt_one E a.2 b.2 ha0 hb0

/-- Theorem (proved, R4): **the local ring at `O` lies in the valuation ring at infinity**: every
element of the stalk at `O`, read in the function field (`Scheme.functionField` algebra), has
`v_∞ ≤ 1` (Silverman, II.1). -/
theorem infinityPlace_le_one_of_stalk_pointO
    (g : (Proj E.toProjective.grading).presheaf.stalk (pointO E)) :
    Affine.infinityPlace E.toAffine (projFunctionFieldEquiv E
      (algebraMap _ (Proj E.toProjective.grading).functionField g)) ≤ 1 := by
  obtain ⟨V, hOV, t, rfl⟩ := (Proj E.toProjective.grading).presheaf.exists_germ_eq g
  have : Nonempty V := ⟨⟨_, hOV⟩⟩
  rw [Scheme.algebraMap_germ_eq_germToFunctionField]
  exact (infinityPlace_germ_pointO E V hOV t).1

/-- Theorem (proved, R4): **the maximal ideal at `O` lies in the maximal ideal at infinity**: an
element of the maximal ideal of the stalk at `O`, read in the function field, has `v_∞ < 1`
(Silverman, II.1). -/
theorem infinityPlace_lt_one_of_mem_maximalIdeal_pointO
    (g : (Proj E.toProjective.grading).presheaf.stalk (pointO E))
    (hg : g ∈ IsLocalRing.maximalIdeal ((Proj E.toProjective.grading).presheaf.stalk (pointO E))) :
    Affine.infinityPlace E.toAffine (projFunctionFieldEquiv E
      (algebraMap _ (Proj E.toProjective.grading).functionField g)) < 1 := by
  obtain ⟨V, hOV, t, rfl⟩ := (Proj E.toProjective.grading).presheaf.exists_germ_eq g
  have : Nonempty V := ⟨⟨_, hOV⟩⟩
  rw [Scheme.algebraMap_germ_eq_germToFunctionField]
  exact (infinityPlace_germ_pointO E V hOV t).2 hg

/-- Theorem (proved): the domination statement at any point equal to `O`, in the form used for
morphisms (a point given through an equation, so no unfolding of `pointO` is needed)
(Silverman, II.1). -/
theorem infinityPlace_germ_lt_one_of_eq_pointO (V : (Proj E.toProjective.grading).Opens)
    [Nonempty V] (x : Proj E.toProjective.grading) (hxO : x = pointO E) (hx : x ∈ V)
    (t : Γ(Proj E.toProjective.grading, V))
    (ht : (Proj E.toProjective.grading).presheaf.germ V x hx t ∈
      IsLocalRing.maximalIdeal ((Proj E.toProjective.grading).presheaf.stalk x)) :
    Affine.infinityPlace E.toAffine
      (projFunctionFieldEquiv E ((Proj E.toProjective.grading).germToFunctionField V t)) < 1 := by
  subst hxO
  exact (infinityPlace_germ_pointO E V hx t).2 ht

end Stalk

section YChart

/-- Definition: the section `Z / Y` of the structure sheaf over `D₊(Y)`
(`AlgebraicGeometry.Proj.awayToSection`). -/
def sectionZOverY : Γ(Proj E.toProjective.grading,
    Proj.basicOpen E.toProjective.grading (E.toProjective.coord 1)) :=
  (Proj.awayToSection E.toProjective.grading (E.toProjective.coord 1)).hom
    (Away.mk _ (E.toProjective.coord_mem_grading 1) 1 (E.toProjective.coord 2)
      (coord_mem_grading_smul E 2))

/-- Theorem (proved): `O ∈ D₊(Y)` (Silverman, III.1). -/
theorem pointO_mem_basicOpen :
    pointO E ∈ Proj.basicOpen E.toProjective.grading (E.toProjective.coord 1) := by
  rw [Proj.mem_basicOpen, mem_pointO_iff E (E.toProjective.coord_mem_grading 1), evalZero_coord]
  exact one_ne_zero

/-- Instance: `D₊(Y)` is nonempty (Silverman, III.1). -/
instance : Nonempty (Proj.basicOpen E.toProjective.grading (E.toProjective.coord 1)) :=
  ⟨⟨_, pointO_mem_basicOpen E⟩⟩

/-- Theorem (proved): the value of `Z / Y` at a point of `D₊(Y)` (Silverman, III.1). -/
theorem sectionZOverY_apply (x : Proj.basicOpen E.toProjective.grading (E.toProjective.coord 1)) :
    (sectionZOverY E).1 x = mapId _ (Submonoid.powers_le.mpr x.2)
      (Away.mk _ (E.toProjective.coord_mem_grading 1) 1 (E.toProjective.coord 2)
        (coord_mem_grading_smul E 2)) :=
  rfl

/-- Theorem (proved): **`Z / Y` vanishes at `O`**: its germ lies in the maximal ideal of the
stalk at `O` (Silverman, III.1). -/
theorem germ_sectionZOverY_mem_maximalIdeal :
    (Proj E.toProjective.grading).presheaf.germ _ (pointO E) (pointO_mem_basicOpen E)
      (sectionZOverY E) ∈
      IsLocalRing.maximalIdeal ((Proj E.toProjective.grading).presheaf.stalk (pointO E)) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have hu' := (isUnit_map_iff (Proj.stalkIso' E.toProjective.grading (pointO E)) _).mpr hu
  have h1 := Proj.stalkIso'_germ E.toProjective.grading _ (pointO E) (pointO_mem_basicOpen E)
    (sectionZOverY E)
  have hu'' : IsUnit ((sectionZOverY E).1 ⟨pointO E, pointO_mem_basicOpen E⟩) := by
    rw [← h1]; exact hu'
  rw [← isUnit_iff_isUnit_val] at hu''
  change IsUnit (Localization.mk (E.toProjective.coord 2) _) at hu''
  rw [Localization.mk_eq_mk', IsLocalization.AtPrime.isUnit_mk'_iff] at hu''
  apply hu''
  exact (mem_pointO_iff E (E.toProjective.coord_mem_grading 2)).mpr
    (by rw [evalZero_coord]; rfl)

/-- Theorem (proved): **`Z / Y` is the function `1 / y`** (Silverman, III.1). -/
theorem projFunctionFieldEquiv_sectionZOverY :
    projFunctionFieldEquiv E
        ((Proj E.toProjective.grading).germToFunctionField _ (sectionZOverY E)) =
      E.toAffine.genericY⁻¹ := by
  rw [projFunctionFieldEquiv_germ]
  have key := atPrimeEquivFunctionField_mapId_awayMk (genericPoint_proj_ideal E)
    (E.toProjective.coord_mem_grading 1) (Submonoid.powers_le.mpr (Ideal.mem_primeCompl_iff.mpr
      ((Proj.mem_basicOpen _ _ _).mp
        (genericPoint_mem E (Proj.basicOpen _ (E.toProjective.coord 1)))))) 1
    (E.toProjective.coord 2) (coord_mem_grading_smul E 2)
  exact key.trans (by rw [dehomogenization_coord, dehomogenization_coord]; simp)

end YChart

section Converse

/-- Instance: `D₊(Z)` is nonempty (it contains the generic point) (Silverman, II.1, III.1). -/
instance : Nonempty (Proj.basicOpen E.toProjective.grading (E.toProjective.coord 2)) := by
  refine ⟨⟨projGenericPoint E, ?_⟩⟩
  rw [Proj.mem_basicOpen]
  intro h
  rw [← HomogeneousIdeal.mem_iff] at h
  change E.toProjective.coord 2 ∈ (⊥ : HomogeneousIdeal E.toProjective.grading).toIdeal at h
  rw [HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot] at h
  exact coord_two_ne_zero E h

/-- Definition: the section `X / Z` of the structure sheaf over `D₊(Z)` (Silverman, II.1, III.1). -/
def sectionXOverZ : Γ(Proj E.toProjective.grading,
    Proj.basicOpen E.toProjective.grading (E.toProjective.coord 2)) :=
  (Proj.awayToSection E.toProjective.grading (E.toProjective.coord 2)).hom (zChartX E)

/-- Theorem (proved): **`X / Z` is the function `x`** (Silverman, II.1, III.1). -/
theorem projFunctionFieldEquiv_sectionXOverZ :
    projFunctionFieldEquiv E
        ((Proj E.toProjective.grading).germToFunctionField _ (sectionXOverZ E)) =
      E.toAffine.genericX := by
  rw [projFunctionFieldEquiv_germ]
  have key := atPrimeEquivFunctionField_mapId_awayMk (genericPoint_proj_ideal E)
    (E.toProjective.coord_mem_grading 2) (Submonoid.powers_le.mpr (Ideal.mem_primeCompl_iff.mpr
      ((Proj.mem_basicOpen _ _ _).mp
        (genericPoint_mem E (Proj.basicOpen _ (E.toProjective.coord 2)))))) 1
    (E.toProjective.coord 0) (coord_mem_grading_smul E 0)
  exact key.trans (by rw [dehomogenization_coord, dehomogenization_coord]; simp)

/-- Theorem (proved): a point whose local ring is dominated by the place at infinity lies on the
line `Z = 0`: otherwise the germ of `X / Z` would be the function `x`, which has a pole at
infinity (Silverman, II.1, III.1). -/
theorem coord_two_mem_of_dominated (P : Proj E.toProjective.grading)
    (H : ∀ g : (Proj E.toProjective.grading).presheaf.stalk P,
      Affine.infinityPlace E.toAffine (projFunctionFieldEquiv E
        (algebraMap _ (Proj E.toProjective.grading).functionField g)) ≤ 1) :
    E.toProjective.coord 2 ∈ P.asHomogeneousIdeal := by
  by_contra hZ
  have hP : P ∈ Proj.basicOpen E.toProjective.grading (E.toProjective.coord 2) := hZ
  have h := H ((Proj E.toProjective.grading).presheaf.germ _ P hP (sectionXOverZ E))
  rw [Scheme.algebraMap_germ_eq_germToFunctionField, projFunctionFieldEquiv_sectionXOverZ,
    infinityPlace_genericX, ← WithZero.exp_zero, WithZero.exp_le_exp] at h
  omega

/-- Theorem (proved): on the curve, `Z = 0` forces `X = 0`: `X³ ∈ (Z)` by the Weierstrass
equation (Silverman, III.1). -/
theorem coord_zero_mem_of_coord_two_mem (P : Proj E.toProjective.grading)
    (hZ : E.toProjective.coord 2 ∈ P.asHomogeneousIdeal) :
    E.toProjective.coord 0 ∈ P.asHomogeneousIdeal := by
  have heq := (Projective.equation_iff _).mp E.toProjective.equation_coord
  have hX3 : E.toProjective.coord 0 ^ 3 = E.toProjective.coord 2 *
      (E.toProjective.coord 1 ^ 2 +
        (E.toProjective.map (algebraMap K E.toProjective.CoordinateRing)).a₁ *
          E.toProjective.coord 0 * E.toProjective.coord 1 +
        (E.toProjective.map (algebraMap K E.toProjective.CoordinateRing)).a₃ *
          E.toProjective.coord 1 * E.toProjective.coord 2 -
        (E.toProjective.map (algebraMap K E.toProjective.CoordinateRing)).a₂ *
          E.toProjective.coord 0 ^ 2 -
        (E.toProjective.map (algebraMap K E.toProjective.CoordinateRing)).a₄ *
          E.toProjective.coord 0 * E.toProjective.coord 2 -
        (E.toProjective.map (algebraMap K E.toProjective.CoordinateRing)).a₆ *
          E.toProjective.coord 2 ^ 2) := by
    linear_combination (-1 : E.toProjective.CoordinateRing) * heq
  refine P.isPrime.mem_of_pow_mem 3 ?_
  rw [hX3]
  exact Ideal.mul_mem_right _ _ hZ

/-- Theorem (proved): substituting `X, Z ↦ 0` changes a polynomial by an element of `(X, Z)`
(Silverman, II.1, III.1). -/
theorem sub_aeval_mem_span (p : MvPolynomial (Fin 3) K) :
    p - aeval ![0, X 1, 0] p ∈ Ideal.span {(X 0 : MvPolynomial (Fin 3) K), X 2} := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    rw [map_add, add_sub_add_comm]
    exact Ideal.add_mem _ hp hq
  | mul_X p n hp =>
    rw [map_mul, aeval_X, show p * X n - aeval ![0, X 1, 0] p * ![0, X 1, 0] n =
      (p - aeval ![0, X 1, 0] p) * X n + aeval ![0, X 1, 0] p * (X n - ![0, X 1, 0] n) by ring]
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ ?_)
    fin_cases n
    · simpa using Ideal.subset_span (Set.mem_insert _ _)
    · simp
    · simpa using Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))

/-- Theorem (proved): on a form of degree `n`, substituting `X, Z ↦ 0` gives `p(0, 1, 0) Yⁿ`
(homogeneous scaling) (Silverman, II.1, III.1). -/
theorem aeval_eq_of_isHomogeneous {p : MvPolynomial (Fin 3) K} {n : ℕ} (hp : p.IsHomogeneous n) :
    aeval (![0, X 1, 0] : Fin 3 → MvPolynomial (Fin 3) K) p =
      C (MvPolynomial.eval ![0, 1, 0] p) * (X 1 : MvPolynomial (Fin 3) K) ^ n := by
  have hv : (![0, X 1, 0] : Fin 3 → MvPolynomial (Fin 3) K) = fun i => X 1 * C (![0, 1, 0] i) := by
    funext i
    fin_cases i <;> simp
  have hc : eval₂ (algebraMap K (MvPolynomial (Fin 3) K)) (fun i => C (![0, 1, 0] i)) p =
      C (MvPolynomial.eval ![0, 1, 0] p) := by
    rw [MvPolynomial.eval, coe_eval₂Hom, eval₂_comp_left]
    rfl
  rw [aeval_def, hv, eval₂_mul_left_of_isHomogeneous _ hp, hc, mul_comm]

/-- Theorem (proved): **a form of degree `n` is `a(0, 1, 0) Yⁿ` modulo `(X, Z)`**
(Silverman, II.1, III.1). -/
theorem form_sub_mem_span {n : ℕ} {a : E.toProjective.CoordinateRing}
    (ha : a ∈ E.toProjective.grading n) :
    a - algebraMap K _ (E.toProjective.evalZero a) * E.toProjective.coord 1 ^ n ∈
      Ideal.span {E.toProjective.coord 0, E.toProjective.coord 2} := by
  obtain ⟨p, hp, rfl⟩ := E.toProjective.mem_grading_iff.mp ha
  have h1 := Ideal.mem_map_of_mem (Ideal.Quotient.mk (Ideal.span {E.toProjective.polynomial}))
    (sub_aeval_mem_span p)
  rw [Ideal.map_span, Set.image_pair, map_sub, aeval_eq_of_isHomogeneous hp, map_mul, map_pow]
    at h1
  rw [Projective.evalZero_mk]
  exact h1

/-- Theorem (proved): **a point on `X = Z = 0` is `O`**: a relevant homogeneous prime containing
`X` and `Z` is the ideal of `O` (it cannot contain a form with `a(0, 1, 0) ≠ 0`, which would put
`Y` and hence the irrelevant ideal into it) (Silverman, II.1, III.1). -/
theorem eq_pointO_of_coord_mem (P : Proj E.toProjective.grading)
    (h0 : E.toProjective.coord 0 ∈ P.asHomogeneousIdeal)
    (h2 : E.toProjective.coord 2 ∈ P.asHomogeneousIdeal) : P = pointO E := by
  have hspan : Ideal.span {E.toProjective.coord 0, E.toProjective.coord 2} ≤
      P.asHomogeneousIdeal.toIdeal := by
    rw [Ideal.span_le]
    rintro z (rfl | rfl)
    · exact h0
    · exact h2
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro n a ha
  rw [mem_pointO_iff E ha]
  have hdec := form_sub_mem_span E ha
  constructor
  · intro haP
    by_contra hc
    have h1 : algebraMap K _ (E.toProjective.evalZero a) * E.toProjective.coord 1 ^ n ∈
        P.asHomogeneousIdeal.toIdeal := by
      have := sub_mem (show a ∈ P.asHomogeneousIdeal.toIdeal from haP) (hspan hdec)
      rwa [sub_sub_cancel] at this
    have hunit : IsUnit (algebraMap K E.toProjective.CoordinateRing
        (E.toProjective.evalZero a)) := (isUnit_iff_ne_zero.mpr hc).map _
    have hYn : E.toProjective.coord 1 ^ n ∈ P.asHomogeneousIdeal.toIdeal := by
      have := Ideal.mul_mem_left _ (↑hunit.unit⁻¹ : E.toProjective.CoordinateRing) h1
      rwa [← mul_assoc, IsUnit.val_inv_mul, one_mul] at this
    have hY := P.isPrime.mem_of_pow_mem n hYn
    apply P.not_irrelevant_le
    intro z hz
    have hz' := E.toProjective.irrelevant_le_span_range_coord hz
    refine (Ideal.span_le.mpr ?_) hz'
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact h0
    · exact hY
    · exact h2
  · intro hc
    rw [hc, map_zero, zero_mul, sub_zero] at hdec
    exact hspan hdec

/-- Theorem (proved, R4): **`O` is the only point whose local ring is dominated by the place at
infinity** (Silverman, II.1 and III.1). -/
theorem eq_pointO_of_dominated (P : Proj E.toProjective.grading)
    (H : ∀ g : (Proj E.toProjective.grading).presheaf.stalk P,
      Affine.infinityPlace E.toAffine (projFunctionFieldEquiv E
        (algebraMap _ (Proj E.toProjective.grading).functionField g)) ≤ 1) :
    P = pointO E :=
  have hZ := coord_two_mem_of_dominated E P H
  eq_pointO_of_coord_mem E P (coord_zero_mem_of_coord_two_mem E P hZ) hZ

/-- Theorem (proved, R4): **a point is `O` exactly when its local ring is dominated by the place
at infinity** (Silverman, II.1, III.1). -/
theorem dominated_iff_eq_pointO (P : Proj E.toProjective.grading) :
    (∀ g : (Proj E.toProjective.grading).presheaf.stalk P,
      Affine.infinityPlace E.toAffine (projFunctionFieldEquiv E
        (algebraMap _ (Proj E.toProjective.grading).functionField g)) ≤ 1) ↔ P = pointO E := by
  refine ⟨eq_pointO_of_dominated E P, ?_⟩
  rintro rfl
  exact infinityPlace_le_one_of_stalk_pointO E

end Converse

section LocalRingAtO

/-- Definition: the local ring at `O`, read in the function field of the curve (Silverman, II.1). -/
def stalkPointOToFunctionField :
    (Proj E.toProjective.grading).presheaf.stalk (pointO E) →+* E.toAffine.FunctionField :=
  (projFunctionFieldEquiv E).toRingHom.comp
    (algebraMap _ (Proj E.toProjective.grading).functionField)

/-- Theorem (proved): **the local ring at `O` consists of the fractions of forms regular at `O`**:
the germ of `a / b` (forms of equal degree, `b ∉ O`) is `a(x, y, 1) / b(x, y, 1)`
(`Proj.stalkIso'_symm_mk`). -/
theorem stalkPointOToFunctionField_mk
    (f : NumDenSameDeg E.toProjective.grading
      (pointO E).asHomogeneousIdeal.toIdeal.primeCompl) :
    stalkPointOToFunctionField E ((Proj.stalkIso' E.toProjective.grading (pointO E)).symm
      (HomogeneousLocalization.mk f)) =
      dehomogenization E f.num / dehomogenization E f.den := by
  have : Nonempty (Proj.basicOpen E.toProjective.grading (f.den : E.toProjective.CoordinateRing)) :=
    ⟨⟨pointO E, f.den_mem⟩⟩
  have h0 := congrArg (stalkPointOToFunctionField E)
    (Proj.stalkIso'_symm_mk E.toProjective.grading (pointO E) f)
  refine h0.trans ?_
  have h := Scheme.algebraMap_germ_eq_germToFunctionField (Proj E.toProjective.grading)
    (U := Proj.basicOpen E.toProjective.grading (f.den : E.toProjective.CoordinateRing))
    (x := pointO E) f.den_mem (sectionInBasicOpen _ (pointO E) f)
  refine ((congrArg (projFunctionFieldEquiv E) h).trans
    (projFunctionFieldEquiv_germ E _ _)).trans ?_
  exact atPrimeEquivFunctionField_mk (genericPoint_proj_ideal E) f.deg f.num f.den _

/-- Definition: the quadratic form `D = Y² + a₁XY + a₃YZ - a₂X² - a₄XZ - a₆Z²`; on the curve
`Z · D = X³`, so `D(x, y, 1) = x³` and `D(0, 1, 0) = 1` (Silverman, III.1). -/
def formD : E.toProjective.CoordinateRing :=
  E.toProjective.coord 1 ^ 2 +
    algebraMap K _ E.a₁ * (E.toProjective.coord 0 * E.toProjective.coord 1) +
    algebraMap K _ E.a₃ * (E.toProjective.coord 1 * E.toProjective.coord 2) -
    algebraMap K _ E.a₂ * E.toProjective.coord 0 ^ 2 -
    algebraMap K _ E.a₄ * (E.toProjective.coord 0 * E.toProjective.coord 2) -
    algebraMap K _ E.a₆ * E.toProjective.coord 2 ^ 2

/-- Theorem (proved): `D` is a form of degree two (Silverman, II.1). -/
theorem formD_mem : formD E ∈ E.toProjective.grading 2 := by
  have h1 : ∀ i j : Fin 3, E.toProjective.coord i * E.toProjective.coord j ∈
      E.toProjective.grading 2 := fun i j =>
    SetLike.mul_mem_graded (E.toProjective.coord_mem_grading i)
      (E.toProjective.coord_mem_grading j)
  have h2 : ∀ i : Fin 3, E.toProjective.coord i ^ 2 ∈ E.toProjective.grading 2 := fun i => by
    rw [pow_two]; exact h1 i i
  have hs : ∀ (c : K) {a : E.toProjective.CoordinateRing}, a ∈ E.toProjective.grading 2 →
      algebraMap K _ c * a ∈ E.toProjective.grading 2 := fun c a ha => by
    rw [← Algebra.smul_def]; exact Submodule.smul_mem _ c ha
  exact sub_mem (sub_mem (sub_mem (add_mem (add_mem (h2 1) (hs _ (h1 0 1))) (hs _ (h1 1 2)))
    (hs _ (h2 0))) (hs _ (h1 0 2))) (hs _ (h2 2))

/-- Theorem (proved): `D(0, 1, 0) = 1` (Silverman, II.1). -/
theorem evalZero_formD : E.toProjective.evalZero (formD E) = 1 := by
  simp [formD]

/-- Theorem (proved): `D(x, y, 1) = x³`, by the Weierstrass equation at the generic point
(Silverman, II.1). -/
theorem dehomogenization_formD : dehomogenization E (formD E) = E.toAffine.genericX ^ 3 := by
  have h0 := (Affine.equation_iff _ _).mp E.toAffine.equation_genericX_genericY
  have h : E.toAffine.genericY ^ 2 +
      algebraMap K E.toAffine.FunctionField E.a₁ * E.toAffine.genericX * E.toAffine.genericY +
      algebraMap K E.toAffine.FunctionField E.a₃ * E.toAffine.genericY =
      E.toAffine.genericX ^ 3 +
      algebraMap K E.toAffine.FunctionField E.a₂ * E.toAffine.genericX ^ 2 +
      algebraMap K E.toAffine.FunctionField E.a₄ * E.toAffine.genericX +
      algebraMap K E.toAffine.FunctionField E.a₆ := h0
  rw [formD]
  rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_sub, RingHom.map_add, RingHom.map_add,
    RingHom.map_mul, RingHom.map_mul, RingHom.map_mul, RingHom.map_mul, RingHom.map_mul,
    RingHom.map_mul, RingHom.map_mul, RingHom.map_mul, RingHom.map_pow, RingHom.map_pow,
    RingHom.map_pow, dehomogenization_algebraMap, dehomogenization_algebraMap,
    dehomogenization_algebraMap, dehomogenization_algebraMap, dehomogenization_algebraMap,
    dehomogenization_coord, dehomogenization_coord, dehomogenization_coord]
  change E.toAffine.genericY ^ 2 + _ * (E.toAffine.genericX * E.toAffine.genericY) +
    _ * (E.toAffine.genericY * 1) - _ * E.toAffine.genericX ^ 2 -
    _ * (E.toAffine.genericX * 1) - _ * 1 ^ 2 = _
  linear_combination h

/-- Theorem (proved): `x ≠ 0` in the function field (Silverman, II.1). -/
theorem genericX_ne_zero : E.toAffine.genericX ≠ 0 := fun h => by
  have := infinityPlace_genericX E
  rw [h, map_zero] at this
  exact WithZero.exp_ne_zero this.symm

/-- Definition: **the image of the local ring at `O`** in the function field (Silverman, II.1). -/
def stalkPointOImage : Subring E.toAffine.FunctionField :=
  (stalkPointOToFunctionField E).range

/-- Theorem (proved): a fraction of forms regular at `O` lies in the image of the local ring
(Silverman, II.1). -/
theorem div_mem_stalkPointOImage (n : ℕ) (a b : E.toProjective.grading n)
    (hb : E.toProjective.evalZero b ≠ 0) :
    dehomogenization E a / dehomogenization E b ∈ stalkPointOImage E :=
  ⟨_, stalkPointOToFunctionField_mk E ⟨n, a, b, fun h => hb ((mem_pointO_iff E b.2).mp h)⟩⟩

/-- Theorem (proved): constants lie in the image of the local ring at `O` (Silverman, II.1). -/
theorem algebraMap_mem_stalkPointOImage (c : K) :
    algebraMap K E.toAffine.FunctionField c ∈ stalkPointOImage E := by
  have h := div_mem_stalkPointOImage E 0 ⟨algebraMap K _ c, SetLike.algebraMap_mem_graded _ c⟩
    ⟨1, SetLike.one_mem_graded _⟩ (by simp)
  simpa [dehomogenization_algebraMap] using h

/-- Theorem (proved): `1 / x = X² / D` lies in the image of the local ring at `O`
(Silverman, II.1). -/
theorem inv_genericX_mem_stalkPointOImage :
    E.toAffine.genericX⁻¹ ∈ stalkPointOImage E := by
  have h := div_mem_stalkPointOImage E 2
    ⟨E.toProjective.coord 0 ^ 2, by
      simpa using SetLike.pow_mem_graded 2 (E.toProjective.coord_mem_grading 0)⟩
    ⟨formD E, formD_mem E⟩ (by rw [evalZero_formD]; exact one_ne_zero)
  have hx := genericX_ne_zero E
  rwa [show dehomogenization E (E.toProjective.coord 0 ^ 2) / dehomogenization E (formD E) =
      E.toAffine.genericX⁻¹ by
    rw [map_pow, dehomogenization_coord, dehomogenization_formD]
    field_simp
    rfl] at h

/-- Theorem (proved): `y / x² = XY / D` lies in the image of the local ring at `O`
(Silverman, II.1). -/
theorem genericY_div_mem_stalkPointOImage :
    E.toAffine.genericY / E.toAffine.genericX ^ 2 ∈ stalkPointOImage E := by
  have h := div_mem_stalkPointOImage E 2
    ⟨E.toProjective.coord 0 * E.toProjective.coord 1,
      SetLike.mul_mem_graded (E.toProjective.coord_mem_grading 0)
        (E.toProjective.coord_mem_grading 1)⟩
    ⟨formD E, formD_mem E⟩ (by rw [evalZero_formD]; exact one_ne_zero)
  have hx := genericX_ne_zero E
  rwa [show dehomogenization E (E.toProjective.coord 0 * E.toProjective.coord 1) /
      dehomogenization E (formD E) = E.toAffine.genericY / E.toAffine.genericX ^ 2 by
    rw [map_mul, dehomogenization_coord, dehomogenization_coord, dehomogenization_formD]
    field_simp
    rfl] at h

/-- Theorem (proved): elements of the image of the local ring at `O` are integral at infinity
(Silverman, II.1). -/
theorem infinityPlace_le_one_of_mem_stalkPointOImage {w : E.toAffine.FunctionField}
    (hw : w ∈ stalkPointOImage E) : Affine.infinityPlace E.toAffine w ≤ 1 := by
  obtain ⟨g, rfl⟩ := hw
  exact infinityPlace_le_one_of_stalk_pointO E g

/-- Theorem (proved): an element of the image with `v_∞ = 1` is the image of a unit, so its
inverse lies in the image (the local ring at `O` is dominated by the place at infinity)
(Silverman, II.1). -/
theorem inv_mem_stalkPointOImage {w : E.toAffine.FunctionField} (hw : w ∈ stalkPointOImage E)
    (h1 : Affine.infinityPlace E.toAffine w = 1) : w⁻¹ ∈ stalkPointOImage E := by
  obtain ⟨g, rfl⟩ := hw
  have hg : IsUnit g := by
    by_contra hg
    have hm : g ∈ IsLocalRing.maximalIdeal _ := (IsLocalRing.mem_maximalIdeal _).mpr hg
    exact absurd h1 (ne_of_lt (infinityPlace_lt_one_of_mem_maximalIdeal_pointO E g hm))
  obtain ⟨u, rfl⟩ := hg
  refine ⟨↑u⁻¹, eq_inv_of_mul_eq_one_left ?_⟩
  rw [← map_mul, Units.inv_mul, map_one]

/-- Theorem (proved): polynomials in `1 / x` lie in the image of the local ring at `O`
(Silverman, II.1). -/
theorem eval₂_inv_genericX_mem (P : Polynomial K) :
    P.eval₂ (algebraMap K E.toAffine.FunctionField) E.toAffine.genericX⁻¹ ∈
      stalkPointOImage E := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.eval₂_add]; exact add_mem hp hq
  | monomial n c =>
    rw [Polynomial.eval₂_monomial]
    exact mul_mem (algebraMap_mem_stalkPointOImage E c)
      (pow_mem (inv_genericX_mem_stalkPointOImage E) n)

/-- Theorem (proved): `v_∞(1 / x) = exp (-2) < 1` (Silverman, II.1). -/
theorem infinityPlace_inv_genericX_lt_one :
    Affine.infinityPlace E.toAffine E.toAffine.genericX⁻¹ < 1 := by
  rw [map_inv₀, infinityPlace_genericX, ← WithZero.exp_neg]
  exact exp_neg_lt_one (by norm_num : (0 : ℤ) < 2)

/-- Theorem (proved): a polynomial in `1 / x` with nonzero constant term is a unit at infinity
(Silverman, II.1). -/
theorem infinityPlace_eval₂_inv_genericX (P : Polynomial K) (hP : P.coeff 0 ≠ 0) :
    Affine.infinityPlace E.toAffine
      (P.eval₂ (algebraMap K E.toAffine.FunctionField) E.toAffine.genericX⁻¹) = 1 := by
  obtain ⟨Q, hQ⟩ : Polynomial.X ∣ P - Polynomial.C (P.coeff 0) :=
    Polynomial.X_dvd_iff.mpr (by simp)
  have hsplit : P.eval₂ (algebraMap K E.toAffine.FunctionField) E.toAffine.genericX⁻¹ =
      E.toAffine.genericX⁻¹ * Q.eval₂ (algebraMap K E.toAffine.FunctionField)
        E.toAffine.genericX⁻¹ + algebraMap K _ (P.coeff 0) := by
    have := congrArg (Polynomial.eval₂ (algebraMap K E.toAffine.FunctionField)
      E.toAffine.genericX⁻¹) hQ
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_C, Polynomial.eval₂_mul, Polynomial.eval₂_X] at this
    linear_combination this
  have hc : Affine.infinityPlace E.toAffine (algebraMap K E.toAffine.FunctionField (P.coeff 0)) =
      1 := Valuation.IsTrivialOn.eq_one (v := Affine.infinityPlace E.toAffine) _ hP
  rw [hsplit, Valuation.map_add_eq_of_lt_right, hc]
  rw [hc, map_mul]
  exact mul_lt_one_of_lt_of_le (infinityPlace_inv_genericX_lt_one E)
    (infinityPlace_le_one_of_mem_stalkPointOImage E (eval₂_inv_genericX_mem E Q))

/-- Theorem (proved): the polynomial algebra map is evaluation at `x` (Silverman, II.1). -/
theorem algebraMap_polynomial_eq_eval₂ (p : Polynomial K) :
    algebraMap (Polynomial K) E.toAffine.FunctionField p =
      p.eval₂ (algebraMap K E.toAffine.FunctionField) E.toAffine.genericX := by
  rw [Affine.algebraMap_eq_aeval_genericX, Polynomial.aeval_def]

/-- Theorem (proved): a rational function of `x` as a quotient of polynomials (Silverman, II.1). -/
theorem algebraMap_ratFunc_eq (A : RatFunc K) :
    algebraMap (RatFunc K) E.toAffine.FunctionField A =
      algebraMap (Polynomial K) E.toAffine.FunctionField A.num /
        algebraMap (Polynomial K) E.toAffine.FunctionField A.denom := by
  conv_lhs => rw [← RatFunc.num_div_denom A]
  rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

/-- Theorem (proved): `p(x) = (reflect N p)(1/x) · x^N` for `deg p ≤ N`
(`Polynomial.eval₂_reflect_mul_pow`) (Silverman, II.1). -/
theorem eval₂_genericX_eq_reflect (p : Polynomial K) {N : ℕ} (hN : p.natDegree ≤ N) :
    p.eval₂ (algebraMap K E.toAffine.FunctionField) E.toAffine.genericX =
      (Polynomial.reflect N p).eval₂ (algebraMap K E.toAffine.FunctionField)
        E.toAffine.genericX⁻¹ * E.toAffine.genericX ^ N := by
  let : Invertible E.toAffine.genericX := invertibleOfNonzero (genericX_ne_zero E)
  rw [← Polynomial.eval₂_reflect_mul_pow _ _ N p hN, invOf_eq_inv]

/-- Theorem (proved): the denominator of a rational function, reflected at its degree, has
constant term `1` (it is monic, `RatFunc.monic_denom`). -/
theorem coeff_zero_reflect_denom (A : RatFunc K) :
    (Polynomial.reflect A.denom.natDegree A.denom).coeff 0 = 1 := by
  rw [Polynomial.coeff_reflect, Polynomial.revAt_le (Nat.zero_le _), Nat.sub_zero]
  exact (RatFunc.monic_denom A).leadingCoeff

/-- Theorem (proved): a rational function of `x` of degree `≤ 0` is regular at `O`
(Silverman, II.1). -/
theorem algebraMap_ratFunc_mem_stalkPointOImage (A : RatFunc K)
    (hA : A = 0 ∨ A.intDegree ≤ 0) :
    algebraMap (RatFunc K) E.toAffine.FunctionField A ∈ stalkPointOImage E := by
  rcases hA with rfl | hA
  · rw [map_zero]; exact zero_mem _
  have hm : A.num.natDegree ≤ A.denom.natDegree := by
    rw [RatFunc.intDegree] at hA; omega
  have hx := genericX_ne_zero E
  rw [algebraMap_ratFunc_eq, algebraMap_polynomial_eq_eval₂, algebraMap_polynomial_eq_eval₂,
    eval₂_genericX_eq_reflect E _ hm, eval₂_genericX_eq_reflect E _ le_rfl,
    mul_div_mul_right _ _ (pow_ne_zero _ hx), div_eq_mul_inv]
  refine mul_mem (eval₂_inv_genericX_mem E _) (inv_mem_stalkPointOImage E
    (eval₂_inv_genericX_mem E _) (infinityPlace_eval₂_inv_genericX E _ ?_))
  rw [coeff_zero_reflect_denom]
  exact one_ne_zero

/-- Theorem (proved): `B(x) y` with `2 deg B + 3 ≤ 0` is regular at `O` (Silverman, II.1). -/
theorem algebraMap_ratFunc_mul_genericY_mem_stalkPointOImage (B : RatFunc K)
    (hB : B = 0 ∨ 2 * B.intDegree + 3 ≤ 0) :
    algebraMap (RatFunc K) E.toAffine.FunctionField B * E.toAffine.genericY ∈
      stalkPointOImage E := by
  rcases hB with rfl | hB
  · rw [map_zero, zero_mul]; exact zero_mem _
  have hm : B.num.natDegree + 2 ≤ B.denom.natDegree := by
    rw [RatFunc.intDegree] at hB; omega
  have hx := genericX_ne_zero E
  have hsplit : algebraMap (RatFunc K) E.toAffine.FunctionField B * E.toAffine.genericY =
      (Polynomial.reflect (B.denom.natDegree - 2) B.num).eval₂
          (algebraMap K E.toAffine.FunctionField) E.toAffine.genericX⁻¹ *
        ((Polynomial.reflect B.denom.natDegree B.denom).eval₂
          (algebraMap K E.toAffine.FunctionField) E.toAffine.genericX⁻¹)⁻¹ *
        (E.toAffine.genericY / E.toAffine.genericX ^ 2) := by
    rw [algebraMap_ratFunc_eq, algebraMap_polynomial_eq_eval₂, algebraMap_polynomial_eq_eval₂,
      eval₂_genericX_eq_reflect E _ (show B.num.natDegree ≤ B.denom.natDegree - 2 by omega),
      eval₂_genericX_eq_reflect E _ le_rfl]
    have hpow : E.toAffine.genericX ^ B.denom.natDegree =
        E.toAffine.genericX ^ (B.denom.natDegree - 2) * E.toAffine.genericX ^ 2 := by
      rw [← pow_add, Nat.sub_add_cancel (by omega)]
    rw [hpow]
    field_simp
  rw [hsplit]
  refine mul_mem (mul_mem (eval₂_inv_genericX_mem E _) (inv_mem_stalkPointOImage E
    (eval₂_inv_genericX_mem E _) (infinityPlace_eval₂_inv_genericX E _ ?_)))
    (genericY_div_mem_stalkPointOImage E)
  rw [coeff_zero_reflect_denom]
  exact one_ne_zero

/-- Theorem (proved, R4): **the valuation ring at infinity is the local ring at `O`**: a function
with `v_∞ ≤ 1` is regular at `O` (it is `A(x) + B(x) y` with `deg A ≤ 0` and `deg B ≤ -2`,
`WeierstrassCurve.Affine.val_add_mul_mk_Y_le_one_iff`, and `1/x`, `y/x²` are regular at `O`;
Silverman, II.1, III.1). -/
theorem mem_stalkPointOImage_of_infinityPlace_le_one {z : E.toAffine.FunctionField}
    (hz : Affine.infinityPlace E.toAffine z ≤ 1) : z ∈ stalkPointOImage E := by
  obtain ⟨A, B, rfl⟩ := Affine.exists_ratFunc_add_mul_mk_Y E.toAffine z
  rw [Affine.val_add_mul_mk_Y_le_one_iff _ (Affine.one_lt_infinityPlace_X E.toAffine)] at hz
  rw [← Affine.genericY_def]
  exact add_mem (algebraMap_ratFunc_mem_stalkPointOImage E A hz.1)
    (algebraMap_ratFunc_mul_genericY_mem_stalkPointOImage E B hz.2)

/-- Theorem (proved, R4): **`infinityPlace` is the valuation at `O`**: its valuation ring is
exactly the image of the local ring of the projective model at `O` (Silverman, II.1). -/
theorem infinityPlace_le_one_iff_mem_stalkPointOImage (z : E.toAffine.FunctionField) :
    Affine.infinityPlace E.toAffine z ≤ 1 ↔ z ∈ stalkPointOImage E :=
  ⟨mem_stalkPointOImage_of_infinityPlace_le_one E,
    infinityPlace_le_one_of_mem_stalkPointOImage E⟩

/-- Theorem (proved, R4): **the maximal ideal at infinity is the image of the maximal ideal at
`O`** (Silverman, II.1). -/
theorem infinityPlace_lt_one_iff_mem_maximalIdeal (z : E.toAffine.FunctionField) :
    Affine.infinityPlace E.toAffine z < 1 ↔
      ∃ g ∈ IsLocalRing.maximalIdeal ((Proj E.toProjective.grading).presheaf.stalk (pointO E)),
        stalkPointOToFunctionField E g = z := by
  refine ⟨fun hz => ?_, fun ⟨g, hg, hgz⟩ => hgz ▸
    infinityPlace_lt_one_of_mem_maximalIdeal_pointO E g hg⟩
  obtain ⟨g, rfl⟩ := mem_stalkPointOImage_of_infinityPlace_le_one E hz.le
  refine ⟨g, (IsLocalRing.mem_maximalIdeal _).mpr fun hg => ?_, rfl⟩
  obtain ⟨u, rfl⟩ := hg
  have h1 := infinityPlace_le_one_of_stalk_pointO E ↑u⁻¹
  have h2 : stalkPointOToFunctionField E ↑u * stalkPointOToFunctionField E ↑u⁻¹ = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have h3 := congrArg (Affine.infinityPlace E.toAffine) h2
  rw [map_mul, map_one] at h3
  change Affine.infinityPlace E.toAffine (stalkPointOToFunctionField E ↑u) < 1 at hz
  change Affine.infinityPlace E.toAffine (stalkPointOToFunctionField E ↑u⁻¹) ≤ 1 at h1
  exact absurd h3 (ne_of_lt (mul_lt_one_of_lt_of_le hz h1))

/-- Theorem (proved, R4): **the image of the local ring at `O` is the valuation subring of the
place at infinity** (Silverman, II.1). -/
theorem stalkPointOImage_eq_valuationSubring :
    stalkPointOImage E = (Affine.infinityPlace E.toAffine).valuationSubring.toSubring := by
  ext z
  rw [ValuationSubring.mem_toSubring, Valuation.mem_valuationSubring_iff]
  exact (infinityPlace_le_one_iff_mem_stalkPointOImage E z).symm

/-- Theorem (proved): the local ring at `O` embeds in the function field (the model is integral;
the `IsFractionRing` instance for stalks of integral schemes in `AlgebraicGeometry/FunctionField`)
(Silverman, II.1). -/
theorem stalkPointOToFunctionField_injective :
    Function.Injective (stalkPointOToFunctionField E) :=
  (projFunctionFieldEquiv E).injective.comp
    (IsFractionRing.injective ((Proj E.toProjective.grading).presheaf.stalk (pointO E))
      (Proj E.toProjective.grading).functionField)

/-- Definition (R4): **the local ring of the projective model at `O` is the valuation ring of
the place at infinity**, as a ring isomorphism onto `(infinityPlace E.toAffine).valuationSubring`
(Silverman, II.1). -/
def stalkPointOEquivValuationSubring :
    (Proj E.toProjective.grading).presheaf.stalk (pointO E) ≃+*
      (Affine.infinityPlace E.toAffine).valuationSubring :=
  RingEquiv.ofBijective
    ((stalkPointOToFunctionField E).codRestrict (Affine.infinityPlace E.toAffine).valuationSubring
      fun g => (Valuation.mem_valuationSubring_iff _ _).mpr
        (infinityPlace_le_one_of_stalk_pointO E g))
    ⟨fun g h hgh => stalkPointOToFunctionField_injective E (congrArg Subtype.val hgh),
      fun ⟨z, hz⟩ => by
        obtain ⟨g, hg⟩ := mem_stalkPointOImage_of_infinityPlace_le_one E
          ((Valuation.mem_valuationSubring_iff _ _).mp hz)
        exact ⟨g, Subtype.ext hg⟩⟩

/-- Theorem (proved): the isomorphism `stalkPointOEquivValuationSubring` is the germ map
(Silverman, II.1). -/
theorem coe_stalkPointOEquivValuationSubring
    (g : (Proj E.toProjective.grading).presheaf.stalk (pointO E)) :
    (stalkPointOEquivValuationSubring E g : E.toAffine.FunctionField) =
      stalkPointOToFunctionField E g :=
  rfl

/-- Theorem (proved, R4): **the local ring at `O` is a discrete valuation ring**: it is the
valuation ring of the place at infinity (`stalkPointOEquivValuationSubring`, Mathlib's
`Valuation.valuationSubring_isDiscreteValuationRing`), and `Z / Y` is a nonzero element of its
maximal ideal (Silverman, II.1). -/
theorem isDiscreteValuationRing_stalk_pointO :
    IsDiscreteValuationRing ((Proj E.toProjective.grading).presheaf.stalk (pointO E)) where
  toIsPrincipalIdealRing := IsPrincipalIdealRing.of_surjective
    (stalkPointOEquivValuationSubring E).symm.toRingHom
    (stalkPointOEquivValuationSubring E).symm.surjective
  toIsLocalRing := inferInstance
  not_a_field' := by
    intro h
    have hg := germ_sectionZOverY_mem_maximalIdeal E
    rw [h, Ideal.mem_bot] at hg
    have h1 := congrArg (stalkPointOToFunctionField E) hg
    rw [map_zero] at h1
    change projFunctionFieldEquiv E (algebraMap _ _ _) = 0 at h1
    rw [Scheme.algebraMap_germ_eq_germToFunctionField, projFunctionFieldEquiv_sectionZOverY]
      at h1
    exact inv_ne_zero (genericY_ne_zero E) h1

end LocalRingAtO
end ZInQ.Contrib.RC53Assist.S2aNumberField
