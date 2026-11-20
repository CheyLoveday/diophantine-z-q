import ZInQKernel.Contrib.RC53Assist.AbelianCurve.WeierstrassReduction
import ZInQKernel.Contrib.RC53Assist.AbelianCurve.BirationalComparison
import ZInQKernel.Contrib.RC53Assist.IsogenyScheme.ProjectiveModel
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.CoordinateRing

/-!
# The comparison with the actual projective Weierstrass model

The target is `Proj` of the homogeneous Weierstrass coordinate ring in the
existing projective-model identification. Its structure morphism is taken
over the rational numbers, using the proved degree-zero-ring equivalence.

Every local ring of a nonsingular projective Weierstrass model is a valuation
ring: off infinity the affine chart is a Dedekind domain, and at infinity the
existing projective-model proof supplies the discrete valuation ring. Thus
no smooth-proper-curve isomorphism theorem or projective-model normality is
assumed as a new input.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.AbelianCurve

open AlgebraicGeometry CategoryTheory Limits
open ZInQ.Contrib.RC53Assist.IsogenyScheme

/-- DEFINITION. The actual projective Weierstrass model over the rational numbers, not merely
an abstract scheme with isomorphic function field.
Locator: `ZInQKernel/Contrib/RC53Assist/IsogenyScheme/ProjectiveModel.lean`, `projModel`;
`WeierstrassCurve.Projective.gradingZeroEquiv`. -/
def projectiveStructure (E : WeierstrassCurve ℚ) :
    Proj E.toProjective.grading ⟶ Spec (.of ℚ) :=
  Proj.toSpecZero E.toProjective.grading ≫
    Spec.map E.toProjective.gradingZeroEquiv.toRingEquiv.toCommRingCatIso.hom

/-- THEOREM (proved). The actual projective model is proper over the rational numbers.
Locator: the existing `IsogenyScheme.isProper_proj`; properness is preserved by the spectrum
of the degree-zero-ring isomorphism. -/
theorem projectiveStructure_proper (E : WeierstrassCurve ℚ) : IsProper (projectiveStructure E) := by
  unfold projectiveStructure
  infer_instance

/-- THEOREM (proved). Every point other than infinity lies on the affine `Z ≠ 0` chart.
Locator: the existing `IsogenyScheme.coord_zero_mem_of_coord_two_mem` and
`IsogenyScheme.eq_pointO_of_coord_mem`, from the homogeneous Weierstrass equation. -/
theorem projectivePoint_mem_zChart (E : WeierstrassCurve ℚ) (P : Proj E.toProjective.grading)
    (hP : P ≠ pointO E) : P ∈ Proj.basicOpen E.toProjective.grading (E.toProjective.coord 2) := by
  rw [Proj.mem_basicOpen]
  intro hZ
  exact hP (eq_pointO_of_coord_mem E P (coord_zero_mem_of_coord_two_mem E P hZ) hZ)

/-- THEOREM (proved). Every local ring of a nonsingular projective Weierstrass model is a
valuation ring. Locator: the existing `IsogenyScheme.affineEquivZChart` and
`IsogenyScheme.isDiscreteValuationRing_stalk_pointO`; Tau Ceti,
`WeierstrassCurve.Affine.isIntegrallyClosed_coordinateRing` and
`isDedekindDomain_coordinateRing_of_isIntegrallyClosed`. -/
theorem projective_valuation_stalk (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : Proj E.toProjective.grading) :
    ValuationRing ((Proj E.toProjective.grading).presheaf.stalk P) := by
  by_cases hP : P = pointO E
  · subst P
    haveI := isDiscreteValuationRing_stalk_pointO E
    infer_instance
  · haveI : IsIntegrallyClosed E.toAffine.CoordinateRing :=
      WeierstrassCurve.Affine.isIntegrallyClosed_coordinateRing E.toAffine
    haveI : IsDedekindDomain E.toAffine.CoordinateRing :=
      WeierstrassCurve.Affine.isDedekindDomain_coordinateRing_of_isIntegrallyClosed E.toAffine
    let U := Proj.basicOpen E.toProjective.grading (E.toProjective.coord 2)
    have hPU : P ∈ U := projectivePoint_mem_zChart E P hP
    let p : U := ⟨P, hPU⟩
    let er := (affineEquivZChart E).toCommRingCatIso
    let es : Spec (.of (ZChart E)) ≅ Spec (.of E.toAffine.CoordinateRing) :=
      { hom := Spec.map er.hom
        inv := Spec.map er.inv
        hom_inv_id := by rw [← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
        inv_hom_id := by rw [← Spec.map_comp, Iso.hom_inv_id, Spec.map_id] }
    let e : U.toScheme ≅ Spec (.of E.toAffine.CoordinateRing) :=
      Proj.basicOpenIsoSpec E.toProjective.grading (E.toProjective.coord 2)
        (E.toProjective.coord_mem_grading 2) (by norm_num) ≪≫ es
    let e₁ := asIso (U.ι.stalkMap p)
    let e₂ := asIso (e.hom.stalkMap p)
    let e₃ := Spec.stalkIso (.of E.toAffine.CoordinateRing) (e.hom p)
    let eR : (Proj E.toProjective.grading).presheaf.stalk P ≃+*
        Localization.AtPrime (e.hom p).asIdeal :=
      (e₁ ≪≫ e₂.symm ≪≫ e₃).commRingCatIsoToRingEquiv
    haveI : IsPrincipalIdealRing ((Proj E.toProjective.grading).presheaf.stalk P) :=
      IsPrincipalIdealRing.of_surjective eR.symm.toRingHom eR.symm.surjective
    infer_instance

/-- THEOREM (proved). A function-field identification with first coordinate having a pole at
the identity transports the identity place to the place at infinity.
Locator: `WeierstrassCurve.Affine.isEquiv_infinityPlace_of_one_lt`, the uniqueness of the
place at infinity; `TauCeti.Place.valuation_eq_exp_neg_ord`. -/
theorem identityPlace_transport_infinity (G : Over (Spec (.of ℚ))) [CategoryTheory.GrpObj G]
    [IsIntegral G.left] [Smooth G.hom] (hdim : topologicalKrullDim G.left = 1)
    (E : WeierstrassCurve ℚ) (e : E.toAffine.FunctionField ≃+* G.left.functionField)
    (hx : letI := functionFieldAlgebra G.hom
      (smoothIdentityPlace G hdim).ord (e E.toAffine.genericX) = -2) :
    letI := functionFieldAlgebra G.hom
    ((smoothIdentityPlace G hdim).valuation.comap e.toRingHom).IsEquiv
      (WeierstrassCurve.Affine.infinityPlace E.toAffine) := by
  letI := functionFieldAlgebra G.hom
  let P := smoothIdentityPlace G hdim
  let v := P.valuation.comap e.toRingHom
  have hscalar : e.toRingHom.comp (algebraMap ℚ E.toAffine.FunctionField) =
      algebraMap ℚ G.left.functionField := RingHom.ext_rat _ _
  haveI : v.IsTrivialOn ℚ := ⟨fun c hc => by
    change P.valuation ((e.toRingHom.comp (algebraMap ℚ E.toAffine.FunctionField)) c) = 1
    rw [RingHom.congr_fun hscalar c]
    exact Valuation.IsTrivialOn.eq_one (v := P.valuation) c hc⟩
  have hx₀ : e E.toAffine.genericX ≠ 0 :=
    (map_ne_zero_iff e e.injective).mpr
      (WeierstrassCurve.Affine.transcendental_genericX E.toAffine).ne_zero
  have hlt : 1 < v (algebraMap (Polynomial ℚ) E.toAffine.FunctionField Polynomial.X) := by
    rw [← WeierstrassCurve.Affine.genericX_eq_algebraMap]
    change 1 < P.valuation (e E.toAffine.genericX)
    rw [P.valuation_eq_exp_neg_ord hx₀, hx]
    rw [← WithZero.exp_zero (M := ℤ), WithZero.exp_lt_exp]
    norm_num
  exact WeierstrassCurve.Affine.isEquiv_infinityPlace_of_one_lt v hlt

/-- THEOREM (proved). The scheme comparison based on the identity's Weierstrass coordinates
sends the actual identity point to the actual projective point at infinity.
Locator: the existing `IsogenyScheme.functionFieldMap_algebraMap_stalk` and
`IsogenyScheme.eq_pointO_of_dominated`; `identityPlace_integers` above. -/
theorem comparison_sends_identity (G : Over (Spec (.of ℚ))) [CategoryTheory.GrpObj G]
    [IsIntegral G.left] [Smooth G.hom] (hdim : topologicalKrullDim G.left = 1)
    (E : WeierstrassCurve ℚ) (e : E.toAffine.FunctionField ≃+* G.left.functionField)
    (i : G.left ≅ Proj E.toProjective.grading)
    (he : i.hom.functionFieldMap.hom = e.toRingHom.comp (projFunctionFieldEquiv E).toRingHom)
    (hx : letI := functionFieldAlgebra G.hom
      (smoothIdentityPlace G hdim).ord (e E.toAffine.genericX) = -2) :
    i.hom (identityPoint G) = pointO E := by
  letI := functionFieldAlgebra G.hom
  let P := smoothIdentityPlace G hdim
  have hv := identityPlace_transport_infinity G hdim E e hx
  apply eq_pointO_of_dominated E (i.hom (identityPoint G))
  intro z
  have hz : P.valuation (e (projFunctionFieldEquiv E
      (algebraMap _ (Proj E.toProjective.grading).functionField z))) ≤ 1 := by
    change P.valuation ((e.toRingHom.comp (projFunctionFieldEquiv E).toRingHom)
      (algebraMap _ (Proj E.toProjective.grading).functionField z)) ≤ 1
    rw [← he, functionFieldMap_algebraMap_stalk i.hom (identityPoint G) z]
    have hm : algebraMap (G.left.presheaf.stalk (identityPoint G)) G.left.functionField
        ((i.hom.stalkMap (identityPoint G)).hom z) ∈ P.integers := by
      haveI := identity_stalk_discreteValuationRing G hdim
      change _ ∈ (smoothIdentityPlace G hdim).integers.toSubring
      rw [smoothIdentityPlace, identityPlace_integers]
      exact Subring.mem_map.mpr ⟨(i.hom.stalkMap (identityPoint G)).hom z, trivial, rfl⟩
    exact P.mem_integers_iff.mp hm
  exact (Valuation.isEquiv_iff_val_le_one.mp hv).mp hz

/-- THEOREM (proved reduction, scheme-level S2a). From the two named differential inputs,
the actual one-dimensional abelian group scheme is isomorphic over the rationals to the
actual projective model of a nonsingular Weierstrass equation. The isomorphism induces the
specified function-field identification produced by Riemann–Roch and sends the identity to
infinity.
Locators: Silverman III.3.1 via the proved S2b; the existing
`IsogenyScheme.projFunctionFieldEquiv`; `isomorphism_of_functionField_equiv` above. -/
theorem abelian_projectiveWeierstrassModel
    (hT : InvariantDifferentialTrivialization) (hC : RegularDifferentialComparison)
    (G : Over (Spec (.of ℚ))) [CategoryTheory.GrpObj G] [IsIntegral G.left]
    [Smooth G.hom] [IsProper G.hom] [GeometricallyIntegral G.hom]
    (hdim : topologicalKrullDim G.left = 1) :
    letI := functionFieldAlgebra G.hom
    ∃ E : WeierstrassCurve ℚ, E.IsElliptic ∧
      ∃ (e : E.toAffine.FunctionField ≃ₐ[ℚ] G.left.functionField)
        (i : G.left ≅ Proj E.toProjective.grading),
        i.hom ≫ projectiveStructure E = G.hom ∧
        i.hom.functionFieldMap.hom =
          e.toRingHom.comp (projFunctionFieldEquiv E).toRingHom ∧
        i.hom (identityPoint G) = pointO E := by
  letI := functionFieldAlgebra G.hom
  obtain ⟨E, hE, e, hx, _, _, _⟩ := abelian_weierstrassCoordinates hT hC G hdim
  haveI : E.IsElliptic := hE
  haveI := projectiveStructure_proper E
  let er := (projFunctionFieldEquiv E).trans e.toRingEquiv
  obtain ⟨i, hi, hη⟩ := isomorphism_of_functionField_equiv G.hom (projectiveStructure E)
    (smooth_curve_valuation_stalk G.hom hdim) (projective_valuation_stalk E) er
  have hfield : i.hom.functionFieldMap.hom =
      e.toRingHom.comp (projFunctionFieldEquiv E).toRingHom :=
    congrArg CommRingCat.Hom.hom (isomorphism_functionFieldMap er i hη)
  exact ⟨E, hE, e, i, hi, hfield, comparison_sends_identity G hdim E e.toRingEquiv i hfield hx⟩

end ZInQ.Contrib.RC53Assist.AbelianCurve
