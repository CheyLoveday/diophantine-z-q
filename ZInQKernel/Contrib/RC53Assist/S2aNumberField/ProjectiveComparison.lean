import ZInQKernel.Contrib.RC53Assist.S2aNumberField.GenusOne
import ZInQKernel.Contrib.RC53Assist.S2aNumberField.ProjectiveModel
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.CoordinateRing

/-!
# The comparison with the projective Weierstrass model over a field of characteristic zero

The target is `Proj` of the homogeneous Weierstrass coordinate ring over a field `K`, with
structure morphism `Proj A ⟶ Spec A₀ ≅ Spec K` (`projectiveStructure`). Its function-field
identification `projFunctionFieldEquiv` is `K`-linear (`projFunctionFieldEquiv_algebraMap`):
on the chart `D₊(Z)` the pulled-back constants are the degree-zero constants.

Every local ring of a nonsingular projective Weierstrass model is a valuation ring: off
infinity the affine chart is a Dedekind domain, and at infinity the local ring is the valuation
ring of the place at infinity. With the extension theorem for proper regular curves, the
Riemann–Roch field identification at the identity extends to a `K`-isomorphism of a
one-dimensional proper smooth geometrically integral group curve with the projective model,
sending the identity to `O` (`abelian_projectiveWeierstrassModel`).

This is the general-field form of the module
`ZInQKernel.Contrib.RC53Assist.AbelianCurve.ProjectiveComparison`. Over `ℚ` the `K`-linearity
of the field identification was automatic; here it is proved from the structure morphism on
homogeneous charts (`toSpecZero_appTop_chart`, the statement and proof of
`AlgebraicGeometry.Proj.toSpecZero_appTop_res` from the Jacobian-Challenge library, which is
vendored in this repository under the Apache-2.0 license).

Mathematical locator: Silverman, *The Arithmetic of Elliptic Curves*, second edition,
Proposition III.3.1 and II.1–II.2; Milne, *Abelian varieties*, version 2.00 (2008), I,
Theorem 3.1, printed pp. 16–17.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.S2aNumberField

open AlgebraicGeometry CategoryTheory Limits HomogeneousLocalization
open ZInQ.Contrib.RC53Assist.AbelianCurve (functionFieldAlgebra fromFunctionField
  isomorphism_functionFieldMap)
open ZInQ.Contrib.RC53Assist.IsogenyScheme (functionFieldMap_algebraMap_stalk)

section Chart

universe u

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜] (f : A) {degree : ℕ}

/-- THEOREM (proved). On a homogeneous affine chart `D₊(f)`, `f` of positive degree, the
structure morphism `Proj A ⟶ Spec A₀` pulls back a degree-zero element to the chart section
of that element. Locator: Mathlib, `AlgebraicGeometry.Proj.awayι_toSpecZero` and
`Proj.basicOpenToSpec_app_top`; the same statement and proof as
`AlgebraicGeometry.Proj.toSpecZero_appTop_res` in the Jacobian-Challenge library
(Apache-2.0, vendored in this repository). -/
theorem toSpecZero_appTop_chart (hf : f ∈ 𝒜 degree) (degreePositive : 0 < degree) :
    (Scheme.ΓSpecIso (.of (𝒜 0))).inv ≫ (Proj.toSpecZero 𝒜).appTop ≫
        (Proj 𝒜).presheaf.map
          (homOfLE (le_top : Proj.basicOpen 𝒜 f ≤ ⊤)).op =
      CommRingCat.ofHom (fromZeroRingHom 𝒜 _) ≫ Proj.awayToSection 𝒜 f := by
  have diagram : (Proj.basicOpen 𝒜 f).ι ≫ Proj.toSpecZero 𝒜 =
      Proj.basicOpenToSpec 𝒜 f ≫ Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 _)) := by
    apply (cancel_epi (Proj.basicOpenIsoSpec 𝒜 f hf degreePositive).inv).mp
    calc
      (Proj.basicOpenIsoSpec 𝒜 f hf degreePositive).inv ≫
          (Proj.basicOpen 𝒜 f).ι ≫ Proj.toSpecZero 𝒜 =
          Proj.awayι 𝒜 f hf degreePositive ≫ Proj.toSpecZero 𝒜 := (Category.assoc _ _ _).symm
      _ = Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 _)) :=
        Proj.awayι_toSpecZero 𝒜 f hf degreePositive
      _ = (Proj.basicOpenIsoSpec 𝒜 f hf degreePositive).inv ≫ Proj.basicOpenToSpec 𝒜 f ≫
          Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 _)) := by
        rw [← Proj.basicOpenIsoSpec_hom 𝒜 f hf degreePositive, Iso.inv_hom_id_assoc]
  have restriction : (Proj.basicOpen 𝒜 f).ι.appTop ≫ (Proj.basicOpen 𝒜 f).topIso.hom =
      (Proj 𝒜).presheaf.map (homOfLE (le_top : Proj.basicOpen 𝒜 f ≤ ⊤)).op := by
    rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom, ← Functor.map_comp]
    rfl
  have sectionsDiagram := congrArg (fun morphism : (Proj.basicOpen 𝒜 f).toScheme ⟶
      Spec (.of (𝒜 0)) ↦ (Scheme.ΓSpecIso (.of (𝒜 0))).inv ≫ morphism.appTop ≫
        (Proj.basicOpen 𝒜 f).topIso.hom) diagram
  simpa only [Scheme.Hom.comp_appTop, Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality_assoc, Proj.basicOpenToSpec_app_top,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id, restriction] using sectionsDiagram

end Chart

variable {K : Type} [Field K]

/-- DEFINITION. The projective Weierstrass model as a scheme over `K`: the structure morphism
`Proj A ⟶ Spec A₀`, followed by the degree-zero-ring identification `A₀ ≅ K`.
Locator: `WeierstrassCurve.Projective.gradingZeroEquiv`; the rational version
`AbelianCurve.projectiveStructure`. -/
def projectiveStructure (E : WeierstrassCurve K) :
    Proj E.toProjective.grading ⟶ Spec (.of K) :=
  Proj.toSpecZero E.toProjective.grading ≫
    Spec.map E.toProjective.gradingZeroEquiv.toRingEquiv.toCommRingCatIso.hom

/-- THEOREM (proved). The projective model is proper over `K`.
Locator: `isProper_proj`; properness is preserved by the spectrum of the degree-zero-ring
isomorphism. -/
theorem projectiveStructure_proper (E : WeierstrassCurve K) :
    IsProper (projectiveStructure E) := by
  unfold projectiveStructure
  infer_instance

/-- THEOREM (proved). A constant pulled back to the projective model is the pulled-back
degree-zero constant. Locator: Mathlib, `Scheme.ΓSpecIso_inv_naturality` and
`Scheme.Hom.comp_appTop`. -/
theorem projectiveStructure_appTop (E : WeierstrassCurve K) (c : K) :
    (projectiveStructure E).appTop ((Scheme.ΓSpecIso (.of K)).inv c) =
      (Proj.toSpecZero E.toProjective.grading).appTop
        ((Scheme.ΓSpecIso (.of (E.toProjective.grading 0))).inv
          (E.toProjective.gradingZeroEquiv c)) := by
  have h := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
    E.toProjective.gradingZeroEquiv.toRingEquiv.toCommRingCatIso.hom) c
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  rw [projectiveStructure, Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply, ← h]
  rfl

/-- THEOREM (proved). On the chart `D₊(Z)` a pulled-back degree-zero constant is the chart
section of that constant. Locator: `toSpecZero_appTop_chart`. -/
theorem toSpecZero_appTop_zChart (E : WeierstrassCurve K) (a : E.toProjective.grading 0) :
    (Proj E.toProjective.grading).presheaf.map
      (homOfLE (le_top : Proj.basicOpen E.toProjective.grading (E.toProjective.coord 2) ≤ ⊤)).op
      ((Proj.toSpecZero E.toProjective.grading).appTop
        ((Scheme.ΓSpecIso (.of (E.toProjective.grading 0))).inv a)) =
      Proj.awayToSection E.toProjective.grading (E.toProjective.coord 2)
        (fromZeroRingHom E.toProjective.grading _ a) := by
  have h := ConcreteCategory.congr_hom (toSpecZero_appTop_chart E.toProjective.grading
    (E.toProjective.coord 2) (E.toProjective.coord_mem_grading 2) Nat.one_pos) a
  simpa using h

/-- THEOREM (proved). The constants of the function field of the projective model are germs of
chart sections of degree-zero constants. Locator: `projectiveStructure_appTop`,
`toSpecZero_appTop_zChart`; Mathlib, `TopCat.Presheaf.germ_res_apply`. -/
theorem algebraMap_projFunctionField (E : WeierstrassCurve K) (c : K) :
    letI := functionFieldAlgebra (projectiveStructure E)
    algebraMap K (Proj E.toProjective.grading).functionField c =
      (Proj E.toProjective.grading).germToFunctionField
        (Proj.basicOpen E.toProjective.grading (E.toProjective.coord 2))
        (Proj.awayToSection E.toProjective.grading (E.toProjective.coord 2)
          (fromZeroRingHom E.toProjective.grading _ (E.toProjective.gradingZeroEquiv c))) := by
  letI := functionFieldAlgebra (projectiveStructure E)
  letI : Nonempty (⊤ : (Proj E.toProjective.grading).Opens) :=
    ⟨⟨genericPoint _, trivial⟩⟩
  rw [RingHom.algebraMap_toAlgebra, CommRingCat.hom_comp, CommRingCat.hom_comp,
    RingHom.comp_apply, RingHom.comp_apply, projectiveStructure_appTop,
    ← toSpecZero_appTop_zChart]
  exact ((Proj E.toProjective.grading).presheaf.germ_res_apply (homOfLE le_top) _ _ _).symm

/-- THEOREM (proved). The function-field identification of the projective model is linear over
the constants. Locator: `algebraMap_projFunctionField`; `projFunctionFieldEquiv_germ`,
`atPrimeEquivFunctionField_mapId` and `zChartToFunctionField_zChartConst`. -/
theorem projFunctionFieldEquiv_algebraMap (E : WeierstrassCurve K) (c : K) :
    letI := functionFieldAlgebra (projectiveStructure E)
    projFunctionFieldEquiv E (algebraMap K (Proj E.toProjective.grading).functionField c) =
      algebraMap K E.toAffine.FunctionField c := by
  letI := functionFieldAlgebra (projectiveStructure E)
  have hconst : fromZeroRingHom E.toProjective.grading _ (E.toProjective.gradingZeroEquiv c) =
      zChartConst E c := by
    change fromZeroRingHom E.toProjective.grading _ (E.toProjective.gradingZeroEquiv c) =
      fromZeroRingHom E.toProjective.grading _ (algebraMap K (E.toProjective.grading 0) c)
    rw [WeierstrassCurve.Projective.gradingZeroEquiv_apply]
  rw [algebraMap_projFunctionField, projFunctionFieldEquiv_germ, hconst]
  exact (atPrimeEquivFunctionField_mapId (genericPoint_proj_ideal E) (zChartConst E c)).trans
    (zChartToFunctionField_zChartConst E c)

/-- THEOREM (proved). Every point other than infinity lies on the affine `Z ≠ 0` chart.
Locator: `coord_zero_mem_of_coord_two_mem` and `eq_pointO_of_coord_mem`. -/
theorem projectivePoint_mem_zChart (E : WeierstrassCurve K) (P : Proj E.toProjective.grading)
    (hP : P ≠ pointO E) :
    P ∈ Proj.basicOpen E.toProjective.grading (E.toProjective.coord 2) := by
  rw [Proj.mem_basicOpen]
  intro hZ
  exact hP (eq_pointO_of_coord_mem E P (coord_zero_mem_of_coord_two_mem E P hZ) hZ)

/-- THEOREM (proved). Every local ring of a nonsingular projective Weierstrass model is a
valuation ring. Locator: `affineEquivZChart` and `isDiscreteValuationRing_stalk_pointO`;
Tau Ceti, `WeierstrassCurve.Affine.isIntegrallyClosed_coordinateRing` and
`isDedekindDomain_coordinateRing_of_isIntegrallyClosed`. -/
theorem projective_valuation_stalk (E : WeierstrassCurve K) [E.IsElliptic]
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

/-- THEOREM (proved). A `K`-linear function-field identification whose first coordinate has a
pole of order two at the identity transports the identity place to the place at infinity.
Locator: `WeierstrassCurve.Affine.isEquiv_infinityPlace_of_one_lt`, the uniqueness of the place
at infinity; `TauCeti.Place.valuation_eq_exp_neg_ord`. -/
theorem identityPlace_transport_infinity [CharZero K] (G : Over (Spec (.of K))) [GrpObj G]
    [IsIntegral G.left] [Smooth G.hom] (hdim : topologicalKrullDim G.left = 1)
    (E : WeierstrassCurve K) (e : E.toAffine.FunctionField ≃+* G.left.functionField)
    (he : letI := functionFieldAlgebra G.hom
      ∀ c : K, e (algebraMap K E.toAffine.FunctionField c) = algebraMap K G.left.functionField c)
    (hx : letI := functionFieldAlgebra G.hom
      (smoothIdentityPlace G hdim).ord (e E.toAffine.genericX) = -2) :
    letI := functionFieldAlgebra G.hom
    ((smoothIdentityPlace G hdim).valuation.comap e.toRingHom).IsEquiv
      (WeierstrassCurve.Affine.infinityPlace E.toAffine) := by
  letI := functionFieldAlgebra G.hom
  let P := smoothIdentityPlace G hdim
  let v := P.valuation.comap e.toRingHom
  have hscalar : e.toRingHom.comp (algebraMap K E.toAffine.FunctionField) =
      algebraMap K G.left.functionField := RingHom.ext he
  haveI : v.IsTrivialOn K := ⟨fun c hc => by
    change P.valuation ((e.toRingHom.comp (algebraMap K E.toAffine.FunctionField)) c) = 1
    rw [RingHom.congr_fun hscalar c]
    exact Valuation.IsTrivialOn.eq_one (v := P.valuation) c hc⟩
  have hx₀ : e E.toAffine.genericX ≠ 0 :=
    (map_ne_zero_iff e e.injective).mpr
      (WeierstrassCurve.Affine.transcendental_genericX E.toAffine).ne_zero
  have hlt : 1 < v (algebraMap (Polynomial K) E.toAffine.FunctionField Polynomial.X) := by
    rw [← WeierstrassCurve.Affine.genericX_eq_algebraMap]
    change 1 < P.valuation (e E.toAffine.genericX)
    rw [P.valuation_eq_exp_neg_ord hx₀, hx]
    rw [← WithZero.exp_zero (M := ℤ), WithZero.exp_lt_exp]
    norm_num
  exact WeierstrassCurve.Affine.isEquiv_infinityPlace_of_one_lt v hlt

/-- THEOREM (proved). The scheme comparison based on the identity's Weierstrass coordinates
sends the identity point to the point at infinity.
Locator: `IsogenyScheme.functionFieldMap_algebraMap_stalk` and `eq_pointO_of_dominated`;
`identityPlace_integers`. -/
theorem comparison_sends_identity [CharZero K] (G : Over (Spec (.of K))) [GrpObj G]
    [IsIntegral G.left] [Smooth G.hom] (hdim : topologicalKrullDim G.left = 1)
    (E : WeierstrassCurve K) (e : E.toAffine.FunctionField ≃+* G.left.functionField)
    (he : letI := functionFieldAlgebra G.hom
      ∀ c : K, e (algebraMap K E.toAffine.FunctionField c) = algebraMap K G.left.functionField c)
    (i : G.left ≅ Proj E.toProjective.grading)
    (hi : i.hom.functionFieldMap.hom = e.toRingHom.comp (projFunctionFieldEquiv E).toRingHom)
    (hx : letI := functionFieldAlgebra G.hom
      (smoothIdentityPlace G hdim).ord (e E.toAffine.genericX) = -2) :
    i.hom (identityPoint G) = pointO E := by
  letI := functionFieldAlgebra G.hom
  let P := smoothIdentityPlace G hdim
  have hv := identityPlace_transport_infinity G hdim E e he hx
  apply eq_pointO_of_dominated E (i.hom (identityPoint G))
  intro z
  have hz : P.valuation (e (projFunctionFieldEquiv E
      (algebraMap _ (Proj E.toProjective.grading).functionField z))) ≤ 1 := by
    change P.valuation ((e.toRingHom.comp (projFunctionFieldEquiv E).toRingHom)
      (algebraMap _ (Proj E.toProjective.grading).functionField z)) ≤ 1
    rw [← hi, functionFieldMap_algebraMap_stalk i.hom (identityPoint G) z]
    have hm : algebraMap (G.left.presheaf.stalk (identityPoint G)) G.left.functionField
        ((i.hom.stalkMap (identityPoint G)).hom z) ∈ P.integers := by
      haveI := identity_stalk_discreteValuationRing G hdim
      change _ ∈ (smoothIdentityPlace G hdim).integers.toSubring
      rw [smoothIdentityPlace, identityPlace_integers]
      exact Subring.mem_map.mpr ⟨(i.hom.stalkMap (identityPoint G)).hom z, trivial, rfl⟩
    exact P.mem_integers_iff.mp hm
  exact (Valuation.isEquiv_iff_val_le_one.mp hv).mp hz

/-- THEOREM (proved, pointed scheme-level S2a over a field of characteristic zero). A
one-dimensional proper smooth geometrically integral group scheme over a field `K` of
characteristic zero is isomorphic over `K` to the projective model of a nonsingular
Weierstrass equation over `K`. The isomorphism induces the specified function-field
identification produced by Riemann–Roch and sends the identity to the point at infinity.
Locators: Silverman III.3.1 via `abelian_weierstrassCoordinates`;
`projFunctionFieldEquiv_algebraMap`; `isomorphism_of_functionField_equiv`. -/
theorem abelian_projectiveWeierstrassModel [CharZero K] (G : Over (Spec (.of K))) [GrpObj G]
    [IsIntegral G.left] [Smooth G.hom] [IsProper G.hom] [GeometricallyIntegral G.hom]
    (hdim : topologicalKrullDim G.left = 1) :
    letI := functionFieldAlgebra G.hom
    ∃ E : WeierstrassCurve K, E.IsElliptic ∧
      ∃ (e : E.toAffine.FunctionField ≃ₐ[K] G.left.functionField)
        (i : G.left ≅ Proj E.toProjective.grading),
        i.hom ≫ projectiveStructure E = G.hom ∧
        i.hom.functionFieldMap.hom =
          e.toRingHom.comp (projFunctionFieldEquiv E).toRingHom ∧
        i.hom (identityPoint G) = pointO E := by
  letI := functionFieldAlgebra G.hom
  obtain ⟨E, hE, e, hx, _, _, _⟩ := abelian_weierstrassCoordinates G hdim
  haveI : E.IsElliptic := hE
  haveI := projectiveStructure_proper E
  have he : ∀ c : K, e.toRingEquiv (algebraMap K E.toAffine.FunctionField c) =
      algebraMap K G.left.functionField c := fun c => e.commutes c
  let er := (projFunctionFieldEquiv E).trans e.toRingEquiv
  have her : letI := functionFieldAlgebra (projectiveStructure E)
      ∀ c : K, er (algebraMap K (Proj E.toProjective.grading).functionField c) =
        algebraMap K G.left.functionField c := by
    letI := functionFieldAlgebra (projectiveStructure E)
    intro c
    change e.toRingEquiv (projFunctionFieldEquiv E (algebraMap K _ c)) = _
    rw [projFunctionFieldEquiv_algebraMap E c]
    exact he c
  obtain ⟨i, hi, hη⟩ := isomorphism_of_functionField_equiv G.hom (projectiveStructure E)
    (smooth_curve_valuation_stalk G.hom hdim) (projective_valuation_stalk E) er her
  have hfield : i.hom.functionFieldMap.hom =
      e.toRingHom.comp (projFunctionFieldEquiv E).toRingHom :=
    congrArg CommRingCat.Hom.hom (isomorphism_functionFieldMap er i hη)
  exact ⟨E, hE, e, i, hi, hfield,
    comparison_sends_identity G hdim E e.toRingEquiv he i hfield hx⟩

end ZInQ.Contrib.RC53Assist.S2aNumberField
