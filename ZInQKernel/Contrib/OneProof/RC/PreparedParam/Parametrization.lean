import ZInQKernel.Contrib.OneProof.RC.PreparedParam.Prints
import ZInQKernel.Contrib.RC53Assist.IsogenyScheme.ProjectiveModel
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Eval

/-! Evaluation of the rational parametrization used in tex 1781–1788 and
2915–2917. The scheme and coordinate proofs are on-the-spot (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassCurve
  ZInQ.Contrib.RC53Assist.IsogenyScheme ZInQ.Contrib.CloudB3RC53.CST

namespace ZInQ.Manuscript.RC.PreparedParam

/-- The structure morphism of the actual projective Weierstrass model. -/
def projectiveOverQ (E : WeierstrassCurve ℚ) :
    Proj E.toProjective.grading ⟶ Spec (.of ℚ) :=
  Proj.toSpecZero E.toProjective.grading ≫
    Spec.map E.toProjective.gradingZeroEquiv.toRingEquiv.toCommRingCatIso.hom

private abbrev affineOpen (E : WeierstrassCurve ℚ) :=
  Proj.basicOpen E.toProjective.grading (E.toProjective.coord 2)

private theorem mem_affineOpen_of_ne_pointO {E : WeierstrassCurve ℚ}
    {P : Proj E.toProjective.grading} (hP : P ≠ pointO E) : P ∈ affineOpen E := by
  rw [affineOpen, Proj.mem_basicOpen]
  intro hZ
  exact hP (eq_pointO_of_coord_mem E P (coord_zero_mem_of_coord_two_mem E P hZ) hZ)

private def affineSpec (E : WeierstrassCurve ℚ) :
    (affineOpen E).toScheme ⟶ Spec (.of E.toAffine.CoordinateRing) :=
  (Proj.basicOpenIsoSpec E.toProjective.grading (E.toProjective.coord 2)
    (E.toProjective.coord_mem_grading 2) (by norm_num)).hom ≫
    Spec.map (affineEquivZChart E).toCommRingCatIso.hom

private theorem range_le_affineOpen {E : WeierstrassCurve ℚ} {F : Type} [Field F]
    (u : Spec (.of F) ⟶ Proj E.toProjective.grading)
    (h : u default ∈ affineOpen E) : Set.range u ⊆ Set.range (affineOpen E).ι := by
  rintro _ ⟨v, rfl⟩
  rw [Subsingleton.elim v (default : Spec (.of F))]
  exact ⟨⟨u default, h⟩, rfl⟩

private def affineChartPoint {E : WeierstrassCurve ℚ} {F : Type} [Field F]
    (u : Spec (.of F) ⟶ Proj E.toProjective.grading)
    (h : u default ∈ affineOpen E) : Spec (.of F) ⟶ Spec (.of E.toAffine.CoordinateRing) :=
  IsOpenImmersion.lift (affineOpen E).ι u (range_le_affineOpen u h) ≫ affineSpec E

private def specToAlgHom {A F : Type} [CommRing A] [Algebra ℚ A] [Field F] [Algebra ℚ F]
    (u : Spec (.of F) ⟶ Spec (.of A)) : A →ₐ[ℚ] F where
  __ := ((Scheme.ΓSpecIso (.of A)).inv ≫ u.appTop ≫ (Scheme.ΓSpecIso (.of F)).hom).hom
  commutes' r := DFunLike.congr_fun
    (Subsingleton.elim
      (((Scheme.ΓSpecIso (.of A)).inv ≫ u.appTop ≫ (Scheme.ΓSpecIso (.of F)).hom).hom.comp
        (algebraMap ℚ A)) (algebraMap ℚ F)) r

private theorem specToAlgHom_map {A F G : Type} [CommRing A] [Algebra ℚ A]
    [Field F] [Algebra ℚ F] [Field G] [Algebra ℚ G]
    (ι : F →ₐ[ℚ] G) (u : Spec (.of F) ⟶ Spec (.of A)) :
    specToAlgHom (Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ u) =
      ι.comp (specToAlgHom u) := by
  apply AlgHom.toRingHom_injective
  have h :
      (Scheme.ΓSpecIso (.of A)).inv ≫ (Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ u).appTop ≫
        (Scheme.ΓSpecIso (.of G)).hom =
      ((Scheme.ΓSpecIso (.of A)).inv ≫ u.appTop ≫ (Scheme.ΓSpecIso (.of F)).hom) ≫
        CommRingCat.ofHom ι.toRingHom := by
    simp only [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality]
  exact congrArg CommRingCat.Hom.hom h

open Classical in
/-- Evaluate a point of the projective model in the point type used by CST.
On `Z ≠ 0` this evaluates the two functions of the affine coordinate ring.
The complement is the single projective point at infinity. -/
def projectiveValue {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {F : Type} [Field F] [Algebra ℚ F] (u : Spec (.of F) ⟶ Proj E.toProjective.grading) :
    (E.baseChange F).toAffine.Point :=
  if h : u default = pointO E then 0 else
    let a := specToAlgHom (affineChartPoint u (mem_affineOpen_of_ne_pointO h))
    .some (a (AdjoinRoot.of E.toAffine.polynomial Polynomial.X))
      (a (AdjoinRoot.root E.toAffine.polynomial))
      (Affine.equation_iff_nonsingular.mp (Affine.CoordinateRing.equation_of_algHom a))

open Classical in
/-- Scheme evaluation commutes with extension of the field, on both
the affine chart and its complement. -/
theorem projectiveValue_map {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {F G : Type} [Field F] [Algebra ℚ F] [Field G] [Algebra ℚ G]
    (ι : F →ₐ[ℚ] G) (u : Spec (.of F) ⟶ Proj E.toProjective.grading) :
    Affine.Point.map (W' := E.toAffine) ι (projectiveValue u) =
      projectiveValue (Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ u) := by
  classical
  have hbase : (Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ u) default = u default := by
    rw [Scheme.Hom.comp_apply, Subsingleton.elim (Spec.map _ default) (default : Spec (.of F))]
  by_cases h : u default = pointO E
  · have hh : (Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ u) default = pointO E :=
      hbase ▸ h
    simp only [projectiveValue, dite_eq_left h, dite_eq_left hh, map_zero]
  · have hh : (Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ u) default ≠ pointO E :=
      hbase ▸ h
    have ha : affineChartPoint (Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ u)
        (mem_affineOpen_of_ne_pointO hh) = Spec.map (CommRingCat.ofHom ι.toRingHom) ≫
          affineChartPoint u (mem_affineOpen_of_ne_pointO h) := by
      unfold affineChartPoint
      rw [← IsOpenImmersion.comp_lift, Category.assoc]
    simp only [projectiveValue, dite_eq_right h, dite_eq_right hh, Affine.Point.map_some, ha,
      specToAlgHom_map, AlgHom.comp_apply]

/-- Missing compatibility at the fixed scale (tex 1781–1788, 2836–2838,
2915–2917, 9347–9350). A morphism over `ℚ` to the projective
Weierstrass model must give the specified `phiAn` on the upper half
plane. No CM point, class field, or choice of a point of `E(H)` is involved.
This is an input for the reduction, not a new print. -/
def AlgebraicParametrizationAtScale (E : WeierstrassCurve ℚ) [E.IsElliptic]
    [NeZero (newformLevel E)] (X : X0Model (newformLevel E))
    (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2)
    (Lat : PeriodPair) (κ : ℂ) : Prop :=
  ∃ (π : X.X ⟶ Proj E.toProjective.grading) (hπ : π ≫ projectiveOverQ E = X.overQ),
    IsDominant π ∧ ∀ τ : UpperHalfPlane,
      projectiveValue ((X.complexPoint τ).comp π hπ).val = phiAn E f Lat κ τ


end ZInQ.Manuscript.RC.PreparedParam
