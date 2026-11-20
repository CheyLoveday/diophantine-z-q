import ZInQKernel.Contrib.OneProof.RC.X0Model.Chart

/-! The first coordinate of the normalized chart (tex 2915–2919, on the
spot, provenance (c)). -/

noncomputable section

open AlgebraicGeometry CategoryTheory Filter ModularCurve ShimuraPointDict
open ZInQ.Contrib.CloudW07JacobiansCurves
open scoped Topology

namespace ZInQ.Manuscript.RC.X0Model2

attribute [local instance] X0Model.jAlgebra X0Model.finite_jAlgebra

/-- The map to the projective j-line used to normalize the model. -/
abbrev jProjection (N : ℕ) [NeZero N] : X0Model.curve N ⟶ NormalModel.P :=
  NormalModel.ν (modularFunctionField N)

private abbrev jAffineChart := NormalModel.chart 0

private abbrev jCoordinateSection : Γ(NormalModel.P, jAffineChart) :=
  ProjectiveLine.polyEquivChart ℚ 0 Polynomial.X

private theorem jAffine_ne (N : ℕ) [NeZero N] :
    Nonempty (jProjection N ⁻¹ᵁ jAffineChart) := by
  obtain ⟨y, hy⟩ := (inferInstance : Nonempty jAffineChart)
  obtain ⟨x, hx⟩ := (jProjection N).surjective y
  exact ⟨⟨x, by rw [Scheme.Hom.mem_preimage, hx]; exact hy⟩⟩

attribute [local instance] jAffine_ne

set_option backward.isDefEq.respectTransparency.types false in
private theorem functionField_jPull (N : ℕ) [NeZero N] (r : Γ(NormalModel.P, jAffineChart)) :
    X0Model.functionField N ((X0Model.curve N).germToFunctionField (jProjection N ⁻¹ᵁ jAffineChart)
      ((jProjection N).app jAffineChart r)) =
      NormalModel.φ (modularFunctionField N) (NormalModel.P.germToFunctionField jAffineChart r) := by
  let F := modularFunctionField N
  let S := Γ(X0Model.curve N, jProjection N ⁻¹ᵁ jAffineChart)
  let C := Γ(NormalModel.P, jAffineChart)
  let hW := NormalModel.isAffineOpen_chart 0
  let hV := hW.preimage (jProjection N)
  let : IsFractionRing S (X0Model.curve N).functionField :=
    functionField_isFractionRing_of_isAffineOpen _ _ hV
  let := ((NormalModel.f F).app jAffineChart).hom.toAlgebra
  let := NormalModel.algSecF F jAffineChart
  let := (NormalModel.φ F).toAlgebra
  let : IsScalarTower C NormalModel.P.functionField F := NormalModel.isScalarTower_secF F jAffineChart
  let : FiniteDimensional NormalModel.P.functionField F := NormalModel.finite_φ F
  let : IsFractionRing C NormalModel.P.functionField :=
    functionField_isFractionRing_of_isAffineOpen _ _ hW
  let : IsFractionRing (integralClosure C F) F :=
    integralClosure.isFractionRing_of_finite_extension NormalModel.P.functionField F
  change IsFractionRing.ringEquivOfRingEquiv
      (((NormalModel.f F).normalizationObjIso hW).commRingCatIsoToRingEquiv.trans
        (NormalModel.εAlg F jAffineChart).mapIntegralClosure.toRingEquiv)
      (algebraMap S (X0Model.curve N).functionField ((jProjection N).app jAffineChart r)) = _
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  change (NormalModel.εIso F jAffineChart).hom
      (((NormalModel.f F).normalizationObjIso hW).hom ((jProjection N).app jAffineChart r)).val = _
  rw [show (jProjection N).app jAffineChart = _ from (NormalModel.f F).fromNormalization_app hW]
  simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
  exact NormalModel.εIso_app_apply F jAffineChart r

private theorem functionField_jCoordinate (N : ℕ) [NeZero N] :
    X0Model.functionField N ((X0Model.curve N).germToFunctionField (jProjection N ⁻¹ᵁ jAffineChart)
      ((jProjection N).app jAffineChart jCoordinateSection)) = ⟨jq, jq_mem N⟩ := by
  rw [functionField_jPull]
  have hr : NormalModel.ratFuncEquiv RatFunc.X =
      NormalModel.P.germToFunctionField jAffineChart jCoordinateSection := by
    let : IsFractionRing Γ(NormalModel.P, jAffineChart) NormalModel.P.functionField :=
      functionField_isFractionRing_of_isAffineOpen _ _ (NormalModel.isAffineOpen_chart 0)
    rw [← RatFunc.algebraMap_X]
    exact IsFractionRing.ringEquivOfRingEquiv_algebraMap (ProjectiveLine.polyEquivChart ℚ 0) _
  rw [← hr]
  change algebraMap (RatFunc ℚ) (modularFunctionField N)
    (NormalModel.ratFuncEquiv.symm (NormalModel.ratFuncEquiv RatFunc.X)) = _
  rw [RingEquiv.symm_apply_apply]
  change (Subfield.inclusion (show (IntermediateField.adjoin ℚ {jq}).toSubfield ≤
    (modularFunctionField N).toSubfield from adjoin_jq_le N))
      (X0Model.jCoordinate RatFunc.X) = _
  rw [X0Model.jCoordinate_X]
  rfl

private abbrev jEval {R : Type} [CommRing R] (q : ℚ →+* R) (j : R) :
    Γ(NormalModel.P, jAffineChart) →+* R :=
  (Polynomial.eval₂RingHom q j).comp (ProjectiveLine.polyEquivChart ℚ 0).symm.toRingHom

/-- A point of the finite affine chart of the j-line. -/
def jLinePoint {R : Type} [CommRing R] (q : ℚ →+* R) (j : R) :
    Spec (.of R) ⟶ NormalModel.P :=
  Spec.map (CommRingCat.ofHom (jEval q j)) ≫ (NormalModel.isAffineOpen_chart 0).fromSpec

private theorem jLinePoint_comp {R S : Type} [CommRing R] [CommRing S]
    (p : R →+* S) (q : ℚ →+* R) (j : R) :
    Spec.map (CommRingCat.ofHom p) ≫ jLinePoint q j = jLinePoint (p.comp q) (p j) := by
  unfold jLinePoint
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  ext r
  exact Polynomial.hom_eval₂ _ q p j

private theorem jLinePoint_injective :
    Function.Injective (jLinePoint (Rat.castHom ℂ)) := by
  intro a b h
  unfold jLinePoint at h
  have hh := (Spec.map_injective (cancel_mono (NormalModel.isAffineOpen_chart 0).fromSpec |>.mp h))
  have hv := congrArg (fun k : Γ(NormalModel.P, jAffineChart) ⟶ CommRingCat.of ℂ =>
    k jCoordinateSection) hh
  simpa [jEval, jCoordinateSection] using hv

private theorem affine_factor {R : Type} [CommRing R] (u : Spec (.of R) ⟶ NormalModel.P)
    (hu : ⊤ ≤ u ⁻¹ᵁ jAffineChart) :
    Spec.map (X0Model.sectionMap u jAffineChart hu) ≫
      (NormalModel.isAffineOpen_chart 0).fromSpec = u := by
  unfold X0Model.sectionMap
  rw [Spec.map_comp, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec u _
    (isAffineOpen_top _) hu, IsAffineOpen.fromSpec_top, ← Scheme.isoSpec_Spec_hom,
    Iso.hom_inv_id_assoc]

private theorem jGeneric (N : ℕ) [NeZero N] {K : Type} [Field K] [CharZero K]
    (e : modularFunctionField N →+* K) :
    X0Model.genericMap N e ≫ jProjection N =
      jLinePoint (Rat.castHom K) (e ⟨jq, jq_mem N⟩) := by
  let u := X0Model.genericMap N e
  let V := jProjection N ⁻¹ᵁ jAffineChart
  have hu : ⊤ ≤ u ⁻¹ᵁ V := by
    intro x _
    have hx : u x = genericPoint (X0Model.curve N) := by
      rw [Subsingleton.elim x (IsLocalRing.closedPoint K)]
      dsimp only [u, X0Model.genericMap]
      erw [Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
    change u x ∈ V
    rw [hx]
    exact ((genericPoint_spec (X0Model.curve N)).mem_open_set_iff V.isOpen).mpr
      (by
        rw [Set.univ_inter]
        exact Set.nonempty_coe_sort.mp (jAffine_ne N))
  have hi : ⊤ ≤ (u ≫ jProjection N) ⁻¹ᵁ jAffineChart := by
    rwa [Scheme.Hom.comp_preimage]
  have he : X0Model.sectionMap (u ≫ jProjection N) jAffineChart hi =
      CommRingCat.ofHom (jEval (Rat.castHom K) (e ⟨jq, jq_mem N⟩)) := by
    unfold X0Model.sectionMap
    rw [← Scheme.Hom.appLE_comp_appLE _ _ jAffineChart V ⊤ le_rfl hu,
      Category.assoc, Scheme.Hom.appLE_eq_app]
    change (jProjection N).app jAffineChart ≫ X0Model.sectionMap u V hu = _
    rw [X0Model.sectionMap_generic N e V hu]
    apply CommRingCat.hom_ext
    let L : Γ(NormalModel.P, jAffineChart) →+* K :=
      (e.comp (X0Model.functionField N).toRingHom).comp
        (((X0Model.curve N).germToFunctionField V).hom.comp ((jProjection N).app jAffineChart).hom)
    change L = jEval (Rat.castHom K) (e ⟨jq, jq_mem N⟩)
    let p := ProjectiveLine.polyEquivChart ℚ 0
    have hh : L.comp p.toRingHom = Polynomial.eval₂RingHom (Rat.castHom K)
        (e ⟨jq, jq_mem N⟩) := by
      apply Polynomial.ringHom_ext' (Subsingleton.elim _ _)
      change L (p Polynomial.X) = Polynomial.eval₂ (Rat.castHom K)
        (e ⟨jq, jq_mem N⟩) Polynomial.X
      rw [Polynomial.eval₂_X]
      change e (X0Model.functionField N ((X0Model.curve N).germToFunctionField V
        ((jProjection N).app jAffineChart jCoordinateSection))) = _
      rw [functionField_jCoordinate]
    apply RingHom.ext
    intro x
    have hv := DFunLike.congr_fun hh (p.symm x)
    change L (p (p.symm x)) = Polynomial.eval₂RingHom (Rat.castHom K)
      (e ⟨jq, jq_mem N⟩) (p.symm x) at hv
    rwa [p.apply_symm_apply] at hv
  rw [← affine_factor _ hi, he]
  rfl

private theorem hasValue_jGerm (τ : UpperHalfPlane) :
    HasValue (X0Model.meromorphicIncl (τ : ℂ) (X0Model.jPolynomial τ Polynomial.X))
      (X0Model.analyticJ τ) := by
    have h : X0Model.meromorphicIncl (τ : ℂ) (X0Model.jPolynomial τ Polynomial.X) =
        ((X0Model.analyticJ ∘ UpperHalfPlane.ofComplex : ℂ → ℂ) : PuncturedGerm (τ : ℂ)) := by
      apply Germ.coe_eq.mpr
      exact Eventually.of_forall fun _ => by simp
    rw [h]
    exact hasValue_coe.mpr (by simpa only [Function.comp_apply, UpperHalfPlane.ofComplex_apply]
      using (X0Model.analyticOn_j τ τ.im_pos).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)

private def finiteJ (τ : UpperHalfPlane) : X0Model.meromorphicValuation (τ : ℂ) :=
  ⟨X0Model.jPolynomial τ Polynomial.X, ⟨X0Model.analyticJ τ, hasValue_jGerm τ⟩⟩

private theorem valueOf_finiteJ (τ : UpperHalfPlane) :
    X0Model.valueOfGerm (τ : ℂ) (finiteJ τ) = X0Model.analyticJ τ :=
  hasValue_unique (finiteValue_spec (X0Model.meromorphicIncl (τ : ℂ)) (finiteJ τ))
    (hasValue_jGerm τ)

private def finiteRat (z : ℂ) : ℚ →+* X0Model.meromorphicValuation z :=
  ((X0Model.constantGerm z).comp (Rat.castHom ℂ)).codRestrict
    (X0Model.meromorphicValuation z).toSubring fun c => by
      change ∃ d, HasValue (((fun _ => (c : ℂ)) : ℂ → ℂ) : PuncturedGerm z) d
      exact ⟨(c : ℂ), hasValue_coe.mpr tendsto_const_nhds⟩

/-- The first coordinate of the point on the normalization is the finite
affine value of the analytic j-function. -/
theorem complexPoint_jProjection (N : ℕ) [NeZero N] (τ : UpperHalfPlane) :
    X0Model.complexPoint N τ ≫ jProjection N =
      jLinePoint (Rat.castHom ℂ) (X0Model.analyticJ τ) := by
  let R := X0Model.meromorphicValuation (τ : ℂ)
  let K := X0Model.MeromorphicGerm (τ : ℂ)
  let : CharZero K := charZero_of_injective_ringHom (X0Model.constantGerm (τ : ℂ)).injective
  let b := projectiveLineToSpec ℚ
  let u := X0Model.analyticArc N τ ≫ jProjection N
  let v := jLinePoint (finiteRat (τ : ℂ)) (finiteJ τ)
  let e := Spec.map (CommRingCat.ofHom (algebraMap R K))
  have hgen : e ≫ u = e ≫ v := by
    unfold u v e
    rw [← Category.assoc, X0Model.analyticArc_generic, jGeneric, jLinePoint_comp]
    have : (algebraMap R K).comp (finiteRat (τ : ℂ)) = Rat.castHom K := Subsingleton.elim _ _
    rw [this, X0Model.fieldGerm_j]
    rfl
  let q := Spec.map (CommRingCat.ofHom (finiteRat (τ : ℂ)))
  have hu : u ≫ b = q := by
    apply Spec.homEquiv.injective
    exact CommRingCat.hom_ext (Subsingleton.elim _ _)
  have hv : v ≫ b = q := by
    apply Spec.homEquiv.injective
    exact CommRingCat.hom_ext (Subsingleton.elim _ _)
  let sq : ValuativeCommSq b :=
    { R := R
      K := K
      i₁ := e ≫ u
      i₂ := q
      commSq := ⟨by rw [Category.assoc, hu]⟩ }
  have huv : u = v := by
    have h := IsSeparated.valuativeCriterion (f := b) sq
    let := h
    exact congrArg CommSq.LiftStruct.l
      (Subsingleton.elim (⟨u, rfl, hu⟩ : sq.commSq.LiftStruct) ⟨v, hgen.symm, hv⟩)
  rw [X0Model.complexPoint, Category.assoc, show X0Model.analyticArc N τ ≫ jProjection N = u from rfl,
    huv, show v = jLinePoint (finiteRat _) (finiteJ _) from rfl, jLinePoint_comp, valueOf_finiteJ]
  congr 1
  exact Subsingleton.elim _ _

/-- Equal normalized chart points have the same analytic j-value. -/
theorem analyticJ_eq_of_complexPoint_eq (N : ℕ) [NeZero N] (τ σ : UpperHalfPlane)
    (h : X0Model.complexPoint N τ = X0Model.complexPoint N σ) :
    X0Model.analyticJ τ = X0Model.analyticJ σ := by
  apply jLinePoint_injective
  rw [← complexPoint_jProjection N τ, ← complexPoint_jProjection N σ, h]


end ZInQ.Manuscript.RC.X0Model2
