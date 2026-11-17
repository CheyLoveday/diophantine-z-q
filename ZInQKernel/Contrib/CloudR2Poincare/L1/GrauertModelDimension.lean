import ZInQKernel.Contrib.CloudR2Poincare.L1.ReducedKernelSplit

/-!
# Constant H0 dimension on an actual universal proper-family model

The comparison uses the ORIGINAL residue field of the image point. Native
matrix-minor rank invariance then transports its dimension to the residue
field of the local open. No equality of different residue-field types is
assumed. The universal comparison is exactly the proved FiniteFreeModel output.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- For a termwise finite-free complex, field-valued fibre cohomology dimension
only depends on the image point, in every degree. -/
theorem finrank_fibre_homology_eq_of_base_eq
    {Y : Scheme.{u}} (P : CochainComplex Y.Modules ℤ) (r : ℤ → ℕ)
    (e : ∀ q, P.X q ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin (r q))))
    {R R' : CommRingCat.{u}} (hR : IsField R) (hR' : IsField R')
    (g : Spec R ⟶ Y) (g' : Spec R' ⟶ Y) (x : Spec R) (x' : Spec R')
    (hbase : g.base x = g'.base x') (q : ℤ) :
    Module.finrank R ((moduleSpecΓFunctor (R := R)).obj
      ((((Scheme.Modules.pullback g).mapHomologicalComplex _).obj P).homology q)) =
    Module.finrank R' ((moduleSpecΓFunctor (R := R')).obj
      ((((Scheme.Modules.pullback g').mapHomologicalComplex _).obj P).homology q)) := by
  let A₁ := Scheme.Modules.freeMatrix ((e q).inv ≫ P.d q (q + 1) ≫ (e (q + 1)).hom)
  let A₂ := Scheme.Modules.freeMatrix ((e (q - 1)).inv ≫ P.d (q - 1) q ≫ (e q).hom)
  have hr₁ := Scheme.Modules.rank_map_appTop_eq_of_base_eq
    (Scheme.isField_Γ_Spec hR) (Scheme.isField_Γ_Spec hR') g g' x x' hbase A₁
  have hr₂ := Scheme.Modules.rank_map_appTop_eq_of_base_eq
    (Scheme.isField_Γ_Spec hR) (Scheme.isField_Γ_Spec hR') g g' x x' hbase A₂
  have hd₁ := Scheme.Modules.finrank_homology_pullback_add_rank_add_rank e hR g q
  have hd₂ := Scheme.Modules.finrank_homology_pullback_add_rank_add_rank e hR' g' q
  change _ + (A₁.map g.appTop).rank + (A₂.map g.appTop).rank = r q at hd₁
  change _ + (A₁.map g'.appTop).rank + (A₂.map g'.appTop).rank = r q at hd₂
  rw [hr₁, hr₂] at hd₁
  omega

/-- The actual proper-family model has H0 fibre dimension one whenever the
ORIGINAL coefficient sheaf has residue H0 rank one. -/
theorem model_H0_dimension_one_of_residueRank_one
    {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (U : Y.Opens)
    (P : CochainComplex U.toScheme.Modules ℤ) (r : ℤ → ℕ)
    (e : ∀ q, P.X q ≅ SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin (r q))))
    (comparison : ∀ {T X' : Scheme.{u}} (g : T ⟶ U.toScheme)
      (px : X' ⟶ X) (pf : X' ⟶ T) [HasInjectiveResolutions X'.Modules],
      IsPullback px pf f (g ≫ U.ι) → ∀ q : ℕ,
        Nonempty ((((Scheme.Modules.pullback g).mapHomologicalComplex _).obj P).homology q ≅
          (Scheme.Modules.higherDirectImage pf q).obj ((Scheme.Modules.pullback px).obj F)))
    (hF : ∀ y : Y, higherDirectImageResidueRank f F 0 y = 1) :
    ∀ z : U.toScheme, derivedFiberDimension P 0 z = 1 := by
  intro z
  let y : Y := U.ι z
  let py := Y.fromSpecResidueField y
  have hyU : y ∈ U := z.property
  have hrange : Set.range py ⊆ Set.range U.ι := by
    rw [Scheme.range_fromSpecResidueField, Scheme.Opens.range_ι]
    exact Set.singleton_subset_iff.mpr hyU
  let gy := IsOpenImmersion.lift U.ι py hrange
  have gy_fac : gy ≫ U.ι = py := IsOpenImmersion.lift_fac _ _ _
  have hsq : IsPullback (pullback.fst f py) (pullback.snd f py) f (gy ≫ U.ι) := by
    rw [gy_fac]
    exact IsPullback.of_hasPullback f py
  haveI := Scheme.Modules.isGrothendieckAbelian (pullback f py)
  let c := (comparison gy (pullback.fst f py) (pullback.snd f py) hsq 0).some
  have hdim : Module.finrank (Y.residueField y)
      ((moduleSpecΓFunctor (R := Y.residueField y)).obj
        ((((Scheme.Modules.pullback gy).mapHomologicalComplex _).obj P).homology 0)) =
      higherDirectImageResidueRank f F 0 y :=
    ((moduleSpecΓFunctor (R := Y.residueField y)).mapIso c).toLinearEquiv.finrank_eq
  obtain ⟨x⟩ : Nonempty (Spec (U.toScheme.residueField z)) := inferInstance
  obtain ⟨x'⟩ : Nonempty (Spec (Y.residueField y)) := inferInstance
  have hbase : (U.toScheme.fromSpecResidueField z).base x = gy.base x' := by
    rw [Scheme.Modules.fromSpecResidueField_base_apply]
    apply U.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, gy_fac, Scheme.fromSpecResidueField_apply]
  have hsame := finrank_fibre_homology_eq_of_base_eq P r e
    (Field.toIsField (U.toScheme.residueField z)) (Field.toIsField (Y.residueField y))
    (U.toScheme.fromSpecResidueField z) gy x x' hbase 0
  change derivedFiberDimension P 0 z = _ at hsame
  rw [hdim, hF] at hsame
  exact hsame

end ZInQ.Contrib.CloudR2Poincare.L1
