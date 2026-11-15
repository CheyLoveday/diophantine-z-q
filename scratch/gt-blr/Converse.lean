import ZInQKernel.Contrib.OneProof.BLRLocalizes

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry

namespace GapBLR

/-! ## General uniqueness and gluing over a base `Spec A`, `A ⊆ K` -/

section General

variable {K : Type} [Field K]

/-- `Spec K → Spec A` is scheme-theoretically dominant when `A → K` is injective. -/
theorem isSTD_of_injective (A : Type) [CommRing A] [Algebra A K]
    (hinj : Function.Injective (algebraMap A K)) :
    IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom (algebraMap A K))) := by
  haveI : _root_.IsReduced A := isReduced_of_injective (algebraMap A K) hinj
  haveI : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap A K))) := by
    rw [isDominant_iff, Spec.map_base]
    show DenseRange (PrimeSpectrum.comap (algebraMap A K))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
    intro x hx
    rw [RingHom.mem_ker] at hx
    rw [hinj (hx.trans (map_zero _).symm)]
    exact zero_mem _
  exact IsSchemeTheoreticallyDominant.of_isDominant _

/-- **Uniqueness over `Spec A`.** Two maps from a smooth `A`-scheme to a separated `S`-scheme, equal over `S`
and on the generic fibre, are equal. -/
theorem uqA (A : Type) [CommRing A] [Algebra A K] (hinj : Function.Injective (algebraMap A K))
    {S : Scheme.{0}} (X : Over S) [IsSeparated X.hom]
    {W : Scheme.{0}} (w : W ⟶ Spec (CommRingCat.of A)) [Smooth w]
    {P : Scheme.{0}} (p : P ⟶ W) (q : P ⟶ Spec (CommRingCat.of K))
    (H : IsPullback p q w (Spec.map (CommRingCat.ofHom (algebraMap A K))))
    (g₁ g₂ : W ⟶ X.left) (h₁₂ : g₁ ≫ X.hom = g₂ ≫ X.hom) (h : p ≫ g₁ = p ≫ g₂) : g₁ = g₂ := by
  haveI := isSTD_of_injective A hinj
  haveI : Smooth q := MorphismProperty.of_isPullback H ‹Smooth w›
  haveI : IsReduced P := LeafQM.AV.R1UnivRigid.isReduced_of_smooth q
  haveI : IsSchemeTheoreticallyDominant p := IsSchemeTheoreticallyDominant.of_isPullback H.flip
  haveI : QuasiCompact p := MorphismProperty.of_isPullback H.flip inferInstance
  haveI : IsReduced W := IsSchemeTheoreticallyDominant.isReduced p
  exact ext_of_isDominant_of_isSeparated X.hom h₁₂ p h

/-- **Gluing over `Spec A`.** Extensions on the pieces of an open cover of a smooth `A`-scheme `Y` that agree
with `b` on the generic fibres glue to an extension of `b`. -/
theorem glue_cover (A : Type) [CommRing A] [Algebra A K] (hinj : Function.Injective (algebraMap A K))
    {S : Scheme.{0}} (X : Over S) [IsSeparated X.hom] (jA : Spec (CommRingCat.of A) ⟶ S)
    {Y : Scheme.{0}} (y : Y ⟶ Spec (CommRingCat.of A)) [Smooth y]
    (b : pullback y (Spec.map (CommRingCat.ofHom (algebraMap A K))) ⟶ X.left)
    (𝒰 : Y.OpenCover) (g : ∀ i, 𝒰.X i ⟶ X.left)
    (hg1 : ∀ i, g i ≫ X.hom = (𝒰.f i ≫ y) ≫ jA)
    (hg2 : ∀ i, pullback.fst (𝒰.f i ≫ y) (Spec.map (CommRingCat.ofHom (algebraMap A K))) ≫ g i =
      pullback.lift (pullback.fst _ _ ≫ 𝒰.f i) (pullback.snd _ _)
        (by rw [Category.assoc]; exact pullback.condition) ≫ b) :
    ∃ f : Y ⟶ X.left, f ≫ X.hom = y ≫ jA ∧
      pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap A K))) ≫ f = b := by
  let kK := Spec.map (CommRingCat.ofHom (algebraMap A K))
  let m : ∀ i, pullback (𝒰.f i ≫ y) kK ⟶ pullback y kK := fun i =>
    pullback.lift (pullback.fst _ _ ≫ 𝒰.f i) (pullback.snd _ _)
      (by rw [Category.assoc]; exact pullback.condition)
  have compat : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ g i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ g j := by
    intro i j
    let w := pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ y
    have hw' : pullback.snd (𝒰.f i) (𝒰.f j) ≫ 𝒰.f j ≫ y = w := by
      simp only [w, ← Category.assoc, pullback.condition]
    let n : pullback w kK ⟶ pullback (𝒰.f i ≫ y) kK :=
      pullback.lift (pullback.fst w kK ≫ pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.snd w kK)
        (by rw [Category.assoc]; exact pullback.condition)
    let n' : pullback w kK ⟶ pullback (𝒰.f j ≫ y) kK :=
      pullback.lift (pullback.fst w kK ≫ pullback.snd (𝒰.f i) (𝒰.f j)) (pullback.snd w kK)
        (by rw [Category.assoc, hw']; exact pullback.condition)
    have hnn : n ≫ m i = n' ≫ m j := by
      apply pullback.hom_ext
      · simp only [n, n', m, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
        rw [pullback.condition]
      · simp only [n, n', m, Category.assoc, pullback.lift_snd]
    refine uqA A hinj X w (pullback.fst w kK) (pullback.snd w kK)
      (IsPullback.of_hasPullback _ _) _ _ ?_ ?_
    · rw [Category.assoc, Category.assoc, hg1 i, hg1 j]
      simp only [Category.assoc]
      rw [pullback.condition_assoc]
    · have e1 : pullback.fst w kK ≫ pullback.fst (𝒰.f i) (𝒰.f j) ≫ g i = n ≫ m i ≫ b := by
        rw [← hg2 i, ← Category.assoc, ← Category.assoc, pullback.lift_fst, Category.assoc]
      have e2 : pullback.fst w kK ≫ pullback.snd (𝒰.f i) (𝒰.f j) ≫ g j = n' ≫ m j ≫ b := by
        rw [← hg2 j, ← Category.assoc, ← Category.assoc, pullback.lift_fst, Category.assoc]
      rw [e1, e2, ← Category.assoc, hnn, Category.assoc]
  refine ⟨𝒰.glueMorphisms g compat, ?_, ?_⟩
  · refine Scheme.Cover.hom_ext 𝒰 _ _ (fun i => ?_)
    rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms, hg1 i, Category.assoc]
  · refine Scheme.Cover.hom_ext (𝒰.pullback₁ (pullback.fst y kK)) _ _ (fun (i : 𝒰.I₀) => ?_)
    let F1 := pullback.fst (pullback.fst y kK) (𝒰.f i)
    let F2 := pullback.snd (pullback.fst y kK) (𝒰.f i)
    have hF : F1 ≫ pullback.fst y kK = F2 ≫ 𝒰.f i := pullback.condition
    let ψ : pullback (pullback.fst y kK) (𝒰.f i) ⟶ pullback (𝒰.f i ≫ y) kK :=
      pullback.lift F2 (F1 ≫ pullback.snd y kK)
        (by rw [← Category.assoc, ← hF, Category.assoc, pullback.condition, Category.assoc])
    have hψ : ψ ≫ m i = F1 := by
      apply pullback.hom_ext
      · simp only [ψ, m, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
        exact hF.symm
      · simp only [ψ, m, Category.assoc, pullback.lift_snd]
    show F1 ≫ pullback.fst y kK ≫ 𝒰.glueMorphisms g compat = F1 ≫ b
    rw [← Category.assoc, hF, Category.assoc, Scheme.Cover.ι_glueMorphisms, ← hψ, Category.assoc,
      ← hg2 i, ← Category.assoc, pullback.lift_fst]

end General

/-! ## The limit `Spec R_𝔭 = lim Spec R[1/s]` in `Over (Spec R)`, and its base change -/

section OverLim

variable {R : Type} [CommRing R] (𝔭 : Ideal R) [𝔭.IsPrime] (R𝔭 : Type) [CommRing R𝔭] [Algebra R R𝔭]
  [IsLocalization.AtPrime R𝔭 𝔭]

theorem map_ej {a b : (Idx 𝔭)ᵒᵖ} (f : a ⟶ b) : (specDiag 𝔭).map f ≫ ej b = ej a := by
  refine (Spec.map_comp (CommRingCat.ofHom (algebraMap R (Loc b.unop)))
    (CommRingCat.ofHom (tr (leOfHom f.unop)))).symm.trans ?_
  congr 1
  apply CommRingCat.hom_ext
  ext x
  exact tr_alg (leOfHom f.unop) x

/-- `s ↦ (Spec R[1/s] → Spec R)` in `Over (Spec R)`. -/
noncomputable def overDiag : (Idx 𝔭)ᵒᵖ ⥤ Over (Spec (CommRingCat.of R)) where
  obj a := Over.mk (ej a)
  map f := Over.homMk ((specDiag 𝔭).map f) (map_ej 𝔭 f)
  map_id a := by ext1; exact (specDiag 𝔭).map_id a
  map_comp f g := by ext1; exact (specDiag 𝔭).map_comp f g

/-- `Spec R_𝔭 → Spec R` as a cone over `overDiag`. -/
noncomputable def overCone : Cone (overDiag 𝔭) where
  pt := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R R𝔭)))
  π := { app a := Over.homMk ((specCone 𝔭 R𝔭).π.app a) (π_ej R𝔭 a)
         naturality a b f := by ext1; exact (specCone 𝔭 R𝔭).π.naturality f }

/-- `Spec R_𝔭 = lim Spec R[1/s]` in `Over (Spec R)`. -/
noncomputable def overConeIsLimit : IsLimit (overCone 𝔭 R𝔭) := by
  haveI : IsConnected (Idx 𝔭)ᵒᵖ := IsCofiltered.isConnected _
  apply isLimitOfReflects (Over.forget _)
  refine (IsLimit.equivOfNatIsoOfIso (NatIso.ofComponents (fun _ => Iso.refl _) ?_) _ _
    (Cone.ext (Iso.refl _) ?_)) (specConeIsLimit 𝔭 R𝔭)
  · intro m n f
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · intro n
    simp only [Iso.refl_hom, Category.id_comp]

variable {V : Scheme.{0}} (v : V ⟶ Spec (CommRingCat.of R))

/-- `s ↦ R[1/s] ×_R V`. -/
noncomputable abbrev bcDiag : (Idx 𝔭)ᵒᵖ ⥤ Scheme.{0} :=
  (overDiag 𝔭 ⋙ Over.pullback v) ⋙ Over.forget V

/-- `R_𝔭 ×_R V` as a cone over `bcDiag`. -/
noncomputable abbrev bcCone : Cone (bcDiag 𝔭 v) :=
  (Over.forget V).mapCone ((Over.pullback v).mapCone (overCone 𝔭 R𝔭))

/-- `R_𝔭 ×_R V = lim R[1/s] ×_R V`. -/
noncomputable def bcConeIsLimit : IsLimit (bcCone 𝔭 R𝔭 v) := by
  haveI : IsConnected (Idx 𝔭)ᵒᵖ := IsCofiltered.isConnected _
  exact isLimitOfPreserves (Over.forget V) (isLimitOfPreserves (Over.pullback v) (overConeIsLimit 𝔭 R𝔭))

/-- The structure maps `R[1/s] ×_R V → Spec R`. -/
noncomputable def bcT : bcDiag 𝔭 v ⟶ (Functor.const _).obj (Spec (CommRingCat.of R)) where
  app a := pullback.snd (ej a) v ≫ v
  naturality a b f := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
    exact pullback.lift_snd_assoc _ _ _ _

end OverLim

end GapBLR
