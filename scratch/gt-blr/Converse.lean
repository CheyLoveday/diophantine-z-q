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

/-! ## The converse: local Néron models at every maximal ideal give a Néron model -/

section Converse

/-- (scratch copy of `neron_ext`, without the section's `𝔭`) -/
theorem neron_ext0 {R K : Type} [CommRing R] [Field K] [Algebra R K]
    {X : Over (Spec (CommRingCat.of R))} (hX : CToPrinted.IsNeronModelOver R K X)
    (Y : Over (Spec (CommRingCat.of R))) [Smooth Y.hom] {P : Scheme.{0}} (p : P ⟶ Y.left)
    (q : P ⟶ Spec (CommRingCat.of K))
    (H : IsPullback p q Y.hom (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (b : P ⟶ X.left) (hb : b ≫ X.hom = q ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    ∃ f : Y.left ⟶ X.left, f ≫ X.hom = Y.hom ∧ p ≫ f = b := by
  have hb' : (H.isoPullback.inv ≫ b) ≫ X.hom =
      pullback.snd Y.hom (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
    rw [Category.assoc, hb, ← Category.assoc, IsPullback.isoPullback_inv_snd]
  let h : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj Y ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj X :=
    Over.homMk (pullback.lift _ _ hb') (pullback.lift_snd _ _ _)
  obtain ⟨f, hf⟩ := (hX.2.2.2.2 Y).2 h
  refine ⟨f.left, Over.w f, ?_⟩
  have h1 := congrArg (fun t => t.left ≫ pullback.fst X.hom
    (Spec.map (CommRingCat.ofHom (algebraMap R K)))) hf
  simp only [Over.pullback_map_left, pullback.lift_fst, h, Over.homMk_left] at h1
  have h2 := congrArg (fun t => H.isoPullback.hom ≫ t) h1
  simp only [IsPullback.isoPullback_hom_fst_assoc, Iso.hom_inv_id_assoc] at h2
  exact h2

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]

/-- The Néron property of `X ⊗_R R_𝔭` over `R_𝔭`, as an extension property for `R`-morphisms into `X`. -/
theorem neron_ext_loc (R𝔭 : Type) [CommRing R𝔭] [Algebra R R𝔭] [Algebra R𝔭 K] [IsScalarTower R R𝔭 K]
    {X : Over (Spec (CommRingCat.of R))}
    (hX : CToPrinted.IsNeronModelOver R𝔭 K
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R R𝔭)))).obj X))
    (Y : Over (Spec (CommRingCat.of R𝔭))) [Smooth Y.hom] {P : Scheme.{0}} (p : P ⟶ Y.left)
    (q : P ⟶ Spec (CommRingCat.of K))
    (H : IsPullback p q Y.hom (Spec.map (CommRingCat.ofHom (algebraMap R𝔭 K))))
    (b : P ⟶ X.left) (hb : b ≫ X.hom = q ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    ∃ f : Y.left ⟶ X.left, f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R R𝔭)) ∧
      p ≫ f = b := by
  have hk : Spec.map (CommRingCat.ofHom (algebraMap R𝔭 K)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R R𝔭)) = Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  let b' : P ⟶ pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap R R𝔭))) :=
    pullback.lift b (q ≫ Spec.map (CommRingCat.ofHom (algebraMap R𝔭 K)))
      (by rw [hb, Category.assoc, hk])
  obtain ⟨f', hf'1, hf'2⟩ := neron_ext0 hX Y p q H b' (pullback.lift_snd _ _ _)
  have hf'1' : f' ≫ pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap R R𝔭))) = Y.hom := hf'1
  refine ⟨f' ≫ pullback.fst _ _, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hf'1']
  · rw [← Category.assoc, hf'2, pullback.lift_fst]

end Converse

section BC

variable {R : Type} [CommRing R] (𝔭 : Ideal R) [𝔭.IsPrime] (R𝔭 : Type) [CommRing R𝔭] [Algebra R R𝔭]
  [IsLocalization.AtPrime R𝔭 𝔭] {V : Scheme.{0}} (v : V ⟶ Spec (CommRingCat.of R))

/-- The cone maps `R_𝔭 ×_R V → R[1/s] ×_R V`, written with explicit pullbacks. -/
noncomputable def bcπ (a : (Idx 𝔭)ᵒᵖ) :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R R𝔭))) v ⟶ pullback (ej a) v :=
  pullback.lift (pullback.fst _ v ≫ Spec.map (CommRingCat.ofHom (toP R𝔭 a.unop))) (pullback.snd _ v)
    (((Category.assoc _ _ _).trans (congrArg (pullback.fst _ v ≫ ·) (toP_ej R𝔭 a))).trans
      pullback.condition)

theorem bcCone_π (a : (Idx 𝔭)ᵒᵖ) : (bcCone 𝔭 R𝔭 v).π.app a = bcπ 𝔭 R𝔭 v a := rfl

theorem bcπ_fst (a : (Idx 𝔭)ᵒᵖ) : (bcCone 𝔭 R𝔭 v).π.app a ≫ pullback.fst (ej a) v =
    pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R R𝔭))) v ≫
      Spec.map (CommRingCat.ofHom (toP R𝔭 a.unop)) :=
  pullback.lift_fst _ _ _

theorem bcπ_snd (a : (Idx 𝔭)ᵒᵖ) : (bcCone 𝔭 R𝔭 v).π.app a ≫ pullback.snd (ej a) v =
    pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R R𝔭))) v :=
  pullback.lift_snd _ _ _

end BC

section Local

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- **Local existence at a point** for the converse: around every point of a smooth `R`-scheme `Y`, an
`R`-morphism `Y_K → X` extends, given the Néron property of `X ⊗_R R_𝔭` at every maximal `𝔭`. -/
theorem local_pt {X : Over (Spec (CommRingCat.of R))} [Smooth X.hom]
    (hloc : ∀ (𝔭 : Ideal R) [𝔭.IsMaximal] (R𝔭 : Type) [CommRing R𝔭] [Algebra R R𝔭]
      [IsLocalization.AtPrime R𝔭 𝔭] [Algebra R𝔭 K] [IsScalarTower R R𝔭 K],
      CToPrinted.IsNeronModelOver R𝔭 K
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R R𝔭)))).obj X))
    {Y : Scheme.{0}} (y : Y ⟶ Spec (CommRingCat.of R)) [Smooth y]
    (a : pullback y (Spec.map (CommRingCat.ofHom (algebraMap R K))) ⟶ X.left)
    (ha : a ≫ X.hom = pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R K))) (x : Y) :
    ∃ U : Y.Opens, x ∈ U ∧ ∃ g : U.toScheme ⟶ X.left, g ≫ X.hom = U.ι ≫ y ∧
      pullback.fst (U.ι ≫ y) (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ g =
        pullback.lift (pullback.fst _ _ ≫ U.ι) (pullback.snd _ _)
          (by rw [Category.assoc]; exact pullback.condition) ≫ a := by
  let ιK := Spec.map (CommRingCat.ofHom (algebraMap R K))
  -- an affine open around `x`
  obtain ⟨_, ⟨V0, hV, rfl⟩, hxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let V : Y.Opens := V0
  haveI : IsAffine V := hV
  let v := V.ι ≫ y
  -- a maximal ideal over the image of `x`
  let q : PrimeSpectrum R := y.base x
  obtain ⟨𝔭, h𝔭, hq𝔭⟩ := Ideal.exists_le_maximal q.asIdeal q.isPrime.ne_top
  haveI := h𝔭
  let R𝔭 := Localization.AtPrime 𝔭
  have hunit : ∀ t : 𝔭.primeCompl, IsUnit (algebraMap R K t) := fun t =>
    isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective R K)).2
      (fun h => t.2 (h ▸ 𝔭.zero_mem)))
  letI : Algebra R𝔭 K := (IsLocalization.lift (M := 𝔭.primeCompl) (S := R𝔭) hunit).toAlgebra
  haveI : IsScalarTower R R𝔭 K :=
    IsScalarTower.of_algebraMap_eq (fun z => (IsLocalization.lift_eq hunit z).symm)
  let jR := Spec.map (CommRingCat.ofHom (algebraMap R R𝔭))
  let kK := Spec.map (CommRingCat.ofHom (algebraMap R𝔭 K))
  have hk : kK ≫ jR = ιK := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have hN := hloc 𝔭 R𝔭
  -- the extension over `V ⊗_R R_𝔭`
  let Y' : Over (Spec (CommRingCat.of R𝔭)) := Over.mk (pullback.fst jR v)
  haveI : Smooth Y'.hom := show Smooth (pullback.fst jR v) from inferInstance
  have eqb : (pullback.fst (pullback.fst jR v) kK ≫ pullback.snd jR v ≫ V.ι) ≫ y =
      pullback.snd (pullback.fst jR v) kK ≫ ιK := by
    show pullback.fst (pullback.fst jR v) kK ≫ pullback.snd jR v ≫ v = _
    rw [← pullback.condition, ← Category.assoc, pullback.condition, Category.assoc, hk]
  let ε : pullback (pullback.fst jR v) kK ⟶ pullback y ιK :=
    pullback.lift (pullback.fst _ _ ≫ pullback.snd jR v ≫ V.ι) (pullback.snd _ _) eqb
  have hb : (ε ≫ a) ≫ X.hom = pullback.snd (pullback.fst jR v) kK ≫ ιK := by
    rw [Category.assoc, ha, ← Category.assoc, pullback.lift_snd]
  obtain ⟨f𝔭, hf1, hf2⟩ := neron_ext_loc R𝔭 hN Y' (pullback.fst _ _) (pullback.snd _ _)
    (IsPullback.of_hasPullback _ _) (ε ≫ a) hb
  have hf1' : f𝔭 ≫ X.hom = pullback.fst jR v ≫ jR := hf1
  have hf2' : pullback.fst (pullback.fst jR v) kK ≫ f𝔭 = ε ≫ a := hf2
  -- spread `f𝔭` to some `R[1/s] ×_R V`
  haveI hA : ∀ (i : (Idx 𝔭)ᵒᵖ), IsAffine ((bcDiag 𝔭 v).obj i) := fun i => by
    haveI : IsAffine ((specDiag 𝔭).obj i) := show IsAffine (Spec _) from inferInstance
    exact show IsAffine (pullback (ej i) v) from inferInstance
  haveI : ∀ {i j : (Idx 𝔭)ᵒᵖ} (f : i ⟶ j), IsAffineHom ((bcDiag 𝔭 v).map f) := fun f => inferInstance
  haveI : ∀ i : (Idx 𝔭)ᵒᵖ, CompactSpace ((bcDiag 𝔭 v).obj i) := fun i => inferInstance
  haveI : ∀ i : (Idx 𝔭)ᵒᵖ, QuasiSeparatedSpace ((bcDiag 𝔭 v).obj i) := fun i => inferInstance
  have ha' : (bcCone 𝔭 R𝔭 v).π ≫ bcT 𝔭 v = (Functor.const _).map (f𝔭 ≫ X.hom) := by
    ext i
    show bcπ 𝔭 R𝔭 v i ≫ pullback.snd (ej i) v ≫ v = f𝔭 ≫ X.hom
    exact (pullback.lift_snd_assoc _ _ _ _).trans (pullback.condition.symm.trans hf1'.symm)
  obtain ⟨s, g, hg1, hg2⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (bcDiag 𝔭 v) (bcT 𝔭 v) X.hom (bcCone 𝔭 R𝔭 v) (bcConeIsLimit 𝔭 R𝔭 v) f𝔭 ha'
  let g' : pullback (ej s) v ⟶ X.left := g
  have hg2' : g' ≫ X.hom = pullback.snd (ej s) v ≫ v := hg2
  have hg1' : bcπ 𝔭 R𝔭 v s ≫ g' = f𝔭 := hg1
  -- the open `U = V ∩ y⁻¹ D(s)` around `x`
  let U : Y.Opens := V ⊓ y ⁻¹ᵁ (ej s).opensRange
  have hxU : x ∈ U := by
    refine ⟨hxV, ?_⟩
    have hrange := Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of R) s.unop.s
    have hmem : y.base x ∈ PrimeSpectrum.basicOpen (R := R) s.unop.s :=
      (PrimeSpectrum.mem_basicOpen _ _).2 (fun h => s.unop.hs (hq𝔭 h))
    exact (congrArg (y.base x ∈ ·) hrange).mpr hmem
  have hle : U ≤ V := inf_le_left
  have hr : Set.range (U.ι ≫ y).base ⊆ Set.range (ej s).base := by
    rintro _ ⟨z, rfl⟩
    exact z.2.2
  let n : U.toScheme ⟶ pullback (ej s) v :=
    pullback.lift (IsOpenImmersion.lift (ej s) (U.ι ≫ y) hr) (Y.homOfLE hle)
      (by rw [IsOpenImmersion.lift_fac]; show _ = Y.homOfLE hle ≫ V.ι ≫ y
          rw [← Category.assoc, Scheme.homOfLE_ι])
  refine ⟨U, hxU, n ≫ g', ?_, ?_⟩
  · rw [Category.assoc, hg2']
    show n ≫ pullback.snd (ej s) v ≫ V.ι ≫ y = U.ι ≫ y
    rw [← Category.assoc, pullback.lift_snd, ← Category.assoc, Scheme.homOfLE_ι]
  · let F := pullback.fst (U.ι ≫ y) ιK
    let G := pullback.snd (U.ι ≫ y) ιK
    have hFG : F ≫ U.ι ≫ y = G ≫ ιK := pullback.condition
    let ρ : pullback (U.ι ≫ y) ιK ⟶ pullback jR v :=
      pullback.lift (G ≫ kK) (F ≫ Y.homOfLE hle) (by
        show (G ≫ kK) ≫ jR = (F ≫ Y.homOfLE hle) ≫ V.ι ≫ y
        rw [Category.assoc, hk, Category.assoc, ← Category.assoc (Y.homOfLE hle), Scheme.homOfLE_ι, hFG])
    have l0 : bcπ 𝔭 R𝔭 v s ≫ pullback.fst (ej s) v ≫ ej s = pullback.fst jR v ≫ jR :=
      (pullback.lift_fst_assoc _ _ _ _).trans ((Category.assoc _ _ _).trans
        (congrArg (pullback.fst jR v ≫ ·) (toP_ej R𝔭 s)))
    have l3 : bcπ 𝔭 R𝔭 v s ≫ pullback.snd (ej s) v = pullback.snd jR v := pullback.lift_snd _ _ _
    have l1 : ρ ≫ bcπ 𝔭 R𝔭 v s ≫ pullback.fst (ej s) v ≫ ej s = G ≫ ιK := by
      rw [l0, pullback.lift_fst_assoc, Category.assoc, hk]
    have l2 : F ≫ n ≫ pullback.fst (ej s) v ≫ ej s = G ≫ ιK := by
      rw [pullback.lift_fst_assoc, IsOpenImmersion.lift_fac, hFG]
    have c1 : ρ ≫ bcπ 𝔭 R𝔭 v s = F ≫ n := by
      apply pullback.hom_ext
      · rw [← cancel_mono (ej s)]
        simp only [Category.assoc]
        rw [l1, l2]
      · simp only [Category.assoc]
        rw [l3, pullback.lift_snd, pullback.lift_snd]
    let ρ' : pullback (U.ι ≫ y) ιK ⟶ pullback (pullback.fst jR v) kK :=
      pullback.lift ρ G (pullback.lift_fst _ _ _)
    have c2 : ρ' ≫ ε = pullback.lift (F ≫ U.ι) G (by rw [Category.assoc]; exact hFG) := by
      apply pullback.hom_ext
      · simp only [ε, ρ', ρ, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc]
        rw [Scheme.homOfLE_ι]
      · simp only [ε, ρ', Category.assoc, pullback.lift_snd]
    have hρ : ρ = ρ' ≫ pullback.fst _ _ := (pullback.lift_fst _ _ _).symm
    have key : F ≫ n ≫ g' = pullback.lift (F ≫ U.ι) G (by rw [Category.assoc]; exact hFG) ≫ a := by
      rw [← Category.assoc, ← c1, Category.assoc, hg1', hρ, Category.assoc, hf2', ← Category.assoc, c2]
    exact key

/-- **The converse of BLR 1.2/4's `.mp`**: if `X ⊗_R R_𝔭` is a Néron model over `R_𝔭` for every maximal `𝔭`,
then `X` is a Néron model over `R`. -/
theorem isNeronModelOver_of_local {X : Over (Spec (CommRingCat.of R))} [Smooth X.hom] [IsSeparated X.hom]
    [QuasiCompact X.hom]
    (hloc : ∀ (𝔭 : Ideal R) [𝔭.IsMaximal] (R𝔭 : Type) [CommRing R𝔭] [Algebra R R𝔭]
      [IsLocalization.AtPrime R𝔭 𝔭] [Algebra R𝔭 K] [IsScalarTower R R𝔭 K],
      CToPrinted.IsNeronModelOver R𝔭 K
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R R𝔭)))).obj X)) :
    CToPrinted.IsNeronModelOver R K X := by
  let ιK := Spec.map (CommRingCat.ofHom (algebraMap R K))
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, fun Y _ => ⟨?_, ?_⟩⟩
  · intro f₁ f₂ h
    have key : f₁.left = f₂.left := by
      refine uqA R (IsFractionRing.injective R K) X Y.hom (pullback.fst Y.hom ιK) (pullback.snd Y.hom ιK)
        (IsPullback.of_hasPullback _ _) _ _ ((Over.w f₁).trans (Over.w f₂).symm) ?_
      have h1 := congrArg (fun t => t.left ≫ pullback.fst _ _) h
      simpa only [Over.pullback_map_left, pullback.lift_fst] using h1
    exact Over.OverMorphism.ext key
  · intro h
    have hw : h.left ≫ pullback.snd X.hom ιK = pullback.snd Y.hom ιK := Over.w h
    let a := h.left ≫ pullback.fst X.hom ιK
    have ha : a ≫ X.hom = pullback.snd Y.hom ιK ≫ ιK := by
      simp only [a, Category.assoc]
      rw [pullback.condition, ← Category.assoc, hw]
    choose U hxU g hg1 hg2 using local_pt hloc Y.hom a ha
    let 𝒰 : Y.left.OpenCover := {
      I₀ := Y.left, X i := (U i), f i := (U i).ι,
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨fun x ↦ ⟨x, by simpa using hxU x⟩, inferInstance⟩ }
    obtain ⟨f, hf1, hf2⟩ := glue_cover R (IsFractionRing.injective R K) X (𝟙 _) Y.hom a 𝒰 g
      (fun i => by rw [Category.comp_id]; exact hg1 i) hg2
    rw [Category.comp_id] at hf1
    refine ⟨Over.homMk f hf1, ?_⟩
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp only [Over.pullback_map_left, Over.homMk_left, pullback.lift_fst]
      exact hf2
    · simp only [Over.pullback_map_left, Over.homMk_left, pullback.lift_snd]
      exact hw.symm

end Local

/-- **BLR §1.2 Prop. 4, proved** (both directions; `CToPrinted.BLR_1_2_4` exactly). -/
theorem blr_1_2_4 : CToPrinted.BLR_1_2_4 := by
  intro R K _ _ _ _ _ X _ _ _
  exact ⟨fun hX 𝔭 _ R𝔭 _ _ _ _ _ => isNeronModelOver_localization (𝔭 := 𝔭) R𝔭 hX,
    fun h => isNeronModelOver_of_local h⟩

end GapBLR
