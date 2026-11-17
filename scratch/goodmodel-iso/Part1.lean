import ZInQKernel.Contrib.OneProof.MumfordGroupLawNeron
import ZInQKernel.Contrib.FrobChain.Rigidity
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Theorems.Thm_NeronModelInfra_exists_opens_extension_of_isProper_of_smooth
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Theorems.Thm_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Theorems.Thm_AlgebraicGeometry_mem_of_ringKrullDim_stalk_le_one_of_isDiscreteValuationRing
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

namespace ZInQ.Contrib.GoodModelIso

open ZInQ.Contrib.GroupLawNeron

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The generic point map never hits the closed point. -/
lemma genMap_ne_closedPoint (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
    (t : Spec (CommRingCat.of K)) : (genMap R K).base t ≠ IsLocalRing.closedPoint R := by
  intro h
  have h1 : ((genMap R K).base t).asIdeal = Ideal.comap (algebraMap R K) t.asIdeal := rfl
  have h2 : t.asIdeal = ⊥ := by
    have := t.isPrime
    exact Ideal.eq_bot_of_prime t.asIdeal
  rw [h, h2, Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)] at h1
  exact IsDiscreteValuationRing.not_a_field R h1

instance (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] :
    IsSchemeTheoreticallyDominant (genMap R K) :=
  NeronC.isSchemeTheoreticallyDominant_spec_map _ (IsFractionRing.injective R K)

/-- **Density of the generic fibre.** Two morphisms from a flat `R`-scheme to a separated one that agree over
`Spec R` and on an open containing every point of the generic fibre are equal. -/
lemma ext_of_generic_open {X Y : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) [Flat p]
    (s : Y ⟶ Spec (CommRingCat.of R)) [IsSeparated s] {f g : X ⟶ Y} (hfs : f ≫ s = g ≫ s)
    (O : X.Opens) (hO : ∀ x, p.base x ≠ IsLocalRing.closedPoint R → x ∈ O)
    (hfg : O.ι ≫ f = O.ι ≫ g) : f = g := by
  let j := pullback.fst p (genMap R (FractionRing R))
  have hr : Set.range j.base ⊆ Set.range O.ι.base := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    apply hO
    have : (j ≫ p).base z = (pullback.snd p (genMap R (FractionRing R)) ≫ genMap R (FractionRing R)).base z := by
      rw [pullback.condition]
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] at this
    rw [this]
    exact genMap_ne_closedPoint _ _
  have hj : j = IsOpenImmersion.lift O.ι j hr ≫ O.ι := (IsOpenImmersion.lift_fac _ _ _).symm
  refine NeronC.ext_of_isSchemeTheoreticallyDominant_of_isSeparated s hfs j ?_
  rw [hj, Category.assoc, Category.assoc, hfg]

open ZInQ.Contrib.CloudW03NeronSurj.FLT in
/-- **Step A–B.** The inverse of `ψ_K` extends to an open `V ⊆ N` containing the generic fibre and meeting every
irreducible component of the special fibre (FLT's extension into a proper target), and on `V` and `ψ⁻¹ V` it is
an inverse of `ψ` (density of the generic fibre). -/
lemma exists_inverse_open (F N : Over (Spec (CommRingCat.of R))) [IsProper F.hom] [Smooth F.hom]
    [Smooth N.hom] [IsSeparated N.hom] [QuasiCompact N.hom] (ψ : F ⟶ N)
    (hK : IsIso ((Over.pullback (genMap R (FractionRing R))).map ψ)) :
    ∃ (V : N.left.Opens) (v : (V : Scheme) ⟶ F.left), v ≫ F.hom = V.ι ≫ N.hom ∧
      (∀ x : N.left, N.hom.base x ≠ IsLocalRing.closedPoint R → x ∈ V) ∧
      (∀ Z ∈ irreducibleComponents {x : N.left // N.hom.base x = IsLocalRing.closedPoint R}, ∃ x ∈ Z, x.1 ∈ V) ∧
      v ≫ ψ.left = V.ι ∧ (ψ.left ∣_ V) ≫ v = (ψ.left ⁻¹ᵁ V).ι := by
  let K := FractionRing R
  let s0 := genMap R K
  let ψK := ((Over.pullback s0).map ψ).left
  haveI : IsIso ψK := by
    have : IsIso ((Over.pullback s0).map ψ) := hK
    exact (Over.forget _).map_isIso ((Over.pullback s0).map ψ)
  have hψK1 : ψK ≫ pullback.fst N.hom s0 = pullback.fst F.hom s0 ≫ ψ.left := by
    simp [ψK]
  have hψK2 : ψK ≫ pullback.snd N.hom s0 = pullback.snd F.hom s0 := by
    simp [ψK]
  let iψ : ((Over.pullback s0).obj N).left ⟶ ((Over.pullback s0).obj F).left := inv ψK
  have hiψ : iψ ≫ pullback.snd F.hom s0 = pullback.snd N.hom s0 := by
    simp only [iψ]; rw [IsIso.inv_comp_eq]; exact hψK2.symm
  let uK : NeronModelInfra.SchemeHomOver (pullback.snd N.hom (NeronModelInfra.specGenericFibreInclusion R K))
      (pullback.snd F.hom (NeronModelInfra.specGenericFibreInclusion R K)) :=
    ⟨iψ, hiψ⟩
  obtain ⟨V, v, hVη, hVs, hvK⟩ :=
    NeronModelInfra.exists_opens_extension_of_isProper_of_smooth R K F.hom N.hom uK
  have hv := v.2
  -- the generic fibre of `v`
  have hvK' : pullback.fst (V.ι ≫ N.hom) s0 ≫ v.1 =
      pullback.map (V.ι ≫ N.hom) s0 N.hom s0 V.ι (𝟙 _) (𝟙 _) (Category.comp_id _)
        ((Category.comp_id _).trans (Category.id_comp _).symm) ≫ inv ψK ≫ pullback.fst F.hom s0 := by
    have := NeronModelInfra.genericFibreRestrict_coe_comp_fst (R := R) (K := K) F.hom (V.ι ≫ N.hom) v
    refine this.symm.trans ?_
    rw [hvK, Category.assoc]
    rfl
  have hB1 : v.1 ≫ ψ.left = V.ι := by
    refine NeronC.ext_of_isSchemeTheoreticallyDominant_of_isSeparated N.hom ?_
      (pullback.fst (V.ι ≫ N.hom) s0) ?_
    · rw [Category.assoc, Over.w ψ, hv]
    · rw [← Category.assoc, hvK', Category.assoc, Category.assoc, ← hψK1, IsIso.inv_hom_id_assoc]
      simp
  refine ⟨V, v.1, hv, hVη, hVs, hB1, ?_⟩
  let P0 := ψ.left ⁻¹ᵁ V
  refine NeronC.ext_of_isSchemeTheoreticallyDominant_of_isSeparated F.hom ?_
    (pullback.fst (P0.ι ≫ F.hom) s0) ?_
  · rw [Category.assoc, hv, ← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w ψ]
  · let m := pullback.map (P0.ι ≫ F.hom) s0 (V.ι ≫ N.hom) s0 (ψ.left ∣_ V) (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, ← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w ψ])
      ((Category.comp_id _).trans (Category.id_comp _).symm)
    let pP := pullback.map (P0.ι ≫ F.hom) s0 F.hom s0 P0.ι (𝟙 _) (𝟙 _) (Category.comp_id _)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
    have h1 : pullback.fst (P0.ι ≫ F.hom) s0 ≫ (ψ.left ∣_ V) = m ≫ pullback.fst (V.ι ≫ N.hom) s0 := by
      simp [m]
    have h2 : m ≫ pullback.map (V.ι ≫ N.hom) s0 N.hom s0 V.ι (𝟙 _) (𝟙 _) (Category.comp_id _)
        ((Category.comp_id _).trans (Category.id_comp _).symm) = pP ≫ ψK := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, hψK1]
        simp [m, pP, morphismRestrict_ι]
        rfl
      · rw [Category.assoc, Category.assoc, hψK2]
        simp [m, pP]
    rw [← Category.assoc, h1, Category.assoc, hvK', ← Category.assoc m, h2, Category.assoc,
      IsIso.hom_inv_id_assoc]
    simp [pP]
    rfl

/-- On `ψ⁻¹ V` a morphism into `F` is determined by its composite with `ψ` (from `(ψ ∣_ V) ≫ v = ι`). -/
lemma eq_of_comp_eq {F N : Over (Spec (CommRingCat.of R))} (ψ : F ⟶ N) (V : N.left.Opens)
    (v : (V : Scheme) ⟶ F.left) (hB2 : (ψ.left ∣_ V) ≫ v = (ψ.left ⁻¹ᵁ V).ι) {S : Scheme.{0}}
    (a b : S ⟶ F.left) (ha : ∀ x, ψ.left.base (a.base x) ∈ V) (hb : ∀ x, ψ.left.base (b.base x) ∈ V)
    (hab : a ≫ ψ.left = b ≫ ψ.left) : a = b := by
  let P0 := ψ.left ⁻¹ᵁ V
  have hra : Set.range a.base ⊆ Set.range P0.ι.base := by
    rintro _ ⟨x, rfl⟩; rw [Scheme.Opens.range_ι]; exact ha x
  have hrb : Set.range b.base ⊆ Set.range P0.ι.base := by
    rintro _ ⟨x, rfl⟩; rw [Scheme.Opens.range_ι]; exact hb x
  let la := IsOpenImmersion.lift P0.ι a hra
  let lb := IsOpenImmersion.lift P0.ι b hrb
  have hla : la ≫ P0.ι = a := IsOpenImmersion.lift_fac _ _ _
  have hlb : lb ≫ P0.ι = b := IsOpenImmersion.lift_fac _ _ _
  have h : la ≫ (ψ.left ∣_ V) = lb ≫ (ψ.left ∣_ V) := by
    rw [← cancel_mono V.ι, Category.assoc, Category.assoc, morphismRestrict_ι, ← Category.assoc,
      ← Category.assoc]
    change (la ≫ P0.ι) ≫ ψ.left = (lb ≫ P0.ι) ≫ ψ.left
    rw [hla, hlb, hab]
  rw [← hla, ← hlb, ← hB2, ← Category.assoc, ← Category.assoc, h]

open ZInQ.Contrib.CloudW03NeronSurj.FLT in
/-- **Steps D–G.** If moreover `ψ` is injective on points, it is an isomorphism (Hartogs extension of `v` into
an affine neighbourhood of each fibre). -/
lemma isIso_of_injective (F N : Over (Spec (CommRingCat.of R))) [IsProper F.hom] [Smooth F.hom]
    [Smooth N.hom] [IsSeparated N.hom] (ψ : F ⟶ N) (V : N.left.Opens) (v : (V : Scheme) ⟶ F.left)
    (hv : v ≫ F.hom = V.ι ≫ N.hom)
    (hVη : ∀ x : N.left, N.hom.base x ≠ IsLocalRing.closedPoint R → x ∈ V)
    (hVs : ∀ Z ∈ irreducibleComponents {x : N.left // N.hom.base x = IsLocalRing.closedPoint R}, ∃ x ∈ Z, x.1 ∈ V)
    (hB1 : v ≫ ψ.left = V.ι) (hB2 : (ψ.left ∣_ V) ≫ v = (ψ.left ⁻¹ᵁ V).ι)
    (hinj : Function.Injective ψ.left.base) : IsIso ψ := by
  have hψN : ψ.left ≫ N.hom = F.hom := Over.w ψ
  haveI : IsProper ψ.left := by
    haveI : IsProper (ψ.left ≫ N.hom) := by rw [hψN]; infer_instance
    exact IsProper.of_comp ψ.left N.hom
  haveI : IsLocallyNoetherian N.left := LocallyOfFiniteType.isLocallyNoetherian N.hom
  have hB1pt : ∀ r, ψ.left.base (v.base r) = V.ι.base r := fun r => by
    rw [← Scheme.Hom.comp_apply, hB1]
  suffices h : IsIso ψ.left by
    haveI : IsIso ((Over.forget _).map ψ) := h
    exact isIso_of_reflects_iso ψ (Over.forget _)
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := MorphismProperty.isomorphisms Scheme)
    (f := ψ.left) (fun z => ?_)
  -- D: an affine open `Y` containing the fibre over `z`, and an affine `U' ∋ z` with `ψ⁻¹ U' ⊆ Y`
  obtain ⟨Y, hY, hYz⟩ : ∃ Y : F.left.Opens, IsAffineOpen Y ∧ ∀ x, ψ.left.base x = z → x ∈ Y := by
    by_cases h : ∃ x, ψ.left.base x = z
    · obtain ⟨x, hx⟩ := h
      obtain ⟨Y, hY, hxY, -⟩ : ∃ Y : F.left.Opens, IsAffineOpen Y ∧ x ∈ Y ∧ Y ≤ ⊤ :=
        (TopologicalSpace.Opens.isBasis_iff_nbhd.mp F.left.isBasis_affineOpens)
        (Set.mem_univ x : x ∈ (⊤ : F.left.Opens))
      exact ⟨Y, hY, fun x' hx' => by rw [hinj (hx'.trans hx.symm)]; exact hxY⟩
    · exact ⟨⊥, isAffineOpen_bot _, fun x hx => (h ⟨x, hx⟩).elim⟩
  let U : N.left.Opens := ⟨(ψ.left.base '' (Y : Set F.left)ᶜ)ᶜ,
    isOpen_compl_iff.mpr (ψ.left.isClosedMap _ Y.isOpen.isClosed_compl)⟩
  have hzU : z ∈ U := by
    rintro ⟨x, hx, rfl⟩; exact hx (hYz x rfl)
  have hUY : ∀ x, ψ.left.base x ∈ U → x ∈ Y := by
    intro x hx; by_contra h; exact hx ⟨x, h, rfl⟩
  obtain ⟨U', hU', hzU', hU'U⟩ : ∃ U' : N.left.Opens, IsAffineOpen U' ∧ z ∈ U' ∧ U' ≤ U :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp N.left.isBasis_affineOpens) hzU
  refine ⟨U', hzU', ?_⟩
  haveI : IsAffine (Y : Scheme) := hY
  haveI : IsAffine (U' : Scheme) := hU'
  -- E: Hartogs
  have hT : ∀ x : (U' : Scheme), IsDomain ((U' : Scheme).presheaf.stalk x) ∧
      IsIntegrallyClosed ((U' : Scheme).presheaf.stalk x) := fun x =>
    AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing R (U'.ι ≫ N.hom) x
  have hVU : ∀ x : (U' : Scheme), ringKrullDim ((U' : Scheme).presheaf.stalk x) ≤ 1 → x ∈ U'.ι ⁻¹ᵁ V := by
    intro x hx
    show U'.ι.base x ∈ V
    refine AlgebraicGeometry.mem_of_ringKrullDim_stalk_le_one_of_isDiscreteValuationRing R N.hom V hVη hVs _ ?_
    rwa [ringKrullDim_eq_of_ringEquiv (asIso (U'.ι.stalkMap x)).commRingCatIsoToRingEquiv]
  let O := U'.ι ⁻¹ᵁ V
  have hr : Set.range ((U'.ι ∣_ V) ≫ v).base ⊆ Set.range Y.ι.base := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    apply hUY
    rw [Scheme.Hom.comp_apply, hB1pt, ← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
    have hm : U'.ι.base (O.ι.base p) ∈ Set.range U'.ι.base := ⟨_, rfl⟩
    rw [Scheme.Opens.range_ι] at hm
    exact hU'U hm
  let v' : (O : Scheme) ⟶ (Y : Scheme) := IsOpenImmersion.lift Y.ι ((U'.ι ∣_ V) ≫ v) hr
  have hv' : v' ≫ Y.ι = (U'.ι ∣_ V) ≫ v := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨φ, hφ, -⟩ := AlgebraicGeometry.existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk hT O hVU v'
  -- `φ` lies over `Spec R` (uniqueness of extensions into the affine `Spec R`)
  have hφR : φ ≫ Y.ι ≫ F.hom = U'.ι ≫ N.hom := by
    obtain ⟨_, -, huniq⟩ := AlgebraicGeometry.existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk hT O hVU
      (O.ι ≫ U'.ι ≫ N.hom)
    have e1 := huniq (φ ≫ Y.ι ≫ F.hom) (by
      beta_reduce
      rw [← Category.assoc, hφ, ← Category.assoc, hv', Category.assoc, hv, ← Category.assoc,
        morphismRestrict_ι, Category.assoc])
    have e2 := huniq (U'.ι ≫ N.hom) rfl
    rw [e1, e2]
  have hOgen : ∀ x : (U' : Scheme), (U'.ι ≫ N.hom).base x ≠ IsLocalRing.closedPoint R → x ∈ O :=
    fun x hx => hVη _ hx
  -- F: `φ` is a section of `ψ` over `U'`
  have h1 : φ ≫ Y.ι ≫ ψ.left = U'.ι := by
    refine ext_of_generic_open (U'.ι ≫ N.hom) N.hom ?_ O hOgen ?_
    · rw [Category.assoc, Category.assoc, hψN, hφR]
    · rw [← Category.assoc, hφ, ← Category.assoc, hv', Category.assoc, hB1, morphismRestrict_ι]
  let P := ψ.left ⁻¹ᵁ U'
  have hrP : Set.range (φ ≫ Y.ι).base ⊆ Set.range P.ι.base := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    show ψ.left.base ((φ ≫ Y.ι).base p) ∈ U'
    rw [← Scheme.Hom.comp_apply, Category.assoc, h1]
    have hm : U'.ι.base p ∈ Set.range U'.ι.base := ⟨_, rfl⟩
    rwa [Scheme.Opens.range_ι] at hm
  let φ' : (U' : Scheme) ⟶ (P : Scheme) := IsOpenImmersion.lift P.ι (φ ≫ Y.ι) hrP
  have hφ' : φ' ≫ P.ι = φ ≫ Y.ι := IsOpenImmersion.lift_fac _ _ _
  have hb : φ' ≫ (ψ.left ∣_ U') = 𝟙 _ := by
    rw [← cancel_mono U'.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hφ', Category.assoc, h1,
      Category.id_comp]
  have ha : (ψ.left ∣_ U') ≫ φ' = 𝟙 _ := by
    rw [← cancel_mono P.ι, Category.assoc, hφ', Category.id_comp]
    let O2 := P.ι ⁻¹ᵁ (ψ.left ⁻¹ᵁ V)
    refine ext_of_generic_open (P.ι ≫ F.hom) F.hom ?_ O2 ?_ ?_
    · rw [Category.assoc, Category.assoc, hφR, ← Category.assoc, morphismRestrict_ι, Category.assoc, hψN]
    · intro x hx
      show ψ.left.base (P.ι.base x) ∈ V
      apply hVη
      rw [← Scheme.Hom.comp_apply, hψN]
      exact hx
    · refine eq_of_comp_eq ψ V v hB2 _ _ ?_ ?_ ?_
      · intro x
        rw [← Scheme.Hom.comp_apply]
        have : ((O2.ι ≫ (ψ.left ∣_ U') ≫ φ ≫ Y.ι) ≫ ψ.left) = O2.ι ≫ P.ι ≫ ψ.left := by
          rw [Category.assoc, Category.assoc, Category.assoc, h1, morphismRestrict_ι]
        rw [this, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
        exact x.2
      · intro x; rw [Scheme.Hom.comp_apply]; exact x.2
      · rw [Category.assoc, Category.assoc, Category.assoc, h1, morphismRestrict_ι, Category.assoc]
  exact (MorphismProperty.isomorphisms.iff _).mpr ⟨⟨φ', ha, hb⟩⟩

end ZInQ.Contrib.GoodModelIso
