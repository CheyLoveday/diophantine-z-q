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

end ZInQ.Contrib.GoodModelIso
