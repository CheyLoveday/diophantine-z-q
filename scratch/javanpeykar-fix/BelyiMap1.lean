import ZInQKernel.Contrib.OneProof.JavanpeykarFix.Basic

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace JavanpeykarFix

open CategoryTheory AlgebraicGeometry Limits

attribute [local instance] MvPolynomial.gradedAlgebra

section Chart

variable (k : Type) [Field k]

/-- The coordinate ring `k[s]` of the chart `D₊(X₁) ⊆ ℙ¹` (`s = X₀/X₁`). -/
abbrev Rk : Type := MvPolynomial {i : Fin 2 // i ≠ 1} k

/-- The index of `s = X₀/X₁`. -/
def i0 : {i : Fin 2 // i ≠ 1} := ⟨0, by decide⟩

instance : Unique {i : Fin 2 // i ≠ 1} where
  default := i0
  uniq := fun ⟨i, hi⟩ => by
    apply Subtype.ext
    show i = 0
    fin_cases i
    · rfl
    · exact absurd rfl hi

/-- The chart `Spec k[s] ≅ D₊(X₁) ⊆ ℙ¹` (vendored `Proj.standardOpenIso`). -/
def chart : Spec (CommRingCat.of (Rk k)) ⟶ P1 k :=
  (Proj.standardOpenIso (Fin 2) k 1).inv ≫
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X 1)).ι

instance : IsOpenImmersion (chart k) := by unfold chart; infer_instance

theorem chart_toSpec : chart k ≫ P1.toSpec k =
    Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* Rk k)) :=
  Proj.standardOpenIso_inv_over (Fin 2) k 1

end Chart

section Construction

variable {k : Type} [Field k] (C : Over (Spec (CommRingCat.of k))) [IsIntegral C.left]

/-- `Spec k(C) → C → Spec k` is `Spec` of the structure map `k → k(C)`. -/
theorem fromSpecFunctionField_hom :
    C.left.fromSpecFunctionField ≫ C.hom =
      Spec.map (CommRingCat.ofHom (ZInQ.LeafPush2.ffStructMap C)) := by
  apply ext_of_isAffine
  rw [← cancel_mono (Scheme.ΓSpecIso _).hom, Scheme.ΓSpecIso_naturality, ← cancel_epi (Scheme.ΓSpecIso _).inv]
  simp only [Scheme.Hom.comp_appTop, Scheme.fromSpecFunctionField,
    Scheme.fromSpecStalk_appTop, ZInQ.LeafPush2.ffStructMap, Scheme.germToFunctionField,
    Category.assoc, Iso.inv_hom_id_assoc]
  ext c
  simp

end Construction


section Points

variable {k : Type} [Field k] (C : Over (Spec (CommRingCat.of k))) [IsIntegral C.left]
  [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]

/-- **On a smooth proper integral curve every point other than the generic point is closed.**
(A non-closed `x ≠ η` specializes to a closed `z ≠ x`, giving `z < x < η` and `dim 𝒪_z ≥ 2`; but
`dim 𝒪_z = 1`, vendored `ringKrullDim_stalk_eq_one_of_isClosed`.) -/
theorem isClosed_of_ne_genericPoint (x : C.left) (hx : x ≠ genericPoint C.left) :
    IsClosed ({x} : Set C.left) := by
  have : CompactSpace C.left := QuasiCompact.compactSpace_of_compactSpace C.hom
  obtain ⟨z, hzS, hz⟩ := (isClosed_closure : IsClosed (closure ({x} : Set C.left))).exists_closed_singleton
    ⟨x, subset_closure rfl⟩
  by_cases hzx : z = x
  · subst hzx; exact hz
  exfalso
  have hxz : x ⤳ z := specializes_iff_mem_closure.mpr hzS
  have h1 : z < x := ⟨hxz, fun h => hzx (h.antisymm hxz).eq⟩
  have hηx : genericPoint C.left ⤳ x := (genericPoint_spec C.left).specializes (Set.mem_univ x)
  have h2 : x < genericPoint C.left := ⟨hηx, fun h => hx (h.antisymm hηx).eq⟩
  have c1 := Order.coheight_add_one_le h1
  have c2 := Order.coheight_add_one_le h2
  have hz1 := Scheme.ringKrullDim_stalk_eq_one_of_isClosed C.hom hz
  rw [ringKrullDim_stalk_eq_coheight] at hz1
  have hz1' : Order.coheight z = 1 := by exact_mod_cast hz1
  have : (2 : ℕ∞) ≤ 1 := by
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ Order.coheight (genericPoint C.left) + 1 + 1 := by gcongr; exact zero_le
      _ ≤ Order.coheight x + 1 := by gcongr
      _ ≤ Order.coheight z := c1
      _ = 1 := hz1'
  exact absurd this (by decide)

/-- **A closed subset of the curve not containing the generic point is finite.** -/
theorem finite_of_isClosed_of_genericPoint_notMem (Z : Set C.left) (hZ : IsClosed Z)
    (hη : genericPoint C.left ∉ Z) : Z.Finite := by
  have : CompactSpace C.left := QuasiCompact.compactSpace_of_compactSpace C.hom
  have : IsLocallyNoetherian C.left := LocallyOfFiniteType.isLocallyNoetherian C.hom
  have : IsNoetherian C.left := {}
  obtain ⟨S, hSf, hSc, hSi, rfl⟩ := TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  refine hSf.sUnion fun T hT => ?_
  have hgen := (hSi T hT).isGenericPoint_genericPoint_closure
  rw [(hSc T hT).closure_eq] at hgen
  have hmem : (hSi T hT).genericPoint ∈ T := hgen.mem
  have hne : (hSi T hT).genericPoint ≠ genericPoint C.left := fun h =>
    hη ⟨T, hT, h ▸ hmem⟩
  have hcl := isClosed_of_ne_genericPoint C _ hne
  rw [← hgen.def, hcl.closure_eq]
  exact Set.finite_singleton _

end Points


section Extension

variable {k : Type} [Field k] (C : Over (Spec (CommRingCat.of k))) [IsIntegral C.left]
  (t : C.left.functionField)

/-- `ψ_t : k[s] → k(C)`, `s ↦ t`. -/
def psi : CommRingCat.of (Rk k) ⟶ C.left.functionField :=
  letI := ZInQ.LeafPush2.ffAlgebra C
  CommRingCat.ofHom (MvPolynomial.aeval (fun _ => t)).toRingHom

theorem psi_C (c : k) : psi C t (MvPolynomial.C c) = ZInQ.LeafPush2.ffStructMap C c := by
  letI := ZInQ.LeafPush2.ffAlgebra C
  show MvPolynomial.aeval (fun _ => t) (MvPolynomial.C c) = _
  rw [MvPolynomial.aeval_C]; rfl

theorem psi_X : psi C t (MvPolynomial.X i0) = t := by
  letI := ZInQ.LeafPush2.ffAlgebra C
  show MvPolynomial.aeval (fun _ => t) (MvPolynomial.X i0) = _
  rw [MvPolynomial.aeval_X]

theorem psi_injective (ht : letI := ZInQ.LeafPush2.ffAlgebra C; Transcendental k t) :
    Function.Injective (psi C t) := by
  letI := ZInQ.LeafPush2.ffAlgebra C
  have : AlgebraicIndependent k (fun _ : {i : Fin 2 // i ≠ 1} => t) :=
    algebraicIndependent_unique_type_iff.mpr ht
  exact this

/-- The point `[t : 1] : Spec k(C) → ℙ¹_k`. -/
def ptT : Spec C.left.functionField ⟶ P1 k :=
  Spec.map (psi C t) ≫ chart k

theorem ptT_toSpec : ptT C t ≫ P1.toSpec k = C.left.fromSpecFunctionField ≫ C.hom := by
  rw [fromSpecFunctionField_hom, ptT, Category.assoc, chart_toSpec, ← Spec.map_comp]
  congr 1
  ext c
  exact psi_C C t c

instance P1.over : (P1 k).Over (Spec (CommRingCat.of k)) := ⟨P1.toSpec k⟩

instance : IsProper (P1 k ↘ Spec (CommRingCat.of k)) :=
  inferInstanceAs (IsProper (Proj.projectiveSpaceOverAffineToSpec (Fin 2) k))

instance : (P1 k).IsSeparated := by
  constructor
  rw [show terminal.from (P1 k) = P1.toSpec k ≫ terminal.from _ from terminal.hom_ext _ _]
  have : IsSeparated (P1.toSpec k) := inferInstanceAs (IsSeparated (P1 k ↘ Spec (CommRingCat.of k)))
  infer_instance

/-- **The morphism `β : C → ℙ¹` defined by `t`** (vendored valuative extension of rational maps,
Hartshorne I.6.8). -/
theorem exists_extension [SmoothOfRelativeDimension 1 C.hom] :
    ∃ β : C.left ⟶ P1 k, β ≫ P1.toSpec k = C.hom ∧ C.left.fromSpecFunctionField ≫ β = ptT C t := by
  letI : C.left.Over (Spec (CommRingCat.of k)) := ⟨C.hom⟩
  have hval : ∀ x : C.left, ValuationRing (C.left.presheaf.stalk x) := fun x =>
    Scheme.valuationRing_stalk C.hom x
  obtain ⟨β, hβo, hβ⟩ := Scheme.exists_hom_of_valuationRing_stalk
    (base := Spec (CommRingCat.of k)) hval (ptT C t) (ptT_toSpec C t)
  exact ⟨β, hβo.comp_over, hβ⟩

end Extension


section Finite

variable {k : Type} [Field k] (C : Over (Spec (CommRingCat.of k))) [IsIntegral C.left]
  [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] (t : C.left.functionField)

theorem beta_genericPoint {β : C.left ⟶ P1 k} (hβ : C.left.fromSpecFunctionField ≫ β = ptT C t) :
    β (genericPoint C.left) = chart k (Spec.map (psi C t)
      (IsLocalRing.closedPoint (C.left.presheaf.stalk (genericPoint C.left)))) := by
  have h := congrArg (fun f : Spec C.left.functionField ⟶ P1 k =>
    f (IsLocalRing.closedPoint (C.left.presheaf.stalk (genericPoint C.left)))) hβ
  simp only [ptT, Scheme.fromSpecFunctionField] at h
  exact (congrArg β (Scheme.fromSpecStalk_closedPoint (x := genericPoint C.left))).symm.trans h

theorem not_isUnit_X : ¬ IsUnit (MvPolynomial.X i0 : Rk k) := by
  intro h
  have := h.map (MvPolynomial.eval (fun _ => (0 : k)))
  simp at this

theorem not_isClosed_beta_genericPoint (ht : letI := ZInQ.LeafPush2.ffAlgebra C; Transcendental k t)
    {β : C.left ⟶ P1 k} (hβ : C.left.fromSpecFunctionField ≫ β = ptT C t) :
    ¬ IsClosed ({β (genericPoint C.left)} : Set (P1 k)) := by
  rw [beta_genericPoint C t hβ]
  intro hcl
  set z₀ := Spec.map (psi C t)
    (IsLocalRing.closedPoint (C.left.presheaf.stalk (genericPoint C.left)))
  have h1 : IsClosed ({z₀} : Set (Spec (CommRingCat.of (Rk k)))) := by
    have := hcl.preimage (chart k).continuous
    have he : (chart k) ⁻¹' {chart k z₀} = {z₀} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact (chart k).isOpenEmbedding.injective.eq_iff
    rwa [he] at this
  have hmax := (PrimeSpectrum.isClosed_singleton_iff_isMaximal z₀).mp h1
  have hbot : z₀.asIdeal = ⊥ := by
    show Ideal.comap (psi C t).hom (IsLocalRing.maximalIdeal _) = ⊥
    ext a
    simp only [Ideal.mem_comap, Ideal.mem_bot, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    constructor
    · intro h
      by_contra ha
      apply h
      have : (psi C t) a ≠ 0 := fun h0 => ha (psi_injective C t ht (h0.trans (map_zero _).symm))
      exact (show IsUnit ((psi C t) a : C.left.functionField) from isUnit_iff_ne_zero.mpr this)
    · rintro rfl
      rw [map_zero]
      exact not_isUnit_zero
  rw [hbot] at hmax
  have hfield : IsField (Rk k) := Ring.isField_iff_maximal_bot.mpr hmax
  obtain ⟨b, hb⟩ := hfield.mul_inv_cancel (MvPolynomial.X_ne_zero i0)
  exact not_isUnit_X (IsUnit.of_mul_eq_one b hb)

theorem finite_fibre (ht : letI := ZInQ.LeafPush2.ffAlgebra C; Transcendental k t)
    {β : C.left ⟶ P1 k} (hβo : β ≫ P1.toSpec k = C.hom)
    (hβ : C.left.fromSpecFunctionField ≫ β = ptT C t) (y : P1 k) : (β ⁻¹' {y}).Finite := by
  have : IsProper (β ≫ P1.toSpec k) := hβo ▸ inferInstance
  have : IsSeparated (P1.toSpec k) :=
    inferInstanceAs (IsSeparated (P1 k ↘ Spec (CommRingCat.of k)))
  have : IsProper β := IsProper.of_comp β (P1.toSpec k)
  have hcm : IsClosedMap β := β.isClosedMap
  by_cases hη : β (genericPoint C.left) = y
  · apply (Set.finite_singleton (genericPoint C.left)).subset
    intro x hx
    by_contra hne
    have h2 := hcm _ (isClosed_of_ne_genericPoint C x hne)
    rw [Set.image_singleton, show β x = y from hx, ← hη] at h2
    exact not_isClosed_beta_genericPoint C t ht hβ h2
  · by_cases hne : (β ⁻¹' {y}).Nonempty
    · obtain ⟨x, hx⟩ := hne
      have hxη : x ≠ genericPoint C.left := fun h => hη (h ▸ hx)
      have hycl : IsClosed ({y} : Set (P1 k)) := by
        have := hcm _ (isClosed_of_ne_genericPoint C x hxη)
        rwa [Set.image_singleton, show β x = y from hx] at this
      exact finite_of_isClosed_of_genericPoint_notMem C _ (hycl.preimage β.continuous) hη
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne]
      exact Set.finite_empty

/-- **`β` is finite** (proper with finite fibres, Mathlib `IsFinite.of_isProper_of_locallyQuasiFinite`). -/
theorem isFinite_beta (ht : letI := ZInQ.LeafPush2.ffAlgebra C; Transcendental k t)
    {β : C.left ⟶ P1 k} (hβo : β ≫ P1.toSpec k = C.hom)
    (hβ : C.left.fromSpecFunctionField ≫ β = ptT C t) : IsFinite β := by
  have : IsProper (β ≫ P1.toSpec k) := hβo ▸ inferInstance
  have : IsSeparated (P1.toSpec k) :=
    inferInstanceAs (IsSeparated (P1 k ↘ Spec (CommRingCat.of k)))
  have : IsProper β := IsProper.of_comp β (P1.toSpec k)
  have : LocallyOfFiniteType (β ≫ P1.toSpec k) := hβo ▸ inferInstance
  have : LocallyOfFiniteType β := locallyOfFiniteType_of_comp β (P1.toSpec k)
  have : LocallyQuasiFinite β :=
    LocallyQuasiFinite.of_finite_preimage_singleton β (finite_fibre C t ht hβo hβ)
  exact IsFinite.of_isProper_of_locallyQuasiFinite β

end Finite


section ChartOpens

variable (k : Type) [Field k]

theorem opensRange_chart : (chart k).opensRange =
    Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X 1) := by
  unfold chart
  rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]

theorem chart_mem_basicOpen_X0 (z : Spec (CommRingCat.of (Rk k))) :
    chart k z ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X 0) ↔
      (MvPolynomial.X i0 : Rk k) ∉ z.asIdeal := by
  rw [show chart k = _ from Proj.standardOpenIso_inv_ι (Fin 2) k 1, Scheme.Hom.comp_apply]
  have key := Proj.awayι_preimage_basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k)
    (MvPolynomial.X_mem_homogeneousSubmodule_one k 1) Nat.one_pos
    (MvPolynomial.X_mem_homogeneousSubmodule_one k 0) Nat.one_pos
  rw [← SetLike.mem_coe, ← Set.mem_preimage, ← TopologicalSpace.Opens.map_coe, key]
  erw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen, Spec.map_apply, PrimeSpectrum.comap_asIdeal,
    Ideal.mem_comap]
  erw [MvPolynomial.homogeneousLocalizationAwayXEquiv_awayMk]
  simp only [pow_one, MvPolynomial.dehomogenizeX, MvPolynomial.aeval_X]
  simp [i0]

theorem chart_mem_basicOpen_X0_sub_X1 (z : Spec (CommRingCat.of (Rk k))) :
    chart k z ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k)
      (MvPolynomial.X 0 - MvPolynomial.X 1) ↔ (MvPolynomial.X i0 - 1 : Rk k) ∉ z.asIdeal := by
  rw [show chart k = _ from Proj.standardOpenIso_inv_ι (Fin 2) k 1, Scheme.Hom.comp_apply]
  have key := Proj.awayι_preimage_basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k)
    (MvPolynomial.X_mem_homogeneousSubmodule_one k 1) Nat.one_pos
    (Submodule.sub_mem _
      (MvPolynomial.X_mem_homogeneousSubmodule_one k 0) (MvPolynomial.X_mem_homogeneousSubmodule_one k 1)) Nat.one_pos
  rw [← SetLike.mem_coe, ← Set.mem_preimage, ← TopologicalSpace.Opens.map_coe, key]
  erw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen, Spec.map_apply, PrimeSpectrum.comap_asIdeal,
    Ideal.mem_comap]
  erw [MvPolynomial.homogeneousLocalizationAwayXEquiv_awayMk]
  simp only [pow_one, MvPolynomial.dehomogenizeX, MvPolynomial.aeval_X, map_sub]
  simp [i0]

end ChartOpens


section MainIdentity

variable {k : Type} [Field k]

/-- The section of `ℙ¹` over the chart `D₊(X₁)` given by `r ∈ k[s]`. -/
def secR : CommRingCat.of (Rk k) ⟶ Γ(P1 k, (chart k) ''ᵁ ⊤) :=
  (Scheme.ΓSpecIso _).inv ≫ ((chart k).appIso ⊤).inv

variable (C : Over (Spec (CommRingCat.of k))) [IsIntegral C.left] (t : C.left.functionField)

theorem fromSpecStalk_appLE_top (X : Scheme) (x : X) (V : X.Opens) (hV : x ∈ V)
    (e : ⊤ ≤ X.fromSpecStalk x ⁻¹ᵁ V) (τ : Γ(X, V)) :
    (X.fromSpecStalk x).appLE V ⊤ e τ = (Scheme.ΓSpecIso _).inv (X.presheaf.germ V x hV τ) := by
  rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hV]
  simp only [CommRingCat.comp_apply]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  have : (homOfLE (le_top : X.fromSpecStalk x ⁻¹ᵁ V ≤ ⊤)).op ≫ (homOfLE e).op = 𝟙 _ :=
    Subsingleton.elim _ _
  rw [this, CategoryTheory.Functor.map_id]
  rfl

/-- Germs at the generic point through `Spec k(C) → C`. -/
theorem germ_app_eq {Y : Scheme} (f : C.left ⟶ Y) (U : Y.Opens) (h : f (genericPoint C.left) ∈ U)
    (σ : Γ(Y, U)) (e : ⊤ ≤ (C.left.fromSpecFunctionField ≫ f) ⁻¹ᵁ U) :
    (Scheme.ΓSpecIso _).inv (C.left.presheaf.germ (f ⁻¹ᵁ U) (genericPoint C.left) h (f.app U σ)) =
      (C.left.fromSpecFunctionField ≫ f).appLE U ⊤ e σ := by
  rw [Scheme.Hom.comp_appLE, CommRingCat.comp_apply]
  exact (fromSpecStalk_appLE_top C.left _ _ h _ _).symm

theorem appLE_top_top {R S : CommRingCat} (φ : R ⟶ S) (e : ⊤ ≤ Spec.map φ ⁻¹ᵁ ⊤) (a : Γ(Spec R, ⊤)) :
    (Spec.map φ).appLE ⊤ ⊤ e a = (Spec.map φ).appTop a := by
  rw [Scheme.Hom.appLE]
  have : (homOfLE e).op = (𝟙 (Opposite.op (⊤ : (Spec S).Opens)) : _) := Subsingleton.elim _ _
  rw [this]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- The chart side: `(Spec φ ≫ chart)^*` of the section `r` is `φ(r)`. -/
theorem specMap_chart_appLE_secR {S : CommRingCat} (φ : CommRingCat.of (Rk k) ⟶ S) (r : Rk k)
    (e : ⊤ ≤ (Spec.map φ ≫ chart k) ⁻¹ᵁ ((chart k) ''ᵁ ⊤)) :
    (Spec.map φ ≫ chart k).appLE ((chart k) ''ᵁ ⊤) ⊤ e (secR r) = (Scheme.ΓSpecIso _).inv (φ r) := by
  rw [Scheme.Hom.comp_appLE, CommRingCat.comp_apply, secR, CommRingCat.comp_apply,
    Scheme.Hom.appIso_inv_app_apply, ← CommRingCat.comp_apply]
  erw [Scheme.Hom.map_appLE]
  rw [appLE_top_top, ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
    CommRingCat.comp_apply]

/-- **Main identity.** For `x ∈ C` with `β(x)` in the chart, the germ at `β(x)` of the section `r`,
pulled back by `β` and specialized to the generic point, is `ψ_t(r)`. -/
theorem stalkMap_secR {β : C.left ⟶ P1 k} (hβ : C.left.fromSpecFunctionField ≫ β = ptT C t)
    (x : C.left) (hx : β x ∈ (chart k) ''ᵁ ⊤) (r : Rk k) :
    C.left.presheaf.stalkSpecializes ((genericPoint_spec C.left).specializes (Set.mem_univ x))
      (β.stalkMap x ((P1 k).presheaf.germ _ (β x) hx (secR r))) = psi C t r := by
  rw [Scheme.Hom.germ_stalkMap_apply]
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply]
  have hη : β (genericPoint C.left) ∈ (chart k) ''ᵁ ⊤ :=
    ((genericPoint_spec C.left).specializes (Set.mem_univ x)).map β.continuous |>.mem_open
      ((chart k) ''ᵁ ⊤).isOpen hx
  have e : ⊤ ≤ (C.left.fromSpecFunctionField ≫ β) ⁻¹ᵁ ((chart k) ''ᵁ ⊤) := by
    intro p _
    have hp : C.left.fromSpecFunctionField p ⤳ genericPoint C.left := by
      have : C.left.fromSpecFunctionField p ∈ Set.range C.left.fromSpecFunctionField := ⟨p, rfl⟩
      rw [Scheme.fromSpecFunctionField, Scheme.range_fromSpecStalk] at this
      exact this
    have heq : C.left.fromSpecFunctionField p = genericPoint C.left :=
      (hp.antisymm ((genericPoint_spec C.left).specializes (Set.mem_univ _))).eq
    show β (C.left.fromSpecFunctionField p) ∈ ((chart k) ''ᵁ ⊤ : (P1 k).Opens)
    rw [heq]
    exact hη
  have key := germ_app_eq C β _ hη (secR r) e
  have h2 : ∀ (g : Spec C.left.functionField ⟶ P1 k) (hg : g = ptT C t)
      (e' : ⊤ ≤ g ⁻¹ᵁ ((chart k) ''ᵁ ⊤)),
      g.appLE ((chart k) ''ᵁ ⊤) ⊤ e' (secR r) = (Scheme.ΓSpecIso _).inv (psi C t r) := by
    rintro g rfl e'
    exact specMap_chart_appLE_secR (psi C t) r e'
  rw [h2 _ hβ e] at key
  have := congrArg (Scheme.ΓSpecIso C.left.functionField).hom key
  simpa using this

end MainIdentity


section Unramified

variable {k : Type} [Field k] (C : Over (Spec (CommRingCat.of k))) [IsIntegral C.left]

/-- The structure map `k → 𝒪_{C,x}`. -/
def iotaX (x : C.left) : CommRingCat.of k ⟶ C.left.presheaf.stalk x :=
  (Scheme.ΓSpecIso _).inv ≫ C.hom.appTop ≫ C.left.presheaf.germ ⊤ x trivial

theorem fromSpecStalk_hom (x : C.left) :
    C.left.fromSpecStalk x ≫ C.hom = Spec.map (iotaX C x) := by
  apply ext_of_isAffine
  rw [← cancel_mono (Scheme.ΓSpecIso _).hom, Scheme.ΓSpecIso_naturality,
    ← cancel_epi (Scheme.ΓSpecIso _).inv]
  simp only [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop, iotaX, Category.assoc,
    Iso.inv_hom_id_assoc]
  ext c
  simp

theorem algebraMap_iotaX (x : C.left) (c : k) :
    algebraMap (C.left.presheaf.stalk x) C.left.functionField (iotaX C x c) =
      ZInQ.LeafPush2.ffStructMap C c := by
  simp only [iotaX, ZInQ.LeafPush2.ffStructMap, CommRingCat.hom_comp, RingHom.comp_apply]
  erw [Scheme.algebraMap_germ_eq_germToFunctionField]

/-- **The residue field of a closed point is `k`** (Mathlib `residueFieldIsoBase`, `k` algebraically
closed): every `b ∈ 𝒪_{C,x}` is congruent to a constant mod `𝔪_x`. -/
theorem exists_sub_const_mem [IsAlgClosed k] [LocallyOfFiniteType C.hom] (x : C.left)
    (hx : IsClosed ({x} : Set C.left)) (b : C.left.presheaf.stalk x) :
    ∃ c : k, b - iotaX C x c ∈ IsLocalRing.maximalIdeal (C.left.presheaf.stalk x) := by
  set e := residueFieldIsoBase C.hom x hx
  have hφ : e.inv = iotaX C x ≫ C.left.residue x := by
    apply Spec.map_injective
    rw [SpecMap_residueFieldIsoBase_inv, Spec.map_comp, Scheme.fromSpecResidueField,
      Category.assoc, fromSpecStalk_hom]
  refine ⟨e.hom (C.left.residue x b), ?_⟩
  rw [← IsLocalRing.residue_eq_zero_iff]
  have : C.left.residue x (iotaX C x (e.hom (C.left.residue x b))) = C.left.residue x b := by
    rw [← CommRingCat.comp_apply, ← hφ, ← CommRingCat.comp_apply, e.hom_inv_id]
    rfl
  rw [map_sub]; exact sub_eq_zero.mpr this.symm

end Unramified

end JavanpeykarFix
