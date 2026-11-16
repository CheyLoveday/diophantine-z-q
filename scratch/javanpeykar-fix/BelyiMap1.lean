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

end JavanpeykarFix
