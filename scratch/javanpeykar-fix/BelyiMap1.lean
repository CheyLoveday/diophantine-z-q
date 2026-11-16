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

end JavanpeykarFix
