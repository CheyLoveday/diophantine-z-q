import ZInQKernel.Contrib.OneProof.ColmezProperModel.MilneLeaf
import ZInQKernel.Contrib.OneProof.ColmezProperModel.Colmez

/-!
# A proper model over `O_F` from Milne's Theorem 7.1

For a finite extension `F` of `ℚ_p` with ring of integers `O_F` (`OF p F`, the integral closure of
`ℤ_p` in `F`) and an abelian variety `A` over `F`, this file builds a proper `O_F`-scheme `𝒳`
whose generic fibre is `A`, from a closed immersion `i : A ⟶ ℙᴺ_F` over `F`
(`MilneThm71Projective`):

* `F = O_F[1/p]` (`isLocalization_away`): every `x ∈ F` has a multiple `p ^ n * x` integral over
  `ℤ_p`. Hence `Spec F ⟶ Spec O_F` is an open immersion (`isOpenImmersion_spec`).
* `ℙᴺ_ℤ ⟶ Spec ℤ` is proper (`isProper_projSpaceZ`), so
  `ℙᴺ_{O_F} := ℙᴺ_ℤ ×_{Spec ℤ} Spec O_F` is proper over `O_F`, and `ℙᴺ_F ⟶ ℙᴺ_{O_F}` is the base
  change of `Spec F ⟶ Spec O_F` (`isPullback_pnMap`), an open immersion.
* `𝒳` is the scheme-theoretic image of `j : A ⟶ ℙᴺ_F ⟶ ℙᴺ_{O_F}`, the closure of `A` in
  `ℙᴺ_{O_F}`. Its ideal sheaf restricts on `ℙᴺ_F` to the ideal sheaf of `i` (the kernel of a
  quasi-compact morphism commutes with restriction to an open subscheme), so `A` is the pullback
  of `𝒳 ⟶ ℙᴺ_{O_F}` along `ℙᴺ_F ⟶ ℙᴺ_{O_F}`; pasting with the square of `ℙᴺ_F ⟶ ℙᴺ_{O_F}`
  identifies the generic fibre of `𝒳 ⟶ Spec O_F` with `A` over `Spec F` (`exists_properModel`).

Main statement: `properModelExists_of_milne : MilneThm71Projective → ProperModelExists`.
-/

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

namespace ZInQ.Contrib.ColmezProperModel

/- The total-degree grading of `MvPolynomial σ R` (`MvPolynomial.gradedAlgebra`), as in
`MilneLeaf.lean`. -/
attribute [local instance] MvPolynomial.gradedAlgebra

namespace MilneModel

/-! ### `F = O_F[1/p]` -/

section Localization

variable (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F]

/-- `p ≠ 0` in `F`. -/
theorem cast_p_ne_zero : (p : F) ≠ 0 := by
  rw [← map_natCast (algebraMap ℚ_[p] F)]
  exact (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)

/-- Every `x ∈ F` has a multiple `p ^ n * x` in `O_F`. -/
theorem exists_pow_mul_mem [FiniteDimensional ℚ_[p] F] (x : F) :
    ∃ n : ℕ, (p : F) ^ n * x ∈ OF p F := by
  have hx : IsIntegral ℚ_[p] x := IsIntegral.of_finite ℚ_[p] x
  let _ := algZp p F
  have : IsScalarTower ℤ_[p] ℚ_[p] F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨⟨m, hm⟩, hmx⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (nonZeroDivisors ℤ_[p]) x hx
  have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
  refine ⟨m.valuation, ?_⟩
  rw [mem_OF_iff]
  have hu : (((PadicInt.unitCoeff hm0)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * m = (p : ℤ_[p]) ^ m.valuation :=
    (congrArg (fun y => (((PadicInt.unitCoeff hm0)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * y)
      (PadicInt.unitCoeff_spec hm0)).trans (Units.inv_mul_cancel_left _ _)
  have key : (p : F) ^ m.valuation * x =
      (((PadicInt.unitCoeff hm0)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) • (m • x) := by
    rw [smul_smul, hu, Algebra.smul_def, map_pow, map_natCast]
  rw [key, Algebra.smul_def]
  exact isIntegral_algebraMap.mul hmx

/-- **`F = O_F[1/p]`.** -/
theorem isLocalization_away [FiniteDimensional ℚ_[p] F] :
    IsLocalization.Away ((p : ℕ) : OF p F) F := by
  refine IsLocalization.Away.mk _ ?_ ?_ ?_
  · rw [map_natCast]
    exact (cast_p_ne_zero p F).isUnit
  · intro s
    obtain ⟨n, hn⟩ := exists_pow_mul_mem p F s
    refine ⟨n, ⟨_, hn⟩, ?_⟩
    rw [map_natCast, mul_comm]
    rfl
  · intro a b h
    exact ⟨0, by rw [pow_zero, one_mul, one_mul]; exact Subtype.ext h⟩

/-- **`Spec F ⟶ Spec O_F` is an open immersion.** -/
theorem isOpenImmersion_spec [FiniteDimensional ℚ_[p] F] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap (OF p F) F))) :=
  have := isLocalization_away p F
  IsOpenImmersion.of_isLocalization ((p : ℕ) : OF p F)

end Localization

/-! ### `ℙᴺ` over a base -/

section Projective

variable (N : ℕ)

/-- The degree-zero part of `ℤ[x_0, …, x_N]` consists of the constants. -/
theorem gradeZero_surjective :
    Function.Surjective (algebraMap ℤ (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℤ 0)) := by
  rintro ⟨x, hx⟩
  obtain ⟨c, hc⟩ : ∃ c : ℤ, x = MvPolynomial.C c := by
    by_cases h0 : x = 0
    · exact ⟨0, by rw [h0, map_zero]⟩
    · exact ⟨_, (MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp
        (((MvPolynomial.mem_homogeneousSubmodule _ _).mp hx).totalDegree h0)⟩
  refine ⟨c, Subtype.ext ?_⟩
  have e := congrArg (fun f : ℤ →+* MvPolynomial (Fin (N + 1)) ℤ => f c)
    (RingHom.ext_int ((algebraMap (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℤ 0)
      (MvPolynomial (Fin (N + 1)) ℤ)).comp
        (algebraMap ℤ (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℤ 0))) MvPolynomial.C)
  exact e.trans hc.symm

/-- `ℤ[x_0, …, x_N]` is of finite type over its degree-zero part. -/
theorem finiteType_gradeZero :
    Algebra.FiniteType (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℤ 0)
      (MvPolynomial (Fin (N + 1)) ℤ) :=
  @Algebra.FiniteType.of_restrictScalars_finiteType ℤ
    (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℤ 0) (MvPolynomial (Fin (N + 1)) ℤ)
    _ _ _ _ _ _ (IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)) _

attribute [local instance] finiteType_gradeZero

/-- **`ℙᴺ_ℤ ⟶ Spec ℤ` is proper.** -/
theorem isProper_projSpaceZ : IsProper (specZIsTerminal.from (projSpaceZ N)) := by
  have h : specZIsTerminal.from (projSpaceZ N) =
      Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℤ) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap ℤ (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℤ 0))) :=
    specZIsTerminal.hom_ext _ _
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap ℤ (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℤ 0)))) :=
    IsClosedImmersion.spec_of_surjective _ (gradeZero_surjective N)
  rw [h]
  infer_instance

/-- `ℙᴺ_X := ℙᴺ_ℤ ×_{Spec ℤ} X`. -/
abbrev PN (X : Scheme.{0}) : Scheme.{0} :=
  pullback (specZIsTerminal.from (projSpaceZ N)) (specZIsTerminal.from X)

/-- `ℙᴺ_Y ⟶ ℙᴺ_X` over `f : Y ⟶ X`. -/
def pnMap {X Y : Scheme.{0}} (f : Y ⟶ X) : PN N Y ⟶ PN N X :=
  pullback.map _ _ _ _ (𝟙 _) f (𝟙 _) (by simp) (specZIsTerminal.hom_ext _ _)

/-- `ℙᴺ_Y` is the base change of `ℙᴺ_X` along `f : Y ⟶ X`. -/
theorem isPullback_pnMap {X Y : Scheme.{0}} (f : Y ⟶ X) :
    IsPullback (pnMap N f) (pullback.snd _ _) (pullback.snd _ _) f := by
  refine IsPullback.of_right ?_ ?_ (IsPullback.of_hasPullback _ _)
  · have h1 : pnMap N f ≫ pullback.fst _ _ = pullback.fst _ _ := by simp [pnMap]
    have h2 : f ≫ specZIsTerminal.from X = specZIsTerminal.from Y := specZIsTerminal.hom_ext _ _
    rw [h1, h2]
    exact IsPullback.of_hasPullback _ _
  · simp [pnMap]

end Projective

/-! ### The model -/

section Model

attribute [local instance] isProper_projSpaceZ

variable {O F : Type} [CommRing O] [Field F] [Algebra O F]
  [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap O F)))]

/-- **A proper model from a projective embedding.** Let `Spec F ⟶ Spec O` be an open immersion and
`i : A ⟶ ℙᴺ_F` a closed immersion over `F`. The scheme-theoretic image `𝒳` of
`A ⟶ ℙᴺ_F ⟶ ℙᴺ_O` is proper over `O`, and its generic fibre is `A` over `Spec F`. -/
theorem exists_properModel (N : ℕ) (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F)
    (i : A.X.left ⟶ PN N (Spec (CommRingCat.of F))) [IsClosedImmersion i]
    (hi : i ≫ pullback.snd _ _ = A.X.hom) :
    ∃ (𝒳 : Scheme) (π : 𝒳 ⟶ Spec (CommRingCat.of O)) (_ : IsProper π)
      (e : pullback π (Spec.map (CommRingCat.ofHom (algebraMap O F))) ≅ A.X.left),
      e.hom ≫ A.X.hom = pullback.snd _ _ := by
  have hsq := isPullback_pnMap N (Spec.map (CommRingCat.ofHom (algebraMap O F)))
  have : IsOpenImmersion (pnMap N (Spec.map (CommRingCat.ofHom (algebraMap O F)))) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hsq.flip inferInstance
  have : QuasiCompact (pnMap N (Spec.map (CommRingCat.ofHom (algebraMap O F)))) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hsq.flip inferInstance
  set φ := pnMap N (Spec.map (CommRingCat.ofHom (algebraMap O F)))
  set j := i ≫ φ
  have hpb : IsPullback i (𝟙 A.X.left) φ j := by
    have h := (IsPullback.id_vert i).paste_horiz (IsKernelPair.id_of_mono φ)
    rwa [Category.comp_id] at h
  have hker : (Scheme.Hom.ker j).comap φ = Scheme.Hom.ker i := by
    refine Scheme.IdealSheafData.ext (funext fun W => ?_)
    rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
      Scheme.ker_ideal_of_isPullback_of_isOpenImmersion j i (𝟙 _) φ hpb W]
  have h1 : IsPullback i j.toImage φ j.imageι :=
    isPullback_of_isClosedImmersion i j.imageι j.toImage φ (Scheme.Hom.toImage_imageι j).symm
      (by rw [Scheme.Hom.imageι, Scheme.IdealSheafData.ker_subschemeι]; exact hker)
  have h2 := h1.flip.paste_vert hsq
  refine ⟨j.image, j.imageι ≫ pullback.snd _ _, inferInstance, h2.isoPullback.symm, ?_⟩
  rw [Iso.symm_hom, ← hi]
  exact h2.isoPullback_inv_snd

end Model

end MilneModel

open MilneModel in
/-- **`ProperModelExists` from Milne's Theorem 7.1.** For a finite extension `F` of `ℚ_p` and an
abelian variety `A` over `F`, the closure of `A ⊆ ℙᴺ_F` in `ℙᴺ_{O_F}` (the scheme-theoretic image) is
a proper model of `A` over `O_F` with generic fibre `A`. -/
theorem properModelExists_of_milne (hM : MilneThm71Projective) : ProperModelExists := by
  intro p _ F _ _ _ A
  obtain ⟨N, i, hi, hiA⟩ := hM F A
  have := hi
  have := isOpenImmersion_spec p F
  exact exists_properModel N A i hiA

end ZInQ.Contrib.ColmezProperModel
