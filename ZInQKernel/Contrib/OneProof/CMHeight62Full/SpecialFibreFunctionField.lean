import Mathlib
import ZInQKernel.Contrib.OneProof.CMHeight62Full.GroupCurveNotP1
import ZInQKernel.Contrib.OneProof.CMHeight62Full.LocalStructure
import ZInQKernel.Contrib.OneProof.CMHeight62Full.WeierstrassDVR

/-!
# The special fibre: function field and landing (node N9-bridge, parts B1 and B2)

**B1.** The function field of the special fibre at the identity point has transcendence degree at
most one over the residue field, in the `TrdegLeOne` form of `GroupCurveNotP1.lean`.

* `trdegLeOne_of_formallyUnramified`: if `B` is a standard smooth `k`-algebra of relative
  dimension one and the field `K` is a formally unramified, essentially finite type `B`-algebra,
  then `TrdegLeOne k K`. The free variable `t` of a submersive presentation spans `Ω[B⁄k]`, so `B`
  is formally unramified over `k[X]` (`X ↦ t`); hence `K` is finite over the fraction field of
  `k[t]`, and `trdeg k K ≤ 1`.
* `trdegLeOne_of_isLocalization`: the same for the fraction field of a localization of `B`.
* `trdegLeOne_of_baseChange`: for `A₀` standard smooth of relative dimension one over `R` and a
  field `K` over `A₀` and over a field `k` under `R`, through the base change `k ⊗[R] A₀`.
* `trdegLeOne_specialFibre`: `κ_w = Frac(A/ϖA)`, `A` the localization of `A₀` at the point of the
  section `σ` over the closed point (the setting of `LocalStructure.lean`).

**B2.** Reductions of elements of `M_n` land in `L(n ē)`.

* `liftValuationSubring`: the composite valuation ring `Õ = {g ∈ 𝒪_w | ḡ ∈ O}` of `Ω`;
  `algebraMap_mem_liftValuationSubring`: it contains `R` when `O` is a constant place.
* `mem_centre_of_hartogs`: Hartogs at a centre, with the height-one primes through `ϖ` controlled
  by `w` and the others by regularity on the generic fibre.
* `reduce_mem_polePart`: given centres dominated by `Õ` for the constant places `O ≠ ē`, the
  reduction `f̄` of `f ∈ M_n` has no pole off `ē` and `f̄ t̄ⁿ ∈ ē`.

Only Mathlib and the earlier files of this directory are used.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CMHeight62Full

namespace SpecialFibreFunctionField

open Algebra Polynomial

section Trdeg

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

theorem trdegLeOne_of_isAlgebraic_adjoin (t : K)
    (ht : Algebra.IsAlgebraic (Algebra.adjoin k {t}) K) : TrdegLeOne k K := by
  intro x hx
  have hle : Algebra.trdeg k K ≤ 1 := by
    have := Algebra.IsAlgebraic.trdeg_le_cardinalMk k ({t} : Set K)
    simpa using this
  have hind : AlgebraicIndependent k (Subtype.val : ({x} : Set K) → K) :=
    algebraicIndependent_unique_type_iff.2 hx
  have hb := hind.isTranscendenceBasis_of_trdeg_le_of_finite (by simpa using hle)
  have := hb.isAlgebraic
  rwa [Subtype.range_coe_subtype, Set.ofPred_mem_eq] at this

end Trdeg

section Core

variable {k B K : Type*} [Field k] [CommRing B] [Field K] [Algebra k B] [Algebra B K]
  [Algebra k K] [IsScalarTower k B K]

theorem trdegLeOne_of_formallyUnramified [IsStandardSmoothOfRelativeDimension 1 k B]
    [FormallyUnramified B K] [EssFiniteType B K] : TrdegLeOne k K := by
  obtain ⟨ι, σ, _, _, P, -⟩ := IsStandardSmoothOfRelativeDimension.out (n := 1) (R := k) (S := B)
  have : Nontrivial B := (algebraMap B K).domain_nontrivial
  have hrank := IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := k) (S := B) 1
  have hcard := P.basisKaehler.mk_eq_rank
  rw [hrank] at hcard
  have h1 : Cardinal.mk ((Set.range P.map)ᶜ : Set ι) = 1 := by
    simpa using hcard
  obtain ⟨hsub, hne⟩ := Cardinal.eq_one_iff_unique.1 h1
  obtain ⟨i₀⟩ := hne
  let : Unique ((Set.range P.map)ᶜ : Set ι) := @uniqueOfSubsingleton _ hsub i₀
  set t : B := P.val i₀ with ht
  let alg1 : Algebra k[X] B := (aeval t).toRingHom.toAlgebra
  have : IsScalarTower k k[X] B := IsScalarTower.of_algebraMap_eq fun c => by
    rw [RingHom.algebraMap_toAlgebra, Polynomial.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply]
    exact (aeval_C t c).symm
  have hspan : ∀ b : B, KaehlerDifferential.D k B b ∈
      Submodule.span B {KaehlerDifferential.D k B t} := by
    intro b
    have htop := P.basisKaehler.span_eq
    rw [Set.range_unique, SubmersivePresentation.basisKaehler_apply,
      show (default : ((Set.range P.map)ᶜ : Set ι)) = i₀ from Subsingleton.elim _ _] at htop
    rw [htop]
    exact Submodule.mem_top
  have hD : ∀ b : B, KaehlerDifferential.D k[X] B b = 0 := by
    intro b
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hspan b)
    have h2 := congrArg (KaehlerDifferential.map k k[X] B B) hc
    rw [map_smul, KaehlerDifferential.map_D, KaehlerDifferential.map_D] at h2
    have h3 : KaehlerDifferential.D k[X] B (algebraMap B B t) = 0 := by
      have : algebraMap B B t = algebraMap k[X] B X := by
        rw [Algebra.algebraMap_self, RingHom.id_apply, RingHom.algebraMap_toAlgebra]
        simp [ht]
      rw [this, Derivation.map_algebraMap]
    rw [h3, smul_zero, Algebra.algebraMap_self, RingHom.id_apply] at h2
    exact h2.symm
  have hΩ : Subsingleton (Ω[B⁄k[X]]) := by
    refine subsingleton_of_forall_eq 0 fun ω => ?_
    have hω : ω ∈ Submodule.span B (Set.range (KaehlerDifferential.D k[X] B)) := by
      rw [KaehlerDifferential.span_range_derivation]; exact Submodule.mem_top
    induction hω using Submodule.span_induction with
    | mem x hx => obtain ⟨b, rfl⟩ := hx; exact hD b
    | zero => rfl
    | add x y _ _ hx hy => rw [hx, hy, add_zero]
    | smul a x _ hx => rw [hx, smul_zero]
  have : FormallyUnramified k[X] B := (formallyUnramified_iff _ _).2 hΩ
  let alg2 : Algebra k[X] K := ((algebraMap B K).comp (algebraMap k[X] B)).toAlgebra
  have : IsScalarTower k[X] B K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : FormallyUnramified k[X] K := FormallyUnramified.comp k[X] B K
  have : FiniteType k B := Generators.finiteType P.toGenerators
  have : FiniteType k[X] B := FiniteType.of_restrictScalars_finiteType k k[X] B
  have : EssFiniteType k[X] B := EssFiniteType.of_finiteType _ _
  have : EssFiniteType k[X] K := EssFiniteType.comp k[X] B K
  set t' : K := algebraMap B K t with ht'
  let A := Algebra.adjoin k ({t'} : Set K)
  let a₀ : A := ⟨t', Algebra.self_mem_adjoin_singleton k t'⟩
  let alg3 : Algebra k[X] A := (aeval a₀).toRingHom.toAlgebra
  have : IsScalarTower k[X] A K := IsScalarTower.of_algebraMap_eq fun p => by
    change algebraMap B K (aeval t p) = ((aeval a₀ p : A) : K)
    rw [Polynomial.aeval_subalgebra_coe]
    change algebraMap B K (aeval t p) = aeval t' p
    rw [ht', ← IsScalarTower.coe_toAlgHom' k B K, Polynomial.aeval_algHom_apply]
  have : FormallyUnramified A K := FormallyUnramified.of_restrictScalars k[X] A K
  have : EssFiniteType A K := EssFiniteType.of_comp k[X] A K
  let : Algebra (FractionRing A) K := FractionRing.liftAlgebra A K
  have : IsScalarTower A (FractionRing A) K := FractionRing.isScalarTower_liftAlgebra A K
  have : FormallyUnramified (FractionRing A) K :=
    FormallyUnramified.of_restrictScalars A (FractionRing A) K
  have : EssFiniteType (FractionRing A) K := EssFiniteType.of_comp A (FractionRing A) K
  have : Module.Finite (FractionRing A) K := FormallyUnramified.finite_of_free _ _
  have : Algebra.IsAlgebraic A (FractionRing A) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors A)
  have : Algebra.IsAlgebraic A K := Algebra.IsAlgebraic.trans A (FractionRing A) K
  exact trdegLeOne_of_isAlgebraic_adjoin t' this

theorem trdegLeOne_of_isLocalization [IsStandardSmoothOfRelativeDimension 1 k B]
    {C : Type*} [CommRing C] [IsDomain C] [Algebra B C] (M : Submonoid B) [IsLocalization M C]
    [Algebra C K] [IsFractionRing C K] [IsScalarTower B C K] : TrdegLeOne k K := by
  have : FormallyUnramified B C := .of_isLocalization M
  have : FormallyUnramified C K := .of_isLocalization (nonZeroDivisors C)
  have : FormallyUnramified B K := .comp B C K
  have : EssFiniteType B C := .of_isLocalization C M
  have : EssFiniteType C K := .of_isLocalization K (nonZeroDivisors C)
  have : EssFiniteType B K := .comp B C K
  exact trdegLeOne_of_formallyUnramified (B := B)

end Core

section BaseChange

open scoped TensorProduct

theorem trdegLeOne_of_baseChange {R k A₀ K : Type*} [CommRing R] [Field k] [CommRing A₀]
    [Field K] [Algebra R k] [Algebra R A₀] [Algebra R K] [Algebra k K] [Algebra A₀ K]
    [IsScalarTower R k K] [IsScalarTower R A₀ K] [IsStandardSmoothOfRelativeDimension 1 R A₀]
    [FormallyUnramified A₀ K] [EssFiniteType A₀ K] : TrdegLeOne k K := by
  have : IsStandardSmoothOfRelativeDimension 1 k (k ⊗[R] A₀) :=
    IsStandardSmoothOfRelativeDimension.baseChange 1 k
  let f : k ⊗[R] A₀ →ₐ[k] K := Algebra.TensorProduct.lift (Algebra.ofId k K)
    (IsScalarTower.toAlgHom R A₀ K) fun _ _ => Commute.all _ _
  let _ : Algebra (k ⊗[R] A₀) K := f.toRingHom.toAlgebra
  have : IsScalarTower k (k ⊗[R] A₀) K :=
    IsScalarTower.of_algebraMap_eq fun c => (f.commutes c).symm
  let _ : Algebra A₀ (k ⊗[R] A₀) := Algebra.TensorProduct.includeRight.toRingHom.toAlgebra
  have : IsScalarTower A₀ (k ⊗[R] A₀) K := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap A₀ K a = f (1 ⊗ₜ a)
    simp [f]
  have : FormallyUnramified (k ⊗[R] A₀) K := .of_restrictScalars A₀ (k ⊗[R] A₀) K
  have : EssFiniteType (k ⊗[R] A₀) K := .of_comp A₀ (k ⊗[R] A₀) K
  exact trdegLeOne_of_formallyUnramified (B := k ⊗[R] A₀)

end BaseChange

section SpecialFibre

open IsLocalRing

theorem trdegLeOne_quotient_localization {R : Type*} [CommRing R] [IsLocalRing R]
    {A₀ : Type*} [CommRing A₀] [Algebra R A₀] [IsStandardSmoothOfRelativeDimension 1 R A₀]
    {A : Type*} [CommRing A] [Algebra A₀ A] [Algebra R A] [IsScalarTower R A₀ A]
    (M : Submonoid A₀) [IsLocalization M A] (I : Ideal A) [IsDomain (A ⧸ I)]
    [Algebra (ResidueField R) (FractionRing (A ⧸ I))]
    [IsScalarTower R (ResidueField R) (FractionRing (A ⧸ I))] :
    TrdegLeOne (ResidueField R) (FractionRing (A ⧸ I)) := by
  have : FormallyUnramified A₀ A := .of_isLocalization M
  have : FormallyUnramified A (A ⧸ I) := FormallyUnramified.quotient I
  have : FormallyUnramified (A ⧸ I) (FractionRing (A ⧸ I)) :=
    .of_isLocalization (nonZeroDivisors (A ⧸ I))
  have : FormallyUnramified A (FractionRing (A ⧸ I)) := .comp A (A ⧸ I) _
  have : FormallyUnramified A₀ (FractionRing (A ⧸ I)) := .comp A₀ A _
  have : EssFiniteType A₀ A := .of_isLocalization A M
  have : FiniteType A (A ⧸ I) :=
    FiniteType.of_surjective (Ideal.Quotient.mkₐ A I) Ideal.Quotient.mk_surjective
  have : EssFiniteType A (A ⧸ I) := .of_finiteType _ _
  have : EssFiniteType (A ⧸ I) (FractionRing (A ⧸ I)) :=
    .of_isLocalization _ (nonZeroDivisors (A ⧸ I))
  have : EssFiniteType A (FractionRing (A ⧸ I)) := .comp A (A ⧸ I) _
  have : EssFiniteType A₀ (FractionRing (A ⧸ I)) := .comp A₀ A _
  exact trdegLeOne_of_baseChange (R := R) (A₀ := A₀)

/-- **B1.** The function field `κ_w = Frac(A/ϖA)` of the special fibre at the identity point has
transcendence degree at most one over the residue field of `R`. Here `A₀` is a standard smooth
`R`-algebra of relative dimension one with a section `σ`, and `A` is its localization at the
point of the section over the closed point. -/
theorem trdegLeOne_specialFibre {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {A₀ : Type*} [CommRing A₀] [Algebra R A₀]
    [IsStandardSmoothOfRelativeDimension 1 R A₀] (σ : A₀ →ₐ[R] R) (ϖ : R)
    [IsDomain (Localization.AtPrime (sectionPrime σ) ⧸
      Ideal.span {algebraMap R (Localization.AtPrime (sectionPrime σ)) ϖ})]
    [Algebra (ResidueField R) (FractionRing (Localization.AtPrime (sectionPrime σ) ⧸
      Ideal.span {algebraMap R (Localization.AtPrime (sectionPrime σ)) ϖ}))]
    [IsScalarTower R (ResidueField R) (FractionRing (Localization.AtPrime (sectionPrime σ) ⧸
      Ideal.span {algebraMap R (Localization.AtPrime (sectionPrime σ)) ϖ}))] :
    TrdegLeOne (ResidueField R) (FractionRing (Localization.AtPrime (sectionPrime σ) ⧸
      Ideal.span {algebraMap R (Localization.AtPrime (sectionPrime σ)) ϖ})) :=
  trdegLeOne_quotient_localization (sectionPrime σ).primeCompl _

end SpecialFibre

section Landing

open IsLocalRing

variable {Ω : Type*} [Field Ω] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (w : Valuation Ω Γ₀)

theorem residue_inv_mem {O : ValuationSubring (ResidueField w.valuationSubring)} {g : Ω}
    (hg : g ∈ w.valuationSubring) (hr : residue w.valuationSubring ⟨g, hg⟩ ∉ O) :
    ∃ h : g⁻¹ ∈ w.valuationSubring, residue w.valuationSubring ⟨g⁻¹, h⟩ ∈ O := by
  have hne : residue w.valuationSubring ⟨g, hg⟩ ≠ 0 := fun h => hr (h ▸ O.zero_mem)
  have hu : IsUnit (⟨g, hg⟩ : w.valuationSubring) := by
    by_contra hnu
    exact hne ((residue_eq_zero_iff _).2 ((mem_maximalIdeal _).2 hnu))
  obtain ⟨u, hu'⟩ := hu
  have hmul : (⟨g, hg⟩ : w.valuationSubring) * ↑u⁻¹ = 1 := by
    rw [← hu']; exact u.mul_inv
  have hg0 : g ≠ 0 := by
    intro h0
    have := congrArg Subtype.val hmul
    simp [h0] at this
  have hval : ((↑u⁻¹ : w.valuationSubring) : Ω) = g⁻¹ := by
    have := congrArg Subtype.val hmul
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at this
    exact (eq_inv_of_mul_eq_one_right this)
  refine ⟨hval ▸ (↑u⁻¹ : w.valuationSubring).2, ?_⟩
  have heq : (⟨g⁻¹, hval ▸ (↑u⁻¹ : w.valuationSubring).2⟩ : w.valuationSubring) = ↑u⁻¹ :=
    Subtype.ext hval.symm
  have hres : residue w.valuationSubring ↑u⁻¹ = (residue w.valuationSubring ⟨g, hg⟩)⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← map_mul, hmul, map_one]
  rw [heq, hres]
  exact (O.mem_or_inv_mem _).resolve_left hr

theorem inv_mem_of_not_mem {O : ValuationSubring (ResidueField w.valuationSubring)} {g : Ω}
    (hg : g ∉ w.valuationSubring) :
    ∃ h : g⁻¹ ∈ w.valuationSubring, residue w.valuationSubring ⟨g⁻¹, h⟩ ∈ O := by
  have hi : g⁻¹ ∈ w.valuationSubring := (w.valuationSubring.mem_or_inv_mem g).resolve_left hg
  refine ⟨hi, ?_⟩
  have hnu : ¬ IsUnit (⟨g⁻¹, hi⟩ : w.valuationSubring) := by
    rintro ⟨u, hu⟩
    apply hg
    have hg0 : g ≠ 0 := by
      rintro rfl
      exact hg w.valuationSubring.zero_mem
    have hmul : ((u : w.valuationSubring) : Ω) * ((↑u⁻¹ : w.valuationSubring) : Ω) = 1 := by
      rw [← MulMemClass.coe_mul, u.mul_inv, OneMemClass.coe_one]
    rw [hu] at hmul
    have : ((↑u⁻¹ : w.valuationSubring) : Ω) = g := by
      have h2 : g⁻¹ * ((↑u⁻¹ : w.valuationSubring) : Ω) = g⁻¹ * g := by
        rw [hmul, inv_mul_cancel₀ hg0]
      exact mul_left_cancel₀ (inv_ne_zero hg0) h2
    exact this ▸ (↑u⁻¹ : w.valuationSubring).2
  rw [(residue_eq_zero_iff _).2 ((mem_maximalIdeal _).2 hnu)]
  exact O.zero_mem

/-- The composite valuation ring `Õ = {g ∈ 𝒪_w | ḡ ∈ O}` of a valuation ring `O` of the residue
field `κ_w` of `w`. -/
def liftValuationSubring (O : ValuationSubring (ResidueField w.valuationSubring)) :
    ValuationSubring Ω where
  carrier := {g | ∃ h : g ∈ w.valuationSubring, residue w.valuationSubring ⟨g, h⟩ ∈ O}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, ?_⟩
    have : (⟨a * b, mul_mem ha hb⟩ : w.valuationSubring) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [this, map_mul]
    exact mul_mem ha' hb'
  one_mem' := by
    refine ⟨one_mem _, ?_⟩
    have : (⟨1, one_mem _⟩ : w.valuationSubring) = 1 := rfl
    rw [this, map_one]
    exact one_mem O
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨add_mem ha hb, ?_⟩
    have : (⟨a + b, add_mem ha hb⟩ : w.valuationSubring) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
    rw [this, map_add]
    exact add_mem ha' hb'
  zero_mem' := by
    refine ⟨zero_mem _, ?_⟩
    have : (⟨0, zero_mem _⟩ : w.valuationSubring) = 0 := rfl
    rw [this, map_zero]
    exact zero_mem O
  neg_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨neg_mem ha, ?_⟩
    have : (⟨-a, neg_mem ha⟩ : w.valuationSubring) = -⟨a, ha⟩ := rfl
    rw [this, map_neg]
    exact neg_mem ha'
  mem_or_inv_mem' := by
    intro g
    by_cases hg : g ∈ w.valuationSubring
    · by_cases hr : residue w.valuationSubring ⟨g, hg⟩ ∈ O
      · exact Or.inl ⟨hg, hr⟩
      · exact Or.inr (residue_inv_mem w hg hr)
    · exact Or.inr (inv_mem_of_not_mem w hg)

variable {w}

theorem mem_liftValuationSubring {O : ValuationSubring (ResidueField w.valuationSubring)}
    {g : Ω} (hg : w g ≤ 1) : g ∈ liftValuationSubring w O ↔ reduce w g hg ∈ O :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨(w.mem_valuationSubring_iff g).2 hg, h⟩⟩

theorem liftValuationSubring_le (O : ValuationSubring (ResidueField w.valuationSubring)) :
    liftValuationSubring w O ≤ w.valuationSubring := fun _ ⟨h, _⟩ => h

/-- `Õ` contains `R` when `O` contains the image of the residue field of `R`. -/
theorem algebraMap_mem_liftValuationSubring {R : Type*} [CommRing R] [IsLocalRing R]
    [Algebra R Ω] (hR : ∀ r : R, w (algebraMap R Ω r) ≤ 1)
    (hm : ∀ r ∈ maximalIdeal R, w (algebraMap R Ω r) < 1)
    {O : ValuationSubring (ResidueField w.valuationSubring)}
    (hO : ∀ c : ResidueField R, residueHom w hR hm c ∈ O) (r : R) :
    algebraMap R Ω r ∈ liftValuationSubring w O := by
  refine (mem_liftValuationSubring (hR r)).2 ?_
  have := isLocalHom_toIntegers w hR hm
  have h : reduce w (algebraMap R Ω r) (hR r) = residueHom w hR hm (residue R r) := by
    rw [residueHom, ResidueField.map_residue]
    rfl
  rw [h]
  exact hO _

/-- **Landing at a centre.** If a subring `A_c` of `Ω` is dominated by `Õ`, every element of
`A_c` with `w ≤ 1` reduces into `O`. -/
theorem reduce_mem_of_mem_centre {O : ValuationSubring (ResidueField w.valuationSubring)}
    {Ac : Subring Ω} (hdom : ∀ a ∈ Ac, a ∈ liftValuationSubring w O) {f : Ω} (hf : w f ≤ 1)
    (hfA : f ∈ Ac) : reduce w f hf ∈ O :=
  (mem_liftValuationSubring hf).1 (hdom f hfA)

/-- **Hartogs at a centre.** In a subring `A_c` of `Ω` with the Hartogs property, an element
regular at every height-one prime lies in `A_c`. The height-one primes through `ϖ` are controlled
by `w ≤ 1` (the identity component is the only component of the special fibre through the
centre), the others by the regularity of `f` on the generic fibre. -/
theorem mem_centre_of_hartogs {Ac : Subring Ω} (ϖ : Ac)
    (hhart : ∀ g : Ω, (∀ 𝔮 : Ideal Ac, 𝔮.IsPrime → 𝔮.height = 1 →
      ∃ r s : Ac, s ∉ 𝔮 ∧ (s : Ω) * g = r) → g ∈ Ac)
    (hvert : ∀ 𝔮 : Ideal Ac, 𝔮.IsPrime → 𝔮.height = 1 → ϖ ∈ 𝔮 → ∀ g : Ω, w g ≤ 1 →
      ∃ r s : Ac, s ∉ 𝔮 ∧ (s : Ω) * g = r)
    {f : Ω} (hf : w f ≤ 1)
    (hhor : ∀ 𝔮 : Ideal Ac, 𝔮.IsPrime → 𝔮.height = 1 → ϖ ∉ 𝔮 →
      ∃ r s : Ac, s ∉ 𝔮 ∧ (s : Ω) * f = r) : f ∈ Ac := by
  refine hhart f fun 𝔮 hq h1 => ?_
  by_cases hϖ : ϖ ∈ 𝔮
  · exact hvert 𝔮 hq h1 hϖ f hf
  · exact hhor 𝔮 hq h1 hϖ

/-- **B2 (algebraic landing).** Let `f ∈ M_n`: `w f ≤ 1` and `f tⁿ ∈ A`, where `A` is the local
ring at the identity point and its image reduces into `ē`. Suppose every constant place
`O ≠ ē` of `κ_w` has a centre `A_c` (from the valuative criterion), dominated by `Õ`, with the
Hartogs property, whose height-one primes through `ϖ` are controlled by `w` and at whose other
height-one primes `f` is regular. Then `f̄` has no pole at any `O ≠ ē` and `f̄ t̄ⁿ ∈ ē`: the
reduction lies in `L(n ē)`. -/
theorem reduce_mem_polePart {k : Type*} [Field k] [Algebra k (ResidueField w.valuationSubring)]
    (ē : ValuationSubring (ResidueField w.valuationSubring)) {A : Type*} [CommRing A]
    [Algebra A Ω] (hAē : ∀ a : A, ∃ h : w (algebraMap A Ω a) ≤ 1,
      reduce w (algebraMap A Ω a) h ∈ ē)
    {t : Ω} (ht : w t ≤ 1) {n : ℕ} {f : Ω} (hf : w f ≤ 1)
    (hpole : ∃ a : A, f * t ^ n = algebraMap A Ω a)
    (hcentre : ∀ O : ValuationSubring (ResidueField w.valuationSubring), IsConstPlace k O →
      O ≠ ē → ∃ (Ac : Subring Ω) (ϖ : Ac), (∀ a ∈ Ac, a ∈ liftValuationSubring w O) ∧
        (∀ g : Ω, (∀ 𝔮 : Ideal Ac, 𝔮.IsPrime → 𝔮.height = 1 →
          ∃ r s : Ac, s ∉ 𝔮 ∧ (s : Ω) * g = r) → g ∈ Ac) ∧
        (∀ 𝔮 : Ideal Ac, 𝔮.IsPrime → 𝔮.height = 1 → ϖ ∈ 𝔮 → ∀ g : Ω, w g ≤ 1 →
          ∃ r s : Ac, s ∉ 𝔮 ∧ (s : Ω) * g = r) ∧
        (∀ 𝔮 : Ideal Ac, 𝔮.IsPrime → 𝔮.height = 1 → ϖ ∉ 𝔮 →
          ∃ r s : Ac, s ∉ 𝔮 ∧ (s : Ω) * f = r)) :
    (∀ O : ValuationSubring (ResidueField w.valuationSubring), IsConstPlace k O → O ≠ ē →
      reduce w f hf ∈ O) ∧ reduce w f hf * reduce w t ht ^ n ∈ ē := by
  refine ⟨fun O hO hne => ?_, ?_⟩
  · obtain ⟨Ac, ϖ, hdom, hhart, hvert, hhor⟩ := hcentre O hO hne
    exact reduce_mem_of_mem_centre hdom hf (mem_centre_of_hartogs ϖ hhart hvert hf hhor)
  · obtain ⟨a, ha⟩ := hpole
    obtain ⟨h1, h2⟩ := hAē a
    have hft : w (f * t ^ n) ≤ 1 := ha ▸ h1
    have heq : reduce w f hf * reduce w t ht ^ n = reduce w (f * t ^ n) hft := by
      simp only [reduce, ← map_pow, ← map_mul]
      rfl
    rw [heq]
    convert h2 using 2

end Landing

end SpecialFibreFunctionField

end ZInQ.Contrib.CMHeight62Full
