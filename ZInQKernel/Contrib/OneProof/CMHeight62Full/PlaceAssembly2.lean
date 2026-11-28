import ZInQKernel.Contrib.OneProof.CMHeight62Full.PlaceAssembly
import ZInQKernel.Contrib.OneProof.CMHeight62Full.SpecialFibreGap

/-!
# cmHeight62 (finite place): the per-place assembly, reduced

The per-place assembly `localComparison_core` with its open inputs discharged, except the centre
data `hL1` and the tree objects.

* `stalkSpecializes_stalkStructMap`: the compatibility `hφS` of the chart with the structure map
  `𝓞_L → 𝒪_{𝒢,ξ}`, from the compatibility of the chart of `exists_localModel_generic_algebraMap`
  with the structure map at `e(s)`.
* `exists_localModel_genericUnit_algebraMap`: that chart for the unit section of `𝒢`, with the
  stalk at the generic point of the section identified with `𝒪_{𝒢,ξ}`.
* `localComparison_reduced`: `localComparison_core` with `hφS` replaced by the compatibility at
  `e(s)`, the gap input `hL5` discharged from `SpecialFibreGap.specialFibreGap` (for a proper
  `𝒢`), and the instances on `R = (𝓞_L)_s` (perfect residue field, characteristic zero, `L` a
  fraction field of `R`) derived from `s = v`.
* `placeAssembly_reduced`: the chart, the uniformizer `ϖ`, the parameter `t` and the instances on
  `A = (A₀)_𝔭` exist, and for every choice of the tree objects over them and the centre data
  `hL1`, the comparison tuple at `v` holds.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CMHeight62Full

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory IsLocalRing
open ZInQ.DefFaltings WeierstrassCurve

namespace PlaceAssembly2

open PlaceAssembly SpecialFibreValuation SpecialFibreFunctionField

universe u

variable {K : Type} [Field K] {E : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L] (𝒢 : GroupModel E L)

/-! ## The chart and the structure map -/

section Chart

/-- **`hφS` from the structure map at `e(s)`.** If the chart `φ` sends the image of `r ∈ 𝓞_L` to
the image of `r` under `𝓞_L → 𝒪_{𝒢,e(s)}`, then its specialization to `𝒪_{𝒢,ξ}` is
`𝒢.structMap r`. -/
theorem stalkSpecializes_stalkStructMap (s : Spec (CommRingCat.of (𝓞 L)))
    [IsDiscreteValuationRing (Localization.AtPrime s.asIdeal)]
    {A₀ : Type} [CommRing A₀] [Algebra (Localization.AtPrime s.asIdeal) A₀]
    (σ : A₀ →ₐ[Localization.AtPrime s.asIdeal] Localization.AtPrime s.asIdeal)
    (φ : Localization.AtPrime (sectionPrime σ) ≃+*
      𝒢.G.left.presheaf.stalk (𝒢.unitSection s))
    (hR : ∀ r : 𝓞 L, φ (algebraMap (Localization.AtPrime s.asIdeal)
      (Localization.AtPrime (sectionPrime σ))
        (algebraMap (𝓞 L) (Localization.AtPrime s.asIdeal) r)) =
        SpecialFibreGap.stalkStructMap 𝒢.G (𝒢.unitSection s) r) :
    ∀ a : 𝓞 L, 𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s)
      (φ (algebraMap (Localization.AtPrime s.asIdeal) (Localization.AtPrime (sectionPrime σ))
        (algebraMap (𝓞 L) (Localization.AtPrime s.asIdeal) a))) = 𝒢.structMap a := by
  intro a
  rw [hR a]
  exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _

/-- **The chart at the generic unit, with the structure map.** The chart of
`exists_localModel_generic_algebraMap` for the unit section of `𝒢`, with the stalk at the generic
point of the section identified with `𝒪_{𝒢,ξ}` (`genericPoint = genericPt`). -/
theorem exists_localModel_genericUnit_algebraMap (s : Spec (CommRingCat.of (𝓞 L)))
    [IsDiscreteValuationRing (Localization.AtPrime s.asIdeal)]
    [IsDomain 𝒢.genStalk] [IsDiscreteValuationRing 𝒢.genStalk] :
    ∃ (A₀ : Type) (_ : CommRing A₀) (_ : Algebra (Localization.AtPrime s.asIdeal) A₀),
      Algebra.IsStandardSmoothOfRelativeDimension 1 (Localization.AtPrime s.asIdeal) A₀ ∧
      ∃ (σ : A₀ →ₐ[Localization.AtPrime s.asIdeal] Localization.AtPrime s.asIdeal)
        (φ : Localization.AtPrime (sectionPrime σ) ≃+*
          𝒢.G.left.presheaf.stalk (𝒢.unitSection s))
        (φη : Localization.AtPrime (RingHom.ker σ) ≃+* 𝒢.genStalk),
        (∀ a, (𝒢.unitSection.stalkMap s).hom (φ a) = specStalkEquiv s (localSection σ a)) ∧
        (∀ x : A₀, 𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s)
          (φ (algebraMap A₀ _ x)) = φη (algebraMap A₀ _ x)) ∧
        ∀ r : 𝓞 L, φ (algebraMap (Localization.AtPrime s.asIdeal)
          (Localization.AtPrime (sectionPrime σ))
            (algebraMap (𝓞 L) (Localization.AtPrime s.asIdeal) r)) =
          SpecialFibreGap.stalkStructMap 𝒢.G (𝒢.unitSection s) r := by
  have key : ∀ (η : Spec (CommRingCat.of (𝓞 L))),
      genericPoint (Spec (CommRingCat.of (𝓞 L))) = η →
      ∀ (_ : IsDomain (𝒢.G.left.presheaf.stalk (𝒢.unitSection η)))
        (_ : IsDiscreteValuationRing (𝒢.G.left.presheaf.stalk (𝒢.unitSection η))),
      ∃ (A₀ : Type) (_ : CommRing A₀) (_ : Algebra (Localization.AtPrime s.asIdeal) A₀),
        Algebra.IsStandardSmoothOfRelativeDimension 1 (Localization.AtPrime s.asIdeal) A₀ ∧
        ∃ (σ : A₀ →ₐ[Localization.AtPrime s.asIdeal] Localization.AtPrime s.asIdeal)
          (φ : Localization.AtPrime (sectionPrime σ) ≃+*
            𝒢.G.left.presheaf.stalk (𝒢.unitSection s))
          (φη : Localization.AtPrime (RingHom.ker σ) ≃+*
            𝒢.G.left.presheaf.stalk (𝒢.unitSection η)),
          (∀ a, (𝒢.unitSection.stalkMap s).hom (φ a) =
            specStalkEquiv s (localSection σ a)) ∧
          (∀ (h : 𝒢.unitSection η ⤳ 𝒢.unitSection s) (x : A₀),
            𝒢.G.left.presheaf.stalkSpecializes h (φ (algebraMap A₀ _ x)) =
              φη (algebraMap A₀ _ x)) ∧
          ∀ r : 𝓞 L, φ (algebraMap (Localization.AtPrime s.asIdeal)
            (Localization.AtPrime (sectionPrime σ))
              (algebraMap (𝓞 L) (Localization.AtPrime s.asIdeal) r)) =
            SpecialFibreGap.stalkStructMap 𝒢.G (𝒢.unitSection s) r := by
    intro η hη _ _
    subst hη
    exact SpecialFibreGap.exists_localModel_generic_algebraMap 𝒢.G.hom 𝒢.unitSection
      (unitSection_comp 𝒢) s
  obtain ⟨A₀, _, _, hstd, σ, φ, φη, hφ, hsp, hR⟩ := key (genericPt L)
    (genericPoint_eq_bot_of_affine _) ‹IsDomain 𝒢.genStalk› ‹IsDiscreteValuationRing 𝒢.genStalk›
  exact ⟨A₀, _, _, hstd, σ, φ, φη, hφ, fun x => hsp _ x, hR⟩

end Chart

/-! ## The per-place assembly with `hφS` and `hL5` discharged -/

section Reduced

/-- **The per-place assembly, reduced.** `localComparison_core` for a proper `𝒢`, with:
* `hφS` replaced by `hR`, the compatibility of `φ` with the structure map at `e(s)` (an output
  of `exists_localModel_genericUnit_algebraMap`);
* `hL5` (the gap at `ē` and no single simple pole at `ē`) discharged by
  `SpecialFibreGap.specialFibreGap`;
* the perfect residue field, characteristic zero and `L = Frac R` derived from `s = v`.

The remaining inputs are the chart and the parameter, the instances on `A` (supplied by
`placeInstances`), the tree objects and the centre data `hL1`. -/
theorem localComparison_reduced [IsProper 𝒢.G.hom] (W : WeierstrassCurve K)
    (v : HeightOneSpectrum (𝓞 L)) (s : Spec (CommRingCat.of (𝓞 L)))
    (hs : s.asIdeal = v.asIdeal)
    [IsDiscreteValuationRing (Localization.AtPrime s.asIdeal)]
    [Algebra (Localization.AtPrime s.asIdeal) L]
    [IsScalarTower (𝓞 L) (Localization.AtPrime s.asIdeal) L]
    {A₀ : Type} [CommRing A₀] [Algebra (Localization.AtPrime s.asIdeal) A₀]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 (Localization.AtPrime s.asIdeal) A₀]
    (σ : A₀ →ₐ[Localization.AtPrime s.asIdeal] Localization.AtPrime s.asIdeal)
    (φ : Localization.AtPrime (sectionPrime σ) ≃+*
      𝒢.G.left.presheaf.stalk (𝒢.unitSection s))
    (φη : Localization.AtPrime (RingHom.ker σ) ≃+* 𝒢.genStalk)
    (hφ : ∀ a, (𝒢.unitSection.stalkMap s).hom (φ a) = specStalkEquiv s (localSection σ a))
    (hsp : ∀ x : A₀, 𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s)
      (φ (algebraMap A₀ _ x)) = φη (algebraMap A₀ _ x))
    (hR : ∀ r : 𝓞 L, φ (algebraMap (Localization.AtPrime s.asIdeal)
      (Localization.AtPrime (sectionPrime σ))
        (algebraMap (𝓞 L) (Localization.AtPrime s.asIdeal) r)) =
      SpecialFibreGap.stalkStructMap 𝒢.G (𝒢.unitSection s) r)
    {ϖ : Localization.AtPrime s.asIdeal} (hϖ : Irreducible ϖ)
    {t : A₀} (ht : t ∈ RingHom.ker σ)
    (hmax : maximalIdeal (Localization.AtPrime (sectionPrime σ)) =
      Ideal.span {(algebraMap (Localization.AtPrime s.asIdeal)
        (Localization.AtPrime (sectionPrime σ)) ϖ),
        algebraMap A₀ (Localization.AtPrime (sectionPrime σ)) t})
    (hker : RingHom.ker (localSection σ) =
      Ideal.span {algebraMap A₀ (Localization.AtPrime (sectionPrime σ)) t})
    (B : Module.Basis (Fin 1) (Localization.AtPrime s.asIdeal) (RingHom.ker σ).Cotangent)
    (hB : ∀ i, B i = (RingHom.ker σ).toCotangent ⟨t, ht⟩)
    [IsNoetherianRing (Localization.AtPrime (sectionPrime σ))]
    [IsDomain (Localization.AtPrime (sectionPrime σ))]
    [FaithfulSMul (Localization.AtPrime s.asIdeal) (Localization.AtPrime (sectionPrime σ))]
    [IsDomain (Localization.AtPrime (sectionPrime σ) ⧸ Ideal.span
      {algebraMap (Localization.AtPrime s.asIdeal) (Localization.AtPrime (sectionPrime σ)) ϖ})]
    [IsDiscreteValuationRing (Localization.AtPrime (sectionPrime σ) ⧸ Ideal.span
      {algebraMap (Localization.AtPrime s.asIdeal) (Localization.AtPrime (sectionPrime σ)) ϖ})]
    {Ω : Type} [Field Ω] [Algebra (Localization.AtPrime (sectionPrime σ)) Ω]
    [IsFractionRing (Localization.AtPrime (sectionPrime σ)) Ω]
    [Algebra L Ω] [Algebra (Localization.AtPrime s.asIdeal) Ω]
    [IsScalarTower (Localization.AtPrime s.asIdeal) (Localization.AtPrime (sectionPrime σ)) Ω]
    [IsScalarTower (Localization.AtPrime s.asIdeal) L Ω]
    {F : Type u} [Field F] [Algebra L F] (Ψ : Ω ≃ₐ[L] F) (P : TauCeti.Place L F)
    (hfd : ∀ n : ℕ, FiniteDimensional L (poleSpace P n))
    (hdimP : ∀ n : ℕ, 1 ≤ n →
      TauCeti.Divisor.dim (Finsupp.single P (n : ℤ) : TauCeti.Divisor L F) = n)
    (hgen : ∀ g : Ω, P.valuation (Ψ g) ≤ 1 ↔
      ∃ r s' : Localization.AtPrime (sectionPrime σ),
        s' ∉ Ideal.span {algebraMap A₀ (Localization.AtPrime (sectionPrime σ)) t} ∧
          algebraMap _ Ω s' * g = algebraMap _ Ω r)
    (hPt : P.valuation (Ψ (algebraMap (Localization.AtPrime (sectionPrime σ)) Ω
      (algebraMap A₀ (Localization.AtPrime (sectionPrime σ)) t))) = WithZero.exp (-1 : ℤ))
    {X' Y' : F} (hW : ((W.map (algebraMap K L)).baseChange F).toAffine.Equation X' Y')
    (hX' : P.valuation X' = WithZero.exp (1 : ℤ) ^ 2)
    (hY' : P.valuation Y' = WithZero.exp (1 : ℤ) ^ 3)
    (hXS : X' ∈ regularAway P) (hYS : Y' ∈ regularAway P)
    (ι : 𝒢.genStalk →+* Ω)
    (hι : ∀ x : A₀, ι (φη (algebraMap A₀ _ x)) =
      algebraMap (Localization.AtPrime (sectionPrime σ)) Ω (algebraMap A₀ _ x))
    (tG : maximalIdeal 𝒢.genStalk) (htG : Ψ (ι tG) = -X' / Y')
    (hL1 : letI := (residueHom (specialFibreValuation (Localization.AtPrime (sectionPrime σ)) Ω hϖ)
        (specialFibreValuation_algebraMap_base_le_one hϖ)
        (specialFibreValuation_algebraMap_base_lt_one hϖ)).toAlgebra
      ∀ f : Ω, (∀ Q : ValuationSubring Ω, (∀ c : L, algebraMap L Ω c ∈ Q) →
        IsDiscreteValuationRing Q → Q ≠ genericSubring Ψ P → f ∈ Q) →
      ∀ O : ValuationSubring (ResidueField
          (specialFibreValuation (Localization.AtPrime (sectionPrime σ)) Ω hϖ).valuationSubring),
        IsConstPlace (ResidueField (Localization.AtPrime s.asIdeal)) O →
        O ≠ specialFibrePlace (Localization.AtPrime (sectionPrime σ)) Ω hϖ →
        ∃ (Ac : Subring Ω) (π : Ac), (∀ a ∈ Ac, a ∈ liftValuationSubring
            (specialFibreValuation (Localization.AtPrime (sectionPrime σ)) Ω hϖ) O) ∧
          (∀ g : Ω, (∀ 𝔮 : Ideal Ac, 𝔮.IsPrime → 𝔮.height = 1 →
            ∃ r s : Ac, s ∉ 𝔮 ∧ (s : Ω) * g = r) → g ∈ Ac) ∧
          (∀ 𝔮 : Ideal Ac, 𝔮.IsPrime → 𝔮.height = 1 → π ∈ 𝔮 → ∀ g : Ω,
            specialFibreValuation (Localization.AtPrime (sectionPrime σ)) Ω hϖ g ≤ 1 →
            ∃ r s : Ac, s ∉ 𝔮 ∧ (s : Ω) * g = r) ∧
          (∀ 𝔮 : Ideal Ac, 𝔮.IsPrime → 𝔮.height = 1 → π ∉ 𝔮 →
            ∃ r s : Ac, s ∉ 𝔮 ∧ (s : Ω) * f = r)) :
    ∃ (W₀ : WeierstrassCurve L) (C : VariableChange L) (θ : 𝒢.hodgeSpace 1) (b : L),
      v.valuation L W₀.Δ = 1 ∧ C⁻¹ • W.map (algebraMap K L) = W₀ ∧ θ ≠ 0 ∧
        (∀ m ∈ 𝒢.detLattice 1, ∃ r : L, v.valuation L r ≤ 1 ∧ m = r • θ) ∧
        𝒢.wedge ![tG] = b • θ ∧ v.valuation L (C.u : L) = v.valuation L b := by
  -- the instances on `R = (𝓞_L)_s`
  have hsb : s.asIdeal ≠ ⊥ := hs ▸ v.ne_bot
  have : s.asIdeal.IsMaximal := hs ▸ v.isMaximal
  have : PerfectField (ResidueField (Localization.AtPrime s.asIdeal)) :=
    SmallGlue.perfectField_residueField_ringOfIntegers s.asIdeal hsb
  have : CharZero (Localization.AtPrime s.asIdeal) :=
    SmallGlue.charZero_localization_ringOfIntegers s.asIdeal
  have : IsFractionRing (Localization.AtPrime s.asIdeal) L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization s.asIdeal.primeCompl _ L
  -- `hφS`
  have hφS := stalkSpecializes_stalkStructMap 𝒢 s σ φ hR
  -- `hL5`, from the special-fibre gap
  have hgap := SpecialFibreGap.specialFibreGap (A₀ := A₀)
    (A := Localization.AtPrime (sectionPrime σ)) s 𝒢.G (sectionPrime σ).primeCompl Ω hϖ φ hR
  have hker' : RingHom.ker (IdentityPointDepth.localSectionAlgHom σ) =
      Ideal.span {algebraMap A₀ (Localization.AtPrime (sectionPrime σ)) t} :=
    (IdentityPointDepth.ker_localSectionAlgHom σ).trans hker
  have hπ := SmallGlue.isUniformizerAt_reduce_specialFibrePlace (Ω := Ω) hϖ
    (IdentityPointDepth.localSectionAlgHom σ) hker'
  have hP := isDegreeOnePlace_specialFibrePlace (Ω := Ω) hϖ
    (IdentityPointDepth.localSectionAlgHom σ)
  exact localComparison_core 𝒢 W v s hs σ φ φη hφ hsp hφS hϖ ht hmax hker B hB Ψ P hfd hdimP
    hgen hPt hW hX' hY' hXS hYS ι hι tG htG hL1
    ⟨hgap.2.1 _ hP _ hπ, hgap.2.2 _ hP⟩

end Reduced

/-! ## The per-place assembly from the tree inputs and the centre data -/

section Final

/-- **The per-place assembly at `v` (`placeAssembly_reduced`).** Let `𝒢` be proper, with
`𝒪_{𝒢,ξ}` a discrete valuation ring, `v` a finite place, `s = v` and `R = (𝓞_L)_s` with `L` an
`R`-algebra compatible with `𝓞_L`. There are the chart `(A₀, σ, φ, φη)` of the smooth model at the
unit section, a uniformizer `ϖ` of `R` and the parameter `t` of the local structure
(`𝔪_A = (ϖ, t)`, `ker (localSection σ) = (t)`), with the instances on `A = (A₀)_𝔭` that the
special-fibre valuation needs, such that: for every fraction field `Ω` of `A` over `L`, every tree
place (`Ψ`, `P`, `hfd`, `hdimP`, `hgen`, `hPt`), every tree pair `X', Y'`, every tree parameter
map (`ι`, `hι`, `tG`, `htG`) and the centre data `hL1`, the comparison tuple of
`abs_norm_le_of_comparisons` at `v` holds for `η = 𝒢.wedge ![tG]`. -/
theorem placeAssembly_reduced [IsProper 𝒢.G.hom] [IsDomain 𝒢.genStalk]
    [IsDiscreteValuationRing 𝒢.genStalk] (W : WeierstrassCurve K)
    (v : HeightOneSpectrum (𝓞 L)) (s : Spec (CommRingCat.of (𝓞 L)))
    (hs : s.asIdeal = v.asIdeal)
    [IsDiscreteValuationRing (Localization.AtPrime s.asIdeal)]
    [Algebra (Localization.AtPrime s.asIdeal) L]
    [IsScalarTower (𝓞 L) (Localization.AtPrime s.asIdeal) L] :
    ∃ (A₀ : Type) (_ : CommRing A₀) (_ : Algebra (Localization.AtPrime s.asIdeal) A₀),
      Algebra.IsStandardSmoothOfRelativeDimension 1 (Localization.AtPrime s.asIdeal) A₀ ∧
      ∃ (σ : A₀ →ₐ[Localization.AtPrime s.asIdeal] Localization.AtPrime s.asIdeal)
        (φ : Localization.AtPrime (sectionPrime σ) ≃+*
          𝒢.G.left.presheaf.stalk (𝒢.unitSection s))
        (φη : Localization.AtPrime (RingHom.ker σ) ≃+* 𝒢.genStalk),
        (∀ a, (𝒢.unitSection.stalkMap s).hom (φ a) = specStalkEquiv s (localSection σ a)) ∧
        (∀ x : A₀, 𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s)
          (φ (algebraMap A₀ _ x)) = φη (algebraMap A₀ _ x)) ∧
        ∃ (ϖ : Localization.AtPrime s.asIdeal) (hϖ : Irreducible ϖ) (t : A₀)
          (_ : t ∈ RingHom.ker σ),
          maximalIdeal (Localization.AtPrime (sectionPrime σ)) =
            Ideal.span {(algebraMap (Localization.AtPrime s.asIdeal)
              (Localization.AtPrime (sectionPrime σ)) ϖ),
              algebraMap A₀ (Localization.AtPrime (sectionPrime σ)) t} ∧
          RingHom.ker (localSection σ) =
            Ideal.span {algebraMap A₀ (Localization.AtPrime (sectionPrime σ)) t} ∧
          ∃ (_ : IsNoetherianRing (Localization.AtPrime (sectionPrime σ)))
            (_ : IsDomain (Localization.AtPrime (sectionPrime σ)))
            (_ : FaithfulSMul (Localization.AtPrime s.asIdeal)
              (Localization.AtPrime (sectionPrime σ)))
            (_ : IsDomain (Localization.AtPrime (sectionPrime σ) ⧸ Ideal.span
              {algebraMap (Localization.AtPrime s.asIdeal)
                (Localization.AtPrime (sectionPrime σ)) ϖ}))
            (_ : IsDiscreteValuationRing (Localization.AtPrime (sectionPrime σ) ⧸ Ideal.span
              {algebraMap (Localization.AtPrime s.asIdeal)
                (Localization.AtPrime (sectionPrime σ)) ϖ})),
          ∀ {Ω : Type} [Field Ω] [Algebra (Localization.AtPrime (sectionPrime σ)) Ω]
            [IsFractionRing (Localization.AtPrime (sectionPrime σ)) Ω]
            [Algebra L Ω] [Algebra (Localization.AtPrime s.asIdeal) Ω]
            [IsScalarTower (Localization.AtPrime s.asIdeal)
              (Localization.AtPrime (sectionPrime σ)) Ω]
            [IsScalarTower (Localization.AtPrime s.asIdeal) L Ω]
            {F : Type u} [Field F] [Algebra L F] (Ψ : Ω ≃ₐ[L] F) (P : TauCeti.Place L F),
            (∀ n : ℕ, FiniteDimensional L (poleSpace P n)) →
            (∀ n : ℕ, 1 ≤ n →
              TauCeti.Divisor.dim (Finsupp.single P (n : ℤ) : TauCeti.Divisor L F) = n) →
            (∀ g : Ω, P.valuation (Ψ g) ≤ 1 ↔
              ∃ r s' : Localization.AtPrime (sectionPrime σ),
                s' ∉ Ideal.span {algebraMap A₀ (Localization.AtPrime (sectionPrime σ)) t} ∧
                  algebraMap _ Ω s' * g = algebraMap _ Ω r) →
            P.valuation (Ψ (algebraMap (Localization.AtPrime (sectionPrime σ)) Ω
              (algebraMap A₀ (Localization.AtPrime (sectionPrime σ)) t))) =
                WithZero.exp (-1 : ℤ) →
            ∀ {X' Y' : F}, ((W.map (algebraMap K L)).baseChange F).toAffine.Equation X' Y' →
            P.valuation X' = WithZero.exp (1 : ℤ) ^ 2 →
            P.valuation Y' = WithZero.exp (1 : ℤ) ^ 3 →
            X' ∈ regularAway P → Y' ∈ regularAway P →
            ∀ (ι : 𝒢.genStalk →+* Ω), (∀ x : A₀, ι (φη (algebraMap A₀ _ x)) =
              algebraMap (Localization.AtPrime (sectionPrime σ)) Ω (algebraMap A₀ _ x)) →
            ∀ (tG : maximalIdeal 𝒢.genStalk), Ψ (ι tG) = -X' / Y' →
            (letI := (residueHom
                (specialFibreValuation (Localization.AtPrime (sectionPrime σ)) Ω hϖ)
                (specialFibreValuation_algebraMap_base_le_one hϖ)
                (specialFibreValuation_algebraMap_base_lt_one hϖ)).toAlgebra
              ∀ f : Ω, (∀ Q : ValuationSubring Ω, (∀ c : L, algebraMap L Ω c ∈ Q) →
                IsDiscreteValuationRing Q → Q ≠ genericSubring Ψ P → f ∈ Q) →
              ∀ O : ValuationSubring (ResidueField (specialFibreValuation
                  (Localization.AtPrime (sectionPrime σ)) Ω hϖ).valuationSubring),
                IsConstPlace (ResidueField (Localization.AtPrime s.asIdeal)) O →
                O ≠ specialFibrePlace (Localization.AtPrime (sectionPrime σ)) Ω hϖ →
                ∃ (Ac : Subring Ω) (π : Ac), (∀ a ∈ Ac, a ∈ liftValuationSubring
                    (specialFibreValuation (Localization.AtPrime (sectionPrime σ)) Ω hϖ) O) ∧
                  (∀ g : Ω, (∀ 𝔮 : Ideal Ac, 𝔮.IsPrime → 𝔮.height = 1 →
                    ∃ r s : Ac, s ∉ 𝔮 ∧ (s : Ω) * g = r) → g ∈ Ac) ∧
                  (∀ 𝔮 : Ideal Ac, 𝔮.IsPrime → 𝔮.height = 1 → π ∈ 𝔮 → ∀ g : Ω,
                    specialFibreValuation (Localization.AtPrime (sectionPrime σ)) Ω hϖ g ≤ 1 →
                    ∃ r s : Ac, s ∉ 𝔮 ∧ (s : Ω) * g = r) ∧
                  (∀ 𝔮 : Ideal Ac, 𝔮.IsPrime → 𝔮.height = 1 → π ∉ 𝔮 →
                    ∃ r s : Ac, s ∉ 𝔮 ∧ (s : Ω) * f = r)) →
            ∃ (W₀ : WeierstrassCurve L) (C : VariableChange L) (θ : 𝒢.hodgeSpace 1) (b : L),
              v.valuation L W₀.Δ = 1 ∧ C⁻¹ • W.map (algebraMap K L) = W₀ ∧ θ ≠ 0 ∧
                (∀ m ∈ 𝒢.detLattice 1, ∃ r : L, v.valuation L r ≤ 1 ∧ m = r • θ) ∧
                𝒢.wedge ![tG] = b • θ ∧ v.valuation L (C.u : L) = v.valuation L b := by
  obtain ⟨A₀, _, _, hstd, σ, φ, φη, hφ, hsp, hR⟩ := exists_localModel_genericUnit_algebraMap 𝒢 s
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime s.asIdeal)
  obtain ⟨t, ht, -, hdim, hmax, hker, B, hB⟩ := localStructure_of_standardSmooth σ hϖ
  obtain ⟨h1, h2, h3, h4, h5⟩ := placeInstances σ hϖ hdim hmax
  refine ⟨A₀, _, _, hstd, σ, φ, φη, hφ, hsp, ϖ, hϖ, t, ht, hmax, hker, h1, h2, h3, h4, h5, ?_⟩
  intro Ω _ _ _ _ _ _ _ F _ _ Ψ P hfd hdimP hgen hPt X' Y' hW hX' hY' hXS hYS ι hι tG htG hL1
  exact localComparison_reduced 𝒢 W v s hs σ φ φη hφ hsp hR hϖ ht hmax hker B hB Ψ P hfd hdimP
    hgen hPt hW hX' hY' hXS hYS ι hι tG htG hL1

end Final

end PlaceAssembly2

end ZInQ.Contrib.CMHeight62Full
