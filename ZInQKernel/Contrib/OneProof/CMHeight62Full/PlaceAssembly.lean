import ZInQKernel.Contrib.OneProof.CMHeight62Full.HodgeLineGlue
import ZInQKernel.Contrib.OneProof.CMHeight62Full.SmallGlue
import ZInQKernel.Contrib.OneProof.CMHeight62Full.HorizontalPrimes
import ZInQKernel.Contrib.OneProof.CMHeight62Full.PoleRegCore
import ZInQKernel.Contrib.OneProof.CMHeight62Full.Weierstrass
import ZInQKernel.Contrib.OneProof.CMHeight62Full.WeierstrassDVR

/-!
# cmHeight62 (finite place): the per-place assembly

The data that `abs_norm_le_of_comparisons` takes at one finite place `v`, assembled from the
local nodes, with every tree object as an explicit hypothesis.

Part 1 (`hcmp_of_localData`): from the outputs of the lattice, pole-ladder, integral-model and
local-parameter steps (a pair `x, y` with exact pole orders two and three, an integral model
`W0` with unit discriminant through `(e x, e y)`, and `-(e x)/(e y) = ε t` with `ε` a unit),
the tuple `(W₀, C, θ, b)` of the comparison at `v`. The variable change `C` comes from the
generic comparison, the line `θ` from the Hodge-line glue, and `η = b • θ` from the first order
change of the parameter: the tree parameter and `u_C · ε t` agree modulo `𝔪_ξ²`.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CMHeight62Full

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory IsLocalRing
open ZInQ.DefFaltings WeierstrassCurve

namespace PlaceAssembly

/-! ## Units of the local ring of `𝓞_L` -/

section Units

variable {L : Type} [Field L] [NumberField L]

/-- A unit of `(𝓞_L)_𝔭` has valuation one at `v` (`𝔭 = v`). -/
theorem valuation_algebraMap_of_isUnit (v : HeightOneSpectrum (𝓞 L))
    (s : Spec (CommRingCat.of (𝓞 L))) (hs : s.asIdeal = v.asIdeal)
    [Algebra (Localization.AtPrime s.asIdeal) L]
    [IsScalarTower (𝓞 L) (Localization.AtPrime s.asIdeal) L]
    {x : Localization.AtPrime s.asIdeal} (hx : IsUnit x) :
    v.valuation L (algebraMap (Localization.AtPrime s.asIdeal) L x) = 1 := by
  obtain ⟨⟨a, ⟨b, hb2⟩⟩, hab⟩ := IsLocalization.surj s.asIdeal.primeCompl x
  have hb : b ∉ v.asIdeal := by
    rw [← hs]
    exact hb2
  have ha : a ∉ v.asIdeal := by
    rw [← hs]
    have hu : IsUnit (algebraMap (𝓞 L) (Localization.AtPrime s.asIdeal) a) := by
      rw [← hab]
      exact hx.mul (IsLocalization.map_units _ (⟨b, hb2⟩ : s.asIdeal.primeCompl))
    exact (IsLocalization.AtPrime.isUnit_to_map_iff _ s.asIdeal a).1 hu
  have h := congrArg (algebraMap (Localization.AtPrime s.asIdeal) L) hab
  rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h
  have h2 := congrArg (v.valuation L) h
  rw [map_mul, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 hb,
    HeightOneSpectrum.intValuation_eq_one_iff.2 ha, mul_one] at h2
  exact h2

end Units

/-! ## Wedges of germs that agree modulo `𝔪_ξ²` -/

section Wedge

variable {L : Type} [Field L] [NumberField L]

/-- `d • m = n • x` with `d ≠ 0` gives `1 ⊗ m = (n / d) • (1 ⊗ x)`. -/
theorem toHodgeOne_eq_div_smul_of_ne_zero {M : Type*} [AddCommGroup M] [Module (𝓞 L) M]
    {n d : 𝓞 L} (hd : d ≠ 0) {m x : M} (h : d • m = n • x) :
    toHodgeOne L m = (algebraMap (𝓞 L) L n / algebraMap (𝓞 L) L d) • toHodgeOne L x := by
  have hd0 : algebraMap (𝓞 L) L d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 L) L)).mpr hd
  have key : algebraMap (𝓞 L) L d • toHodgeOne L m = algebraMap (𝓞 L) L n • toHodgeOne L x := by
    rw [algebraMap_smul, algebraMap_smul, ← map_smul, ← map_smul, h]
  calc toHodgeOne L m
      = (algebraMap (𝓞 L) L d)⁻¹ • (algebraMap (𝓞 L) L d • toHodgeOne L m) := by
        rw [smul_smul, inv_mul_cancel₀ hd0, one_smul]
    _ = _ := by rw [key, smul_smul, div_eq_inv_mul]

variable {K : Type} [Field K] {E : PkgI3.AbVar K} [Algebra K L] (𝒢 : GroupModel E L)

/-- If `d · g ≡ n · h` modulo `𝔪_ξ²` (`d ≠ 0`), then `𝒢.wedge ![g] = (n / d) • 𝒢.wedge ![h]`. -/
theorem wedge_eq_div_smul_of_sub_mem_sq (g h : maximalIdeal 𝒢.genStalk) {n d : 𝓞 L}
    (hd : d ≠ 0)
    (hsub : 𝒢.structMap d * (g : 𝒢.genStalk) - 𝒢.structMap n * (h : 𝒢.genStalk) ∈
      maximalIdeal 𝒢.genStalk ^ 2) :
    𝒢.wedge ![g] = (algebraMap (𝓞 L) L n / algebraMap (𝓞 L) L d) • 𝒢.wedge ![h] := by
  rw [wedge_eq_toHodgeOne, wedge_eq_toHodgeOne]
  apply toHodgeOne_eq_div_smul_of_ne_zero hd
  rw [smul_cotangent_def, smul_cotangent_def]
  have hg : 𝒢.structMap d * (g : 𝒢.genStalk) ∈ maximalIdeal 𝒢.genStalk :=
    Ideal.mul_mem_left _ _ g.2
  have hh : 𝒢.structMap n * (h : 𝒢.genStalk) ∈ maximalIdeal 𝒢.genStalk :=
    Ideal.mul_mem_left _ _ h.2
  rw [← dCls_mul 𝒢 _ g hg, ← dCls_mul 𝒢 _ h hh, ← sub_eq_zero]
  have hdiff : 𝒢.dCls ⟨_, hg⟩ - 𝒢.dCls ⟨_, hh⟩ =
      𝒢.dCls (⟨_, hg⟩ - ⟨_, hh⟩ : maximalIdeal 𝒢.genStalk) :=
    (map_sub ((maximalIdeal 𝒢.genStalk).toCotangent) _ _).symm
  rw [hdiff, dCls_eq_zero_iff]
  exact hsub

end Wedge

/-! ## Germs of order at least two at the generic point of the section -/

section Order

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {A₀ : Type*} [CommRing A₀] [Algebra R A₀] (σ : A₀ →ₐ[R] R) {t : A₀}

/-- A ring isomorphism of local rings reflects membership in `𝔪²`. -/
theorem mem_maximalIdeal_sq_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) {x : A} (hx : e x ∈ maximalIdeal B ^ 2) :
    x ∈ maximalIdeal A ^ 2 := by
  by_contra h
  exact ringEquiv_notMem_maximalIdeal_sq e h hx

/-- **Order two at the generic point of the section.** Let `ν` be a valuation on the fraction
field `Ω` of `A = (A₀)_𝔭` whose valuation ring is `A_(t)` (`hgen`) and with `ν(t) = exp (-1)`.
Let `ι : D → Ω` be a ring map from a local ring `D ≅ Localization.AtPrime (ker σ)` compatible
with `A₀`. If `ν(ι g) · exp 1 ^ 2 ≤ 1`, then `g ∈ 𝔪_D²`. -/
theorem mem_maximalIdeal_sq_of_valuation
    (hker : RingHom.ker (localSection σ) =
      Ideal.span {algebraMap A₀ (Localization.AtPrime (sectionPrime σ)) t})
    [IsDomain (Localization.AtPrime (sectionPrime σ))]
    {Ω : Type*} [Field Ω] [Algebra (Localization.AtPrime (sectionPrime σ)) Ω]
    [IsFractionRing (Localization.AtPrime (sectionPrime σ)) Ω]
    (ν : Valuation Ω (WithZero (Multiplicative ℤ)))
    (hgen : ∀ g : Ω, ν g ≤ 1 ↔ ∃ r s' : Localization.AtPrime (sectionPrime σ),
      s' ∉ Ideal.span {algebraMap A₀ (Localization.AtPrime (sectionPrime σ)) t} ∧
        algebraMap _ Ω s' * g = algebraMap _ Ω r)
    (hνt : ν (algebraMap _ Ω (algebraMap A₀ (Localization.AtPrime (sectionPrime σ)) t)) =
      WithZero.exp (-1 : ℤ))
    {D : Type*} [CommRing D] [IsLocalRing D] (φη : Localization.AtPrime (RingHom.ker σ) ≃+* D)
    (ι : D →+* Ω)
    (hι : ∀ x : A₀, ι (φη (algebraMap A₀ _ x)) =
      algebraMap (Localization.AtPrime (sectionPrime σ)) Ω (algebraMap A₀ _ x))
    (g : D) (hg : ν (ι g) * WithZero.exp (1 : ℤ) ^ 2 ≤ 1) : g ∈ maximalIdeal D ^ 2 := by
  have := isPrime_span_sectionParam σ hker
  obtain ⟨e', he'⟩ := localizationAtSectionKer_equiv σ hker
  let := atPrimeAlgebra (Ω := Ω)
    (Ideal.span {algebraMap A₀ (Localization.AtPrime (sectionPrime σ)) t})
  have := atPrime_isScalarTower (Ω := Ω)
    (Ideal.span {algebraMap A₀ (Localization.AtPrime (sectionPrime σ)) t})
  have := atPrime_isFractionRing (Ω := Ω)
    (Ideal.span {algebraMap A₀ (Localization.AtPrime (sectionPrime σ)) t})
  set tA := algebraMap A₀ (Localization.AtPrime (sectionPrime σ)) t with htA
  have hext : ι.comp (φη : Localization.AtPrime (RingHom.ker σ) →+* D) =
      (algebraMap (Localization.AtPrime (Ideal.span {tA})) Ω).comp
        (e' : Localization.AtPrime (RingHom.ker σ) →+* Localization.AtPrime (Ideal.span {tA})) := by
    refine IsLocalization.ringHom_ext (RingHom.ker σ).primeCompl (RingHom.ext fun x => ?_)
    simp only [RingHom.comp_apply, RingHom.coe_coe]
    rw [hι, he' x, IsScalarTower.algebraMap_apply A₀ (Localization.AtPrime (sectionPrime σ))
      (Localization.AtPrime (Ideal.span {tA})),
      ← IsScalarTower.algebraMap_apply (Localization.AtPrime (sectionPrime σ))
        (Localization.AtPrime (Ideal.span {tA})) Ω]
  have hιeq : ι g = algebraMap (Localization.AtPrime (Ideal.span {tA})) Ω (e' (φη.symm g)) := by
    have := RingHom.congr_fun hext (φη.symm g)
    simpa using this
  set z := e' (φη.symm g) with hzdef
  have hT : algebraMap (Localization.AtPrime (sectionPrime σ)) Ω tA ≠ 0 := by
    intro h
    rw [h, map_zero] at hνt
    exact WithZero.exp_ne_zero hνt.symm
  have hle : ν (algebraMap (Localization.AtPrime (Ideal.span {tA})) Ω z /
      algebraMap (Localization.AtPrime (sectionPrime σ)) Ω tA ^ 2) ≤ 1 := by
    rw [map_div₀, map_pow, hνt, ← hιeq, WithZero.exp_neg, inv_pow, div_inv_eq_mul]
    exact hg
  obtain ⟨r, s', hs', hrs⟩ := (hgen _).1 hle
  have hs'u : IsUnit (algebraMap (Localization.AtPrime (sectionPrime σ))
      (Localization.AtPrime (Ideal.span {tA})) s') :=
    IsLocalization.map_units (Localization.AtPrime (Ideal.span {tA}))
      (⟨s', hs'⟩ : (Ideal.span {tA}).primeCompl)
  have hinj := IsFractionRing.injective (Localization.AtPrime (Ideal.span {tA})) Ω
  have hD : algebraMap (Localization.AtPrime (sectionPrime σ))
      (Localization.AtPrime (Ideal.span {tA})) s' * z =
      algebraMap (Localization.AtPrime (sectionPrime σ))
        (Localization.AtPrime (Ideal.span {tA})) r *
        algebraMap (Localization.AtPrime (sectionPrime σ))
          (Localization.AtPrime (Ideal.span {tA})) tA ^ 2 := by
    apply hinj
    simp only [map_mul, map_pow, ← IsScalarTower.algebraMap_apply]
    rw [← hrs]
    field_simp
  have hz : z ∈ maximalIdeal (Localization.AtPrime (Ideal.span {tA})) ^ 2 := by
    have htt : algebraMap A₀ (Localization.AtPrime (Ideal.span {tA})) t =
        algebraMap (Localization.AtPrime (sectionPrime σ))
          (Localization.AtPrime (Ideal.span {tA})) tA :=
      IsScalarTower.algebraMap_apply _ _ _ t
    rw [maximalIdeal_localization_span_sectionParam σ hker, Ideal.span_singleton_pow, htt]
    have hz' : z = (hs'u.unit⁻¹ : (Localization.AtPrime (Ideal.span {tA}))ˣ) *
        algebraMap (Localization.AtPrime (sectionPrime σ))
          (Localization.AtPrime (Ideal.span {tA})) r *
        algebraMap (Localization.AtPrime (sectionPrime σ))
          (Localization.AtPrime (Ideal.span {tA})) tA ^ 2 := by
      rw [mul_assoc, ← hD, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
    rw [hz']
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  exact mem_maximalIdeal_sq_of_ringEquiv (φη.symm.trans e'.toRingEquiv) hz

end Order

/-! ## Part 1: the comparison tuple from the local data -/

section Comparison

variable {K : Type} [Field K] {E : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L] (𝒢 : GroupModel E L)

/-- **The comparison at `v` from the local data.** Hypotheses, in order:
* the place: `v`, the point `s` of `Spec 𝓞_L` with `s = v`, and `L` as an algebra over
  `R = (𝓞_L)_s` compatible with `𝓞_L`;
* the chart of the smooth model at the unit section (`σ`, `φ`, `φη`, `hφ`, `hsp`), with `φ`
  compatible with the structure map `𝓞_L → 𝒪_{𝒢,ξ}` (`hφS`);
* the parameter `t` (`ht`, `hker`, the cotangent basis `B`);
* the fraction field `Ω` of `A = (A₀)_𝔭`, an `L`-algebra compatible with `R → A → Ω`;
* the tree place: `Ψ : Ω ≃ₐ[L] F`, `P`, `hfd`, the ladder `hdimP`, `hgen`, `hPt`;
* the tree pair `X', Y'` on `W_L` with poles of order two and three at `P` only;
* the map `ι : 𝒪_{𝒢,ξ} → Ω` (compatible with `A₀`) and the tree parameter `tG` with
  `Ψ (ι tG) = -X'/Y'`;
* the local data: `x ∈ V₂ \ V₁`, `y ∈ V₃ \ V₂`, the integral model `W0` with unit discriminant
  through `(e x, e y)`, and the unit `ε` with `-(e x)/(e y) = ε t`.

The conclusion is the tuple of `abs_norm_le_of_comparisons` at `v`, for `η = 𝒢.wedge ![tG]`. -/
theorem hcmp_of_localData (W : WeierstrassCurve K)
    (v : HeightOneSpectrum (𝓞 L)) (s : Spec (CommRingCat.of (𝓞 L)))
    (hs : s.asIdeal = v.asIdeal)
    [IsDiscreteValuationRing (Localization.AtPrime s.asIdeal)]
    [Algebra (Localization.AtPrime s.asIdeal) L]
    [IsScalarTower (𝓞 L) (Localization.AtPrime s.asIdeal) L]
    {A₀ : Type} [CommRing A₀] [Algebra (Localization.AtPrime s.asIdeal) A₀]
    (σ : A₀ →ₐ[Localization.AtPrime s.asIdeal] Localization.AtPrime s.asIdeal)
    (φ : Localization.AtPrime (sectionPrime σ) ≃+*
      𝒢.G.left.presheaf.stalk (𝒢.unitSection s))
    (φη : Localization.AtPrime (RingHom.ker σ) ≃+* 𝒢.genStalk)
    (hφ : ∀ a, (𝒢.unitSection.stalkMap s).hom (φ a) = specStalkEquiv s (localSection σ a))
    (hsp : ∀ x : A₀, 𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s)
      (φ (algebraMap A₀ _ x)) = φη (algebraMap A₀ _ x))
    (hφS : ∀ a : 𝓞 L, 𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s)
      (φ (algebraMap (Localization.AtPrime s.asIdeal) (Localization.AtPrime (sectionPrime σ))
        (algebraMap (𝓞 L) (Localization.AtPrime s.asIdeal) a))) = 𝒢.structMap a)
    {t : A₀} (ht : t ∈ RingHom.ker σ)
    (hker : RingHom.ker (localSection σ) =
      Ideal.span {algebraMap A₀ (Localization.AtPrime (sectionPrime σ)) t})
    (B : Module.Basis (Fin 1) (Localization.AtPrime s.asIdeal) (RingHom.ker σ).Cotangent)
    (hB : ∀ i, B i = (RingHom.ker σ).toCotangent ⟨t, ht⟩)
    [IsDomain (Localization.AtPrime (sectionPrime σ))]
    {Ω : Type*} [Field Ω] [Algebra (Localization.AtPrime (sectionPrime σ)) Ω]
    [IsFractionRing (Localization.AtPrime (sectionPrime σ)) Ω]
    [Algebra L Ω] [Algebra (Localization.AtPrime s.asIdeal) Ω]
    [IsScalarTower (Localization.AtPrime s.asIdeal) (Localization.AtPrime (sectionPrime σ)) Ω]
    [IsScalarTower (Localization.AtPrime s.asIdeal) L Ω]
    {F : Type*} [Field F] [Algebra L F] (Ψ : Ω ≃ₐ[L] F) (P : TauCeti.Place L F)
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
    {x y : Ω} (hx2 : x ∈ poleSpaceIn Ψ P 2) (hx1 : x ∉ poleSpaceIn Ψ P 1)
    (hy3 : y ∈ poleSpaceIn Ψ P 3) (hy2 : y ∉ poleSpaceIn Ψ P 2)
    (W0 : WeierstrassCurve (Localization.AtPrime s.asIdeal))
    (e : (Localization.AtPrime s.asIdeal)ˣ) (hΔ : IsUnit W0.Δ)
    (heq : (W0.map (algebraMap (Localization.AtPrime s.asIdeal) Ω)).toAffine.Equation
      (algebraMap (Localization.AtPrime s.asIdeal) Ω e * x)
      (algebraMap (Localization.AtPrime s.asIdeal) Ω e * y))
    (ε : (Localization.AtPrime (sectionPrime σ))ˣ)
    (hε : -(algebraMap (Localization.AtPrime s.asIdeal) Ω e * x) /
        (algebraMap (Localization.AtPrime s.asIdeal) Ω e * y) =
      algebraMap (Localization.AtPrime (sectionPrime σ)) Ω ε *
        algebraMap (Localization.AtPrime (sectionPrime σ)) Ω
          (algebraMap A₀ (Localization.AtPrime (sectionPrime σ)) t)) :
    ∃ (W₀ : WeierstrassCurve L) (C : VariableChange L) (θ : 𝒢.hodgeSpace 1) (b : L),
      v.valuation L W₀.Δ = 1 ∧ C⁻¹ • W.map (algebraMap K L) = W₀ ∧ θ ≠ 0 ∧
        (∀ m ∈ 𝒢.detLattice 1, ∃ r : L, v.valuation L r ≤ 1 ∧ m = r • θ) ∧
        𝒢.wedge ![tG] = b • θ ∧ v.valuation L (C.u : L) = v.valuation L b := by
  classical
  -- the Hodge line
  obtain ⟨tS, htS, -, hθ, hM⟩ :=
    hodgeLine_of_localModel_generic 𝒢 s v hs σ φ φη hφ hsp ht hker B hB
  set tA := algebraMap A₀ (Localization.AtPrime (sectionPrime σ)) t with htA
  -- `ι` on the local ring at the closed point of the section
  have hιA : ∀ a : Localization.AtPrime (sectionPrime σ),
      ι (𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s) (φ a)) =
        algebraMap (Localization.AtPrime (sectionPrime σ)) Ω a := by
    have hext : ι.comp ((𝒢.G.left.presheaf.stalkSpecializes
        (𝒢.specializes_genericUnit s)).hom.comp (φ : _ →+* _)) =
        algebraMap (Localization.AtPrime (sectionPrime σ)) Ω := by
      refine IsLocalization.ringHom_ext (sectionPrime σ).primeCompl (RingHom.ext fun z => ?_)
      have h1 := hsp z
      have h2 := hι z
      simp only [RingHom.comp_apply, RingHom.coe_coe]
      exact (congrArg ι h1).trans h2
    intro a
    exact RingHom.congr_fun hext a
  have hιS : ∀ a : 𝓞 L, ι (𝒢.structMap a) = algebraMap L Ω (algebraMap (𝓞 L) L a) := by
    intro a
    rw [← hφS a, hιA, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply (Localization.AtPrime s.asIdeal) L Ω,
      ← IsScalarTower.algebraMap_apply (𝓞 L) (Localization.AtPrime s.asIdeal) L]
  -- the germ `t₀` of `ε t`
  have hkerS := ker_stalkMap_eq_span 𝒢 s σ φ hφ hker
  have hτmem := stalkSpecializes_mem_maximalIdeal 𝒢 s (f := φ tA)
    (by rw [hkerS]; exact Ideal.mem_span_singleton_self _)
  have ht₀mem : 𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s)
      (φ (ε : Localization.AtPrime (sectionPrime σ)) * φ tA) ∈ maximalIdeal 𝒢.genStalk := by
    rw [map_mul]
    exact Ideal.mul_mem_left _ _ hτmem
  set t₀ : maximalIdeal 𝒢.genStalk := ⟨_, ht₀mem⟩ with ht₀def
  obtain ⟨r, hr, hθ₀⟩ := exists_wedge_eq_smul_of_isUnit 𝒢 s v hs (φ tA)
    (φ (ε : Localization.AtPrime (sectionPrime σ))) (ε.isUnit.map φ) tS t₀ htS rfl
  have hιt₀ : ι (t₀ : 𝒢.genStalk) =
      algebraMap (Localization.AtPrime (sectionPrime σ)) Ω ((ε : _) * tA) := by
    rw [ht₀def]
    change ι (𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s)
      (φ (ε : Localization.AtPrime (sectionPrime σ)) * φ tA)) = _
    rw [← map_mul, hιA]
  -- valuations of constants
  have hPL : ∀ (Q : TauCeti.Place L F) (c : L), c ≠ 0 → Q.valuation (algebraMap L F c) = 1 :=
    fun Q c hc => Valuation.IsTrivialOn.eq_one c hc
  have hPLle : ∀ (Q : TauCeti.Place L F) (c : L), Q.valuation (algebraMap L F c) ≤ 1 := by
    intro Q c
    by_cases hc : c = 0
    · rw [hc, map_zero, map_zero]
      exact zero_le_one
    · exact (hPL Q c hc).le
  have hΨe : ∀ f : Ω, Ψ (algebraMap (Localization.AtPrime s.asIdeal) Ω e * f) =
      algebraMap L F (algebraMap (Localization.AtPrime s.asIdeal) L e) * Ψ f := by
    intro f
    rw [map_mul, IsScalarTower.algebraMap_apply (Localization.AtPrime s.asIdeal) L Ω,
      AlgEquiv.commutes]
  have he0 : algebraMap (Localization.AtPrime s.asIdeal) L (e : _) ≠ 0 :=
    (e.isUnit.map (algebraMap (Localization.AtPrime s.asIdeal) L)).ne_zero
  set x₀ := algebraMap (Localization.AtPrime s.asIdeal) Ω e * x with hx₀def
  set y₀ := algebraMap (Localization.AtPrime s.asIdeal) Ω e * y with hy₀def
  have hx₀P : P.valuation (Ψ x₀) = WithZero.exp (1 : ℤ) ^ 2 := by
    rw [hx₀def, hΨe, map_mul, hPL P _ he0, one_mul]
    exact SmallGlue.valuation_eq_two_of_mem_poleSpaceIn Ψ P hx2 hx1
  have hy₀P : P.valuation (Ψ y₀) = WithZero.exp (1 : ℤ) ^ 3 := by
    rw [hy₀def, hΨe, map_mul, hPL P _ he0, one_mul]
    exact SmallGlue.valuation_eq_three_of_mem_poleSpaceIn Ψ P hy3 hy2
  have hx₀S : Ψ x₀ ∈ regularAway P := fun Q hQ => by
    rw [hx₀def, hΨe, map_mul, hPL Q _ he0, one_mul]
    exact ((mem_poleSpaceIn_iff Ψ P 2 x).1 hx2).1 Q hQ
  have hy₀S : Ψ y₀ ∈ regularAway P := fun Q hQ => by
    rw [hy₀def, hΨe, map_mul, hPL Q _ he0, one_mul]
    exact ((mem_poleSpaceIn_iff Ψ P 3 y).1 hy3).1 Q hQ
  -- the equation of `W₀ = W0_L` at `(Ψ x₀, Ψ y₀)`
  have hW₀ : ((W0.map (algebraMap (Localization.AtPrime s.asIdeal) L)).baseChange F).toAffine.Equation
      (Ψ x₀) (Ψ y₀) := by
    have h := weierstrass_equation_map (Ψ : Ω →+* F) _ heq
    have hcurve : (W0.map (algebraMap (Localization.AtPrime s.asIdeal) Ω)).map (Ψ : Ω →+* F) =
        (W0.map (algebraMap (Localization.AtPrime s.asIdeal) L)).baseChange F := by
      rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_map, WeierstrassCurve.map_map]
      congr 1
      ext c
      simp only [RingHom.comp_apply, RingHom.coe_coe]
      rw [IsScalarTower.algebraMap_apply (Localization.AtPrime s.asIdeal) L Ω, AlgEquiv.commutes]
    rw [hcurve] at h
    exact h
  -- the generic comparison
  obtain ⟨C, -, hC, hxC, hyC⟩ := exists_variableChange_of_riemannRoch P hfd hdimP
    (W.map (algebraMap K L)) (W0.map (algebraMap (Localization.AtPrime s.asIdeal) L)) hW hW₀
    hX' hY' hx₀P hy₀P hXS hYS hx₀S hy₀S
  -- the first order change of the parameter
  have hpar := valuation_param_sub_le P.valuation one_lt_exp_one_int hX' hY'
    (hPL P _ C.u.ne_zero) (hPLle P C.r) (hPLle P C.s) (hPLle P C.t)
  have hnum : algebraMap L F (C.u : L) ^ 2 * X' + algebraMap L F C.r = Ψ x₀ := by
    rw [hxC, map_pow]
  have hden : algebraMap L F (C.u : L) ^ 3 * Y' +
      algebraMap L F C.s * algebraMap L F (C.u : L) ^ 2 * X' + algebraMap L F C.t = Ψ y₀ := by
    rw [hyC, map_mul, map_pow, map_pow]
  rw [hnum, hden] at hpar
  have hz : -Ψ x₀ / Ψ y₀ =
      Ψ (algebraMap (Localization.AtPrime (sectionPrime σ)) Ω ((ε : _) * tA)) := by
    rw [← map_neg, ← map_div₀, hx₀def, hy₀def, hε]
    simp only [map_mul]
  rw [hz] at hpar
  -- `C.u = n / d`
  obtain ⟨n, d, hd, hnd⟩ := IsFractionRing.div_surjective (A := 𝓞 L) (C.u : L)
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hd0' : algebraMap (𝓞 L) L d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 L) L)).mpr hd0
  have hn0' : algebraMap (𝓞 L) L n ≠ 0 := by
    intro h
    rw [h, zero_div] at hnd
    exact C.u.ne_zero hnd.symm
  have hY0 : Y' ≠ 0 := by
    intro h
    rw [h, map_zero] at hY'
    exact pow_ne_zero 3 WithZero.exp_ne_zero hY'.symm
  -- `d · tG ≡ n · t₀` modulo `𝔪_ξ²`
  set g : 𝒢.genStalk := 𝒢.structMap d * (tG : 𝒢.genStalk) - 𝒢.structMap n * (t₀ : 𝒢.genStalk)
    with hgdef
  have hιg : Ψ (ι g) = -algebraMap L F (algebraMap (𝓞 L) L n) *
      (Ψ (algebraMap (Localization.AtPrime (sectionPrime σ)) Ω ((ε : _) * tA)) -
        (algebraMap L F (C.u : L))⁻¹ * (-X' / Y')) := by
    have hF0 : algebraMap L F (algebraMap (𝓞 L) L n) ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap L F).injective).mpr hn0'
    have hF1 : algebraMap L F (algebraMap (𝓞 L) L d) ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap L F).injective).mpr hd0'
    rw [hgdef, map_sub, map_mul, map_mul, hιS, hιS, hιt₀, map_sub, map_mul, map_mul,
      AlgEquiv.commutes, AlgEquiv.commutes, htG, ← hnd, map_div₀]
    field_simp
    ring
  have hg2 : P.valuation.comap (Ψ : Ω →+* F) (ι g) * WithZero.exp (1 : ℤ) ^ 2 ≤ 1 := by
    rw [Valuation.comap_apply, RingHom.coe_coe, hιg, map_mul, Valuation.map_neg,
      hPL P _ hn0', one_mul]
    exact hpar
  have hgsq : g ∈ maximalIdeal 𝒢.genStalk ^ 2 :=
    mem_maximalIdeal_sq_of_valuation σ hker (P.valuation.comap (Ψ : Ω →+* F)) hgen hPt φη ι hι
      g hg2
  have hwG := wedge_eq_div_smul_of_sub_mem_sq 𝒢 tG t₀ hd0 hgsq
  rw [hnd] at hwG
  refine ⟨W0.map (algebraMap (Localization.AtPrime s.asIdeal) L), C, 𝒢.wedge ![tS],
    (C.u : L) * r, ?_, hC, hθ, hM, ?_, ?_⟩
  · rw [WeierstrassCurve.map_Δ]
    exact valuation_algebraMap_of_isUnit v s hs hΔ
  · rw [hwG, hθ₀, smul_smul]
  · rw [map_mul, hr, mul_one]

end Comparison

end PlaceAssembly

end ZInQ.Contrib.CMHeight62Full
