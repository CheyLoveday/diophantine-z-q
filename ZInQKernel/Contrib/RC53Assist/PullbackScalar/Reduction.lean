import ZInQKernel.Contrib.CloudB3RC53.ModularWeil.IsogenyScalar
import ZInQKernel.Contrib.CloudB3RC53.ModularWeil.DifferentialLine
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Unramified
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Eval

/-!
# Constant pullback coefficients from a differential comparison

The divisor argument is proved here: on a genus-one function field with exact constants,
a nonzero regular Weil differential has zero divisor; a function multiplying it to another
regular differential is a constant. The cotrace of Weil differentials along an isogeny over
`ℚ` preserves regularity, because the different divisor is zero.

The invariant differential is proved to be locally regular in the Kähler sense at every
place. On the affine chart the two partial derivatives generate the unit ideal, giving a
regular expression in `dx` and `dy`. At infinity, with `z = -x/y` and `s = -1/y`, it is
`q⁻¹ dz`, where `q = 1 - a₁z - a₂z² - 2a₃s - 2a₄zs - 3a₆s²` has valuation one.

The remaining input `RationalResidueComparisonFact` concerns arbitrary one-variable function
fields with exact constant field `ℚ`: a function-field-linear Kähler–Weil equivalence,
compatibility with cotrace for finite separable extensions, and local vanishing of
`Res_P(g df)` when `f,g` are integral at `P`. No assertion about elliptic curves or isogeny
coefficients occurs in that input. In particular no elliptic regularity print is needed.

The comparison clauses are a differential dictionary, not a claimed quotation. Rational
differential and pullback conventions are those of Silverman, *The Arithmetic of Elliptic
Curves*, second edition, II.4; the invariant differential is the one in III.5. The local
calculations and all implications here are proofs, not substituted literature assertions.
No printed result is installed as an axiom.

Kinds: definitions of explicit inputs and theorems proved from their displayed hypotheses.
-/

set_option maxHeartbeats 800000

noncomputable section

namespace ZInQ.Contrib.RC53Assist.PullbackScalar

open TauCeti WeierstrassCurve.Affine
open ZInQ.Contrib.CloudB3RC53.ModularWeil

section GenusOne

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- Kind: PROVED. A nonzero regular Weil differential on an exact genus-one function field
has zero divisor. Locators: `Differential/CanonicalDivisor.lean`,
`degree_weilDifferentialDivisor`; `Divisor/Basic.lean`, `Divisor.eq_of_le_of_degree_eq`. -/
theorem regular_weilDivisor_eq_zero (hK : IsFunctionField k K)
    (hex : IsIntegrallyClosedIn k K) (hg : genus k K = 1)
    {ω : Module.Dual k ↥(repartitionSpace k K)}
    (hmem : ω ∈ weilDifferentialSpace k K) (hω : ω ≠ 0)
    (hreg : ω ∈ weilDifferentialFiltration (0 : Divisor k K)) :
    weilDifferentialDivisor hK hex hmem hω = 0 := by
  have hnonneg : (0 : Divisor k K) ≤ weilDifferentialDivisor hK hex hmem hω :=
    (mem_weilDifferentialFiltration_iff_le_weilDifferentialDivisor hK hex hmem hω 0).mp hreg
  have hdeg : Divisor.degree (weilDifferentialDivisor hK hex hmem hω) = 0 := by
    rw [degree_weilDifferentialDivisor, hg]
    norm_num
  exact (Divisor.eq_of_le_of_degree_eq hK hnonneg
    (by rw [Divisor.degree_zero, hdeg])).symm

/-- Kind: PROVED. A function carrying a nonzero regular Weil differential to a regular
Weil differential is a constant on an exact genus-one function field. Locators:
`regular_weilDivisor_eq_zero`; `Differential/CanonicalDivisor.lean`,
`weilDifferentialDivisor_repartitionDualMul`; `Divisor/Principal.lean`,
`Divisor.principal_eq_zero_iff`. -/
theorem constant_of_regular_weil_multiple (hK : IsFunctionField k K)
    (hex : IsIntegrallyClosedIn k K) (hg : genus k K = 1)
    {ω : Module.Dual k ↥(repartitionSpace k K)}
    (hreg : ω ∈ weilDifferentialFiltration (0 : Divisor k K)) (hω : ω ≠ 0)
    (c : K) (hc : repartitionDualMul hK c ω ∈
      weilDifferentialFiltration (0 : Divisor k K)) :
    c ∈ Set.range (algebraMap k K) := by
  rcases eq_or_ne c 0 with rfl | hc0
  · exact ⟨0, map_zero _⟩
  have hmem : ω ∈ weilDifferentialSpace k K :=
    weilDifferentialFiltration_le_weilDifferentialSpace 0 hreg
  have hcmem := repartitionDualMul_mem_weilDifferentialSpace hK c hmem
  have hczero := repartitionDualMul_ne_zero hK hc0 hω
  have hdiv := regular_weilDivisor_eq_zero hK hex hg hmem hω hreg
  have hcdiv := regular_weilDivisor_eq_zero hK hex hg hcmem hczero hc
  have htrans := weilDifferentialDivisor_repartitionDualMul hK hex hmem hω (Units.mk0 c hc0)
  simp only [Units.val_mk0] at htrans
  have hprincipal : Divisor.principal hK (Units.mk0 c hc0) = 0 := by
    rw [hcdiv, hdiv, add_zero] at htrans
    exact htrans.symm
  exact (Divisor.principal_eq_zero_iff hK hex (Units.mk0 c hc0)).mp hprincipal

end GenusOne

/-- Kind: DEFINITION of comparison data, not an existence theorem. An equivalence between
Kähler and Weil differentials that is linear over the function field, with the Weil action
`(f • ω)(a) = ω(f • a)`. Locators: Silverman II.4, rational differentials (dictionary);
`Differential/Weil.lean`, `weilDifferentialSpaceModule`. -/
abbrev KaehlerWeilComparison (K : Type) [Field K] [Algebra ℚ K]
    (hK : IsFunctionField ℚ K) : Type :=
  letI := weilDifferentialSpaceModule hK
  KaehlerDifferential ℚ K ≃ₗ[K] ↥(weilDifferentialSpace ℚ K)

/-- Kind: DEFINITION of required comparison data on all one-variable function fields with
exact constant field `ℚ`. This supplies no naturality or regularity theorem. Locators:
`KaehlerWeilComparison`; Silverman II.4, differential dictionary. -/
def ComparisonFamily : Type 1 :=
  ∀ (K : Type) [Field K] [Algebra ℚ K] (hK : IsFunctionField ℚ K)
    (_hex : IsIntegrallyClosedIn ℚ K), KaehlerWeilComparison K hK

/-- Kind: DEFINITION of an explicit compatibility input. For every finite separable
extension of exact one-variable function fields over `ℚ`, comparison carries the Kähler
pullback to the Weil cotrace, for every differential. This is not a statement about an
isogeny scalar. Locators: Silverman II.4, pullback of rational differentials (dictionary);
`Differential/Cotrace.lean`, `weilDifferentialCotrace`. -/
def CotraceCompatibility (C : ComparisonFamily) : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L]
    [Algebra K L] [IsScalarTower ℚ K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (hK : IsFunctionField ℚ K) (hL : IsFunctionField ℚ L)
    (hexK : IsIntegrallyClosedIn ℚ K) (hexL : IsIntegrallyClosedIn ℚ L)
    (η : KaehlerDifferential ℚ K),
    C L hL hexL (KaehlerDifferential.map ℚ ℚ K L η) =
      weilDifferentialCotrace ℚ L hK hL (C K hK hexK η)

/-- Kind: DEFINITION. Restriction of the comparison family to the function field of an
elliptic Weierstrass equation. Locators: `ComparisonFamily`;
`Affine/FunctionField/Genus.lean`, `isIntegrallyClosedIn_functionField`. -/
def curveComparison (C : ComparisonFamily) (W : WeierstrassCurve.Affine ℚ)
    [W.IsElliptic] : KaehlerWeilComparison W.FunctionField W.isFunctionField :=
  C W.FunctionField W.isFunctionField (isIntegrallyClosedIn_functionField W)

/-- Kind: DEFINITION of the single-curve regularity condition. The comparison sends the
specific differential `dx / (2y + a₁x + a₃)` into the zero step of the Weil filtration.
There is no isogeny in this statement. Locators: Silverman III.5, invariant differentials;
`invariantRegularity_of_localExactRegularity`, which proves this condition from the generic
local comparison input. No elliptic regularity assertion is assumed in the final reduction. -/
def InvariantRegularity (C : ComparisonFamily) : Prop :=
  ∀ (W : WeierstrassCurve.Affine ℚ) [W.IsElliptic],
    (curveComparison C W (invariantDifferential W) :
      Module.Dual ℚ ↥(repartitionSpace ℚ W.FunctionField)) ∈
        weilDifferentialFiltration (0 : Divisor ℚ W.FunctionField)

/-- Kind: PROVED. Function-field linearity of the comparison, expressed using the action
on repartition duals. Locators: `KaehlerWeilComparison`;
`Differential/Weil.lean`, `coe_weilDifferentialSpaceModule_smul`. -/
theorem comparison_smul (K : Type) [Field K] [Algebra ℚ K]
    (hK : IsFunctionField ℚ K) (e : KaehlerWeilComparison K hK)
    (c : K) (η : KaehlerDifferential ℚ K) :
    (e (c • η) : Module.Dual ℚ ↥(repartitionSpace ℚ K)) =
      repartitionDualMul hK c (e η : Module.Dual ℚ ↥(repartitionSpace ℚ K)) := by
  let _ := weilDifferentialSpaceModule hK
  rw [map_smul, coe_weilDifferentialSpaceModule_smul]

/-- Kind: DEFINITION, constructed without a differential-comparison input. The pullback of
Weil differentials along a rational isogeny is the cotrace for its induced function-field
extension. Locators: `Isogeny/FunctionField.lean`, `fieldPullback`;
`Isogeny/Separability.lean`, `isSeparable_functionField`;
`Differential/Cotrace.lean`, `weilDifferentialCotrace`. -/
def weilPullback {W₁ W₂ : WeierstrassCurve.Affine ℚ} [W₁.IsElliptic] [W₂.IsElliptic]
    (β : TauCeti.Isogeny W₁ W₂) :
    ↥(weilDifferentialSpace ℚ W₂.FunctionField) →ₗ[ℚ]
      ↥(weilDifferentialSpace ℚ W₁.FunctionField) := by
  have : CharZero β.fieldPullback.fieldRange :=
    charZero_of_injective_algebraMap (algebraMap ℚ β.fieldPullback.fieldRange).injective
  let : Algebra W₂.FunctionField W₁.FunctionField := β.fieldPullback.toRingHom.toAlgebra
  have hmap : ∀ z, algebraMap W₂.FunctionField W₁.FunctionField z = β.fieldPullback z :=
    fun z => RingHom.congr_fun (RingHom.algebraMap_toAlgebra β.fieldPullback.toRingHom) z
  have := β.isScalarTower_of_algebraMap_eq_fieldPullback hmap
  have := β.finiteDimensional_functionField hmap
  have := β.isSeparable_functionField hmap
  exact weilDifferentialCotrace ℚ W₁.FunctionField W₂.isFunctionField W₁.isFunctionField

/-- Kind: PROVED, with no comparison input. The Weil pullback of a regular differential
along a rational isogeny is regular. Locators: `Isogeny/Unramified.lean`,
`Isogeny.different_eq_zero`; `Differential/Cotrace.lean`,
`weilDifferentialCotrace_mem_weilDifferentialFiltration`. -/
theorem weilPullback_regular {W₁ W₂ : WeierstrassCurve.Affine ℚ}
    [W₁.IsElliptic] [W₂.IsElliptic] (β : TauCeti.Isogeny W₁ W₂)
    (ω : ↥(weilDifferentialSpace ℚ W₂.FunctionField))
    (hω : (ω : Module.Dual ℚ ↥(repartitionSpace ℚ W₂.FunctionField)) ∈
      weilDifferentialFiltration (0 : Divisor ℚ W₂.FunctionField)) :
    (weilPullback β ω : Module.Dual ℚ ↥(repartitionSpace ℚ W₁.FunctionField)) ∈
      weilDifferentialFiltration (0 : Divisor ℚ W₁.FunctionField) := by
  have : CharZero β.fieldPullback.fieldRange :=
    charZero_of_injective_algebraMap (algebraMap ℚ β.fieldPullback.fieldRange).injective
  let : Algebra W₂.FunctionField W₁.FunctionField := β.fieldPullback.toRingHom.toAlgebra
  have hmap : ∀ z, algebraMap W₂.FunctionField W₁.FunctionField z = β.fieldPullback z :=
    fun z => RingHom.congr_fun (RingHom.algebraMap_toAlgebra β.fieldPullback.toRingHom) z
  have := β.isScalarTower_of_algebraMap_eq_fieldPullback hmap
  have := β.finiteDimensional_functionField hmap
  have := β.isSeparable_functionField hmap
  have h := weilDifferentialCotrace_mem_weilDifferentialFiltration
    W₂.isFunctionField W₁.isFunctionField ω hω
  simpa only [weilPullback, map_zero, β.different_eq_zero hmap, zero_add] using h

/-- Kind: PROVED from the displayed generic compatibility input. Comparison intertwines
the actual isogeny pullback of Kähler differentials with the constructed Weil pullback.
Locators: `CotraceCompatibility`; `Isogeny/Differential.lean`,
`pullbackDifferential_apply`; `RingTheory/Kaehler/MapSemilinear.lean`,
`mapSemilinear_toAlgHom_apply`. -/
theorem comparison_pullback (C : ComparisonFamily) (hC : CotraceCompatibility C)
    {W₁ W₂ : WeierstrassCurve.Affine ℚ} [W₁.IsElliptic] [W₂.IsElliptic]
    (β : TauCeti.Isogeny W₁ W₂) (η : KaehlerDifferential ℚ W₂.FunctionField) :
    curveComparison C W₁ (β.pullbackDifferential η) =
      weilPullback β (curveComparison C W₂ η) := by
  have : CharZero β.fieldPullback.fieldRange :=
    charZero_of_injective_algebraMap (algebraMap ℚ β.fieldPullback.fieldRange).injective
  let : Algebra W₂.FunctionField W₁.FunctionField := β.fieldPullback.toRingHom.toAlgebra
  have hmap : ∀ z, algebraMap W₂.FunctionField W₁.FunctionField z = β.fieldPullback z :=
    fun z => RingHom.congr_fun (RingHom.algebraMap_toAlgebra β.fieldPullback.toRingHom) z
  have := β.isScalarTower_of_algebraMap_eq_fieldPullback hmap
  have := β.finiteDimensional_functionField hmap
  have := β.isSeparable_functionField hmap
  have hhom : IsScalarTower.toAlgHom ℚ W₂.FunctionField W₁.FunctionField = β.fieldPullback :=
    AlgHom.ext hmap
  have hη : KaehlerDifferential.map ℚ ℚ W₂.FunctionField W₁.FunctionField η =
      β.pullbackDifferential η := by
    rw [TauCeti.Isogeny.pullbackDifferential_apply,
      ← KaehlerDifferential.mapSemilinear_toAlgHom_apply, hhom]
  simpa only [curveComparison, weilPullback, hη] using
    hC W₂.FunctionField W₁.FunctionField W₂.isFunctionField W₁.isFunctionField
      (isIntegrallyClosedIn_functionField W₂) (isIntegrallyClosedIn_functionField W₁) η

/-- Kind: PROVED from the displayed comparison and single-curve inputs. This is a reduction
of the exact constant-coefficient target, not an unconditional discharge. Locators:
`constant_of_regular_weil_multiple`, `comparison_pullback`, `weilPullback_regular`;
`ModularWeil/IsogenyScalar.lean`, `PullbackCoefficientConstantGlue`. -/
theorem pullbackCoefficientConstantGlue_of_comparison (C : ComparisonFamily)
    (hC : CotraceCompatibility C) (hω : InvariantRegularity C) :
    PullbackCoefficientConstantGlue := by
  intro E₁ E₂ h₁ h₂ β c hc
  let e₁ := curveComparison C E₁.toAffine
  let e₂ := curveComparison C E₂.toAffine
  have hne : (e₁ (invariantDifferential E₁.toAffine) :
      Module.Dual ℚ ↥(repartitionSpace ℚ E₁.toAffine.FunctionField)) ≠ 0 := by
    intro hzero
    have hz : e₁ (invariantDifferential E₁.toAffine) = 0 := Subtype.ext hzero
    exact invariantDifferential_ne_zero E₁.toAffine
      (e₁.injective (hz.trans (map_zero e₁).symm))
  have hpreg : (e₁ (β.pullbackDifferential (invariantDifferential E₂.toAffine)) :
      Module.Dual ℚ ↥(repartitionSpace ℚ E₁.toAffine.FunctionField)) ∈
      weilDifferentialFiltration (0 : Divisor ℚ E₁.toAffine.FunctionField) := by
    change (curveComparison C E₁.toAffine
      (β.pullbackDifferential (invariantDifferential E₂.toAffine)) :
        Module.Dual ℚ ↥(repartitionSpace ℚ E₁.toAffine.FunctionField)) ∈ _
    rw [comparison_pullback C hC]
    exact weilPullback_regular β (e₂ (invariantDifferential E₂.toAffine)) (hω E₂.toAffine)
  have hcreg : repartitionDualMul E₁.toAffine.isFunctionField c
      (e₁ (invariantDifferential E₁.toAffine) :
        Module.Dual ℚ ↥(repartitionSpace ℚ E₁.toAffine.FunctionField)) ∈
      weilDifferentialFiltration (0 : Divisor ℚ E₁.toAffine.FunctionField) := by
    rw [← comparison_smul E₁.toAffine.FunctionField E₁.toAffine.isFunctionField e₁, hc]
    exact hpreg
  exact constant_of_regular_weil_multiple E₁.toAffine.isFunctionField
    (isIntegrallyClosedIn_functionField E₁.toAffine) (genus_functionField E₁.toAffine)
    (hω E₁.toAffine) hne c hcreg

namespace Local

open Polynomial
open scoped Polynomial.Bivariate

variable {k : Type*} [Field k]

/-- Kind: PROVED. The two partial derivatives generate the unit ideal
in the coordinate ring. Locators: `CoordinateRing.equation_of_algHom`,
`WeierstrassCurve.Affine.equation_iff_nonsingular`, `Ideal.mem_span_pair`. -/
theorem coordinate_partials_bezout (W : WeierstrassCurve.Affine k) [W.IsElliptic] :
    ∃ a b : W.CoordinateRing,
      a * CoordinateRing.mk W W.polynomialX + b * CoordinateRing.mk W W.polynomialY = 1 := by
  have htop : Ideal.span ({CoordinateRing.mk W W.polynomialX,
      CoordinateRing.mk W W.polynomialY} : Set W.CoordinateRing) = ⊤ := by
    by_contra htop
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ htop
    let _ := hM
    let f : W.CoordinateRing →ₐ[k] W.CoordinateRing ⧸ M := Ideal.Quotient.mkₐ k M
    have hns := equation_iff_nonsingular.mp (CoordinateRing.equation_of_algHom f)
    have hx : f (CoordinateRing.mk W W.polynomialX) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span (Set.mem_insert _ _)))
    have hy : f (CoordinateRing.mk W W.polynomialY) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span (Set.mem_insert_of_mem _ rfl)))
    rw [CoordinateRing.algHom_mk_eq_evalEval, ← map_polynomialX] at hx
    rw [CoordinateRing.algHom_mk_eq_evalEval, ← map_polynomialY] at hy
    exact hns.2.elim (fun h => h hx) (fun h => h hy)
  apply Ideal.mem_span_pair.mp
  rw [htop]
  trivial

/-- Kind: PROVED. Differentiating the Weierstrass equation gives the
coefficient of `dy` in the separating coordinate `x`. Locators:
`equation_genericX_genericY`, `derivativeOfSeparating_self`, `Derivation.leibniz_pow`. -/
theorem denominator_mul_derivativeY (W : WeierstrassCurve.Affine k) [W.IsElliptic] :
    invariantDifferentialDenom W *
        derivativeOfSeparating (transcendental_genericX W) (genericY W) =
      -algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W W.polynomialX) := by
  let δ := derivativeOfSeparating (transcendental_genericX W)
  have hx : δ (genericX W) = 1 := derivativeOfSeparating_self _
  have heq := (equation_iff (W := (W⁄W.FunctionField).toAffine) _ _).mp
    (equation_genericX_genericY W)
  have hd := congrArg δ heq
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at hd
  simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow,
    Derivation.map_algebraMap, hx, smul_eq_mul,
    nsmul_eq_mul, mul_one, pow_one, Nat.add_one_sub_one] at hd
  change invariantDifferentialDenom W * δ (genericY W) = _
  rw [invariantDifferentialDenom_def]
  have hpx : algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W W.polynomialX) =
      algebraMap k W.FunctionField W.a₁ * genericY W -
        (3 * genericX W ^ 2 + 2 * algebraMap k W.FunctionField W.a₂ * genericX W +
          algebraMap k W.FunctionField W.a₄) := by
    rw [← evalEval_genericX_genericY, ← map_polynomialX, evalEval_polynomialX]
    rfl
  rw [hpx]
  linear_combination hd

/-- Kind: PROVED. The invariant differential is a regular linear
combination of `dx` and `dy` on the affine chart. Locators:
`coordinate_partials_bezout`, `denominator_mul_derivativeY`, `invariantDifferential_def`. -/
theorem invariant_affine_expression (W : WeierstrassCurve.Affine k) [W.IsElliptic]
    {a b : W.CoordinateRing}
    (hab : a * CoordinateRing.mk W W.polynomialX +
      b * CoordinateRing.mk W W.polynomialY = 1) :
    invariantDifferential W =
      algebraMap W.CoordinateRing W.FunctionField b •
        KaehlerDifferential.D k W.FunctionField (genericX W) +
      (-algebraMap W.CoordinateRing W.FunctionField a) •
        KaehlerDifferential.D k W.FunctionField (genericY W) := by
  let A := algebraMap W.CoordinateRing W.FunctionField a
  let B := algebraMap W.CoordinateRing W.FunctionField b
  let d := invariantDifferentialDenom W
  let p := algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W W.polynomialX)
  have hd : d ≠ 0 := invariantDifferentialDenom_ne_zero W
  have hAB : A * p + B * d = 1 := by
    have h := congrArg (algebraMap W.CoordinateRing W.FunctionField) hab
    change algebraMap W.CoordinateRing W.FunctionField a *
      algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W W.polynomialX) +
      algebraMap W.CoordinateRing W.FunctionField b * invariantDifferentialDenom W = 1
    rw [invariantDifferentialDenom_eq_algebraMap_mk_polynomialY]
    simpa only [map_add, map_mul, map_one] using h
  have hdy : derivativeOfSeparating (transcendental_genericX W) (genericY W) = -p / d := by
    apply (eq_div_iff hd).mpr
    simpa only [mul_comm] using denominator_mul_derivativeY W
  rw [invariantDifferential_def,
    ← derivativeOfSeparating_smul_D (transcendental_genericX W) (genericY W),
    hdy, smul_smul, ← add_smul]
  congr 1
  change d⁻¹ = B + (-A) * (-p / d)
  field_simp
  linear_combination -hAB

/-- Kind: DEFINITION. The usual parameter `z = -x/y` at infinity.
Locator: Silverman III.5, invariant differential calculation. -/
def parameterAtInfinity (W : WeierstrassCurve.Affine k) : W.FunctionField :=
  -genericX W / genericY W

/-- Kind: DEFINITION. The auxiliary coordinate `s = -1/y` at infinity.
Locator: the Weierstrass equation in the chart containing infinity. -/
def auxiliaryAtInfinity (W : WeierstrassCurve.Affine k) : W.FunctionField :=
  -(genericY W)⁻¹

/-- Kind: DEFINITION. The coefficient `q` in `dz = q ω`, written in coordinates regular
at infinity. Locators: `parameterAtInfinity`, `auxiliaryAtInfinity`, Weierstrass equation. -/
def differentialUnitAtInfinity (W : WeierstrassCurve.Affine k) : W.FunctionField :=
  1 - (algebraMap k W.FunctionField W.a₁ * parameterAtInfinity W +
    algebraMap k W.FunctionField W.a₂ * parameterAtInfinity W ^ 2 +
    algebraMap k W.FunctionField (2 * W.a₃) * auxiliaryAtInfinity W +
    algebraMap k W.FunctionField (2 * W.a₄) * parameterAtInfinity W * auxiliaryAtInfinity W +
    algebraMap k W.FunctionField (3 * W.a₆) * auxiliaryAtInfinity W ^ 2)

/-- Kind: PROVED. The parameter `-x/y` has positive order at infinity.
Locator: `Affine/FunctionField/InfinityPlace/Basic.lean`, `infinityPlace.X_div_mk_Y`. -/
theorem valuation_parameterAtInfinity (W : WeierstrassCurve.Affine k) :
    W.infinityPlace (parameterAtInfinity W) = WithZero.exp (-1 : ℤ) := by
  rw [parameterAtInfinity, neg_div, Valuation.map_neg, genericX_def, genericY_def,
    CoordinateRing.mk_C_eq_algebraMap]
  exact infinityPlace.X_div_mk_Y W

/-- Kind: PROVED. The auxiliary coordinate `-1/y` has positive order
at infinity. Locator: `Affine/FunctionField/InfinityPlace/Basic.lean`, `infinityPlace.mk_Y`. -/
theorem valuation_auxiliaryAtInfinity (W : WeierstrassCurve.Affine k) :
    W.infinityPlace (auxiliaryAtInfinity W) = WithZero.exp (-3 : ℤ) := by
  rw [auxiliaryAtInfinity, Valuation.map_neg, map_inv₀, genericY_def, infinityPlace.mk_Y,
    ← WithZero.exp_neg]

/-- Kind: PROVED. The coefficient `q` has valuation one at infinity.
Locators: `valuation_parameterAtInfinity`, `valuation_auxiliaryAtInfinity`,
`Valuation.map_sub_eq_of_lt_left`. -/
theorem valuation_differentialUnitAtInfinity (W : WeierstrassCurve.Affine k) :
    W.infinityPlace (differentialUnitAtInfinity W) = 1 := by
  let v := W.infinityPlace
  let z := parameterAtInfinity W
  let s := auxiliaryAtInfinity W
  have hz : v z < 1 := by
    change W.infinityPlace (parameterAtInfinity W) < 1
    rw [valuation_parameterAtInfinity, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hs : v s < 1 := by
    change W.infinityPlace (auxiliaryAtInfinity W) < 1
    rw [valuation_auxiliaryAtInfinity, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hmul {f g : W.FunctionField} (hf : v f ≤ 1) (hg : v g < 1) : v (f * g) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hf zero_le) (by simpa using hg)
  have hconst (a : k) {f : W.FunctionField} (hf : v f < 1) :
      v (algebraMap k W.FunctionField a * f) < 1 :=
    hmul (Valuation.IsTrivialOn.valuation_algebraMap_le_one v a) hf
  have hz2 : v (z ^ 2) < 1 := by simpa only [pow_two] using hmul hz.le hz
  have hs2 : v (s ^ 2) < 1 := by simpa only [pow_two] using hmul hs.le hs
  have hzs : v (z * s) < 1 := hmul hz.le hs
  have hsum : v (algebraMap k W.FunctionField W.a₁ * z +
      algebraMap k W.FunctionField W.a₂ * z ^ 2 +
      algebraMap k W.FunctionField (2 * W.a₃) * s +
      algebraMap k W.FunctionField (2 * W.a₄) * z * s +
      algebraMap k W.FunctionField (3 * W.a₆) * s ^ 2) < 1 :=
    v.map_add_lt (v.map_add_lt (v.map_add_lt
      (v.map_add_lt (hconst W.a₁ hz) (hconst W.a₂ hz2)) (hconst (2 * W.a₃) hs))
      (by simpa only [mul_assoc] using hconst (2 * W.a₄) hzs)) (hconst (3 * W.a₆) hs2)
  change v (1 - _) = 1
  exact (v.map_sub_eq_of_lt_left (by simpa only [map_one] using hsum)).trans (map_one v)

/-- Kind: PROVED. The invariant differential is `q⁻¹ dz` at infinity,
with `q` a unit of the valuation ring. Locators: `denominator_mul_derivativeY`,
`equation_genericX_genericY`, `valuation_differentialUnitAtInfinity`. -/
theorem invariant_infinity_expression (W : WeierstrassCurve.Affine k) [W.IsElliptic] :
    invariantDifferential W = (differentialUnitAtInfinity W)⁻¹ •
      KaehlerDifferential.D k W.FunctionField (parameterAtInfinity W) := by
  let δ := derivativeOfSeparating (transcendental_genericX W)
  let x := genericX W
  let y := genericY W
  let d := invariantDifferentialDenom W
  let p := algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W W.polynomialX)
  let q := differentialUnitAtInfinity W
  have hd : d ≠ 0 := invariantDifferentialDenom_ne_zero W
  have hy : y ≠ 0 := by
    intro hy
    have hval : W.infinityPlace y = WithZero.exp (3 : ℤ) := by
      change W.infinityPlace (genericY W) = _
      rw [genericY_def, infinityPlace.mk_Y]
    rw [hy, map_zero] at hval
    exact WithZero.exp_ne_zero hval.symm
  have hq : q ≠ 0 := by
    intro hq
    have hval := valuation_differentialUnitAtInfinity W
    change W.infinityPlace q = 1 at hval
    rw [hq, map_zero] at hval
    exact zero_ne_one hval
  have hdy : δ y = -p / d := by
    apply (eq_div_iff hd).mpr
    simpa only [mul_comm] using denominator_mul_derivativeY W
  have hx : δ x = 1 := derivativeOfSeparating_self _
  have heq := (equation_iff (W := (W⁄W.FunctionField).toAffine) _ _).mp
    (equation_genericX_genericY W)
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at heq
  have hp : p = algebraMap k W.FunctionField W.a₁ * y -
      (3 * x ^ 2 + 2 * algebraMap k W.FunctionField W.a₂ * x +
        algebraMap k W.FunctionField W.a₄) := by
    change algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W W.polynomialX) = _
    rw [← evalEval_genericX_genericY, ← map_polynomialX, evalEval_polynomialX]
    rfl
  have hqcoef : q * y ^ 2 = -d * y - x * p := by
    dsimp only [q, differentialUnitAtInfinity, parameterAtInfinity, auxiliaryAtInfinity]
    change (1 - (algebraMap k W.FunctionField W.a₁ * (-x / y) +
      algebraMap k W.FunctionField W.a₂ * (-x / y) ^ 2 +
      algebraMap k W.FunctionField (2 * W.a₃) * -y⁻¹ +
      algebraMap k W.FunctionField (2 * W.a₄) * (-x / y) * -y⁻¹ +
      algebraMap k W.FunctionField (3 * W.a₆) * (-y⁻¹) ^ 2)) * y ^ 2 = _
    simp only [map_mul, map_ofNat]
    field_simp [hy]
    rw [hp]
    dsimp only [d, x, y]
    rw [invariantDifferentialDenom_def]
    linear_combination 3 * heq
  have hder : δ (parameterAtInfinity W) = q / d := by
    rw [parameterAtInfinity, Derivation.leibniz_div, map_neg]
    change y⁻¹ ^ 2 * (y * -(δ x) - (-x) * δ y) = q / d
    rw [hx, hdy]
    field_simp [hy, hd]
    linear_combination -hqcoef
  rw [invariantDifferential_def,
    ← derivativeOfSeparating_smul_D (transcendental_genericX W) (parameterAtInfinity W),
    hder, smul_smul]
  congr 1
  change d⁻¹ = q⁻¹ * (q / d)
  field_simp

/-- Kind: DEFINITION. The local differential subspace is generated over the constants by
`a df` for functions `a` and `f` in the valuation ring. Locator: Silverman II.4, regular
rational differentials; the definition uses only Kähler differentials and valuation rings. -/
def localKaehlerSpace {K : Type*} [Field K] [Algebra k K] (P : Place k K) :
    Submodule k (KaehlerDifferential k K) :=
  Submodule.span k {η | ∃ a f : K, a ∈ P.integers ∧ f ∈ P.integers ∧
    a • KaehlerDifferential.D k K f = η}

/-- Kind: PROVED. The concrete invariant differential belongs to the
local differential subspace at every place, without a Weil-comparison input.
Locators: `invariant_affine_expression`, `invariant_infinity_expression`,
`Place.valuation_algebraMap_le_one_of_ne_infinity`. -/
theorem invariant_mem_localKaehlerSpace (W : WeierstrassCurve.Affine k) [W.IsElliptic]
    (P : Place k W.FunctionField) : invariantDifferential W ∈ localKaehlerSpace P := by
  by_cases hP : P = Place.infinity W
  · subst P
    rw [invariant_infinity_expression W]
    apply Submodule.subset_span
    refine ⟨(differentialUnitAtInfinity W)⁻¹, parameterAtInfinity W, ?_, ?_, rfl⟩
    · rw [Place.mem_integers_iff, Place.valuation_infinity, map_inv₀,
        valuation_differentialUnitAtInfinity, inv_one]
    · rw [Place.mem_integers_iff, Place.valuation_infinity, valuation_parameterAtInfinity,
        ← WithZero.exp_zero, WithZero.exp_le_exp]
      norm_num
  · obtain ⟨a, b, hab⟩ := coordinate_partials_bezout W
    have hcoord (r : W.CoordinateRing) : algebraMap W.CoordinateRing W.FunctionField r ∈
        P.integers := P.mem_integers_iff.mpr (Place.valuation_algebraMap_le_one_of_ne_infinity hP r)
    have hx : genericX W ∈ P.integers := by rw [genericX_def]; exact hcoord _
    have hy : genericY W ∈ P.integers := by rw [genericY_def]; exact hcoord _
    rw [invariant_affine_expression W hab]
    apply Submodule.add_mem
    · exact Submodule.subset_span ⟨_, _, hcoord b, hx, rfl⟩
    · exact Submodule.subset_span ⟨_, _, P.integers.neg_mem _ (hcoord a), hy, rfl⟩

end Local

/-- Kind: DEFINITION of a generic local comparison input. At any place of any exact
one-variable function field over `ℚ`, the local component of the compared exact differential
`df` kills every integral function whenever `f` is integral. In residue language this is
`Res_P(g df) = 0` for `f,g ∈ O_P`. There is no elliptic curve or isogeny in the statement.
Locators: Silverman II.4, regular differentials (dictionary);
`Differential/LocalComponent.lean`, `repartitionDualComponent`. -/
def LocalExactRegularity (C : ComparisonFamily) : Prop :=
  ∀ (K : Type) [Field K] [Algebra ℚ K] (hK : IsFunctionField ℚ K)
    (hex : IsIntegrallyClosedIn ℚ K) (P : Place ℚ K) (f g : K),
    f ∈ P.integers → g ∈ P.integers →
      repartitionDualComponent
        (C K hK hex (KaehlerDifferential.D ℚ K f) :
          Module.Dual ℚ ↥(repartitionSpace ℚ K)) P g = 0

/-- Kind: PROVED from the displayed generic local comparison input. A differential lying
in the local Kähler subspace at every place is sent to a regular Weil differential.
Locators: `LocalExactRegularity`, `Local.localKaehlerSpace`, `comparison_smul`;
`Differential/LocalComponent.lean`,
`mem_weilDifferentialFiltration_iff_repartitionDualComponent_eq_zero`. -/
theorem comparison_regular_of_local (C : ComparisonFamily) (hL : LocalExactRegularity C)
    (K : Type) [Field K] [Algebra ℚ K] (hK : IsFunctionField ℚ K)
    (hex : IsIntegrallyClosedIn ℚ K) (η : KaehlerDifferential ℚ K)
    (hη : ∀ P : Place ℚ K, η ∈ Local.localKaehlerSpace P) :
    (C K hK hex η : Module.Dual ℚ ↥(repartitionSpace ℚ K)) ∈
      weilDifferentialFiltration (0 : Divisor ℚ K) := by
  apply (mem_weilDifferentialFiltration_iff_repartitionDualComponent_eq_zero
    (C K hK hex η).prop).mpr
  intro P g hg
  rw [AlgebraicGeometry.WeilDivisor.coeff_zero, WithZero.exp_zero] at hg
  have hgreg : g ∈ P.integers := P.mem_integers_iff.mpr hg
  have hloc := hη P
  change η ∈ Submodule.span ℚ {θ | ∃ a f : K, a ∈ P.integers ∧ f ∈ P.integers ∧
    a • KaehlerDifferential.D ℚ K f = θ} at hloc
  have hvanish : ∀ g : K, g ∈ P.integers →
      repartitionDualComponent (C K hK hex η :
        Module.Dual ℚ ↥(repartitionSpace ℚ K)) P g = 0 := by
    refine Submodule.span_induction
      (p := fun θ _ => ∀ g : K, g ∈ P.integers →
        repartitionDualComponent (C K hK hex θ :
          Module.Dual ℚ ↥(repartitionSpace ℚ K)) P g = 0)
      ?_ ?_ ?_ ?_ hloc
    · intro θ hθ g hg
      obtain ⟨a, f, ha, hf, rfl⟩ := hθ
      rw [comparison_smul, repartitionDualComponent_repartitionDualMul]
      exact hL K hK hex P f (a * g) hf (mul_mem ha hg)
    · intro g hg
      simp only [map_zero, Submodule.coe_zero, repartitionDualComponent_apply, LinearMap.zero_apply]
    · intro θ ψ hθ hψ ihθ ihψ g hg
      simp only [map_add, Submodule.coe_add, repartitionDualComponent_apply, LinearMap.add_apply]
      change repartitionDualComponent (C K hK hex θ :
        Module.Dual ℚ ↥(repartitionSpace ℚ K)) P g +
        repartitionDualComponent (C K hK hex ψ :
          Module.Dual ℚ ↥(repartitionSpace ℚ K)) P g = 0
      rw [ihθ g hg, ihψ g hg, zero_add]
    · intro r θ hθ ihθ g hg
      rw [← algebraMap_smul K r θ, comparison_smul, repartitionDualComponent_repartitionDualMul]
      exact ihθ (algebraMap ℚ K r * g) (mul_mem (P.algebraMap_mem_integers r) hg)
  exact hvanish g hgreg

/-- Kind: PROVED from the generic local comparison input, not from an elliptic-curve print.
The specific invariant differential has regular comparison image on every elliptic curve.
Locators: `comparison_regular_of_local`, `Local.invariant_mem_localKaehlerSpace`;
`InvariantRegularity`. -/
theorem invariantRegularity_of_localExactRegularity (C : ComparisonFamily)
    (hL : LocalExactRegularity C) : InvariantRegularity C := by
  intro W hW
  exact comparison_regular_of_local C hL W.FunctionField W.isFunctionField
    (isIntegrallyClosedIn_functionField W) (invariantDifferential W)
    (fun P => Local.invariant_mem_localKaehlerSpace W P)

/-- Kind: DEFINITION of the precisely typed remaining standard comparison fact. There
exists a function-field-linear Kähler–Weil comparison on all exact one-variable function
fields over `ℚ`, compatible with finite separable cotrace and the vanishing of residues
`Res_P(g df)` for integral `f,g`. Neither an elliptic curve nor an isogeny scalar appears
in these clauses. This fact is not proved here. Locators: `ComparisonFamily`,
`CotraceCompatibility`, `LocalExactRegularity`; Silverman II.4 (differential dictionary). -/
def RationalResidueComparisonFact : Prop :=
  ∃ C : ComparisonFamily, CotraceCompatibility C ∧ LocalExactRegularity C

/-- Kind: PROVED from the generic standard comparison fact. This reduces the exact
constant-coefficient target to function-field-linear comparison, cotrace compatibility, and
local vanishing of the residue of an integral exact differential times an integral function.
All elliptic-curve regularity is proved rather than supplied as an input. Locators:
`invariantRegularity_of_localExactRegularity`, `pullbackCoefficientConstantGlue_of_comparison`;
`ModularWeil/IsogenyScalar.lean`, `PullbackCoefficientConstantGlue`. -/
theorem pullbackCoefficientConstantGlue_of_residueComparison (h : RationalResidueComparisonFact) :
    PullbackCoefficientConstantGlue := by
  obtain ⟨C, hC, hL⟩ := h
  exact pullbackCoefficientConstantGlue_of_comparison C hC
    (invariantRegularity_of_localExactRegularity C hL)

/-- Kind: PROVED from the generic standard comparison fact. The complete algebraic
isogeny-scalar formulation follows, including rationality and nonvanishing. Locators:
`pullbackCoefficientConstantGlue_of_residueComparison`;
`ModularWeil/IsogenyScalar.lean`, `isogenyScalarRationalGlue_of_constant`. -/
theorem isogenyScalarRationalGlue_of_residueComparison (h : RationalResidueComparisonFact) :
    IsogenyScalarRationalGlue :=
  isogenyScalarRationalGlue_of_constant (pullbackCoefficientConstantGlue_of_residueComparison h)

end ZInQ.Contrib.RC53Assist.PullbackScalar
