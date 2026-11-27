import ZInQKernel.Contrib.RC53Assist.DiskOrders.Literature

/-!
# The degree-two disk order of the calibration and the genuine Selmer group

Proposition `ex:arith-central-calibration` (`diophantine_zq.tex`, tex 3987–4141), proof at
tex 4007–4014: universal coefficients give
`0 → H¹(C_K) ⊗ ℚ₂/ℤ₂ → Sel_{2^∞}(E/K) → H²(C_K)_tors → 0`, and "the last finite group is
Selmer modulo its maximal divisible subgroup".

For the address curves `E_ℓ` over `K = ℚ(√k)` (the central twist bound to the base change of
`E_ℓ`, `hcurve`), the universal-coefficient map `j` of the integral free part is constructed in
the integral central model from the coefficient comparison `I` (the comparison of the
coefficient-quotient complex with the discrete Selmer complex, the same input that gives rank one
of `H¹(C_K)` under Selmer corank one), and its cokernel is the integral degree-two torsion. Here:

* `card_torsion_two_eq_selmer`: `|H²(C_K)_tors| = |Sel_{2^∞}(E_ℓ/K) / j(free part ⊗ ℚ₂/ℤ₂)|`,
  for the genuine two-primary Selmer group `SelK ℓ k` over `ℚ(√k)`;
* **`diskArith_central_selmer`**: `DiskArith G t shaA` (with `t` the order of the rational
  `2`-primary torsion of the central twist) as soon as the `2`-part of `shaA` is the order of the
  Selmer group modulo the image of the free part (`hSel`).
* **`diskArith_arithmetic`**: the same from the ten cited PRINT statements, `I`, Selmer corank one
  over `K` and `hSel`, with rank one, finite generation, finite torsion and integral duality
  derived; **`diskArith_address`**: the same for `k < 0`, with `K` totally complex and `k` not a
  square derived (`isTotallyComplex_of_neg`, `not_isSquare_of_neg`).

Kinds: PROVED from the named inputs (as in `diskArith_central`, with `hsha` replaced by the
comparison `I` and the Selmer statement `hSel`).
-/

noncomputable section

set_option autoImplicit false

namespace ZInQ.Contrib.RC53Assist.DiskOrders

open NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53
open ZInQ.Contrib.RC53Assist.Calibration
open ZInQ.Contrib.RC53Assist.CalibrationIntegral
open ZInQ.Contrib.RC53Assist.CalibrationShape
open ZInQ.Contrib.RC53Assist.InnerLimitArith (MilneLocalFiniteness MilneGlobalFiniteness)
open ZInQ.Manuscript.RC53Assist.CentralUniversal
open ZInQ.Manuscript.RC53Assist.QuadraticDescent
open ZInQ.Manuscript.RC (SelmerCorankOneOverK)
open ZInQ.Contrib.RC53Assist.DerivedKummer (MilneLocalDualityPrint MilneFiniteLocalDualityPrint)
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteLocalDegreeBound
  (MilneFiniteDegreeBoundPrint)
open ZInQ.Contrib.RC53Assist.IntegralDuality
  (NekovarIntegralCompactLocality NekovarIntegralGlobalDuality)
open ZInQ.Contrib.RC53Assist.DKLocalAdapter (integralCentralKummerDuality_of_literature)

section SelmerBridge

/-- Equality in `ℚ(√k)` is decided classically, as for the point groups of the central model.
Kind: definition. -/
local instance (priority := 10000) quadraticFieldDecEq (k : ℤ) : DecidableEq (QuadraticField k) :=
  fun a b => Classical.propDecidable (a = b)

variable (ℓ : ℕ) (k : ℤ) [(Ecurve ℓ).IsElliptic] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}
  (G : GenuineKummerData (QuadraticField k) E₀ hZ)
  (hcurve : centralCurve G = (Ecurve ℓ).baseChange (QuadraticField k))

/-- **The integral degree-two torsion is the Selmer group modulo the image of the free part**
(tex 4010–4014), for the genuine two-primary Selmer group of `E_ℓ` over `ℚ(√k)`, given the
coefficient comparison `I`. Kind: PROVED. -/
theorem card_torsion_two_eq_selmer
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (I : KummerCoefficientComparison ℓ k G.S (arithmeticCentralFull ℓ k G hcurve)) :
    Nat.card (Submodule.torsion ℤ_[2] ((compactCentralComplex G).homology 2)) =
      Nat.card (SelK ℓ k ⧸ (arithmetic_j ℓ k G.S (arithmeticCentralFull ℓ k G hcurve) I
        (arithmeticCentralFinite ℓ k G hcurve hfinite)).range) := by
  rw [Nat.card_congr (arithmetic_j_cokernelEquiv ℓ k G.S (arithmeticCentralFull ℓ k G hcurve) I
    (arithmeticCentralFinite ℓ k G hcurve hfinite)).toEquiv,
    compactCentral_eq_arithmetic ℓ k G hcurve]

/-- **`DiskArith` from the genuine Selmer group**: for Kummer data `G` over `ℚ(√k)` whose central
twist is the base change of `E_ℓ`, with the inputs of `diskArith_central`, the coefficient
comparison `I`, and `hSel`: the `2`-part of `shaA` is the order of the Selmer group modulo the
image of the integral free part. Kind: PROVED (from the named inputs). -/
theorem diskArith_central_selmer
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (hdual : IntegralCentralKummerDuality G hfinite)
    (hloc : MilneLocalFiniteness) (hglob : MilneGlobalFiniteness)
    (hlocal : MilneLocalDimensionTwo) (hglobal : MilneGlobalDimensionTwo)
    (hK : IsTotallyComplex (QuadraticField k))
    (h2 : ∀ v : HeightOneSpectrum (𝓞 (QuadraticField k)),
      (2 : 𝓞 (QuadraticField k)) ∈ v.asIdeal → v ∈ G.S)
    [Finite (AddCommGroup.primaryComponent (centralCurve G).toAffine.Point 2)]
    (hrank : Module.finrank ℤ_[2] ((compactCentralComplex G).homology 1) = 1)
    (I : KummerCoefficientComparison ℓ k G.S (arithmeticCentralFull ℓ k G hcurve))
    (shaA : ℕ) (hSel : Nat.card (SelK ℓ k ⧸ (arithmetic_j ℓ k G.S
      (arithmeticCentralFull ℓ k G hcurve) I
        (arithmeticCentralFinite ℓ k G hcurve hfinite)).range) = 2 ^ padicValNat 2 shaA) :
    DiskArith G (Nat.card (AddCommGroup.primaryComponent (centralCurve G).toAffine.Point 2))
      shaA :=
  diskArith_central G hfinite hdual hloc hglob hlocal hglobal hK h2 hrank shaA
    ((card_torsion_two_eq_selmer ℓ k G hcurve hfinite I).trans hSel)

/-- **`DiskArith` at an address curve, from cited statements and the Selmer inputs**: for Kummer
data `G` over `ℚ(√k)` whose central twist is the base change of `E_ℓ` (`hcurve`), from the ten
PRINT statements (Milne I.3.4, I.2.3 twice, I.2.1, I.4.15, I.4.10(c), I.2.3; Nekovář 5.4.1,
5.4.3(ii); Silverman VIII.6.7), `K` totally complex, the places above `2` in the support, `k` not a
square, the coefficient comparison `I`, Selmer corank one over `K` (tex 2616–2626), and `hSel`
(the `2`-part of `shaA` is the order of the Selmer group modulo the image of the free part).
Rank one of `H¹(C_K)` is derived. Kind: PROVED (from the named inputs). -/
theorem diskArith_arithmetic (hMW : MordellWeilNumberFieldPrint)
    (hM : MilneLocalDualityPrint) (hF : MilneFiniteLocalDualityPrint)
    (hH : MilneFiniteDegreeBoundPrint)
    (h541 : NekovarIntegralCompactLocality) (h543 : NekovarIntegralGlobalDuality)
    (hglob : MilneGlobalFiniteness) (hloc : MilneLocalFiniteness)
    (hglobal : MilneGlobalDimensionTwo) (hlocal : MilneLocalDimensionTwo)
    (hK : IsTotallyComplex (QuadraticField k))
    (h2 : ∀ v : HeightOneSpectrum (𝓞 (QuadraticField k)),
      (2 : 𝓞 (QuadraticField k)) ∈ v.asIdeal → v ∈ G.S)
    (hk : ¬ IsSquare (k : ℚ))
    (I : KummerCoefficientComparison ℓ k G.S (arithmeticCentralFull ℓ k G hcurve))
    (hSelC : SelmerCorankOneOverK ℓ k) (shaA : ℕ)
    (hSel : Nat.card (SelK ℓ k ⧸ (arithmetic_j ℓ k G.S (arithmeticCentralFull ℓ k G hcurve) I
      (arithmeticCentralFinite ℓ k G hcurve (centralCohomologyFinite G hloc hglob h2))).range) =
        2 ^ padicValNat 2 shaA) :
    DiskArith G (Nat.card (AddCommGroup.primaryComponent (centralCurve G).toAffine.Point 2))
      shaA :=
  have := finite_central_torsion hMW G
  diskArith_central_selmer ℓ k G hcurve (centralCohomologyFinite G hloc hglob h2)
    (integralCentralKummerDuality_of_literature G hM hF hH h541 h543 hglob hloc hglobal hlocal
      hK h2)
    hloc hglob hlocal hglobal hK h2
    (compactCentral_rank_one ℓ k G hcurve (centralCohomologyFinite G hloc hglob h2) hk I hSelC)
    I shaA hSel

/-- `ℚ(√k)` is totally complex for `k < 0` (a real embedding would send `√k` to a real square
root of the negative number `k`; tex 2595–2600, 2720). Kind: PROVED. -/
theorem isTotallyComplex_of_neg {k : ℤ} (hk : k < 0) : IsTotallyComplex (QuadraticField k) := by
  refine ⟨fun v => NumberField.InfinitePlace.not_isReal_iff_isComplex.mp fun hv => ?_⟩
  let ψ := NumberField.InfinitePlace.embedding_of_isReal hv
  let α : QuadraticField k :=
    IntermediateField.AdjoinSimple.gen ℚ (ZInQ.Manuscript.RC53Assist.QuadraticDescent.sqrtK k)
  have hα : α ^ 2 = (k : QuadraticField k) := by
    apply (algebraMap (QuadraticField k) (SeparableClosure ℚ)).injective
    rw [map_pow, IntermediateField.AdjoinSimple.algebraMap_gen, map_intCast,
      ZInQ.Manuscript.RC53Assist.QuadraticDescent.sqrtK_sq, map_intCast]
  have h1 : ψ α ^ 2 = (k : ℝ) := by rw [← map_pow, hα, map_intCast]
  have h2 : (k : ℝ) < 0 := by exact_mod_cast hk
  linarith [sq_nonneg (ψ α)]

/-- A negative integer is not a square in `ℚ`. Kind: PROVED. -/
theorem not_isSquare_of_neg {k : ℤ} (hk : k < 0) : ¬ IsSquare (k : ℚ) := by
  rintro ⟨r, hr⟩
  have h2 : (k : ℚ) < 0 := by exact_mod_cast hk
  nlinarith [mul_self_nonneg r]

/-- **`DiskArith` at an address with negative companion `k`** (tex 2595–2600: `K = ℚ(√k)` is
imaginary): `diskArith_arithmetic` with `K` totally complex and `k` not a square derived from
`k < 0`. Kind: PROVED (from the named inputs). -/
theorem diskArith_address (hMW : MordellWeilNumberFieldPrint)
    (hM : MilneLocalDualityPrint) (hF : MilneFiniteLocalDualityPrint)
    (hH : MilneFiniteDegreeBoundPrint)
    (h541 : NekovarIntegralCompactLocality) (h543 : NekovarIntegralGlobalDuality)
    (hglob : MilneGlobalFiniteness) (hloc : MilneLocalFiniteness)
    (hglobal : MilneGlobalDimensionTwo) (hlocal : MilneLocalDimensionTwo)
    (hneg : k < 0)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 (QuadraticField k)),
      (2 : 𝓞 (QuadraticField k)) ∈ v.asIdeal → v ∈ G.S)
    (I : KummerCoefficientComparison ℓ k G.S (arithmeticCentralFull ℓ k G hcurve))
    (hSelC : SelmerCorankOneOverK ℓ k) (shaA : ℕ)
    (hSel : Nat.card (SelK ℓ k ⧸ (arithmetic_j ℓ k G.S (arithmeticCentralFull ℓ k G hcurve) I
      (arithmeticCentralFinite ℓ k G hcurve (centralCohomologyFinite G hloc hglob h2))).range) =
        2 ^ padicValNat 2 shaA) :
    DiskArith G (Nat.card (AddCommGroup.primaryComponent (centralCurve G).toAffine.Point 2))
      shaA :=
  diskArith_arithmetic ℓ k G hcurve hMW hM hF hH h541 h543 hglob hloc hglobal hlocal
    (isTotallyComplex_of_neg hneg) h2 (not_isSquare_of_neg hneg) I hSelC shaA hSel

end SelmerBridge

end ZInQ.Contrib.RC53Assist.DiskOrders
