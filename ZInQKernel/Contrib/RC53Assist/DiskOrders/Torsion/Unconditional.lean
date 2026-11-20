import ZInQKernel.Contrib.RC53Assist.DiskOrders.ShaBridge
import ZInQKernel.Contrib.RC53Assist.DiskOrders.Torsion.PrimaryFinite

/-!
# The calibration disk orders without the Mordell–Weil theorem

Proposition `ex:arith-central-calibration` (`diophantine_zq.tex`, tex 3987–4141). The degree-zero
disk order (`arith0`, tex 4005–4010: `H¹(C_K)_tors = E^{(h)}(K)[2^∞]`) needs the rational
`2`-primary torsion of the central twist `E^{(h)}/K` to be finite. The disk-order modules obtain
this from the Mordell–Weil theorem (`MordellWeilNumberFieldPrint`, Silverman VIII.6.7) through
`finite_central_torsion`, and that is the only use of that PRINT statement. Here the finiteness is
proved outright, by reduction at one prime of good reduction prime to `2`
(`Torsion.finite_primaryComponent`, Silverman VII.3.1(b)), and every disk-order theorem that took
the Mordell–Weil statement is restated without it, with the same conclusion and otherwise the
same hypotheses.

* `finite_central_torsion_proved`: `E^{(h)}(K)[2^∞]` is finite, for every number field `K`.
* `arith0_central_unconditional`: `arith0_of_mordellWeil` without the Mordell–Weil statement.
* `diskArith_central_of_literature'`, `diskArith_central_of_literature_sha'`: the literature
  routes of `DiskArith` without it.
* `diskArith_arithmetic'`, `diskArith_address'`: the Selmer routes at the address curves.
* `diskArith_address_sha'`: the `Ш` route at the address curves.

Kinds: PROVED (the remaining inputs are exactly those of the original statements, minus the
Mordell–Weil statement).
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

section CentralTorsion

/-- **The rational `2`-primary torsion of the central twist is finite**, for every number field
`K` and without the Mordell–Weil theorem: the central twist `E^{(h)}/K` is an elliptic curve over
the number field `K`, and its `2`-primary torsion is finite by reduction at a prime of good
reduction prime to `2` (`Torsion.finite_primaryComponent`; Silverman, AEC, 2nd ed.,
Proposition VII.3.1(b)). Same statement as `finite_central_torsion` without its Mordell–Weil
argument. Kind: PROVED. -/
theorem finite_central_torsion_proved {K : Type} [Field K] [NumberField K] [DecidableEq K]
    {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} (G : GenuineKummerData K E₀ hZ) :
    Finite (AddCommGroup.primaryComponent (centralCurve G).toAffine.Point 2) :=
  Torsion.finite_primaryComponent K (centralCurve G) Nat.prime_two

end CentralTorsion

section Arith0

open scoped Classical

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}

/-- **The field `arith0` of `DiskArith`, unconditionally** (tex 4005–4010): for the genuine finite
central Kummer Selmer complexes of `G`, `|H⁰| = 2^{i v₂ t}` for all large `i`, `t` the order of
the (finite) rational `2`-primary torsion of the central twist. Same statement as
`arith0_of_mordellWeil` without its Mordell–Weil argument. Kind: PROVED. -/
theorem arith0_central_unconditional (G : GenuineKummerData K E₀ hZ) :
    ∃ i₀ : ℕ, ∀ i ≥ i₀, Nat.card (G.selH i 0) =
      2 ^ (padicValNat 2 (Nat.card (AddCommGroup.primaryComponent
        (centralCurve G).toAffine.Point 2)) * i) :=
  have := finite_central_torsion_proved G
  arith0_central G

end Arith0

section Literature

open scoped Classical

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}

/-- **`DiskArith` for the actual orders, from the cited book statements other than
Mordell–Weil**: `diskArith_central_of_literature` without its Mordell–Weil argument, the
finiteness of the rational `2`-primary torsion being `finite_central_torsion_proved`. Inputs: the
nine PRINT statements (Milne I.3.4, I.2.3 twice, I.2.1, I.4.15, I.4.10(c), I.2.3; Nekovář 5.4.1,
5.4.3(ii)), `K` totally complex, the places above `2` in the support, and rank one of `H¹(C_K)`.
Kind: PROVED (from the named inputs). -/
theorem diskArith_central_of_literature' (G : GenuineKummerData K E₀ hZ)
    (hM : MilneLocalDualityPrint) (hF : MilneFiniteLocalDualityPrint)
    (hH : MilneFiniteDegreeBoundPrint)
    (h541 : NekovarIntegralCompactLocality) (h543 : NekovarIntegralGlobalDuality)
    (hglob : MilneGlobalFiniteness) (hloc : MilneLocalFiniteness)
    (hglobal : MilneGlobalDimensionTwo) (hlocal : MilneLocalDimensionTwo)
    (hK : IsTotallyComplex K)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ G.S)
    (hrank : Module.finrank ℤ_[2] ((compactCentralComplex G).homology 1) = 1) :
    DiskArith G (Nat.card (AddCommGroup.primaryComponent (centralCurve G).toAffine.Point 2))
      (Nat.card (Submodule.torsion ℤ_[2] ((compactCentralComplex G).homology 2))) :=
  have := finite_central_torsion_proved G
  diskArith_central_actual G (centralCohomologyFinite G hloc hglob h2)
    (integralCentralKummerDuality_of_literature G hM hF hH h541 h543 hglob hloc hglobal hlocal
      hK h2)
    hloc hglob hlocal hglobal hK h2 hrank

/-- **`DiskArith` with a declared `Ш`-order, from the cited book statements other than
Mordell–Weil**: `diskArith_central_of_literature_sha` without its Mordell–Weil argument.
Kind: PROVED (from the named inputs). -/
theorem diskArith_central_of_literature_sha' (G : GenuineKummerData K E₀ hZ)
    (hM : MilneLocalDualityPrint) (hF : MilneFiniteLocalDualityPrint)
    (hH : MilneFiniteDegreeBoundPrint)
    (h541 : NekovarIntegralCompactLocality) (h543 : NekovarIntegralGlobalDuality)
    (hglob : MilneGlobalFiniteness) (hloc : MilneLocalFiniteness)
    (hglobal : MilneGlobalDimensionTwo) (hlocal : MilneLocalDimensionTwo)
    (hK : IsTotallyComplex K)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ G.S)
    (hrank : Module.finrank ℤ_[2] ((compactCentralComplex G).homology 1) = 1)
    (shaA : ℕ) (hsha : Nat.card (Submodule.torsion ℤ_[2] ((compactCentralComplex G).homology 2)) =
      2 ^ padicValNat 2 shaA) :
    DiskArith G (Nat.card (AddCommGroup.primaryComponent (centralCurve G).toAffine.Point 2))
      shaA := by
  refine diskArith_congr_valuation (diskArith_central_of_literature' G hM hF hH h541 h543
    hglob hloc hglobal hlocal hK h2 hrank) rfl ?_
  rw [hsha, padicValNat.prime_pow]

end Literature

section SelmerBridge

attribute [local instance 10000] quadraticFieldDecEq

variable (ℓ : ℕ) (k : ℤ) [(Ecurve ℓ).IsElliptic] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}
  (G : GenuineKummerData (QuadraticField k) E₀ hZ)
  (hcurve : centralCurve G = (Ecurve ℓ).baseChange (QuadraticField k))

/-- **`DiskArith` at an address curve, from cited statements other than Mordell–Weil and the
Selmer inputs**: `diskArith_arithmetic` without its Mordell–Weil argument. Inputs: the nine PRINT
statements (Milne I.3.4, I.2.3 twice, I.2.1, I.4.15, I.4.10(c), I.2.3; Nekovář 5.4.1, 5.4.3(ii)),
`K` totally complex, the places above `2` in the support, `k` not a square, the coefficient
comparison `I`, Selmer corank one over `K` (tex 2616–2626), and `hSel`. Kind: PROVED (from the
named inputs). -/
theorem diskArith_arithmetic'
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
  have := finite_central_torsion_proved G
  diskArith_central_selmer ℓ k G hcurve (centralCohomologyFinite G hloc hglob h2)
    (integralCentralKummerDuality_of_literature G hM hF hH h541 h543 hglob hloc hglobal hlocal
      hK h2)
    hloc hglob hlocal hglobal hK h2
    (compactCentral_rank_one ℓ k G hcurve (centralCohomologyFinite G hloc hglob h2) hk I hSelC)
    I shaA hSel

/-- **`DiskArith` at an address with negative companion `k`, without Mordell–Weil**
(tex 2595–2600: `K = ℚ(√k)` is imaginary): `diskArith_address` without its Mordell–Weil
argument, with `K` totally complex and `k` not a square derived from `k < 0`. Kind: PROVED (from
the named inputs). -/
theorem diskArith_address'
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
  diskArith_arithmetic' ℓ k G hcurve hM hF hH h541 h543 hglob hloc hglobal hlocal
    (isTotallyComplex_of_neg hneg) h2 (not_isSquare_of_neg hneg) I hSelC shaA hSel

/-- Non-vacuity of the finiteness at the address fields: over the imaginary quadratic field
`ℚ(√-1)`, the curve `y² = x³ - x` (discriminant `64`) has finite rational `2`-primary torsion.
Kind: PROVED (non-vacuity). -/
example : Finite (AddCommGroup.primaryComponent
    ((⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℚ).baseChange (QuadraticField (-1))).toAffine.Point
      2) :=
  have : (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℚ).IsElliptic :=
    ⟨isUnit_iff_ne_zero.2 (by norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈])⟩
  Torsion.finite_primaryComponent (QuadraticField (-1)) _ Nat.prime_two

end SelmerBridge

section ShaBridge

attribute [local instance 10000] quadraticFieldDecEq'

variable (ℓ : ℕ) (k : ℤ) [(Ecurve ℓ).IsElliptic] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}
  (G : GenuineKummerData (QuadraticField k) E₀ hZ)
  (hcurve : centralCurve G = (Ecurve ℓ).baseChange (QuadraticField k))

/-- **`DiskArith` at an address curve with the actual torsion and `Ш` orders, without
Mordell–Weil**: `diskArith_address_sha` without its Mordell–Weil argument. For Kummer data `G`
over `ℚ(√k)`, `k < 0`, whose central twist is the base change of `E_ℓ`, the disk orders are
`tA = |E^{(h)}(K)[2^∞]|` and `shaA = |Ш(E_ℓ/K)[2^∞]|`, from the ten PRINT statements (the nine of
`diskArith_address'` and `KummerSequenceTwoPowerPrint`), finiteness of `Ш(E_ℓ/K)[2^∞]`, the
places above `2` in the support, the coefficient comparison `I` and Selmer corank one over `K`.
Kind: PROVED (from the named inputs). -/
theorem diskArith_address_sha'
    (hKum : KummerSequenceTwoPowerPrint)
    (hM : MilneLocalDualityPrint) (hF : MilneFiniteLocalDualityPrint)
    (hH : MilneFiniteDegreeBoundPrint)
    (h541 : NekovarIntegralCompactLocality) (h543 : NekovarIntegralGlobalDuality)
    (hglob : MilneGlobalFiniteness) (hloc : MilneLocalFiniteness)
    (hglobal : MilneGlobalDimensionTwo) (hlocal : MilneLocalDimensionTwo)
    (hneg : k < 0)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 (QuadraticField k)),
      (2 : 𝓞 (QuadraticField k)) ∈ v.asIdeal → v ∈ G.S)
    [Finite (AddCommGroup.primaryComponent (shaK (sqrtK k) (Ecurve ℓ)) 2)]
    (I : KummerCoefficientComparison ℓ k G.S (arithmeticCentralFull ℓ k G hcurve))
    (hSelC : SelmerCorankOneOverK ℓ k) :
    DiskArith G (Nat.card (AddCommGroup.primaryComponent (centralCurve G).toAffine.Point 2))
      (Nat.card (AddCommGroup.primaryComponent (shaK (sqrtK k) (Ecurve ℓ)) 2)) := by
  refine diskArith_address' ℓ k G hcurve hM hF hH h541 h543 hglob hloc hglobal hlocal hneg h2
    I hSelC _ ?_
  rw [card_selmer_quot_eq_sha ℓ k G hcurve hKum (centralCohomologyFinite G hloc hglob h2) I]
  exact card_primaryComponent_two

end ShaBridge

end ZInQ.Contrib.RC53Assist.DiskOrders
