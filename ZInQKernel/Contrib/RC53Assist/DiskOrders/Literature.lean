import ZInQKernel.Contrib.RC53Assist.DiskOrders.DualityOrders
import ZInQKernel.Contrib.RC53Assist.DKLocalAdapter.ArithmeticCentralDuality

/-!
# The disk orders of the calibration from cited book statements

Proposition `ex:arith-central-calibration` (`diophantine_zq.tex`, tex 3987–4141; proof
tex 4007–4018 and (5.7a)–(5.7b) at tex 5280–5302). The integral Kummer self-duality used for
the degree-three and degree-two disks is supplied by the literature theorem of the integral
central Kummer duality (from the nine cited statements of Milne, *Arithmetic Duality
Theorems*, and Nekovář, *Selmer complexes*, the PRINT inputs of the literature route of the
calibration leaf), finite generation of the integral compact central cohomology by the two
Milne finiteness statements, and finiteness of the rational `2`-primary torsion by the
Mordell–Weil theorem (`MordellWeilNumberFieldPrint`).

* **`diskArith_central_of_literature`**: `DiskArith G t |H²(C_K)_tors|` for the genuine finite
  central Kummer complexes, with `t` the order of the rational `2`-primary torsion of the
  central twist `E^{(h)}/K`, from the ten PRINT statements, `K` totally complex, the places
  above `2` in the support, and rank one of the integral first cohomology.
* **`diskArith_central_of_literature_sha`**: `DiskArith G t shaA` for any `shaA` whose `2`-part
  is `|H²(C_K)_tors|` (`hsha`).

Kinds: PROVED from the named PRINT statements and hypotheses.
-/

noncomputable section

set_option autoImplicit false

namespace ZInQ.Contrib.RC53Assist.DiskOrders

open NumberField IsDedekindDomain
open ZInQ.Contrib.RC53Assist.Calibration
open ZInQ.Contrib.RC53Assist.CalibrationIntegral
open ZInQ.Contrib.RC53Assist.CalibrationShape
open ZInQ.Contrib.RC53Assist.InnerLimitArith (MilneLocalFiniteness MilneGlobalFiniteness)
open ZInQ.Contrib.RC53Assist.DerivedKummer (MilneLocalDualityPrint MilneFiniteLocalDualityPrint)
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteLocalDegreeBound
  (MilneFiniteDegreeBoundPrint)
open ZInQ.Contrib.RC53Assist.IntegralDuality
  (NekovarIntegralCompactLocality NekovarIntegralGlobalDuality)
open ZInQ.Contrib.RC53Assist.DKLocalAdapter (integralCentralKummerDuality_of_literature)

section Literature

open scoped Classical

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}

/-- **`DiskArith` for the actual orders, from the cited book statements**: for the genuine
finite central Kummer complexes of `G`, `|H⁰| = |H³| = 2^{i v₂ t}` and
`|H²| = 2^{i (i + v₂ |H²(C_K)_tors| + v₂ t)}` for all large `i`, where `t` is the order of the
rational `2`-primary torsion of the central twist. Inputs: the PRINT statements (Milne I.3.4,
I.2.3 twice, I.2.1, I.4.15, I.4.10(c), I.2.3; Nekovář 5.4.1, 5.4.3(ii); Silverman VIII.6.7),
`K` totally complex, the places above `2` in the support, and rank one of `H¹(C_K)`.
Kind: PROVED. -/
theorem diskArith_central_of_literature (G : GenuineKummerData K E₀ hZ)
    (hMW : MordellWeilNumberFieldPrint)
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
  have := finite_central_torsion hMW G
  diskArith_central_actual G (centralCohomologyFinite G hloc hglob h2)
    (integralCentralKummerDuality_of_literature G hM hF hH h541 h543 hglob hloc hglobal hlocal
      hK h2)
    hloc hglob hlocal hglobal hK h2 hrank

/-- **`DiskArith` with a declared `Ш`-order, from the cited book statements**: as
`diskArith_central_of_literature`, for any `shaA` whose `2`-part is the order of
`H²(C_K)_tors` (`hsha`; tex 4010–4014: `H²(C_K)_tors` is Selmer modulo its maximal divisible
subgroup, which is `Ш(E^{(h)}/K)[2^∞]` when that group is finite). Kind: PROVED. -/
theorem diskArith_central_of_literature_sha (G : GenuineKummerData K E₀ hZ)
    (hMW : MordellWeilNumberFieldPrint)
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
  refine diskArith_congr_valuation (diskArith_central_of_literature G hMW hM hF hH h541 h543
    hglob hloc hglobal hlocal hK h2 hrank) rfl ?_
  rw [hsha, padicValNat.prime_pow]

end Literature

end ZInQ.Contrib.RC53Assist.DiskOrders
