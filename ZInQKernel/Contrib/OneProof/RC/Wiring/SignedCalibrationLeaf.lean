import ZInQKernel.Contrib.OneProof.RC.Wiring.SignedCorank
import ZInQKernel.Contrib.OneProof.RC.Wiring.CalibrationLeafLit
import ZInQKernel.Contrib.CloudB3RC53.KummerCorankZero.Basic

/-!
# Theorem 5.3, Lane RC36: the calibration block's rank one at addresses of either sign

The calibration leaf's literature form (`CalibrationInputsLit`, `RC/Wiring/CalibrationLeafLit.lean`,
Proposition `ex:arith-central-calibration`, tex 3987–4141) carries at every address a Kummer block
`KummerCoordinateBlockLit K (Ecurve ℓ) h_x …` with the per-address input `rank_one` (the integral
central `H¹` has rank one). Its in-tree discharge `centralRankOne_of_arithmetic_pos` covers only
`h_x > 0`. With `K = ℚ(√k)`, `k < 0`, this file feeds the block at an address of either sign from
the signed arithmetic statements (`SignedCentral.lean`):

* `kummerBlockLitOfArithmeticSigned`: the RC53 group's block `KummerCoordinateBlockG` with the
  named inputs and, in place of `rank_one`, the signed arithmetic inputs (the coefficient comparison
  for `E_{ℓh}` and the signed Selmer input), gives the literature block; its `rank_one` is
  `centralRankOne_of_arithmetic_ne` (`kummerBlockLitOfArithmeticSigned_rank_one`), and the field
  and non-square hypotheses come from `k < 0`;
* `calibrationShape_of_literature_ne`, `diskTie_of_literature_ne`: the literature route's
  calibration shape and order tie (`calibrationShape_of_literature`, `diskTie_of_literature`) at an
  address of either sign, with the rank one from the signed arithmetic statements;
* the Selmer input from the forward theorems, for either sign: `kummerCorankZero_holds` (the
  skeleton's `KummerCorankZero`, PROVED in the tree), `KummerCorankOneGlue` (GLUE, its rank-one
  companion), `selmerCorankOneOverKSigned_of_forward` (Kolyvagin and BCDT from the blueprint's
  `Prints`, which are stated for every elliptic curve over `ℚ`), and `centralRankOne_of_forward_ne`:
  at an address with the calibration's two analytic hypotheses, `rank_one` from the coefficient
  comparison, the two Milne finiteness prints, the places above `2`, `Prints` and
  `KummerCorankOneGlue`.

Every declaration below is PROVED (or a definition).
-/

noncomputable section

namespace ZInQ.Manuscript.RC

open CategoryTheory NumberField IsDedekindDomain WeierstrassCurve
open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53
open ZInQ.Manuscript.RC53Assist.CentralUniversal
open ZInQ.Contrib.RC53Assist.Calibration ZInQ.Contrib.RC53Assist.CalibrationIntegral
open ZInQ.Contrib.RC53Assist.CalibrationModel
open ZInQ.Manuscript.RC.Wiring (KummerCoordinateBlockLit CalibrationBookProps
  calibrationShape_of_literature diskTie_of_literature isTotallyComplex_quadraticField_of_neg
  not_isSquare_intCast_of_neg)

/-- **The literature block at an address of either sign, from the signed arithmetic** (tex
3877–3909, 4005–4018, 4050–4064): for `k < 0` and `K = ℚ(√k)`, the RC53 group's Kummer block `L`
at the address `h`, the named inputs of the literature route (finite generation, the places above
`2`, finite `2`-primary torsion, the disk-length identification) and, in place of `rank_one`, the
coefficient comparison for `E_{ℓh}` and the signed Selmer input. The field hypothesis `hK` and the
non-square hypothesis come from `k < 0`. Kind: definition. -/
def kummerBlockLitOfArithmeticSigned {k : ℤ} {ℓ : ℕ} {h : ℤ} {n : ℕ}
    {DK : Matrix (Fin n) (Fin n) (PowerSeries ℚ_[2])} {zK wK : Fin n → PowerSeries ℚ_[2]}
    {j vL m : ℤ} {tA shaA : ℕ}
    (L : KummerCoordinateBlockG (QuadraticField k) (Ecurve ℓ) h DK zK wK j vL m tA shaA)
    [(curve ((ℓ : ℚ) * h)).IsElliptic] (hk : k < 0)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex L.G).homology n))
    (h2 : ∀ v : HeightOneSpectrum (𝓞 (QuadraticField k)),
      (2 : 𝓞 (QuadraticField k)) ∈ v.asIdeal → v ∈ L.G.S)
    (finite2 : ∀ [DecidableEq (QuadraticField k)],
      Finite (AddCommGroup.primaryComponent (centralCurve L.G).toAffine.Point 2))
    (I : KummerCoefficientComparisonSigned ((ℓ : ℚ) * h) k L.G.S
      (arithmeticCentralFullSigned ((ℓ : ℚ) * h) k L.G (centralCurve_eq_curve_mul L.G)))
    (hSel : SelmerCorankOneOverKSigned ((ℓ : ℚ) * h) k)
    (hval₁ : L.x₁.valuation = (centralDiskMatrix L.G hfinite 1).det.valuation)
    (hval₂ : L.x₂.valuation = (centralDiskMatrix L.G hfinite 2).det.valuation)
    (hval₃ : L.x₃.valuation = (centralDiskMatrix L.G hfinite 3).det.valuation) :
    KummerCoordinateBlockLit (QuadraticField k) (Ecurve ℓ) h DK zK wK j vL m tA shaA :=
  ZInQ.Manuscript.RC.Wiring.KummerCoordinateBlockLit.ofG L hfinite h2
    (isTotallyComplex_quadraticField_of_neg hk) finite2
    (centralRankOne_of_arithmetic_ne L.G hfinite (not_isSquare_intCast_of_neg hk) I hSel)
    hval₁ hval₂ hval₃

/-- The block built from the signed arithmetic keeps the Kummer data of `L`. Kind: PROVED. -/
theorem kummerBlockLitOfArithmeticSigned_G {k : ℤ} {ℓ : ℕ} {h : ℤ} {n : ℕ}
    {DK : Matrix (Fin n) (Fin n) (PowerSeries ℚ_[2])} {zK wK : Fin n → PowerSeries ℚ_[2]}
    {j vL m : ℤ} {tA shaA : ℕ}
    (L : KummerCoordinateBlockG (QuadraticField k) (Ecurve ℓ) h DK zK wK j vL m tA shaA)
    [(curve ((ℓ : ℚ) * h)).IsElliptic] (hk : k < 0)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex L.G).homology n))
    (h2 : ∀ v : HeightOneSpectrum (𝓞 (QuadraticField k)),
      (2 : 𝓞 (QuadraticField k)) ∈ v.asIdeal → v ∈ L.G.S)
    (finite2 : ∀ [DecidableEq (QuadraticField k)],
      Finite (AddCommGroup.primaryComponent (centralCurve L.G).toAffine.Point 2))
    (I : KummerCoefficientComparisonSigned ((ℓ : ℚ) * h) k L.G.S
      (arithmeticCentralFullSigned ((ℓ : ℚ) * h) k L.G (centralCurve_eq_curve_mul L.G)))
    (hSel : SelmerCorankOneOverKSigned ((ℓ : ℚ) * h) k)
    (hval₁ : L.x₁.valuation = (centralDiskMatrix L.G hfinite 1).det.valuation)
    (hval₂ : L.x₂.valuation = (centralDiskMatrix L.G hfinite 2).det.valuation)
    (hval₃ : L.x₃.valuation = (centralDiskMatrix L.G hfinite 3).det.valuation) :
    (kummerBlockLitOfArithmeticSigned L hk hfinite h2 finite2 I hSel hval₁ hval₂ hval₃).G = L.G :=
  rfl

/-- The `rank_one` of the block built from the signed arithmetic is
`centralRankOne_of_arithmetic_ne`. Kind: PROVED. -/
theorem kummerBlockLitOfArithmeticSigned_rank_one {k : ℤ} {ℓ : ℕ} {h : ℤ} {n : ℕ}
    {DK : Matrix (Fin n) (Fin n) (PowerSeries ℚ_[2])} {zK wK : Fin n → PowerSeries ℚ_[2]}
    {j vL m : ℤ} {tA shaA : ℕ}
    (L : KummerCoordinateBlockG (QuadraticField k) (Ecurve ℓ) h DK zK wK j vL m tA shaA)
    [(curve ((ℓ : ℚ) * h)).IsElliptic] (hk : k < 0)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex L.G).homology n))
    (h2 : ∀ v : HeightOneSpectrum (𝓞 (QuadraticField k)),
      (2 : 𝓞 (QuadraticField k)) ∈ v.asIdeal → v ∈ L.G.S)
    (finite2 : ∀ [DecidableEq (QuadraticField k)],
      Finite (AddCommGroup.primaryComponent (centralCurve L.G).toAffine.Point 2))
    (I : KummerCoefficientComparisonSigned ((ℓ : ℚ) * h) k L.G.S
      (arithmeticCentralFullSigned ((ℓ : ℚ) * h) k L.G (centralCurve_eq_curve_mul L.G)))
    (hSel : SelmerCorankOneOverKSigned ((ℓ : ℚ) * h) k)
    (hval₁ : L.x₁.valuation = (centralDiskMatrix L.G hfinite 1).det.valuation)
    (hval₂ : L.x₂.valuation = (centralDiskMatrix L.G hfinite 2).det.valuation)
    (hval₃ : L.x₃.valuation = (centralDiskMatrix L.G hfinite 3).det.valuation) :
    (kummerBlockLitOfArithmeticSigned L hk hfinite h2 finite2 I hSel hval₁ hval₂ hval₃).rank_one =
      centralRankOne_of_arithmetic_ne L.G hfinite (not_isSquare_intCast_of_neg hk) I hSel :=
  rfl

section Literature

/-- **The literature route's calibration shape at an address of either sign** (tex 4005–4018):
`calibrationShape_of_literature` for the Kummer data `G` of the address, `K = ℚ(√k)`, `k < 0`,
with the rank one from `centralRankOne_of_arithmetic_ne`. Kind: PROVED. -/
theorem calibrationShape_of_literature_ne {k : ℤ} {ℓ : ℕ} {h : ℤ} (hk : k < 0)
    (G : GenuineKummerData (QuadraticField k) (Ecurve ℓ) h)
    [(curve ((ℓ : ℚ) * h)).IsElliptic]
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (B : CalibrationBookProps)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 (QuadraticField k)),
      (2 : 𝓞 (QuadraticField k)) ∈ v.asIdeal → v ∈ G.S)
    (finite2 : ∀ [DecidableEq (QuadraticField k)],
      Finite (AddCommGroup.primaryComponent (centralCurve G).toAffine.Point 2))
    (I : KummerCoefficientComparisonSigned ((ℓ : ℚ) * h) k G.S
      (arithmeticCentralFullSigned ((ℓ : ℚ) * h) k G (centralCurve_eq_curve_mul G)))
    (hSel : SelmerCorankOneOverKSigned ((ℓ : ℚ) * h) k) :
    CalibrationCohomologyShape (compactCentralComplex G) :=
  calibrationShape_of_literature G hfinite B (isTotallyComplex_quadraticField_of_neg hk) h2
    (hpt := @finite2 fun a b => Classical.propDecidable (a = b))
    (centralRankOne_of_arithmetic_ne G hfinite (not_isSquare_intCast_of_neg hk) I hSel)

/-- **The literature route's order tie at an address of either sign** (tex 3429–3431, 4005–4018):
`diskTie_of_literature` for the Kummer data `G` of the address, `K = ℚ(√k)`, `k < 0`, with the rank
one from `centralRankOne_of_arithmetic_ne`. Kind: PROVED. -/
theorem diskTie_of_literature_ne {k : ℤ} {ℓ : ℕ} {h : ℤ} (hk : k < 0)
    (G : GenuineKummerData (QuadraticField k) (Ecurve ℓ) h)
    [(curve ((ℓ : ℚ) * h)).IsElliptic]
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (B : CalibrationBookProps)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 (QuadraticField k)),
      (2 : 𝓞 (QuadraticField k)) ∈ v.asIdeal → v ∈ G.S)
    (finite2 : ∀ [DecidableEq (QuadraticField k)],
      Finite (AddCommGroup.primaryComponent (centralCurve G).toAffine.Point 2))
    (I : KummerCoefficientComparisonSigned ((ℓ : ℚ) * h) k G.S
      (arithmeticCentralFullSigned ((ℓ : ℚ) * h) k G (centralCurve_eq_curve_mul G)))
    (hSel : SelmerCorankOneOverKSigned ((ℓ : ℚ) * h) k) :
    DiskTie G (centralDiskMatrix G hfinite 1).det (centralDiskMatrix G hfinite 2).det
      (centralDiskMatrix G hfinite 3).det :=
  @diskTie_of_literature (QuadraticField k) _ _ (Ecurve ℓ) h G hfinite B
    (isTotallyComplex_quadraticField_of_neg hk) h2
    (@finite2 fun a b => Classical.propDecidable (a = b))
    (centralRankOne_of_arithmetic_ne G hfinite (not_isSquare_intCast_of_neg hk) I hSel)

end Literature

/-! **The Selmer input from the forward theorems, for either sign** -/

section Forward

open ZInQ.Contrib.RC53Assist.CalibrationShape ZInQ.Contrib.RC53Assist.InnerLimitArith

/-- **The Kummer sequence in rank zero is PROVED in the tree**: the skeleton's `KummerCorankZero`
(tex 1098–1104) is `kummerCorankZero_proof` (the same statement, by unfolding). Kind: PROVED. -/
theorem kummerCorankZero_holds : KummerCorankZero :=
  ZInQ.Contrib.CloudB3RC53.KummerCorankZero.kummerCorankZero_proof

/-- **The Kummer sequence in rank one** (GLUE; `lem:forward-rank`, tex 1098–1104: "the ordinary
Kummer sequence `0 → A(ℚ) ⊗ ℚ₂/ℤ₂ → Sel_{2^∞}(A/ℚ) → Ш(A/ℚ)[2^∞] → 0` gives the corank
assertion"; Silverman, *The Arithmetic of Elliptic Curves*, X.4, with Mordell–Weil): rank one and
finite `Ш` give `corank Sel_{2^∞} = 1`. The rank-one companion of the skeleton's
`KummerCorankZero` (which is PROVED, `kummerCorankZero_holds`), stated for every elliptic curve over
`ℚ`; unlike rank zero it needs `A(ℚ)` finitely generated (Mordell–Weil), so that
`A(ℚ) ⊗ ℚ₂/ℤ₂ ≅ ℚ₂/ℤ₂`. No inhabitant is supplied. Kind: definition (GLUE input). -/
def KummerCorankOneGlue : Prop :=
  ∀ A : WeierstrassCurve ℚ, A.IsElliptic → Module.rank ℤ A.toAffine.Point = 1 →
    Finite (sha A) → Z2Corank (selmerTwoPower A) 1

/-- **The signed Selmer input from the forward theorems** (tex 4020–4021, `lem:forward-rank`,
tex 1086–1108; the calibration's hypotheses, tex 3988–3991): if `ord_{s=1} L(E^{(h)}, s) = 1` and
`L(E^{(hk)}, 1) ≠ 0` (as `AnalyticRank … 0`), with `ℓ h ≠ 0` and `k ≠ 0`, then BCDT and
Kolyvagin (the blueprint's `Prints`, stated for every elliptic curve over `ℚ`) and the Kummer
sequence in rank one (`KummerCorankOneGlue`) and in rank zero (`kummerCorankZero_holds`) give
`SelmerCorankOneOverKSigned (ℓ h) k`, for `h` of either sign. Kind: PROVED. -/
theorem selmerCorankOneOverKSigned_of_forward (Pr : Prints) (hK1 : KummerCorankOneGlue)
    {ℓ : ℕ} {h k : ℤ} (hlh : (ℓ : ℚ) * h ≠ 0) (hk : k ≠ 0)
    (h1 : AnalyticRank (Etw ℓ h) 1) (h0 : AnalyticRank (Etw ℓ (h * k)) 0) :
    SelmerCorankOneOverKSigned ((ℓ : ℚ) * h) k := by
  rw [selmerCorankOneOverK_of_ne]
  have hE : (Etw ℓ h).IsElliptic := by
    rw [etw_eq_curve_mul]
    exact curve_isElliptic_of_ne hlh
  have hEk : (Etw ℓ (h * k)).IsElliptic := by
    rw [etw_eq_curve_mul]
    refine curve_isElliptic_of_ne ?_
    rw [Int.cast_mul, ← mul_assoc]
    exact mul_ne_zero hlh (Int.cast_ne_zero.mpr hk)
  obtain ⟨hr1, hs1⟩ := Pr.kolyvagin _ hE (Pr.bcdt _ hE) 1 le_rfl h1
  obtain ⟨hr0, hs0⟩ := Pr.kolyvagin _ hEk (Pr.bcdt _ hEk) 0 (Nat.zero_le 1) h0
  refine ⟨hK1 _ hE (by exact_mod_cast hr1) hs1,
    kummerCorankZero_holds _ hEk (by exact_mod_cast hr0) hs0⟩

/-- **The calibration block's `rank_one` at an address of either sign, from the forward theorems**
(tex 3987–4141, 4006–4021): for `k < 0`, the Kummer data `G` of an address `h` with
`ord_{s=1} L(E^{(h)}, s) = 1` and `L(E^{(hk)}, 1) ≠ 0` (the two analytic hypotheses under which
`CalibrationInputsLit` asks for a model), the coefficient comparison for `E_{ℓh}`, the two Milne
finiteness prints (fields of `CalibrationBookProps`), the places above `2` in the support,
`Prints` and the Kummer sequence in rank one (`KummerCorankOneGlue`; rank zero is PROVED), the
integral central first cohomology has rank one. Kind: PROVED. -/
theorem centralRankOne_of_forward_ne (Pr : Prints) (hK1 : KummerCorankOneGlue)
    (hloc : MilneLocalFiniteness) (hglob : MilneGlobalFiniteness)
    {k : ℤ} {ℓ : ℕ} {h : ℤ} (hk : k < 0)
    (G : GenuineKummerData (QuadraticField k) (Ecurve ℓ) h)
    [(curve ((ℓ : ℚ) * h)).IsElliptic]
    (h2 : ∀ v : HeightOneSpectrum (𝓞 (QuadraticField k)),
      (2 : 𝓞 (QuadraticField k)) ∈ v.asIdeal → v ∈ G.S)
    (I : KummerCoefficientComparisonSigned ((ℓ : ℚ) * h) k G.S
      (arithmeticCentralFullSigned ((ℓ : ℚ) * h) k G (centralCurve_eq_curve_mul G)))
    (h1 : AnalyticRank (Etw ℓ h) 1) (h0 : AnalyticRank (Etw ℓ (h * k)) 0) :
    Module.finrank ℤ_[2] ((compactCentralComplex G).homology 1) = 1 :=
  centralRankOne_of_arithmetic_ne G (centralCohomologyFinite G hloc hglob h2)
    (not_isSquare_intCast_of_neg hk) I
    (selmerCorankOneOverKSigned_of_forward Pr hK1 (mul_ne_zero_of_genuineKummerData G) hk.ne h1
      h0)

end Forward

end ZInQ.Manuscript.RC
