import ZInQKernel.Contrib.OneProof.RC.Wiring.SignedCoefficient

/-!
# Theorem 5.3, Lane RC36: integral rank one of the central twist at an address of either sign

The calibration's Kummer block (`KummerCoordinateBlockLit`, `RC/Wiring/CalibrationLeafLit.lean`)
needs, at every address, the rank one of the integral central first cohomology,
`rank_{ℤ₂} H¹(C_K) = 1` for the compact Kummer complex of the central twist `E^{(h_x)} ⊗ K`
(`s₂(E^{(h_x)}/K) = 1`, tex 4006–4021). The RC53 group's discharge `compactCentral_rank_one`
(`RC53Assist/CalibrationShape/CalibrationDischarge.lean`) binds the central twist to `Ecurve ℓ'`,
`ℓ' : ℕ`, so its address form `centralRankOne_of_arithmetic_pos` covers only `h_x > 0`. This file
restates the central discharge layer for the family curve `E_t`, `t : ℚ` of either sign, and
applies it at the signed address parameter `t = ℓ h_x` (`centralCurve_eq_curve_mul`):

* generic layer, for Kummer data `D` over `K = ℚ(√k)` whose central curve is `(E_t)_K`:
  `arithmeticCentralFullSigned`, `compactCentral_eq_arithmeticSigned`,
  `arithmeticCentralFiniteSigned`, `compactCentral_rank_one_signed`,
  `calibrationShape_of_arithmetic_signed`, `diskTie_of_arithmetic_signed` (the RC53 group's
  `arithmeticCentralFull`, …, `diskTie_of_arithmetic` with `Ecurve ℓ` replaced by `curve t`);
* address layer, `h` of either sign: `centralRankOne_of_arithmetic_ne` (the conclusion is the type
  of the block's `rank_one`), `centralRankOne_of_arithmetic_ne_address` (the Selmer input in the
  address's own form, `E^{(h)}` and `E^{(hk)}`), `selmerCorankOneOverK_of_ne`,
  `diskTie_of_arithmetic_ne` (the field and non-square hypotheses from `k < 0`);
* agreement with the positive route: `kummerCoefficientComparisonSigned_of_pos` (at `h > 0` the
  RC53 group's comparison for `Ecurve (ℓ · h.toNat)` is the signed one at `t = ℓ h`).

`h ≠ 0` is not a hypothesis: the existence of the Kummer data `G` of the address forces it
(`ne_zero_of_genuineKummerData`), and supplies the ellipticity instance of `E_{ℓh}`
(`isElliptic_curve_mul_of_genuineKummerData`).

Every declaration below is PROVED (or a definition); the arithmetic inputs (finite generation, the
coefficient comparison, the two rational coranks, integral duality, the Milne prints) stay
hypotheses, as in the RC53 group's statements.
-/

noncomputable section

namespace ZInQ.Manuscript.RC

open CategoryTheory NumberField IsDedekindDomain WeierstrassCurve
open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53
open ZInQ.Manuscript.RC53Assist.CentralUniversal ZInQ.Manuscript.RC53Assist.CentralKummer
open ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.RC53Assist.Calibration ZInQ.Contrib.RC53Assist.CalibrationIntegral
open ZInQ.Contrib.RC53Assist.CalibrationModel ZInQ.Contrib.RC53Assist.InnerLimitArith
open ZInQ.Contrib.RC53Assist.CalibrationShape

/-! **The central discharge layer for `E_t`** -/

section Generic

variable (t : ℚ) (k : ℤ) [(curve t).IsElliptic] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}
  (D : GenuineKummerData (QuadraticField k) E₀ hZ)
  (hcurve : centralCurve D = (curve t).baseChange (QuadraticField k))

include hcurve

omit [(curve t).IsElliptic] in
/-- Full two-power torsion of `(E_t)_K`, transported along the curve binding from the central
twist. Kind: PROVED. -/
theorem arithmeticCentralFullSigned : ∀ n : ℕ, FullTorsion (QuadraticField k) D.S
    ((curve t).baseChange (QuadraticField k)) (2 ^ n) :=
  fun n => hcurve ▸ centralFullTorsion D n

/-- **The compact central complex is the genuine compact Kummer complex of `(E_t)_K`** (the
actual curve-congruence map, retaining `D.S` and the transported full torsion). Kind: PROVED. -/
theorem compactCentral_eq_arithmeticSigned : compactCentralComplex D =
    arithmeticCompactComplexSigned t k D.S (arithmeticCentralFullSigned t k D hcurve) := by
  rw [compactCentralComplex_eq]
  exact compactKummerComplex_curve_congr D.S (centralCurve D)
    ((curve t).baseChange (QuadraticField k)) hcurve (centralFullTorsion D)
      (arithmeticCentralFullSigned t k D hcurve)

variable (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex D).homology n))

include hfinite

/-- The finite-generation input of the universal-coefficient layer, from integral finite generation
of the compact central cohomology. Kind: PROVED. -/
theorem arithmeticCentralFiniteSigned :
    KummerCohomologyFiniteSigned t k D.S (arithmeticCentralFullSigned t k D hcurve) where
  finite_one := by rw [← compactCentral_eq_arithmeticSigned t k D hcurve]; exact hfinite 1
  finite_two := by rw [← compactCentral_eq_arithmeticSigned t k D hcurve]; exact hfinite 2

/-- **Integral rank one of the compact central cohomology, for `E_t` of either sign**
(tex 4006–4021): if the central twist of `D` is `(E_t)_K`, `K = ℚ(√k)` with `k` not a square, the
compact central cohomology is finitely generated, the coefficient comparison for `E_t` holds and
`Sel_{2^∞}(E_t/ℚ)`, `Sel_{2^∞}(E_t^{(k)}/ℚ)` have coranks one and zero, then
`rank_{ℤ₂} H¹(C_K) = 1`. The RC53 group's `compactCentral_rank_one` with `Ecurve ℓ` replaced by
`curve t`. Kind: PROVED. -/
theorem compactCentral_rank_one_signed (hk : ¬ IsSquare (k : ℚ))
    (I : KummerCoefficientComparisonSigned t k D.S (arithmeticCentralFullSigned t k D hcurve))
    (hSel : SelmerCorankOneOverKSigned t k) :
    Module.finrank ℤ_[2] ((compactCentralComplex D).homology 1) = 1 := by
  have h := arithmeticRankSigned_eq_one t k D.S (arithmeticCentralFullSigned t k D hcurve) hk I
    (arithmeticCentralFiniteSigned t k D hcurve hfinite) hSel
  have hr : arithmeticRankSigned t k D.S (arithmeticCentralFullSigned t k D hcurve) =
      Module.finrank ℤ_[2] ((arithmeticCompactComplexSigned t k D.S
        (arithmeticCentralFullSigned t k D hcurve)).homology 1) :=
    finrank_quotient_eq_of_le_torsion (le_refl _)
  rw [compactCentral_eq_arithmeticSigned t k D hcurve]
  exact hr.symm.trans h

attribute [local instance 10000] ZInQ.Contrib.RC53Assist.CalibrationShape.arithmeticFieldDecidableEq

/-- **The calibration shape for `E_t` of either sign** (tex 4005–4018): cohomology in degrees one
to three with ranks `1, 1, 0`, from the finiteness and dimension prints, `K` totally complex, the
places above `2` in the support, finite `2`-primary torsion, the signed rank-one inputs and
integral self-duality. The RC53 group's `calibrationShape_of_arithmetic` with `Ecurve ℓ` replaced
by `curve t`. Kind: PROVED. -/
theorem calibrationShape_of_arithmetic_signed (hloc : MilneLocalFiniteness)
    (hglob : MilneGlobalFiniteness) (hlocal : MilneLocalDimensionTwo)
    (hglobal : MilneGlobalDimensionTwo) (hK : IsTotallyComplex (QuadraticField k))
    (h2 : ∀ v : HeightOneSpectrum (𝓞 (QuadraticField k)),
      (2 : 𝓞 (QuadraticField k)) ∈ v.asIdeal → v ∈ D.S)
    [hpt : Finite (AddCommGroup.primaryComponent (centralCurve D).toAffine.Point 2)]
    (hk : ¬ IsSquare (k : ℚ))
    (I : KummerCoefficientComparisonSigned t k D.S (arithmeticCentralFullSigned t k D hcurve))
    (hSel : SelmerCorankOneOverKSigned t k) (hdual : IntegralCentralKummerDuality D hfinite) :
    CalibrationCohomologyShape (compactCentralComplex D) := by
  have hout : ∀ n : ℤ, n < 1 ∨ 3 < n → Subsingleton ((compactCentralComplex D).homology n) :=
    @compactCentral_outside (QuadraticField k) _ _ E₀ hZ D hloc hglob hlocal hglobal hK h2 hpt
  have hrank := compactCentral_rank_one_signed t k D hcurve hfinite hk I hSel
  refine ⟨hout, hrank, ?_, ?_⟩
  · exact ((integralCentralDuality_ranks D hfinite hdual 2).trans
      (cohomology_finrank_degree_congr (compactCentralComplex D) (by decide))).trans hrank
  · have h : Module.finrank ℤ_[2] ((compactCentralComplex D).homology 3) =
        Module.finrank ℤ_[2] ((compactCentralComplex D).homology 0) :=
      (integralCentralDuality_ranks D hfinite hdual 3).trans
        (cohomology_finrank_degree_congr (compactCentralComplex D) (by decide))
    have : Subsingleton ((compactCentralComplex D).homology 0) := hout 0 (by omega)
    exact h.trans Module.finrank_zero_of_subsingleton

/-- **The disk-order statement for `E_t` of either sign** (tex 3429–3431, 4005–4018): the RC53
group's `diskTie_of_finite_cohomology` at `calibrationShape_of_arithmetic_signed`, with the proved
canonical reductions; the RC53 group's `diskTie_of_arithmetic` with `Ecurve ℓ` replaced by
`curve t`. Kind: PROVED. -/
theorem diskTie_of_arithmetic_signed (hloc : MilneLocalFiniteness)
    (hglob : MilneGlobalFiniteness) (hlocal : MilneLocalDimensionTwo)
    (hglobal : MilneGlobalDimensionTwo) (hK : IsTotallyComplex (QuadraticField k))
    (h2 : ∀ v : HeightOneSpectrum (𝓞 (QuadraticField k)),
      (2 : 𝓞 (QuadraticField k)) ∈ v.asIdeal → v ∈ D.S)
    [Finite (AddCommGroup.primaryComponent (centralCurve D).toAffine.Point 2)]
    (hk : ¬ IsSquare (k : ℚ))
    (I : KummerCoefficientComparisonSigned t k D.S (arithmeticCentralFullSigned t k D hcurve))
    (hSel : SelmerCorankOneOverKSigned t k) (hdual : IntegralCentralKummerDuality D hfinite) :
    DiskTie D (centralDiskMatrix D hfinite 1).det (centralDiskMatrix D hfinite 2).det
      (centralDiskMatrix D hfinite 3).det :=
  diskTie_of_finite_cohomology D hfinite
    (calibrationShape_of_arithmetic_signed t k D hcurve hfinite hloc hglob hlocal hglobal hK h2 hk
      I hSel hdual)
    (fun i _ => canonicalCentralReductionMap_quasiIso D i)

end Generic

/-! **The address layer, `h` of either sign** -/

section Address

/-- **Integral rank one at an address of either sign** (tex 3987–4141; universal coefficients,
tex 4006–4014, and the two coranks, tex 2616–2626, 4020–4021): for Kummer data `G` of an address
`h` (any nonzero integer; `h ≠ 0` is forced by `G`, `ne_zero_of_genuineKummerData`), finite
generation, `k` not a square, the coefficient comparison for the signed curve `E_{ℓh}` and the
signed Selmer input, the integral first cohomology of the compact central complex of `G` has rank
one. The conclusion is the type of the calibration
block's field `rank_one` (`KummerCoordinateBlockLit`, with `K = ℚ(√k)`). It is
`compactCentral_rank_one_signed` at `t = ℓ h`, through `centralCurve_eq_curve_mul`; the
ellipticity instance is supplied by `isElliptic_curve_mul_of_genuineKummerData G`. Kind: PROVED. -/
theorem centralRankOne_of_arithmetic_ne {k : ℤ} {ℓ : ℕ} {h : ℤ}
    (G : GenuineKummerData (QuadraticField k) (Ecurve ℓ) h)
    [(curve ((ℓ : ℚ) * h)).IsElliptic]
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (hk : ¬ IsSquare (k : ℚ))
    (I : KummerCoefficientComparisonSigned ((ℓ : ℚ) * h) k G.S
      (arithmeticCentralFullSigned ((ℓ : ℚ) * h) k G (centralCurve_eq_curve_mul G)))
    (hSel : SelmerCorankOneOverKSigned ((ℓ : ℚ) * h) k) :
    Module.finrank ℤ_[2] ((compactCentralComplex G).homology 1) = 1 :=
  compactCentral_rank_one_signed ((ℓ : ℚ) * h) k G (centralCurve_eq_curve_mul G) hfinite hk I
    hSel

/-- **The signed Selmer input at an address** (the counterpart of `selmerCorankOneOverK_of_pos`,
with no sign condition): `SelmerCorankOneOverKSigned (ℓ h) k` holds exactly when `E^{(h)}` has
`2^∞`-Selmer corank one and `E^{(hk)}` has corank zero over `ℚ`. Kind: PROVED. -/
theorem selmerCorankOneOverK_of_ne (ℓ : ℕ) (h k : ℤ) :
    SelmerCorankOneOverKSigned ((ℓ : ℚ) * h) k ↔
      (SelmerCorankOne (Etw ℓ h) ∧ Z2Corank (selmerTwoPower (Etw ℓ (h * k))) 0) :=
  selmerCorankOneOverKSigned_address ℓ h k

/-- **Integral rank one at an address of either sign, with the Selmer input in the address's own
form** (tex 2616–2626, 4020–4021): corank one for `Sel_{2^∞}(E^{(h)}/ℚ)` and corank zero for
`Sel_{2^∞}(E^{(hk)}/ℚ)`. Kind: PROVED. -/
theorem centralRankOne_of_arithmetic_ne_address {k : ℤ} {ℓ : ℕ} {h : ℤ}
    (G : GenuineKummerData (QuadraticField k) (Ecurve ℓ) h)
    [(curve ((ℓ : ℚ) * h)).IsElliptic]
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (hk : ¬ IsSquare (k : ℚ))
    (I : KummerCoefficientComparisonSigned ((ℓ : ℚ) * h) k G.S
      (arithmeticCentralFullSigned ((ℓ : ℚ) * h) k G (centralCurve_eq_curve_mul G)))
    (hE : SelmerCorankOne (Etw ℓ h)) (hEk : Z2Corank (selmerTwoPower (Etw ℓ (h * k))) 0) :
    Module.finrank ℤ_[2] ((compactCentralComplex G).homology 1) = 1 :=
  centralRankOne_of_arithmetic_ne G hfinite hk I ((selmerCorankOneOverK_of_ne ℓ h k).mpr ⟨hE, hEk⟩)

attribute [local instance 10000] ZInQ.Contrib.RC53Assist.CalibrationShape.arithmeticFieldDecidableEq

/-- **The disk-order statement at an address of either sign** (tex 3987–4141; self-duality and the
free parts, tex 4015–4018): for `k < 0`, the signed counterpart of `diskTie_of_arithmetic_pos`.
The field hypothesis and the non-square hypothesis come from `k < 0` (tex 2595–2600, 2720); the
other inputs are those of `diskTie_of_arithmetic_signed` at `t = ℓ h`. Kind: PROVED. -/
theorem diskTie_of_arithmetic_ne {k : ℤ} {ℓ : ℕ} {h : ℤ} (hk : k < 0)
    (G : GenuineKummerData (QuadraticField k) (Ecurve ℓ) h)
    [(curve ((ℓ : ℚ) * h)).IsElliptic]
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n))
    (hloc : MilneLocalFiniteness) (hglob : MilneGlobalFiniteness)
    (hlocal : MilneLocalDimensionTwo) (hglobal : MilneGlobalDimensionTwo)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 (QuadraticField k)),
      (2 : 𝓞 (QuadraticField k)) ∈ v.asIdeal → v ∈ G.S)
    [Finite (AddCommGroup.primaryComponent (centralCurve G).toAffine.Point 2)]
    (I : KummerCoefficientComparisonSigned ((ℓ : ℚ) * h) k G.S
      (arithmeticCentralFullSigned ((ℓ : ℚ) * h) k G (centralCurve_eq_curve_mul G)))
    (hSel : SelmerCorankOneOverKSigned ((ℓ : ℚ) * h) k)
    (hdual : IntegralCentralKummerDuality G hfinite) :
    DiskTie G (centralDiskMatrix G hfinite 1).det (centralDiskMatrix G hfinite 2).det
      (centralDiskMatrix G hfinite 3).det :=
  diskTie_of_arithmetic_signed ((ℓ : ℚ) * h) k G (centralCurve_eq_curve_mul G) hfinite hloc hglob
    hlocal hglobal (Wiring.isTotallyComplex_quadraticField_of_neg hk) h2
    (Wiring.not_isSquare_intCast_of_neg hk) I hSel hdual

end Address

/-! **Agreement with the positive route** -/

section Positive

/-- **At `h > 0` the RC53 group's comparison is the signed one**: the comparison for
`Ecurve (ℓ · h.toNat)` at the transported full torsion of `centralCurve_eq_of_pos` gives the signed
comparison at `t = ℓ h` and the transported full torsion of `centralCurve_eq_curve_mul` (the two
parameters are equal rationals). So wherever the positive route applies, its inputs feed the signed
statements. Kind: definition. -/
def kummerCoefficientComparisonSigned_of_pos {k : ℤ} {ℓ : ℕ} {h : ℤ} (hh : 0 < h)
    (G : GenuineKummerData (QuadraticField k) (Ecurve ℓ) h)
    [(Ecurve (ℓ * h.toNat)).IsElliptic] [(curve ((ℓ : ℚ) * h)).IsElliptic]
    (I : KummerCoefficientComparison (ℓ * h.toNat) k G.S
      (arithmeticCentralFull (ℓ * h.toNat) k G (Wiring.centralCurve_eq_of_pos hh G))) :
    KummerCoefficientComparisonSigned ((ℓ : ℚ) * h) k G.S
      (arithmeticCentralFullSigned ((ℓ : ℚ) * h) k G (centralCurve_eq_curve_mul G)) :=
  KummerCoefficientComparisonSigned.congrParam
    (by rw [Nat.cast_mul, Wiring.natCast_toNat_of_pos hh])
    (KummerCoefficientComparisonSigned.ofNat I)

/-- At `h > 0` the signed Selmer input is the RC53 group's `SelmerCorankOneOverK (ℓ · h.toNat) k`.
Kind: PROVED. -/
theorem selmerCorankOneOverKSigned_iff_of_pos {ℓ : ℕ} {h : ℤ} (hh : 0 < h) (k : ℤ) :
    SelmerCorankOneOverKSigned ((ℓ : ℚ) * h) k ↔ SelmerCorankOneOverK (ℓ * h.toNat) k := by
  rw [selmerCorankOneOverK_of_ne, Wiring.selmerCorankOneOverK_of_pos hh]

end Positive

end ZInQ.Manuscript.RC
