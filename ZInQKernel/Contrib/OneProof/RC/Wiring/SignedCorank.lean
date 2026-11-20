import ZInQKernel.Contrib.OneProof.RC.Wiring.SignedCentral
import ZInQKernel.Contrib.OneProof.RC.Wiring.CoefficientCorank

/-!
# Theorem 5.3, Lane RC36: rank = Selmer corank for `E_t` at a signed parameter

The universal-coefficient sequence `0 → H¹(C_K) ⊗ ℚ₂/ℤ₂ → Sel_{2^∞}(E_t/K) → H²(C_K)_tors → 0`
(`SignedCoefficient.lean`), with `H²(C_K)` finitely generated (so its torsion is a finite group,
`finite_torsion_of_moduleFinite`) and the additive splitting of the divisible first term
(`z2Corank_coefficientQuotient_homology_one`), computes the `ℤ₂`-corank of the genuine full Selmer
group over `K = ℚ(√k)` in the project's sense (`Z2Corank`: `M ≃ (ℚ₂/ℤ₂)^r × F`, `F` finite):

* `z2Corank_selKSigned`: `corank Sel_{2^∞}(E_t/K) = rank_{ℤ₂} H¹(C_K)`, the finite part being the
  torsion of `H²(C_K)`;
* `z2Corank_unique`: a corank is unique;
* `finrank_arithmeticH1Signed_eq_add`, `z2Corank_selKSigned_add`: corank additivity under the
  quadratic descent `g f = f g = [2]`,
  `corank Sel_{2^∞}(E_t/K) = corank Sel_{2^∞}(E_t/ℚ) + corank Sel_{2^∞}(E_t^{(k)}/ℚ)`, now as a
  genuine corank of the Selmer group over `K`;
* `z2Corank_selKSigned_central`: at Kummer data `D` whose central twist is `(E_t)_K`, the corank of
  `Sel_{2^∞}(E_t/K)` is the integral rank of the compact central `H¹`.

All for `t : ℚ` of either sign. Every theorem below is PROVED; the comparison and finite
generation are the named inputs of `SignedCoefficient.lean`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53
open ZInQ.Manuscript.RC53Assist.CentralUniversal ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.BaseZeroLimit
open ZInQ.Contrib.RC53Assist.Calibration ZInQ.Contrib.RC53Assist.CalibrationIntegral

/-- **A `ℤ₂`-corank is unique** (it is the dimension of the rational Tate module,
`finrank_ratTate_of_Z2Corank`). Kind: PROVED. -/
theorem z2Corank_unique {M : Type*} [AddCommGroup M] {r s : ℕ} (hr : Z2Corank M r)
    (hs : Z2Corank M s) : r = s :=
  (finrank_ratTate_of_Z2Corank hr).symm.trans (finrank_ratTate_of_Z2Corank hs)

section Generic

variable {t : ℚ} {k : ℤ} [(curve t).IsElliptic]
  {S : Set (HeightOneSpectrum (𝓞 (QuadraticField k)))}
  {hFull : ∀ n : ℕ, FullTorsion (QuadraticField k) S
    ((curve t).baseChange (QuadraticField k)) (2 ^ n)}

/-- **Rank = Selmer corank, with finite torsion `H²`** (tex 4006–4018): under the coefficient
comparison and finite generation of `H¹(C_K)`, `H²(C_K)`, the genuine `Sel_{2^∞}(E_t/ℚ(√k))` is
`(ℚ₂/ℤ₂)^r × F` with `r = rank_{ℤ₂} H¹(C_K)` and `F` finite (the torsion of `H²(C_K)`). The
universal-coefficient splitting transported by the Selmer identification of the comparison.
Kind: PROVED. -/
theorem z2Corank_selKSigned (I : KummerCoefficientComparisonSigned t k S hFull)
    (F : KummerCohomologyFiniteSigned t k S hFull) :
    Z2Corank (SelKSigned t k)
      (Module.finrank ℤ_[2] ((arithmeticCompactComplexSigned t k S hFull).homology 1)) := by
  have := F.finite_one
  have := F.finite_two
  exact z2Corank_of_addEquiv
    (z2Corank_coefficientQuotient_homology_one (arithmeticCompactComplexSigned t k S hFull))
    I.selmerEquiv

/-- **The integral rank of `H¹(C_K)` is the sum of the two rational coranks** (corank additivity
under the quadratic descent, with the universal coefficients): with coranks `r₁` of
`Sel_{2^∞}(E_t/ℚ)` and `r₂` of `Sel_{2^∞}(E_t^{(k)}/ℚ)`, `rank_{ℤ₂} H¹(C_K) = r₁ + r₂`.
Kind: PROVED. -/
theorem finrank_arithmeticH1Signed_eq_add (hk : ¬ IsSquare (k : ℚ))
    (I : KummerCoefficientComparisonSigned t k S hFull)
    (F : KummerCohomologyFiniteSigned t k S hFull) {r₁ r₂ : ℕ}
    (h₁ : Z2Corank (selmerTwoPower (curve t)) r₁)
    (h₂ : Z2Corank (selmerTwoPower (qtwist (curve t) (k : ℚ))) r₂) :
    Module.finrank ℤ_[2] ((arithmeticCompactComplexSigned t k S hFull).homology 1) = r₁ + r₂ := by
  have hr : arithmeticRankSigned t k S hFull =
      Module.finrank ℤ_[2] ((arithmeticCompactComplexSigned t k S hFull).homology 1) :=
    finrank_quotient_eq_of_le_torsion (le_refl _)
  rw [← hr]
  exact arithmeticRankSigned_eq_add t k S hFull hk I F h₁ h₂

/-- **Corank additivity for the genuine Selmer group over `K`** (tex 2616–2626): under the
coefficient comparison and finite generation, if `Sel_{2^∞}(E_t/ℚ)` has corank `r₁` and
`Sel_{2^∞}(E_t^{(k)}/ℚ)` has corank `r₂`, then `Sel_{2^∞}(E_t/ℚ(√k))` has corank `r₁ + r₂`.
Kind: PROVED. -/
theorem z2Corank_selKSigned_add (hk : ¬ IsSquare (k : ℚ))
    (I : KummerCoefficientComparisonSigned t k S hFull)
    (F : KummerCohomologyFiniteSigned t k S hFull) {r₁ r₂ : ℕ}
    (h₁ : Z2Corank (selmerTwoPower (curve t)) r₁)
    (h₂ : Z2Corank (selmerTwoPower (qtwist (curve t) (k : ℚ))) r₂) :
    Z2Corank (SelKSigned t k) (r₁ + r₂) := by
  have h := z2Corank_selKSigned I F
  rwa [finrank_arithmeticH1Signed_eq_add hk I F h₁ h₂] at h

/-- **Under the signed Selmer input, `Sel_{2^∞}(E_t/ℚ(√k))` has corank one** (`s₂(E_t/K) = 1` as a
genuine corank over `K`). Kind: PROVED. -/
theorem z2Corank_selKSigned_one (hk : ¬ IsSquare (k : ℚ))
    (I : KummerCoefficientComparisonSigned t k S hFull)
    (F : KummerCohomologyFiniteSigned t k S hFull) (hSel : SelmerCorankOneOverKSigned t k) :
    Z2Corank (SelKSigned t k) 1 :=
  z2Corank_selKSigned_add hk I F hSel.1 hSel.2

end Generic

/-- **Rank = Selmer corank at the central twist** (tex 4006–4021): for Kummer data `D` over
`K = ℚ(√k)` whose central twist is `(E_t)_K`, with finitely generated compact central cohomology and
the coefficient comparison, `corank Sel_{2^∞}(E_t/K) = rank_{ℤ₂} H¹` of the compact central
complex of `D`. For `t = ℓ h` and `G` the data of an address (`centralCurve_eq_curve_mul`) this is
the identity `s₂(E^{(h)}/K) = rank H¹(C_K)` for `h` of either sign. Kind: PROVED. -/
theorem z2Corank_selKSigned_central (t : ℚ) (k : ℤ) [(curve t).IsElliptic]
    {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} (D : GenuineKummerData (QuadraticField k) E₀ hZ)
    (hcurve : centralCurve D = (curve t).baseChange (QuadraticField k))
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex D).homology n))
    (I : KummerCoefficientComparisonSigned t k D.S (arithmeticCentralFullSigned t k D hcurve)) :
    Z2Corank (SelKSigned t k) (Module.finrank ℤ_[2] ((compactCentralComplex D).homology 1)) := by
  have h := z2Corank_selKSigned I (arithmeticCentralFiniteSigned t k D hcurve hfinite)
  rwa [← compactCentral_eq_arithmeticSigned t k D hcurve] at h

end ZInQ.Manuscript.RC
