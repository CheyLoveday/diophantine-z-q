import ZInQKernel.Contrib.OneProof.RC.Wiring.SignedCalibrationLeaf
import Mathlib.Tactic.NormNum.LegendreSymbol

/-!
# Theorem 5.3, Lane RC36: non-vacuity of the signed calibration route

Two kinds of checks for the signed restatement (`SignedCurve`, `SignedSelmer`, `SignedCoefficient`,
`SignedCentral`, `SignedCorank`, `SignedCalibrationLeaf`).

**The negative case occurs in Lean.** `signedExampleFamily` (`b = 1`, `Q = {7}`, `λ_7(x) = x₀`)
is admissible for `S = {2, 3, 11}`, `k = −3` (`signedExampleFamily_admissible`: `7` is an odd
prime outside `S`, `(−3/7) = 1`, `λ_7 ≠ 0`), and its member at `x = (1)` is `7* = −7`
(`signedExampleFamily_h`). So `Family.Admissible` alone does not force `h_x > 0`, the positive
route does not apply there (`signedExample_not_pos`), the natural-number encoding gives the
singular `E_0` (`signedExample_ecurve_toNat`), while the signed parameter gives the elliptic curve
`E^{(−7)} = E_{−77}` for `ℓ = 11` (`signedExample_etw`, `signedExample_isElliptic`), which is not
isomorphic over `ℚ` to `E_{77}` (`signedExample_not_iso`). The example is not claimed to satisfy
`FinalFamilyAt` (whose analytic clauses are not instantiated here).

**The input structures are no more demanding than the accepted ones.** The three restated inputs
are the RC53 group's inputs with `Ecurve ℓ` replaced by `curve t`:
* `KummerCohomologyFiniteSigned` holds at an address as soon as the two Milne finiteness prints and
  the places above `2` are given (`kummerCohomologyFiniteSigned_of_prints`);
* `KummerCoefficientComparisonSigned` (GLUE: the genuine truncated cochain comparison) is, at
  `t = ℓ`, exactly the original (`kummerCoefficientComparisonSigned_natCast_nonempty_iff`), and at
  a positive address exactly the original at `ℓ · h.toNat`
  (`nonempty_kummerCoefficientComparisonSigned_iff_of_pos`); at a negative address no original is
  available, and its truth is the same Galois-cohomological statement for the curve `E_{ℓh}`. No
  inhabitant is constructed here; RC37's `kcKummerCoefficientComparisonSigned`
  (`KummerCompArith.lean`) inhabits it for `k < 0` and `S` finite containing the primes above `2`,
  from the named finite-level Selmer description `KcArithSelmerLevel`;
* `SelmerCorankOneOverKSigned` is the original at `t = ℓ` (`selmerCorankOneOverKSigned_natCast`)
  and at positive addresses (`selmerCorankOneOverKSigned_iff_of_pos`).

The one new GLUE statement, `KummerCorankOneGlue` (used only by the forward route of
`SignedCalibrationLeaf.lean`), is the rank-one companion of the skeleton's `KummerCorankZero`
(PROVED in the tree, `kummerCorankZero_holds`); it holds by the Kummer sequence and Mordell–Weil,
is stated for every elliptic curve over `ℚ`, and has no inhabitant here.

Every declaration below is PROVED (or a definition).
-/

noncomputable section

namespace ZInQ.Manuscript.RC

open NumberField IsDedekindDomain WeierstrassCurve
open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53
open ZInQ.Manuscript.RC53Assist.CentralUniversal ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.RC53Assist.Calibration ZInQ.Contrib.RC53Assist.CalibrationIntegral
open ZInQ.Contrib.RC53Assist.CalibrationShape ZInQ.Contrib.RC53Assist.InnerLimitArith

/-! **An admissible family with a negative member** -/

/-- The linear form `x ↦ x₀` on `𝔽₂^1`. Kind: definition. -/
def signedExampleForm : Addr 1 →ₗ[ZMod 2] ZMod 2 where
  toFun x := x 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **A binary family with a negative member**: `b = 1`, `Q = {7}`, `λ_7(x) = x₀` (the other
forms zero), so `h_x = (7*)^{x₀}` with `7* = −7`. Kind: definition. -/
def signedExampleFamily : Family where
  b := 1
  Q := {7}
  lam q := if q = 7 then signedExampleForm else 0

/-- **The family is admissible** for `S = {2, 3, 11}` and `k = −3`: `7` is an odd prime outside
`S`, split in `ℚ(√−3)` (`(−3/7) = 1`), and `λ_7 ≠ 0`. Kind: PROVED. -/
theorem signedExampleFamily_admissible : signedExampleFamily.Admissible {2, 3, 11} (-3) := by
  intro q hq
  simp only [signedExampleFamily, Finset.mem_singleton] at hq
  subst hq
  refine ⟨by norm_num, by norm_num, by decide, by norm_num, ?_⟩
  simp only [signedExampleFamily, ite_true]
  intro h
  have h1 := LinearMap.congr_fun h (fun _ => 1)
  exact one_ne_zero h1

/-- **Its member at `x = (1)` is `7* = −7`.** Kind: PROVED. -/
theorem signedExampleFamily_h : signedExampleFamily.h (fun _ => 1) = -7 := by
  rfl

/-- The positive route does not apply at that address. Kind: PROVED. -/
theorem signedExample_not_pos : ¬ 0 < signedExampleFamily.h (fun _ => 1) := by
  rw [signedExampleFamily_h]
  norm_num

/-- At that address the natural-number encoding of the positive route gives the singular `E_0`.
Kind: PROVED. -/
theorem signedExample_ecurve_toNat :
    Ecurve (11 * (signedExampleFamily.h (fun _ => 1)).toNat) = curve 0 ∧
      ¬ (curve 0).IsElliptic :=
  ⟨ecurve_mul_toNat_of_neg (by rw [signedExampleFamily_h]; norm_num), not_isElliptic_curve_zero⟩

/-- At that address, for `ℓ = 11`, the twist is the signed family curve `E_{−77}`.
Kind: PROVED. -/
theorem signedExample_etw : Etw 11 (signedExampleFamily.h (fun _ => 1)) = curve (-77) := by
  rw [etw_eq_curve_mul, signedExampleFamily_h]
  norm_num

/-- `E_{−77}` is elliptic. Kind: PROVED. -/
theorem signedExample_isElliptic : (curve (-77)).IsElliptic :=
  curve_isElliptic_of_ne (by norm_num)

/-- `E_{−77}` is not isomorphic over `ℚ` to `E_{77} = E_{|−77|}`. Kind: PROVED. -/
theorem signedExample_not_iso (C : VariableChange ℚ) : C • curve (-77) ≠ curve 77 := by
  have h := variableChange_curve_ne_curve_abs (t := -77) (by norm_num) C
  rwa [show |(-77 : ℚ)| = 77 by norm_num] at h

/-! **The input structures** -/

/-- **The finite-generation input at an address from the two Milne finiteness prints** and the
places above `2` (`centralCohomologyFinite`), for `h` of either sign. Kind: PROVED. -/
theorem kummerCohomologyFiniteSigned_of_prints {k : ℤ} {ℓ : ℕ} {h : ℤ}
    (G : GenuineKummerData (QuadraticField k) (Ecurve ℓ) h)
    [(curve ((ℓ : ℚ) * h)).IsElliptic]
    (hloc : MilneLocalFiniteness) (hglob : MilneGlobalFiniteness)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 (QuadraticField k)),
      (2 : 𝓞 (QuadraticField k)) ∈ v.asIdeal → v ∈ G.S) :
    KummerCohomologyFiniteSigned ((ℓ : ℚ) * h) k G.S
      (arithmeticCentralFullSigned ((ℓ : ℚ) * h) k G (centralCurve_eq_curve_mul G)) :=
  arithmeticCentralFiniteSigned ((ℓ : ℚ) * h) k G (centralCurve_eq_curve_mul G)
    (centralCohomologyFinite G hloc hglob h2)

/-- **At a positive address the signed comparison is exactly the RC53 group's comparison** for
`Ecurve (ℓ · h.toNat)` (both directions, by transport along the equality of the two rational
parameters). Kind: PROVED. -/
theorem nonempty_kummerCoefficientComparisonSigned_iff_of_pos {k : ℤ} {ℓ : ℕ} {h : ℤ}
    (hh : 0 < h) (G : GenuineKummerData (QuadraticField k) (Ecurve ℓ) h)
    [(Ecurve (ℓ * h.toNat)).IsElliptic] [(curve ((ℓ : ℚ) * h)).IsElliptic] :
    Nonempty (KummerCoefficientComparisonSigned ((ℓ : ℚ) * h) k G.S
      (arithmeticCentralFullSigned ((ℓ : ℚ) * h) k G (centralCurve_eq_curve_mul G))) ↔
      Nonempty (KummerCoefficientComparison (ℓ * h.toNat) k G.S
        (arithmeticCentralFull (ℓ * h.toNat) k G (Wiring.centralCurve_eq_of_pos hh G))) := by
  have hpar : (((ℓ * h.toNat : ℕ) : ℚ)) = (ℓ : ℚ) * h := by
    rw [Nat.cast_mul, Wiring.natCast_toNat_of_pos hh]
  constructor
  · rintro ⟨I⟩
    exact ⟨KummerCoefficientComparisonSigned.toNat
      (KummerCoefficientComparisonSigned.congrParam hpar.symm I)⟩
  · rintro ⟨I⟩
    exact ⟨kummerCoefficientComparisonSigned_of_pos hh G I⟩

end ZInQ.Manuscript.RC
