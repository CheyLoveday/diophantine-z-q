import ZInQKernel.Contrib.OneProof.RC.TateWiring.Discharge
import ZInQKernel.Contrib.OneProof.RC.TateWiring.Kummer

/-!
# Lane RC22 (glue sweep), Tate share: lane RC17's Tate image without the determinant GLUE

Lane RC17 (`RC/TateWiring/Image.lean`, `Kummer.lean`) builds lane RC4's `TateImage` and
`MovingSetting` from the genuine `2`-adic Tate representation; its final statements take the GLUE
`DetTateTwoEqCyclotomic E` (`det ρ₂ = χ₂` over Mathlib's `cyclotomicCharacter`), bundled for `E_ℓ` as
`GlueTate := ∀ (E) [E.IsElliptic], DetTateTwoEqCyclotomic E`. Unlike lane RC9's `GlueArith`, this
bundle carries `[E.IsElliptic]`, and it is PROVED in the tree: lane RC17's
`ZInQ.Manuscript.RC.TateWiring.detTateTwoEqCyclotomic_holds` (`Discharge.lean`, the same body as
`ZInQ.Contrib.CloudB3RC53.DetTateCyclotomic.detTateTwoEqCyclotomic`, by definitional equality).

So the hypothesis is ALREADY DISCHARGED IN TREE, but the downstream statements still take it. Here:
* `glueTate : GlueTate` (PROVED);
* `tateImageOf`, `tateImageEcurveOf`, `movingSettingOf` (constructions without the GLUE);
* `moving_character_tate_of`, `moving_character_genuine_of`, `moving_character_ecurve_of`,
  `moving_character_ecurve_genuine_of`: Proposition `ex:arith-moving-character` (tex 3500–3702)
  over the genuine Tate image, from lane RC4's remaining interface fields, Serre's print and
  non-CM (for `E_ℓ`: the prints `ArithPrints` and `CMjInteger`) only.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.GlueSweep.Tate

open ZInQ.Manuscript.RC.PrintsArith ZInQ.Manuscript.RC.Moving ZInQ.Manuscript.RC.TateWiring
open scoped WeierstrassCurve MatrixGroups

/-- **Lane RC17's bundle `GlueTate` holds** (tex 3597–3605, "the determinant is the cyclotomic
character"). Kind: PROVED (no remaining hypothesis). Consumer: the hypothesis `H : GlueTate` of lane
RC17's `tateImageEcurve`, `moving_character_ecurve`, `moving_character_ecurve_genuine`; discharger:
lane RC17's `detTateTwoEqCyclotomic_holds` (= `ZInQ.Contrib.CloudB3RC53.DetTateCyclotomic.
detTateTwoEqCyclotomic`). -/
theorem glueTate : GlueTate :=
  ⟨fun E _ => detTateTwoEqCyclotomic_holds E⟩

/-- **The converse direction of `det ρ₂ = χ₂` holds for every elliptic `E/ℚ`** (tex 3598–3599: an
element of `G_{ℚ(μ_{2^∞})}` has `det ρ₂ = 1`, so `ρ₂` maps `G_{ℚ(μ_{2^∞})}` into `SL₂(ℤ₂)`). Kind:
PROVED (no remaining hypothesis). Consumer: the hypothesis `hconv` of lane RC17's
`det_tateMatrix_eq_one`, `rhoSL`, `mem_range_rhoSL_iff`, `serre_Γ_le_range`; discharger: lane RC17's
`DetTateTwoEqCyclotomic.converse` applied to `detTateTwoEqCyclotomic_holds`. -/
theorem detTateTwoCyclotomicConverse_holds (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    DetTateTwoCyclotomicConverse E :=
  (detTateTwoEqCyclotomic_holds E).converse

/-- **`Γ_d ⊂ J = ρ₂(G_{ℚ(μ_{2^∞})})`** (tex 3600–3605) for a non-CM elliptic `E/ℚ`, with `J` the range of
`rhoSL E` built from the proved converse direction. Kind: PROVED from `SerreThm3` (PRINT) and
`HasNoCM E`. Consumer: lane RC17's `serre_Γ_le_range` (hypothesis `hconv` discharged by
`detTateTwoCyclotomicConverse_holds`). -/
theorem serre_Γ_le_range_of (E : WeierstrassCurve ℚ) [E.IsElliptic] (hS : SerreThm3)
    (hE : HasNoCM E) :
    ∃ d : ℕ, 2 ≤ d ∧ Γ d ≤ (rhoSL E (detTateTwoCyclotomicConverse_holds E)).range :=
  serre_Γ_le_range E hS hE (detTateTwoCyclotomicConverse_holds E)

/-- **The fixed Tate image of an elliptic non-CM `E/ℚ` as lane RC4's `TateImage`, without the
determinant GLUE** (tex 3597–3605): lane RC17's `tateImage E hS hE hdetEq` with `hdetEq` discharged
by `detTateTwoEqCyclotomic_holds`. Hypotheses: `SerreThm3` (PRINT) and `HasNoCM E`. -/
def tateImageOf (E : WeierstrassCurve ℚ) [E.IsElliptic] (hS : SerreThm3) (hE : HasNoCM E) :
    TateImage :=
  tateImage E hS hE (detTateTwoEqCyclotomic_holds E)

/-- **Proposition `ex:arith-moving-character` for the genuine Tate image of a non-CM elliptic
`E/ℚ`** (tex 3500–3702), with `c_E = 16 d + 21`. Kind: PROVED from `SerreThm3` (PRINT), `HasNoCM E`
and lane RC4's remaining `MovingSetting` fields. Consumer: lane RC17's `moving_character_tate`
(hypothesis `hdetEq` discharged by `detTateTwoEqCyclotomic_holds`). -/
theorem moving_character_tate_of {E : WeierstrassCurve ℚ} [E.IsElliptic] (hS : SerreThm3)
    (hE : HasNoCM E) {n : ℕ} (M : MovingSetting (tateImageOf E hS hE) n) (B : ℕ)
    (S : Finset ℕ) :
    ∃ r : ℕ, r ∉ S ∧ r.Prime ∧ M.good r ∧ (2 : ℤ) ^ B ∣ (r : ℤ) - 1 ∧
      ∃ ξ : M.P r →+ ZMod (2 ^ n),
        (∀ y : ZMod (2 ^ n), ∃ z ∈ M.inertia r, ξ z = y) ∧
        (∀ j, M.over2N j → ∀ z ∈ M.decomp r j ⊔ M.decompBar r j, ξ z = 0) ∧
        (∀ j, M.act j → ξ (M.q r j) = 1 ∧ ξ (M.qbar r j) = -1) ∧
        ¬ (2 : ℤ) ^ (cE (tateImageOf E hS hE).d + 1) ∣ 2 + M.ap r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageOf E hS hE).d + 1) ∣ 2 - M.ap r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageOf E hS hE).d + 1) ∣ 1 + M.ap r + r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageOf E hS hE).d + 1) ∣ 1 - M.ap r + r ∧
        ∀ χ : ℤ, (χ = 1 ∨ χ = -1) →
          ¬ (2 : ℤ) ^ (cE (tateImageOf E hS hE).d + 1) ∣ M.ap r - 2 * χ :=
  moving_character_tate hS hE (detTateTwoEqCyclotomic_holds E) M B S

/-- **Lane RC4's `MovingSetting` over the genuine Tate image and Kummer layer, from lane RC17's
`MovingData`, without the determinant GLUE**: lane RC17's `MovingData.toMovingSetting` with `hdetEq`
discharged by `detTateTwoEqCyclotomic_holds` (its fields `GF_index`, `HL_le`, `kum_of_mem_HL`,
`mem_HL_of_kum` are lane RC17's PROVED `GFinf_index`, `KummerData.HLinf_le`,
`KummerData.kum_of_mem_HL`, `KummerData.mem_HL_of_kum`). -/
def movingSettingOf {E : WeierstrassCurve ℚ} [E.IsElliptic] (hS : SerreThm3) (hE : HasNoCM E)
    {n : ℕ} (M : MovingData E n) : MovingSetting (tateImageOf E hS hE) n :=
  M.toMovingSetting hS hE (detTateTwoEqCyclotomic_holds E)

/-- **Proposition `ex:arith-moving-character` over the genuine Tate image and Kummer layer**
(tex 3500–3702). Kind: PROVED from `SerreThm3` (PRINT), `HasNoCM E` and the remaining fields of lane
RC17's `MovingData` (RC4's GLUE/PRINT fields other than the four Kummer fields). Consumer: lane
RC17's `moving_character_genuine` (hypothesis `hdetEq` discharged by
`detTateTwoEqCyclotomic_holds`). -/
theorem moving_character_genuine_of {E : WeierstrassCurve ℚ} [E.IsElliptic] (hS : SerreThm3)
    (hE : HasNoCM E) {n : ℕ} (M : MovingData E n) (B : ℕ) (S : Finset ℕ) :
    ∃ r : ℕ, r ∉ S ∧ r.Prime ∧ M.good r ∧ (2 : ℤ) ^ B ∣ (r : ℤ) - 1 ∧
      ∃ ξ : M.P r →+ ZMod (2 ^ n),
        (∀ y : ZMod (2 ^ n), ∃ z ∈ M.inertia r, ξ z = y) ∧
        (∀ j, M.over2N j → ∀ z ∈ M.decomp r j ⊔ M.decompBar r j, ξ z = 0) ∧
        (∀ j, M.act j → ξ (M.q r j) = 1 ∧ ξ (M.qbar r j) = -1) ∧
        ¬ (2 : ℤ) ^ (cE (tateImageOf E hS hE).d + 1) ∣ 2 + M.ap r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageOf E hS hE).d + 1) ∣ 2 - M.ap r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageOf E hS hE).d + 1) ∣ 1 + M.ap r + r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageOf E hS hE).d + 1) ∣ 1 - M.ap r + r ∧
        ∀ χ : ℤ, (χ = 1 ∨ χ = -1) →
          ¬ (2 : ℤ) ^ (cE (tateImageOf E hS hE).d + 1) ∣ M.ap r - 2 * χ :=
  moving_character_genuine hS hE (detTateTwoEqCyclotomic_holds E) M B S

/-! ### The curves `E_ℓ` -/

/-- **The fixed Tate image of `E_ℓ`, `ℓ > 0`, without the determinant GLUE** (tex 3597–3605): lane
RC17's `tateImageEcurve P hcm H hℓ` with `H := glueTate`. Hypotheses: `ArithPrints` (only its field
`serre` is used) and `CMjInteger` (GLUE, non-CM of `E_ℓ`). -/
def tateImageEcurveOf (P : ArithPrints) (hcm : CMjInteger) {ℓ : ℕ} (hℓ : 0 < ℓ) : TateImage :=
  tateImageEcurve P hcm glueTate hℓ

/-- **Proposition `ex:arith-moving-character` for `E_ℓ`** (tex 3500–3702). Kind: PROVED from
`ArithPrints` (PRINT), `CMjInteger` (GLUE) and lane RC4's remaining `MovingSetting` fields.
Consumer: lane RC17's `moving_character_ecurve` (hypothesis `H : GlueTate` discharged by
`glueTate`). -/
theorem moving_character_ecurve_of (P : ArithPrints) (hcm : CMjInteger) {ℓ : ℕ} (hℓ : 0 < ℓ)
    {n : ℕ} (M : MovingSetting (tateImageEcurveOf P hcm hℓ) n) (B : ℕ) (S : Finset ℕ) :
    ∃ r : ℕ, r ∉ S ∧ r.Prime ∧ M.good r ∧ (2 : ℤ) ^ B ∣ (r : ℤ) - 1 ∧
      ∃ ξ : M.P r →+ ZMod (2 ^ n),
        (∀ y : ZMod (2 ^ n), ∃ z ∈ M.inertia r, ξ z = y) ∧
        (∀ j, M.over2N j → ∀ z ∈ M.decomp r j ⊔ M.decompBar r j, ξ z = 0) ∧
        (∀ j, M.act j → ξ (M.q r j) = 1 ∧ ξ (M.qbar r j) = -1) ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurveOf P hcm hℓ).d + 1) ∣ 2 + M.ap r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurveOf P hcm hℓ).d + 1) ∣ 2 - M.ap r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurveOf P hcm hℓ).d + 1) ∣ 1 + M.ap r + r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurveOf P hcm hℓ).d + 1) ∣ 1 - M.ap r + r ∧
        ∀ χ : ℤ, (χ = 1 ∨ χ = -1) →
          ¬ (2 : ℤ) ^ (cE (tateImageEcurveOf P hcm hℓ).d + 1) ∣ M.ap r - 2 * χ :=
  moving_character_ecurve P hcm glueTate hℓ M B S

/-- **Proposition `ex:arith-moving-character` for `E_ℓ` over the genuine Kummer layer**
(tex 3500–3702). Kind: PROVED from `ArithPrints` (PRINT), `CMjInteger` (GLUE) and the remaining
fields of lane RC17's `MovingData`. Consumer: lane RC17's `moving_character_ecurve_genuine`
(hypothesis `H : GlueTate` discharged by `glueTate`). -/
theorem moving_character_ecurve_genuine_of (P : ArithPrints) (hcm : CMjInteger) {ℓ : ℕ}
    (hℓ : 0 < ℓ) {n : ℕ} (M : MovingData (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) n) (B : ℕ)
    (S : Finset ℕ) :
    ∃ r : ℕ, r ∉ S ∧ r.Prime ∧ M.good r ∧ (2 : ℤ) ^ B ∣ (r : ℤ) - 1 ∧
      ∃ ξ : M.P r →+ ZMod (2 ^ n),
        (∀ y : ZMod (2 ^ n), ∃ z ∈ M.inertia r, ξ z = y) ∧
        (∀ j, M.over2N j → ∀ z ∈ M.decomp r j ⊔ M.decompBar r j, ξ z = 0) ∧
        (∀ j, M.act j → ξ (M.q r j) = 1 ∧ ξ (M.qbar r j) = -1) ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurveOf P hcm hℓ).d + 1) ∣ 2 + M.ap r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurveOf P hcm hℓ).d + 1) ∣ 2 - M.ap r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurveOf P hcm hℓ).d + 1) ∣ 1 + M.ap r + r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurveOf P hcm hℓ).d + 1) ∣ 1 - M.ap r + r ∧
        ∀ χ : ℤ, (χ = 1 ∨ χ = -1) →
          ¬ (2 : ℤ) ^ (cE (tateImageEcurveOf P hcm hℓ).d + 1) ∣ M.ap r - 2 * χ :=
  moving_character_ecurve_genuine P hcm glueTate hℓ M B S

end ZInQ.Manuscript.RC.GlueSweep.Tate
