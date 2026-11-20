import ZInQKernel.Contrib.OneProof.RC.Height.Discharge
import ZInQKernel.Contrib.OneProof.RC.Central.Nodes

/-!
# Lane RC22 (glue sweep, central share): the calibration (4.6) and `UpperBound` with the regulator
# inputs discharged

Proposition `ex:arith-central-calibration` of the 11/5 manuscript (`diophantine_zq.tex`, lines
3987–4140), at the regulator step (tex 4022–4030, 4082–4091, 4106–4113): "the sum/difference
isogenies are dual and compose to `[2]`. Their free-lattice indices satisfy `IJ = 2`, with regulator
ratio `2/I²`", then the arithmetic isogeny identity
`s_A − s_B = 2g_A − 2g_B + v₂(Reg_B/Reg_A) + v₂(Ω_B/Ω_A) + v₂(C_B/C_A)`.

Lane RC15 takes the regulator facts as hypotheses:

* `Calibration.calibration_46` and `Nodes.upperBound_of_calibration` take
  `hReg : v₂(Reg_B/Reg_A) = 1 ∨ v₂(Reg_B/Reg_A) = −1` (for an abstract integer `vReg`);
* `Calibration.milne_valuation_form` takes `hRegA : Reg_A ≠ 0` and `hρReg : ρ_Reg ≠ 0` with
  `Reg_B = ρ_Reg Reg_A`, `ρ_Reg ∈ ℚ`;
* `Calibration.regulator_ratio` (over `ℝ`) and `milne_valuation_form_of_adjunction` take the height
  adjunction `α Reg_B = β Reg_A` with `αβ = 2` for real regulators and derive the rational ratio
  `Reg_B/Reg_A = 2/α²`.

Lane RC19 proved these for the genuine regulators
(`ZInQ.Manuscript.RC.Height.regulator_ratio_sumDiff` and `regulator_inputs_sumDiff`: for rank-one
free generators `g_A` of `A(ℚ) = E^{(h)}(K)` and `g_B` of `B(ℚ) = E^{(h)}(ℚ) × E^{(hk)}(ℚ)`, the
adjunction on the real canonical heights,
`Reg_B = (2/α²) Reg_A`, `v₂(2/α²) = ±1`, `Reg_A > 0`; lane RC19's DEPARTURE D1 and GLUE G1 fix the
pairings of `A` and `B`). This file composes them with lane RC15's consumers, so that the consumers
no longer take the regulator hypotheses. Where a statement names the rational ratio `ρ_Reg`, the
hypothesis `hρ : Reg_B = ρ_Reg Reg_A` only names the rational value of the real ratio of the genuine
regulators (it exists and is `2/α²`: `exists_regulator_ratio_sumDiff`; it is unique as `Reg_A > 0`);
it is not an assumption on the regulators, and the node-level statements
(`calibration_46_of_milne_genuine_sumDiff`, `upperBound_of_milne_sumDiff`) do not take it.

* `padicValRat_regulator_sumDiff`, `exists_regulator_ratio_sumDiff`: the regulator ratio is a
  rational number of two-adic valuation `±1` (lane RC15's `hReg`).
* `milne_valuation_form_sumDiff`: lane RC15's `milne_valuation_form` on the genuine regulators,
  `hRegA` and `hρReg` removed.
* `calibration_46_sumDiff`: lane RC15's `calibration_46`, `hReg` removed.
* `calibration_46_of_milne_sumDiff`: (4.6) from Milne's print on the genuine regulators (the
  valuation identity, `hReg`, `hRegA`, `hρReg` all derived).
* `calibration_46_of_milne_genuine_sumDiff`: the same with the regulator ratio produced, not named:
  `Reg_B/Reg_A = 2/α²` for the indices `α, β` of the free generators (lane RC15's
  `regulator_ratio_div` and `milne_valuation_form_of_adjunction` on lane RC19's adjunction).
* `upperBound_of_calibration_sumDiff`: lane RC15's `upperBound_of_calibration`, `hReg` removed.
* `upperBound_of_milne_sumDiff`: the node `UpperBound C B` from Milne's print on the genuine
  regulators at every address (the rational regulator ratios are derived, not inputs).

Every theorem in this file is PROVED (from the stated remaining inputs).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.GlueSweep.Central

open ZInQ.Contrib.CloudB3RC53
open ZInQ.Manuscript.RC.Height (heightB IsFreeGenerator QuadData)
open ZInQ.Manuscript.RC.Central (diskContribution MilneIsogenyInvariance)

/-! ### The regulator ratio at one address -/

section Regulator

variable {K : Type*} [Field K] [NumberField K] [DecidableEq K] [Algebra.IsQuadraticExtension ℚ K]
  (E : WeierstrassCurve ℚ) (h k : ℚ) (Dq : QuadData K k)
  [(qtwist E h).IsElliptic] [(qtwist E (h * k)).IsElliptic]

include Dq

/-- **The regulator ratio `Reg_B / Reg_A` is a rational number of two-adic valuation `±1`**
(tex 4024–4025, 4088–4090, 4110: "`Reg_B/Reg_A = 2/I²`").

Consumer: the hypothesis `hReg` of lane RC15's `ZInQ.Manuscript.RC.Central.calibration_46` (and of
`upperBound_of_calibration`), for `vReg = v₂ ρ_Reg`. Discharger: lane RC19's
`ZInQ.Manuscript.RC.Height.regulator_inputs_sumDiff`. For rank-one free generators `g_A` of
`A(ℚ) = E^{(h)}(K)` and `g_B` of `B(ℚ) = E^{(h)}(ℚ) × E^{(hk)}(ℚ)` (`K = ℚ(√k)` with its data `Dq`),
any rational `ρ_Reg` with `Reg_B = ρ_Reg Reg_A` (`Reg_A = ĥ(g_A) > 0`, `Reg_B = ĥ_B(g_B)`) is
`2/α²` and has `v₂ ρ_Reg = ±1`. PROVED, from the remaining inputs: rank one (the free generators,
forward-theorem inputs, tex 4020–4021) and lane RC19's pairings of `A`, `B` (DEPARTURE D1 /
GLUE G1 there). -/
theorem padicValRat_regulator_sumDiff (genA : ((qtwist E h).baseChange K).toAffine.Point)
    (genB : ((qtwist E h).baseChange ℚ).toAffine.Point ×
      ((qtwist E (h * k)).baseChange ℚ).toAffine.Point)
    (hA : IsFreeGenerator genA) (hB : IsFreeGenerator genB) (ρReg : ℚ)
    (hρ : heightB E h k genB = (ρReg : ℝ) * genA.canonicalHeight) :
    padicValRat 2 ρReg = 1 ∨ padicValRat 2 ρReg = -1 := by
  obtain ⟨α, β, -, -, -, -, -, hreg, hv, hpos⟩ :=
    ZInQ.Manuscript.RC.Height.regulator_inputs_sumDiff E h k Dq genA genB hA hB
  have h1 : (ρReg : ℝ) = ((2 / (α : ℚ) ^ 2 : ℚ) : ℝ) :=
    mul_right_cancel₀ hpos.ne' (hρ.symm.trans hreg)
  have h2 : ρReg = 2 / (α : ℚ) ^ 2 := by exact_mod_cast h1
  rw [h2]
  exact hv

/-- **The regulator ratio exists and is a nonzero rational of valuation `±1`, with `Reg_A > 0`**
(tex 4024–4025, 4088–4090). Consumer: the inputs `hReg` of `calibration_46` and `hRegA`, `hρReg`
of `milne_valuation_form` (lane RC15). Discharger: lane RC19's
`ZInQ.Manuscript.RC.Height.regulator_inputs_sumDiff`. PROVED, from rank one (the free
generators). -/
theorem exists_regulator_ratio_sumDiff (genA : ((qtwist E h).baseChange K).toAffine.Point)
    (genB : ((qtwist E h).baseChange ℚ).toAffine.Point ×
      ((qtwist E (h * k)).baseChange ℚ).toAffine.Point)
    (hA : IsFreeGenerator genA) (hB : IsFreeGenerator genB) :
    ∃ ρReg : ℚ, heightB E h k genB = (ρReg : ℝ) * genA.canonicalHeight ∧ ρReg ≠ 0 ∧
      (padicValRat 2 ρReg = 1 ∨ padicValRat 2 ρReg = -1) ∧ 0 < genA.canonicalHeight := by
  obtain ⟨α, β, -, -, hαβ, -, -, hreg, hv, hpos⟩ :=
    ZInQ.Manuscript.RC.Height.regulator_inputs_sumDiff E h k Dq genA genB hA hB
  have hα : (α : ℚ) ≠ 0 := by
    have : α ≠ 0 := by rintro rfl; simp at hαβ
    exact_mod_cast this
  exact ⟨2 / (α : ℚ) ^ 2, hreg, div_ne_zero two_ne_zero (pow_ne_zero 2 hα), hv, hpos⟩

/-- **The two-adic isogeny identity on the genuine regulators** (tex 4027–4030, 4106–4113).

Consumer: lane RC15's `ZInQ.Manuscript.RC.Central.milne_valuation_form`, whose inputs
`hRegA : Reg_A ≠ 0` and `hρReg : ρ_Reg ≠ 0` are removed here. Discharger: lane RC19's
`ZInQ.Manuscript.RC.Height.regulator_inputs_sumDiff` (through `exists_regulator_ratio_sumDiff` and
`padicValRat_regulator_sumDiff`). Milne's print (`MilneIsogenyInvariance`, PRINT, lane RC15) is
applied with `Reg_A = ĥ(g_A)` and `Reg_B = ĥ_B(g_B)`, the genuine regulators at rank one; the
conclusion also records `v₂ ρ_Reg = ±1`.

PROVED, from the remaining inputs: rank one (free generators), the nonvanishing of the orders and
periods, and the print; `hρ` only names the rational value `ρ_Reg` of the real ratio
`Reg_B/Reg_A` (it exists: `exists_regulator_ratio_sumDiff`). -/
theorem milne_valuation_form_sumDiff (genA : ((qtwist E h).baseChange K).toAffine.Point)
    (genB : ((qtwist E h).baseChange ℚ).toAffine.Point ×
      ((qtwist E (h * k)).baseChange ℚ).toAffine.Point)
    (hA : IsFreeGenerator genA) (hB : IsFreeGenerator genB) (ρReg : ℚ)
    (hρ : heightB E h k genB = (ρReg : ℝ) * genA.canonicalHeight)
    {shaA shaB tA tB CA CB : ℕ} {ΩA : ℝ} {ρΩ : ℚ}
    (hshaA : shaA ≠ 0) (hshaB : shaB ≠ 0) (htA : tA ≠ 0) (htB : tB ≠ 0) (hCA : CA ≠ 0)
    (hCB : CB ≠ 0) (hΩA : ΩA ≠ 0) (hρΩ : ρΩ ≠ 0)
    (hMilne : MilneIsogenyInvariance shaA shaB tA tA tB tB CA CB genA.canonicalHeight
      (heightB E h k genB) ΩA ((ρΩ : ℝ) * ΩA)) :
    (padicValNat 2 shaA : ℤ) - padicValNat 2 shaB =
        2 * (padicValNat 2 tA : ℤ) - 2 * padicValNat 2 tB + padicValRat 2 ρReg +
          padicValRat 2 ρΩ + padicValRat 2 ((CB : ℚ) / CA) ∧
      (padicValRat 2 ρReg = 1 ∨ padicValRat 2 ρReg = -1) := by
  have hv := padicValRat_regulator_sumDiff E h k Dq genA genB hA hB ρReg hρ
  obtain ⟨-, -, -, -, hpos⟩ := exists_regulator_ratio_sumDiff E h k Dq genA genB hA hB
  have hρ0 : ρReg ≠ 0 := by
    rintro rfl
    simp at hv
  rw [hρ] at hMilne
  exact ⟨ZInQ.Manuscript.RC.Central.milne_valuation_form hshaA hshaB htA htB hCA hCB hpos.ne' hΩA
    hρ0 hρΩ hMilne, hv⟩

/-- **The calibration (4.6) with `hReg` discharged** (tex 4044–4047, 4051–4140; regulator step tex
4082–4091, 4110).

Consumer: lane RC15's `ZInQ.Manuscript.RC.Central.calibration_46`, with `vReg := v₂ ρ_Reg` for the
genuine regulator ratio, so its hypothesis `hReg : vReg = 1 ∨ vReg = −1` is removed. Discharger:
lane RC19's `ZInQ.Manuscript.RC.Height.regulator_inputs_sumDiff` (through
`padicValRat_regulator_sumDiff`).

PROVED, from the remaining inputs: rank one (free generators) (`hρ` only names the rational value
of the real ratio `Reg_B/Reg_A`); and lane RC15's other inputs with their kinds: `hprim` (ELLIOT),
`hvN` (PROVED in lane RC15 as `padicValInt_movingNorm`), `hMilne` (the valuation form of Milne's
PRINT), `hsB`, `hvC` (component ratio, with Edixhoven's
PRINT), `hΩ` (period ratio, GLUE real change of variables), `hgB` (ELLIOT torsion bound), `hvL`. -/
theorem calibration_46_sumDiff (genA : ((qtwist E h).baseChange K).toAffine.Point)
    (genB : ((qtwist E h).baseChange ℚ).toAffine.Point ×
      ((qtwist E (h * k)).baseChange ℚ).toAffine.Point)
    (hA : IsFreeGenerator genA) (hB : IsFreeGenerator genB) (ρReg : ℚ)
    (hρ : heightB E h k genB = (ρReg : ℝ) * genA.canonicalHeight)
    {j vL vm vN ω gA sA gB sB sh shk vΩ vC T vprim G₀ : ℤ}
    (hprim : vprim = (j + vL + vm) + (j + vL + vm) +
      (diskContribution 1 gA + diskContribution 2 sA + diskContribution 3 gA) +
      (2 * diskContribution 2 vN + ω * (2 * diskContribution 2 2)))
    (hvN : vN = vm) (hMilne : sA - sB = 2 * gA - 2 * gB + padicValRat 2 ρReg + vΩ + vC)
    (hsB : sB = sh + shk) (hvC : vC = T) (hΩ : |vΩ| ≤ 4)
    (hgB : 0 ≤ gB ∧ gB ≤ G₀) (hvL : 0 ≤ vL) :
    vprim = 2 * j - 4 * ω - sh - shk - T + (2 * vL + 2 * gB - padicValRat 2 ρReg - vΩ) ∧
      |2 * vL + 2 * gB - padicValRat 2 ρReg - vΩ| ≤ 2 * vL + 2 * G₀ + 5 :=
  ZInQ.Manuscript.RC.Central.calibration_46 hprim hvN hMilne hsB hvC
    (padicValRat_regulator_sumDiff E h k Dq genA genB hA hB ρReg hρ) hΩ hgB hvL

/-- **The calibration (4.6) from Milne's print on the genuine regulators** (tex 4022–4030,
4044–4047, 4082–4113).

Consumers: lane RC15's `calibration_46` and `milne_valuation_form` composed, with the Kummer
torsion and Tate–Shafarevich lengths read off the orders: `g_A = v₂ t_A`, `s_A = v₂ |Ш(A)|`,
`g_B = v₂ t_B`, `s_B = v₂ |Ш(B)|`, `v₂(C_B/C_A)` and `v₂ ρ_Ω`. Removed: `hReg`, `hRegA`, `hρReg`
and the valuation identity `hMilne` (now derived from the print). Dischargers: lane RC19's
`ZInQ.Manuscript.RC.Height.regulator_inputs_sumDiff` and lane RC15's own `milne_valuation_form`.

PROVED, from the remaining inputs: rank one (free generators), the nonvanishing of the orders and
periods, Milne's print `MilneIsogenyInvariance` at `Reg_A = ĥ(g_A)`, `Reg_B = ĥ_B(g_B)` (PRINT),
and lane RC15's `hprim` (ELLIOT), `hvN`, `hsB`, `hvC` (with Edixhoven's PRINT), `hΩ` (GLUE real
change of variables), `hgB` (ELLIOT), `hvL`; `hρ` only names the rational value of the real ratio
`Reg_B/Reg_A` (see `calibration_46_of_milne_genuine_sumDiff` for the form without it). -/
theorem calibration_46_of_milne_sumDiff (genA : ((qtwist E h).baseChange K).toAffine.Point)
    (genB : ((qtwist E h).baseChange ℚ).toAffine.Point ×
      ((qtwist E (h * k)).baseChange ℚ).toAffine.Point)
    (hA : IsFreeGenerator genA) (hB : IsFreeGenerator genB) (ρReg : ℚ)
    (hρ : heightB E h k genB = (ρReg : ℝ) * genA.canonicalHeight)
    {shaA shaB tA tB CA CB : ℕ} {ΩA : ℝ} {ρΩ : ℚ}
    (hshaA : shaA ≠ 0) (hshaB : shaB ≠ 0) (htA : tA ≠ 0) (htB : tB ≠ 0) (hCA : CA ≠ 0)
    (hCB : CB ≠ 0) (hΩA : ΩA ≠ 0) (hρΩ : ρΩ ≠ 0)
    (hMilne : MilneIsogenyInvariance shaA shaB tA tA tB tB CA CB genA.canonicalHeight
      (heightB E h k genB) ΩA ((ρΩ : ℝ) * ΩA))
    {j vL vm vN ω sh shk T vprim G₀ : ℤ}
    (hprim : vprim = (j + vL + vm) + (j + vL + vm) +
      (diskContribution 1 (padicValNat 2 tA) + diskContribution 2 (padicValNat 2 shaA) +
        diskContribution 3 (padicValNat 2 tA)) +
      (2 * diskContribution 2 vN + ω * (2 * diskContribution 2 2)))
    (hvN : vN = vm) (hsB : (padicValNat 2 shaB : ℤ) = sh + shk)
    (hvC : padicValRat 2 ((CB : ℚ) / CA) = T) (hΩ : |padicValRat 2 ρΩ| ≤ 4)
    (hgB : (padicValNat 2 tB : ℤ) ≤ G₀) (hvL : 0 ≤ vL) :
    vprim = 2 * j - 4 * ω - sh - shk - T +
        (2 * vL + 2 * (padicValNat 2 tB : ℤ) - padicValRat 2 ρReg - padicValRat 2 ρΩ) ∧
      |2 * vL + 2 * (padicValNat 2 tB : ℤ) - padicValRat 2 ρReg - padicValRat 2 ρΩ| ≤
        2 * vL + 2 * G₀ + 5 := by
  obtain ⟨hid, hv⟩ := milne_valuation_form_sumDiff E h k Dq genA genB hA hB ρReg hρ hshaA hshaB
    htA htB hCA hCB hΩA hρΩ hMilne
  exact ZInQ.Manuscript.RC.Central.calibration_46 hprim hvN hid hsB hvC hv hΩ
    ⟨Int.natCast_nonneg _, hgB⟩ hvL

/-- **The calibration (4.6) from Milne's print on the genuine regulators, the regulator ratio
derived** (tex 4022–4030, 4044–4047, 4082–4113).

As `calibration_46_of_milne_sumDiff`, without naming the ratio: the indices `α, β` of the free
generators are produced (`φ g_A ≡ α g_B`, `ψ g_B ≡ β g_A` modulo torsion, `αβ = 2`), the real ratio
of the genuine regulators `ĥ_B(g_B) / ĥ_A(g_A)` is the rational number `2/α²` (lane RC15's
`regulator_ratio_div`, over `ℝ`, fed with lane RC19's adjunction `regulator_ratio_sumDiff`), and
(4.6) holds with the error `2v₂L + 2g_B − v₂(2/α²) − v₂ρ_Ω`, `|error| ≤ 2v₂L + 2G₀ + 5`. Consumers:
lane RC15's `milne_valuation_form_of_adjunction` and `calibration_46`. Dischargers: lane RC19's
`regulator_ratio_sumDiff`, `regulator_inputs_sumDiff`.

PROVED, from the remaining inputs: rank one (free generators), the nonvanishing of the orders and
periods, Milne's print at `Reg_A = ĥ(g_A)`, `Reg_B = ĥ_B(g_B)` (PRINT), and lane RC15's `hprim`
(ELLIOT), `hvN`, `hsB`, `hvC` (with Edixhoven's PRINT), `hΩ` (GLUE real change of variables), `hgB`
(ELLIOT), `hvL`. No rational regulator ratio is an input: the hypotheses are those of
`calibration_46_of_milne_sumDiff` without `ρ_Reg` and `hρ`. -/
theorem calibration_46_of_milne_genuine_sumDiff
    (genA : ((qtwist E h).baseChange K).toAffine.Point)
    (genB : ((qtwist E h).baseChange ℚ).toAffine.Point ×
      ((qtwist E (h * k)).baseChange ℚ).toAffine.Point)
    (hA : IsFreeGenerator genA) (hB : IsFreeGenerator genB)
    {shaA shaB tA tB CA CB : ℕ} {ΩA : ℝ} {ρΩ : ℚ}
    (hshaA : shaA ≠ 0) (hshaB : shaB ≠ 0) (htA : tA ≠ 0) (htB : tB ≠ 0) (hCA : CA ≠ 0)
    (hCB : CB ≠ 0) (hΩA : ΩA ≠ 0) (hρΩ : ρΩ ≠ 0)
    (hMilne : MilneIsogenyInvariance shaA shaB tA tA tB tB CA CB genA.canonicalHeight
      (heightB E h k genB) ΩA ((ρΩ : ℝ) * ΩA))
    {j vL vm vN ω sh shk T vprim G₀ : ℤ}
    (hprim : vprim = (j + vL + vm) + (j + vL + vm) +
      (diskContribution 1 (padicValNat 2 tA) + diskContribution 2 (padicValNat 2 shaA) +
        diskContribution 3 (padicValNat 2 tA)) +
      (2 * diskContribution 2 vN + ω * (2 * diskContribution 2 2)))
    (hvN : vN = vm) (hsB : (padicValNat 2 shaB : ℤ) = sh + shk)
    (hvC : padicValRat 2 ((CB : ℚ) / CA) = T) (hΩ : |padicValRat 2 ρΩ| ≤ 4)
    (hgB : (padicValNat 2 tB : ℤ) ≤ G₀) (hvL : 0 ≤ vL) :
    ∃ α β : ℤ, IsOfFinAddOrder (ZInQ.Manuscript.RC.Height.diffMap E h k Dq genA - α • genB) ∧
      IsOfFinAddOrder (ZInQ.Manuscript.RC.Height.sumMap E h k Dq genB - β • genA) ∧
      α * β = 2 ∧
      heightB E h k genB / genA.canonicalHeight = ((2 / (α : ℚ) ^ 2 : ℚ) : ℝ) ∧
      vprim = 2 * j - 4 * ω - sh - shk - T +
        (2 * vL + 2 * (padicValNat 2 tB : ℤ) - padicValRat 2 (2 / (α : ℚ) ^ 2) -
          padicValRat 2 ρΩ) ∧
      |2 * vL + 2 * (padicValNat 2 tB : ℤ) - padicValRat 2 (2 / (α : ℚ) ^ 2) -
          padicValRat 2 ρΩ| ≤ 2 * vL + 2 * G₀ + 5 := by
  obtain ⟨α, β, hα, hβ, hαβ, hadj, -, -, -, hpos⟩ :=
    ZInQ.Manuscript.RC.Height.regulator_inputs_sumDiff E h k Dq genA genB hA hB
  obtain ⟨hid, hv⟩ := ZInQ.Manuscript.RC.Central.milne_valuation_form_of_adjunction hαβ hadj
    hshaA hshaB htA htB hCA hCB hpos.ne' hΩA hρΩ hMilne
  obtain ⟨hcal, hbd⟩ := ZInQ.Manuscript.RC.Central.calibration_46 hprim hvN hid hsB hvC hv hΩ
    ⟨Int.natCast_nonneg _, hgB⟩ hvL
  exact ⟨α, β, hα, hβ, hαβ,
    (ZInQ.Manuscript.RC.Central.regulator_ratio_div hαβ hadj hpos.ne').1, hcal, hbd⟩

end Regulator

/-! ### `UpperBound` at every address -/

section Addresses

variable {K : Type*} [Field K] [NumberField K] [DecidableEq K] [Algebra.IsQuadraticExtension ℚ K]
  (E : WeierstrassCurve ℚ) (k : ℚ) (Dq : QuadData K k) {b : ℕ} (h : (Fin b → ZMod 2) → ℚ)
  [∀ x, (qtwist E (h x)).IsElliptic] [∀ x, (qtwist E (h x * k)).IsElliptic]

include Dq

/-- **`UpperBound` from the calibration inputs, `hReg` discharged** (tex 4044–4047, 4082–4091,
5730–5733, 10886–10893).

Consumer: lane RC15's `ZInQ.Manuscript.RC.Central.upperBound_of_calibration`, with
`vReg x := v₂ ρ_Reg(x)` for the genuine regulator ratio at each address `x ≠ 0` (twist `h x`, final
companion `k`, `K = ℚ(√k)`), so its hypothesis `hReg` is removed. Discharger: lane RC19's
`ZInQ.Manuscript.RC.Height.regulator_inputs_sumDiff` (through `padicValRat_regulator_sumDiff`).

PROVED, from the remaining inputs: at each `x ≠ 0`, rank one (free generators `genA x`, `genB x`)
(`hρ` only names the rational value of the real ratio `Reg_B/Reg_A`, which enters the valuation
identity `hMilne`); and lane RC15's other inputs of
`upperBound_of_calibration` with their kinds (`hprim` ELLIOT, `hvN`, `hMilne` in valuation form,
`hsB`, `hvC`, `hΩ` GLUE, `hgB` ELLIOT, `hvL`, `h47`, `he`, `h39` = (3.9) + (3.4), `hs`). -/
theorem upperBound_of_calibration_sumDiff (C : CoordData b)
    (genA : ∀ x, ((qtwist E (h x)).baseChange K).toAffine.Point)
    (genB : ∀ x, ((qtwist E (h x)).baseChange ℚ).toAffine.Point ×
      ((qtwist E (h x * k)).baseChange ℚ).toAffine.Point)
    (hA : ∀ x, x ≠ 0 → IsFreeGenerator (genA x)) (hB : ∀ x, x ≠ 0 → IsFreeGenerator (genB x))
    (ρReg : (Fin b → ZMod 2) → ℚ)
    (hρ : ∀ x, x ≠ 0 → heightB E (h x) k (genB x) = (ρReg x : ℝ) * (genA x).canonicalHeight)
    (uprim0 e : (Fin b → ZMod 2) → ℚ_[2])
    (j vm vN ω gA sA gB sB sh shk vΩ vC T : (Fin b → ZMod 2) → ℤ) (vL G₀ CJ : ℤ)
    (hprimne : ∀ x, x ≠ 0 → uprim0 x ≠ 0)
    (hprim : ∀ x, x ≠ 0 → (uprim0 x).valuation = (j x + vL + vm x) + (j x + vL + vm x) +
      (diskContribution 1 (gA x) + diskContribution 2 (sA x) + diskContribution 3 (gA x)) +
      (2 * diskContribution 2 (vN x) + ω x * (2 * diskContribution 2 2)))
    (hvN : ∀ x, x ≠ 0 → vN x = vm x)
    (hMilne : ∀ x, x ≠ 0 →
      sA x - sB x = 2 * gA x - 2 * gB x + padicValRat 2 (ρReg x) + vΩ x + vC x)
    (hsB : ∀ x, x ≠ 0 → sB x = sh x + shk x) (hvC : ∀ x, x ≠ 0 → vC x = T x)
    (hΩ : ∀ x, x ≠ 0 → |vΩ x| ≤ 4)
    (hgB : ∀ x, x ≠ 0 → 0 ≤ gB x ∧ gB x ≤ G₀) (hvL : 0 ≤ vL)
    (h47 : ∀ x, x ≠ 0 → C.u x 0 = e x * uprim0 x)
    (he : ∀ x, x ≠ 0 → e x ≠ 0 ∧ (e x).valuation = 0)
    (h39 : ∀ x, x ≠ 0 → 2 * j x ≤ 4 * ω x + CJ)
    (hs : ∀ x, x ≠ 0 → 0 ≤ sh x ∧ 0 ≤ shk x ∧ 0 ≤ T x)
    (B : ℕ) (hB' : CJ + (2 * vL + 2 * G₀ + 5) ≤ B) : UpperBound C B :=
  ZInQ.Manuscript.RC.Central.upperBound_of_calibration C uprim0 e j vm vN ω gA sA gB sB sh shk
    (fun x => padicValRat 2 (ρReg x)) vΩ vC T vL G₀ CJ hprimne hprim hvN hMilne hsB hvC
    (fun x hx => padicValRat_regulator_sumDiff E (h x) k Dq (genA x) (genB x) (hA x hx) (hB x hx)
      (ρReg x) (hρ x hx))
    hΩ hgB hvL h47 he h39 hs B hB'

/-- **`UpperBound` from Milne's print on the genuine regulators at every address** (tex
4022–4030, 4044–4047, 4082–4113, 5730–5733, 10886–10893).

Consumer: lane RC15's `ZInQ.Manuscript.RC.Central.upperBound_of_calibration`, with the lengths read
off the orders (`g_A = v₂ t_A`, `s_A = v₂ |Ш(A)|`, `g_B = v₂ t_B`, `s_B = v₂ |Ш(B)|`,
`v_C = v₂(C_B/C_A)`, `v_Ω = v₂ ρ_Ω`, `v_Reg = v₂ ρ_Reg` at each address `x ≠ 0`). Removed: `hReg`,
and the valuation identity `hMilne` (now derived at each address from Milne's print by lane RC15's
`milne_valuation_form`, whose inputs `hRegA`, `hρReg` are discharged). Dischargers: lane RC19's
`ZInQ.Manuscript.RC.Height.regulator_inputs_sumDiff` (through `exists_regulator_ratio_sumDiff` and
`milne_valuation_form_sumDiff`): the rational regulator ratio `ρ_Reg(x) = Reg_B/Reg_A` at each
address is derived from the genuine regulators, it is not an input.

PROVED, from the remaining inputs: at each `x ≠ 0`, rank one (free generators), the nonvanishing
of the orders and periods, Milne's print on `Reg_A = ĥ(g_A)`, `Reg_B = ĥ_B(g_B)` (PRINT); and lane
RC15's other inputs (`hprimne`, `hprim` ELLIOT, `hvN`, `hsB`, `hvC` with Edixhoven's PRINT, `hΩ`
GLUE, `hgB` ELLIOT, `hvL`, `h47`, `he`, `h39` = (3.9) + (3.4), `hs`). The bound is lane RC15's
`B ≥ C_J + 2 v₂L + 2G₀ + 5`. -/
theorem upperBound_of_milne_sumDiff (C : CoordData b)
    (genA : ∀ x, ((qtwist E (h x)).baseChange K).toAffine.Point)
    (genB : ∀ x, ((qtwist E (h x)).baseChange ℚ).toAffine.Point ×
      ((qtwist E (h x * k)).baseChange ℚ).toAffine.Point)
    (hA : ∀ x, x ≠ 0 → IsFreeGenerator (genA x)) (hB : ∀ x, x ≠ 0 → IsFreeGenerator (genB x))
    (shaA shaB tA tB CA CB : (Fin b → ZMod 2) → ℕ) (ΩA : (Fin b → ZMod 2) → ℝ)
    (ρΩ : (Fin b → ZMod 2) → ℚ)
    (hnz : ∀ x, x ≠ 0 → shaA x ≠ 0 ∧ shaB x ≠ 0 ∧ tA x ≠ 0 ∧ tB x ≠ 0 ∧ CA x ≠ 0 ∧ CB x ≠ 0 ∧
      ΩA x ≠ 0 ∧ ρΩ x ≠ 0)
    (hMilne : ∀ x, x ≠ 0 → MilneIsogenyInvariance (shaA x) (shaB x) (tA x) (tA x) (tB x) (tB x)
      (CA x) (CB x) (genA x).canonicalHeight (heightB E (h x) k (genB x)) (ΩA x)
      ((ρΩ x : ℝ) * ΩA x))
    (uprim0 e : (Fin b → ZMod 2) → ℚ_[2])
    (j vm vN ω sh shk T : (Fin b → ZMod 2) → ℤ) (vL G₀ CJ : ℤ)
    (hprimne : ∀ x, x ≠ 0 → uprim0 x ≠ 0)
    (hprim : ∀ x, x ≠ 0 → (uprim0 x).valuation = (j x + vL + vm x) + (j x + vL + vm x) +
      (diskContribution 1 (padicValNat 2 (tA x)) + diskContribution 2 (padicValNat 2 (shaA x)) +
        diskContribution 3 (padicValNat 2 (tA x))) +
      (2 * diskContribution 2 (vN x) + ω x * (2 * diskContribution 2 2)))
    (hvN : ∀ x, x ≠ 0 → vN x = vm x)
    (hsB : ∀ x, x ≠ 0 → (padicValNat 2 (shaB x) : ℤ) = sh x + shk x)
    (hvC : ∀ x, x ≠ 0 → padicValRat 2 ((CB x : ℚ) / CA x) = T x)
    (hΩ : ∀ x, x ≠ 0 → |padicValRat 2 (ρΩ x)| ≤ 4)
    (hgB : ∀ x, x ≠ 0 → (padicValNat 2 (tB x) : ℤ) ≤ G₀) (hvL : 0 ≤ vL)
    (h47 : ∀ x, x ≠ 0 → C.u x 0 = e x * uprim0 x)
    (he : ∀ x, x ≠ 0 → e x ≠ 0 ∧ (e x).valuation = 0)
    (h39 : ∀ x, x ≠ 0 → 2 * j x ≤ 4 * ω x + CJ)
    (hs : ∀ x, x ≠ 0 → 0 ≤ sh x ∧ 0 ≤ shk x ∧ 0 ≤ T x)
    (B : ℕ) (hB' : CJ + (2 * vL + 2 * G₀ + 5) ≤ B) : UpperBound C B := by
  -- the rational regulator ratio at each address, derived from the genuine regulators
  have hex : ∀ x, ∃ ρ : ℚ, x ≠ 0 →
      heightB E (h x) k (genB x) = (ρ : ℝ) * (genA x).canonicalHeight := by
    intro x
    by_cases hx : x = 0
    · exact ⟨0, fun h0 => absurd hx h0⟩
    · obtain ⟨ρ, hρ, -⟩ :=
        exists_regulator_ratio_sumDiff E (h x) k Dq (genA x) (genB x) (hA x hx) (hB x hx)
      exact ⟨ρ, fun _ => hρ⟩
  choose ρReg hρ using hex
  have hid : ∀ x, x ≠ 0 →
      (padicValNat 2 (shaA x) : ℤ) - padicValNat 2 (shaB x) =
        2 * (padicValNat 2 (tA x) : ℤ) - 2 * padicValNat 2 (tB x) + padicValRat 2 (ρReg x) +
          padicValRat 2 (ρΩ x) + padicValRat 2 ((CB x : ℚ) / CA x) := by
    intro x hx
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hnz x hx
    exact (milne_valuation_form_sumDiff E (h x) k Dq (genA x) (genB x) (hA x hx) (hB x hx)
      (ρReg x) (hρ x hx) h1 h2 h3 h4 h5 h6 h7 h8 (hMilne x hx)).1
  exact upperBound_of_calibration_sumDiff E k Dq h C genA genB hA hB ρReg hρ uprim0 e j vm vN ω
    (fun x => (padicValNat 2 (tA x) : ℤ)) (fun x => (padicValNat 2 (shaA x) : ℤ))
    (fun x => (padicValNat 2 (tB x) : ℤ)) (fun x => (padicValNat 2 (shaB x) : ℤ)) sh shk
    (fun x => padicValRat 2 (ρΩ x)) (fun x => padicValRat 2 ((CB x : ℚ) / CA x)) T vL G₀ CJ
    hprimne hprim hvN hid hsB hvC hΩ (fun x hx => ⟨Int.natCast_nonneg _, hgB x hx⟩) hvL h47 he
    h39 hs B hB'

end Addresses

end ZInQ.Manuscript.RC.GlueSweep.Central
