import ZInQKernel.Contrib.CloudB3RC53.AppGEndpoints.FinalFamily
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.CentralCalibration

/-!
# Lane RC22 (glue sweep, central share): `UpperBound` with the input (3.9) + (3.4) discharged

The node `UpperBound C B` of the shared top layer (tex 5730–5733: `v₂ ũ_x(0) ≤ B` at `x ≠ 0`, "from
(3.9), (3.4), (4.6), (4.7)"). Lane RC15's `ZInQ.Manuscript.RC.Central.upperBound_node` (and
`upperBound_of_calibration`) takes the consequence of (3.9) and (3.4) as the hypothesis

  `h39 : ∀ x, x ≠ 0 → 2 * j x ≤ 4 * ω x + C_J`

(Proposition `ex:sec7-final-family`, tex 2704–2705: "By (3.4), now with fixed `k`,
`2 j_rc(h_x,k) ≤ 4ω(h_x) + C_J`"). The shared top layer has since proved exactly this step,
`AppGEndpoints.rcUpperCJ_proof` (App G, tex 10866–10870), from the two bounds of (3.9) at `h = h_x`
(`j_gen(h) ≤ ω(h) + C_o`, `v₂ L_*(hk) ≤ 2ω(h) + C_e`) and (3.4)
(`2 j_rc(h,k) − 2 j_gen(h) = v₂ L_*(hk) − v₂ L_*(h_*) + C_per + ε`, `|ε| ≤ 2`), with
`C_J = 2C_o + C_e − v₂ L_*(h_*) + (C_per + 2)`; these are the outputs of its final-family composite
`oddMinimumToFinalFamily_proof` (the two bounds at every nonzero address of the family) and of its
(3.4) node `GenusOdd.GenusLower34`. This file removes `h39` from lane RC15's consumers.

* `h39_of_finalFamily`: lane RC15's `h39` at the family `h_x`, from (3.9) and (3.4).
* `upperBound_node_of_finalFamily`: lane RC15's `upperBound_node` with `h39` removed.
* `upperBound_of_milne_finalFamily_sumDiff`: the node from Milne's print on the genuine regulators
  (`upperBound_of_milne_sumDiff`) with `h39` also removed.

Every theorem in this file is PROVED (from the stated remaining inputs).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.GlueSweep.Central

open ZInQ.Contrib.CloudB3RC53
open ZInQ.Contrib.CloudB3RC53.AppGEndpoints (omega rcUpperCJ_proof)
open ZInQ.Manuscript.RC.Height (heightB IsFreeGenerator QuadData)
open ZInQ.Manuscript.RC.Central (diskContribution MilneIsogenyInvariance)

/-- **`2 j_rc(h_x, k) ≤ 4ω(h_x) + C_J` at every nonzero address** (tex 2704–2705, 10866–10870).

Consumer: the hypothesis `h39` of lane RC15's `ZInQ.Manuscript.RC.Central.upperBound_node` and
`upperBound_of_calibration`, at `j x = j_rc(h_x, k)`, `ω x = ω(h_x)`. Discharger: the shared top
layer's `AppGEndpoints.rcUpperCJ_proof`.

PROVED, from the remaining inputs at every `x ≠ 0`: the two bounds of (3.9) (`hj`, `hL`) and (3.4)
(`h34`), in the shared top layer's generic form (`j_gen`, `j_rc`, `L_*` as functions; `ω` genuine);
`C_J = 2C_o + C_e − v₂ L_*(h_*) + (C_per + 2)`. -/
theorem h39_of_finalFamily {b : ℕ} (hfam : (Fin b → ZMod 2) → ℤ) (jgen : ℤ → ℤ)
    (jrc : ℤ → ℤ → ℤ) (Lstar : ℤ → ℚ) (k hstar Co Ce Cper : ℤ)
    (hj : ∀ x, x ≠ 0 → jgen (hfam x) ≤ (omega (hfam x) : ℤ) + Co)
    (hL : ∀ x, x ≠ 0 → padicValRat 2 (Lstar (hfam x * k)) ≤ 2 * (omega (hfam x) : ℤ) + Ce)
    (h34 : ∀ x, x ≠ 0 → ∃ ε : ℤ, |ε| ≤ 2 ∧ 2 * jrc (hfam x) k - 2 * jgen (hfam x) =
      padicValRat 2 (Lstar (hfam x * k)) - padicValRat 2 (Lstar hstar) + Cper + ε) :
    ∀ x, x ≠ 0 → 2 * jrc (hfam x) k ≤
      4 * (omega (hfam x) : ℤ) + (2 * Co + Ce - padicValRat 2 (Lstar hstar) + (Cper + 2)) :=
  fun x hx => rcUpperCJ_proof jgen jrc Lstar (hfam x) k hstar Co Ce Cper (hj x hx) (hL x hx)
    (h34 x hx)

/-- **`UpperBound` from (F.8) and the final family, `h39` discharged** (tex 2704–2705,
5730–5733, 10866–10893).

Consumer: lane RC15's `ZInQ.Manuscript.RC.Central.upperBound_node`, at `j x = j_rc(h_x, k)` and
`ω x = ω(h_x)` for the final family `h_x = hfam x`; its hypothesis `h39` is removed. Discharger:
the shared top layer's `AppGEndpoints.rcUpperCJ_proof` (through `h39_of_finalFamily`).

PROVED, from the remaining inputs: lane RC15's `hF8` ((F.8): (4.6) transported by (4.7)), `hε`,
`hs`; and at every `x ≠ 0` the two bounds of (3.9) and (3.4) (`hj`, `hL`, `h34`); for every
`B ≥ C_J + C_cal` with `C_J = 2C_o + C_e − v₂ L_*(h_*) + (C_per + 2)`. -/
theorem upperBound_node_of_finalFamily {b : ℕ} (C : CoordData b) (hfam : (Fin b → ZMod 2) → ℤ)
    (jgen : ℤ → ℤ) (jrc : ℤ → ℤ → ℤ) (Lstar : ℤ → ℚ) (k hstar Co Ce Cper : ℤ)
    (sh shk T ε : (Fin b → ZMod 2) → ℤ) (Ccal : ℤ)
    (hF8 : ∀ x, x ≠ 0 → C.u x 0 ≠ 0 ∧ (C.u x 0).valuation =
      2 * jrc (hfam x) k - 4 * (omega (hfam x) : ℤ) - sh x - shk x - T x + ε x)
    (hj : ∀ x, x ≠ 0 → jgen (hfam x) ≤ (omega (hfam x) : ℤ) + Co)
    (hL : ∀ x, x ≠ 0 → padicValRat 2 (Lstar (hfam x * k)) ≤ 2 * (omega (hfam x) : ℤ) + Ce)
    (h34 : ∀ x, x ≠ 0 → ∃ ε' : ℤ, |ε'| ≤ 2 ∧ 2 * jrc (hfam x) k - 2 * jgen (hfam x) =
      padicValRat 2 (Lstar (hfam x * k)) - padicValRat 2 (Lstar hstar) + Cper + ε')
    (hε : ∀ x, x ≠ 0 → |ε x| ≤ Ccal) (hs : ∀ x, x ≠ 0 → 0 ≤ sh x ∧ 0 ≤ shk x ∧ 0 ≤ T x)
    (B : ℕ) (hB : (2 * Co + Ce - padicValRat 2 (Lstar hstar) + (Cper + 2)) + Ccal ≤ B) :
    UpperBound C B :=
  ZInQ.Manuscript.RC.Central.upperBound_node C (fun x => jrc (hfam x) k)
    (fun x => (omega (hfam x) : ℤ)) sh shk T ε
    (2 * Co + Ce - padicValRat 2 (Lstar hstar) + (Cper + 2)) Ccal hF8
    (h39_of_finalFamily hfam jgen jrc Lstar k hstar Co Ce Cper hj hL h34) hε hs B hB

/-- **`UpperBound` with the regulator inputs and (3.9) + (3.4) discharged** (tex 2704–2705,
4022–4030, 4044–4047, 4082–4113, 5730–5733, 10866–10893).

Consumer: lane RC15's `ZInQ.Manuscript.RC.Central.upperBound_of_calibration`, at the final family
`h_x = hfam x` (`j x = j_rc(h_x, k)`, `ω x = ω(h_x)`, twists `E^{(h_x)}`, `E^{(h_x k)}`,
`K = ℚ(√k)`), with the lengths read off the orders as in `upperBound_of_milne_sumDiff`. Removed:
`hReg`, the valuation identity `hMilne` (derived from Milne's print), and `h39`. Dischargers: lane
RC19's `ZInQ.Manuscript.RC.Height.regulator_inputs_sumDiff` (through `upperBound_of_milne_sumDiff`)
and the shared top layer's `AppGEndpoints.rcUpperCJ_proof` (through `h39_of_finalFamily`).

PROVED, from the remaining inputs: at every `x ≠ 0`, rank one (free generators), the rational
regulator ratio `hρ`, the nonvanishing of the orders and periods, Milne's print on the genuine
regulators (PRINT), lane RC15's `hprimne`, `hprim` (ELLIOT), `hvN`, `hsB`, `hvC` (with Edixhoven's
PRINT), `hΩ` (GLUE real change of variables), `hgB` (ELLIOT), `hvL`, `h47`, `he`, `hs`, and the two
bounds of (3.9) with (3.4) (`hj`, `hL`, `h34`). The bound: `B ≥ C_J + 2 v₂L + 2G₀ + 5` with
`C_J = 2C_o + C_e − v₂ L_*(h_*) + (C_per + 2)`. -/
theorem upperBound_of_milne_finalFamily_sumDiff {K : Type*} [Field K] [NumberField K]
    [DecidableEq K] [Algebra.IsQuadraticExtension ℚ K] (E : WeierstrassCurve ℚ) (k : ℤ)
    (Dq : QuadData K (k : ℚ)) {b : ℕ} (hfam : (Fin b → ZMod 2) → ℤ)
    [∀ x, (qtwist E (hfam x : ℚ)).IsElliptic] [∀ x, (qtwist E ((hfam x : ℚ) * (k : ℚ))).IsElliptic]
    (C : CoordData b)
    (genA : ∀ x, ((qtwist E (hfam x : ℚ)).baseChange K).toAffine.Point)
    (genB : ∀ x, ((qtwist E (hfam x : ℚ)).baseChange ℚ).toAffine.Point ×
      ((qtwist E ((hfam x : ℚ) * (k : ℚ))).baseChange ℚ).toAffine.Point)
    (hA : ∀ x, x ≠ 0 → IsFreeGenerator (genA x)) (hB : ∀ x, x ≠ 0 → IsFreeGenerator (genB x))
    (ρReg : (Fin b → ZMod 2) → ℚ)
    (hρ : ∀ x, x ≠ 0 →
      heightB E (hfam x : ℚ) (k : ℚ) (genB x) = (ρReg x : ℝ) * (genA x).canonicalHeight)
    (shaA shaB tA tB CA CB : (Fin b → ZMod 2) → ℕ) (ΩA : (Fin b → ZMod 2) → ℝ)
    (ρΩ : (Fin b → ZMod 2) → ℚ)
    (hnz : ∀ x, x ≠ 0 → shaA x ≠ 0 ∧ shaB x ≠ 0 ∧ tA x ≠ 0 ∧ tB x ≠ 0 ∧ CA x ≠ 0 ∧ CB x ≠ 0 ∧
      ΩA x ≠ 0 ∧ ρΩ x ≠ 0)
    (hMilne : ∀ x, x ≠ 0 → MilneIsogenyInvariance (shaA x) (shaB x) (tA x) (tA x) (tB x) (tB x)
      (CA x) (CB x) (genA x).canonicalHeight (heightB E (hfam x : ℚ) (k : ℚ) (genB x)) (ΩA x)
      ((ρΩ x : ℝ) * ΩA x))
    (jgen : ℤ → ℤ) (jrc : ℤ → ℤ → ℤ) (Lstar : ℤ → ℚ) (hstar Co Ce Cper : ℤ)
    (uprim0 e : (Fin b → ZMod 2) → ℚ_[2])
    (vm vN sh shk T : (Fin b → ZMod 2) → ℤ) (vL G₀ : ℤ)
    (hprimne : ∀ x, x ≠ 0 → uprim0 x ≠ 0)
    (hprim : ∀ x, x ≠ 0 → (uprim0 x).valuation =
      (jrc (hfam x) k + vL + vm x) + (jrc (hfam x) k + vL + vm x) +
      (diskContribution 1 (padicValNat 2 (tA x)) + diskContribution 2 (padicValNat 2 (shaA x)) +
        diskContribution 3 (padicValNat 2 (tA x))) +
      (2 * diskContribution 2 (vN x) +
        (omega (hfam x) : ℤ) * (2 * diskContribution 2 2)))
    (hvN : ∀ x, x ≠ 0 → vN x = vm x)
    (hsB : ∀ x, x ≠ 0 → (padicValNat 2 (shaB x) : ℤ) = sh x + shk x)
    (hvC : ∀ x, x ≠ 0 → padicValRat 2 ((CB x : ℚ) / CA x) = T x)
    (hΩ : ∀ x, x ≠ 0 → |padicValRat 2 (ρΩ x)| ≤ 4)
    (hgB : ∀ x, x ≠ 0 → (padicValNat 2 (tB x) : ℤ) ≤ G₀) (hvL : 0 ≤ vL)
    (h47 : ∀ x, x ≠ 0 → C.u x 0 = e x * uprim0 x)
    (he : ∀ x, x ≠ 0 → e x ≠ 0 ∧ (e x).valuation = 0)
    (hj : ∀ x, x ≠ 0 → jgen (hfam x) ≤ (omega (hfam x) : ℤ) + Co)
    (hL : ∀ x, x ≠ 0 → padicValRat 2 (Lstar (hfam x * k)) ≤ 2 * (omega (hfam x) : ℤ) + Ce)
    (h34 : ∀ x, x ≠ 0 → ∃ ε : ℤ, |ε| ≤ 2 ∧ 2 * jrc (hfam x) k - 2 * jgen (hfam x) =
      padicValRat 2 (Lstar (hfam x * k)) - padicValRat 2 (Lstar hstar) + Cper + ε)
    (hs : ∀ x, x ≠ 0 → 0 ≤ sh x ∧ 0 ≤ shk x ∧ 0 ≤ T x)
    (B : ℕ) (hB' : (2 * Co + Ce - padicValRat 2 (Lstar hstar) + (Cper + 2)) +
      (2 * vL + 2 * G₀ + 5) ≤ B) : UpperBound C B :=
  upperBound_of_milne_sumDiff E (k : ℚ) Dq (fun x => (hfam x : ℚ)) C genA genB hA hB ρReg hρ
    shaA shaB tA tB CA CB ΩA ρΩ hnz hMilne uprim0 e (fun x => jrc (hfam x) k) vm vN
    (fun x => (omega (hfam x) : ℤ)) sh shk T vL G₀
    (2 * Co + Ce - padicValRat 2 (Lstar hstar) + (Cper + 2)) hprimne hprim hvN hsB hvC hΩ hgB hvL
    h47 he (h39_of_finalFamily hfam jgen jrc Lstar k hstar Co Ce Cper hj hL h34) hs B hB'

end ZInQ.Manuscript.RC.GlueSweep.Central
