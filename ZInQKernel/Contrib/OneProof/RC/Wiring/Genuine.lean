import ZInQKernel.Contrib.OneProof.RC.Wiring.Uniform
import ZInQKernel.Contrib.OneProof.RC.Rings.OValuation

/-!
# Theorem 5.3, Lane RC0 round 2: (3.5) over the genuine `𝒪` (lane RC20)

`eq35Inputs_of_genuine` (PROVED): the inputs of (3.5) (`Eq35Inputs`, lane RC16's
`exLimitsUniformLowerBound`) with the valuation identification `ValuationOfO` discharged over the
genuine outer ring: `K = Frac 𝒪`, `v = v_𝒪`, `ι : Frac Λ → Frac 𝒪` (lane RC20's
`valuationOfO_genuine`, tex 3727–3730, 4914–4920). What remains is `Eq35InputsGenuine`: the
primitive coordinates at the companion pairs, their height-one regularity processes, (4.6) at the
companion pairs and the outer switching processes over `v_𝒪`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53
  ZInQ.Manuscript.RC.Uniform ZInQ.Manuscript.RC.Rings ZInQ.Manuscript.RC.Determinant Filter Topology

variable {ℓ : ℕ} (W : WData ℓ)

/-- **The inputs of (3.5) over the genuine `𝒪`** (the body of `Eq35Inputs` at `K = Frac 𝒪`,
`v = v_𝒪`, `ι = ι_𝒪`; tex 2441–2446, 3987–4047, 4909–5202; ELLIOT; owners RC16, RC15, RC6,
batch 3). -/
def Eq35InputsGenuine : Prop :=
  ∃ (uprim : ℤ → ℤ → FractionRing Lambda) (C₀ : ℤ),
    (∀ h k' : ℤ, W.prepared h → AnalyticRank (Etw ℓ h) 1 → W.IsRoughCompanion h k' →
      RegularityInputs (uprim h k')) ∧
    (∀ h k' : ℤ, W.prepared h → AnalyticRank (Etw ℓ h) 1 → W.IsRoughCompanion h k' →
      ∀ uh : LambdaHalf, lambdaHalfToFrac uh = uprim h k' →
        ∃ (t : ℕ → ℕ) (err : ℤ), (∀ p, t p ≤ 2) ∧ |err| ≤ C₀ ∧
          v2 (centralSpecialization uh) =
            ((2 * W.jrc h k' - 4 * (omega h : ℤ) - sFun ℓ h - sFun ℓ (h * k') -
              ∑ p ∈ k'.natAbs.primeFactors, (t p : ℤ) + err : ℤ) : WithTop ℤ)) ∧
    (∀ A : ℕ, ∀ inst : ℕ → CompanionPair W A,
      ∃ (P : OuterSwitchProcessPF vO (Filter.hyperfilter ℕ)) (S₀ : P.Stage),
        ∀ᶠ j in ((Filter.hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ),
          vO (P.coord S₀ j) = vO (iotaO (uprim (inst j).h (inst j).k)))

/-- **`ValuationOfO` discharged** (PROVED from lane RC20's `valuationOfO_genuine`). -/
theorem eq35Inputs_of_genuine (h : Eq35InputsGenuine W) : Eq35Inputs W :=
  ⟨FractionRing OO, inferInstance, vO, iotaO, valuationOfO_genuine, h⟩

end ZInQ.Manuscript.RC.Wiring
