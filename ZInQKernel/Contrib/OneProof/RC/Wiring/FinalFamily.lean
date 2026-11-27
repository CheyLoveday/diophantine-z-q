import ZInQKernel.Contrib.OneProof.RC.Wiring.Data

/-!
# Theorem 5.3, Lane RC0 round 2: the final family (3.9) is a theorem (batch 3's App G)

`finalFamilyTarget_of` (PROVED from batch 3's `AppGEndpoints.finalFamilyField_proof`): the step
`RCSteps.final_family` ((3.9), Proposition `ex:sec7-final-family`, tex 2674–2712; App G
`ex:app-odd-minimum` 10151–10256 and `ex:app-final-family` 10792–10861) from
* (O.8) (`VisibilityTarget`) and the advancing stages,
* the inputs of (F.4): the rough companion with (F.3) (`F3Target`), (3.4) at the companions
  (`Gz34Target`, first part) and (3.5) (`Eq35Target`),
* the GLUE that admissible theta parameters lie in the prepared filter (`PreparedGlue`),
* `δ_o` is the attained odd minimum (`OddMinimumTarget`),
* in Branch 2 the address input at `δ_o` (`AddressLeaf`), for the constants supplied by the
  inputs above.
The constants are those of batch 3's proof: `C_o = δ_o + C_det`, `C_e = C_{e,final}`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 Filter Topology

attribute [local instance] Nat.fact_prime_two

/-- The skeleton's `ω` is batch 3's (same body; PROVED). -/
theorem omega_eq_appG (n : ℤ) : omega n = AppGEndpoints.omega n := rfl

variable {ℓ : ℕ} (W : WData ℓ)

/-- (F.3) at given constants `A`, `C_E` (the body of `F3Target`). -/
def F3At (A : ℕ) (CE : ℤ) : Prop :=
  ∀ h : ℤ, W.prepared h → AnalyticRank (Etw ℓ h) 1 →
    ∃ k' : ℤ, W.IsRoughCompanion h k' ∧ (omega k' : ℤ) ≤ A ∧ W.Lstar (h * k') ≠ 0 ∧
      padicValRat 2 (W.Lstar (h * k')) ≤ 2 * omega h + 2 * omega k' + sFun ℓ (h * k') + CE

/-- (3.4) at the rough companions at a given period constant (the first part of `Gz34Target`). -/
def Gz34CompAt (Cper : ℤ) : Prop :=
  ∀ h k' : ℤ, W.prepared h → AnalyticRank (Etw ℓ h) 1 → W.IsRoughCompanion h k' →
    ∃ ε : ℤ, |ε| ≤ 2 ∧ 2 * W.jrc h k' - 2 * W.jgen h =
      padicValRat 2 (W.Lstar (h * k')) - padicValRat 2 (W.Lstar W.hstar) + Cper + ε

/-- (3.5) at given `A` and `C_R` (the body of `Eq35Target`). -/
def Eq35At (A : ℕ) (CR : ℤ) : Prop :=
  ∀ h k' : ℤ, W.prepared h → AnalyticRank (Etw ℓ h) 1 →
    W.IsRoughCompanion h k' → (omega k' : ℤ) ≤ A →
      4 * (omega h : ℤ) + sFun ℓ h + sFun ℓ (h * k') - CR ≤ 2 * W.jrc h k'

/-- (O.8) at a given constant `C_det` (the body of `VisibilityTarget`). -/
def VisAt (Cdet : ℤ) : Prop :=
  ∀ θ : ℕ, ∀ Dd : ℤ, W.admissible θ Dd → vZ (W.aθ θ Dd) < W.Mθ θ →
    AnalyticRank (Etw ℓ Dd) 1 ∧ (W.jgen Dd : WithTop ℤ) ≤ vZ (W.aθ θ Dd) + Cdet

/-- **The address input, for every choice of the constants supplied by the other inputs** (App G
`ex:app-odd-stabilization`, `ex:app-simultaneous-address`, `ex:app-final-family`, tex
10508–10860; ELLIOT; lane RC2 with lane RC3's K-split seed; batch 3 AppGEndpoints). The address
construction uses the coarse bound (F.5), which holds for any constants `A, C_E, C_per, C_R, C_det`
satisfying (F.3), (3.4), (3.5) and (O.8); so the input is required for exactly those constants. -/
def AddressLeaf : Prop :=
  ∀ (A : ℕ) (CE CR Cper Cdet : ℤ), F3At W A CE → Gz34CompAt W Cper → Eq35At W A CR →
    VisAt W Cdet → AddressTarget W A CR CE Cper Cdet

/-- **The final family (3.9)** (PROVED from batch 3's `finalFamilyField_proof`). -/
theorem finalFamilyTarget_of (hvis : VisibilityTarget W.toRCData)
    (hM : Tendsto W.Mθ (W.stages : Filter ℕ) atTop) (hF3 : F3Target W) (hGz : Gz34Target W)
    (h35 : Eq35Target W) (hPrep : PreparedGlue W) (hmin : OddMinimumTarget W)
    (hAddr : AddressLeaf W) : FinalFamilyTarget W.toRCData := by
  intro hU
  obtain ⟨Cdet, hCdet⟩ := hvis
  obtain ⟨A, CE, h33⟩ := hF3
  obtain ⟨Cper, h34, -⟩ := hGz
  obtain ⟨CR, h35A⟩ := h35 A
  have hAd := hAddr A CE CR Cper Cdet h33 h34 h35A hCdet
  obtain ⟨Co, Ce, b₀, hfam⟩ := AppGEndpoints.finalFamilyField_proof W.prepared
    (fun h => AnalyticRank (Etw ℓ h) 1) W.Lstar W.jgen W.jrc W.hstar W.stages W.Mθ
    (fun θ Dd => vZ (W.aθ θ Dd)) W.admissible W.δo W.kfin W.IsRoughCompanion
    (fun h => shaLength (Etw ℓ h)) A CR CE Cper Cdet Family Family.b Family.h
    (Family.Admissible W.S W.kfin) hCdet hM
    (fun h hp hz => by
      obtain ⟨k', hk, hω, hL, hv⟩ := h33 h hp hz
      exact ⟨k', hk, hω, hL, by simpa [sFun, omega_eq_appG] using hv⟩)
    h34
    (fun h k' hp hz hk hω => by simpa [sFun, omega_eq_appG] using h35A h k' hp hz hk hω)
    hPrep hmin (fun hne => hAd hne) hU
  exact ⟨Co, Ce, b₀, fun b hb => by
    obtain ⟨F, hFb, hadm, hx⟩ := hfam b hb
    exact ⟨F, hFb, hadm, fun x hx0 => hx x hx0⟩⟩

end ZInQ.Manuscript.RC.Wiring
