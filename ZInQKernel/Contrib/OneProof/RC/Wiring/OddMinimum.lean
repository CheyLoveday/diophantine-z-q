import ZInQKernel.Contrib.OneProof.RC.Wiring.FinalFamily

/-!
# Theorem 5.3, Lane RC0 round 2: the attained odd minimum `δ_o` (batch 3's App G)

`exists_oddMinimum` (PROVED from batch 3's `genusLowerF4_proof`, `coarseF5_proof` and
`oddMinimumF6_proof`): the depth set of the odd coefficients has a least element, from (O.8), the
inputs of (F.4), the prepared-filter GLUE and the fixed visible witness `D_w` (tex 2460–2500, (3.7)).
The skeleton's `δ_o` is then chosen as this least element (`Leaves.lean`), so the requested field
`odd_minimum` (`OddMinimumTarget`) is a theorem, not a hypothesis.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 Filter Topology

attribute [local instance] Nat.fact_prime_two

variable {ℓ : ℕ} (W : WData ℓ)

/-- **The fixed visible witness** (tex 2460–2500, (3.7) and its use at 2536–2546; ELLIOT, with
Cai–Shu–Tian Thm 1.1 (PRINT) for the nontorsion of `P_{D_w}^{gen}` and finite Chebotarev; owner
batch 3 GenusOdd / lane RC12 (detector)): one admissible `D_w` whose coefficient has one fixed
valuation `c_w < M_θ` on a set of stages in the ultrafilter. -/
def WitnessLeaf : Prop :=
  ∃ Dw c : ℤ, ∀ᶠ θ in (W.stages : Filter ℕ), W.admissible θ Dw ∧
    vZ (W.aθ θ Dw) = (c : WithTop ℤ) ∧ (c : WithTop ℤ) < W.Mθ θ

/-- **The odd minimum is attained** (PROVED from batch 3's (F.4), (F.5), (F.6)). -/
theorem exists_oddMinimum {A : ℕ} {CE CR Cper Cdet : ℤ} (h33 : F3At W A CE)
    (h34 : Gz34CompAt W Cper) (h35 : Eq35At W A CR) (hvis : VisAt W Cdet)
    (hPrep : PreparedGlue W) (hwit : WitnessLeaf W) :
    ∃ δ : ℤ, IsLeast
      (AppGEndpoints.DepthSet W.stages W.Mθ (fun θ Dd => vZ (W.aθ θ Dd)) W.admissible) δ := by
  set Cgen : ℤ := 2 * (A : ℤ) + CR + CE - padicValRat 2 (W.Lstar W.hstar) + (Cper + 2)
  have hF4 : ∀ θ Dd, W.admissible θ Dd → AnalyticRank (Etw ℓ Dd) 1 →
      2 * (AppGEndpoints.omega Dd : ℤ) + (shaLength (Etw ℓ Dd) : ℤ) - Cgen ≤ 2 * W.jgen Dd :=
    fun θ Dd hD hz => AppGEndpoints.genusLowerF4_proof W.prepared
      (fun h => AnalyticRank (Etw ℓ h) 1) W.IsRoughCompanion W.Lstar W.jgen W.jrc
      (fun h => shaLength (Etw ℓ h)) W.hstar A CR CE Cper
      (fun h hp hz => by
        obtain ⟨k', hk, hω, hL, hv⟩ := h33 h hp hz
        exact ⟨k', hk, hω, hL, by simpa [sFun, omega_eq_appG] using hv⟩)
      h34
      (fun h k' hp hz hk hω => by simpa [sFun, omega_eq_appG] using h35 h k' hp hz hk hω)
      Dd (hPrep θ Dd hD) hz
  have hF5 : ∀ θ Dd, W.admissible θ Dd →
      AppGEndpoints.QLe (min (W.Mθ θ : ℚ) (AppGEndpoints.omega Dd - ((Cgen : ℚ) / 2 + Cdet)))
        (vZ (W.aθ θ Dd)) :=
    fun θ Dd hD => AppGEndpoints.coarseF5_proof (W.admissible θ)
      (fun h => AnalyticRank (Etw ℓ h) 1) W.jgen (fun h => shaLength (Etw ℓ h))
      (fun D => vZ (W.aθ θ D)) (W.Mθ θ) Cdet Cgen (fun D' hD' hlt => hvis θ D' hD' hlt)
      (fun D' hD' hz => hF4 θ D' hD' hz) Dd hD
  obtain ⟨δ, hδ, -⟩ := AppGEndpoints.oddMinimumF6_proof W.stages W.Mθ
    (fun θ Dd => vZ (W.aθ θ Dd)) W.admissible ((Cgen : ℚ) / 2 + Cdet) hF5 hwit
  exact ⟨δ, hδ⟩

end ZInQ.Manuscript.RC.Wiring
