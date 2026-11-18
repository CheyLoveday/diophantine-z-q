import ZInQKernel.Contrib.OneProof.RC.Wiring.FinalFamily
import ZInQKernel.Contrib.OneProof.RC.Wiring.Odd

/-!
# Theorem 5.3, Lane RC0 round 2: the attained odd minimum `δ_o` (batch 3's App G)

`exists_oddMinimum` (PROVED from batch 3's `genusLowerF4_proof`, `coarseF5_proof` and
`oddMinimumF6_proof`): the depth set of the odd coefficients has a least element, from (O.8), the
inputs of (F.4), the prepared-filter GLUE and the fixed visible witness `D_w` (tex 2460–2500, (3.7);
the minimum: App G 10151–10209, §7 2538–2546).
The skeleton's `δ_o` is then chosen as this least element (`Leaves.lean`), so the requested field
`odd_minimum` (`OddMinimumTarget`) is a theorem, not a hypothesis.

`coarseF5_of_leaves` (PROVED) exposes the coarse bound (F.5) computed from the same inputs, and
`oddStageSource_of_leaves` (PROVED, lane RC27) feeds it, with `OddMinimumTarget`, to the bridge
`oddStageSource_of_data`: for every finite operator budget the odd stages are valid
(`Odd.OddStageSource`, the depth inequalities of App G used by (O.9)–(O.11)) eventually along the
ultrafilter.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 Filter Topology

attribute [local instance] Nat.fact_prime_two

variable {ℓ : ℕ} (W : WData ℓ)

/-- **The fixed visible witness** ((3.7), tex 2460–2498, 2534–2536; (O.2), App F 8225–8405; the
valuation, App F 9391–9403; ELLIOT, with PRINT Bump–Friedberg–Hoffstein (Invent. Math. 102 (1990),
pp. 543–544, clause (i)) for `L'(E^{(D_w)},1) ≠ 0`, PRINT Cai–Shu–Tian Thm 1.1 for the nontorsion of
`P_{D_w}^{gen}`, PRINT Serre's open image for the Kummer image, and GLUE finite Chebotarev; owner
batch 3 GenusOdd / lane RC12 (detector)): one admissible `D_w` whose coefficient has one fixed
valuation `c = c_θ + c_w = 9 + ω(N) + c_w < M_θ` on a set of stages in the ultrafilter (the text
gives it at every stage with `M_θ > c`). BFH supplies the simple-zero parameter before the height
and detector construction. `D_w` must be prime to `S`, so the final `k` is chosen prime to `D_w`. -/
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

/-- **(F.5) over the data from the leaves** (PROVED from batch 3's `genusLowerF4_proof` and
`coarseF5_proof`; App G, tex 10171–10187; the computation inside `exists_oddMinimum`):
`v₂ a_M(D) ≥ min{M, ω(D) − C_coarse}` at every admissible `D` of every stage, for one constant
`C_coarse = C_gen/2 + C_det`. -/
theorem coarseF5_of_leaves {A : ℕ} {CE CR Cper Cdet : ℤ} (h33 : F3At W A CE)
    (h34 : Gz34CompAt W Cper) (h35 : Eq35At W A CR) (hvis : VisAt W Cdet)
    (hPrep : PreparedGlue W) :
    ∃ Ccoarse : ℚ, ∀ θ Dd, W.admissible θ Dd →
      AppGEndpoints.QLe (min (W.Mθ θ : ℚ) (AppGEndpoints.omega Dd - Ccoarse))
        (vZ (W.aθ θ Dd)) := by
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
  exact ⟨(Cgen : ℚ) / 2 + Cdet, fun θ Dd hD => AppGEndpoints.coarseF5_proof (W.admissible θ)
    (fun h => AnalyticRank (Etw ℓ h) 1) W.jgen (fun h => shaLength (Etw ℓ h))
    (fun D => vZ (W.aθ θ D)) (W.Mθ θ) Cdet Cgen (fun D' hD' hlt => hvis θ D' hD' hlt)
    (fun D' hD' hz => hF4 θ D' hD' hz) Dd hD⟩

/-- **PROVED (lane RC27; App G, Proposition `ex:app-odd-minimum`, tex 10171–10227): the valid odd
stages from the leaves.** The inputs of (F.4)–(F.5) used by `exists_oddMinimum` ((F.3), (3.4) at the
companions, (3.5), (O.8), the prepared-filter GLUE), `δ_o` the attained minimum
(`OddMinimumTarget`), the advancing stages, and, for the theta stages, their cores
(`Odd.OddStageCore`, ELLIOT) and the phase relation with `W.aθ` (tex 2538, (3.8)): for every finite
operator budget `W_U` and `R ≥ 2`, the stages are valid (`Odd.OddStageSource`) on a set in the
ultrafilter. -/
theorem oddStageSource_of_leaves {A : ℕ} {CE CR Cper Cdet : ℤ} (h33 : F3At W A CE)
    (h34 : Gz34CompAt W Cper) (h35 : Eq35At W A CR) (hvis : VisAt W Cdet)
    (hPrep : PreparedGlue W) (hmin : OddMinimumTarget W)
    (hM : Tendsto W.Mθ (W.stages : Filter ℕ) atTop) (O : Type*) [CommRing O]
    (η : (θ : ℕ) → ℕ → Odd.StageRing O (W.Mθ θ)) (Good : ℕ → ℕ → Prop) (ap : ℕ → ℤ)
    (a : (θ : ℕ) → ℕ → Odd.StageRing O (W.Mθ θ))
    (hcore : ∀ θ, Odd.OddStageCore O (W.Mθ θ) (η θ) (Good θ) (fun n => W.admissible θ n) ap (a θ))
    (ζ : ℕ → ℕ → O)
    (hphase : ∀ θ (Dn : ℕ), Squarefree Dn → W.admissible θ Dn →
      a θ Dn = Ideal.Quotient.mk (Ideal.span {(2 : O) ^ W.Mθ θ}) (ζ θ Dn * (W.aθ θ Dn : O)))
    (WU R : ℕ) (hR : 2 ≤ R) :
    ∀ᶠ θ in (W.stages : Filter ℕ), Odd.OddStageSource O WU R (W.Mθ θ) W.δo (η θ) (Good θ)
      (fun n => W.admissible θ n) ap (a θ) := by
  obtain ⟨Cc, hF5⟩ := coarseF5_of_leaves W h33 h34 h35 hvis hPrep
  exact oddStageSource_of_data W.toRCData O η Good ap a hcore ζ hphase hM Cc hF5 hmin WU R hR

end ZInQ.Manuscript.RC.Wiring
