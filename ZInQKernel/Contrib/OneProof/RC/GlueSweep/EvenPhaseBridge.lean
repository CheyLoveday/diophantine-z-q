import ZInQKernel.Contrib.OneProof.RC.Even.EvenPhase
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.EvenLowerBound

/-!
# Lane RC22 (glue sweep), even share: Proposition `ex:app-even-phase` without the continuation
# and lower-bound hypotheses

Lane RC11's file `EvenPhase.lean` proves (E.10) (`E10_of_waldspurgerCor2`, tex 7968–8028), (E.11)
(`EvenPhaseData.E11`, tex 8136–8142) and the attained minimum of `v₂ a(D) − ω(D)`
(`EvenPhaseData.minimum`, tex 7807–7810, 8193–8199) with hypotheses that the tree discharges:

* the entire continuations `hF₀`, `hF` (in (E.10)) and `hcont` (in (E.11) and the minimum): from
  the shared printed leaf `PoleS12.BCDTThmA` and lane RC8's GLUE `HasseConvergence`
  (`twistContinuation_of_bcdt`, `EvenLowerBound.lean`);
* the lower bound `h9 : EvenLowerBound E L` (in the minimum): from (3.2), `Prints` and
  `HasseConvergence` (`evenLowerBound_of_evenScalar32_of_prints`), or from Appendix E's outputs
  (`evenLowerBound_of_appE_of_prints`).

Waldspurger's Corollaire 2 (`WaldspurgerCor2`, lane RC8's PRINT) and the ELLIOT data
`EvenPhaseData` remain. All results here are `PROVED`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.GlueSweep.Even

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 ZInQ.Manuscript.RC.PrintsAnalytic

/-- **(E.10) with the continuations discharged** (tex 7968–8028; PROVED from lane RC8's PRINT
`WaldspurgerCor2`, the shared printed leaf `PoleS12.BCDTThmA` and lane RC8's GLUE
`HasseConvergence`). Consumer: lane RC11's `E10_of_waldspurgerCor2` (hypotheses `hF₀`, `hF` and
the functions `F₀`, `F` removed; the conclusion does not mention them). Discharger:
`twistContinuation_of_bcdt` at `σD₀` and `σD`, which are nonzero (`sigma_mul_ne_zero`). -/
theorem E10_of_waldspurgerCor2_of_bcdt (hW : WaldspurgerCor2) (hB : PoleS12.BCDTThmA)
    (hH : HasseConvergence) {E : WeierstrassCurve ℚ} [hE : E.IsElliptic]
    (L : ZInQ.Manuscript.RC.Even.CentralNormalization E) {N : ℕ} (hN : 4 ∣ N)
    (ψ η : DirichletCharacter ℂ N) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    (hψη : ∀ n : ℕ, n.Coprime N → η n = ψ n * (kronecker (-σ) n : ℂ))
    {g : UpperHalfPlane → ℂ} (hg : IsInWaldspurgerEigenspace E N ψ η g) {D₀ D : ℕ}
    (hD₀ : 0 < D₀) (hD : 0 < D) (hsq₀ : Squarefree D₀) (hsq : Squarefree D)
    (hc₀ : D₀.Coprime N) (hc : D.Coprime N) (hcl : SameUnitClassesAtLevel N D D₀)
    (ha₀ : hiwCoeff g D₀ ≠ 0) (hL₀ : L.Lstar (σ * D₀) ≠ 0) :
    (hiwCoeff g D / hiwCoeff g D₀) ^ 2 =
      ψ D * (ψ D₀)⁻¹ * (((L.Lstar (σ * D) / L.Lstar (σ * D₀) : ℚ) : ℝ) : ℂ) := by
  obtain ⟨F₀, hF₀⟩ := twistContinuation_of_bcdt hB hH E (σ * D₀)
    (ZInQ.Manuscript.RC.Even.sigma_mul_ne_zero hσ hD₀)
  obtain ⟨F, hF⟩ := twistContinuation_of_bcdt hB hH E (σ * D)
    (ZInQ.Manuscript.RC.Even.sigma_mul_ne_zero hσ hD)
  exact ZInQ.Manuscript.RC.Even.E10_of_waldspurgerCor2 hW hE L hN ψ η hσ hψη hg hD₀ hD hsq₀ hsq
    hc₀ hc hcl hF₀ hF ha₀ hL₀

/-- **(E.11) with the continuations discharged** (tex 8136–8142; PROVED from lane RC8's PRINT
`WaldspurgerCor2`, the ELLIOT data `EvenPhaseData`, the shared printed leaf `PoleS12.BCDTThmA`
and lane RC8's GLUE `HasseConvergence`). Consumer: lane RC11's `EvenPhaseData.E11` (hypothesis
`hcont` removed). Discharger: `twistContinuation_of_bcdt`. -/
theorem evenPhaseData_E11_of_bcdt (hW : WaldspurgerCor2) (hB : PoleS12.BCDTThmA)
    (hH : HasseConvergence) {E : WeierstrassCurve ℚ} [hE : E.IsElliptic]
    {L : ZInQ.Manuscript.RC.Even.CentralNormalization E} {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    {D₀ : ℕ} (P : ZInQ.Manuscript.RC.Even.EvenPhaseData E L σ D₀) (hL₀ : L.Lstar (σ * D₀) ≠ 0) :
    ∀ D ∈ P.retained, ∃ r : ℚ, hiwCoeff P.g D / hiwCoeff P.g D₀ = P.z D * (r : ℂ) ∧
      r ^ 2 = L.Lstar (σ * D) / L.Lstar (σ * D₀) :=
  P.E11 hW hE hσ hL₀ (twistContinuation_of_bcdt hB hH E)

/-- **The attained minimum of `v₂ a(D) − ω(D)` from (3.2)** (tex 7807–7810, 8193–8199; PROVED
from lane RC8's PRINT `WaldspurgerCor2`, the ELLIOT data `EvenPhaseData`, lane RC11's (3.2)
`EvenScalar32 E N L`, the shared printed leaves `Prints` and lane RC8's GLUE `HasseConvergence`).
Consumer: lane RC11's `EvenPhaseData.minimum` (hypotheses `hcont` and `h9` removed).
Dischargers: `twistContinuation_of_bcdt` and `evenLowerBound_of_evenScalar32_of_prints`. -/
theorem evenPhaseData_minimum_of_prints (hW : WaldspurgerCor2) (hP : Prints)
    (hH : HasseConvergence) {E : WeierstrassCurve ℚ} [hE : E.IsElliptic]
    {L : ZInQ.Manuscript.RC.Even.CentralNormalization E} {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    {D₀ : ℕ} (P : ZInQ.Manuscript.RC.Even.EvenPhaseData E L σ D₀) (hL₀ : L.Lstar (σ * D₀) ≠ 0)
    {N : ℕ} (h32 : ZInQ.Manuscript.RC.Even.EvenScalar32 E N L) :
    ∃ r : ℕ → ℚ, (∀ D ∈ P.retained, hiwCoeff P.g D / hiwCoeff P.g D₀ = P.z D * (r D : ℂ) ∧
        r D ^ 2 = L.Lstar (σ * D) / L.Lstar (σ * D₀)) ∧
      ∃ δ : ℤ, (∃ D ∈ P.retained, r D ≠ 0 ∧
          padicValRat 2 (r D) - ZInQ.Manuscript.RC.Even.omegaN D = δ) ∧
        ∀ D ∈ P.retained, r D ≠ 0 → δ ≤ padicValRat 2 (r D) - ZInQ.Manuscript.RC.Even.omegaN D :=
  P.minimum hW hE hσ hL₀ (twistContinuation_of_bcdt hP.bcdt hH E)
    (evenLowerBound_of_evenScalar32_of_prints hP hH h32)

/-- **The attained minimum from Appendix E's outputs** (tex 7614–7787 then 7807–7810,
8193–8199; PROVED from lane RC8's PRINT `WaldspurgerCor2`, the ELLIOT data `EvenPhaseData` and
`AppEOutputs E N L` (`N ≠ 0`), the shared `Prints` and lane RC8's GLUE `HasseConvergence`):
lane RC11's `evenScalar32_of_appE` followed by `evenPhaseData_minimum_of_prints`. -/
theorem evenPhaseData_minimum_of_appE (hW : WaldspurgerCor2) (hP : Prints)
    (hH : HasseConvergence) {E : WeierstrassCurve ℚ} [hE : E.IsElliptic]
    {L : ZInQ.Manuscript.RC.Even.CentralNormalization E} {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    {D₀ : ℕ} (P : ZInQ.Manuscript.RC.Even.EvenPhaseData E L σ D₀) (hL₀ : L.Lstar (σ * D₀) ≠ 0)
    {N : ℕ} (hN : N ≠ 0) (hA : ZInQ.Manuscript.RC.Even.AppEOutputs E N L) :
    ∃ r : ℕ → ℚ, (∀ D ∈ P.retained, hiwCoeff P.g D / hiwCoeff P.g D₀ = P.z D * (r D : ℂ) ∧
        r D ^ 2 = L.Lstar (σ * D) / L.Lstar (σ * D₀)) ∧
      ∃ δ : ℤ, (∃ D ∈ P.retained, r D ≠ 0 ∧
          padicValRat 2 (r D) - ZInQ.Manuscript.RC.Even.omegaN D = δ) ∧
        ∀ D ∈ P.retained, r D ≠ 0 → δ ≤ padicValRat 2 (r D) - ZInQ.Manuscript.RC.Even.omegaN D :=
  evenPhaseData_minimum_of_prints hW hP hH hσ P hL₀ (ZInQ.Manuscript.RC.Even.evenScalar32_of_appE hN hA)

end ZInQ.Manuscript.RC.GlueSweep.Even
