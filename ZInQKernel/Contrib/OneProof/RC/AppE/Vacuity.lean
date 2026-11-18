import ZInQKernel.Contrib.OneProof.RC.AppE.Assembly
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.EvenPhaseForm

/-!
# Appendix E: the retained set of `EvenPhaseData` contains the whole `S₀` filter (a check on the
# statement)

Lane RC11's structure `EvenPhaseData` used to bound `retained` only from above (`retained_spec`)
and to ask only `D₀ ∈ retained`. With `retained = {D₀}` and `z = 1` its phase fields held
trivially (`z_sq` at `D₀` is `1 = ψ(D₀)ψ(D₀)⁻¹`, `rational` at `D₀` is `1 = 1 · 1`), so it was
inhabited from lane RC8's print `WaldspurgerNonvanishing` alone, with no Galois comparison, no
Ramsey model and no two-power order, and its minimum `EvenPhaseData.minimum` was a minimum over
`{D₀}`.

The structure now carries the fixed support `S₀` (a set of primes) and the lower bound
`filter_mem : ∀ D, S0Filter S₀ D₀ D → D ∈ retained`, as in the text: "For every retained positive
squarefree `D` in the original `S₀` filter" (tex 7800–7801); "In (E.10)–(E.11), `D` ranges over
positive squarefree parameters in these same unit squareclasses at every prime of `S₀`"
(tex 7816–7817).

* `EvenPhaseData.retained_ne_singleton_of_mem` (in `RC/Even/EvenPhase.lean`) — `retained = {D₀}`
  contradicts `filter_mem` as soon as the filter has another element;
* `not_exists_evenPhaseData_singleton` — the token instance is refuted outright: no
  `P : EvenPhaseData E L σ S₀ D₀` has `retained = {D₀}`, since the filter is infinite
  (`S0Filter.infinite`, `EvenPhaseData.retained_infinite`);
* `evenPhaseData_Ecurve_retained_infinite` — the strengthened structure is still inhabited for the
  curve `E_ℓ` from the inputs of `evenPhaseData_Ecurve` (the PRINTs `WaldspurgerNonvanishing`,
  `WaldspurgerCor2`, `RamseyAlgebraicModel`, `ModularNewform`, the GLUE `HasseConvergence` and the
  GLUE hypothesis `HalfIntegralTwist`), with retained set the whole, infinite, `S₀` filter;
* `evenPhaseRest_of_prints` — lane RC22's phase bundle `EvenPhaseRest` (which now carries
  `filter_mem` too) for every reference form the print can return, from the same prints: the
  hypothesis `rest` of `evenPhaseData_of_waldspurgerNonvanishing` is satisfiable
  (`evenPhaseData_nonempty_of_prints`).

PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.AppE

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 ZInQ.Manuscript.RC.PrintsAnalytic UpperHalfPlane
open ZInQ.Manuscript.RC.Even (S0Filter S0Filter.spec S0Filter.self)

/-- **The token instance `retained = {D₀}` is refuted** (PROVED, from
`EvenPhaseData.retained_ne_singleton`): for every `E`, `L`, `σ`, `S₀`, `D₀`, no instance of the
strengthened `EvenPhaseData` has `retained = {D₀}`; its retained set is infinite. -/
theorem not_exists_evenPhaseData_singleton {E : WeierstrassCurve ℚ}
    {L : ZInQ.Manuscript.RC.Even.CentralNormalization E} {σ : ℤ} {S₀ : Finset ℕ} {D₀ : ℕ} :
    ¬ ∃ P : ZInQ.Manuscript.RC.Even.EvenPhaseData E L σ S₀ D₀, P.retained = {D₀} :=
  fun ⟨P, hP⟩ => P.retained_ne_singleton hP

/-- **Non-vacuity witness for the strengthened structure, for `E_ℓ`** (PROVED from the inputs of
`evenPhaseData_Ecurve`: the PRINTs `WaldspurgerNonvanishing`, `WaldspurgerCor2`,
`RamseyAlgebraicModel`, `ModularNewform`, the GLUE `HasseConvergence` and the GLUE hypothesis
`HalfIntegralTwist`): with `S₀ = primes(2N₀)` and `D₀ > 0` squarefree prime to `2N₀` with
`L_*(σD₀) ≠ 0`, there is `P : EvenPhaseData (Ecurve ℓ) L σ S₀ D₀` whose retained set is the whole
`S₀` filter, and that set is infinite. -/
theorem evenPhaseData_Ecurve_retained_infinite (hWN : WaldspurgerNonvanishing)
    (hW : WaldspurgerCor2) (hR : RamseyAlgebraicModel) (hTw : HalfIntegralTwist)
    (hM : ModularNewform) (hH : HasseConvergence) {ℓ : ℕ} (hℓ : 0 < ℓ)
    (L : ZInQ.Manuscript.RC.Even.CentralNormalization (Ecurve ℓ)) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    {N₀ : ℕ} {w₀ : ℤ} (h₀ : RootNumberAt (Ecurve ℓ) N₀ w₀)
    {D₀ : ℕ} (hD₀ : 0 < D₀) (hsq₀ : Squarefree D₀) (hD₀S : ∀ p ∈ (2 * N₀).primeFactors, ¬ p ∣ D₀)
    (hL₀ : L.Lstar (σ * D₀) ≠ 0) :
    ∃ P : ZInQ.Manuscript.RC.Even.EvenPhaseData (Ecurve ℓ) L σ (2 * N₀).primeFactors D₀,
      P.retained = {D | S0Filter (2 * N₀).primeFactors D₀ D} ∧ P.retained.Infinite := by
  obtain ⟨P, hP, -⟩ := evenPhaseData_Ecurve hWN hW hR hTw hM hH hℓ L hσ h₀ hD₀ hsq₀ hD₀S hL₀
  exact ⟨P, hP, P.retained_infinite⟩

/-- **The phase bundle `EvenPhaseRest` for every reference form the print can return** (PROVED
construction from the PRINTs `WaldspurgerCor2`, `RamseyAlgebraicModel`, `PoleS12.BCDTThmA`, the
GLUE `HasseConvergence` and the GLUE hypothesis `HalfIntegralTwist`; tex 7800–7817, 8086–8138):
for a form `g` in the eigenspace of `E` and `η = ψχ_{−σ}` at a level `N` (`4 ∣ N`) with prime
support in `S₀ ∋ 2`, `ψ` of two-power order and `a_g(D₀) ≠ 0`, the retained set may be taken to be
the whole `S₀` filter, `z` the phase, and the Galois comparison holds. This is the non-vacuity
witness of the changed `EvenPhaseRest` (and of the hypothesis `rest` of lane RC22's
`evenPhaseData_of_waldspurgerNonvanishing`). -/
def evenPhaseRest_of_prints (hW : WaldspurgerCor2) (hR : RamseyAlgebraicModel)
    (hTw : HalfIntegralTwist) (hB : PoleS12.BCDTThmA) (hH : HasseConvergence)
    {E : WeierstrassCurve ℚ} [hE : E.IsElliptic]
    (L : ZInQ.Manuscript.RC.Even.CentralNormalization E) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    {S₀ : Finset ℕ} (h2 : 2 ∈ S₀) {D₀ : ℕ} (hD₀ : 0 < D₀) (hsq₀ : Squarefree D₀)
    (hD₀S : ∀ p ∈ S₀, ¬ p ∣ D₀) (hL₀ : L.Lstar (σ * D₀) ≠ 0) :
    ∀ (N : ℕ) (ψ η : DirichletCharacter ℂ N) (g : UpperHalfPlane → ℂ), 4 ∣ N →
      (∀ p : ℕ, p.Prime → p ∣ N → p ∈ S₀) →
      (∀ n : ℕ, n.Coprime N → η n = ψ n * (kronecker (-σ) n : ℂ)) →
      (∃ k : ℕ, ψ ^ (2 ^ k) = 1) →
      IsInWaldspurgerEigenspace E N ψ η g → hiwCoeff g D₀ ≠ 0 →
      ZInQ.Manuscript.RC.GlueSweep.Even.EvenPhaseRest S₀ D₀ N ψ g := by
  intro N ψ η g hN hNS hψη hψ2 hg ha₀
  -- the level is positive: a finite `S₀` cannot contain every prime
  have hN0 : N ≠ 0 := by
    rintro rfl
    obtain ⟨p, hp1, hp⟩ := Nat.exists_infinite_primes (S₀.sup id + 1)
    have hpS := hNS p hp (dvd_zero p)
    have := Finset.le_sup (f := id) hpS
    simp only [id] at this
    omega
  have : NeZero N := ⟨hN0⟩
  have hσD₀ := ZInQ.Manuscript.RC.Even.sigma_mul_ne_zero hσ hD₀
  have hcont := ZInQ.Manuscript.RC.GlueSweep.Even.twistContinuation_of_bcdt hB hH E
  have hF₀ := F_one_ne_zero_of_lstar L hσD₀ hL₀
  have hself := S0Filter.self h2 hD₀ hsq₀ hD₀S
  have hc₀ : D₀.Coprime N := (S0Filter.spec hNS hself).2.2.1
  exact { retained := {D | S0Filter S₀ D₀ D},
          retained_spec := fun D hD => S0Filter.spec hNS hD,
          filter_mem := fun D hD => hD,
          D₀_mem := hself,
          z := phase N η D₀,
          z_root := fun D hD => hψ2.elim fun k hψk => phase_root hN0 hN ψ η hσ hψη hψk hc₀
            (S0Filter.spec hNS hD).2.2.1 (S0Filter.spec hNS hD).2.2.2,
          z_sq := fun D hD => phase_sq hN0 hN ψ η hσ hψη hc₀ (S0Filter.spec hNS hD).2.2.1
            (S0Filter.spec hNS hD).2.2.2,
          rational := fun D hD => rational_of_ramsey hR hTw hW hE hcont hσ hF₀ hN ψ η hψη hg ha₀
            hD₀ hsq₀ hc₀ (S0Filter.spec hNS hD).1 (S0Filter.spec hNS hD).2.1
            (S0Filter.spec hNS hD).2.2.1 (S0Filter.spec hNS hD).2.2.2 }

/-- **Lane RC22's bridge applies** (PROVED from the PRINTs `WaldspurgerNonvanishing`,
`WaldspurgerCor2`, `RamseyAlgebraicModel`, `PoleS12.BCDTThmA`, the GLUE `HasseConvergence` and the
GLUE hypothesis `HalfIntegralTwist`): `evenPhaseData_of_waldspurgerNonvanishing` with
`rest := evenPhaseRest_of_prints …` gives an instance of the strengthened `EvenPhaseData`. -/
theorem evenPhaseData_nonempty_of_prints (hWN : WaldspurgerNonvanishing) (hW : WaldspurgerCor2)
    (hR : RamseyAlgebraicModel) (hTw : HalfIntegralTwist) (hB : PoleS12.BCDTThmA)
    (hH : HasseConvergence) {E : WeierstrassCurve ℚ} [hE : E.IsElliptic]
    (L : ZInQ.Manuscript.RC.Even.CentralNormalization E) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    (S₀ : Finset ℕ) (hS₀ : ∀ p ∈ S₀, p.Prime) (h2 : 2 ∈ S₀)
    (hcond : ∀ (N : ℕ) (w : ℤ), RootNumberAt E N w → ∀ p : ℕ, p.Prime → p ∣ N → p ∈ S₀)
    {D₀ : ℕ} (hD₀ : 0 < D₀) (hsq₀ : Squarefree D₀) (hD₀S : ∀ p ∈ S₀, ¬ p ∣ D₀)
    (hL₀ : L.Lstar (σ * D₀) ≠ 0) :
    Nonempty (ZInQ.Manuscript.RC.Even.EvenPhaseData E L σ S₀ D₀) :=
  ZInQ.Manuscript.RC.GlueSweep.Even.evenPhaseData_of_waldspurgerNonvanishing hWN hB hH L hσ S₀
    hS₀ h2 hcond hD₀ hsq₀ hD₀S hL₀
    (evenPhaseRest_of_prints hW hR hTw hB hH L hσ h2 hD₀ hsq₀ hD₀S hL₀)

end ZInQ.Manuscript.RC.AppE
