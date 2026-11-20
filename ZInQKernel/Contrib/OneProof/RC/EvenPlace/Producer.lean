import ZInQKernel.Contrib.OneProof.RC.AppE.Assembly

/-! Keep the character orders on the same App E witness (tex 7943–7944). -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenPlace

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 PrintsAnalytic
open AppE ZInQ.Manuscript.RC.Even UpperHalfPlane

/-- Additional provenance for the original, unchanged phase record. -/
structure PhaseOrigin {E : WeierstrassCurve ℚ} {L : CentralNormalization E}
    {σ : ℤ} {S : Finset ℕ} {D₀ : ℕ} (P : EvenPhaseData E L σ S D₀) : Prop where
  retained_eq : P.retained = {D | S0Filter S D₀ D}
  phase_eq : P.z = phase P.N P.η D₀
  psi_order : ∃ e : ℕ, P.ψ ^ (2 ^ e) = 1
  eta_order : ∃ e : ℕ, P.η ^ (2 ^ e) = 1

/-- Forget the two order proofs. The very same record satisfies the original
producer's conclusion, with its retained set and phase equality verbatim. -/
theorem phaseData_forget_order {E : WeierstrassCurve ℚ} {L : CentralNormalization E}
    {σ : ℤ} {S : Finset ℕ} {D₀ : ℕ} {P : EvenPhaseData E L σ S D₀}
    (hP : PhaseOrigin P) :
    P.retained = {D | S0Filter S D₀ D} ∧ P.z = phase P.N P.η D₀ :=
  ⟨hP.retained_eq, hP.phase_eq⟩

/-- Refine `AppE.evenPhaseData_of_prints` at its witness construction.
All fields of the phase record have the original construction, with the
two order equations recorded alongside it. -/
theorem phaseData_with_order_of_prints (hWN : WaldspurgerNonvanishing) (hW : WaldspurgerCor2)
    (hR : RamseyAlgebraicModel) (hTw : HalfIntegralTwist) (hB : PoleS12.BCDTThmA)
    (hH : HasseConvergence) {E : WeierstrassCurve ℚ} [hE : E.IsElliptic]
    (L : CentralNormalization E) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    (S₀ : Finset ℕ) (hS₀ : ∀ p ∈ S₀, p.Prime) (h2 : 2 ∈ S₀)
    (hcond : ∀ (N : ℕ) (w : ℤ), RootNumberAt E N w → ∀ p : ℕ, p.Prime → p ∣ N → p ∈ S₀)
    {D₀ : ℕ} (hD₀ : 0 < D₀) (hsq₀ : Squarefree D₀) (hD₀S : ∀ p ∈ S₀, ¬ p ∣ D₀)
    (hL₀ : L.Lstar (σ * D₀) ≠ 0) :
    ∃ P : EvenPhaseData E L σ S₀ D₀, PhaseOrigin P := by
  have hσD₀ := sigma_mul_ne_zero hσ hD₀
  have hA : AnalyticRank (qtwist E ((σ * D₀ : ℤ) : ℚ)) 0 :=
    (ZInQ.Manuscript.RC.GlueSweep.Even.lstar_ne_zero_iff_of_bcdt hB hH L hσD₀).mp hL₀
  obtain ⟨N, hN, hNS, ψ, η, hψη, ⟨k, hψk⟩, g, hg, ha₀⟩ :=
    hWN E hE σ hσ S₀ hS₀ h2 hcond D₀ hD₀ hsq₀ hD₀S hA
  -- the level is positive: a finite `S₀` cannot contain every prime
  have hN0 : N ≠ 0 := by
    rintro rfl
    obtain ⟨p, hp1, hp⟩ := Nat.exists_infinite_primes (S₀.sup id + 1)
    have hpS := hNS p hp (dvd_zero p)
    have := Finset.le_sup (f := id) hpS
    simp only [id] at this
    omega
  have : NeZero N := ⟨hN0⟩
  have hcont := ZInQ.Manuscript.RC.GlueSweep.Even.twistContinuation_of_bcdt hB hH E
  have hF₀ := F_one_ne_zero_of_lstar L hσD₀ hL₀
  have hself := S0Filter.self h2 hD₀ hsq₀ hD₀S
  refine ⟨{ hS₀ := hS₀, hD₀S := hD₀S, N := N, hN := hN, hNS := hNS, ψ := ψ, η := η,
            hψη := hψη, g := g, hg := hg, ha₀ := ha₀,
            retained := {D | S0Filter S₀ D₀ D},
            retained_spec := fun D hD => S0Filter.spec hNS hD,
            filter_mem := fun D hD => hD,
            D₀_mem := hself,
            z := phase N η D₀,
            z_root := fun D hD => ?_,
            z_sq := fun D hD => ?_,
            rational := fun D hD => ?_ }, ⟨rfl, rfl, ⟨k, hψk⟩,
      ⟨k + 1, eta_pow_two_pow_eq_one hN ψ η hσ hψη hψk⟩⟩⟩
  · obtain ⟨-, -, hc, hcl⟩ := S0Filter.spec hNS hD
    obtain ⟨-, -, hc₀, -⟩ := S0Filter.spec hNS hself
    exact phase_root hN0 hN ψ η hσ hψη hψk hc₀ hc hcl
  · obtain ⟨-, -, hc, hcl⟩ := S0Filter.spec hNS hD
    obtain ⟨-, -, hc₀, -⟩ := S0Filter.spec hNS hself
    exact phase_sq hN0 hN ψ η hσ hψη hc₀ hc hcl
  · obtain ⟨hD0, hsq, hc, hcl⟩ := S0Filter.spec hNS hD
    obtain ⟨-, -, hc₀, -⟩ := S0Filter.spec hNS hself
    exact rational_of_ramsey hR hTw hW hE hcont hσ hF₀ hN ψ η hψη hg ha₀ hD₀ hsq₀ hc₀ hD0 hsq hc
      hcl

end ZInQ.Manuscript.RC.EvenPlace
