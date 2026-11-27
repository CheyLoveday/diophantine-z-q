import ZInQKernel.Contrib.OneProof.RC.EvenPlace.Producer
import ZInQKernel.Contrib.OneProof.RC.AuxInputs.Assembly
import ZInQKernel.Contrib.OneProof.RC.EvenReading.Source

/-! Thread the unmodified App E witness into the two source records.
The negative form is fixed per total type; the positive form is for the
companion twist at reference index one. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenPlace

open ZInQ.Manuscript AddressGenuine AuxInputs ZInQ.Manuscript.RC.Even EvenReading AppE PrintsAnalytic Wiring
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

/-- Use the same minimum construction as `AuxInputs.evenSource_of_phase`,
keeping the provenance of its input when filling the phase field. -/
private theorem evenSource_with_origin {ℓ : ℕ} {W : WData ℓ} (hS : SupportSpec W)
    {L : CentralNormalization (Ecurve ℓ)} (hL : L.Lstar = W.Lstar)
    (hE : (Ecurve ℓ).IsElliptic) (hW : WaldspurgerCor2)
    (hcont : ∀ h : ℤ, h ≠ 0 → ∃ F, IsLContinuation (Etw ℓ h) F)
    (h9 : EvenLowerBound (Ecurve ℓ) L) {τ : SqClass (conductor W.S)} {D₀ : ℕ}
    (hD₀ : evenFilter W.S τ D₀) (h₀ : W.Lstar (-(D₀ : ℤ)) ≠ 0)
    (P : EvenPhaseData (Ecurve ℓ) L (-1) W.S D₀) (hP : PhaseOrigin P) :
    ∃ Q : EvenSource W L τ, PhaseOrigin Q.phaseData := by
  have hf : ∀ D, evenFilter W.S τ D → D ∈ P.retained := by
    intro D hD
    exact P.filter_mem _ ((s0Filter_iff_type hS.1 hS.2.1 hD₀.2.2.1).2
      ⟨hD.1, hD.2.1, hD.2.2.1, hD.2.2.2.trans hD₀.2.2.2.symm⟩)
  have h₀' : L.Lstar ((-1 : ℤ) * (D₀ : ℤ)) ≠ 0 := by simpa [hL] using h₀
  obtain ⟨r, hr, δ, ⟨D, hD, hne, hval⟩, hlower⟩ :=
    P.minimum_on hW hE (Or.inr rfl) h₀' hcont h9 {D | evenFilter W.S τ D}
      (fun D hD => hf D hD) hD₀
  refine ⟨⟨D₀, hD₀, h₀, P, r, ?_, δ, ⟨D, hD, hne, hval⟩, hlower⟩, hP⟩
  intro D hD
  simpa using hr D (hf D hD)

/-- The fixed negative source from the existing App E inputs, with order. -/
theorem evenSource_with_order_of_prints {ℓ : ℕ} {W : WData ℓ} (hS : SupportSpec W)
    {L : CentralNormalization (Ecurve ℓ)} (hL : L.Lstar = W.Lstar) (hℓ : 0 < ℓ)
    (hWN : WaldspurgerNonvanishing) (hW : WaldspurgerCor2) (hR : AppE.RamseyAlgebraicModel)
    (hB : PoleS12.BCDTThmA) (hH : HasseConvergence)
    (hcond : ∀ (N : ℕ) (w : ℤ), RootNumberAt (Ecurve ℓ) N w →
      ∀ p : ℕ, p.Prime → p ∣ N → p ∈ W.S)
    (h9 : EvenLowerBound (Ecurve ℓ) L) {τ : SqClass (conductor W.S)}
    (hRef : HasReference W τ) : ∃ P : EvenSource W L τ, PhaseOrigin P.phaseData := by
  let _ : (Ecurve ℓ).IsElliptic := PoleRC.curve_isElliptic (by exact_mod_cast hℓ.ne')
  obtain ⟨D₀, hD₀, h₀⟩ := hRef
  have h₀' : L.Lstar ((-1 : ℤ) * (D₀ : ℤ)) ≠ 0 := by simpa [hL] using h₀
  obtain ⟨P, hP⟩ := phaseData_with_order_of_prints hWN hW hR HalfIntegral.halfIntegralTwist hB hH L (Or.inr rfl)
    W.S hS.1 hS.2.1 hcond hD₀.1 hD₀.2.1
    ((coprime_conductor hS.1 hS.2.1 _).1 hD₀.2.2.1) h₀'
  exact evenSource_with_origin hS hL inferInstance hW
    (GlueSweep.Even.twistContinuation_of_bcdt hB hH (Ecurve ℓ)) h9 hD₀ h₀ P hP

variable {ℓ : ℕ} {W : WData ℓ} {L : CentralNormalization (Ecurve ℓ)}

/-- Choose the App E witness once per type, before any budget. -/
theorem sourceFamily_with_order_of_prints (hS : SupportSpec W) (hL : L.Lstar = W.Lstar) (hℓ : 0 < ℓ)
    (hWN : WaldspurgerNonvanishing) (hW : WaldspurgerCor2) (hR : AppE.RamseyAlgebraicModel)
    (hB : PoleS12.BCDTThmA) (hH : HasseConvergence)
    (hcond : ∀ (N : ℕ) (w : ℤ), RootNumberAt (Ecurve ℓ) N w →
      ∀ p : ℕ, p.Prime → p ∣ N → p ∈ W.S) (h9 : EvenLowerBound (Ecurve ℓ) L) :
    ∃ P : SourceFamily W L, ∀ τ h, PhaseOrigin (P τ h).phaseData := by
  classical
  have hex (τ : SqClass (conductor W.S)) (h : HasReference W τ) :=
    evenSource_with_order_of_prints hS hL hℓ hWN hW hR hB hH hcond h9 h
  exact ⟨fun τ h => (hex τ h).choose, fun τ h => (hex τ h).choose_spec⟩

/-- The actual positive companion source, with the two orders on its phase field. -/
theorem genuineEvenSource_with_order_of_prints (hWN : WaldspurgerNonvanishing) (hW : WaldspurgerCor2)
    (hR : RamseyAlgebraicModel) (hB : PoleS12.BCDTThmA) (hH : HasseConvergence)
    {ℓ : ℕ} (hℓ : 0 < ℓ) (C : CentralNormalization (Ecurve ℓ)) {k : ℤ}
    (hk : k < 0) (hLk : C.Lstar k ≠ 0) (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) :
    ∃ S : Finset ℕ, T ⊆ S ∧ ∃ G : GenuineEvenSource C hk S, PhaseOrigin G.P := by
  classical
  let E' := qtwist (Ecurve ℓ) (k : ℚ)
  let C' := transportedNormalization C hk
  let : E'.IsElliptic :=
    Nonvanishing.qtwist_isElliptic (Nonvanishing.curve_nat_isElliptic hℓ) (by exact_mod_cast hk.ne)
  have hcont := GlueSweep.Even.twistContinuation_of_bcdt hB hH E'
  have h1 : qtwist E' (1 : ℚ) = E' := by
    dsimp only [E']
    rw [Nonvanishing.qtwist_qtwist, one_mul]
  have hL₁ : C'.Lstar (1 * (↑(1 : ℕ) : ℤ)) ≠ 0 := by
    simpa [C', transportedNormalization] using hLk
  obtain ⟨F, hF⟩ := hcont 1 one_ne_zero
  have hF' : IsLContinuation (qtwist E' ((1 * (↑(1 : ℕ) : ℤ) : ℤ) : ℚ)) F := by
    simpa using hF
  have hF1 := F_one_ne_zero_of_lstar C' (by norm_num) hL₁ F hF'
  have hFE' : IsLContinuation E' F := by simpa only [Int.cast_one, h1] using hF
  obtain ⟨S, hTS, hS, h2, hcond⟩ := exists_evenSupport hFE' hF1 T hT
  obtain ⟨P, hP⟩ := phaseData_with_order_of_prints hWN hW hR HalfIntegral.halfIntegralTwist
    hB hH C' (Or.inl rfl) S hS h2 hcond (D₀ := 1) (by decide) squarefree_one
    (fun p hp => (hS p hp).not_dvd_one) hL₁
  have hcoeff (n : ℕ) (hn : S0Filter S 1 n) := P.E11 hW inferInstance (Or.inl rfl) hL₁
    hcont n (P.filter_mem n hn)
  let r (n : ℕ) : ℚ := if hn : S0Filter S 1 n then (hcoeff n hn).choose else 0
  refine ⟨S, hTS, ⟨hcond, P, hP.retained_eq, hP.phase_eq, r, fun n hn => ?_⟩, hP⟩
  simpa [r, dite_eq_left hn, C', transportedNormalization] using (hcoeff n hn).choose_spec

end ZInQ.Manuscript.RC.EvenPlace
