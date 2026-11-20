import ZInQKernel.Contrib.OneProof.RC.EvenPlace.Sources
import ZInQKernel.Contrib.OneProof.RC.EvenPlace.Source
import ZInQKernel.Contrib.OneProof.RC.EvenBudget.Place

/-! Place the fixed negative App E source in the coefficient record used
by the even budget. The same algebraic valuation ring will be used for
the complex singleton calculation. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenPlace

open ZInQ.Manuscript AddressGenuine AuxInputs ZInQ.Manuscript.RC.Even EvenBudget Wiring
open ZInQ.Contrib.CloudB3RC53
open NumberField

/-- Both characters and every phase of the selected record lie in this
one algebraic valuation ring, viewed through its complex embedding. -/
structure PhaseScalarsAt {E : WeierstrassCurve ℚ} {L : CentralNormalization E}
    {σ : ℤ} {S : Finset ℕ} {D₀ : ℕ} (P : EvenPhaseData E L σ S D₀)
    {F : IntermediateField ℚ ℂ} [NumberField F] (V : Place F) : Prop where
  psi_mem : ∀ x : ZMod P.N, P.ψ x ∈ V.complexIntegers
  eta_mem : ∀ x : ZMod P.N, P.η x ∈ V.complexIntegers
  phase_mem : ∀ D, P.z D ∈ V.complexIntegers

/-- The two-power bounds put the scalars of this exact App E witness
in the ring at any chosen prime over two of the common field. -/
theorem phaseScalarsAt_of_order {E : WeierstrassCurve ℚ} {L : CentralNormalization E}
    {σ : ℤ} {S : Finset ℕ} {D₀ e eψ eη : ℕ}
    {P : EvenPhaseData E L σ S D₀} (V : Place (PhaseField e)) (hP : PhaseOrigin P)
    (hψ : P.ψ ^ (2 ^ eψ) = 1) (hη : P.η ^ (2 ^ eη) = 1) (hleψ : eψ ≤ e) (hleη : eη ≤ e) :
    PhaseScalarsAt P V := by
  have heta := V.character_mem P.η hη hleη
  refine ⟨V.character_mem P.ψ hψ hleψ, heta, ?_⟩
  intro D
  rw [hP.phase_eq]
  exact heta (AppE.sqrtRatio P.N D₀ D)

/-- Two records may come from different forms and levels. Take one bound
for their four character orders and select a single prime over two. -/
theorem common_phase_scalars {E₁ E₂ : WeierstrassCurve ℚ}
    {L₁ : CentralNormalization E₁} {L₂ : CentralNormalization E₂}
    {σ₁ σ₂ : ℤ} {S₁ S₂ : Finset ℕ} {D₁ D₂ : ℕ}
    {P₁ : EvenPhaseData E₁ L₁ σ₁ S₁ D₁} {P₂ : EvenPhaseData E₂ L₂ σ₂ S₂ D₂}
    (h₁ : PhaseOrigin P₁) (h₂ : PhaseOrigin P₂) :
    ∃ e : ℕ, ∃ V : Place (PhaseField e), PhaseScalarsAt P₁ V ∧ PhaseScalarsAt P₂ V := by
  obtain ⟨a, ha⟩ := h₁.psi_order
  obtain ⟨b, hb⟩ := h₁.eta_order
  obtain ⟨c, hc⟩ := h₂.psi_order
  obtain ⟨d, hd⟩ := h₂.eta_order
  let e := max (max a b) (max c d)
  obtain ⟨V⟩ := place_exists (PhaseField e)
  exact ⟨e, V,
    phaseScalarsAt_of_order V h₁ ha hb
      ((le_max_left a b).trans (le_max_left _ _)) ((le_max_right a b).trans (le_max_left _ _)),
    phaseScalarsAt_of_order V h₂ hc hd
      ((le_max_left c d).trans (le_max_right _ _)) ((le_max_right c d).trans (le_max_right _ _))⟩

variable {ℓ : ℕ} {W : WData ℓ} {L : CentralNormalization (Ecurve ℓ)}
variable {τ : SqClass (conductor W.S)}
variable {F : IntermediateField ℚ ℂ} [NumberField F]

/-- One fixed shift pays the negative source's depth at every index,
using the exact negative-sign recurrence and the original type sieve. -/
theorem budget_shift_mem (P : EvenSource W L τ) (hS : SupportSpec W)
    {V : Place F} (H : PhaseScalarsAt P.phaseData V) (n : ℕ) :
    (2 : ℂ) ^ (-P.δ) * P.sievedCoeff n ∈ V.complexIntegers := by
  refine V.source_shift_mem (η := fun j : ℕ => P.phaseData.η j) (z := P.phaseData.z)
    (r := P.r) (G := (evenTypes W.S hS.1).Good) (adm := evenFilter W.S τ)
    (ap := fun p => (Ecurve ℓ).LFunction p) P.δ (fun j => H.eta_mem j) (fun j _ => H.phase_mem j)
    (by simp [EvenSource.sievedCoeff]) ?_ (fun _ => sieved_off_squarefree P)
    (fun _ _ hn => (squarefree_phase P hS hn).1) ?_ ?_ n
  · rintro j ⟨q, hq, hbad⟩
    have hn : ¬ j.Coprime (conductor W.S) := fun h =>
      hbad (good_primeFactors hS.1 h q hq)
    simp [EvenSource.sievedCoeff, hn]
  · intro j hj hr
    have hl := P.lower j hj hr
    have hω : 0 ≤ (omegaN j : ℤ) := Int.natCast_nonneg _
    omega
  · intro p hp hg
    exact ⟨1, Or.inl rfl, sieved_recurrence P hS hg⟩

/-- The source's unshifted coefficients lift to the embedded number
field; its shifted coefficients lift to the completed integers. -/
def sourceAtPlace (P : EvenSource W L τ) (hS : SupportSpec W)
    {V : Place F} (H : PhaseScalarsAt P.phaseData V) :
    SourceAtPlace P V.LocalIntegers V.LocalField where
  K₀ := F
  eC := F.subtype
  eK := FinitePlace.embedding V.v
  c n := V.unshiftedLift (-P.δ) (P.sievedCoeff n) (budget_shift_mem P hS H n)
  η₀ n := V.fieldLift (P.phaseData.η n) (H.eta_mem n)
  k := -P.δ
  a n := V.localLift ((2 : ℂ) ^ (-P.δ) * P.sievedCoeff n) (budget_shift_mem P hS H n)
  η n := V.localLift (P.phaseData.η n) (H.eta_mem n)
  complex_coeff n := V.unshiftedLift_complex _ _ (budget_shift_mem P hS H n)
  complex_eta n := V.fieldLift_complex _ (H.eta_mem n)
  integral_coeff n := V.unshiftedLift_local _ _ (budget_shift_mem P hS H n)
  integral_eta n := V.localLift_eq _ (H.eta_mem n)
  phase_lift D _ :=
    ⟨V.fieldLift _ (H.phase_mem D), V.localLift _ (H.phase_mem D),
      V.fieldLift_complex _ (H.phase_mem D), V.localLift_eq _ (H.phase_mem D)⟩
  padicInt := V.padicInt
  padic := V.padic
  padic_agree := V.padic_agree

/-- The integral character of the same coefficient record has precisely
the power equation needed at every good prime. -/
theorem sourceAtPlace_eta_phase (P : EvenSource W L τ) (hS : SupportSpec W)
    {V : Place F} (H : PhaseScalarsAt P.phaseData V) (hP : PhaseOrigin P.phaseData)
    {p : ℕ} (hp : (evenTypes W.S hS.1).Good p) :
    ∃ t : ℕ, (sourceAtPlace P hS H).η p ^ (2 ^ t) = 1 := by
  exact eta_phase_of_character (sourceAtPlace P hS H) hS Subtype.val_injective hP.eta_order hp

/-- In particular, the original fixed-type source has a populated
`SourceAtPlace` and its required good-prime phase condition. -/
theorem sourceAtPlace_exists (P : EvenSource W L τ) (hS : SupportSpec W)
    (hP : PhaseOrigin P.phaseData) :
    ∃ e : ℕ, ∃ V : Place (PhaseField e), ∃ C : SourceAtPlace P V.LocalIntegers V.LocalField,
      ∀ p, (evenTypes W.S hS.1).Good p → ∃ t : ℕ, C.η p ^ (2 ^ t) = 1 := by
  obtain ⟨e, V, H, _⟩ := common_phase_scalars hP hP
  exact ⟨e, V, sourceAtPlace P hS H, fun _ => sourceAtPlace_eta_phase P hS H hP⟩

end ZInQ.Manuscript.RC.EvenPlace
