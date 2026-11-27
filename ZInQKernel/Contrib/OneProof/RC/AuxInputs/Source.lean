import ZInQKernel.Contrib.OneProof.RC.AuxInputs.Types
import ZInQKernel.Contrib.OneProof.RC.AppE.Assembly
import ZInQKernel.Contrib.OneProof.RC.HalfIntegral.Twist

/-! Negative even sources at fixed total types. The minimum belongs to the
original full filter of this source (tex 7793–7810, 10079–10087, 10146). -/

noncomputable section

namespace ZInQ.Manuscript.RC.AuxInputs

open ZInQ.Manuscript AddressGenuine PrintsAnalytic Symbols Wiring ZInQ.Manuscript.RC.Even
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

def evenFilter (S : Finset ℕ) (τ : SqClass (conductor S)) (D : ℕ) : Prop :=
  0 < D ∧ Squarefree D ∧ D.Coprime (conductor S) ∧ sqClassOf (conductor S) (D : ℤ) = τ

/-- A nonzero negative reference at this total type. This condition also
allows nonzero references in negative filters other than the prepared one. -/
def HasReference {ℓ : ℕ} (W : WData ℓ) (τ : SqClass (conductor W.S)) : Prop :=
  ∃ D : ℕ, evenFilter W.S τ D ∧ W.Lstar (-(D : ℤ)) ≠ 0

theorem lstarTarget_of_normalization {ℓ : ℕ} {W : WData ℓ}
    {L : CentralNormalization (Ecurve ℓ)} (hL : L.Lstar = W.Lstar) (hℓ : 0 < ℓ)
    (hB : PoleS12.BCDTThmA) (hH : HasseConvergence) : LstarTarget W.toRCData := by
  let _ : (Ecurve ℓ).IsElliptic := PoleRC.curve_isElliptic (by exact_mod_cast hℓ.ne')
  intro d hd
  rw [← hL]
  exact GlueSweep.Even.lstar_ne_zero_iff_of_bcdt hB hH L hd

theorem prepared_hasReference {ℓ : ℕ} (W : WData ℓ) (hS : SupportSpec W)
    (hL : LstarTarget W.toRCData) {τ : SqClass (conductor W.S)}
    (ht : PreparedType W (evenTypes W.S hS.1) τ) : HasReference W τ := by
  obtain ⟨d, hd, _, hsf, hdS, hrank, ht⟩ := ht
  have hc : d.natAbs.Coprime (conductor W.S) :=
    (coprime_conductor hS.1 hS.2.1 _).2 (fun p hp hpd => hdS p hp (Int.natCast_dvd.mpr hpd))
  have hsfN := Int.squarefree_natAbs.mpr hsf
  have htype := total_of_good_primes hS.1 _ (good_primeFactors hS.1 hc)
  rw [Nat.prod_primeFactors_of_squarefree hsfN, ht] at htype
  have habs : (d.natAbs : ℤ) = -d := by
    rw [← Int.natAbs_neg]
    exact Int.natAbs_of_nonneg (by omega)
  have hsign : -(d.natAbs : ℤ) = d := by rw [habs, neg_neg]
  exact ⟨d.natAbs, ⟨Int.natAbs_pos.mpr hd.ne, hsfN, hc, htype.symm⟩,
    by rw [hsign]; exact (hL _ hd.ne).2 hrank⟩

/-- The App E form, its rational phase-removed coefficients on the exact
type filter and its attained valuation depth. This record makes no
assertion about arithmetic graph rules or lattice realizations. -/
structure EvenSource {ℓ : ℕ} (W : WData ℓ) (L : CentralNormalization (Ecurve ℓ))
    (τ : SqClass (conductor W.S)) where
  D₀ : ℕ
  reference : evenFilter W.S τ D₀
  nonzero : W.Lstar (-(D₀ : ℤ)) ≠ 0
  phaseData : EvenPhaseData (Ecurve ℓ) L (-1) W.S D₀
  r : ℕ → ℚ
  coeff : ∀ D, evenFilter W.S τ D →
    hiwCoeff phaseData.g D / hiwCoeff phaseData.g D₀ = phaseData.z D * (r D : ℂ) ∧
      r D ^ 2 = L.Lstar (-(D : ℤ)) / L.Lstar (-(D₀ : ℤ))
  δ : ℤ
  attained : ∃ D, evenFilter W.S τ D ∧ r D ≠ 0 ∧ padicValRat 2 (r D) - omegaN D = δ
  lower : ∀ D, evenFilter W.S τ D → r D ≠ 0 → δ ≤ padicValRat 2 (r D) - omegaN D

/-- Fix the original filter before taking a minimum. App E produces the
same minimum and witness even if its `retained` field is a larger set. -/
theorem evenSource_of_phase {ℓ : ℕ} {W : WData ℓ} (hS : SupportSpec W)
    {L : CentralNormalization (Ecurve ℓ)} (hL : L.Lstar = W.Lstar)
    (hE : (Ecurve ℓ).IsElliptic) (hW : WaldspurgerCor2)
    (hcont : ∀ h : ℤ, h ≠ 0 → ∃ F, IsLContinuation (Etw ℓ h) F)
    (h9 : EvenLowerBound (Ecurve ℓ) L) {τ : SqClass (conductor W.S)} {D₀ : ℕ}
    (hD₀ : evenFilter W.S τ D₀) (h₀ : W.Lstar (-(D₀ : ℤ)) ≠ 0)
    (P : EvenPhaseData (Ecurve ℓ) L (-1) W.S D₀) : Nonempty (EvenSource W L τ) := by
  have hf : ∀ D, evenFilter W.S τ D → D ∈ P.retained := by
    intro D hD
    exact P.filter_mem _ ((s0Filter_iff_type hS.1 hS.2.1 hD₀.2.2.1).2
      ⟨hD.1, hD.2.1, hD.2.2.1, hD.2.2.2.trans hD₀.2.2.2.symm⟩)
  have h₀' : L.Lstar ((-1 : ℤ) * (D₀ : ℤ)) ≠ 0 := by simpa [hL] using h₀
  obtain ⟨r, hr, δ, ⟨D, hD, hne, hval⟩, hlower⟩ :=
    P.minimum_on hW hE (Or.inr rfl) h₀' hcont h9 {D | evenFilter W.S τ D}
      (fun D hD => hf D hD) hD₀
  refine ⟨⟨D₀, hD₀, h₀, P, r, ?_, δ, ⟨D, hD, hne, hval⟩, hlower⟩⟩
  intro D hD
  simpa using hr D (hf D hD)

/-- Instantiate the phase producer already in the tree for the original
curve and support, without a later extra exclusion sieve. -/
theorem evenSource_of_prints {ℓ : ℕ} {W : WData ℓ} (hS : SupportSpec W)
    {L : CentralNormalization (Ecurve ℓ)} (hL : L.Lstar = W.Lstar) (hℓ : 0 < ℓ)
    (hWN : WaldspurgerNonvanishing) (hW : WaldspurgerCor2) (hR : AppE.RamseyAlgebraicModel)
    (hB : PoleS12.BCDTThmA) (hH : HasseConvergence)
    (hcond : ∀ (N : ℕ) (w : ℤ), RootNumberAt (Ecurve ℓ) N w →
      ∀ p : ℕ, p.Prime → p ∣ N → p ∈ W.S)
    (h9 : EvenLowerBound (Ecurve ℓ) L) {τ : SqClass (conductor W.S)}
    (hRef : HasReference W τ) : Nonempty (EvenSource W L τ) := by
  let _ : (Ecurve ℓ).IsElliptic := PoleRC.curve_isElliptic (by exact_mod_cast hℓ.ne')
  obtain ⟨D₀, hD₀, h₀⟩ := hRef
  have h₀' : L.Lstar ((-1 : ℤ) * (D₀ : ℤ)) ≠ 0 := by simpa [hL] using h₀
  obtain ⟨P, _, _⟩ := AppE.evenPhaseData_of_prints hWN hW hR HalfIntegral.halfIntegralTwist hB hH L (Or.inr rfl)
    W.S hS.1 hS.2.1 hcond hD₀.1 hD₀.2.1
    ((coprime_conductor hS.1 hS.2.1 _).1 hD₀.2.2.1) h₀'
  exact evenSource_of_phase hS hL inferInstance hW
    (GlueSweep.Even.twistContinuation_of_bcdt hB hH (Ecurve ℓ)) h9 hD₀ h₀ P

/-- The binary reading of one actual source, after phase removal. -/
def EvenSource.reading {ℓ : ℕ} {W : WData ℓ} {L : CentralNormalization (Ecurve ℓ)}
    {τ : SqClass (conductor W.S)} (P : EvenSource W L τ) : Finset ℕ → ZMod 2 :=
  coeffReading (fun D => (P.r D : ℚ_[2])) P.δ (evenFilter W.S τ)

def EvenSource.symbol {ℓ : ℕ} {W : WData ℓ} {L : CentralNormalization (Ecurve ℓ)}
    {τ : SqClass (conductor W.S)} (P : EvenSource W L τ) (hS : SupportSpec W) :
    Config (SqClass (conductor W.S)) → ZMod 2 :=
  symb (evenTypes W.S hS.1) P.reading

variable {ℓ : ℕ} {W : WData ℓ} {L : CentralNormalization (Ecurve ℓ)}
    {τ : SqClass (conductor W.S)} (P : EvenSource W L τ) (hS : SupportSpec W)

theorem EvenSource.symbol_off : VanishesOffFilter (P.symbol hS) τ := by
  classical
  intro Γ h
  unfold EvenSource.symbol symb at h
  split at h
  next hr =>
    let f := hr.choose
    have hf : IsReal (evenTypes W.S hS.1) Γ f := hr.choose_spec
    have hh := total_of_good_primes hS.1 (Γ.V.image f)
      (fun p hp => by
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
        exact (hf.2.1 v hv).1)
    change (∑ p ∈ Γ.V.image f, (evenTypes W.S hS.1).typ p) = _ at hh
    rw [Finset.sum_image (fun v hv w hw he => hf.1 hv hw he)] at hh
    have he : (∑ v ∈ Γ.V, (evenTypes W.S hS.1).typ (f v)) = Γ.total :=
      Finset.sum_congr rfl (fun v hv => (hf.2.1 v hv).2)
    rw [he] at hh
    unfold EvenSource.reading coeffReading coeffSymbol at h
    split at h
    next hv => exact hh.trans hv.1.2.2.2
    next => exact (zero_ne_one h).elim
  next => exact (zero_ne_one h).elim

theorem EvenSource.symbol_primeFactors
    (hswap : ∀ B, FixedUFactorization (evenTypes W.S hS.1) P.reading B)
    {D : ℕ} (hsf : Squarefree D) (hc : D.Coprime (conductor W.S)) :
    P.symbol hS (primeConfig D.primeFactors (evenTypes W.S hS.1).typ) =
      coeffSymbol (fun n => (P.r n : ℚ_[2])) P.δ (evenFilter W.S τ) D := by
  let T := evenTypes W.S hS.1
  calc
    _ = readPrimes (fun n => (P.r n : ℚ_[2])) P.δ (evenFilter W.S τ)
        (primeConfig D.primeFactors T.typ) :=
      symb_primeConfig T _ _ _ (hswap D.primeFactors.card) _
        (good_primeFactors hS.1 hc) le_rfl
    _ = _ := by
      change coeffSymbol _ _ _ (∏ p ∈ D.primeFactors, p) = _
      rw [Nat.prod_primeFactors_of_squarefree hsf]

/-- The attained minimum gives a unit seed by reading its actual prime
factors. Only fixed-set factorization is needed for this dictionary step. -/
theorem EvenSource.unitSeed
    (hswap : ∀ B, FixedUFactorization (evenTypes W.S hS.1) P.reading B) :
    ∃ Γ, IsUnitSeed (evenSign W.S) (P.symbol hS) Γ := by
  obtain ⟨D, hD, hr, hval⟩ := P.attained
  let T := evenTypes W.S hS.1
  let V := D.primeFactors
  have hV : ∀ p ∈ V, T.Good p := good_primeFactors hS.1 hD.2.2.1
  have hf : IsReal T (primeConfig V T.typ) id :=
    ⟨Set.injOn_id _, fun v hv => ⟨hV v hv, rfl⟩, fun _ _ _ _ _ => rfl⟩
  have hg := compatible_of_real T hf
  refine ⟨primeConfig V T.typ, hg, ?_⟩
  classical
  rw [P.symbol_primeFactors hS hswap hD.2.1 hD.2.2.1]
  have hnz : (P.r D : ℚ_[2]) ≠ 0 := by exact_mod_cast hr
  have hv : Padic.valuation (P.r D : ℚ_[2]) = P.δ + (D.primeFactors.card : ℤ) := by
    rw [Padic.valuation_ratCast]
    unfold omegaN at hval
    omega
  simp [coeffSymbol, hD, hnz, hv]


end ZInQ.Manuscript.RC.AuxInputs
