import ZInQKernel.Contrib.OneProof.RC.AuxInputs.Source
import ZInQKernel.Contrib.OneProof.RC.O12.Inputs
import ZInQKernel.Contrib.CloudB3RC53.FrobCount.ApModFour

/-! The same-source even (O.12) handoff and the auxiliary inputs of (F.3).
No odd stage data or upper transfer is used to produce the auxiliary factor. -/

noncomputable section

namespace ZInQ.Manuscript.RC.AuxInputs

open ZInQ.Manuscript AddressGenuine PrintsAnalytic Symbols Wiring ZInQ.Manuscript.RC.Even
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

variable {ℓ : ℕ} {W : WData ℓ} {L : CentralNormalization (Ecurve ℓ)}
variable {τ : SqClass (conductor W.S)}

theorem evenAp (hS : SupportSpec W) :
    ApEven (evenTypes W.S hS.1) (fun p => (Ecurve ℓ).LFunction p) := by
  have hcov : ∀ p : ℕ, p.Prime → p ∣ 6 * (ℓ : ℤ).natAbs → p ∣ (evenTypes W.S hS.1).m := by
    intro p hp hpd
    apply (conductor_support hS.1 hS.2.1 hp).2
    rw [Int.natAbs_natCast] at hpd
    rcases hp.dvd_mul.mp hpd with h6 | hℓ
    · rcases hp.dvd_mul.mp (show p ∣ 2 * 3 from h6) with h2 | h3
      · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2]
        exact hS.2.1
      · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3]
        exact hS.2.2.1
    · exact hS.2.2.2 p hp hℓ
  simpa only [Int.cast_natCast] using FrobCount.apEven_curve_typeData (evenTypes W.S hS.1) (ℓ : ℤ) hcov

/-- All-index coefficients of the normalized source after the original
support and total squareclass sieve (tex 7793–7801, 8148–8155, 9471–9483).
The condition is on the squareclass of the whole index, including its
square factor, and no later exclusions occur here. -/
def EvenSource.sievedCoeff (P : EvenSource W L τ) (n : ℕ) : ℂ :=
  if n ≠ 0 ∧ n.Coprime (conductor W.S) ∧ sqClassOf (conductor W.S) (n : ℤ) = τ then
    hiwCoeff P.phaseData.g n / hiwCoeff P.phaseData.g P.D₀ else 0

/-- A realization at one operator budget, on the existing (O.12)
interfaces. The archimedean and coefficient-place maps agree on the
same Fourier coefficients. Rescaling by an integer power of two for
integrality shifts the depth by the same amount. -/
def EvenSource.BudgetRealization (P : EvenSource W L τ) (hS : SupportSpec W) (B : ℕ) : Prop :=
  letI : NeZero (conductor W.S) := ⟨(conductor_pos hS.1).ne'⟩
  ∃ (X : GaloisConstituentModel (evenTypes W.S hS.1) P.reading
      (fun p => (Ecurve ℓ).LFunction p) B (typChar (conductor W.S)))
    (F : O12.FourierData X) (S : O12.ThetaData F),
    CharZero X.K ∧ O12.LocalInput F ∧
    ∃ (K₀ : Type) (_ : Field K₀) (eC : K₀ →+* ℂ) (eK : K₀ →+* X.K)
      (c : ℕ → K₀) (k : ℤ),
      S.δ = P.δ + k ∧ S.admissible = evenFilter W.S τ ∧
      (∀ n, eC (c n) = P.sievedCoeff n) ∧
      ∀ n, algebraMap X.O X.K (S.a n) = (2 : X.K) ^ k * eK (c n)

/-- The finite budget models all read one fixed App E source and depth.
The two existing (O.12) inputs give fixed-set factorization and all
three graph rules, without using a common finite budget for all graphs. -/
theorem EvenSource.rules_and_seed (P : EvenSource W L τ) (hS : SupportSpec W)
    (hReal : ∀ B, P.BudgetRealization hS B) :
    CoefficientRules (evenSign W.S) (P.symbol hS) ∧
      ∃ Γ, IsUnitSeed (evenSign W.S) (P.symbol hS) Γ := by
  let _ : NeZero (conductor W.S) := ⟨(conductor_pos hS.1).ne'⟩
  have htyp : IsTypeChar (evenTypes W.S hS.1) (typChar (conductor W.S)) :=
    isTypeChar_typeData _ (conductor_pos hS.1) _
  have hmodel (B : ℕ) : ∃ X : GaloisConstituentModel (evenTypes W.S hS.1) P.reading
      (fun p => (Ecurve ℓ).LFunction p) B (typChar (conductor W.S)), X.Inputs := by
    obtain ⟨X, F, S, hchar, hlocal, _⟩ := hReal B
    let _ : CharZero X.K := hchar
    exact ⟨X, O12.inputs_of_theta S hlocal htyp⟩
  choose X hX using hmodel
  exact ⟨coefficientRules_of_galoisConstituents X hX htyp (evenAp hS),
    P.unitSeed hS (fun B => (X B).fixedU_of_constituents (hX B) htyp)⟩

/-- A choice of one fixed source at each type for which App E admits a
nonzero reference. The finite alphabet is specified independently. -/
abbrev SourceFamily (W : WData ℓ) (L : CentralNormalization (Ecurve ℓ)) :=
  ∀ τ : SqClass (conductor W.S), HasReference W τ → EvenSource W L τ

theorem sourceFamily_of_prints (hS : SupportSpec W) (hL : L.Lstar = W.Lstar) (hℓ : 0 < ℓ)
    (hWN : WaldspurgerNonvanishing) (hW : WaldspurgerCor2) (hR : AppE.RamseyAlgebraicModel)
    (hB : PoleS12.BCDTThmA) (hH : HasseConvergence)
    (hcond : ∀ (N : ℕ) (w : ℤ), RootNumberAt (Ecurve ℓ) N w →
      ∀ p : ℕ, p.Prime → p ∣ N → p ∈ W.S) (h9 : EvenLowerBound (Ecurve ℓ) L) :
    Nonempty (SourceFamily W L) :=
  ⟨fun _ hRef => Classical.choice (evenSource_of_prints hS hL hℓ hWN hW hR hB hH hcond h9 hRef)⟩

/-- Where no nonzero negative reference exists there is no even unit to
prepare. The binary reading is identically zero on that branch. -/
def symbolFamily (P : SourceFamily W L) (hS : SupportSpec W) (τ : SqClass (conductor W.S)) :
    Config (SqClass (conductor W.S)) → ZMod 2 := by
  classical
  exact if h : HasReference W τ then (P τ h).symbol hS else fun _ => 0

theorem lstar_zero_of_noReference (h : ¬ HasReference W τ) {D : ℕ} (hD : evenFilter W.S τ D) :
    W.Lstar (-(D : ℤ)) = 0 := by
  by_contra hn
  exact h ⟨D, hD, hn⟩

theorem symbolFamily_rules (P : SourceFamily W L) (hS : SupportSpec W)
    (hReal : ∀ τ h B, (P τ h).BudgetRealization hS B) :
    ∀ τ, CoefficientRules (evenSign W.S) (symbolFamily P hS τ) := by
  classical
  intro τ
  by_cases h : HasReference W τ
  · simpa only [symbolFamily, dite_eq_left h] using ((P τ h).rules_and_seed hS (hReal τ h)).1
  · rw [symbolFamily, dite_eq_right h]
    exact ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => zero_add 0, fun _ _ _ _ _ _ => rfl⟩

theorem symbolFamily_off (P : SourceFamily W L) (hS : SupportSpec W) :
    ∀ τ, VanishesOffFilter (symbolFamily P hS τ) τ := by
  classical
  intro τ
  by_cases h : HasReference W τ
  · simpa only [symbolFamily, dite_eq_left h] using (P τ h).symbol_off hS
  · rw [symbolFamily, dite_eq_right h]
    exact fun _ he => (zero_ne_one he).elim

theorem symbolFamily_seed (P : SourceFamily W L) (hS : SupportSpec W)
    (hL : LstarTarget W.toRCData)
    (hReal : ∀ τ h B, (P τ h).BudgetRealization hS B)
    (τ : SqClass (conductor W.S)) (ht : PreparedType W (evenTypes W.S hS.1) τ) :
    ∃ Γ, IsUnitSeed (evenSign W.S) (symbolFamily P hS τ) Γ := by
  classical
  have h := prepared_hasReference W hS hL ht
  simpa only [symbolFamily, dite_eq_left h] using ((P τ h).rules_and_seed hS (hReal τ h)).2

/-- The manuscript's certificate on the negative squarefree filter.
This defines the new data predicate; it does not infer anything from
the arbitrary predicate field of a pre-existing `WData`. -/
def partitionCertificate (W : WData ℓ) (hS : SupportSpec W)
    (A : SqClass (conductor W.S) → Config (SqClass (conductor W.S)) → ZMod 2) (d : ℤ) : Prop :=
  d < 0 ∧ Squarefree d ∧ (∀ p ∈ W.S, ¬ (p : ℤ) ∣ d) ∧
    IsPartitionable (evenSign W.S) (A (primeConfig d.natAbs.primeFactors (evenTypes W.S hS.1).typ).total)
      (primeConfig d.natAbs.primeFactors (evenTypes W.S hS.1).typ)

def withPartitionCertificate (W : WData ℓ) (hS : SupportSpec W)
    (A : SqClass (conductor W.S) → Config (SqClass (conductor W.S)) → ZMod 2) : WData ℓ :=
  { W with Partitionable := partitionCertificate W hS A }

theorem withPartitionCertificate_eq (hS : SupportSpec W)
    (A : SqClass (conductor W.S) → Config (SqClass (conductor W.S)) → ZMod 2)
    (h : W.Partitionable = partitionCertificate W hS A) :
    withPartitionCertificate W hS A = W := by
  cases W with
  | mk V part => exact congrArg (WData.mk V) h.symm

theorem auxFactorInputs_of_realizations (P : SourceFamily W L) (hS : SupportSpec W)
    (hL : LstarTarget W.toRCData) (hReal : ∀ τ h B, (P τ h).BudgetRealization hS B) :
    AuxFactorInputs (withPartitionCertificate W hS (symbolFamily P hS)) := by
  let _ : NeZero (conductor W.S) := ⟨(conductor_pos hS.1).ne'⟩
  exact ⟨SqClass (conductor W.S), inferInstance, inferInstance, evenSign W.S, evenTypes W.S hS.1,
    symbolFamily P hS, fun _ hp => (conductor_support hS.1 hS.2.1 hp).1,
    symbolFamily_rules P hS hReal, symbolFamily_off P hS, symbolFamily_seed P hS hL hReal,
    fun _ hd hsf hc hpart => ⟨hd, hsf, hc, hpart⟩⟩

/-- An already constructed data record only needs the forward
certificate comparison. Neither equality nor a change to its predicate
is needed in the conclusion. -/
theorem auxFactorInputs_of_compatible_partition (P : SourceFamily W L) (hS : SupportSpec W)
    (hL : LstarTarget W.toRCData) (hReal : ∀ τ h B, (P τ h).BudgetRealization hS B)
    (hpart : ∀ d, partitionCertificate W hS (symbolFamily P hS) d → W.Partitionable d) :
    AuxFactorInputs W := by
  obtain ⟨G, iG, fG, ε, T, A, hm, hr, hf, hu, hcert⟩ :=
    auxFactorInputs_of_realizations P hS hL hReal
  exact ⟨G, iG, fG, ε, T, A, hm, hr, hf, hu,
    fun d hd hsf hc hp => hpart d (hcert d hd hsf hc hp)⟩

theorem auxFactor_of_realizations (P : SourceFamily W L) (hS : SupportSpec W)
    (hL : LstarTarget W.toRCData) (hReal : ∀ τ h B, (P τ h).BudgetRealization hS B) :
    ∃ A₀, AuxFactor (withPartitionCertificate W hS (symbolFamily P hS)) A₀ :=
  auxFactor_of_inputs _ hS (auxFactorInputs_of_realizations P hS hL hReal)

theorem f3Target_of_realizations (P : SourceFamily W L) (hS : SupportSpec W)
    (hL : LstarTarget W.toRCData) (hReal : ∀ τ h B, (P τ h).BudgetRealization hS B)
    (prints : Prints) (hKum : KummerCorankZero) (hHL : Nonvanishing.HoffsteinLuo)
    (hTS : Nonvanishing.BFHTwistSign) (hRN : Nonvanishing.FromRC8.RootNumberExists) (hℓ : 0 < ℓ)
    (hPrep : PreparedSpec W) {C₁ : ℤ}
    (hUpper : EvenUpper33b (withPartitionCertificate W hS (symbolFamily P hS)) C₁) :
    F3Target (withPartitionCertificate W hS (symbolFamily P hS)) := by
  obtain ⟨A₀, hAux⟩ := auxFactor_of_realizations P hS hL hReal
  exact f3Target_of _ prints hKum hHL hTS hRN hℓ hL hS hPrep hAux hUpper

#print axioms evenAp
#print axioms EvenSource.rules_and_seed
#print axioms sourceFamily_of_prints
#print axioms lstar_zero_of_noReference
#print axioms symbolFamily_rules
#print axioms symbolFamily_off
#print axioms symbolFamily_seed
#print axioms withPartitionCertificate_eq
#print axioms auxFactorInputs_of_realizations
#print axioms auxFactorInputs_of_compatible_partition
#print axioms auxFactor_of_realizations
#print axioms f3Target_of_realizations

end ZInQ.Manuscript.RC.AuxInputs
