import ZInQKernel.Contrib.OneProof.RC.PreparedParam.Descent
import ZInQKernel.Contrib.OneProof.RC.Gz34Instance.Assembly
import ZInQKernel.Contrib.OneProof.RC.StageKummer.Selector

/-! Install the same conductor-one value theorem at the two existing
consumer interfaces (on-the-spot (c)). -/

noncomputable section

open ZInQ.Manuscript ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.SelmerTwoPower
  ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd

namespace ZInQ.Manuscript.RC.PreparedParam

/-- The value theorem at the actual curve, in the exact `halgG` slot of
`Gz34Instance.instanceOfParamValues` and `gz34CompAt_of_paramValues`. -/
theorem genusParamValues {ℓ : ℕ} {W : WData ℓ} (P : Prints) (hℓ : 0 < ℓ)
    [NeZero (newformLevel (Ecurve ℓ))] {X : X0Model (newformLevel (Ecurve ℓ))}
    {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel (Ecurve ℓ)) :
      Subgroup (GL (Fin 2) ℝ)) 2}
    {Lat : PeriodPair} {κ : ℂ} (hCM : CMFieldOfDefinition X)
    (hπ : letI := Gz34Instance.curve_elliptic hℓ
          AlgebraicParametrizationAtScale (Ecurve ℓ) X f Lat κ)
    (hpartner : IsGenusPartner ℓ W.hstar)
    (hlevel0 : ∀ p : ℕ, p.Prime → p ∣ 2 * newformLevel (Ecurve ℓ) → p ∈ S0 ℓ) :
    ∀ h (hp : Prepared (Ecurve ℓ) W.hstar h),
      StageSelector.PreparedParamValue (Ecurve ℓ) f Lat κ (Gz34Instance.curve_form P hℓ).1
        (Gz34Instance.genusPartner_of_support hpartner hlevel0) hp := by
  let _ := Gz34Instance.curve_elliptic hℓ
  exact preparedParamValues hCM hπ _ _

/-- The Kummer selector needs the same values only at its admissible
nonwitness holes. Its original witness remains as supplied in the setup. -/
theorem missingParamValues {ℓ : ℕ} {W : WData ℓ} {I : GenusOddInstance W} {L : ℕ}
    [NeZero (newformLevel (Ecurve ℓ))] {X : X0Model (newformLevel (Ecurve ℓ))}
    (s : StageKummer.Setup I L) (hCM : CMFieldOfDefinition X)
    (hπ : letI := s.eE; AlgebraicParametrizationAtScale (Ecurve ℓ) X I.f I.Lat I.κ) :
    StageKummer.MissingParamValues s := by
  let _ := s.eE
  intro D h _ _
  exact preparedParamValues hCM hπ (StageKummer.positiveLevel s) I.hgp D
    (I.hprep D (StageKummer.preparedGlue s h.choose D h.choose_spec))

/-- Apply the existing rough companion assembly with the conductor-one
selector obtained from the same modular morphism. The index equality
uses this selector, and the conductor-`|h|` values remain separate. -/
theorem gz34CompAt_of_scaledParametrization {ℓ : ℕ} {W : WData ℓ} (P : Prints) (hℓ : 0 < ℓ)
    [NeZero (newformLevel (Ecurve ℓ))] {X : X0Model (newformLevel (Ecurve ℓ))}
    {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel (Ecurve ℓ)) :
      Subgroup (GL (Fin 2) ℝ)) 2}
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = ((Ecurve ℓ).LFunction n : ℂ))
    {Lat : PeriodPair} (hLat : IsLatticeOf (Ecurve ℓ) Lat) (hNC : IsNonCMLattice Lat)
    {κ : ℂ} (hκ : IsParamScale (newformLevel (Ecurve ℓ)) f Lat κ)
    (hCM : CMFieldOfDefinition X)
    (hπ : letI := Gz34Instance.curve_elliptic hℓ
          AlgebraicParametrizationAtScale (Ecurve ℓ) X f Lat κ)
    (N : Even.CentralNormalization (Ecurve ℓ)) (hN : N.Lstar = W.Lstar)
    (hElkikMD : ∃ q : ℚ, q ≠ 0 ∧ (q : ℂ) = Lstar (Ecurve ℓ) Lat W.hstar)
    (hpartner : IsGenusPartner ℓ W.hstar)
    (hlevel0 : ∀ p : ℕ, p.Prime → p ∣ 2 * newformLevel (Ecurve ℓ) → p ∈ S0 ℓ)
    (hS : SupportSpec W) (hprepared : PreparedSpec W)
    (hstarS : ∀ p ∈ W.hstar.natAbs.primeFactors, p ∈ W.S)
    (hpreparedLoc : ∀ h, W.prepared h →
      ∀ p : ℕ, p.Prime → p ∣ 2 * newformLevel (Ecurve ℓ) → SquareAt p h)
    (halgR : ∀ h k (hp : Prepared (Ecurve ℓ) W.hstar h) (hk : Companion (Ecurve ℓ) Lat W.hstar h k),
      Gz34Instance.RingParamValue (Ecurve ℓ) f Lat κ (Gz34Instance.curve_form P hℓ).1 hp hk)
    (hjg : W.jgen = jgenOf (Ecurve ℓ) f Lat κ W.hstar
      (Gz34Instance.selectGenus (Gz34Instance.curve_form P hℓ).1
        (Gz34Instance.genusPartner_of_support hpartner hlevel0)
        (genusParamValues P hℓ hCM hπ hpartner hlevel0)))
    (hjr : W.jrc = jrcOf (Ecurve ℓ) f Lat κ
      (Gz34Instance.selectRing (Gz34Instance.curve_form P hℓ).1 halgR))
    (hArtin : ArtinFactorization) (hRN : Nonvanishing.FromRC8.RootNumberExists) :
    Gz34CompAt W 0 :=
  Gz34Instance.gz34CompAt_of_paramValues P hℓ hf hLat hNC hκ N hN hElkikMD hpartner
    hlevel0 hS hprepared hstarS hpreparedLoc (genusParamValues P hℓ hCM hπ hpartner hlevel0)
    halgR hjg hjr hArtin hRN


end ZInQ.Manuscript.RC.PreparedParam
