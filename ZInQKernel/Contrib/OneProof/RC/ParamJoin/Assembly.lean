import ZInQKernel.Contrib.OneProof.RC.ParamJoin.RingValues

/-! Equation (3.4) for the rough companions, with both sets of values supplied
by the fixed chart (tex 2404–2439; provenance (c)). -/

noncomputable section

open ZInQ.Manuscript ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.SelmerTwoPower
  ZInQ.Manuscript.RC.PreparedParam
  ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd

namespace ZInQ.Manuscript.RC.ParamJoin

/-- The conductor-one values in the exact slot used by the (3.4) assembly. -/
theorem genus_values {ℓ : ℕ} {W : WData ℓ} (P : Prints) (hℓ : 0 < ℓ)
    {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel (Ecurve ℓ)) :
      Subgroup (GL (Fin 2) ℝ)) 2}
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = ((Ecurve ℓ).LFunction n : ℂ))
    {Lat : PeriodPair} (hLat : IsLatticeOf (Ecurve ℓ) Lat)
    {κ : ℂ} (hκ : IsParamScale (newformLevel (Ecurve ℓ)) f Lat κ) (hr : ∃ c : ℚ, (c : ℂ) = κ)
    (hCM : letI : NeZero (newformLevel (Ecurve ℓ)) := ⟨(Gz34Instance.curve_form P hℓ).1.ne'⟩
           CMFieldOfDefinition (X0Branch.model (newformLevel (Ecurve ℓ))))
    (hpartner : IsGenusPartner ℓ W.hstar)
    (hlevel0 : ∀ p : ℕ, p.Prime → p ∣ 2 * newformLevel (Ecurve ℓ) → p ∈ S0 ℓ) :
    ∀ h (hp : Prepared (Ecurve ℓ) W.hstar h),
      StageSelector.PreparedParamValue (Ecurve ℓ) f Lat κ (Gz34Instance.curve_form P hℓ).1
        (Gz34Instance.genusPartner_of_support hpartner hlevel0) hp := by
  let _ := Gz34Instance.curve_elliptic hℓ
  let _ : NeZero (newformLevel (Ecurve ℓ)) := ⟨(Gz34Instance.curve_form P hℓ).1.ne'⟩
  exact genusParamValues P hℓ hCM (algebraicParametrizationAtScale f hf hLat hκ hr) hpartner hlevel0

/-- Both native index families are the readings of the existing selectors,
whose value proofs now come from the constructed modular chart. -/
theorem gz34CompAt {ℓ : ℕ} {W : WData ℓ} (P : Prints) (hℓ : 0 < ℓ)
    {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel (Ecurve ℓ)) :
      Subgroup (GL (Fin 2) ℝ)) 2}
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = ((Ecurve ℓ).LFunction n : ℂ))
    {Lat : PeriodPair} (hLat : IsLatticeOf (Ecurve ℓ) Lat) (hNC : IsNonCMLattice Lat)
    {κ : ℂ} (hκ : IsParamScale (newformLevel (Ecurve ℓ)) f Lat κ) (hr : ∃ c : ℚ, (c : ℂ) = κ)
    (hCM : letI : NeZero (newformLevel (Ecurve ℓ)) := ⟨(Gz34Instance.curve_form P hℓ).1.ne'⟩
           CMFieldOfDefinition (X0Branch.model (newformLevel (Ecurve ℓ))))
    (N : Even.CentralNormalization (Ecurve ℓ)) (hN : N.Lstar = W.Lstar)
    (hElkikMD : ∃ q : ℚ, q ≠ 0 ∧ (q : ℂ) = Lstar (Ecurve ℓ) Lat W.hstar)
    (hpartner : IsGenusPartner ℓ W.hstar)
    (hlevel0 : ∀ p : ℕ, p.Prime → p ∣ 2 * newformLevel (Ecurve ℓ) → p ∈ S0 ℓ)
    (hS : SupportSpec W) (hprepared : PreparedSpec W)
    (hstarS : ∀ p ∈ W.hstar.natAbs.primeFactors, p ∈ W.S)
    (hpreparedLoc : ∀ h, W.prepared h →
      ∀ p : ℕ, p.Prime → p ∣ 2 * newformLevel (Ecurve ℓ) → SquareAt p h)
    (hjg : W.jgen = jgenOf (Ecurve ℓ) f Lat κ W.hstar
      (Gz34Instance.selectGenus (Gz34Instance.curve_form P hℓ).1
        (Gz34Instance.genusPartner_of_support hpartner hlevel0)
        (genus_values P hℓ hf hLat hκ hr hCM hpartner hlevel0)))
    (hjr : W.jrc = jrcOf (Ecurve ℓ) f Lat κ
      (Gz34Instance.selectRing (Gz34Instance.curve_form P hℓ).1
        (ring_values P hℓ hf hLat hκ hr hCM (s := W.hstar))))
    (hArtin : ArtinFactorization) (hRN : Nonvanishing.FromRC8.RootNumberExists) :
    Gz34CompAt W 0 :=
  Gz34Instance.gz34CompAt_of_paramValues P hℓ hf hLat hNC hκ N hN hElkikMD hpartner
    hlevel0 hS hprepared hstarS hpreparedLoc (genus_values P hℓ hf hLat hκ hr hCM hpartner hlevel0)
    (ring_values P hℓ hf hLat hκ hr hCM (s := W.hstar)) hjg hjr hArtin hRN

#print axioms genus_values
#print axioms gz34CompAt

end ZInQ.Manuscript.RC.ParamJoin
