import ZInQKernel.Contrib.OneProof.RC.Gz34Instance.Curve
import ZInQKernel.Contrib.OneProof.RC.Gz34Instance.Selector
import ZInQKernel.Contrib.OneProof.RC.Wiring.FinalFamily

/-! The actual inputs to (3.4), tex 2404–2440, and its use at 10172–10178.
The assembly applies the existing CST/Kolyvagin route. The interface
equalities and assembly are on-the-spot (c). -/

noncomputable section

open ZInQ.Manuscript ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.SelmerTwoPower
  ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd

namespace ZInQ.Manuscript.RC.Gz34Instance

section Assembly

variable {ℓ : ℕ} {W : WData ℓ} (P : Prints) (hℓ : 0 < ℓ)
  {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel (Ecurve ℓ)) :
    Subgroup (GL (Fin 2) ℝ)) 2}
  (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = ((Ecurve ℓ).LFunction n : ℂ))
  {Lat : PeriodPair} (hLat : IsLatticeOf (Ecurve ℓ) Lat) (hNC : IsNonCMLattice Lat)
  {κ : ℂ} (hκ : IsParamScale (newformLevel (Ecurve ℓ)) f Lat κ)
  (N : Even.CentralNormalization (Ecurve ℓ)) (hN : N.Lstar = W.Lstar)
  (hElkikMD : ∃ q : ℚ, q ≠ 0 ∧ (q : ℂ) = Lstar (Ecurve ℓ) Lat W.hstar)
  (hpartner : IsGenusPartner ℓ W.hstar)
  (hlevel0 : ∀ p : ℕ, p.Prime → p ∣ 2 * newformLevel (Ecurve ℓ) → p ∈ S0 ℓ)
  (hS : SupportSpec W)
  (hprepared : PreparedSpec W)
  (hstarS : ∀ p ∈ W.hstar.natAbs.primeFactors, p ∈ W.S)
  (hpreparedLoc : ∀ h, W.prepared h →
    ∀ p : ℕ, p.Prime → p ∣ 2 * newformLevel (Ecurve ℓ) → SquareAt p h)

variable
  (halgG : ∀ h (hp : Prepared (Ecurve ℓ) W.hstar h),
    StageSelector.PreparedParamValue (Ecurve ℓ) f Lat κ (curve_form P hℓ).1
      (genusPartner_of_support hpartner hlevel0) hp)
  (halgR : ∀ h k (hp : Prepared (Ecurve ℓ) W.hstar h) (hk : Companion (Ecurve ℓ) Lat W.hstar h k),
    RingParamValue (Ecurve ℓ) f Lat κ (curve_form P hℓ).1 hp hk)
  (hjg : W.jgen = jgenOf (Ecurve ℓ) f Lat κ W.hstar
    (selectGenus (curve_form P hℓ).1 (genusPartner_of_support hpartner hlevel0) halgG))
  (hjr : W.jrc = jrcOf (Ecurve ℓ) f Lat κ (selectRing (curve_form P hℓ).1 halgR))

include hlevel0 hS in
private theorem level_mem_support :
    ∀ p : ℕ, p.Prime → p ∣ 2 * newformLevel (Ecurve ℓ) → p ∈ W.S := by
  intro p hp hd
  have hm := hlevel0 p hp hd
  simp only [S0, Finset.mem_insert] at hm
  rcases hm with rfl | rfl | hmem
  · exact hS.2.1
  · exact hS.2.2.1
  · exact hS.2.2.2 p hp (Nat.dvd_of_mem_primeFactors hmem)

include hElkikMD in
private theorem omegaMinus_ne_zero_of_partner : omegaMinus Lat ≠ 0 := by
  obtain ⟨q, hq0, hq⟩ := hElkikMD
  apply omegaMinus_ne_zero_of (E := Ecurve ℓ) (a := W.hstar)
  rw [← hq]
  exact_mod_cast hq0

variable (hk0 : W.kfin < 0) (hksq : Squarefree W.kfin) (hk4 : W.kfin % 4 = 1)
  (hk2N : ∀ p : ℕ, p.Prime → p ∣ 2 * newformLevel (Ecurve ℓ) → UnitSquareAt p W.kfin)
  (hkcop : IsCoprime W.kfin W.hstar)

/-- Assemble the actual GenusOdd instance from the two algebraic value
inputs and the named curve, filter, normalization and index inputs. -/
def instanceOfParamValues : GenusOddInstance W where
  hE := curve_elliptic hℓ
  f := f
  hf := hf
  Lat := Lat
  hLat := hLat
  hNC := hNC
  κ := κ
  hκ := hκ
  N := N
  hN := hN
  hElkikMD := hElkikMD
  hgp := genusPartner_of_support hpartner hlevel0
  selG := selectGenus (curve_form P hℓ).1 (genusPartner_of_support hpartner hlevel0) halgG
  selR := selectRing (curve_form P hℓ).1 halgR
  hselG := fun _ hp _ => selectGenus_isSome _ _ _ hp
  hselR := fun _ _ hp _ hk => selectRing_isSome _ _ hp hk
  hprep := prepared_of_support hprepared hpartner.1.ne hstarS hpreparedLoc
  hjg := hjg
  hjr := hjr
  hcomp := fun h _ hp hk => companion_of_rough (level_mem_support hlevel0 hS)
    hpartner.1.ne (omegaMinus_ne_zero_of_partner hElkikMD)
    (prepared_of_support hprepared hpartner.1.ne hstarS hpreparedLoc h hp) hk
  hk0 := hk0
  hksq := hksq
  hk4 := hk4
  hk2N := hk2N
  hkcop := hkcop

include P hℓ hf hLat hNC hκ N hN hElkikMD hpartner hlevel0 hS
  hprepared hstarS hpreparedLoc halgG halgR hjg hjr in
/-- Equation (3.4) on the rough companions with period constant zero.
This consequence uses only the rough companion inputs. -/
theorem gz34CompAt_of_paramValues (hArtin : ArtinFactorization)
    (hRN : Nonvanishing.FromRC8.RootNumberExists) : Gz34CompAt W 0 := by
  have := curve_elliptic hℓ
  have hscale : LstarScaled (Ecurve ℓ) W.Lstar := by
    rw [← hN]
    refine lstarScaled_of_centralNormalization N fun d hd => ?_
    exact cont_of_rootNumberExists hRN
      (PrintsAnalytic.qtwist_isElliptic (E := Ecurve ℓ) (by exact_mod_cast hd.ne))
  have hΩ := omegaMinus_ne_zero_of_partner hElkikMD
  obtain ⟨q, -, hq⟩ := hElkikMD
  have hG := genusPartner_of_support hpartner hlevel0
  have hgz := gzEveryCompanion_of_scaled_artin P hArtin (E := Ecurve ℓ) rfl rfl
    hf hLat hNC hκ hG ⟨q, hq⟩
    (selectGenus (curve_form P hℓ).1 hG halgG) (selectRing (curve_form P hℓ).1 halgR)
    (fun _ hp _ => selectGenus_isSome _ _ _ hp)
    (fun _ _ hp _ hk => selectRing_isSome _ _ hp hk) hscale
  intro h k hp hz hk
  have hp' := prepared_of_support hprepared hpartner.1.ne hstarS hpreparedLoc h hp
  have hk' := companion_of_rough (level_mem_support hlevel0 hS) hpartner.1.ne hΩ hp' hk
  rw [hjg, hjr]
  exact hgz h k hp' hz hk'

include P hℓ hf hLat hNC hκ N hN hElkikMD hpartner hlevel0 hS
  hprepared hstarS hpreparedLoc halgG halgR hjg hjr hk0 hksq hk4 hk2N hkcop in
/-- Equation (3.4) with the common period constant, also at the final `k`. -/
theorem gz34Target_of_paramValues (hArtin : ArtinFactorization)
    (hRN : Nonvanishing.FromRC8.RootNumberExists) : Gz34Target W :=
  gz34Target_of_genusOdd P hArtin hRN
    (instanceOfParamValues P hℓ hf hLat hNC hκ N hN hElkikMD hpartner hlevel0 hS
      hprepared hstarS hpreparedLoc halgG halgR hjg hjr hk0 hksq hk4 hk2N hkcop)

end Assembly

#print axioms level_mem_support
#print axioms omegaMinus_ne_zero_of_partner
#print axioms instanceOfParamValues
#print axioms gz34CompAt_of_paramValues
#print axioms gz34Target_of_paramValues

end ZInQ.Manuscript.RC.Gz34Instance
