import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.Decomp
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.LevelGood
import ZInQKernel.Contrib.OneProof.RC.ElkikMD.Birch
import ZInQKernel.Contrib.OneProof.RC.ElkikMD.QuadraticFourier
import ZInQKernel.Contrib.OneProof.RC.TwistDictionary.Dictionary

/-! The remaining input for the actual curve is the cusp comparison with its period lattice. -/

noncomputable section

open Complex HeckeRing.GL2
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST
  ZInQ.Contrib.CloudB3RC53.GenusOdd

namespace ZInQ.Manuscript.RC.ElkikMD

/-- Extend the existing prime comparison of Jacobi and Kronecker symbols to every positive
coefficient index. -/
theorem chiD_eq_kronecker_pos {d : ℤ} (hd : d % 4 = 1) {n : ℕ} (hn : n ≠ 0) :
    chiD d n = PrintsAnalytic.kronecker d n := by
  induction n using Nat.recOnMul with
  | zero => exact (hn rfl).elim
  | one => simp [chiD, TwistDictionary.kronecker_one]
  | prime p hp => exact chiD_eq_kronecker hd hp
  | mul a b ha hb =>
    have ha0 : a ≠ 0 := fun h => hn (by simp [h])
    have hb0 : b ≠ 0 := fun h => hn (by simp [h])
    rw [show chiD d (a * b) = chiD d a * chiD d b by simp [chiD, jacobiSym.mul_left],
      ha ha0, hb hb0, TwistDictionary.kronecker_mul d ha0 hb0]

/-- The genus partner's twisted coefficients agree with the Jacobi twist of the newform,
including at primes of the level and primes of the discriminant. -/
theorem genusPartner_twisted_coeff {E : WeierstrassCurve ℚ} [E.IsElliptic] {d : ℤ}
    [NeZero d.natAbs] [NeZero (newformLevel E)]
    {f : Newform (newformLevel E) 2} (hf : PrintsAnalytic.IsNewformOf E f)
    (hgp : GenusPartner E d) (n : ℕ) (hn : 0 < n) :
    jacobiCharacter d.natAbs n * PrintsAnalytic.nfCoeff f n =
      PrintsAnalytic.lcoeff (qtwist E d) n := by
  have hD : PrintsAnalytic.IsFundamentalDiscriminant d :=
    ⟨by have := hgp.1; omega, Or.inl ⟨hgp.2.1, hgp.2.2.1⟩⟩
  have hDN : IsCoprime d (newformLevel E : ℤ) := by
    apply Int.isCoprime_iff_gcd_eq_one.mpr
    change Nat.Coprime d.natAbs (newformLevel E)
    apply Nat.coprime_of_dvd'
    intro p hp hpd hpN
    exact ((hgp.2.2.2.2.1 p hp (dvd_mul_of_dvd_right hpN 2)).1 (Int.natCast_dvd.mpr hpd)).elim
  rw [← Int.cast_natCast, jacobiCharacter_intCast]
  change (chiD d n : ℂ) * PrintsAnalytic.nfCoeff f n = _
  rw [chiD_eq_kronecker_pos hgp.2.1 hn.ne', hf.2 n hn]
  exact (TwistDictionary.twistDictionary E inferInstance _ f hf d hD hDN n hn).symm

/-- For the manuscript curve and its actual genus partner, the output has exactly the type of
`Gz34Instance`'s `hElkikMD`. The residual geometric assertion is `hAJ` at rational scale `κ`,
in addition to realizing Elkik's printed objects and supplying the print. The finite Fourier
evaluation, the analytic Birch formula and partner nonvanishing are all proved in Lean. -/
theorem hElkikMD_of_maninDrinfeld {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] {d : ℤ}
    [NeZero (newformLevel (Ecurve ℓ))] {J : Type*} [AddCommGroup J]
    {cuspClass : OnePoint ℚ → J} (hMD : ManinDrinfeld (newformLevel (Ecurve ℓ)) cuspClass)
    {f : Newform (newformLevel (Ecurve ℓ)) 2} (hf : PrintsAnalytic.IsNewformOf (Ecurve ℓ) f)
    (hgp : GenusPartner (Ecurve ℓ) d) (Lat : PeriodPair) {κ : ℚ} (hκ : κ ≠ 0)
    (φ : J →+ ℂ ⧸ Lat.lattice.toAddSubgroup)
    (hAJ : ∀ a < d.natAbs, chiD d a ≠ 0 → φ (cuspClass (((a : ℚ) / d.natAbs : ℚ) : OnePoint ℚ)) =
      QuotientAddGroup.mk' Lat.lattice.toAddSubgroup ((κ : ℂ) * cuspSymbol f.toCuspForm ((a : ℚ) / d.natAbs))) :
    ∃ q : ℚ, q ≠ 0 ∧ (q : ℂ) = Lstar (Ecurve ℓ) Lat d := by
  let M := d.natAbs
  let N := newformLevel (Ecurve ℓ)
  let : NeZero M := ⟨Int.natAbs_ne_zero.mpr hgp.1.ne⟩
  let : NeZero N := inferInstanceAs (NeZero (newformLevel (Ecurve ℓ)))
  have hdabs : (M : ℤ) = -d := by
    have hd := hgp.1
    dsimp [M]
    omega
  have hMmod : M % 4 = 3 := by have := hgp.2.1; omega
  have hMsq : Squarefree M := Int.squarefree_natAbs.mpr hgp.2.2.1
  obtain ⟨ε, hε, hDFT⟩ := jacobiCharacter_fourier hMmod hMsq
  let L := N * M * M
  let : NeZero L := ⟨mul_ne_zero (mul_ne_zero (NeZero.ne N) (NeZero.ne M)) (NeZero.ne M)⟩
  have hML : M * M ∣ L := by dsimp [L]; rw [mul_assoc]; exact dvd_mul_left _ _
  have hNL : N * M ∣ L := dvd_mul_right _ _
  let τ : ℂ := (ε : ℂ) * (Real.sqrt (M : ℝ) : ℂ) * I
  have hτ : τ ≠ 0 := by
    have he : (ε : ℂ) ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
    have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
    have hM' : (0 : ℝ) < M := by exact_mod_cast hM
    exact mul_ne_zero (mul_ne_zero he (ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hM').ne')) I_ne_zero
  obtain ⟨F, hF, -⟩ := analyticRank_zero_iff.mp hgp.2.2.2.2.2
  have hB := quadraticCuspSum_eq_twisted_value (d := d) f.toCuspForm (jacobiCharacter M)
    hNL hML hτ hDFT (genusPartner_twisted_coeff hf hgp) ⟨F, hF⟩
  have hreal : (M : ℝ) = |(d : ℝ)| := by
    rw [abs_of_neg (by exact_mod_cast hgp.1)]
    exact_mod_cast hdabs
  apply hElkikMD_of_cuspidalSubgroup hgp hMD Lat f.toCuspForm hκ φ hAJ ε hε
  rw [hB]
  dsimp [τ]
  rw [hreal]
  ring

/-- The newform supplied by the existing modularity input is at the least level of the
assembly and has the same function as its given `Γ₀` cusp form (tex 1779–1787). -/
theorem curveNewform_eq_assemblyForm {ℓ : ℕ} [(Ecurve ℓ).IsElliptic]
    [NeZero (newformLevel (Ecurve ℓ))] (hM : PrintsAnalytic.ModularNewform)
    (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel (Ecurve ℓ)) :
      Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = ((Ecurve ℓ).LFunction n : ℂ)) :
    ∃ g : Newform (newformLevel (Ecurve ℓ)) 2,
      PrintsAnalytic.IsNewformOf (Ecurve ℓ) g ∧
        (⇑f : UpperHalfPlane → ℂ) = ⇑g.toCuspForm := by
  obtain ⟨M, _, g, hg⟩ := hM _ (inferInstance : (Ecurve ℓ).IsElliptic)
  have hCM : HasCuspFormAtLevel (Ecurve ℓ) M := by
    have hmem : g.toCuspForm ∈ cuspFormCharSpace 2 (1 : (ZMod M)ˣ →* ℂˣ) := by
      have h := g.mem_charSpace
      rwa [hg.1] at h
    refine ⟨TauCeti.cuspFormCharSpaceOneEquiv M 2 ⟨g.toCuspForm, hmem⟩, fun n hn => ?_⟩
    rw [TauCeti.coe_cuspFormCharSpaceOneEquiv_apply]
    exact hg.2 n hn
  have hN : 0 < newformLevel (Ecurve ℓ) := NeZero.pos _
  have heq : newformLevel (Ecurve ℓ) = M :=
    le_antisymm (Nat.sInf_le ⟨NeZero.pos M, hCM⟩)
      (Nat.le_of_dvd hN (dvd_of_hasCuspFormAtLevel hg hN ⟨f, hf⟩))
  obtain rfl := heq.symm
  exact ⟨g, hg, coe_eq_of_coeff hg f hf⟩

/-- The reduction stated for the actual cusp form in the base assembly. The comparison
is requested only for the cusps with nonzero weight and uses the very same `f` and `Lat`. -/
theorem hElkikMD_of_assemblyForm {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] {d : ℤ}
    [NeZero (newformLevel (Ecurve ℓ))] (hM : PrintsAnalytic.ModularNewform)
    (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel (Ecurve ℓ)) :
      Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = ((Ecurve ℓ).LFunction n : ℂ))
    {J : Type*} [AddCommGroup J] {cuspClass : OnePoint ℚ → J}
    (hMD : ManinDrinfeld (newformLevel (Ecurve ℓ)) cuspClass)
    (hgp : GenusPartner (Ecurve ℓ) d) (Lat : PeriodPair) {κ : ℚ} (hκ : κ ≠ 0)
    (φ : J →+ ℂ ⧸ Lat.lattice.toAddSubgroup)
    (hAJ : ∀ a < d.natAbs, chiD d a ≠ 0 → φ (cuspClass (((a : ℚ) / d.natAbs : ℚ) : OnePoint ℚ)) =
      QuotientAddGroup.mk' Lat.lattice.toAddSubgroup ((κ : ℂ) * cuspSymbol f ((a : ℚ) / d.natAbs))) :
    ∃ q : ℚ, q ≠ 0 ∧ (q : ℂ) = Lstar (Ecurve ℓ) Lat d := by
  obtain ⟨g, hg, heq⟩ := curveNewform_eq_assemblyForm hM f hf
  exact hElkikMD_of_maninDrinfeld hMD hg hgp Lat hκ φ (heq ▸ hAJ)


end ZInQ.Manuscript.RC.ElkikMD
