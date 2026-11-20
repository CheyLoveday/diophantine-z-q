import ZInQKernel.Contrib.CloudB3RC53.ModularWeil.WeakWeil
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.LevelGood
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.AnaLevel
import ZInQKernel.Contrib.OneProof.RC.Wiring.GenusOdd34
import ZInQKernel.Contrib.OneProof.RC.Wiring.Genus

/-! Curve and filter data for tex 1092–1093, 1765–1767, 2343–2353,
2404–2410. The translations between the existing interfaces are
on-the-spot (c). -/

noncomputable section

open ZInQ.Manuscript ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.SelmerTwoPower
  ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd

namespace ZInQ.Manuscript.RC.Gz34Instance

/-- The actual curve is elliptic at every positive parameter. -/
theorem curve_elliptic {ℓ : ℕ} (hℓ : 0 < ℓ) : (Ecurve ℓ).IsElliptic :=
  PoleRC.curve_isElliptic (by exact_mod_cast hℓ.ne')

/-- BCDT supplies the cusp form with all the required coefficients at the
positive least level, the level used by the existing height formula. -/
theorem curve_form (P : Prints) {ℓ : ℕ} (hℓ : 0 < ℓ) :
    0 < newformLevel (Ecurve ℓ) ∧ HasCuspFormAtLevel (Ecurve ℓ) (newformLevel (Ecurve ℓ)) :=
  ModularWeil.exists_form_at_newformLevel _ (P.bcdt _ (curve_elliptic hℓ))

/-- All level primes of the actual curve lie in the base support. At
a prime of the newform level the coefficient of `p²` is the square of
that of `p`, which is impossible at a good prime. -/
theorem curve_level_support (P : Prints) (hM : PrintsAnalytic.ModularNewform)
    {ℓ : ℕ} (hℓ : 0 < ℓ) (p : ℕ) (hp : p.Prime) (hpN : p ∣ 2 * newformLevel (Ecurve ℓ)) :
    p ∈ S0 ℓ := by
  rcases hp.dvd_mul.mp hpN with h2 | hpN
  · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2]
    simp [S0]
  obtain ⟨M, _, f, hf⟩ := hM _ (curve_elliptic hℓ)
  obtain ⟨hpos, hC⟩ := curve_form P hℓ
  have hC' : HasCuspFormAtLevel (Ecurve ℓ) M := by
    have hmem : f.toCuspForm ∈ cuspFormCharSpace 2 (1 : (ZMod M)ˣ →* ℂˣ) := by
      have h := f.mem_charSpace
      rwa [hf.1] at h
    refine ⟨TauCeti.cuspFormCharSpaceOneEquiv M 2 ⟨f.toCuspForm, hmem⟩, fun n hn => ?_⟩
    rw [TauCeti.coe_cuspFormCharSpaceOneEquiv_apply]
    exact hf.2 n hn
  have heq : newformLevel (Ecurve ℓ) = M :=
    le_antisymm (Nat.sInf_le ⟨NeZero.pos M, hC'⟩)
      (Nat.le_of_dvd hpos (dvd_of_hasCuspFormAtLevel hf hpos hC))
  have hrec := GlueSweep.Ana.newform_coeff_prime_sq_of_dvd f hp (by rw [← heq]; exact hpN)
  rw [hf.2 _ (pow_pos hp.pos 2), hf.2 _ hp.pos] at hrec
  have hbad : ¬ Nonvanishing.GoodAt (Ecurve ℓ) p := by
    intro hg
    simp only [PrintsAnalytic.lcoeff, GlueSweep.Ana.LFunction_prime_sq_of_goodAt hp hg] at hrec
    have hz : ((p : ℤ) : ℂ) = 0 := by
      push_cast at hrec ⊢
      linear_combination -hrec
    exact hp.ne_zero (by exact_mod_cast hz)
  exact Nonvanishing.bad_curve_mem (m := (ℓ : ℤ)) (S := S0 ℓ) (by simp [S0]) (by simp [S0])
    (fun q hq hqℓ => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Nat.mem_primeFactors.mpr ⟨hq, Int.natCast_dvd_natCast.mp hqℓ, hℓ.ne'⟩)))
    p hp (by simpa [Ecurve] using hbad)

/-- Uniformization gives the period lattice with the invariants of
the specified Weierstrass model. -/
theorem curve_lattice {ℓ : ℕ} (hℓ : 0 < ℓ) : ∃ Lat : PeriodPair, IsLatticeOf (Ecurve ℓ) Lat := by
  have := curve_elliptic hℓ
  exact ModularWeil.exists_isLatticeOf _

/-- A scale can be chosen along with the form and lattice from the already
named period input. This alone does not give an algebraic CM value. -/
theorem curve_scale (P : Prints) (hper : ModularWeil.NewformPeriodsRational)
    {ℓ : ℕ} (hℓ : 0 < ℓ) :
    ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel (Ecurve ℓ)) :
          Subgroup (GL (Fin 2) ℝ)) 2) (Lat : PeriodPair) (κ : ℚ),
      (∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = ((Ecurve ℓ).LFunction n : ℂ)) ∧
      IsLatticeOf (Ecurve ℓ) Lat ∧ IsParamScale (newformLevel (Ecurve ℓ)) f Lat (κ : ℂ) := by
  obtain ⟨-, f, hf⟩ := curve_form P hℓ
  obtain ⟨Lat, hLat⟩ := curve_lattice hℓ
  obtain ⟨κ, hκ⟩ := hper _ (curve_elliptic hℓ) f hf Lat hLat
  exact ⟨f, Lat, κ, hf, hLat, hκ⟩

theorem squareAt_of_padic {d : ℤ} {p : ℕ} (hp : p.Prime)
    (hu : ¬ (p : ℤ) ∣ d) (hs : Nonvanishing.IsSquareAt p (d : ℚ)) : SquareAt p d := by
  have hs' := Nonvanishing.splitsIn_of_isSquareAt hp hu hs
  exact ⟨hu, hs'.1, fun h => (hs'.2 h).2⟩

private theorem coprime_of_avoids {a b : ℤ} (hb : b ≠ 0)
    (h : ∀ p ∈ b.natAbs.primeFactors, ¬ (p : ℤ) ∣ a) : IsCoprime a b := by
  apply Int.isCoprime_iff_gcd_eq_one.mpr
  change a.natAbs.gcd b.natAbs = 1
  apply Nat.coprime_of_dvd
  intro p hp hpa hpb
  exact h p (Nat.mem_primeFactors.mpr ⟨hp, hpb, Int.natAbs_ne_zero.mpr hb⟩)
    (Int.natCast_dvd.mpr hpa)

/-- The partner from the base support is a GenusOdd partner once that
support is known to contain the primes of twice the level. -/
theorem genusPartner_of_support {ℓ : ℕ} {s : ℤ} (hs : IsGenusPartner ℓ s)
    (hlevel : ∀ p : ℕ, p.Prime → p ∣ 2 * newformLevel (Ecurve ℓ) → p ∈ S0 ℓ) :
    GenusPartner (Ecurve ℓ) s := by
  have hsf := (hs.2.2.1).squarefree_of_odd (Int.odd_iff.mpr (by have := hs.2.1; omega))
  refine ⟨hs.1, hsf.2, hsf.1, ?_, fun p hp hpd => ?_, ?_⟩
  · have := hs.1
    have := hs.2.1
    rw [abs_of_neg hs.1]
    omega
  · obtain ⟨hq, hu⟩ := hs.2.2.2.1 p (hlevel p hp hpd)
    exact squareAt_of_padic hp hu hq
  · rw [show qtwist (Ecurve ℓ) (s : ℚ) = curve ((s * ℓ : ℤ) : ℚ) from Etw_eq_curve ℓ s]
    exact hs.2.2.2.2.2

/-- Positivity and squarefreeness come from the existing prepared filter.
Its unit classes and avoidance of the partner supply the remaining clauses. -/
theorem prepared_of_support {ℓ : ℕ} {W : WData ℓ} (hS : PreparedSpec W)
    (hstar : W.hstar ≠ 0) (hstarS : ∀ p ∈ W.hstar.natAbs.primeFactors, p ∈ W.S)
    (hloc : ∀ h, W.prepared h → ∀ p : ℕ, p.Prime → p ∣ 2 * newformLevel (Ecurve ℓ) → SquareAt p h)
    (h : ℤ) (hp : W.prepared h) : Prepared (Ecurve ℓ) W.hstar h := by
  have hh := hS h hp
  exact ⟨hh.1, hh.2.1, hloc h hp, coprime_of_avoids hstar fun p hp => hh.2.2.2 p (hstarS p hp)⟩

/-- The rough companion relation supplies all the GenusOdd companion
conditions, including nonvanishing in the lattice convention. -/
theorem companion_of_rough {ℓ : ℕ} {W : WData ℓ} {Lat : PeriodPair}
    (hlevel : ∀ p : ℕ, p.Prime → p ∣ 2 * newformLevel (Ecurve ℓ) → p ∈ W.S)
    (hstar : W.hstar ≠ 0) (hΩ : omegaMinus Lat ≠ 0) {h k : ℤ}
    (hp : Prepared (Ecurve ℓ) W.hstar h) (hk : W.IsRoughCompanion h k) :
    Companion (Ecurve ℓ) Lat W.hstar h k := by
  obtain ⟨hneg, h8, hfund, hloc, havoid, -, hL⟩ := hk
  have hsf := hfund.squarefree_of_odd (Int.odd_iff.mpr (by omega))
  refine ⟨hneg, hsf.2, hsf.1, fun p hpp hpd => ?_, coprime_of_avoids hstar havoid, ?_⟩
  · have hdiv : (p : ℤ) ∣ ((2 * newformLevel (Ecurve ℓ) : ℕ) : ℤ) * h := by exact_mod_cast hpd
    have hmem : p ∈ W.S ∪ h.natAbs.primeFactors := by
      rcases (Nat.prime_iff_prime_int.mp hpp).dvd_mul.mp hdiv with hN | hh
      · exact Finset.mem_union_left _ (hlevel p hpp (Int.natCast_dvd_natCast.mp hN))
      · exact Finset.mem_union_right _ (Nat.mem_primeFactors.mpr
          ⟨hpp, Int.natCast_dvd.mp hh, Int.natAbs_ne_zero.mpr hp.1.ne'⟩)
    obtain ⟨hsq, hu⟩ := hloc p hmem
    exact squareAt_of_padic hpp hu hsq
  · exact Lstar_ne_zero_of hΩ (mul_neg_of_pos_of_neg hp.1 hneg).ne
      (Lval_ne_zero_of_analyticRank_zero hL)

#print axioms curve_elliptic
#print axioms curve_form
#print axioms curve_level_support
#print axioms curve_lattice
#print axioms curve_scale
#print axioms squareAt_of_padic
#print axioms coprime_of_avoids
#print axioms genusPartner_of_support
#print axioms prepared_of_support
#print axioms companion_of_rough

end ZInQ.Manuscript.RC.Gz34Instance
