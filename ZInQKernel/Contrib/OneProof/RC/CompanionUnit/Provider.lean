import ZInQKernel.Contrib.OneProof.RC.KSplitOldUnit.Comparison
import ZInQKernel.Contrib.OneProof.RC.HalfIntegral.Assembly
import ZInQKernel.Contrib.OneProof.RC.Wiring.CompanionLeaf
import ZInQKernel.Contrib.CloudB3RC53.Companion.Disc
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.LevelGood
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.RamifiedPrimes

/-! Choose the final companion at the attained minimum of the separate negative
Appendix E source (tex 2595–2603). All exclusions are set before choosing its
minimum; adding the companion factors builds the support for the next step. -/

noncomputable section

namespace ZInQ.Manuscript.RC.CompanionUnit

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53
open ZInQ.Manuscript.RC.Even AppE KSplitOldUnit PrintsAnalytic Wiring

/-- Primes carrying squareclass tests in the separate source. -/
def levelPrimes (ℓ : ℕ) : Finset ℕ := (2 * CST.newformLevel (Ecurve ℓ)).primeFactors

/-- Only coprimality is imposed by this part of the initial sieve.
`Sold` and `T` are the pre-companion odd support and the torsion ramification support. -/
def exclusions (Sold T : Finset ℕ) (hstar : ℤ) : Finset ℕ :=
  Sold ∪ T ∪ hstar.natAbs.primeFactors

/-- The final support for the companion interface and the transport comparison. -/
def finalSupport (ℓ : ℕ) (Sold T : Finset ℕ) (hstar k : ℤ) : Finset ℕ :=
  levelPrimes ℓ ∪ exclusions Sold T hstar ∪ k.natAbs.primeFactors

/-- Signed form of the initial filter. The test at two implies
`k % 4 = 1` and excludes both exceptional imaginary fields. -/
def NegativeFilter (ℓ : ℕ) (Sold T : Finset ℕ) (hstar k : ℤ) : Prop :=
  k < 0 ∧ Squarefree k ∧ (∀ p ∈ levelPrimes ℓ, UnitSquareAt p k) ∧
    ∀ p ∈ exclusions Sold T hstar, ¬ (p : ℤ) ∣ k

/-- The dyadic prime is in the level support. -/
theorem two_mem_levelPrimes {ℓ : ℕ} (hN : 0 < CST.newformLevel (Ecurve ℓ)) :
    2 ∈ levelPrimes ℓ :=
  Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_mul_right 2 _, mul_ne_zero two_ne_zero hN.ne'⟩

/-- Convert the unsigned test relative to a signed square-unit reference
to the signed test in the initial filter. -/
theorem signed_class_iff {d D₀ p : ℕ} (hp : p.Prime)
    (href : UnitSquareAt p (-(D₀ : ℤ))) :
    ((p = 2 → (d * D₀) % 8 = 1) ∧ (p ≠ 2 → IsSquare ((d * D₀ : ℕ) : ZMod p))) ↔
      ((p = 2 → (-(d : ℤ)) % 8 = 1) ∧ (p ≠ 2 → IsSquare (Int.cast (-(d : ℤ)) : ZMod p))) := by
  by_cases h2 : p = 2
  · subst p
    have href8 := href.2.1 rfl
    have h7 : D₀ % 8 = 7 := by omega
    have hm : (d * D₀) % 8 = (d % 8 * 7) % 8 := by rw [Nat.mul_mod, h7]
    simp only [eq_self, true_implies, ne_eq, not_true_eq_false, false_implies, and_true]
    rw [hm]
    omega
  · let : Fact p.Prime := ⟨hp⟩
    let a : ZMod p := Int.cast (-(D₀ : ℤ))
    let b : ZMod p := Int.cast (-(d : ℤ))
    have ha : a ≠ 0 := fun hz => href.1 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz)
    have hs : IsSquare a := href.2.2 h2
    have he : ((d * D₀ : ℕ) : ZMod p) = b * a := by simp [a, b]
    rw [he]
    simp only [h2, false_implies, ne_eq, not_false_eq_true, true_implies, true_and]
    exact ⟨fun h => by simpa only [mul_div_cancel_right₀ _ ha] using h.div hs,
      fun h => h.mul hs⟩

/-- The exact negative filter, expressed using the positive Fourier index
and the reference squareclasses in `OldSource`. -/
theorem negativeFilter_iff_oldRetained {ℓ : ℕ} {Sold T : Finset ℕ} {hstar k : ℤ}
    {D₀ : ℕ} (hk : k < 0) (href : ∀ p ∈ levelPrimes ℓ, UnitSquareAt p (-(D₀ : ℤ))) :
    NegativeFilter ℓ Sold T hstar k ↔
      oldRetained (levelPrimes ℓ) (exclusions Sold T hstar) D₀ k.natAbs := by
  have hsign : -(k.natAbs : ℤ) = k := by rw [Int.natCast_natAbs, abs_of_neg hk, neg_neg]
  have hclass (p : ℕ) (hp : p ∈ levelPrimes ℓ) :=
    signed_class_iff (d := k.natAbs) (Nat.prime_of_mem_primeFactors hp) (href p hp)
  constructor
  · rintro ⟨_, hsf, hsq, havoid⟩
    refine oldRetained_of_companion_avoidance ⟨Int.natAbs_pos.mpr hk.ne,
      Int.squarefree_natAbs.mpr hsf, fun p hp h => (hsq p hp).1 (Int.natCast_dvd.mpr h),
      fun p hp => (hclass p hp).mpr ?_⟩ havoid
    simpa only [hsign] using (hsq p hp).2
  · rintro ⟨⟨_, hsf, hnd, hsq⟩, havoid⟩
    refine ⟨hk, Int.squarefree_natAbs.mp hsf, fun p hp => ⟨?_, ?_⟩,
      fun p hp hd => havoid p hp (Int.natCast_dvd.mp hd)⟩
    · exact fun hd => hnd p hp (Int.natCast_dvd.mp hd)
    · simpa only [hsign] using (hclass p hp).mp (hsq p hp)

/-- Identify the level in the original functional equation with the least
level in the companion interface, using the existing newform divisibility theorem. -/
theorem rootNumberAt_newformLevel {E : WeierstrassCurve ℚ} [hE : E.IsElliptic]
    {w : ℤ} (hw : RootNumber E w) (hM : ModularNewform) :
    RootNumberAt E (CST.newformLevel E) w := by
  obtain ⟨N, hN, f, hf⟩ := hM E hE
  let : NeZero N := hN
  have hm : f.toCuspForm ∈ cuspFormCharSpace 2 (1 : (ZMod N)ˣ →* ℂˣ) := by
    have hc := f.mem_charSpace
    rwa [hf.1] at hc
  have hlevel : N ∈ {M : ℕ | 0 < M ∧ CST.HasCuspFormAtLevel E M} := by
    refine ⟨NeZero.pos N, TauCeti.cuspFormCharSpaceOneEquiv N 2 ⟨f.toCuspForm, hm⟩, fun n hn => ?_⟩
    rw [TauCeti.coe_cuspFormCharSpaceOneEquiv_apply]
    exact hf.2 n hn
  have hmin := Nat.sInf_mem ⟨N, hlevel⟩
  have heq : CST.newformLevel E = N := Nat.le_antisymm (Nat.sInf_le hlevel)
    (Nat.le_of_dvd hmin.1 (GenusOdd.dvd_of_hasCuspFormAtLevel hf hmin.1 hmin.2))
  obtain ⟨M, hbase⟩ := rootNumber_iff_exists_rootNumberAt.mp hw
  have hM_eq : M = N := (eq_level_and_sign_of_rootNumberAt hf hbase).1
  simpa only [heq, ← hM_eq] using hbase

/-- The reference supplies the local type; `oldSource_of_phase` fixes the
old rational coefficients and attained depth on the entire initial sieve. -/
theorem oldSource_of_negative_reference {ℓ : ℕ} (hℓ : 0 < ℓ)
    (hN : RootNumberAt (Ecurve ℓ) (CST.newformLevel (Ecurve ℓ)) (-1))
    (hM : ModularNewform) (hH : HasseConvergence) (hWN : WaldspurgerNonvanishing)
    (hW : WaldspurgerCor2) (hR : RamseyAlgebraicModel)
    (C : CentralNormalization (Ecurve ℓ)) (h9 : EvenLowerBound (Ecurve ℓ) C)
    {Sold T : Finset ℕ} {hstar : ℤ} {D₀ : ℕ}
    (hF : NegativeFilter ℓ Sold T hstar (-(D₀ : ℤ)))
    (hL : C.Lstar (-(D₀ : ℤ)) ≠ 0) :
    Nonempty (OldSource C (levelPrimes ℓ) (exclusions Sold T hstar) D₀) := by
  let : (Ecurve ℓ).IsElliptic := Nonvanishing.curve_nat_isElliptic hℓ
  have hB := bcdtThmA_of_modularNewform hM
  have hd : 0 < D₀ := by have := hF.1; omega
  have hsf : Squarefree D₀ := by simpa only [← Int.squarefree_natAbs, Int.natAbs_neg,
    Int.natAbs_natCast] using hF.2.1
  have hnd : ∀ p ∈ levelPrimes ℓ, ¬ p ∣ D₀ := fun p hp hdvd =>
    (hF.2.2.1 p hp).1 (by simpa using (Int.natCast_dvd.mpr hdvd :
      (p : ℤ) ∣ (D₀ : ℤ)))
  obtain ⟨P, -, -⟩ := evenPhaseData_of_prints hWN hW hR HalfIntegral.halfIntegralTwist hB hH C
    (Or.inr rfl) (levelPrimes ℓ) (fun _ hp => Nat.prime_of_mem_primeFactors hp)
    (two_mem_levelPrimes hN.1) (hcond_primeFactors hM inferInstance hN) hd hsf hnd
    (by simpa only [neg_one_mul] using hL)
  obtain ⟨O, -⟩ := oldSource_of_phase P hL (fun p hp hdvd =>
    hF.2.2.2 p hp (by simpa using (Int.natCast_dvd.mpr hdvd : (p : ℤ) ∣ (D₀ : ℤ))))
    hW inferInstance (GlueSweep.Even.twistContinuation_of_bcdt hB hH (Ecurve ℓ)) h9
  exact ⟨O⟩

/-- The existing BFH clause (ii) furnishes a reference in the entire
initial sieve; the reference is used to prepare the form. Selection of
the companion itself will instead use attainment on that form. -/
theorem exists_negative_reference {ℓ : ℕ} (hℓ : 0 < ℓ)
    (hN : RootNumberAt (Ecurve ℓ) (CST.newformLevel (Ecurve ℓ)) (-1))
    (hM : ModularNewform) (hH : HasseConvergence) (hBFH : Nonvanishing.BFHNonvanishing)
    (C : CentralNormalization (Ecurve ℓ))
    (Sold T : Finset ℕ) (hSold : ∀ p ∈ Sold, p.Prime) (hT : ∀ p ∈ T, p.Prime) (hstar : ℤ) :
    ∃ D₀ : ℕ, NegativeFilter ℓ Sold T hstar (-(D₀ : ℤ)) ∧ C.Lstar (-(D₀ : ℤ)) ≠ 0 := by
  let hE : (Ecurve ℓ).IsElliptic := Nonvanishing.curve_nat_isElliptic hℓ
  have hB := bcdtThmA_of_modularNewform hM
  have hX : ∀ p ∈ exclusions Sold T hstar, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (Finset.mem_union.mp hp).elim (hSold p) (hT p)
    · exact Nat.prime_of_mem_primeFactors hp
  let S := (levelPrimes ℓ ∪ exclusions Sold T hstar) ∪ Wiring.S0 ℓ
  have hSL : levelPrimes ℓ ⊆ S := fun _ hp =>
    Finset.mem_union_left _ (Finset.mem_union_left _ hp)
  have hSX : exclusions Sold T hstar ⊆ S := fun _ hp =>
    Finset.mem_union_left _ (Finset.mem_union_right _ hp)
  have hSB : Wiring.S0 ℓ ⊆ S := fun _ hp => Finset.mem_union_right _ hp
  have hS : ∀ p ∈ S, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (Finset.mem_union.mp hp).elim Nat.prime_of_mem_primeFactors (hX p)
    · simp only [Wiring.S0, Finset.mem_insert] at hp
      rcases hp with rfl | rfl | hp
      · exact Nat.prime_two
      · exact Nat.prime_three
      · exact Nat.prime_of_mem_primeFactors hp
  have hbad : ∀ p : ℕ, p.Prime → ¬ Nonvanishing.GoodAt (Ecurve ℓ) p → p ∈ S := by
    intro p hp hn
    refine Nonvanishing.bad_curve_mem (m := (ℓ : ℤ))
      (hSB (by simp [Wiring.S0])) (hSB (by simp [Wiring.S0])) ?_ p hp ?_
    · intro q hq hd
      exact hSB (by simp [Wiring.S0, Nat.mem_primeFactors, hq, hℓ.ne',
        (show q ∣ ℓ by exact_mod_cast hd)])
    · simpa [Ecurve] using hn
  obtain ⟨D, hfund, hsign, hsplit, hra⟩ :=
    hBFH _ hE (hB _ hE) (-1) ⟨_, hN⟩ S hS hbad
  have hD : D < 0 := by omega
  have hD8 := (hsplit 2 (hSL (two_mem_levelPrimes hN.1))).two
  have hsf := (hfund.squarefree_of_odd (Int.odd_iff.mpr (by omega))).1
  have hlocal (p : ℕ) (hp : p ∈ levelPrimes ℓ) : UnitSquareAt p D :=
    ⟨Nonvanishing.SplitsIn.not_dvd (hS p (hSL hp)) (hsplit p (hSL hp)),
      (hsplit p (hSL hp)).1, fun h2 => ((hsplit p (hSL hp)).2 h2).2⟩
  have hL := (GlueSweep.Even.lstar_ne_zero_iff_of_bcdt hB hH C hD.ne).mpr hra
  refine ⟨D.natAbs, ?_⟩
  rw [Int.natCast_natAbs, abs_of_neg hD, neg_neg]
  exact ⟨⟨hD, hsf, hlocal, fun p hp =>
    Nonvanishing.SplitsIn.not_dvd (hS p (hSX hp)) (hsplit p (hSX hp))⟩, hL⟩

/-- A single choice retaining the reference, the original source and the
same-index reading. The support is prescribed by `finalSupport` after `k`
is fixed. -/
structure Selection {ℓ : ℕ} (C : CentralNormalization (Ecurve ℓ))
    (Sold T : Finset ℕ) (hstar : ℤ) where
  D₀ : ℕ
  reference : NegativeFilter ℓ Sold T hstar (-(D₀ : ℤ))
  old : OldSource C (levelPrimes ℓ) (exclusions Sold T hstar) D₀
  k : ℤ
  filter : NegativeFilter ℓ Sold T hstar k
  level_pos : 0 < CST.newformLevel (Ecurve ℓ)
  modEight : k % 8 = 1
  oldUnit : CompanionOldUnit old k
  central : C.Lstar k ≠ 0

/-- With the old source prepared in the correct class, choose `k` by the
attained minimum. Its nonzero central value is a consequence of (E.11). -/
theorem exists_selection_of_source {ℓ : ℕ} {C : CentralNormalization (Ecurve ℓ)}
    {Sold T : Finset ℕ} {hstar : ℤ} {D₀ : ℕ}
    (hN : 0 < CST.newformLevel (Ecurve ℓ))
    (hSold : ∀ p ∈ Sold, p.Prime) (hT : ∀ p ∈ T, p.Prime)
    (href : NegativeFilter ℓ Sold T hstar (-(D₀ : ℤ)))
    (O : OldSource C (levelPrimes ℓ) (exclusions Sold T hstar) D₀) :
    ∃ A : Selection C Sold T hstar, ∃ e : A.D₀ = D₀, (e ▸ A.old) = O := by
  obtain ⟨k, hk, hu⟩ := exists_companionOldUnit O
  have hf := (negativeFilter_iff_oldRetained hk href.2.2.1).mpr ((companionOldUnit_iff O k).mp hu).1
  have h8 := (hf.2.2.1 2 (two_mem_levelPrimes hN)).2.1 rfl
  have hS : ∀ p ∈ finalSupport ℓ Sold T hstar k, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · exact Nat.prime_of_mem_primeFactors hp
      · rcases Finset.mem_union.mp hp with hp | hp
        · exact (Finset.mem_union.mp hp).elim (hSold p) (hT p)
        · exact Nat.prime_of_mem_primeFactors hp
    · exact Nat.prime_of_mem_primeFactors hp
  have hL := (old_transport_inputs O hk hu hS
    (fun _ hp => Finset.mem_union_left _ (Finset.mem_union_left _ hp))
    (fun _ hp => Finset.mem_union_left _ (Finset.mem_union_right _ hp))
    (fun _ hp => Finset.mem_union_right _ hp)).1
  exact ⟨⟨D₀, href, O, k, hf, hN, h8, hu, hL⟩, rfl, rfl⟩

/-- Complete companion selection from the existing prints and Appendix E
inputs, with the nonzero reference prepared in the exact initial sieve. -/
theorem exists_selection_of_prints {ℓ : ℕ} (hℓ : 0 < ℓ)
    (hw : RootNumber (Ecurve ℓ) (-1))
    (hM : ModularNewform) (hH : HasseConvergence) (hBFH : Nonvanishing.BFHNonvanishing)
    (hWN : WaldspurgerNonvanishing) (hW : WaldspurgerCor2) (hR : RamseyAlgebraicModel)
    (C : CentralNormalization (Ecurve ℓ)) (h9 : EvenLowerBound (Ecurve ℓ) C)
    (Sold T : Finset ℕ) (hSold : ∀ p ∈ Sold, p.Prime) (hT : ∀ p ∈ T, p.Prime) (hstar : ℤ) :
    Nonempty (Selection C Sold T hstar) := by
  let : (Ecurve ℓ).IsElliptic := Nonvanishing.curve_nat_isElliptic hℓ
  have hN := rootNumberAt_newformLevel hw hM
  obtain ⟨D₀, hF, hL⟩ := exists_negative_reference hℓ hN hM hH hBFH C Sold T hSold hT hstar
  obtain ⟨O⟩ := oldSource_of_negative_reference hℓ hN hM hH hWN hW hR C h9 hF hL
  obtain ⟨A, -⟩ := exists_selection_of_source hN.1 hSold hT hF O
  exact ⟨A⟩

namespace Selection

variable {ℓ : ℕ} {C : CentralNormalization (Ecurve ℓ)} {Sold T : Finset ℕ} {hstar : ℤ}

/-- Populate `W.kfin` with the selected `k` and `W.S` with
`finalSupport`. The calibration `W.Lstar = C.Lstar` makes the two
certificates concern the same curve and same companion. -/
theorem leaf_and_oldUnit (A : Selection C Sold T hstar) (hstar₀ : hstar ≠ 0)
    (W : WData ℓ) (hk : W.kfin = A.k) (hS : W.S = finalSupport ℓ Sold T hstar A.k)
    (hh : W.hstar = hstar) (hC : W.Lstar = C.Lstar) :
    CompanionLeaf W ∧ CompanionOldUnit A.old W.kfin := by
  refine ⟨fun _ => ?_, hk.symm ▸ A.oldUnit⟩
  rw [hk, hS, hh, hC]
  have h8 := A.modEight
  refine ⟨A.filter.1, A.filter.2.1, by omega, by omega, ?_, by omega, ?_, ?_, A.central⟩
  · intro p hp hd
    exact Finset.mem_union_right _ (Nat.mem_primeFactors.mpr
      ⟨hp, Int.natCast_dvd.mp hd, Int.natAbs_ne_zero.mpr A.filter.1.ne⟩)
  · intro p hp hd
    apply A.filter.2.2.1 p
    exact Nat.mem_primeFactors.mpr ⟨hp, hd, mul_ne_zero two_ne_zero A.level_pos.ne'⟩
  · rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd]
    refine Nat.coprime_of_dvd fun p hp hpk hph => ?_
    exact A.filter.2.2.2 p
      (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr
        ⟨hp, hph, Int.natAbs_ne_zero.mpr hstar₀⟩)) (Int.natCast_dvd.mpr hpk)

/-- Every prime factor of the chosen discriminant avoids the two old
supports. There is such a prime, and it ramifies in the quadratic field
containing `√k`. Thus the witness is outside all old fields whose
ramification is covered by those supports. -/
theorem fresh_ramification (A : Selection C Sold T hstar) {K : Type} [Field K]
    [NumberField K] (hK : Module.finrank ℚ K = 2) {s : K} (hs : s ^ 2 = A.k) :
    NumberField.discr K = A.k ∧
      ∃ p ∈ NumberField.ramifiedPrimes K, p ∉ Sold ∧ p ∉ T := by
  have h8 := A.modEight
  have hdisc := Companion.discr_eq_of_sq hK A.filter.2.1 (by omega) (ne_of_lt (A.filter.1.trans zero_lt_one)) hs
  refine ⟨hdisc, ?_⟩
  have habs : A.k.natAbs ≠ 1 := by
    intro h
    have hh : (A.k.natAbs : ℤ) = -A.k := by rw [Int.natCast_natAbs, abs_of_neg A.filter.1]
    rw [h] at hh
    omega
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd habs
  have hd' : (p : ℤ) ∣ A.k := Int.natCast_dvd.mpr hd
  exact ⟨p, (NumberField.mem_ramifiedPrimes_iff_dvd_discr hp).mpr (hdisc.symm ▸ hd'),
    fun h => A.filter.2.2.2 p (Finset.mem_union_left _ (Finset.mem_union_left _ h)) hd',
    fun h => A.filter.2.2.2 p (Finset.mem_union_left _ (Finset.mem_union_right _ h)) hd'⟩

end Selection

end ZInQ.Manuscript.RC.CompanionUnit
