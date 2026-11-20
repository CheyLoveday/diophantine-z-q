import ZInQKernel.Contrib.OneProof.RC.EvenReading.Source
import ZInQKernel.Contrib.OneProof.RC.AddressGenuine.DensityLeaf

/-! The fresh prime and the even reading of the genuine address leaf, in Branch 2. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenReading

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53
open AddressGenuine AppE ZInQ.Manuscript.RC.Even PrintsAnalytic Symbols Wiring
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

/-- Tex 2595–2608: the old support contains the ramification of all old fixed
label extensions and of the torsion field. The label modulus `m₁` is supported
there, and the chosen companion avoids it. Only the inclusion of prime supports
of `m₁` and the companion's avoidance are needed for the existing `FreshPrime`. -/
theorem freshPrime_of_support {ℓ : ℕ} {W : WData ℓ} (D : LabelData W)
    (hcomp : CompanionLeaf W) (hU : ¬ W.OddEmptyUnit) {Sold : Finset ℕ}
    (hm₁ : ∀ p : ℕ, p.Prime → p ∣ D.m₁ → p ∈ Sold)
    (havoid : ∀ p ∈ Sold, ¬ (p : ℤ) ∣ W.kfin) : FreshPrime W D := by
  obtain ⟨hk, _, hk₁, _, _, _, _, _, _⟩ := hcomp hU
  have habs : W.kfin.natAbs ≠ 1 := by
    intro h
    have h' : (W.kfin.natAbs : ℤ) = -W.kfin := by
      rw [Int.natCast_natAbs, abs_of_neg hk]
    rw [h] at h'
    exact hk₁ (by omega)
  obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd habs
  have hd : (p : ℤ) ∣ W.kfin := Int.natCast_dvd.mpr hdvd
  exact ⟨p, hp, hd, fun hp₁ => havoid p (hm₁ p hp hp₁) hd⟩

/-- A finite product of distinct primes has exactly that many prime divisors
(tex 2044–2046 and 10089–10091). -/
theorem omegaN_prod_primes (U : Finset ℕ) (hU : ∀ q ∈ U, q.Prime) :
    omegaN (∏ q ∈ U, q) = U.card := by
  rw [omegaN, Nat.primeFactors_prod hU]

/-- Reading one gives membership in the index filter, a nonzero rational
coefficient and its valuation at the product of primes. -/
theorem revGen_eq_one {S U : Finset ℕ} {r : ℕ → ℚ}
    (hprime : ∀ q ∈ U, q.Prime) (hU : RevGen S r U = 1) :
    let n := ∏ q ∈ U, q
    S0Filter S 1 n ∧ r n ≠ 0 ∧ padicValRat 2 (r n) = U.card := by
  unfold RevGen coeffReading coeffSymbol at hU
  split_ifs at hU with hu
  · obtain ⟨hf, hn, hv⟩ := hu
    refine ⟨hf, fun h0 => hn (by simp [h0]), ?_⟩
    rw [Padic.valuation_ratCast, zero_add] at hv
    change _ = (omegaN (∏ q ∈ U, q) : ℤ) at hv
    rw [omegaN_prod_primes U hprime] at hv
    exact hv
  · exact (zero_ne_one hU).elim

/-- The Branch 2 companion supplies the nonzero reference value. The RC11
normalization certifies that the transported values are those of `W`. -/
theorem genuineEvenSource_of_companion (hWN : WaldspurgerNonvanishing) (hW : WaldspurgerCor2)
    (hR : RamseyAlgebraicModel) (hB : PoleS12.BCDTThmA) (hH : HasseConvergence)
    {ℓ : ℕ} {W : WData ℓ} (hℓ : 0 < ℓ) (hcomp : CompanionLeaf W) (hbranch : ¬ W.OddEmptyUnit)
    (hN : LstarNormalized W.toRCData) (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) :
    ∃ (C : CentralNormalization (Ecurve ℓ)) (hk : W.kfin < 0) (S : Finset ℕ),
      C.Lstar = W.Lstar ∧ T ⊆ S ∧ Nonempty (GenuineEvenSource C hk S) := by
  obtain ⟨C, hC⟩ := hN
  obtain ⟨hk, _, _, _, _, _, _, _, hLk⟩ := hcomp hbranch
  obtain ⟨S, hTS, G⟩ := genuineEvenSource_of_prints hWN hW hR hB hH hℓ C hk
    (by rwa [hC]) T hT
  exact ⟨C, hk, S, hC, hTS, G⟩

/-- (F.1) for a unit of the genuine transported reading (tex 10079–10094,
10320–10322), with equality and `CeFinal = v₂ L_*(k)`. -/
theorem lstar_eq_of_revGen {ℓ : ℕ} {W : WData ℓ}
    {C : CentralNormalization (Ecurve ℓ)} {hk : W.kfin < 0} {S : Finset ℕ}
    (G : GenuineEvenSource C hk S) (hC : C.Lstar = W.Lstar) (hLk : W.Lstar W.kfin ≠ 0)
    (U : Finset ℕ) (hprime : ∀ q ∈ U, q.Prime) (hU : RevGen S G.r U = 1) :
    let h := (∏ q ∈ U, (q : ℤ)) * W.kfin
    W.Lstar h ≠ 0 ∧ padicValRat 2 (W.Lstar h) = 2 * (U.card : ℤ) + padicValRat 2 (W.Lstar W.kfin) := by
  let n := ∏ q ∈ U, q
  obtain ⟨hf, hr, hv⟩ := revGen_eq_one hprime hU
  have hs := (G.coeff_eq n hf).2
  rw [hC] at hs
  have hn : W.Lstar ((n : ℤ) * W.kfin) ≠ 0 := by
    intro h0
    rw [h0, zero_div] at hs
    exact (pow_ne_zero 2 hr) hs
  have hval := congrArg (padicValRat 2) hs
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [padicValRat.pow, padicValRat.div hn hLk, hv] at hval
  have hcast : (n : ℤ) = ∏ q ∈ U, (q : ℤ) := by simp [n]
  rw [hcast] at hn hval
  exact ⟨hn, by omega⟩

/-- The `EvenReading` conjunct is supplied by the equality for the genuine reading. -/
theorem evenReading_of_genuineEven {ℓ : ℕ} {W : WData ℓ} (D : LabelData W)
    {C : CentralNormalization (Ecurve ℓ)} {hk : W.kfin < 0} {S : Finset ℕ}
    (G : GenuineEvenSource C hk S) (hC : C.Lstar = W.Lstar)
    (hcomp : CompanionLeaf W) (hbranch : ¬ W.OddEmptyUnit) :
    AddressGenuine.EvenReading W D (RevGen S G.r) := by
  obtain ⟨_, _, _, _, _, _, _, _, hLk⟩ := hcomp hbranch
  refine ⟨padicValRat 2 (W.Lstar W.kfin), fun U hgood hU => ?_⟩
  obtain ⟨hn, he⟩ := lstar_eq_of_revGen G hC hLk U (fun p hp => (hgood p hp).1) hU
  exact ⟨hn, he.le⟩

end ZInQ.Manuscript.RC.EvenReading
