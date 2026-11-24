import ZInQKernel.Contrib.OneProof.RC.EvenReading.Normalization
import ZInQKernel.Contrib.OneProof.RC.AppE.Assembly
import ZInQKernel.Contrib.OneProof.RC.HalfIntegral.Twist
import ZInQKernel.Contrib.OneProof.RC.Wiring.Even
import ZInQKernel.Contrib.CloudB3RC53.CoefficientDictionary.Rules

/-! The genuine source of sign plus one, with reference index one (tex 10288–10295). -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenReading

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53
open AppE ZInQ.Manuscript.RC.Even PrintsAnalytic
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

/-- A prescribed finite set of primes extends to a support containing two and the level
primes of every functional equation for the same nonzero entire continuation. -/
theorem exists_evenSupport {E : WeierstrassCurve ℚ} {F : ℂ → ℂ}
    (hF : IsLContinuation E F) (hF1 : F 1 ≠ 0) (T : Finset ℕ)
    (hT : ∀ p ∈ T, p.Prime) :
    ∃ S : Finset ℕ, T ⊆ S ∧ (∀ p ∈ S, p.Prime) ∧ 2 ∈ S ∧
      (∀ (N : ℕ) (w : ℤ), RootNumberAt E N w → ∀ p : ℕ, p.Prime → p ∣ N → p ∈ S) := by
  classical
  by_cases h : ∃ N w, RootNumberAt E N w
  · obtain ⟨N₀, w₀, hN₀, F₀, hF₀, he₀⟩ := h
    have hne : F ≠ 0 := fun he => hF1 (congrFun he 1)
    rw [isLContinuation_eq hF₀ hF] at he₀
    refine ⟨insert 2 (T ∪ N₀.primeFactors), fun p hp => Finset.mem_insert_of_mem
      (Finset.mem_union_left _ hp), ?_, Finset.mem_insert_self _ _, ?_⟩
    · intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact Nat.prime_two
      · rcases Finset.mem_union.mp hp with hp | hp
        · exact hT p hp
        · exact Nat.prime_of_mem_primeFactors hp
    · intro N w hNw p hp hd
      obtain ⟨hN, G, hG, he⟩ := hNw
      rw [isLContinuation_eq hG hF] at he
      have hNN := (level_sign_unique hF.1 hne hN hN₀ he he₀).1
      exact Finset.mem_insert_of_mem (Finset.mem_union_right _
        (Nat.mem_primeFactors.mpr ⟨hp, hNN ▸ hd, hN₀.ne'⟩))
  · refine ⟨insert 2 T, fun p hp => Finset.mem_insert_of_mem hp, ?_,
      Finset.mem_insert_self _ _, fun N w hNw => (h ⟨N, w, hNw⟩).elim⟩
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact Nat.prime_two
    · exact hT p hp

/-- A phase and its rational coefficients for the transported source. The retained set
and phase are the ones supplied by Appendix E, and the coefficients obey (E.11). -/
structure GenuineEvenSource {ℓ : ℕ} (C : CentralNormalization (Ecurve ℓ))
    {k : ℤ} (hk : k < 0) (S : Finset ℕ) where
  baseLevelSupport : ∀ (N : ℕ) (w : ℤ), RootNumberAt (qtwist (Ecurve ℓ) (k : ℚ)) N w →
    ∀ p : ℕ, p.Prime → p ∣ N → p ∈ S
  P : EvenPhaseData (qtwist (Ecurve ℓ) (k : ℚ)) (transportedNormalization C hk) 1 S 1
  retained_eq : P.retained = {n | S0Filter S 1 n}
  phase_eq : P.z = AppE.phase P.N P.η 1
  r : ℕ → ℚ
  coeff_eq : ∀ n, S0Filter S 1 n →
    hiwCoeff P.g n / hiwCoeff P.g 1 = P.z n * (r n : ℂ) ∧
      r n ^ 2 = C.Lstar ((n : ℤ) * k) / C.Lstar k

/-- The symbol uses the rational part of (E.11) in the whole transported filter. -/
def RevGen (S : Finset ℕ) (r : ℕ → ℚ) : Finset ℕ → ZMod 2 :=
  coeffReading (fun n => (r n : ℚ_[2])) 0 (S0Filter S 1)

/-- Construct the transported source from the existing Appendix E inputs.
The support can include any prescribed finite set of primes. -/
theorem genuineEvenSource_of_prints (hWN : WaldspurgerNonvanishing) (hW : WaldspurgerCor2)
    (hR : RamseyAlgebraicModel) (hB : PoleS12.BCDTThmA) (hH : HasseConvergence)
    {ℓ : ℕ} (hℓ : 0 < ℓ) (C : CentralNormalization (Ecurve ℓ)) {k : ℤ}
    (hk : k < 0) (hLk : C.Lstar k ≠ 0) (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) :
    ∃ S : Finset ℕ, T ⊆ S ∧ Nonempty (GenuineEvenSource C hk S) := by
  classical
  let E' := qtwist (Ecurve ℓ) (k : ℚ)
  let C' := transportedNormalization C hk
  let : E'.IsElliptic :=
    Nonvanishing.qtwist_isElliptic (Nonvanishing.curve_nat_isElliptic hℓ) (by exact_mod_cast hk.ne)
  have hcont := GlueSweep.Even.twistContinuation_of_bcdt hB hH E'
  have h1 : qtwist E' (1 : ℚ) = E' := by
    dsimp only [E']
    rw [Nonvanishing.qtwist_qtwist, one_mul]
  have hL₁ : C'.Lstar (1 * (↑(1 : ℕ) : ℤ)) ≠ 0 := by
    simpa [C', transportedNormalization] using hLk
  obtain ⟨F, hF⟩ := hcont 1 one_ne_zero
  have hF' : IsLContinuation (qtwist E' ((1 * (↑(1 : ℕ) : ℤ) : ℤ) : ℚ)) F := by
    simpa using hF
  have hF1 := F_one_ne_zero_of_lstar C' (by norm_num) hL₁ F hF'
  have hFE' : IsLContinuation E' F := by simpa only [Int.cast_one, h1] using hF
  obtain ⟨S, hTS, hS, h2, hcond⟩ := exists_evenSupport hFE' hF1 T hT
  obtain ⟨P, hret, hz⟩ := evenPhaseData_of_prints hWN hW hR HalfIntegral.halfIntegralTwist
    hB hH C' (Or.inl rfl) S hS h2 hcond (D₀ := 1) (by decide) squarefree_one
    (fun p hp => (hS p hp).not_dvd_one) hL₁
  have hcoeff (n : ℕ) (hn : S0Filter S 1 n) := P.E11 hW inferInstance (Or.inl rfl) hL₁
    hcont n (P.filter_mem n hn)
  let r (n : ℕ) : ℚ := if hn : S0Filter S 1 n then (hcoeff n hn).choose else 0
  refine ⟨S, hTS, ⟨⟨hcond, P, hret, hz, r, fun n hn => ?_⟩⟩⟩
  simpa [r, dite_eq_left hn, C', transportedNormalization] using (hcoeff n hn).choose_spec

end ZInQ.Manuscript.RC.EvenReading
