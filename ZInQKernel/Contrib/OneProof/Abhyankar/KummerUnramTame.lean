import ZInQKernel.Contrib.OneProof.Abhyankar.KummerUnramBasic

/-!
# abhyankar: tameness of `L/K` at the height-one primes of `A`

For `L/K` Galois of degree `N < p` over a local `A` of residue characteristic `p`, at a DVR `R = A_{P₀}`
every prime of the integral closure has ramification index dividing `N` (hence a unit of `R`) and a separable
residue field extension (degree `≤ N < p`, residue characteristic `0` or `p`).
-/

open IsLocalRing HDec Polynomial

set_option linter.all false

noncomputable section

namespace Abhyankar

theorem tame_at {A K L : Type} [CommRing A] [IsDomain A] [IsLocalRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    (p : ℕ) (hp : p.Prime) (hpm : (p : A) ∈ maximalIdeal A) (hdeg : Module.finrank K L < p)
    (P₀ : Ideal A) [P₀.IsPrime]
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra A R]
    [IsLocalization.AtPrime R P₀] [Algebra R K] [IsScalarTower A R K] [Algebra R L]
    [IsScalarTower R K L] :
    ∀ (Q₀ : Ideal (integralClosure R L)) [Q₀.IsPrime] [Q₀.LiesOver (maximalIdeal R)],
      Q₀.ramificationIdx R ∣ Module.finrank K L ∧ IsUnit ((Q₀.ramificationIdx R : ℕ) : R) ∧
      Algebra.IsSeparable (R ⧸ maximalIdeal R) (integralClosure R L ⧸ Q₀) := by
  intro Q₀ _ _
  classical
  haveI : IsFractionRing R K := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P₀.primeCompl R K
  haveI : IsFractionRing (integralClosure R L) L := integralClosure.isFractionRing_of_finite_extension K L
  haveI : IsDedekindDomain (integralClosure R L) :=
    IsIntegralClosure.isDedekindDomain R K L (integralClosure R L)
  haveI : Module.Finite R (integralClosure R L) := IsIntegralClosure.finite R K L (integralClosure R L)
  haveI : Module.IsTorsionFree R (integralClosure R L) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    intro x y hxy
    have h1 := congrArg Subtype.val hxy
    have hRL : Function.Injective (algebraMap R L) := by
      rw [IsScalarTower.algebraMap_eq R K L]
      exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
    exact hRL h1
  haveI : Module.Flat R (integralClosure R L) := inferInstance
  letI : MulSemiringAction Gal(L/K) (integralClosure R L) :=
    IsIntegralClosure.MulSemiringAction R K L (integralClosure R L)
  haveI : IsGaloisGroup Gal(L/K) R (integralClosure R L) := IsGaloisGroup.of_isFractionRing _ _ _ K L
  have hform := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (maximalIdeal R)
    (integralClosure R L) Gal(L/K)
  rw [IsGalois.card_aut_eq_finrank] at hform
  have he := Ideal.ramificationIdxIn_eq_ramificationIdx (maximalIdeal R) Q₀ Gal(L/K)
  have hf := Ideal.inertiaDegIn_eq_inertiaDeg (maximalIdeal R) Q₀ Gal(L/K)
  rw [he, hf] at hform
  have hedvd : Q₀.ramificationIdx R ∣ Module.finrank K L :=
    hform ▸ dvd_mul_of_dvd_right (dvd_mul_right _ _) _
  have hfdvd : Q₀.inertiaDeg R ∣ Module.finrank K L :=
    hform ▸ dvd_mul_of_dvd_right (dvd_mul_left _ _) _
  have hN : 0 < Module.finrank K L := Module.finrank_pos
  have hnotdvd : ∀ d, d ∣ Module.finrank K L → ¬ p ∣ d := fun d hd hpd =>
    absurd (Nat.le_of_dvd hN (dvd_trans hpd hd)) (not_le.mpr hdeg)
  refine ⟨hedvd, ?_, ?_⟩
  · have := (isUnit_natCast_of_not_dvd hp hpm (hnotdvd _ hedvd)).map (algebraMap A R)
    rwa [map_natCast] at this
  · haveI : Q₀.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) Q₀
      (by rw [← Ideal.LiesOver.over (P := Q₀) (p := maximalIdeal R)]; infer_instance)
    letI : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
    letI : Field (integralClosure R L ⧸ Q₀) := Ideal.Quotient.field _
    have hfin : Module.finrank (R ⧸ maximalIdeal R) (integralClosure R L ⧸ Q₀) < p := by
      rw [← Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal R) Q₀]
      exact lt_of_le_of_lt (Nat.le_of_dvd hN hfdvd) hdeg
    haveI : Module.Finite (R ⧸ maximalIdeal R) (integralClosure R L ⧸ Q₀) := inferInstance
    rcases CharP.char_is_prime_or_zero (R ⧸ maximalIdeal R) (ringChar (R ⧸ maximalIdeal R)) with hq | hq
    · -- residue characteristic `q = p`
      have hqp : ringChar (R ⧸ maximalIdeal R) = p := by
        by_contra hne
        have hqm : ((ringChar (R ⧸ maximalIdeal R) : ℕ) : R) ∈ maximalIdeal R := by
          rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ringChar.spec]
        have hqA : ((ringChar (R ⧸ maximalIdeal R) : ℕ) : A) ∈ maximalIdeal A := by
          have h1 : ((ringChar (R ⧸ maximalIdeal R) : ℕ) : A) ∈ (maximalIdeal R).under A := by
            rw [Ideal.under, Ideal.mem_comap, map_natCast]; exact hqm
          rw [IsLocalization.AtPrime.under_maximalIdeal R P₀] at h1
          exact le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance) h1
        have hcop : Nat.Coprime (ringChar (R ⧸ maximalIdeal R)) p :=
          (Nat.coprime_primes hq hp).mpr hne
        have := isUnit_natCast_of_not_dvd hp hpm (n := ringChar (R ⧸ maximalIdeal R))
          (fun h => hne ((Nat.prime_dvd_prime_iff_eq hp hq).mp h).symm)
        exact (mem_maximalIdeal _).mp hqA this
      haveI : CharP (R ⧸ maximalIdeal R) p := hqp ▸ ringChar.charP _
      haveI : Fact p.Prime := ⟨hp⟩
      exact PropTSGlue.isSeparable_of_finrank_lt p hfin
    · haveI : CharP (R ⧸ maximalIdeal R) 0 := hq ▸ ringChar.charP _
      haveI : CharZero (R ⧸ maximalIdeal R) := CharP.charP_to_charZero _
      haveI : Algebra.IsAlgebraic (R ⧸ maximalIdeal R) (integralClosure R L ⧸ Q₀) :=
        Algebra.IsIntegral.isAlgebraic
      exact Algebra.IsAlgebraic.isSeparable_of_perfectField

end Abhyankar
