import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.Decomp

/-! The norm character on conductor-one ideal classes (tex 9178–9194). -/

noncomputable section

open scoped NumberField
open NumberField IsDedekindDomain
open TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder TauCeti.ClassFieldTheory
open ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd

namespace ZInQ.Manuscript.RC.O7Actual

/-- ELLIOT: the smallest norm-character descent statement at positive
`D > 1`. The source consists of the integral ideals prime to the genus
partner, and the character factors through the *actual* Picard group. -/
def NormCharacterDescent (F : Type) [Field F] [NumberField F] (hstar : ℤ) : Prop :=
  ∃ χ : Pic (conductorOrder F 1) →* ℤˣ,
    ∀ J : integralIdealsPrimeTo (conductorOrder F 1).conductorModulus,
      (Ideal.absNorm J.val).Coprime hstar.natAbs →
        (χ ((conductorOrder F 1).picClass J) : ℤ) = chiD hstar (Ideal.absNorm J.val)

/-- Tex 9191–9194: for `D = 1` the norm character is trivial at every
prime ideal away from the discriminant. The residue degree at an inert
prime is two, and the character at a split prime is one. -/
theorem norm_character_self_prime {F : Type} [Field F] [NumberField F]
    (h₂ : Module.finrank ℚ F = 2) (hodd : Odd (discr F)) {p : ℕ} (hp : p.Prime)
    (hpd : ¬ (p : ℤ) ∣ discr F)
    (P : HeightOneSpectrum (𝓞 F)) (hP : P ∈ primesAbove F p) :
    chiD (discr F) (Ideal.absNorm P.asIdeal) = 1 := by
  rcases decomposition h₂ hodd hp with
    ⟨P₁, P₂, _, hset, hN₁, hN₂, _, _, hs⟩ |
    ⟨P₁, hset, hN, _, _⟩ | ⟨_, _, _, _, hram⟩
  · have hN : Ideal.absNorm P.asIdeal = p := by
      rw [hset, Set.mem_insert_iff, Set.mem_singleton_iff] at hP
      rcases hP with h | h
      · rw [h]; exact hN₁
      · rw [h]; exact hN₂
    rw [hN, chiD_eq_kronecker (discr_mod_four_of_odd h₂ hodd) hp, hs]
  · rw [hset, Set.mem_singleton_iff] at hP
    rw [hP, hN]
    have hg : (p : ℤ).gcd ((discr F).natAbs : ℤ) = 1 := by
      rw [Int.gcd_natCast_natCast]
      exact (Nat.Prime.coprime_iff_not_dvd hp).mpr (fun h => hpd (Int.natCast_dvd.mpr h))
    unfold chiD
    push_cast
    exact jacobiSym.sq_one' hg
  · exact (hpd hram).elim

/-- Tex 9191–9194: in the case `D = 1`, multiplicativity extends
triviality from the prime ideals to all allowed integral ideals. -/
theorem norm_character_self_ideal {F : Type} [Field F] [NumberField F]
    (h₂ : Module.finrank ℚ F = 2) (hodd : Odd (discr F)) (J : Ideal (𝓞 F))
    (hJ : J ≠ ⊥) (hcop : (Ideal.absNorm J).Coprime (discr F).natAbs) :
    chiD (discr F) (Ideal.absNorm J) = 1 := by
  induction J using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact (hJ rfl).elim
  | h₂ J hunit =>
    obtain rfl : J = ⊤ := by simpa using hunit
    simp [chiD]
  | h₃ J P hJ' hP ih =>
    have hcop' : (Ideal.absNorm P).Coprime (discr F).natAbs ∧
        (Ideal.absNorm J).Coprime (discr F).natAbs := by
      simpa only [map_mul, Nat.coprime_mul_iff_left] using hcop
    have hPi := Ideal.isPrime_of_prime hP
    let : P.IsMaximal := hPi.isMaximal hP.ne_zero
    obtain ⟨p, n, hn, hmem, hp, hN⟩ := Ideal.exists_prime_and_absNorm_eq_pow P
    have hpp : p.Coprime (discr F).natAbs := (Nat.Coprime.of_dvd_left
      (dvd_pow_self p hn.ne') (hN ▸ hcop'.1))
    have hpd : ¬ (p : ℤ) ∣ discr F := by
      intro h
      exact (Nat.Prime.coprime_iff_not_dvd hp).mp hpp (Int.natCast_dvd.mp h)
    have hv := norm_character_self_prime h₂ hodd hp hpd
      ⟨P, hPi, hP.ne_zero⟩ (by simpa [primesAbove, Int.cast_natCast] using hmem)
    have hv' : chiD (discr F) (Ideal.absNorm P) = 1 := hv
    simp only [chiD, map_mul, Nat.cast_mul, jacobiSym.mul_left] at ih hv' ⊢
    rw [hv', ih hJ' hcop'.2, one_mul]

/-- The trivial character on the actual Picard group realizes norm descent
when the parameter is `D = 1`. -/
theorem normCharacterDescent_self {F : Type} [Field F] [NumberField F]
    (h₂ : Module.finrank ℚ F = 2) (hodd : Odd (discr F)) :
    NormCharacterDescent F (discr F) := by
  refine ⟨1, fun J hcop => ?_⟩
  have hJ := ((conductorOrder F 1).mem_integralIdealsPrimeTo_conductorModulus_iff.mp J.prop).1
  simpa using (norm_character_self_ideal h₂ hodd J.val hJ hcop).symm

end ZInQ.Manuscript.RC.O7Actual
