import ZInQKernel.Contrib.OneProof.HeckePin

noncomputable section
namespace AfTateLam.HeckePin
open PkgI4 (CF coeff)
open Function UpperHalfPlane Real
open scoped MatrixGroups ModularForm
local notation "Iℂ" => Complex.I
local notation "𝕢" => Function.Periodic.qParam

variable {N : ℕ}

/-- `Σ_{j<p} e^{2πi n (τ+j)/p} = p e^{2πi (n/p) τ}` if `p ∣ n`, else `0`. -/
theorem sum_exp_shift (p : ℕ) (hp : 0 < p) (n : ℕ) (τ : ℂ) :
    ∑ j ∈ Finset.range p, Complex.exp (2 * π * Iℂ * n * ((τ + j) / p)) =
      if p ∣ n then (p : ℂ) * Complex.exp (2 * π * Iℂ * (n / p : ℕ) * τ) else 0 := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hsplit : ∀ j : ℕ, Complex.exp (2 * π * Iℂ * n * ((τ + j) / p)) =
      Complex.exp (2 * π * Iℂ * n * τ / p) * Complex.exp (2 * π * Iℂ * n / p) ^ j := by
    intro j
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1; field_simp
  simp_rw [hsplit, ← Finset.mul_sum]
  split_ifs with hdvd
  · obtain ⟨m, rfl⟩ := hdvd
    have h1 : Complex.exp (2 * π * Iℂ * ((p * m : ℕ) : ℂ) / p) = 1 := by
      rw [Complex.exp_eq_one_iff]; exact ⟨m, by push_cast; field_simp⟩
    rw [h1]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [Nat.mul_div_cancel_left _ hp]
    rw [mul_comm]; congr 2; push_cast; field_simp
  · have hne : Complex.exp (2 * π * Iℂ * n / p) ≠ 1 := by
      rw [Ne, Complex.exp_eq_one_iff]
      rintro ⟨k, hk⟩
      apply hdvd
      have hk' : (n : ℂ) = k * p := by
        have h2 : (2 * π * Iℂ : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
        field_simp at hk
        linear_combination hk
      have : (n : ℤ) = k * p := by exact_mod_cast hk'
      have : (p : ℤ) ∣ n := ⟨k, by rw [this]; ring⟩
      exact_mod_cast this
    rw [geom_sum_eq hne, ← Complex.exp_nat_mul]
    have : Complex.exp (p * (2 * π * Iℂ * n / p)) = 1 := by
      rw [Complex.exp_eq_one_iff]; exact ⟨n, by push_cast; field_simp⟩
    rw [this]; simp

/-- The Hecke recurrence at a prime: `a_p a_m = a_{pm} + [p ∣ m] χ(p) p a_{m/p}`. -/
theorem coeff_rec_prime {χ : DirichletCharacter ℂ N} {f : CF N 2}
    (hf : PkgI4.IsNormalizedEigenform f χ) (p : ℕ) (hp : p.Prime) (m : ℕ) :
    coeff f p * coeff f m =
      coeff f (p * m) + if p ∣ m then χ (p : ZMod N) * p * coeff f (m / p) else 0 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [coeff_zero_eq]
  have key := hf.2.2 p m hp.pos hm
  by_cases hpm : p ∣ m
  · have hg : Nat.gcd p m = p := Nat.gcd_eq_left hpm
    rw [hg, hp.divisors, Finset.sum_pair (by have := hp.one_lt; omega)] at key
    rw [key, if_pos hpm]
    obtain ⟨k, rfl⟩ := hpm
    have e2 : p * (p * k) / p ^ 2 = k := by
      rw [show p * (p * k) = k * p ^ 2 by ring]; exact Nat.mul_div_cancel _ (pow_pos hp.pos _)
    rw [e2, Nat.mul_div_cancel_left _ hp.pos]
    simp
  · have hg : Nat.gcd p m = 1 := (Nat.Prime.coprime_iff_not_dvd hp).2 hpm
    rw [hg, Nat.divisors_one, Finset.sum_singleton] at key
    rw [key, if_neg hpm]
    simp

theorem coe_shiftDiv (p j : ℕ) (hp : 0 < p) (τ : UpperHalfPlane) :
    ((shiftDiv p j τ : UpperHalfPlane) : ℂ) = ((τ : ℂ) + j) / p := by
  simp [shiftDiv, hp]

theorem coe_mulNat (p : ℕ) (hp : 0 < p) (τ : UpperHalfPlane) :
    ((mulNat p τ : UpperHalfPlane) : ℂ) = p * (τ : ℂ) := by
  simp [mulNat, hp]

theorem qParam_pow (z : ℂ) (n : ℕ) : 𝕢 1 z ^ n = Complex.exp (2 * π * Iℂ * n * z) := by
  rw [Function.Periodic.qParam, ← Complex.exp_nat_mul]; congr 1; push_cast; ring

theorem hasSum_coeff {f : CF N 2} (w : UpperHalfPlane) :
    HasSum (fun n => coeff f n * 𝕢 1 (w : ℂ) ^ n) (f w) := by
  have hΓ : (1 : ℝ) ∈ (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simp [CongruenceSubgroup.strictPeriods_Gamma1]
  have : Fact (IsCusp OnePoint.infty (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  exact ModularForm.hasSum_qExpansion f one_pos hΓ w

/-- **`T_p f = a_p f` as functions on `ℍ`** (weight 2, DS's normalization): from the `q`-expansion and the
coefficient relations. -/
theorem hecke_eigen_fun {χ : DirichletCharacter ℂ N} {f : CF N 2}
    (hf : PkgI4.IsNormalizedEigenform f χ) (p : ℕ) (hp : p.Prime) (τ : UpperHalfPlane) :
    (∑ j ∈ Finset.range p, f (shiftDiv p j τ)) / p + p * χ (p : ZMod N) * f (mulNat p τ) =
      coeff f p * f τ := by
  have hp0 : 0 < p := hp.pos
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
  set q := 𝕢 1 (τ : ℂ) with hq
  -- the shifted sum
  have h1 : HasSum (fun n => coeff f n * ∑ j ∈ Finset.range p,
      Complex.exp (2 * π * Iℂ * n * (((τ : ℂ) + j) / p))) (∑ j ∈ Finset.range p, f (shiftDiv p j τ)) := by
    have := hasSum_sum (s := Finset.range p) (fun j _ => hasSum_coeff (f := f) (shiftDiv p j τ))
    convert this using 1
    funext n
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [qParam_pow, coe_shiftDiv p j hp0]
  simp_rw [sum_exp_shift p hp0] at h1
  have h1' : HasSum (fun n => if p ∣ n then coeff f n * q ^ (n / p) else 0)
      ((∑ j ∈ Finset.range p, f (shiftDiv p j τ)) / p) := by
    convert h1.div_const (p : ℂ) using 1
    funext n
    split_ifs
    · rw [hq, qParam_pow]; field_simp
    · simp
  have hinj : Injective (fun m : ℕ => p * m) := fun a b h => by simpa [hp0.ne'] using h
  have hA : HasSum (fun m => coeff f (p * m) * q ^ m)
      ((∑ j ∈ Finset.range p, f (shiftDiv p j τ)) / p) := by
    rw [← hinj.hasSum_iff (fun n hn => by
      rw [if_neg]; rintro ⟨k, rfl⟩; exact hn ⟨k, rfl⟩)] at h1'
    convert h1' using 1
    funext m
    simp [hp0.ne', Nat.mul_div_cancel_left _ hp0]
  -- the `f(pτ)` term
  have h2 : HasSum (fun n => if p ∣ n then coeff f (n / p) * q ^ n else 0) (f (mulNat p τ)) := by
    rw [← hinj.hasSum_iff (fun n hn => by
      rw [if_neg]; rintro ⟨k, rfl⟩; exact hn ⟨k, rfl⟩)]
    convert hasSum_coeff (f := f) (mulNat p τ) using 1
    funext m
    simp only [comp_apply, dvd_mul_right, if_true, Nat.mul_div_cancel_left _ hp0]
    rw [hq, qParam_pow, qParam_pow, coe_mulNat p hp0]
    congr 2; push_cast; ring
  have h3 := hA.add (h2.mul_left (p * χ (p : ZMod N)))
  have h4 := (hasSum_coeff (f := f) τ).mul_left (coeff f p)
  refine h3.unique ?_
  convert h4 using 1
  funext m
  rw [← mul_assoc, coeff_rec_prime hf p hp m]
  split_ifs <;> ring

end AfTateLam.HeckePin
