import Mathlib.Analysis.Fourier.ZMod
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-! The finite Fourier calculation for an odd squarefree quadratic character (provenance (c)). -/

noncomputable section

open Complex
open scoped ZMod

namespace ZInQ.Manuscript.RC.ElkikMD

private theorem jacobi_congr {M : ℕ} {a b : ℤ} (h : (a : ZMod M) = (b : ZMod M)) :
    jacobiSym a M = jacobiSym b M :=
  jacobiSym.mod_left' ((ZMod.intCast_eq_intCast_iff' a b M).mp h)

/-- The Jacobi character modulo `M`, including its zero values on nonunits. -/
def jacobiCharacter (M : ℕ) [NeZero M] : DirichletCharacter ℂ M where
  toFun a := (jacobiSym a.val M : ℂ)
  map_one' := by
    have h := jacobi_congr (M := M) (a := ((1 : ZMod M).val : ℤ)) (b := 1) (by simp)
    rw [h, jacobiSym.one_left, Int.cast_one]
  map_mul' a b := by
    have h := jacobi_congr (M := M) (a := ((a * b).val : ℤ)) (b := (a.val : ℤ) * b.val) (by simp)
    rw [h, jacobiSym.mul_left, Int.cast_mul]
  map_nonunit' a ha := by
    have hnc : ¬ a.val.Coprime M := by
      intro hc
      exact ha (by simpa using (ZMod.isUnit_iff_coprime _ _).mpr hc)
    have h := jacobiSym.eq_zero_iff_not_coprime (a := (a.val : ℤ)) (b := M)
    have hg : (a.val : ℤ).gcd M ≠ 1 := by simpa only [Int.gcd, Int.natAbs_natCast] using hnc
    rw [h.mpr hg, Int.cast_zero]

/-- On all integer representatives the character evaluates to the Jacobi symbol. -/
theorem jacobiCharacter_intCast (M : ℕ) [NeZero M] (a : ℤ) :
    jacobiCharacter M a = (jacobiSym a M : ℂ) := by
  change ((jacobiSym ((a : ZMod M).val : ℤ) M : ℤ) : ℂ) = _
  rw [jacobi_congr (M := M) (a := ((a : ZMod M).val : ℤ)) (b := a) (by simp)]

/-- At an odd squarefree modulus the Jacobi character is primitive. For each omitted prime,
CRT chooses a nonsquare there and the residue one at the rest of the modulus. -/
theorem jacobiCharacter_isPrimitive {M : ℕ} [NeZero M] (hM : Odd M) (hsq : Squarefree M) :
    (jacobiCharacter M).IsPrimitive := by
  let χ := jacobiCharacter M
  change χ.conductor = M
  obtain ⟨k, hk⟩ := χ.conductor_dvd_level
  by_contra hneq
  have hk1 : k ≠ 1 := by intro h; apply hneq; simpa [h] using hk.symm
  obtain ⟨p, hp, t, ht⟩ := Nat.exists_prime_and_dvd hk1
  let q := χ.conductor * t
  have hMprod : M = p * q := calc
    M = χ.conductor * k := hk
    _ = p * q := by rw [ht]; dsimp [q]; ring
  have hqp : q ∣ M := hMprod ▸ dvd_mul_left q p
  have hpM : p ∣ M := hMprod ▸ dvd_mul_right p q
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hM) (even_iff_two_dvd.mpr hpM)
  have hpq : p.Coprime q := hp.coprime_iff_not_dvd.mpr fun h =>
    (Nat.squarefree_iff_prime_squarefree.mp hsq p hp) (hMprod ▸ by simpa [pow_two] using mul_dvd_mul_left p h)
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one (F := ZMod p) (by simpa [ZMod.ringChar_zmod_n] using hp2)
  let r := Nat.chineseRemainder hpq a.val 1
  have hrp : ((r.val : ℤ) : ZMod p) = a := by
    have h := (ZMod.natCast_eq_natCast_iff _ _ _).mpr r.property.1
    simpa only [ZMod.natCast_zmod_val, Int.cast_natCast] using h
  have hrq : ((r.val : ℤ) : ZMod q) = 1 := by
    have h := (ZMod.natCast_eq_natCast_iff _ _ _).mpr r.property.2
    simpa only [Nat.cast_one, Int.cast_natCast] using h
  have hq0 : q ≠ 0 := ne_zero_of_dvd_ne_zero (NeZero.ne M) hqp
  have hrq' : jacobiSym (r.val : ℤ) q = 1 := by
    rw [jacobi_congr (b := 1) (by simpa using hrq), jacobiSym.one_left]
  have hχr : χ (r.val : ZMod M) = -1 := by
    change jacobiCharacter M (r.val : ZMod M) = _
    rw [← Int.cast_natCast, jacobiCharacter_intCast, hMprod, jacobiSym.mul_right' _ hp.ne_zero hq0,
      hrq', mul_one,
      ← jacobiSym.legendreSym.to_jacobiSym, legendreSym, hrp, ha]
    simp
  have hrUnit : IsUnit (r.val : ZMod M) := by
    apply (MulChar.apply_ne_zero_iff (χ := χ)).mp
    rw [hχr]
    norm_num
  have hfac := χ.factorsThrough_conductor.mono χ (show χ.conductor ∣ q from dvd_mul_right _ _) hqp
  have heq : χ (r.val : ZMod M) = 1 := by
    have hcop : IsCoprime (r.val : ℤ) M := isCoprime_comm.mp
      ((ZMod.coe_int_isUnit_iff_isCoprime (r.val : ℤ) M).mp (by simpa only [Int.cast_natCast] using hrUnit))
    rw [hfac.eq_changeLevel, ← Int.cast_natCast,
      DirichletCharacter.changeLevel_eq_cast_of_dvd' hfac.χ₀ hfac.dvd hcop, hrq, map_one]
  rw [heq] at hχr
  norm_num at hχr

/-- The odd primitive Jacobi character's Fourier transform divided by `M`: the weights are the
character values divided by its Gauss sum. Fourier inversion gives its square `-M`, so only the
sign of `i√M` is undetermined. -/
theorem jacobiCharacter_fourier {M : ℕ} [NeZero M] (hM : M % 4 = 3) (hsq : Squarefree M) :
    ∃ (ε : ℤ), (ε = 1 ∨ ε = -1) ∧ ∀ a : ZMod M,
      (M : ℂ)⁻¹ * ZMod.dft (jacobiCharacter M) a =
        jacobiCharacter M a / ((ε : ℂ) * (Real.sqrt (M : ℝ) : ℂ) * I) := by
  let χ := jacobiCharacter M
  have hodd : Odd M := Nat.odd_iff.mpr (by omega)
  have hp : χ.IsPrimitive := jacobiCharacter_isPrimitive hodd hsq
  have hquad : χ.IsQuadratic := by
    intro a
    change ((jacobiSym a.val M : ℤ) : ℂ) = 0 ∨ _
    change ((jacobiSym a.val M : ℤ) : ℂ) = 0 ∨ ((jacobiSym a.val M : ℤ) : ℂ) = 1 ∨
      ((jacobiSym a.val M : ℤ) : ℂ) = -1
    rcases jacobiSym.trichotomy (a.val : ℤ) M with ha | ha | ha <;> rw [ha] <;> norm_num
  have hneg : χ (-1) = -1 := by
    have h := jacobiCharacter_intCast M (-1)
    rw [jacobiSym.at_neg_one hodd, ZMod.χ₄_nat_three_mod_four hM] at h
    simpa only [Int.cast_neg, Int.cast_one] using h
  let τ := gaussSum χ ZMod.stdAddChar
  have hD : ZMod.dft (χ : ZMod M → ℂ) = fun a => -τ * χ a := by
    funext a
    rw [hp.fourierTransform_eq_inv_mul_gaussSum, hquad.inv, ← neg_one_mul a, map_mul, hneg]
    dsimp [τ]
    ring
  have hτ : τ ^ 2 = -(M : ℂ) := by
    have heq := congrFun (ZMod.dft_dft (χ : ZMod M → ℂ)) 1
    rw [hD, ZMod.dft_const_mul] at heq
    simp only [hD, map_one, mul_one, smul_eq_mul, hneg] at heq
    linear_combination heq
  have hm : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hτ0 : τ ≠ 0 := fun hz => hm (by simpa [hz] using hτ.symm)
  have hroot : ((Real.sqrt (M : ℝ) : ℂ) * I) ^ 2 = -(M : ℂ) := by
    rw [mul_pow, I_sq, ← ofReal_pow, Real.sq_sqrt (by positivity)]
    simp
  have hsign : τ = (Real.sqrt (M : ℝ) : ℂ) * I ∨ τ = -((Real.sqrt (M : ℝ) : ℂ) * I) :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (hτ.trans hroot.symm)
  have hDFT : ∀ a : ZMod M, (M : ℂ)⁻¹ * ZMod.dft χ a = χ a / τ := by
    intro a
    rw [hD]
    field_simp
    linear_combination -(χ a) * hτ
  rcases hsign with h | h
  · exact ⟨1, Or.inl rfl, by simpa only [Int.cast_one, one_mul, h] using hDFT⟩
  · exact ⟨-1, Or.inr rfl, by simpa only [Int.cast_neg, Int.cast_one, neg_one_mul, neg_mul, one_mul, h] using hDFT⟩

#print axioms jacobi_congr
#print axioms jacobiCharacter_intCast
#print axioms jacobiCharacter_isPrimitive
#print axioms jacobiCharacter_fourier

end ZInQ.Manuscript.RC.ElkikMD
