import ZInQKernel.Contrib.OneProof.FHNonvanishing.FE

open HeckeRing.GL2 CongruenceSubgroup ZMod

namespace ZInQ.GZFH

open ZInQ.GZDecomp

/-! ## The character `χ_D` on `ZMod |D|` and its Fourier transform -/

section Character

variable {D : ℤ}

theorem chiDMod_eq (x : ZMod D.natAbs) : chiDMod D x = (jacobiSym (x.val : ℤ) D.natAbs : ℂ) := rfl

theorem chiDMod_intCast [NeZero D.natAbs] (n : ℤ) :
    chiDMod D (n : ZMod D.natAbs) = (jacobiSym n D.natAbs : ℂ) := by
  rw [chiDMod_eq, ZMod.val_intCast, ← jacobiSym.mod_left]

theorem chiDMod_mul [NeZero D.natAbs] (x y : ZMod D.natAbs) :
    chiDMod D (x * y) = chiDMod D x * chiDMod D y := by
  have hx : x = ((x.val : ℤ) : ZMod D.natAbs) := by simp
  have hy : y = ((y.val : ℤ) : ZMod D.natAbs) := by simp
  rw [hx, hy, ← Int.cast_mul, chiDMod_intCast, chiDMod_intCast, chiDMod_intCast,
    jacobiSym.mul_left]
  push_cast; ring

theorem chiDMod_one [NeZero D.natAbs] : chiDMod D 1 = 1 := by
  rw [show (1 : ZMod D.natAbs) = ((1 : ℤ) : ZMod D.natAbs) by simp, chiDMod_intCast,
    jacobiSym.one_left]; simp

theorem chiDMod_unit [NeZero D.natAbs] (u : (ZMod D.natAbs)ˣ) :
    chiDMod D u = 1 ∨ chiDMod D u = -1 := by
  rw [chiDMod_eq]
  have h := ZMod.val_coe_unit_coprime u
  rcases jacobiSym.eq_one_or_neg_one (a := ((u : ZMod D.natAbs).val : ℤ)) (b := D.natAbs)
    (by rw [Int.gcd_natCast_natCast]; exact h) with h1 | h1
  · left; rw [h1]; simp
  · right; rw [h1]; simp

theorem chiDMod_unit_sq [NeZero D.natAbs] (u : (ZMod D.natAbs)ˣ) :
    chiDMod D u * chiDMod D u = 1 := by
  rcases chiDMod_unit u with h | h <;> rw [h] <;> norm_num

theorem chiDMod_inv [NeZero D.natAbs] (u : (ZMod D.natAbs)ˣ) :
    chiDMod D (↑u⁻¹ : ZMod D.natAbs) = chiDMod D u := by
  have h1 : chiDMod D u * chiDMod D (↑u⁻¹ : ZMod D.natAbs) = 1 := by
    rw [← chiDMod_mul, Units.mul_inv, chiDMod_one]
  rcases chiDMod_unit u with h | h <;> rw [h] at h1 ⊢
  · linear_combination h1
  · linear_combination -h1

/-- `𝓕 χ_D (u) = χ_D(u) 𝓕 χ_D (1)` at a unit `u`. -/
theorem dft_chiDMod_unit [NeZero D.natAbs] (u : (ZMod D.natAbs)ˣ) :
    𝓕 (chiDMod D) u = chiDMod D u * 𝓕 (chiDMod D) 1 := by
  rw [dft_apply, dft_apply, Finset.mul_sum]
  refine Fintype.sum_equiv (Units.mulRight u) _ _ (fun j => ?_)
  simp only [Units.mulRight_apply, mul_one, smul_eq_mul]
  rw [chiDMod_mul]
  linear_combination (-(stdAddChar (-(j * (u : ZMod D.natAbs))) * chiDMod D j)) * chiDMod_unit_sq u

/-- **The witness for primitivity.** For a non-unit `a` of `ZMod |D|` (`D` an odd fundamental
discriminant) there is a unit `x ≡ 1` modulo `|D| / p` (`p ∣ gcd(a, |D|)` prime), so that
`(x − 1) a = 0`, with `χ_D(x) = −1` (`x` a non-residue modulo `p`). -/
theorem exists_twist_witness (hD : IsOddFundDisc D) [NeZero D.natAbs] (a : ZMod D.natAbs)
    (ha : ¬ IsUnit a) :
    ∃ x : (ZMod D.natAbs)ˣ, ((x : ZMod D.natAbs) - 1) * a = 0 ∧ chiDMod D x = -1 := by
  have hcop : ¬ Nat.Coprime a.val D.natAbs := fun h =>
    ha (by rw [← ZMod.natCast_zmod_val a]; exact (ZMod.isUnit_iff_coprime _ _).mpr h)
  obtain ⟨p, hp, hpa, hpr⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
  obtain ⟨r', hr'⟩ := hpr
  have hsq : Squarefree D.natAbs := Int.squarefree_natAbs.mpr hD.2.2
  have hr'0 : r' ≠ 0 := by
    rintro rfl; rw [mul_zero] at hr'; exact NeZero.ne D.natAbs hr'
  have hpr' : Nat.Coprime p r' := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => ?_
    obtain ⟨t, ht⟩ := h
    have : p * p ∣ D.natAbs := ⟨t, by rw [hr', ht]; ring⟩
    exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hsq p this))
  have hrodd : D.natAbs % 2 = 1 := by
    have h4 := hD.2.1
    omega
  have hp2 : p ≠ 2 := by
    rintro rfl
    have : 2 ∣ D.natAbs := ⟨r', hr'⟩
    omega
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero r' := ⟨hr'0⟩
  obtain ⟨g, hg⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by rw [ZMod.ringChar_zmod_n]; exact hp2)
  obtain ⟨n, hn1, hn2⟩ := Nat.chineseRemainder hpr' g.val 1
  -- `χ_D(n) = (n/p)(n/r') = (−1)(1)`
  have hJp : jacobiSym (n : ℤ) p = -1 := by
    rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_neg_one_iff]
    have : ((n : ℤ) : ZMod p) = g := by
      have := (ZMod.natCast_eq_natCast_iff n g.val p).mpr hn1
      push_cast; rw [this, ZMod.natCast_zmod_val]
    rw [this]; exact hg
  have hJr' : jacobiSym (n : ℤ) r' = 1 := by
    rw [jacobiSym.mod_left' (a₂ := 1)]
    · exact jacobiSym.one_left _
    · exact_mod_cast hn2
  have hJ : jacobiSym (n : ℤ) D.natAbs = -1 := by
    rw [hr', jacobiSym.mul_right, hJp, hJr']; norm_num
  have hunit : IsUnit ((n : ℕ) : ZMod D.natAbs) := by
    refine (ZMod.isUnit_iff_coprime _ _).mpr ?_
    have h0 : jacobiSym (n : ℤ) D.natAbs ≠ 0 := by rw [hJ]; norm_num
    rw [Ne, jacobiSym.eq_zero_iff_not_coprime, not_not, Int.gcd_natCast_natCast] at h0
    exact h0
  refine ⟨hunit.unit, ?_, ?_⟩
  · rw [IsUnit.unit_spec]
    have hdvd : (D.natAbs : ℤ) ∣ ((n : ℤ) - 1) * (a.val : ℤ) := by
      have h1 : (r' : ℤ) ∣ (n : ℤ) - 1 := by
        have := (Nat.ModEq.dvd hn2.symm)
        push_cast at this; exact this
      have h2 : (p : ℤ) ∣ (a.val : ℤ) := by exact_mod_cast hpa
      have hc : ((D.natAbs : ℕ) : ℤ) = (r' : ℤ) * p := by rw [hr']; push_cast; ring
      rw [hc]
      exact mul_dvd_mul h1 h2
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ D.natAbs).mpr hdvd
    push_cast at this
    rwa [ZMod.natCast_zmod_val] at this
  · rw [IsUnit.unit_spec, show ((n : ℕ) : ZMod D.natAbs) = ((n : ℤ) : ZMod D.natAbs) by push_cast; rfl,
      chiDMod_intCast, hJ]; push_cast; rfl

/-- `𝓕 χ_D` vanishes at the non-units (primitivity of `χ_D`). -/
theorem dft_chiDMod_nonunit (hD : IsOddFundDisc D) [NeZero D.natAbs] (a : ZMod D.natAbs)
    (ha : ¬ IsUnit a) : 𝓕 (chiDMod D) a = 0 := by
  obtain ⟨x, hxa, hx⟩ := exists_twist_witness hD a ha
  have h : 𝓕 (chiDMod D) a = chiDMod D x * 𝓕 (chiDMod D) a := by
    rw [dft_apply, Finset.mul_sum]
    refine Fintype.sum_equiv (Units.mulLeft x) _ _ (fun j => ?_)
    simp only [Units.mulLeft_apply, smul_eq_mul]
    have e : (x : ZMod D.natAbs) * j * a = j * a := by
      linear_combination j * hxa
    rw [e, chiDMod_mul]
    linear_combination (-(stdAddChar (-(j * a)) * chiDMod D j)) * chiDMod_unit_sq x
  rw [hx] at h
  linear_combination h / 2

end Character

end ZInQ.GZFH
