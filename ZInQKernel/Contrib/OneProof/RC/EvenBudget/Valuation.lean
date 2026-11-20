import ZInQKernel.Contrib.OneProof.RC.EvenBudget.Divided
import ZInQKernel.Contrib.OneProof.RC.O12Theta.Symbol
import Mathlib.NumberTheory.Padics.RingHoms

/-! Phase removal and division at the chosen place (tex 8183–8189,
9638–9646, 9675–9698). Transport through the rational two-adics is
provenance (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenBudget

variable {O K : Type} [CommRing O] [Field K] [CharZero K] [Algebra O K]

private theorem padic_two_valuation : (2 : ℚ_[2]).valuation = 1 := by
  simp

private theorem integral_normalized (r : ℚ) (e : ℤ)
    (h : r ≠ 0 → e ≤ padicValRat 2 r) :
    ∃ x : ℤ_[2], (x : ℚ_[2]) = (2 : ℚ_[2]) ^ (-e) * (r : ℚ_[2]) ∧
      x.zmodRepr = if r ≠ 0 ∧ padicValRat 2 r = e then 1 else 0 := by
  by_cases hr : r = 0
  · subst r
    exact ⟨0, by simp, by simp⟩
  let y : ℚ_[2] := (2 : ℚ_[2]) ^ (-e) * (r : ℚ_[2])
  have hy : y ≠ 0 := mul_ne_zero (zpow_ne_zero _ (by norm_num)) (by exact_mod_cast hr)
  have hv : y.valuation = padicValRat 2 r - e := by
    unfold y
    rw [Padic.valuation_mul (zpow_ne_zero _ (by norm_num)) (by exact_mod_cast hr),
      Padic.valuation_zpow, padic_two_valuation, Padic.valuation_ratCast, mul_one]
    omega
  let x : ℤ_[2] := ⟨y, (Padic.norm_le_one_iff_val_nonneg y).mpr (by rw [hv]; exact sub_nonneg.mpr (h hr))⟩
  refine ⟨x, rfl, ?_⟩
  have hx : x ≠ 0 := fun hx => hy (congrArg (fun t : ℤ_[2] => (t : ℚ_[2])) hx)
  have hxv : (x.valuation : ℤ) = padicValRat 2 r - e := by
    rw [← PadicInt.valuation_coe]
    exact hv
  have h2 : ((2 : ℕ) : ℤ_[2]) ∣ x ↔ 1 ≤ x.valuation := by
    simpa only [Ideal.mem_span_singleton, pow_one] using PadicInt.mem_span_pow_iff_le_valuation x hx 1
  have hxlt := x.zmodRepr_lt_p
  by_cases he : padicValRat 2 r = e
  · rw [ite_eq_left ⟨hr, he⟩]
    have hne : x.zmodRepr ≠ 0 := by
      rw [ne_eq, PadicInt.zmodRepr_eq_zero_iff_dvd, h2]
      omega
    omega
  · rw [ite_eq_right (fun h => he h.2), PadicInt.zmodRepr_eq_zero_iff_dvd, h2]
    have := h hr
    omega

/-- A permitted phase times a rational coefficient reduces to the prime
subfield bit of its normalized rational valuation. The integer two, not
a uniformizer of a possibly ramified extension, is the normalizing base. -/
theorem phase_rational_residue (inj : Function.Injective (algebraMap O K)) {m : Ideal O}
    (hm : m.IsMaximal) (h2 : (2 : O) ∈ m)
    (i : ℤ_[2] →+* O) (j : ℚ_[2] →+* K)
    (hi : ∀ x : ℤ_[2], algebraMap O K (i x) = j (x : ℚ_[2]))
    {ζ b : O} (hζ : ∃ k : ℕ, ζ ^ (2 ^ k) = 1) {r : ℚ} {e : ℤ}
    (h : r ≠ 0 → e ≤ padicValRat 2 r)
    (hb : algebraMap O K b = algebraMap O K ζ * (2 : K) ^ (-e) * (r : K)) :
    Ideal.Quotient.mk m b = if r ≠ 0 ∧ padicValRat 2 r = e then 1 else 0 := by
  let : IsDomain O := Function.Injective.isDomain (algebraMap O K) inj
  let : CharZero O := ⟨fun x y hxy => Nat.cast_injective (R := K)
    (by simpa only [map_natCast] using congrArg (algebraMap O K) hxy)⟩
  obtain ⟨x, hx, hbit⟩ := integral_normalized r e h
  have hxi : b = ζ * i x := by
    apply inj
    rw [hb, map_mul, hi, hx, map_mul, map_zpow₀, map_ofNat, map_ratCast, mul_assoc]
  have hdiv : ((2 : ℕ) : ℤ_[2]) ∣ x - (x.zmodRepr : ℤ_[2]) := by
    apply Ideal.mem_span_singleton.mp
    rw [← PadicInt.maximalIdeal_eq_span_p]
    exact PadicInt.sub_zmodRepr_mem x
  have he : Ideal.Quotient.mk m (i x) = (x.zmodRepr : O ⧸ m) := by
    have hd := map_dvd i hdiv
    simp only [map_sub, map_natCast, Nat.cast_ofNat, map_ofNat] at hd
    simpa only [map_natCast] using O12Theta.residue_congr h2 hd
  rw [hxi, map_mul, O12Theta.phase_residue hm h2 hζ, one_mul, he, hbit]
  split <;> simp

/-- Integral divisibility for the squarefree source, from the same
phase-removed rational lower bound and the same coefficient-place maps. -/
theorem phase_rational_dvd (inj : Function.Injective (algebraMap O K))
    (i : ℤ_[2] →+* O) (j : ℚ_[2] →+* K)
    (hi : ∀ x : ℤ_[2], algebraMap O K (i x) = j (x : ℚ_[2]))
    {ζ b : O} {r : ℚ} {k : ℤ} {s : ℕ}
    (h : r ≠ 0 → (s : ℤ) - k ≤ padicValRat 2 r)
    (hb : algebraMap O K b = algebraMap O K ζ * (2 : K) ^ k * (r : K)) :
    (2 : O) ^ s ∣ b := by
  obtain ⟨x, hx, _⟩ := integral_normalized r ((s : ℤ) - k) h
  refine ⟨ζ * i x, inj ?_⟩
  have hz : (s : ℤ) + -((s : ℤ) - k) = k := by omega
  rw [hb, map_mul, map_mul, map_pow, map_ofNat, hi, hx, map_mul, map_zpow₀, map_ofNat,
    map_ratCast]
  rw [mul_left_comm ((2 : K) ^ s), ← mul_assoc ((2 : K) ^ s), ← zpow_natCast,
    ← zpow_add₀ (by norm_num : (2 : K) ≠ 0), hz, mul_assoc]

#print axioms padic_two_valuation
#print axioms integral_normalized
#print axioms phase_rational_residue
#print axioms phase_rational_dvd

end ZInQ.Manuscript.RC.EvenBudget
