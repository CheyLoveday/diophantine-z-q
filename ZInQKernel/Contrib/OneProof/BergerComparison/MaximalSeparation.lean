import ZInQKernel.Contrib.OneProof.BergerComparison.CoefficientFrobenius

/-! The embedded maximal ring is p-adically separated. This permits
checking identities between maps into it on finite period expressions. -/

noncomputable section

namespace ZInQ.Manuscript.BergerComparison

open HDec.PkgI4 BergerBst FontaineSt PowerSeries Ideal
open PanBergerSplit (Ainf AinfP)
open ZInQ.Contrib.G9.BdrKer.Cp

variable (p : ℕ) [hp : Fact p.Prime]

private abbrev relation := maximalRelSub p

private theorem dvd_relation_mul (k : ℕ) (g : restricted p)
    (h : (p : restricted p)^k ∣ relation p * g) : (p : restricted p)^k ∣ g := by
  apply (pDvd_iff_coeff p g k).mpr
  have hh := (pDvd_iff_coeff p _ k).mp h
  intro n
  induction n with
  | zero =>
    specialize hh 0
    change (p : Ainf p)^k ∣ coeff 0 (maximalRelation p * g.val) at hh
    apply pow_p_dvd_of_dvd_xi_mul p k
    simpa only [maximalRelation, sub_mul, map_sub, mul_assoc, PowerSeries.coeff_zero_X_mul,
      PowerSeries.coeff_C_mul, sub_zero] using hh
  | succ n ih =>
    specialize hh (n + 1)
    change (p : Ainf p)^k ∣ coeff (n + 1) (maximalRelation p * g.val) at hh
    simp only [maximalRelation, sub_mul, map_sub, mul_assoc, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_C_mul] at hh
    apply pow_p_dvd_of_dvd_xi_mul p k
    simpa only [sub_add_cancel] using dvd_add hh (Dvd.dvd.mul_left ih (p : Ainf p))

/-- Equality in the maximal period image can be tested modulo all p-powers. -/
theorem amax_eq_zero_of_pDvd (b : Amax p) (h : ∀ k, (p : Amax p)^k ∣ b) : b = 0 := by
  obtain ⟨f, rfl⟩ := maxToImage_surjective p b
  have hex (k : ℕ) : ∃ q : restricted p, (p : restricted p)^k ∣ f - relation p * q := by
    obtain ⟨y, hy⟩ := h k
    obtain ⟨g, rfl⟩ := maxToImage_surjective p y
    have he : maxToImage p (f - (p : restricted p)^k * g) = 0 := by
      rw [map_sub, map_mul, map_pow, map_natCast, ← hy, sub_self]
    have hzero : maximalEval p ((f - (p : restricted p)^k * g : restricted p).val) = 0 :=
      congrArg Subtype.val he
    obtain ⟨q, hq, hrel⟩ :=
      (maximalEval_zero_iff p (f - (p : restricted p)^k * g).property).mp hzero
    have hEq : f - (p : restricted p)^k * g = relation p * ⟨q, hq⟩ := Subtype.ext hrel
    refine ⟨⟨q, hq⟩, g, ?_⟩
    rw [← hEq, sub_sub_cancel]
  choose q hq using hex
  have hC (k l : ℕ) (hkl : k ≤ l) : (p : restricted p)^k ∣ q k - q l := by
    apply dvd_relation_mul p
    rw [show relation p * (q k - q l) = (f - relation p * q l) -
      (f - relation p * q k) by ring]
    exact dvd_sub ((pow_dvd_pow _ hkl).trans (hq l)) (hq k)
  obtain ⟨L, hL⟩ := exists_restricted_limit p q hC
  have hf : f = relation p * L := by
    apply (IsHausdorff.eq_iff_smodEq (I := Ideal.span {(p : restricted p)})).mpr
    intro k
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    convert dvd_add (hq k) (Dvd.dvd.mul_left (hL k) (relation p)) using 1
    ring
  rw [hf, map_mul]
  have hrel : maxToImage p (relation p) = 0 := Subtype.ext (maximalEval_relation p)
  rw [hrel, zero_mul]

/-- A finite polynomial represents any restricted series modulo a prescribed
power of p. -/
theorem exists_polynomial_mod_pPow (f : restricted p) (k : ℕ) :
    ∃ Q : Polynomial (Ainf p),
      (p : restricted p)^k ∣ f - ⟨Q, polynomial_mem_restricted p Q⟩ := by
  obtain ⟨N, hN⟩ := f.property k
  refine ⟨trunc N f.val, (pDvd_iff_coeff p _ _).mpr fun n => ?_⟩
  change (p : Ainf p)^k ∣ coeff n (f.val - ((trunc N f.val : Polynomial _) : (Ainf p)⟦X⟧))
  rw [map_sub, Polynomial.coeff_coe, coeff_trunc]
  split_ifs with h
  · rw [sub_self]; exact dvd_zero _
  · rw [sub_zero]; exact hN n (le_of_not_gt h)

/-- Two maps into the maximal image agree if they agree on all finite
polynomials before taking the source image. -/
theorem restricted_to_amax_ext (g₁ g₂ : restricted p →+* Amax p)
    (h : ∀ Q : Polynomial (Ainf p), g₁ ⟨Q, polynomial_mem_restricted p Q⟩ =
      g₂ ⟨Q, polynomial_mem_restricted p Q⟩) : g₁ = g₂ := by
  apply RingHom.ext
  intro f
  apply sub_eq_zero.mp
  apply amax_eq_zero_of_pDvd p
  intro k
  obtain ⟨Q, hQ⟩ := exists_polynomial_mod_pPow p f k
  have h₁ := map_dvd g₁ hQ
  have h₂ := map_dvd g₂ hQ
  rw [map_sub, map_pow, map_natCast, h Q] at h₁
  rw [map_sub, map_pow, map_natCast] at h₂
  convert dvd_sub h₁ h₂ using 1
  ring

end ZInQ.Manuscript.BergerComparison
