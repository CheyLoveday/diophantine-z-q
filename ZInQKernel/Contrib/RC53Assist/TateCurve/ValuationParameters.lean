import ZInQKernel.Contrib.RC53Assist.TateCurve.PrintedUniformization
import ZInQKernel.Contrib.RC53Assist.TateCurve.InertiaRoots

/-!
# Valuation facts for Tate parameters

Multiplicative reduction gives a nonintegral `j`-invariant. Such a
`j`-invariant is neither zero nor 1728, so the curve has only the two
Weierstrass automorphisms relevant to quadratic descent. An admissible Tate
parameter has infinite order, also after passing to the algebraic closure.

References: the definitions of multiplicative reduction and of `j`;
Silverman, AEC, VII.5 and Appendix C, §14. All results below are proved.
-/

noncomputable section

set_option maxHeartbeats 800000

namespace ZInQ.Contrib.RC53Assist.TateCurve

open WeierstrassCurve IsDiscreteValuationRing
open scoped Classical WithZero

section Valuations

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

/-- **PROVED**: an integer has valuation at most one.
Locator: the valuation triangle inequality, by induction. -/
theorem valuation_natCast_le_one (v : Valuation K Γ) (n : ℕ) : v (n : K) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ]
    exact (v.map_add _ _).trans (max_le ih (by rw [map_one]))

/-- **PROVED**: nonintegral `j` forces nonzero `c₄` and `c₆`.
Locator: `j = c₄³/Δ` and `c₄³-c₆² = 1728Δ`. -/
theorem nonintegral_j_invariants (v : Valuation K Γ) (E : WeierstrassCurve K)
    [E.IsElliptic] (hJ : 1 < v E.j) : E.c₄ ≠ 0 ∧ E.c₆ ≠ 0 := by
  constructor
  · intro h4
    have hj := E.j_eq_zero h4
    rw [hj, map_zero] at hJ
    exact not_lt_of_ge zero_le_one hJ
  · intro h6
    have hc : E.c₄ ^ 3 = 1728 * E.Δ := by
      have h := E.c_relation
      rw [h6, zero_pow two_ne_zero, sub_zero] at h
      exact h.symm
    have hj : E.j = 1728 := by
      rw [E.j_eq, hc, mul_comm (1728 : K) E.Δ, ← mul_assoc,
        inv_mul_cancel₀ E.isUnit_Δ.ne_zero, one_mul]
    rw [hj] at hJ
    exact not_lt_of_ge (valuation_natCast_le_one v 1728) hJ

/-- **PROVED**: an element of valuation less than one has infinite
multiplicative order. Locator: a finite-order unit has valuation one. -/
theorem admissible_parameter_infinite_order (v : Valuation K Γ) (q : Kˣ)
    (hq : v (q : K) < 1) : Function.Injective fun m : ℤ => q ^ m := by
  rw [injective_zpow_iff_not_isOfFinOrder]
  intro hfin
  obtain ⟨N, hN, hpow⟩ := hfin.exists_pow_eq_one
  have hval := valuation_of_torsion_unit v.valuationSubring N hN.ne' q hpow
  have hv : v (q : K) = 1 :=
    (Valuation.isEquiv_valuation_valuationSubring v).eq_one_iff_eq_one.mpr hval
  exact hq.ne hv

end Valuations

section Discrete

variable {K : Type*} [Field K]

/-- **PROVED**: the canonical DVR valuation and the original valuation
have the same valuation subring. Locator: the DVR fraction-field valuation. -/
theorem maximalIdeal_valuationSubring_eq (A : ValuationSubring K)
    [IsDiscreteValuationRing A] :
    ((IsDiscreteValuationRing.maximalIdeal A).valuation K).valuationSubring = A := by
  have h := IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring (A := A) (K := K)
  ext x
  change x ∈
    ((IsDiscreteValuationRing.maximalIdeal A).valuation K).valuationSubring.toSubring ↔
      x ∈ A.toSubring
  rw [← h, Subring.mem_map]
  constructor
  · rintro ⟨a, _, rfl⟩
    exact a.property
  · intro hx
    exact ⟨⟨x, hx⟩, Subring.mem_top _, rfl⟩

/-- **PROVED**: multiplicative reduction gives `|j| > 1`, in the
multiplicative-valuation convention. Locator: `HasMultiplicativeReduction`
and `j = c₄³/Δ`; invariance under minimal-model change of variables. -/
theorem multiplicative_j_nonintegral [Valued K ℤᵐ⁰]
    [IsDiscreteValuationRing (Valued.v.valuationSubring : ValuationSubring K)]
    (E : WeierstrassCurve K) [E.IsElliptic]
    (hM : WeierstrassCurve.HasMultiplicativeReduction
      (Valued.v.valuationSubring : ValuationSubring K)
      (E.minimal (Valued.v.valuationSubring : ValuationSubring K))) :
    1 < Valued.v E.j := by
  let A := (Valued.v.valuationSubring : ValuationSubring K)
  let W := E.minimal A
  letI : W.IsElliptic := by
    change ((E.exists_isMinimal A).choose • E).IsElliptic
    infer_instance
  let d := (IsDiscreteValuationRing.maximalIdeal A).valuation K
  have hd : d.IsEquiv (Valued.v : Valuation K ℤᵐ⁰) :=
    (Valuation.isEquiv_iff_valuationSubring _ _).mpr (maximalIdeal_valuationSubring_eq A)
  have h4 : Valued.v W.c₄ = 1 := hd.eq_one_iff_eq_one.mp hM.multiplicativeReduction
  have hΔ : Valued.v W.Δ < 1 := hd.lt_one_iff_lt_one.mp hM.badReduction
  have hΔ0 : 0 < Valued.v W.Δ := by
    simpa only [Valuation.pos_iff] using W.isUnit_Δ.ne_zero
  have hj : W.j = E.j := by simp [W, WeierstrassCurve.minimal]
  rw [← hj, W.j_eq, map_mul, map_inv₀, map_pow, h4, one_pow, mul_one]
  exact (inv_lt_inv₀ zero_lt_one hΔ0).mpr hΔ

end Discrete

section Closure

variable {K : Type*} [Field K] [CharZero K] [Valued K ℤᵐ⁰]

/-- **PROVED**: an admissible Tate parameter has infinite order in the
algebraic closure. Locator: `admissible_parameter_infinite_order` and the
injectivity of the field embedding. -/
theorem closureParameter_infinite_order (q : Kˣ) (hq : Valued.v (q : K) < 1) :
    Function.Injective fun m : ℤ => closureParameter q ^ m := by
  have hb := admissible_parameter_infinite_order Valued.v q hq
  have hu : Function.Injective (Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom) := by
    intro x y h
    apply Units.ext
    apply (algebraMap K (AlgebraicClosure K)).injective
    exact congrArg Units.val h
  intro a b h
  change Units.map _ q ^ a = Units.map _ q ^ b at h
  rw [← map_zpow, ← map_zpow] at h
  exact hb (hu h)

end Closure

end ZInQ.Contrib.RC53Assist.TateCurve
