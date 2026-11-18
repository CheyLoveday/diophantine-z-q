import ZInQKernel.Contrib.OneProof.RC.TwistDictionary.Model
import ZInQKernel.RouteK.Rank.LFunctionCd

/-!
# Lane RC18-twist: Mathlib's local polynomial is an isomorphism invariant

Mathlib's `WeierstrassCurve.localPolynomial` is computed from a minimal model chosen by
`Classical.choice`. Two minimal models differ by a change of variables with `u` a unit, which
descends to the valuation ring, so they have the same reduction type (good, multiplicative, split
multiplicative) and isomorphic reductions. Hence `localPolynomial` can be computed from any minimal
model (`localPolynomial_of_isMinimal`) and does not change under a change of variables
(`localPolynomial_smul`). `hasSplitMultiplicativeReduction_iff` reads the split condition on the
reduction through `splitPoly`.
-/

namespace ZInQ.Manuscript.RC.TwistDictionary

open WeierstrassCurve Polynomial

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- **`splitPoly` under a change of variables** (PROVED): over any commutative ring,
`splitPoly ((u, r, s, t) • V) = u⁻⁶ · (splitPoly V)(u X + s)`. -/
theorem splitPoly_smul {S : Type*} [CommRing S] (V : WeierstrassCurve S) (D : VariableChange S) :
    splitPoly (D • V) = Polynomial.C ((↑D.u⁻¹ : S) ^ 6) *
      (splitPoly V).comp (Polynomial.C (D.u : S) * X + Polynomial.C D.s) := by
  have h : Polynomial.C (D.u : S) * Polynomial.C (↑D.u⁻¹ : S) = 1 := by
    rw [← Polynomial.C_mul, Units.mul_inv, Polynomial.C_1]
  have hc : Polynomial.C V.c₄ = Polynomial.C V.b₂ ^ 2 - 24 * Polynomial.C V.b₄ := by
    rw [c₄, map_sub, map_pow, map_mul, map_ofNat]
  simp only [splitPoly, variableChange_c₄, variableChange_a₁, variableChange_a₂,
    variableChange_b₂, variableChange_b₄, variableChange_b₆, sub_comp, add_comp, mul_comp,
    C_comp, X_comp, X_pow_comp]
  simp only [map_mul, map_sub, map_add, map_pow, map_ofNat]
  linear_combination (-(Polynomial.C (↑D.u⁻¹ : S) ^ 4 * Polynomial.C V.c₄ *
    (Polynomial.C (↑D.u⁻¹ : S) * Polynomial.C (D.u : S) + 1) * X ^ 2 +
    Polynomial.C (↑D.u⁻¹ : S) ^ 5 * Polynomial.C V.c₄ *
      (Polynomial.C V.a₁ + 2 * Polynomial.C D.s) * X)) * h +
    (-3 * Polynomial.C (↑D.u⁻¹ : S) ^ 6 * Polynomial.C D.r) * hc

/-- Over a field, multiplying by a nonzero constant does not change whether a polynomial
splits. -/
theorem splits_C_mul_iff_of_ne_zero {F : Type*} [Field F] {a : F} (ha : a ≠ 0) (f : F[X]) :
    Splits (Polynomial.C a * f) ↔ Splits f := by
  refine ⟨fun h => ?_, fun h => h.C_mul a⟩
  have := h.C_mul a⁻¹
  rwa [← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ ha, Polynomial.C_1, one_mul] at this

/-- Over a field, whether `splitPoly` splits does not change under a change of variables
(PROVED). -/
theorem splits_splitPoly_smul_iff {F : Type*} [Field F] (V : WeierstrassCurve F)
    (D : VariableChange F) : Splits (splitPoly (D • V)) ↔ Splits (splitPoly V) := by
  rw [splitPoly_smul, splits_C_mul_iff_of_ne_zero (pow_ne_zero _ (Units.ne_zero _)),
    ← splits_iff_comp_splits_of_natDegree_eq_one (natDegree_linear (Units.ne_zero _))]

/-- **Split multiplicative reduction through the reduction** (PROVED): for a minimal `W`, split
multiplicative reduction is multiplicative reduction with `splitPoly (W.reduction R)` split. -/
theorem hasSplitMultiplicativeReduction_iff (W : WeierstrassCurve K) [IsMinimal R W] :
    W.HasSplitMultiplicativeReduction R ↔
      W.HasMultiplicativeReduction R ∧ Splits (splitPoly (W.reduction R)) := by
  have key : Splits (splitPoly (W.reduction R)) ↔
      Splits ((splitPoly (integralModel R W)).map (algebraMap R (IsLocalRing.ResidueField R))) := by
    rw [IsLocalRing.ResidueField.algebraMap_eq, splitPoly_map, reduction]
  rw [WeierstrassCurve.hasSplitMultiplicativeReduction_iff, key]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h2⟩⟩

/-- Two minimal models related by a change of variables: same good reduction (PROVED). -/
theorem hasGoodReduction_smul_iff (W : WeierstrassCurve K) (hΔ : W.Δ ≠ 0) (C : VariableChange K)
    [IsMinimal R W] [IsMinimal R (C • W)] :
    (C • W).HasGoodReduction R ↔ W.HasGoodReduction R := by
  have hu := ZInQ.Literature.vK_u_eq_one (R := R) hΔ C
  have h1 : IsMinimal R W := inferInstance
  have h2 : IsMinimal R (C • W) := inferInstance
  simp only [hasGoodReduction_iff, variableChange_Δ, map_mul, map_pow, Units.val_inv_eq_inv_val,
    map_inv₀, hu, inv_one, one_pow, one_mul, h1, h2, true_and]

/-- Two minimal models related by a change of variables: same multiplicative reduction (PROVED). -/
theorem hasMultiplicativeReduction_smul_iff (W : WeierstrassCurve K) (hΔ : W.Δ ≠ 0)
    (C : VariableChange K) [IsMinimal R W] [IsMinimal R (C • W)] :
    (C • W).HasMultiplicativeReduction R ↔ W.HasMultiplicativeReduction R := by
  have hu := ZInQ.Literature.vK_u_eq_one (R := R) hΔ C
  have h1 : IsMinimal R W := inferInstance
  have h2 : IsMinimal R (C • W) := inferInstance
  simp only [hasMultiplicativeReduction_iff, variableChange_Δ, variableChange_c₄, map_mul, map_pow,
    Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one, one_pow, one_mul, h1, h2, true_and]

/-- Two minimal models related by a change of variables: same split multiplicative reduction
(PROVED). -/
theorem hasSplitMultiplicativeReduction_smul_iff (W : WeierstrassCurve K) (hΔ : W.Δ ≠ 0)
    (C : VariableChange K) [IsMinimal R W] [IsMinimal R (C • W)] :
    (C • W).HasSplitMultiplicativeReduction R ↔ W.HasSplitMultiplicativeReduction R := by
  obtain ⟨C', hC'⟩ := ZInQ.Literature.exists_reduction_variableChange (R := R) W C
    (ZInQ.Literature.vK_u_eq_one hΔ C)
  rw [ZInQ.Manuscript.RC.TwistDictionary.hasSplitMultiplicativeReduction_iff,
    ZInQ.Manuscript.RC.TwistDictionary.hasSplitMultiplicativeReduction_iff,
    hasMultiplicativeReduction_smul_iff W hΔ C, hC', splits_splitPoly_smul_iff]

/-- Two minimal models related by a change of variables, with good reduction: their reductions
have the same number of points (PROVED). -/
theorem natCard_point_reduction_smul (W : WeierstrassCurve K) (hΔ : W.Δ ≠ 0)
    (C : VariableChange K) [IsMinimal R W] [IsMinimal R (C • W)] (hg : W.HasGoodReduction R) :
    Nat.card ((C • W).reduction R).toAffine.Point = Nat.card (W.reduction R).toAffine.Point := by
  obtain ⟨C', hC'⟩ := ZInQ.Literature.exists_reduction_variableChange (R := R) W C
    (ZInQ.Literature.vK_u_eq_one hΔ C)
  have : (W.reduction R).IsElliptic := (hasGoodReduction_iff_isElliptic_reduction R).mp hg
  rw [hC', ZInQ.Literature.natCard_point_variableChange]

open scoped Classical in
/-- The `if` chain of `localPolynomial` takes the same value on two minimal models related by a
change of variables (PROVED). -/
theorem localPolynomial_chain_eq_of_eq_smul {V V' : WeierstrassCurve K} (hΔ : V.Δ ≠ 0)
    (D : VariableChange K) (h : V' = D • V) [IsMinimal R V] [IsMinimal R V'] :
    (if V'.HasGoodReduction R then
        1 - C ((Nat.card (IsLocalRing.ResidueField R) : ℤ) + 1 -
          Nat.card (V'.reduction R).toAffine.Point) * X +
          C (Nat.card (IsLocalRing.ResidueField R) : ℤ) * X ^ 2
      else if V'.HasSplitMultiplicativeReduction R then 1 - X
      else if V'.HasMultiplicativeReduction R then 1 + X
      else 1) =
    (if V.HasGoodReduction R then
        1 - C ((Nat.card (IsLocalRing.ResidueField R) : ℤ) + 1 -
          Nat.card (V.reduction R).toAffine.Point) * X +
          C (Nat.card (IsLocalRing.ResidueField R) : ℤ) * X ^ 2
      else if V.HasSplitMultiplicativeReduction R then 1 - X
      else if V.HasMultiplicativeReduction R then 1 + X
      else 1) := by
  subst h
  by_cases hg : V.HasGoodReduction R
  · rw [ite_eq_left hg, ite_eq_left ((hasGoodReduction_smul_iff V hΔ D).mpr hg),
      natCard_point_reduction_smul V hΔ D hg]
  rw [ite_eq_right hg, ite_eq_right (mt (hasGoodReduction_smul_iff V hΔ D).mp hg)]
  by_cases hs : V.HasSplitMultiplicativeReduction R
  · rw [ite_eq_left hs, ite_eq_left ((hasSplitMultiplicativeReduction_smul_iff V hΔ D).mpr hs)]
  rw [ite_eq_right hs, ite_eq_right (mt (hasSplitMultiplicativeReduction_smul_iff V hΔ D).mp hs)]
  by_cases hm : V.HasMultiplicativeReduction R
  · rw [ite_eq_left hm, ite_eq_left ((hasMultiplicativeReduction_smul_iff V hΔ D).mpr hm)]
  rw [ite_eq_right hm, ite_eq_right (mt (hasMultiplicativeReduction_smul_iff V hΔ D).mp hm)]

open scoped Classical in
/-- **`localPolynomial` from any minimal model** (PROVED). -/
theorem localPolynomial_of_isMinimal (W : WeierstrassCurve K) (hΔ : W.Δ ≠ 0) [IsMinimal R W] :
    W.localPolynomial R =
      if W.HasGoodReduction R then
        1 - C ((Nat.card (IsLocalRing.ResidueField R) : ℤ) + 1 -
          Nat.card (W.reduction R).toAffine.Point) * X +
          C (Nat.card (IsLocalRing.ResidueField R) : ℤ) * X ^ 2
      else if W.HasSplitMultiplicativeReduction R then 1 - X
      else if W.HasMultiplicativeReduction R then 1 + X
      else 1 := by
  unfold localPolynomial
  exact localPolynomial_chain_eq_of_eq_smul hΔ _ (ZInQ.Literature.minimal_eq_smul W)

/-- **`localPolynomial` is invariant under changes of variables** (PROVED). -/
theorem localPolynomial_smul (W : WeierstrassCurve K) (hΔ : W.Δ ≠ 0) (C : VariableChange K) :
    (C • W).localPolynomial R = W.localPolynomial R := by
  have hΔ₀ : (W.minimal R).Δ ≠ 0 := by
    rw [ZInQ.Literature.minimal_eq_smul, variableChange_Δ]
    exact mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) hΔ
  have h : (C • W).minimal R = (((C • W).exists_isMinimal R).choose * C *
      (W.exists_isMinimal R).choose⁻¹) • W.minimal R := by
    rw [ZInQ.Literature.minimal_eq_smul (C • W), ZInQ.Literature.minimal_eq_smul W, mul_smul,
      mul_smul, inv_smul_smul]
  unfold localPolynomial
  exact localPolynomial_chain_eq_of_eq_smul hΔ₀ _ h

end ZInQ.Manuscript.RC.TwistDictionary
