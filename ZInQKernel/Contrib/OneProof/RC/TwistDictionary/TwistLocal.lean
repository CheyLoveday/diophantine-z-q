import ZInQKernel.Contrib.OneProof.RC.TwistDictionary.Model
import ZInQKernel.RouteK.Rank.LFunctionCd

/-!
# Lane RC18-twist: the twist of a minimal model by a unit

Over a discrete valuation ring `R` with fraction field `K` (`2 ≠ 0` in `K`), let `M` be a minimal
Weierstrass model and `D = 1 + 4c` a unit of `R`. The integral model
`T = twistInt (integralModel R M) D c` of the twist `M^{(D)}` is again minimal
(`isMinimal_twistInt`): an integral model of `M^{(D)}` with smaller discriminant would, twisted back
by `D` (`twistK (twistK X D) D ≅ X`), give an integral model of `M` with smaller discriminant. Since
`Δ(T) = D⁶ Δ(M)` and `c₄(T) = D² c₄(M)` with `D` a unit, `T` and `M` have the same reduction type
(`hasGoodReduction_twistInt_iff`, `hasMultiplicativeReduction_twistInt_iff`), and the reduction of
`T` is the twist of the reduction of `M` (`reduction_twistInt`).

All results here are `PROVED`.
-/

namespace ZInQ.Manuscript.RC.TwistDictionary

open WeierstrassCurve IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

section Iso

variable {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
include h2

/-- Twisting twice by `d ≠ 0` gives back the curve, up to a change of variables. -/
theorem exists_smul_twistK_twistK (X : WeierstrassCurve K) {d : K} (hd : d ≠ 0) :
    ∃ C : VariableChange K, C • twistK (twistK X d) d = X := by
  refine ⟨(sqChange X)⁻¹ * (⟨Units.mk0 d⁻¹ (inv_ne_zero hd), 0, 0, 0⟩ : VariableChange K)⁻¹, ?_⟩
  rw [twistK_twistK X h2, show d * d = 1 * d ^ 2 by ring, twistK_mul_sq X h2 1 hd,
    twistK_one X h2, mul_smul, inv_smul_smul, inv_smul_smul]

/-- A change of variables of `X` twists to a change of variables of the twist. -/
theorem exists_smul_twistK_of_smul {X Y : WeierstrassCurve K} {C : VariableChange K}
    (hC : C • X = Y) (d : K) : ∃ C' : VariableChange K, C' • twistK X d = twistK Y d :=
  ⟨⟨C.u, d * C.r, 0, 0⟩, by rw [← hC, twistK_smul X h2]⟩

end Iso

section Generic

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]


omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- The base change of `twistInt` to the fraction field is a change of variables of `twistK`. -/
theorem baseChange_twistInt (h2 : (2 : K) ≠ 0) (W : WeierstrassCurve R) {D c : R}
    (hDc : D = 1 + 4 * c) :
    ∃ C : VariableChange K, C • twistK (W.baseChange K) (algebraMap R K D) =
      (twistInt W D c).baseChange K := by
  have hDc' : algebraMap R K D = 1 + 4 * algebraMap R K c := by
    rw [hDc, map_add, map_mul, map_one, map_ofNat]
  refine ⟨(sqChange (twistInt (W.map (algebraMap R K)) (algebraMap R K D) (algebraMap R K c)))⁻¹,
    ?_⟩
  show _ • twistK (W.map (algebraMap R K)) _ = (twistInt W D c).map (algebraMap R K)
  rw [twistInt_map, ← twistInt_eq_smul_twistK _ h2 hDc']

/-- A unit of `R` has valuation `1`. -/
theorem vK_algebraMap_of_isUnit {D : R} (hD : IsUnit D) : (valuation K (IsDiscreteValuationRing.maximalIdeal R)) (algebraMap R K D) = 1 := by
  rw [valuation_of_algebraMap, intValuation_eq_one_iff]
  exact IsLocalRing.notMem_maximalIdeal.mpr hD

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- The discriminant of the base change of `twistInt`. -/
theorem baseChange_twistInt_Δ (W : WeierstrassCurve R) {D c : R} (hDc : D = 1 + 4 * c) :
    ((twistInt W D c).baseChange K).Δ = algebraMap R K D ^ 6 * (W.baseChange K).Δ := by
  simp only [baseChange, map_Δ, twistInt_Δ W hDc, map_mul, map_pow]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- The `c₄` of the base change of `twistInt`. -/
theorem baseChange_twistInt_c₄ (W : WeierstrassCurve R) {D c : R} (hDc : D = 1 + 4 * c) :
    ((twistInt W D c).baseChange K).c₄ = algebraMap R K D ^ 2 * (W.baseChange K).c₄ := by
  simp only [baseChange, map_c₄, twistInt_c₄ W hDc, map_mul, map_pow]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- The integral twist of `M` is a change of variables of `twistK M D`. -/
theorem exists_smul_twistK_eq_twistInt (h2 : (2 : K) ≠ 0) (M : WeierstrassCurve K)
    [IsIntegral R M] {D c : R} (hDc : D = 1 + 4 * c) :
    ∃ C : VariableChange K, C • twistK M (algebraMap R K D) =
      (twistInt (integralModel R M) D c).baseChange K := by
  obtain ⟨C, hC⟩ := baseChange_twistInt h2 (integralModel R M) hDc
  rw [baseChange_integralModel_eq] at hC
  exact ⟨C, hC⟩

/-- **The twist of a minimal model by a unit is minimal** (PROVED). -/
theorem isMinimal_twistInt (h2 : (2 : K) ≠ 0) (M : WeierstrassCurve K) [hM : IsMinimal R M]
    {D c : R} (hDc : D = 1 + 4 * c) (hD : IsUnit D) :
    IsMinimal R ((twistInt (integralModel R M) D c).baseChange K) := by
  set T := (twistInt (integralModel R M) D c).baseChange K with hT
  have hTi : IsIntegral R T := ⟨twistInt (integralModel R M) D c, rfl⟩
  have hDK : algebraMap R K D ≠ 0 := by
    intro h0
    have := vK_algebraMap_of_isUnit (K := K) hD
    rw [h0, map_zero] at this
    exact zero_ne_one this
  refine ⟨⟨by simpa using hTi, fun j hj hle => ?_⟩⟩
  simp only [one_smul] at hle ⊢
  -- the integral model `J` of `j • T`, and its twist back `T'`
  set J := integralModel R (j • T)
  have hJ : J.baseChange K = j • T := baseChange_integralModel_eq R (j • T)
  -- `T' := (twistInt J D c)_K` is a change of variables of `M`
  obtain ⟨C₁, hC₁⟩ := baseChange_twistInt h2 J hDc
  obtain ⟨C₂, hC₂⟩ : ∃ C : VariableChange K, C • twistK M (algebraMap R K D) = T :=
    exists_smul_twistK_eq_twistInt h2 M hDc
  obtain ⟨C₃, hC₃⟩ := exists_smul_twistK_of_smul h2 hC₂ (algebraMap R K D)
  obtain ⟨C₄, hC₄⟩ := exists_smul_twistK_twistK h2 M hDK
  obtain ⟨C₅, hC₅⟩ := exists_smul_twistK_of_smul h2 (rfl : j • T = j • T) (algebraMap R K D)
  have e4 : twistK (twistK M (algebraMap R K D)) (algebraMap R K D) = C₄⁻¹ • M := by
    rw [eq_inv_smul_iff]; exact hC₄
  -- `twistK (j • T) D = C₅ • twistK T D`, `twistK T D = C₃ • twistK (twistK M D) D`
  have hM' : (C₁ * C₅ * C₃ * C₄⁻¹) • M = (twistInt J D c).baseChange K := by
    rw [← hC₁, hJ, ← hC₅, ← hC₃, e4, mul_smul, mul_smul, mul_smul]
  have hIM : IsIntegral R ((C₁ * C₅ * C₃ * C₄⁻¹) • M) := by
    rw [hM']; exact ⟨twistInt J D c, rfl⟩
  have key := hM.val_Δ_maximal.2 (j := C₁ * C₅ * C₃ * C₄⁻¹) hIM
  simp only [one_smul] at key
  have := hTi
  have : IsIntegral R (j • T) := hj
  have := hIM
  have aux : ∀ (X : WeierstrassCurve K) [IsIntegral R X],
      ((valuation_Δ_aux R X : { v : WithZero (Multiplicative ℤ) // v ≤ 1 }) :
        WithZero (Multiplicative ℤ)) = (valuation K (IsDiscreteValuationRing.maximalIdeal R)) X.Δ :=
    fun X _ => valuation_Δ_aux_eq_of_isIntegral R X
  rw [← Subtype.coe_le_coe, aux, aux] at hle ⊢
  have key' : (valuation K (IsDiscreteValuationRing.maximalIdeal R)) M.Δ ≤ (valuation K (IsDiscreteValuationRing.maximalIdeal R)) ((C₁ * C₅ * C₃ * C₄⁻¹) • M).Δ →
      (valuation K (IsDiscreteValuationRing.maximalIdeal R)) ((C₁ * C₅ * C₃ * C₄⁻¹) • M).Δ ≤ (valuation K (IsDiscreteValuationRing.maximalIdeal R)) M.Δ := by
    intro h
    have := key (by rw [← Subtype.coe_le_coe, aux, aux]; exact h)
    rwa [← Subtype.coe_le_coe, aux, aux] at this
  have hvT : (valuation K (IsDiscreteValuationRing.maximalIdeal R)) T.Δ = (valuation K (IsDiscreteValuationRing.maximalIdeal R)) M.Δ := by
    rw [hT, baseChange_twistInt_Δ _ hDc, baseChange_integralModel_eq, map_mul, map_pow,
      vK_algebraMap_of_isUnit hD, one_pow, one_mul]
  have hvT' : (valuation K (IsDiscreteValuationRing.maximalIdeal R)) ((C₁ * C₅ * C₃ * C₄⁻¹) • M).Δ = (valuation K (IsDiscreteValuationRing.maximalIdeal R)) (j • T).Δ := by
    rw [hM', baseChange_twistInt_Δ _ hDc, hJ, map_mul, map_pow, vK_algebraMap_of_isUnit hD,
      one_pow, one_mul]
  rw [hvT, ← hvT'] at hle ⊢
  exact key' hle

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- The integral model of the twist is `twistInt` of the integral model of `M`. -/
theorem integralModel_twistInt (M : WeierstrassCurve K) [IsIntegral R M] (D c : R)
    [IsIntegral R ((twistInt (integralModel R M) D c).baseChange K)] :
    integralModel R ((twistInt (integralModel R M) D c).baseChange K) =
      twistInt (integralModel R M) D c := by
  apply WeierstrassCurve.map_injective (IsFractionRing.injective R K)
  exact baseChange_integralModel_eq R _

/-- **The reduction of the twist is the twist of the reduction** (PROVED). -/
theorem reduction_twistInt (M : WeierstrassCurve K) [IsMinimal R M] (D c : R)
    [IsMinimal R ((twistInt (integralModel R M) D c).baseChange K)] :
    ((twistInt (integralModel R M) D c).baseChange K).reduction R =
      twistInt (M.reduction R) (IsLocalRing.residue R D) (IsLocalRing.residue R c) := by
  rw [reduction, integralModel_twistInt M D c, reduction, twistInt_map]

/-- **Same good reduction** (PROVED). -/
theorem hasGoodReduction_twistInt_iff (M : WeierstrassCurve K) [hM : IsMinimal R M] {D c : R}
    (hDc : D = 1 + 4 * c) (hD : IsUnit D)
    [IsMinimal R ((twistInt (integralModel R M) D c).baseChange K)] :
    ((twistInt (integralModel R M) D c).baseChange K).HasGoodReduction R ↔
      M.HasGoodReduction R := by
  rw [hasGoodReduction_iff, hasGoodReduction_iff, baseChange_twistInt_Δ _ hDc,
    baseChange_integralModel_eq, map_mul, map_pow, vK_algebraMap_of_isUnit hD, one_pow, one_mul]
  exact ⟨fun h => ⟨hM, h.2⟩, fun h => ⟨inferInstance, h.2⟩⟩

/-- **Same multiplicative reduction** (PROVED). -/
theorem hasMultiplicativeReduction_twistInt_iff (M : WeierstrassCurve K) [hM : IsMinimal R M]
    {D c : R} (hDc : D = 1 + 4 * c) (hD : IsUnit D)
    [IsMinimal R ((twistInt (integralModel R M) D c).baseChange K)] :
    ((twistInt (integralModel R M) D c).baseChange K).HasMultiplicativeReduction R ↔
      M.HasMultiplicativeReduction R := by
  rw [hasMultiplicativeReduction_iff, hasMultiplicativeReduction_iff,
    baseChange_twistInt_Δ _ hDc, baseChange_twistInt_c₄ _ hDc, baseChange_integralModel_eq]
  simp only [map_mul, map_pow, vK_algebraMap_of_isUnit hD, one_pow, one_mul]
  exact ⟨fun h => ⟨hM, h.2⟩, fun h => ⟨inferInstance, h.2⟩⟩

end Generic

end ZInQ.Manuscript.RC.TwistDictionary
