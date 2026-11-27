import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Point.Division

/-!
# Mattuck at `p = 2`, part 2: doubling on the formal group, from `2I` onto `4I`

Manuscript `diophantine_zq.tex`, tex 4551–4556 (the `ℤ₂^{d_w}` summand of `E^{(h)}(K_w)^∧_2`).

Let `I` be an adic ideal of a complete linearly topologised domain `O` with `2 ≠ 0`, and `Ê(I)` the
formal group of a Weierstrass curve (Tau Ceti's `FormalGroupPoint`). The doubling series
`[2](T) = 2T + a₂T² + a₃T³ + ⋯` satisfies, after rescaling `T ↦ 2T`,

`[2](2X) = 4 · G(X)`,  `G(X) = X + ∑_{k ≥ 2} aₖ 2^{k−2} Xᵏ`  (`rescale_two_nsmulSeries`),

and `G` has linear coefficient `1`, hence a compositional inverse. Consequently, on the parameters
`2I = {2t : t ∈ I}` (`aeval_two_mul`):

* `two_nsmul_coe_of_eq_two_mul`: for `P = 2t`, `t ∈ I`, the parameter of `2P` is `4 G(t)` with
  `G(t) ∈ I` — doubling maps `2I` into `4I`;
* **`eq_zero_of_two_nsmul_eq_zero_of_eq_two_mul`**: no nonzero point of `2I` is killed by `2`
  (`G` is injective on `I`, by the left inverse);
* **`exists_two_nsmul_eq_of_eq_four_mul`**: every point of `4I` is `2P` for a point `P` of `2I`
  (`G` is surjective on `I`, by the right inverse).

So doubling is a bijection from the points of `2I` onto the points of `4I`. No logarithm is used.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.Mattuck

open WeierstrassCurve

variable {O : Type*} [CommRing O]

/-- **The rescaled doubling series** `G(X) = X + ∑_{k ≥ 2} aₖ 2^{k−2} Xᵏ`, where
`[2](T) = ∑ aₖ Tᵏ`. -/
def dblSeries (W : WeierstrassCurve O) : PowerSeries O :=
  PowerSeries.mk fun k => if k = 0 then 0 else if k = 1 then 1 else
    PowerSeries.coeff k ((formalGroup W).nsmulSeries 2) * 2 ^ (k - 2)

theorem constantCoeff_dblSeries (W : WeierstrassCurve O) :
    PowerSeries.constantCoeff (dblSeries W) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, dblSeries, PowerSeries.coeff_mk]
  simp

theorem coeff_one_dblSeries (W : WeierstrassCurve O) : PowerSeries.coeff 1 (dblSeries W) = 1 := by
  rw [dblSeries, PowerSeries.coeff_mk]
  simp

/-- **`[2](2X) = 4 G(X)`.** -/
theorem rescale_two_nsmulSeries (W : WeierstrassCurve O) :
    PowerSeries.rescale (2 : O) ((formalGroup W).nsmulSeries 2) = (4 : O) • dblSeries W := by
  ext k
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_smul, smul_eq_mul, dblSeries,
    PowerSeries.coeff_mk]
  rcases k with _ | _ | k
  · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, (formalGroup W).constantCoeff_nsmulSeries 2]
    simp
  · rw [(formalGroup W).coeff_one_nsmulSeries 2]
    norm_num
  · simp only [show k + 1 + 1 ≠ 0 by omega, show k + 1 + 1 ≠ 1 by omega, ↓reduceIte,
      show k + 1 + 1 - 2 = k by omega]
    rw [pow_add, pow_add]
    ring

theorem isUnit_coeff_one_dblSeries (W : WeierstrassCurve O) :
    IsUnit (PowerSeries.coeff 1 (dblSeries W)) := by
  rw [coeff_one_dblSeries]; exact isUnit_one

variable [UniformSpace O] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
  [IsTopologicalRing O] [IsLinearTopology O O]

/-- **Evaluation at `2t`**: `[2](2t) = 4 G(t)`. -/
theorem aeval_two_mul (W : WeierstrassCurve O) {t : O} (ht : PowerSeries.HasEval t)
    (h2t : PowerSeries.HasEval (2 * t)) :
    PowerSeries.aeval h2t ((formalGroup W).nsmulSeries 2) =
      4 * PowerSeries.aeval ht (dblSeries W) := by
  have h1 := PowerSeries.hasSum_aeval h2t ((formalGroup W).nsmulSeries 2)
  have h2 := (PowerSeries.hasSum_aeval ht (dblSeries W)).mul_left 4
  refine h1.unique (h2.congr_fun ?_)
  intro d
  have hc := congrArg (PowerSeries.coeff d) (rescale_two_nsmulSeries W)
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_smul] at hc
  simp only [smul_eq_mul]
  rw [mul_pow, ← mul_assoc, mul_comm (PowerSeries.coeff d _) (2 ^ d), hc]
  ring

variable {W : WeierstrassCurve O} {I : Ideal O} [Fact (IsAdic I)]

omit [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsLinearTopology O O] in
theorem hasEval_of_mem {t : O} (ht : t ∈ I) : PowerSeries.HasEval t :=
  (Fact.out : IsAdic I).isTopologicallyNilpotent_of_mem ht

open MvPowerSeries.WithPiTopology in
/-- A power series with zero constant coefficient takes values in `I` on `I`. -/
theorem aeval_mem_of_constantCoeff_eq_zero {f : PowerSeries O}
    (hf : PowerSeries.constantCoeff f = 0) {t : O} (ht : t ∈ I) :
    PowerSeries.aeval (R := O) (hasEval_of_mem ht) f ∈ I := by
  have h := MvPowerSeries.eval₂_mem_pow (φ := RingHom.id O) continuous_id
    (PowerSeries.hasEval (hasEval_of_mem ht)) (Fact.out : IsAdic I) (k := 1)
    (fun _ ↦ by simpa using ht) f (by simp [← PowerSeries.constantCoeff_eq, hf])
  simpa [PowerSeries.coe_aeval, PowerSeries.eval₂, Algebra.algebraMap_self] using h

/-- The compositional inverse of `G`. -/
abbrev dblInv (W : WeierstrassCurve O) : PowerSeries O :=
  (dblSeries W).substInvOfIsUnit (isUnit_coeff_one_dblSeries W)

open MvPowerSeries.WithPiTopology in
/-- **`G` is surjective on `I`.** -/
theorem exists_aeval_dblSeries_eq {σ : O} (hσ : σ ∈ I) :
    ∃ (t : O) (ht : t ∈ I), PowerSeries.aeval (hasEval_of_mem ht) (dblSeries W) = σ := by
  have hQ : PowerSeries.constantCoeff (dblInv W) = 0 :=
    PowerSeries.constantCoeff_substInvOfIsUnit _ _
  have htI := aeval_mem_of_constantCoeff_eq_zero hQ hσ
  refine ⟨_, htI, ?_⟩
  have h := congrArg (PowerSeries.aeval (R := O) (hasEval_of_mem hσ))
    (PowerSeries.subst_substInvOfIsUnit_right (dblSeries W) (constantCoeff_dblSeries W)
      (isUnit_coeff_one_dblSeries W))
  rw [PowerSeries.aeval_subst (PowerSeries.HasSubst.of_constantCoeff_zero hQ)
    (PowerSeries.continuous_aeval (hasEval_of_mem hσ)) (hasEval_of_mem htI),
    PowerSeries.aeval_X] at h
  exact h

/-- Evaluation at `0` is the constant coefficient. -/
theorem aeval_zero_eq (f : PowerSeries O) (h0 : PowerSeries.HasEval (0 : O)) :
    PowerSeries.aeval h0 f = PowerSeries.constantCoeff f := by
  have h := PowerSeries.hasSum_aeval h0 f
  refine h.unique ?_
  have : (fun d => PowerSeries.coeff d f • (0 : O) ^ d) =
      fun d => if d = 0 then PowerSeries.constantCoeff f else 0 := by
    funext d
    rcases d with _ | d
    · simp
    · simp
  rw [this]
  exact hasSum_ite_eq 0 _

open MvPowerSeries.WithPiTopology in
/-- **`G` is injective on `I`.** -/
theorem eq_zero_of_aeval_dblSeries_eq_zero {t : O} (ht : t ∈ I)
    (h : PowerSeries.aeval (hasEval_of_mem ht) (dblSeries W) = 0) : t = 0 := by
  have hG := constantCoeff_dblSeries W
  have hQ : PowerSeries.constantCoeff (dblInv W) = 0 :=
    PowerSeries.constantCoeff_substInvOfIsUnit _ _
  have h0I : (0 : O) ∈ I := I.zero_mem
  have key := congrArg (PowerSeries.aeval (R := O) (hasEval_of_mem ht))
    (PowerSeries.subst_substInvOfIsUnit_left (dblSeries W) hG (isUnit_coeff_one_dblSeries W))
  rw [PowerSeries.aeval_subst (PowerSeries.HasSubst.of_constantCoeff_zero hG)
    (PowerSeries.continuous_aeval (hasEval_of_mem ht)) (by rw [h]; exact hasEval_of_mem h0I),
    PowerSeries.aeval_X] at key
  rw [← key]
  simp only [h]
  rw [aeval_zero_eq, hQ]

/-! ### Doubling on the points of `2I` -/

/-- **Doubling maps `2I` into `4I`**: for `P = 2t`, `t ∈ I`, the parameter of `2P` is `4 G(t)`. -/
theorem two_nsmul_coe_of_eq_two_mul (P : FormalGroupPoint W I) {t : O} (ht : t ∈ I)
    (hP : (P : O) = 2 * t) :
    ((2 • P : FormalGroupPoint W I) : O) =
      4 * PowerSeries.aeval (hasEval_of_mem ht) (dblSeries W) := by
  rw [FormalGroupPoint.coe_nsmul]
  have h2t : PowerSeries.HasEval (2 * t) := hP ▸ P.hasEval
  rw [← aeval_two_mul W (hasEval_of_mem ht) h2t]
  rw [PowerSeries.coe_aeval, Algebra.algebraMap_self, hP]

/-- **No nonzero point of `2I` is killed by `2`** (`O` a domain with `2 ≠ 0`). PROVED. -/
theorem eq_zero_of_two_nsmul_eq_zero_of_eq_two_mul [IsDomain O] (h2 : (2 : O) ≠ 0)
    (P : FormalGroupPoint W I) {t : O} (ht : t ∈ I) (hP : (P : O) = 2 * t)
    (h : 2 • P = 0) : P = 0 := by
  have hc := two_nsmul_coe_of_eq_two_mul P ht hP
  rw [h] at hc
  have h4 : (4 : O) ≠ 0 := by
    rw [show (4 : O) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have hG : PowerSeries.aeval (hasEval_of_mem ht) (dblSeries W) = 0 :=
    (mul_eq_zero.mp (show (4 : O) * _ = 0 from hc.symm)).resolve_left h4
  have ht0 := eq_zero_of_aeval_dblSeries_eq_zero ht hG
  apply FormalGroupPoint.ext
  rw [hP, ht0, mul_zero]
  rfl

/-- **Every point of `4I` is the double of a point of `2I`.** PROVED. -/
theorem exists_two_nsmul_eq_of_eq_four_mul (Q : FormalGroupPoint W I) {σ : O} (hσ : σ ∈ I)
    (hQ : (Q : O) = 4 * σ) :
    ∃ (P : FormalGroupPoint W I) (t : O), t ∈ I ∧ (P : O) = 2 * t ∧ 2 • P = Q := by
  obtain ⟨t, ht, hGt⟩ := exists_aeval_dblSeries_eq (W := W) hσ
  let P : FormalGroupPoint W I := ⟨2 * t, I.mul_mem_left 2 ht⟩
  refine ⟨P, t, ht, rfl, FormalGroupPoint.ext ?_⟩
  rw [two_nsmul_coe_of_eq_two_mul P ht rfl, hGt, hQ]

end ZInQ.Contrib.CloudB3RC53.Mattuck
