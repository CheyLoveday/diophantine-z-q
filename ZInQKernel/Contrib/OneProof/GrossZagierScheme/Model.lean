import ZInQKernel.Contrib.OneProof.GrossZagierAlgebraic.X0Model
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_phiIrreducible_of_finrank_eq
import ZInQKernel.Contrib.CloudW07JacobiansCurves.NormalModel

/-!
# hgz-steps: `ℚ(X₀(N))` is a finite extension of `ℚ(T)`, so it has a normal proper model
-/

noncomputable section

open Polynomial AlgebraicGeometry

namespace ZInQ.GZSch

open ZInQ.GZAlg ModularCurve

variable (N : ℕ) [NeZero N]

/-- `jq ∈ ℚ(X₀(N))`. -/
def jqF : X0Field N := ⟨jq, jq_mem N⟩

/-- `jq(q^N) ∈ ℚ(X₀(N))`. -/
def jqNF : X0Field N := ⟨jqN N, jqN_mem N⟩

theorem jqF_transc : ∀ p : ℚ[X], p ≠ 0 → aeval (jqF N) p ≠ 0 :=
  transcendental_of_order_neg _ jq_order_neg

/-- `ℚ(T) → ℚ(X₀(N))`, `T ↦ j`. -/
def ratFuncHom : RatFunc ℚ →+* X0Field N :=
  RatFunc.liftRingHom (aeval (jqF N)).toRingHom (fun p hp =>
    mem_nonZeroDivisors_of_ne_zero (jqF_transc N p (nonZeroDivisors.ne_zero hp)))

theorem ratFuncHom_algebraMap (p : ℚ[X]) :
    ratFuncHom N (algebraMap ℚ[X] (RatFunc ℚ) p) = aeval (jqF N) p := by
  have h := RatFunc.liftRingHom_apply_div (aeval (jqF N)).toRingHom
    (fun p hp => mem_nonZeroDivisors_of_ne_zero (jqF_transc N p (nonZeroDivisors.ne_zero hp))) p 1
  rw [map_one, div_one, map_one, div_one] at h
  exact h

/-- The `ℚ(T)`-algebra structure on `ℚ(X₀(N))`. -/
abbrev algQj : Algebra (RatFunc ℚ) (X0Field N) := (ratFuncHom N).toAlgebra

theorem isIntegral_jqNF : @IsIntegral (RatFunc ℚ) (X0Field N) _ _ (algQj N) (jqNF N) := by
  letI := algQj N
  obtain ⟨data, -⟩ := exists_phiIrreducible_of_finrank_eq N (finrank_adjoin_jqN_eq_dedekindPsi N)
  let ι₀ : ℤ[X] →+* RatFunc ℚ :=
    (algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ))
  refine ⟨data.Φ.map ι₀, data.monic.map ι₀, ?_⟩
  have hcomp : (((X0Field N).val : X0Field N →+* LaurentSeries ℚ).comp
      ((algebraMap (RatFunc ℚ) (X0Field N)).comp ι₀)) = evalAtJ := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp only [RingHom.coe_comp, Function.comp_apply, ι₀, coe_mapRingHom, map_X, evalAtJ]
    change ((ratFuncHom N (algebraMap ℚ[X] (RatFunc ℚ) X) : X0Field N) : LaurentSeries ℚ) = _
    rw [ratFuncHom_algebraMap, aeval_X]
    simp [jqF]
  apply (X0Field N).val.injective
  rw [map_zero, eval₂_map]
  have h1 := Polynomial.hom_eval₂ data.Φ ((algebraMap (RatFunc ℚ) (X0Field N)).comp ι₀)
    ((X0Field N).val : X0Field N →+* LaurentSeries ℚ) (jqNF N)
  change ((X0Field N).val : X0Field N →+* LaurentSeries ℚ) _ = 0
  rw [h1, hcomp]
  exact data.eval_eq_zero


theorem adjoin_jqNF_eq_top :
    @IntermediateField.adjoin (RatFunc ℚ) _ (X0Field N) _ (algQj N) {jqNF N} = ⊤ := by
  letI := algQj N
  set M := IntermediateField.adjoin (RatFunc ℚ) {jqNF N}
  set M' : Subfield (LaurentSeries ℚ) :=
    M.toSubfield.map ((X0Field N).val : X0Field N →+* LaurentSeries ℚ)
  have hj : jqF N ∈ M := by
    have : jqF N = algebraMap (RatFunc ℚ) (X0Field N) (algebraMap ℚ[X] (RatFunc ℚ) X) := by
      change _ = ratFuncHom N _
      rw [ratFuncHom_algebraMap, aeval_X]
    rw [this]; exact M.algebraMap_mem _
  have hjN : jqNF N ∈ M := IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)
  have hle : (X0Field N).toSubfield ≤ M' := by
    rw [X0Field, ModularCurve.modularFunctionField]
    refine IntermediateField.adjoin_le_subfield ℚ _ ?_ ?_
    · rintro _ ⟨c, rfl⟩
      rw [eq_ratCast]
      exact SubfieldClass.ratCast_mem M' c
    · intro z hz
      rcases hz with rfl | rfl
      · exact ⟨jqF N, hj, rfl⟩
      · exact ⟨jqNF N, hjN, rfl⟩
  rw [eq_top_iff]
  intro g _
  obtain ⟨m, hm, hmg⟩ := hle g.2
  have : m = g := (X0Field N).val.injective hmg
  rw [← this]; exact hm

theorem finiteDimensional_X0Field :
    @FiniteDimensional (RatFunc ℚ) (X0Field N) _ _ (@Algebra.toModule _ _ _ _ (algQj N)) := by
  letI := algQj N
  haveI := IntermediateField.adjoin.finiteDimensional (isIntegral_jqNF N)
  have h := adjoin_jqNF_eq_top N
  rw [h] at this
  exact Module.Finite.equiv (IntermediateField.topEquiv (F := RatFunc ℚ) (E := X0Field N)).toLinearEquiv

/-- **A normal proper model of `X₀(N)` over `ℚ`** (cloud-w07's `NormalModelOfFunctionFieldQ_proof`
for the finite extension `ℚ(X₀(N)) ⊃ ℚ(j)`). -/
theorem exists_model : ∃ (X : Scheme.{0}) (_ : IsIntegral X)
    (sX : X ⟶ Spec (CommRingCat.of ℚ)), IsProper sX ∧ ZInQ.Contrib.CurvesG.IsNormalScheme X ∧
      topologicalKrullDim X = 1 ∧ Nonempty (X.functionField ≃+* X0Field N) := by
  letI := algQj N
  haveI := finiteDimensional_X0Field N
  obtain ⟨Xo, hprop, hint, hN, hdim, he⟩ :=
    ZInQ.Contrib.CloudW07JacobiansCurves.NormalModelOfFunctionFieldQ_proof (X0Field N)
  exact ⟨Xo.left, hint, Xo.hom, hprop, hN, hdim, he⟩

end ZInQ.GZSch
