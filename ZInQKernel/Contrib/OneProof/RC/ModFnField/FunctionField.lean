import ZInQKernel.Contrib.OneProof.RC.ModFnField.FieldMembership
import ZInQKernel.Contrib.OneProof.RC.ParamAtScale.Algebraization
import ZInQKernel.Contrib.CloudB3RC53.NewformS13.FunctionFieldPullback

/-! The fixed-scale coordinate map on function fields. On-the-spot (c)
for tex 1785–1787 and 2836–2838. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Filter ModularCurve Polynomial UpperHalfPlane WeierstrassCurve
open ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.RC53Assist.IsogenyScheme
open ZInQ.Manuscript.RC.ParamAtScale ZInQ.Manuscript.RC.PreparedParam

namespace ZInQ.Manuscript.RC.ModFnField

/-- An affine point with transcendental x-coordinate embeds the elliptic
function field into the target field. -/
theorem fieldHom_of_transcendental_point (E : WeierstrassCurve ℚ) {K : Type*} [Field K]
    [Algebra ℚ K] {x y : K} (h : (E.baseChange K).toAffine.Equation x y)
    (hx : Transcendental ℚ x) :
    ∃ ι : E.toAffine.FunctionField →+* K,
      ι E.toAffine.genericX = x ∧ ι E.toAffine.genericY = y := by
  have heval : eval₂ (aeval x).toRingHom y E.toAffine.polynomial = 0 := by
    have he := (Affine.equation_iff _ _).mp h
    simp only [baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] at he
    rw [Affine.polynomial]
    simp only [eval₂_sub, eval₂_add, eval₂_pow, eval₂_X, eval₂_C, eval₂_mul,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, map_add, map_mul, aeval_C, map_pow]
    linear_combination he
  let P : E.toAffine.CoordinateRing →+* K := AdjoinRoot.lift (aeval x).toRingHom y heval
  have hP (p : ℚ[X]) : P (algebraMap ℚ[X] E.toAffine.CoordinateRing p) = aeval x p :=
    AdjoinRoot.lift_of heval
  have hPy : P (Affine.CoordinateRing.mk E.toAffine Polynomial.X) = y := by
    simp [P, Affine.CoordinateRing.mk]
  have hPinj : Function.Injective P := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    obtain ⟨p, q, rfl⟩ := Affine.CoordinateRing.exists_smul_basis_eq r
    let r : E.toAffine.CoordinateRing := p • 1 + q • Affine.CoordinateRing.mk E.toAffine Polynomial.X
    let : Module.Finite ℚ[X] E.toAffine.CoordinateRing :=
      Module.Finite.of_basis (Affine.CoordinateRing.basis E.toAffine)
    suffices hn : Algebra.norm ℚ[X] r = 0 from Algebra.norm_eq_zero_iff.mp hn
    by_contra hn
    apply hx
    refine ⟨Algebra.norm ℚ[X] r, hn, ?_⟩
    rw [← hP]
    change P (AdjoinRoot.of E.toAffine.polynomial
      (Algebra.norm ℚ[X] (p • 1 + q • Affine.CoordinateRing.mk E.toAffine Polynomial.X))) = 0
    rw [Affine.CoordinateRing.coe_norm_smul_basis, map_mul]
    have hpq : P (Affine.CoordinateRing.mk E.toAffine (C p + C q * Polynomial.X)) = 0 := by
      convert hr using 1
      simp only [map_add, map_mul, Affine.CoordinateRing.mk_C_eq_algebraMap, Algebra.smul_def, mul_one]
    rw [map_mul P, hpq, zero_mul]
  let ι : E.toAffine.FunctionField →+* K := IsFractionRing.lift hPinj
  refine ⟨ι, ?_, ?_⟩
  · rw [Affine.genericX_def, IsFractionRing.lift_algebraMap,
      Affine.CoordinateRing.mk_C_eq_algebraMap, hP, aeval_X]
  · rw [Affine.genericY_def, IsFractionRing.lift_algebraMap, hPy]

set_option maxHeartbeats 700000 in
/-- From the complex converse, the affine coordinates define the generic map
to the specified field, with both prescribed analytic expansions. -/
theorem functionField_coordinates (E : WeierstrassCurve ℚ) {N : ℕ} [NeZero N]
    (hclass : ComplexCuspClassification N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    {L : PeriodPair} (hL : IsLatticeOf E L) {κ : ℚ} (hκ : IsParamScale N f L (κ : ℂ)) :
    ∃ (ι : E.toAffine.FunctionField →+* modularFunctionField N),
      Realizes (complexify (ι E.toAffine.genericX)) (fun τ => xCoordinate E f L κ τ) ∧
      Realizes (complexify (ι E.toAffine.genericY)) (fun τ => yCoordinate E f L κ τ) := by
  obtain ⟨x, y, hlead, hx, hy, he⟩ :=
    coordinates_in_modularFunctionField_with_equation E hclass f hf hL hκ
  let j : modularFunctionField N →+* LaurentSeries ℚ :=
    (modularFunctionField N).toSubfield.subtype
  have hmap (q : ℚ) :
      j (algebraMap ℚ (modularFunctionField N) q) = algebraMap ℚ (LaurentSeries ℚ) q :=
    DFunLike.congr_fun (RingHom.ext_rat (j.comp (algebraMap ℚ (modularFunctionField N)))
      (algebraMap ℚ (LaurentSeries ℚ))) q
  have h : (E.baseChange (modularFunctionField N)).toAffine.Equation x y := by
    apply (Affine.equation_iff _ _).mpr
    apply j.injective
    have hjx : j x = (x : LaurentSeries ℚ) := rfl
    have hjy : j y = (y : LaurentSeries ℚ) := rfl
    have he' := (Affine.equation_iff (W := (E.baseChange (LaurentSeries ℚ)).toAffine)
      (x : LaurentSeries ℚ) (y : LaurentSeries ℚ)).mp he
    simp only [baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆,
      map_add, map_mul, map_pow, hmap, hjx, hjy]
    simpa only [baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] using he'
  have hne : (x : LaurentSeries ℚ).coeff (-2) ≠ 0 := by
    intro hz
    rw [hz, Rat.cast_zero] at hlead
    exact (pow_ne_zero _ (inv_ne_zero hκ.1)) hlead.symm
  have ht := ZInQ.Contrib.CloudB3RC53.NewformS13.transcendental_of_nonconst
    ⟨-2, by norm_num, hne⟩
  have htx : Transcendental ℚ x := by
    intro ha
    exact ht (ha.algHom j.toRatAlgHom)
  obtain ⟨ι, hιx, hιy⟩ := fieldHom_of_transcendental_point E h htx
  exact ⟨ι, hιx.symm ▸ hx, hιy.symm ▸ hy⟩

/-- With any supplied source model, the complex converse yields a dominant
morphism over ℚ through the fixed generic coordinates. -/
theorem dominant_morphism_of_classification (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {N : ℕ} [NeZero N] (X : X0Model N)
    (hclass : ComplexCuspClassification N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    {L : PeriodPair} (hL : IsLatticeOf E L) {κ : ℚ} (hκ : IsParamScale N f L (κ : ℂ)) :
    letI := X.integral
    ∃ (ι : E.toAffine.FunctionField →+* modularFunctionField N)
      (π : X.X ⟶ Proj E.toProjective.grading),
      π ≫ projectiveOverQ E = X.overQ ∧ IsDominant π ∧
      X.X.fromSpecFunctionField ≫ π =
        Spec.map (CommRingCat.ofHom (X.functionField.symm.toRingHom.comp
          (ι.comp (projFunctionFieldEquiv E).toRingHom))) ≫
            (Proj E.toProjective.grading).fromSpecFunctionField ∧
      Realizes (complexify (ι E.toAffine.genericX)) (fun τ => xCoordinate E f L κ τ) ∧
      Realizes (complexify (ι E.toAffine.genericY)) (fun τ => yCoordinate E f L κ τ) := by
  obtain ⟨ι, hx, hy⟩ := functionField_coordinates E hclass f hf hL hκ
  obtain ⟨π, hπ, hdom, hgen⟩ := morphism_of_functionField X ι
  exact ⟨ι, π, hπ, hdom, hgen, hx, hy⟩


end ZInQ.Manuscript.RC.ModFnField
