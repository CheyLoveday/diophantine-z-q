import ZInQKernel.Contrib.OneProof.RC.X0Model.ComplexGerms
import ZInQKernel.Contrib.OneProof.RC.X0Model.Specialization
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_phiIrreducible_all
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_ModularPolynomialData_minpoly_jqN_eq
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_ModularPolynomialData_eval_E4_cube_div_discriminant_smul_eq_zero

/-! The complex point on the normalization selected by the analytic modular
branch. The analytic realization and specialization are on the spot
(provenance (c)); tex 2915–2919 uses complex lattice points of this model. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Filter IntermediateField ModularCurve
open ShimuraPointDict
open scoped Topology

namespace ZInQ.Manuscript.RC.X0Model

private theorem jPolynomial_regular (τ : UpperHalfPlane) : nonZeroDivisors (Polynomial ℚ) ≤
    (nonZeroDivisors (MeromorphicGerm (τ : ℂ))).comap (jPolynomial τ) := by
  intro p hp
  exact mem_nonZeroDivisors_iff_ne_zero.mpr (fun hz =>
    (mem_nonZeroDivisors_iff_ne_zero.mp hp) (map_eq_zero_iff _ (jPolynomial_injective τ) |>.mp hz))

private def jMap (τ : UpperHalfPlane) : ℚ⟮jq⟯ →+* MeromorphicGerm (τ : ℂ) :=
  (RatFunc.liftRingHom (jPolynomial τ) (jPolynomial_regular τ)).comp jCoordinate.symm.toRingHom

private theorem jMap_jGen (τ : UpperHalfPlane) :
    jMap τ jGen = jPolynomial τ Polynomial.X := by
  unfold jMap
  change (RatFunc.liftRingHom (jPolynomial τ) (jPolynomial_regular τ)) (jCoordinate.symm jGen) = _
  rw [← jCoordinate_X, RingEquiv.symm_apply_apply, RatFunc.liftRingHom_X]

private def jNGerm (N : ℕ) [NeZero N] (τ : UpperHalfPlane) : MeromorphicGerm (τ : ℂ) :=
  ⟨(analyticJN N ∘ UpperHalfPlane.ofComplex : ℂ → ℂ),
    _, rfl, (analyticOn_jN N τ τ.im_pos).meromorphicAt⟩

private theorem germ_eval₂ {R : Type} [CommRing R] (z : ℂ) (b : ℂ → R →+* ℂ)
    (a : ℂ → ℂ) (P : Polynomial R) :
    P.eval₂ ((Germ.coeRingHom (𝓝[≠] z)).comp (RingHom.pi b)) (a : PuncturedGerm z) =
      ((fun w => P.eval₂ (b w) (a w)) : PuncturedGerm z) := by
  calc
    _ = (Germ.coeRingHom (𝓝[≠] z)) (P.eval₂ (RingHom.pi b) a) :=
      (Polynomial.hom_eval₂ P (RingHom.pi b) (Germ.coeRingHom (𝓝[≠] z)) a).symm
    _ = _ := by
      apply congrArg (Germ.coeRingHom (𝓝[≠] z))
      funext w
      exact Polynomial.hom_eval₂ P (RingHom.pi b) (Pi.evalRingHom (fun _ : ℂ => ℂ) w) a

private theorem modularPolynomial_germ_zero (N : ℕ) [NeZero N]
    (τ : UpperHalfPlane) (P : ModularPolynomialData N) :
    P.toAdjoin.eval₂ (jMap τ) (jNGerm N τ) = 0 := by
  rw [ModularPolynomialData.toAdjoin, Polynomial.eval₂_map]
  apply (meromorphicIncl (τ : ℂ)).injective
  rw [map_zero, Polynomial.hom_eval₂]
  have hcomp : (meromorphicIncl (τ : ℂ)).comp ((jMap τ).comp evalAtJGen) =
      (Germ.coeRingHom _).comp (RingHom.pi fun w : ℂ =>
        Polynomial.eval₂RingHom (Int.castRingHom ℂ) (analyticJ (UpperHalfPlane.ofComplex w))) := by
    apply Polynomial.ringHom_ext' (Subsingleton.elim _ _)
    change meromorphicIncl (τ : ℂ) (jMap τ (evalAtJGen Polynomial.X)) = _
    rw [show evalAtJGen Polynomial.X = jGen from Polynomial.eval₂_X _ _, jMap_jGen]
    change ((fun w => Polynomial.eval₂ (Rat.castHom ℂ)
      (analyticJ (UpperHalfPlane.ofComplex w)) Polynomial.X) : PuncturedGerm (τ : ℂ)) = _
    apply congrArg (Germ.coeRingHom (𝓝[≠] (τ : ℂ)))
    funext w
    exact (Polynomial.eval₂_X (Rat.castHom ℂ) (analyticJ (UpperHalfPlane.ofComplex w))).trans
      (Polynomial.eval₂_X (Int.castRingHom ℂ) (analyticJ (UpperHalfPlane.ofComplex w))).symm
  rw [hcomp]
  change _ = ((fun _ : ℂ => (0 : ℂ)) : PuncturedGerm (τ : ℂ))
  rw [show meromorphicIncl (τ : ℂ) (jNGerm N τ) =
    ((analyticJN N ∘ UpperHalfPlane.ofComplex : ℂ → ℂ) : PuncturedGerm (τ : ℂ)) from rfl,
    germ_eval₂]
  apply Germ.coe_eq.mpr
  apply Filter.Eventually.of_forall
  intro w
  let σ := UpperHalfPlane.ofComplex w
  change P.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) (analyticJ σ))
    (analyticJN N σ) = 0
  rw [Polynomial.eval₂_eq_eval_map]
  exact P.eval_E4_cube_div_discriminant_smul_eq_zero N σ (dilate N σ) rfl

private theorem minpoly_germ_zero (N : ℕ) [NeZero N] (τ : UpperHalfPlane)
    (P : ModularPolynomialData N) :
    (minpoly ℚ⟮jq⟯ (jqN N)).eval₂ (jMap τ) (jNGerm N τ) = 0 := by
  rw [P.minpoly_jqN_eq (phiIrreducible_all N P)]
  exact modularPolynomial_germ_zero N τ P

/-- The analytic modular branch at a parameter realizes the model field in the
local meromorphic field. Its construction sends the second generator to j(Nτ). -/
def fieldGerm (N : ℕ) [NeZero N] (τ : UpperHalfPlane) :
    modularFunctionField N →+* MeromorphicGerm (τ : ℂ) :=
  let P := Classical.choice (nonempty_modularPolynomialData N)
  (AdjoinRoot.lift (jMap τ) _ (minpoly_germ_zero N τ P)).comp
    ((adjoinRootEquivAdjoin ℚ⟮jq⟯ (integral_jN P)).symm.toRingHom.comp
      (secondCoordinate N).toRingHom)

theorem fieldGerm_j (N : ℕ) [NeZero N] (τ : UpperHalfPlane) :
    fieldGerm N τ ⟨jq, jq_mem N⟩ = jPolynomial τ Polynomial.X := by
  let P := Classical.choice (nonempty_modularPolynomialData N)
  let e := (adjoinRootEquivAdjoin ℚ⟮jq⟯ (integral_jN P)).symm
  have h : secondCoordinate N ⟨jq, jq_mem N⟩ =
      algebraMap ℚ⟮jq⟯ (↥ℚ⟮jq⟯)⟮jqN N⟯ jGen := Subtype.ext rfl
  change AdjoinRoot.lift (jMap τ) (jNGerm N τ) (minpoly_germ_zero N τ P)
    (e (secondCoordinate N ⟨jq, jq_mem N⟩)) = _
  rw [h, e.commutes, AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of, jMap_jGen]

theorem fieldGerm_jN (N : ℕ) [NeZero N] (τ : UpperHalfPlane) :
    meromorphicIncl (τ : ℂ) (fieldGerm N τ ⟨jqN N, jqN_mem N⟩) =
      ((analyticJN N ∘ UpperHalfPlane.ofComplex : ℂ → ℂ) : PuncturedGerm (τ : ℂ)) := by
  let P := Classical.choice (nonempty_modularPolynomialData N)
  let e := (adjoinRootEquivAdjoin ℚ⟮jq⟯ (integral_jN P)).symm
  have h : secondCoordinate N ⟨jqN N, jqN_mem N⟩ = AdjoinSimple.gen ℚ⟮jq⟯ (jqN N) :=
    Subtype.ext rfl
  change meromorphicIncl (τ : ℂ)
    (AdjoinRoot.lift (jMap τ) (jNGerm N τ) (minpoly_germ_zero N τ P)
      (e (secondCoordinate N ⟨jqN N, jqN_mem N⟩))) = _
  rw [h, show e (AdjoinSimple.gen ℚ⟮jq⟯ (jqN N)) = _ from
    adjoinRootEquivAdjoin_symm_apply_gen _ _, AdjoinRoot.lift_root]
  rfl

private def valuationRat (z : ℂ) : ℚ →+* meromorphicValuation z :=
  ((constantGerm z).comp (Rat.castHom ℂ)).codRestrict (meromorphicValuation z)
    fun c => ⟨(c : ℂ), hasValue_coe.mpr tendsto_const_nhds⟩

/-- The extension of the complex branch to the local ring of finite germs. -/
def analyticArc (N : ℕ) [NeZero N] (τ : UpperHalfPlane) :
    Spec (.of (meromorphicValuation (τ : ℂ))) ⟶ curve N :=
  letI := (valuationRat (τ : ℂ)).toAlgebra
  (existsUnique_specialization (R := meromorphicValuation (τ : ℂ)) N
    (fieldGerm N τ)).exists.choose

theorem analyticArc_generic (N : ℕ) [NeZero N] (τ : UpperHalfPlane) :
    Spec.map (CommRingCat.ofHom
      (algebraMap (meromorphicValuation (τ : ℂ)) (MeromorphicGerm (τ : ℂ)))) ≫
        analyticArc N τ = genericMap N (fieldGerm N τ) :=
  letI := (valuationRat (τ : ℂ)).toAlgebra
  (existsUnique_specialization (R := meromorphicValuation (τ : ℂ)) N
    (fieldGerm N τ)).exists.choose_spec.1

/-- The complex point obtained by evaluating the lifted analytic branch. -/
def complexPoint (N : ℕ) [NeZero N] (τ : UpperHalfPlane) : Spec (.of ℂ) ⟶ curve N :=
  Spec.map (CommRingCat.ofHom (valueOfGerm (τ : ℂ))) ≫ analyticArc N τ

theorem complexPoint_overQ (N : ℕ) [NeZero N] (τ : UpperHalfPlane) :
    complexPoint N τ ≫ overQ N = Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ)) := by
  apply Spec.homEquiv.injective
  exact CommRingCat.hom_ext (Subsingleton.elim _ _)


end ZInQ.Manuscript.RC.X0Model
