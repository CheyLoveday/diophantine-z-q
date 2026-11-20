import ZInQKernel.Contrib.OneProof.RC.Wiring.InnerLimitRegularity
import ZInQKernel.Contrib.RC53Assist.Detection.Producer
import ZInQKernel.Contrib.RC53Assist.InnerLimitMoving.Consumers

/-!
# Detection and cohomology identifications for one inner-limit stage step

The finite plane in the relaxed localization and the two side cohomology
identifications use the same retained global complex and the same retained
localization. The relevant manuscript passages are tex L4391–4451,
L5040–5072, L5072–5082, and L5087–5114.

The detecting determinant is supplied by `produce_arithmetic_detection`, through
`makeArithmeticDetection`. The additional comparison is an equality of the
localization of each specialized one-cycle with its normalized original-basis
evaluation at the selected label. This equality is named `RetainedEvaluationTie`.
It asserts neither a determinant condition nor a containment of planes.

The finite and singular cohomology identifications are those constructed from
retained cochain maps and the integral minimal models in
`InnerLimitMoving.Consumers`. They do not follow from reflection of principal
cocycles. The final construction returns `ILStageStep` itself and therefore
uses its existing conversion to `InnerLimitStepData`.
-/

set_option maxHeartbeats 600000
set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.StageStepDetection

open CategoryTheory Filter NumberField IsDedekindDomain IsLocalRing
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.UniformSwitch
open ZInQ.Contrib.CloudB3RC53.SwitchInputs (fiberH1)
open ZInQ.Manuscript.RC.Uniform (Lambda finPlane)
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.CoefModules (ActualConj)
open ZInQ.Manuscript.RC.LambdaCoef (HasFullTwoTorsion IsContChar)
open ZInQ.Manuscript.RC.PrintsArith (GalQ Qbar)
open ZInQ.Manuscript.RC.Limits (StageA stageMap stageIdeal stageIdeal_tendsToZero
  residualCohomologyAt ulim ulimMat ulimMat_apply ulimMat_mul ulimMat_const ulimMat_eq_of_sub_mem)
open ZInQ.Manuscript.RC.FibreDuality (RetainedLimitPairingStages RetainedGlobalDualityStages
  localPairingOfMat transportedPairing conjMatrix splitSelData stageLocMat)
open ZInQ.Manuscript.RC.Wiring (ResAt resAt ILStageStep)
open ZInQ.Contrib.RC53Assist.InnerLimit (ComplexStages Vec2 splitLocalComplex
  fibreLimitGlobal finiteLimitSide singularLimitSide limitRelaxed)
open ZInQ.Contrib.RC53Assist.InnerLimitArith (MovingLabel CompatibleArithmeticLabel
  ResidualCohomologyFinite finPlane_le_limitRelaxed_U)
open ZInQ.Contrib.RC53Assist.Detection
open ZInQ.Contrib.RC53Assist.InnerLimitMoving (IntegralMatrixStageData selmerStages
  derivativeDiagram retainedRestrictionStages fibreFiniteStageEquiv fibreSingularStageEquiv)
open scoped WeierstrassCurve PowerSeries.WithPiTopology Matrix

section FiniteCohomology

/-- Kind: proved instance; tex L4391–4451. The first cohomology of the
specialized retained complex is a subquotient of its finite-dimensional
first term. No additional cohomology-finiteness hypothesis is needed. -/
instance fibre_h1_finite (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite)
    (P : Ideal Lambda) [P.IsPrime] (C : ComplexStages (R := Lambda) stageIdeal U) :
    FiniteDimensional (ResAt P) ((fibreLimitGlobal U hU P C).toCC.homology 1) := by
  have : Module.Finite (ResAt P) ((fibreLimitGlobal U hU P C).X 1) :=
    inferInstanceAs (Module.Finite (ResAt P) (Fin (C.rank 1) → ResAt P))
  apply (ZInQ.Manuscript.RC.FibreDuality.moduleFinite_homology_iff
    (fibreLimitGlobal U hU P C) 1).2
  infer_instance

end FiniteCohomology

section EvaluationComparison

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} {e : AlgebraicClosure K ≃ₐ[ℚ] Qbar}
  {α : GKS K S →* Lambdaˣ} [IsContChar α]
  {E : WeierstrassCurve ℚ} [E.IsElliptic] [HasFullTwoTorsion K S (E⁄K)]
  {U : Ultrafilter ℕ} {P : Ideal Lambda} [P.IsPrime]
  [DistribMulAction RationalSequences (FibrePair P)]
  [SMulCommClass RationalSequences (ResAt P) (FibrePair P)]
  {n : ℕ} {Q : GCx (ResAt P)}

/-- Kind: definition (retained cochain comparison); tex L4391–4451,
L5040–5072, L5087–5114. The localization of a specialized one-cycle is the
normalized evaluation of its original integral columns at this very label.
No plane containment, determinant, or cohomology equivalence is asserted. -/
def RetainedEvaluationTie
    (R : RetainedEvaluation (S := S) (e := e) (α := α) (E := E) (U := U) (P := P) n Q)
    (res : GHom Q (splitLocalComplex (ResAt P))) (L : MovingLabel K S) : Prop :=
  ∀ x : LinearMap.ker (Q.d 1 2 rfl),
    res.f 1 1 rfl x.val =
      (basisValue P U R.original L.frob (R.coordinates x.val), 0)

/-- Kind: definition (original integral evaluation columns); tex L4391–4451,
L4809–4830, L5087–5114. No localized coordinates are applied at a finite
coefficient stage. -/
def originalEvaluationMatrix
    (R : RetainedEvaluation (S := S) (e := e) (α := α) (E := E) (U := U) (P := P) n Q)
    (L : MovingLabel K S) (i : ℕ) : Matrix (Fin 2) (Fin n) Lambda := fun a j =>
  ZInQ.Manuscript.RC.LambdaCoef.tlamHomeomorph
    (K := K) (S := S) (W := E⁄K) (α := α)
    (ZInQ.Contrib.RC53Assist.InnerLimitArith.evalOne Lambda
      (ZInQ.Manuscript.RC.LambdaCoef.TLam K S (E⁄K) α) (L.frob i) (R.original j i)) a

omit [SMulCommClass RationalSequences (ResAt P) (FibrePair P)] in
/-- Kind: proved theorem; tex L4391–4451, L4809–4830, L5087–5114.
Normalized evaluation is the specialized integral column matrix followed by
the specified fibre coordinates, in that order. -/
theorem basisValue_matrix
    (R : RetainedEvaluation (S := S) (e := e) (α := α) (E := E) (U := U) (P := P) n Q)
    (L : MovingLabel K S) (w : Fin n → ResAt P) :
    basisValue P U R.original L.frob w =
      (ulimMat U (originalEvaluationMatrix R L)).map (algebraMap Lambda (ResAt P)) *ᵥ w := by
  funext a
  simp only [basisValue, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ j : Fin n, w j * algebraMap Lambda (ResAt P)
    (ulimMat U (originalEvaluationMatrix R L) a j)) =
      ∑ j : Fin n, algebraMap Lambda (ResAt P)
        (ulimMat U (originalEvaluationMatrix R L) a j) * w j
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

end EvaluationComparison

section RetainedColumns

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} {e : AlgebraicClosure K ≃ₐ[ℚ] Qbar}
  {α : GKS K S →* Lambdaˣ} [IsContChar α]
  {E : WeierstrassCurve ℚ} [E.IsElliptic] [HasFullTwoTorsion K S (E⁄K)]
  {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ cofinite)
  (P : Ideal Lambda) [P.IsPrime] {C : ComplexStages (R := Lambda) stageIdeal U}
  (D : RetainedLimitPairingStages U C)
  [DistribMulAction RationalSequences (FibrePair P)]
  [SMulCommClass RationalSequences (ResAt P) (FibrePair P)] {n : ℕ}
  (R : RetainedEvaluation (S := S) (e := e) (α := α) (E := E) (U := U) (P := P)
    n (fibreLimitGlobal U hU P C)) (L : MovingLabel K S)

/-- Kind: structure (finite-stage cochain comparisons); tex L4391–4451,
L4809–4830, L5040–5072. One fixed scalar clears the normalized fibre
coordinates. The finite localization columns are the original evaluations
at the retained precisions. The singular localization is homotopic to zero
in degree one. These data concern cochain matrices, not detection. -/
structure RetainedEvaluationColumns where
  /-- Kind: data; tex L4391–4451. A fixed denominator-clearing scalar. -/
  scale : Lambda
  /-- Kind: hypothesis; tex L4651–4704. Its specialization is nonzero. -/
  scale_ne_zero : algebraMap Lambda (ResAt P) scale ≠ 0
  /-- Kind: data; tex L4391–4451. Cleared coordinates of the original integral columns. -/
  coordinates : Matrix (Fin n) (Fin (C.rank 1)) Lambda
  /-- Kind: hypothesis; tex L4391–4451, L4651–4704. Exact normalized coordinates after specialization. -/
  normalization : ∀ x : Fin (C.rank 1) → ResAt P,
    algebraMap Lambda (ResAt P) scale • R.coordinates x =
      coordinates.map (algebraMap Lambda (ResAt P)) *ᵥ x
  /-- Kind: hypothesis; tex L4809–4830, L5087–5114. The actual finite localization columns at the stages. -/
  finite_columns : ∀ᶠ i in (U : Filter ℕ), ∀ a b,
    (scale • (D.res 1 i).submatrix Sum.inl id -
      originalEvaluationMatrix R L i * coordinates) a b ∈ stageIdeal i
  /-- Kind: data; tex L4391–4451, L5040–5072. The degree-one singular null-homotopy. -/
  singularHom : Matrix (Fin 2) (Fin (C.rank 2)) Lambda
  /-- Kind: hypothesis; tex L4391–4451, L5040–5072. Singular localization factors through the differential. -/
  singular_columns : ∀ᶠ i in (U : Filter ℕ), ∀ a b,
    ((D.res 1 i).submatrix Sum.inr id - singularHom * C.d i 1 2 rfl) a b ∈ stageIdeal i

variable {hU P D R L}

omit [SMulCommClass RationalSequences (ResAt P) (FibrePair P)] in
/-- Kind: proved theorem; tex L4391–4451, L4809–4830, L5040–5072.
Finite-stage column congruences imply the exact retained evaluation tie.
Denominators are cleared by the fixed scalar before the integral limit;
the scalar is cancelled only after specialization. Singular localization
vanishes on cycles because its retained null-homotopy factors through the
differential. No integral lift of a specialized cycle is required. -/
theorem RetainedEvaluationColumns.toEvaluationTie
    (T : RetainedEvaluationColumns hU P D R L) :
    RetainedEvaluationTie R (D.resLimit hU P) L := by
  have hf := ulimMat_eq_of_sub_mem stageIdeal_tendsToZero hU T.finite_columns
  rw [ZInQ.Manuscript.RC.FibreDuality.ulimMat_smul_const,
    ulimMat_mul, ulimMat_const] at hf
  have hf' : algebraMap Lambda (ResAt P) T.scale •
      (D.resK P 1).submatrix Sum.inl id =
      (ulimMat U (originalEvaluationMatrix R L)).map (algebraMap Lambda (ResAt P)) *
        T.coordinates.map (algebraMap Lambda (ResAt P)) := by
    have he := congrArg (fun M : Matrix (Fin 2) (Fin (C.rank 1)) Lambda =>
      M.map (algebraMap Lambda (ResAt P))) hf
    rw [Matrix.map_mul] at he
    ext a b
    have hab := congrFun (congrFun he a) b
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul] at hab
    change algebraMap Lambda (ResAt P) T.scale *
      algebraMap Lambda (ResAt P) (ulim U (fun i => D.res 1 i (Sum.inl a) b)) = _ at hab
    change algebraMap Lambda (ResAt P) T.scale *
      algebraMap Lambda (ResAt P) (ulim U (fun i => D.res 1 i (Sum.inl a) b)) = _
    exact hab
  have hs := ulimMat_eq_of_sub_mem stageIdeal_tendsToZero hU T.singular_columns
  rw [ulimMat_mul, ulimMat_const] at hs
  have hs' : (D.resK P 1).submatrix Sum.inr id =
      T.singularHom.map (algebraMap Lambda (ResAt P)) *
        (ulimMat U (fun i => C.d i 1 2 rfl)).map (algebraMap Lambda (ResAt P)) := by
    have he := congrArg (fun M : Matrix (Fin 2) (Fin (C.rank 1)) Lambda =>
      M.map (algebraMap Lambda (ResAt P))) hs
    rw [Matrix.map_mul] at he
    ext a b
    have hab := congrFun (congrFun he a) b
    simp only [Matrix.map_apply] at hab
    change algebraMap Lambda (ResAt P) (ulim U (fun i => D.res 1 i (Sum.inr a) b)) = _ at hab
    change algebraMap Lambda (ResAt P) (ulim U (fun i => D.res 1 i (Sum.inr a) b)) = _
    exact hab
  intro x
  let v : Fin (C.rank 1) → ResAt P := x.val
  change (D.resLimit hU P).f 1 1 rfl v =
    (basisValue P U R.original L.frob (R.coordinates v), 0)
  apply Prod.ext
  · change ((D.resK P 1).submatrix Sum.inl id) *ᵥ v =
      basisValue P U R.original L.frob (R.coordinates v)
    rw [basisValue_matrix]
    have hv := congrArg (fun M : Matrix (Fin 2) (Fin (C.rank 1)) (ResAt P) => M *ᵥ v) hf'
    rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, ← T.normalization v,
      Matrix.mulVec_smul] at hv
    funext a
    apply mul_left_cancel₀ T.scale_ne_zero
    exact congrFun hv a
  · change ((D.resK P 1).submatrix Sum.inr id) *ᵥ v = (0 : Vec2 (ResAt P))
    rw [hs', ← Matrix.mulVec_mulVec]
    have hx : (ulimMat U (fun i => C.d i 1 2 rfl)).map (algebraMap Lambda (ResAt P)) *ᵥ v = 0 :=
      x.property
    rw [hx, Matrix.mulVec_zero]

end RetainedColumns

section Detection

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
  (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
  (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar) (α : GKS K S →* Lambdaˣ) [IsContChar α]
  (E : WeierstrassCurve ℚ) [E.IsElliptic] [HasFullTwoTorsion K S (E⁄K)]
  (Cn : ActualConj K S) (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite)
  (P : Ideal Lambda) [P.IsPrime] (hP : P.height = 1) (hne : P ≠ Ideal.span {2})
  [DistribMulAction RationalSequences (FibrePair P)]
  [SMulCommClass RationalSequences (ResAt P) (FibrePair P)]
  (B : ℕ → IntermediateField ℚ Qbar) [∀ i, Normal ℚ (B i)]
  [∀ i, FiniteDimensional ℚ (B i)]
  (F0 : ℕ → IntermediateField ℚ Qbar) [∀ i, FiniteDimensional ℚ (F0 i)]
  (excl : ℕ → Finset ℕ) (hdegree : Module.finrank ℚ K = 2)
  (C : ComplexStages (R := Lambda) stageIdeal U) (D : RetainedLimitPairingStages U C)

/-- Kind: proved theorem from the displayed arithmetic and cochain-comparison
inputs; tex L5040–5072, L5087–5114. The producer chooses an independent partner
and an actual arithmetic label through the prescribed nonzero class. Its
normalized determinant and the retained evaluation tie give exactly the
finite-plane containment required by `ILStageStep.hdet`. Finite kernel
membership is used only by the existing arithmetic producer. -/
theorem produced_hdet {n : ℕ}
    (coeff : InducedCoefficientDictionary S e α E Cn U P)
    (scalar : ArithmeticCommonScalar S e α E P B) (span : CoefficientSpanWitness P)
    (R : RetainedEvaluation (S := S) (e := e) (α := α) (E := E) (U := U) (P := P)
      n (fibreLimitGlobal U hU P C))
    (a : LinearMap.ker ((fibreLimitGlobal U hU P C).d 1 2 rfl))
    (ha : clsAt (fibreLimitGlobal U hU P C) 1 2 rfl a ≠ 0)
    (hdim : 1 < Module.finrank (ResAt P) ((fibreLimitGlobal U hU P C).toCC.homology 1)) :
    let r := makeArithmeticDetection S hS e α E Cn U hU P hP hne B F0 excl hdegree
      (fibreLimitGlobal U hU P C) coeff scalar span R a ha hdim
    let H := arithmeticKernelFamily E S e α r.kernel
    let X := basisArithmeticLabel S hS e α E Cn R.original H (fun i => F0 i ⊔ B i) excl hdegree
    RetainedEvaluationTie R (D.resLimit hU P) X.label →
      finPlane (ResAt P) (Vec2 (ResAt P)) (Vec2 (ResAt P)) ≤
        (limitRelaxed (fibreLimitGlobal U hU P C) (D.resLimit hU P)).U := by
  dsimp only
  let r := makeArithmeticDetection S hS e α E Cn U hU P hP hne B F0 excl hdegree
    (fibreLimitGlobal U hU P C) coeff scalar span R a ha hdim
  intro htie
  exact finPlane_le_limitRelaxed_U (fibreLimitGlobal U hU P C) (D.resLimit hU P)
    a.property r.partner.property (htie a) (htie r.partner) r.detecting

end Detection

section SideIdentifications

variable {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ cofinite)
  (P : Ideal Lambda) [P.IsPrime] {C : ComplexStages (R := Lambda) stageIdeal U}
  (D : RetainedLimitPairingStages U C)
  {F : Type} [Field F] {ι : Localization.AtPrime P →+* F}

/-- Kind: constructed linear equivalence; tex L4391–4451, L5040–5054,
L5072–5082. The retained finite-side cochain comparison and its computed
integral minimal model supply the exact type of `ILStageStep.φ`. The last
hypothesis identifies the already specified stage with that computed stage. -/
def finite_identification
    (D0 : IntegralMatrixStageData stageIdeal_tendsToZero hU
      (algebraMap Lambda (Localization.AtPrime P)) ι
      (selmerStages (derivativeDiagram C (retainedRestrictionStages D) .finite)))
    (S0 : TwoTermStage ι) (hS0 : D0.stage = S0) :
    (selCx (finiteLimitSide (fibreLimitGlobal U hU P C) (D.resLimit hU P)).Dside).toCC.homology 1
      ≃ₗ[ResAt P] fiberH1 (resAt P) S0 := by
  subst S0
  exact fibreFiniteStageEquiv hU P D D0

/-- Kind: constructed linear equivalence; tex L4391–4451, L5040–5054,
L5072–5082. The singular-side cochain comparison uses its own computed
integral minimal model and supplies the exact type of `ILStageStep.φ'`. -/
def singular_identification
    (D1 : IntegralMatrixStageData stageIdeal_tendsToZero hU
      (algebraMap Lambda (Localization.AtPrime P)) ι
      (selmerStages (derivativeDiagram C (retainedRestrictionStages D) .singular)))
    (S1 : TwoTermStage ι) (hS1 : D1.stage = S1) :
    (selCx (singularLimitSide (fibreLimitGlobal U hU P C) (D.resLimit hU P)).Dside).toCC.homology 1
      ≃ₗ[ResAt P] fiberH1 (resAt P) S1 := by
  subst S1
  exact fibreSingularStageEquiv hU P D D1

end SideIdentifications

section StageStepCore

variable (P : Ideal Lambda) [P.IsPrime]
  {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (Cn : ActualConj K S) (W : WeierstrassCurve K) (hW : W.map (Cn.κ : K →+* K) = W)
  [W.IsElliptic] [HasFullTwoTorsion K S W]

/-- Kind: structure (the other inputs of one stage step); tex L4385–4451,
L4834–4907, L5027–5072. These are exactly the fields of `ILStageStep` before
`hdet`, `φ`, and `φ'`. None of those three target fields is assumed. -/
structure StageStepCore where
  /-- Kind: data; tex L4391–4451, L5030–5032. The common ultrafilter. -/
  U : Ultrafilter ℕ
  /-- Kind: hypothesis; tex L4391–4451, L5030–5032. Nonprincipality. -/
  hU : (U : Filter ℕ) ≤ cofinite
  /-- Kind: data; tex L4391–4414. The coefficient-stage complexes. -/
  G : ∀ i, GCx (StageA i)
  /-- Kind: hypothesis; tex L4392–4395, L4412–4414. Flat stage terms. -/
  hflat : ∀ i n, Module.Flat (StageA i) ((G i).X n)
  /-- Kind: data; tex L4859–4868. The stage local conditions. -/
  Uc : ∀ i, GCx (StageA i)
  /-- Kind: data; tex L4859–4868. The stage localizations. -/
  res : ∀ i, GHom (G i) (splitLocalComplex (StageA i))
  /-- Kind: data; tex L4859–4868. The local-condition inclusions. -/
  ιc : ∀ i, GHom (Uc i) (splitLocalComplex (StageA i))
  /-- Kind: data; tex L4385–4388, L4859–4873. The stage Selmer pairings. -/
  Q : ∀ i, SelPairData (splitSelData (G i) (res i) (Uc i) (ιc i))
    (splitSelData (G i) (res i) (Uc i) (ιc i))
  /-- Kind: data; tex L4385–4388, L4859–4873. The stage traces. -/
  tr : ∀ i, (coneCx (Q i).resE).X 3 →ₗ[StageA i] StageA i
  /-- Kind: hypothesis; tex L4385–4388. The traces kill boundaries. -/
  htr : ∀ i z, tr i ((coneCx (Q i).resE).d 2 3 rfl z) = 0
  /-- Kind: hypothesis; tex L4385–4451. Stage global duality. -/
  hdual : ∀ i, QuasiIso (GHom.toCC (globalDualityMap (Q i) (tr i) (htr i)))
  /-- Kind: hypothesis; tex L4392–4394. Finite residual cohomology. -/
  hres : ∀ i [NeZero i], ResidualCohomologyFinite (G i)
  /-- Kind: data; tex L4400–4406. The lower cohomological bound. -/
  lo : ℤ
  /-- Kind: data; tex L4400–4406. The upper cohomological bound. -/
  hi : ℤ
  /-- Kind: hypothesis; tex L4400–4406. Bounded residual cohomology. -/
  hbdd : ∀ i [NeZero i] (n : ℤ), n < lo ∨ hi < n →
    Module.finrank (ResidueField (StageA i)) (residualCohomologyAt (G i) n) = 0
  /-- Kind: data; tex L4400–4406. The uniform rank bound. -/
  B : ℕ
  /-- Kind: hypothesis; tex L4400–4406. Uniformly bounded residual ranks. -/
  hB : ∀ i [NeZero i] (n : ℤ),
    Module.finrank (ResidueField (StageA i)) (residualCohomologyAt (G i) n) ≤ B
  /-- Kind: data; tex L4391–4451. The retained integral complexes. -/
  C : ComplexStages (R := Lambda) stageIdeal U
  /-- Kind: data; tex L4385–4451. The retained localization and pairings. -/
  D : RetainedLimitPairingStages U C
  /-- Kind: data; tex L4385–4451. The retained global-duality inverse. -/
  E : RetainedGlobalDualityStages D
  /-- Kind: hypothesis; tex L4385–4451. The local pairing lifts its stage pairings. -/
  hlift : ∀ i, i ≠ 0 → ∀ a b, (D.loc a b i).map (stageMap i) = stageLocMat (Q i) (tr i) a b
  /-- Kind: hypothesis; tex L4400–4451. The model ranks are the retained residual ranks. -/
  hrank : ∀ᶠ i in (U : Filter ℕ), ∀ [NeZero i] (n : ℤ),
    C.rank n = Module.finrank (ResidueField (StageA i)) (residualCohomologyAt (G i) n)
  /-- Kind: hypothesis; tex L4400–4406. The model ranks obey the same bound. -/
  hrankB : ∀ n, C.rank n ≤ B
  /-- Kind: data; tex L2816–2820, L4888–4890. The degree-zero trace scalar. -/
  ε₀ : ResAt P
  /-- Kind: data; tex L2816–2820, L4888–4890. The top-degree trace scalar. -/
  ε₂ : ResAt P
  /-- Kind: data; tex L5035–5037. The transported cross-pairing scalar. -/
  ε : ResAt P
  /-- Kind: data; tex L4888–4890, L5035–5037. The second cross-pairing scalar. -/
  σ : ResAt P
  /-- Kind: hypothesis; tex L4866–4868. The top-degree scalar is nonzero. -/
  hε₂ : ε₂ ≠ 0
  /-- Kind: hypothesis; tex L5035–5037. The cross-pairing scalar is nonzero. -/
  hε : ε ≠ 0
  /-- Kind: hypothesis; tex L4888–4890, L5035–5037. The second scalar is nonzero. -/
  hσ : σ ≠ 0
  /-- Kind: hypothesis; tex L5027–5042. The actual retained local residue identity. -/
  hloc : localPairingOfMat (D.locK P) = transportedPairing ε₀ ε₂ ε σ (conjMatrix Cn W hW P)

end StageStepCore

section Assembly

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
  {S : Set (HeightOneSpectrum (𝓞 K))} {E : WeierstrassCurve ℚ} [E.IsElliptic]
  [HasFullTwoTorsion K S (E⁄K)] {Cn : ActualConj K S}
  {hW : (E⁄K).map (Cn.κ : K →+* K) = E⁄K} {P : Ideal Lambda} [P.IsPrime]
  [DistribMulAction RationalSequences (FibrePair P)]
  [SMulCommClass RationalSequences (ResAt P) (FibrePair P)]

/-- Kind: constructed stage step from the displayed inputs; tex L4385–4451,
L5040–5072, L5072–5082, L5087–5114. The unchanged stage and duality data are
copied from `Y`. Detection is produced arithmetically and both side
identifications are derived from their integral models. The result is the
original `ILStageStep`, with no assumption of any of its three target fields. -/
def StageStepCore.toILStageStep
    (Y : StageStepCore P Cn (E⁄K) hW)
    (hS : S.Finite) (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
    (α : GKS K S →* Lambdaˣ) [IsContChar α]
    (hP : P.height = 1) (hne : P ≠ Ideal.span {2})
    (B0 : ℕ → IntermediateField ℚ Qbar) [∀ i, Normal ℚ (B0 i)]
    [∀ i, FiniteDimensional ℚ (B0 i)]
    (F0 : ℕ → IntermediateField ℚ Qbar) [∀ i, FiniteDimensional ℚ (F0 i)]
    (excl : ℕ → Finset ℕ) (hdegree : Module.finrank ℚ K = 2)
    {n : ℕ}
    (coeff : InducedCoefficientDictionary S e α E Cn Y.U P)
    (scalar : ArithmeticCommonScalar S e α E P B0) (span : CoefficientSpanWitness P)
    (R : RetainedEvaluation (S := S) (e := e) (α := α) (E := E) (U := Y.U) (P := P)
      n (fibreLimitGlobal Y.U Y.hU P Y.C))
    (a : LinearMap.ker ((fibreLimitGlobal Y.U Y.hU P Y.C).d 1 2 rfl))
    (ha : clsAt (fibreLimitGlobal Y.U Y.hU P Y.C) 1 2 rfl a ≠ 0)
    (hdim : 1 < Module.finrank (ResAt P) ((fibreLimitGlobal Y.U Y.hU P Y.C).toCC.homology 1))
    (htie :
      let r := makeArithmeticDetection S hS e α E Cn Y.U Y.hU P hP hne B0 F0 excl hdegree
        (fibreLimitGlobal Y.U Y.hU P Y.C) coeff scalar span R a ha hdim
      let H := arithmeticKernelFamily E S e α r.kernel
      let X := basisArithmeticLabel S hS e α E Cn R.original H (fun i => F0 i ⊔ B0 i) excl hdegree
      RetainedEvaluationTie R (Y.D.resLimit Y.hU P) X.label)
    {F : Type} [Field F] {ι : Localization.AtPrime P →+* F}
    (D0 : IntegralMatrixStageData stageIdeal_tendsToZero Y.hU
      (algebraMap Lambda (Localization.AtPrime P)) ι
      (selmerStages (derivativeDiagram Y.C (retainedRestrictionStages Y.D) .finite)))
    (D1 : IntegralMatrixStageData stageIdeal_tendsToZero Y.hU
      (algebraMap Lambda (Localization.AtPrime P)) ι
      (selmerStages (derivativeDiagram Y.C (retainedRestrictionStages Y.D) .singular))) :
    ILStageStep P Cn (E⁄K) hW D0.stage D1.stage where
  U := Y.U
  hU := Y.hU
  G := Y.G
  hflat := Y.hflat
  Uc := Y.Uc
  res := Y.res
  ιc := Y.ιc
  Q := Y.Q
  tr := Y.tr
  htr := Y.htr
  hdual := Y.hdual
  hres := Y.hres
  lo := Y.lo
  hi := Y.hi
  hbdd := Y.hbdd
  B := Y.B
  hB := Y.hB
  C := Y.C
  D := Y.D
  E := Y.E
  hlift := Y.hlift
  hrank := Y.hrank
  hrankB := Y.hrankB
  ε₀ := Y.ε₀
  ε₂ := Y.ε₂
  ε := Y.ε
  σ := Y.σ
  hε₂ := Y.hε₂
  hε := Y.hε
  hσ := Y.hσ
  hloc := Y.hloc
  hdet := produced_hdet S hS e α E Cn Y.U Y.hU P hP hne B0 F0 excl hdegree Y.C Y.D
    coeff scalar span R a ha hdim htie
  φ := finite_identification Y.hU P Y.D D0 D0.stage rfl
  φ' := singular_identification Y.hU P Y.D D1 D1.stage rfl

/-- Kind: constructed stage step from finite-stage cochain comparisons;
tex L4385–4451, L4809–4830, L5040–5072, L5072–5082, L5087–5114.
The remaining localization comparison is supplied by the explicit original
column congruences and a retained singular null-homotopy, not by a plane
containment or a determinant assumption. Both side identifications remain
constructed from the same retained diagram. -/
def StageStepCore.fromColumns
    (Y : StageStepCore P Cn (E⁄K) hW)
    (hS : S.Finite) (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
    (α : GKS K S →* Lambdaˣ) [IsContChar α]
    (hP : P.height = 1) (hne : P ≠ Ideal.span {2})
    (B0 : ℕ → IntermediateField ℚ Qbar) [∀ i, Normal ℚ (B0 i)]
    [∀ i, FiniteDimensional ℚ (B0 i)]
    (F0 : ℕ → IntermediateField ℚ Qbar) [∀ i, FiniteDimensional ℚ (F0 i)]
    (excl : ℕ → Finset ℕ) (hdegree : Module.finrank ℚ K = 2) {n : ℕ}
    (coeff : InducedCoefficientDictionary S e α E Cn Y.U P)
    (scalar : ArithmeticCommonScalar S e α E P B0) (span : CoefficientSpanWitness P)
    (R : RetainedEvaluation (S := S) (e := e) (α := α) (E := E) (U := Y.U) (P := P)
      n (fibreLimitGlobal Y.U Y.hU P Y.C))
    (a : LinearMap.ker ((fibreLimitGlobal Y.U Y.hU P Y.C).d 1 2 rfl))
    (ha : clsAt (fibreLimitGlobal Y.U Y.hU P Y.C) 1 2 rfl a ≠ 0)
    (hdim : 1 < Module.finrank (ResAt P) ((fibreLimitGlobal Y.U Y.hU P Y.C).toCC.homology 1)) :
    let r := makeArithmeticDetection S hS e α E Cn Y.U Y.hU P hP hne B0 F0 excl hdegree
      (fibreLimitGlobal Y.U Y.hU P Y.C) coeff scalar span R a ha hdim
    let H := arithmeticKernelFamily E S e α r.kernel
    let X := basisArithmeticLabel S hS e α E Cn R.original H (fun i => F0 i ⊔ B0 i) excl hdegree
    ∀ (_T : RetainedEvaluationColumns Y.hU P Y.D R X.label)
      {F : Type} [Field F] {ι : Localization.AtPrime P →+* F}
      (D0 : IntegralMatrixStageData stageIdeal_tendsToZero Y.hU
        (algebraMap Lambda (Localization.AtPrime P)) ι
        (selmerStages (derivativeDiagram Y.C (retainedRestrictionStages Y.D) .finite)))
      (D1 : IntegralMatrixStageData stageIdeal_tendsToZero Y.hU
        (algebraMap Lambda (Localization.AtPrime P)) ι
        (selmerStages (derivativeDiagram Y.C (retainedRestrictionStages Y.D) .singular))),
      ILStageStep P Cn (E⁄K) hW D0.stage D1.stage := by
  dsimp only
  intro T F _ ι D0 D1
  exact Y.toILStageStep hS e α hP hne B0 F0 excl hdegree coeff scalar span R a ha hdim
    T.toEvaluationTie D0 D1

end Assembly

end ZInQ.Contrib.RC53Assist.StageStepDetection
