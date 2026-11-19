import ZInQKernel.Contrib.OneProof.RC.Wiring.InnerLimitSwitchModel
import ZInQKernel.Contrib.RC53Assist.SwitchInterface.Assembly

/-!
Theorem 5.3, Lane RC0 round 14: the RC53 group's remaining inputs give the switch model.

Proposition `ex:limits-uniform-lower-bound`, height-one regularity (tex 4976–5195), with the switch
at a derivative label taken on the inner-limit objects (tex 4391–4451, 5027–5086).

The side models of `InnerLimitSwitchModel` are homotopy equivalences over `k(𝔭)` between the
Selmer complex of each limit side and the family fibre. The RC53 group's integral side models give
them.
For a retained side, the identification behind its side-to-stage cohomology isomorphism `φ` is a
composite of cochain isomorphisms (the literal side datum, the derivative Selmer cone, the residue
of the integral matrix limit) and of the scalar extension of the minimal-model homotopy
equivalence; only its last link passes to coordinates of `H¹`. That link is lifted here to a
cochain isomorphism: the residual minimal model and the stage's fibre complex both have vanishing
differentials (minimality, resp. the stage matrix reduces to zero) and the same based terms in
degrees one and two (tex 4976–4996). Composing with the inverse family model gives the side
models (tex 4997–5003, 5040–5086).

This is a conditional bridge from the supplied integral minimal models and frame.
`residualStageIso` compares two zero-differential models with the stated degree-one and degree-two
bases; it does not extend arbitrary H¹-only data. The full composites compare the Selmer complexes
of the supplied step sides with the fibres of `atlas.family`. Those fibres are retained matrix
presentations. Transporting these model comparisons to the prescribed genuine arithmetic family,
and supplying a frame for actual classes whose residue may vanish, remain separate ELLIOT + GLUE
obligations. The bridge does not prove `IsGenuineFamilyAt` or construct `InnerLimitSwitchActual`
from `RemainingInputsIso` alone.

* `residualStageIso` (PROVED): the residual complex of a based minimal model is isomorphic, as a
  complex, to the fibre complex of any stage of the same size whose matrix reduces to zero.
* `integralStageChainEquiv`, `derivativeSideChainEquiv`, `retainedFibreChainEquiv`,
  `stepFiniteSideChainEquiv`, `stepSingularSideChainEquiv`, `stepRemainingFiniteSideEquiv`,
  `stepRemainingSingularSideEquiv` (PROVED): the chain-level side-to-stage equivalences.
* `IntegralSideModels`, `SwitchModelFrame.toInnerLimitSwitchModel` (PROVED): a frame and step
  data with integral side models at every switch give the switch model.
* `RemainingInputsIso.toInnerLimitSwitchModel`, `RemainingInputs.toInnerLimitSwitchModel`
  (PROVED): the RC53 group's remaining inputs give the switch model, with the steps `toStepData`.
* `InnerLimitSwitchInputs.toInnerLimitSwitchModel` (PROVED): literal side equalities give side
  models (identity equivalences).
* `RemainingInputsIso.regular_of_switchModel` (PROVED, from the inputs): regularity at a
  height-one prime through the switch model.
* `SwitchModelFrame.toInnerLimitSwitchActual` (PROVED): a frame and linked switches on the actual
  stage complexes with integral side models give the actual inputs.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open CategoryTheory CategoryTheory.Limits Filter NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.UniformSwitch ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.CloudB3RC53.ResidualTransfer (resCx resF resF_additive)
open ZInQ.Contrib.RC53Assist.InnerLimit (ComplexStages MapStages)
open ZInQ.Contrib.RC53Assist.InnerLimitMoving (BasedTwoTermModel IntegralMatrixStageData
  canonicalMatrixModel residualMatrixIso scalarComplex derivativeMatrixIso derivativeSideData
  selmerStages derivativeDiagram fullLocalStages ConditionKind retainedRestrictionStages
  localizedResidue_comp)
open ZInQ.Contrib.RC53Assist.SwitchWiring (StepRemainingInputs DetectionRemaining RetentionRequest
  retainedFibreData step_finite_side_data step_singular_side_data)
open ZInQ.Manuscript.RC.Limits (IdealsTendToZero stageIdeal stageIdeal_tendsToZero)
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.FibreDuality (RetainedLimitPairingStages)
open ZInQ.Manuscript.RC.SelmerComplex (GKS)
open ZInQ.Manuscript.RC.CoefModules (ActualConj IsOpenKer)
open ZInQ.Manuscript.RC.LambdaCoef (HasFullTwoTorsion IsContChar)
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Manuscript.RC.PrintsArith (Qbar)
open scoped WeierstrassCurve PowerSeries.WithPiTopology

/-! **The residual minimal model and the stage fibre complex** -/

section ResidualStage

variable {A : Type} [CommRing A] [IsLocalRing A] {C : GCx A}

/-- **The fibre complex of a residually zero stage has zero differentials** (tex 4976–4996).
Kind: PROVED. -/
theorem twoTermFiberComplex_d_eq_zero {F : Type} [Field F] {ι : A →+* F} (S : TwoTermStage ι)
    (hS : S.D.map (IsLocalRing.residue A) = 0) (i j : ℤ) :
    (twoTermFiberComplex (IsLocalRing.residue A) S).d i j = 0 := by
  by_cases h01 : i = 0 ∧ j = 1
  · obtain ⟨rfl, rfl⟩ := h01
    rfl
  by_cases h12 : i = 1 ∧ j = 2
  · obtain ⟨rfl, rfl⟩ := h12
    change ModuleCat.ofHom ((S.D.map (IsLocalRing.residue A)).mulVecLin) = 0
    rw [hS]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Matrix.zero_mulVec x
  exact threeTermD_eq_zero _ _ i j h01 h12

omit [IsLocalRing A] in
/-- The fibre complex of a stage vanishes outside degrees one and two. Kind: PROVED. -/
theorem twoTermFiberComplex_isZero {F k : Type} [Field F] [Field k] {ι : A →+* F}
    (ρ : A →+* k) (S : TwoTermStage ι) (i : ℤ) (h1 : i ≠ 1) (h2 : i ≠ 2) :
    IsZero ((twoTermFiberComplex ρ S).X i) := by
  have : Subsingleton ((twoTermFiberComplex ρ S).X i) := by
    rcases i with (_ | _ | _ | n) | n
    · exact (inferInstance : Subsingleton PUnit)
    · exact absurd rfl h1
    · exact absurd rfl h2
    · exact (inferInstance : Subsingleton PUnit)
    · exact (inferInstance : Subsingleton PUnit)
  exact ModuleCat.isZero_of_subsingleton _

/-- The residual complex of a based minimal model vanishes outside degrees one and two.
Kind: PROVED. -/
theorem residualModel_isZero (M : BasedTwoTermModel C) (i : ℤ) (h1 : i ≠ 1) (h2 : i ≠ 2) :
    IsZero ((resCx M.model.toCC).X i) := by
  have := resF_additive (R := A)
  have := M.outside i h1 h2
  exact (resF A).map_isZero (ModuleCat.isZero_of_subsingleton (M.model.X i))

/-- The basis in degree two identifies the residual degree-two term with its coordinates.
Kind: definition. -/
def residualCoordsTwo (M : BasedTwoTermModel C) :
    (resCx M.model.toCC).X 2 ≃ₗ[IsLocalRing.ResidueField A]
      (Fin (M.n + 1) → IsLocalRing.ResidueField A) := by
  letI := (IsLocalRing.residue A).toAlgebra
  exact (M.b2.baseChange (IsLocalRing.ResidueField A)).equivFun

/-- The components of `residualStageIso`: the retained bases in degrees one and two, zero
elsewhere. Kind: definition. -/
def residualStageIsoX (M : BasedTwoTermModel C) {F : Type} [Field F] {ι : A →+* F}
    (S : TwoTermStage ι) (hn : S.n = M.n) (i : ℤ) :
    (resCx M.model.toCC).X i ≅ (twoTermFiberComplex (IsLocalRing.residue A) S).X i :=
  if h1 : i = 1 then
    eqToIso (congrArg (resCx M.model.toCC).X h1) ≪≫
      (M.residualCoords.trans (LinearEquiv.funCongrLeft _ _
        (finCongr (congrArg (· + 1) hn)))).toModuleIso ≪≫
      eqToIso (congrArg (twoTermFiberComplex (IsLocalRing.residue A) S).X h1.symm)
  else if h2 : i = 2 then
    eqToIso (congrArg (resCx M.model.toCC).X h2) ≪≫
      ((residualCoordsTwo M).trans (LinearEquiv.funCongrLeft _ _
        (finCongr (congrArg (· + 1) hn)))).toModuleIso ≪≫
      eqToIso (congrArg (twoTermFiberComplex (IsLocalRing.residue A) S).X h2.symm)
  else
    (residualModel_isZero M i h1 h2).iso (twoTermFiberComplex_isZero _ S i h1 h2)

/-- **The residual minimal model is the stage's fibre complex** (tex 4976–4996): both complexes
have zero differentials (minimality, resp. the stage matrix reduces to zero) and the same based
terms in degrees one and two. Kind: PROVED. -/
def residualStageIso (M : BasedTwoTermModel C) {F : Type} [Field F] {ι : A →+* F}
    (S : TwoTermStage ι) (hn : S.n = M.n) (hS : S.D.map (IsLocalRing.residue A) = 0) :
    resCx M.model.toCC ≅ twoTermFiberComplex (IsLocalRing.residue A) S :=
  HomologicalComplex.Hom.isoOfComponents (residualStageIsoX M S hn) fun i j _ => by
    rw [M.residual_d_zero i j, twoTermFiberComplex_d_eq_zero S hS i j, comp_zero, zero_comp]

end ResidualStage

/-! **The chain-level side-to-stage equivalences** -/

section IntegralModels

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CompactSpace R] [T2Space R] {I : ℕ → Ideal R} {U : Ultrafilter ℕ}
  {hI : IdealsTendToZero I} {hU : (U : Filter ℕ) ≤ cofinite}
  {A : Type} [CommRing A] [IsLocalRing A] {ρ : R →+* A} {F : Type} [Field F] {ι : A →+* F}

/-- **The chain-level equivalence of an integral matrix model with its stage** (tex 4391–4451,
4976–4996): the residue of the integral matrix limit (`residualMatrixIso`), the scalar extension
of the minimal-model homotopy equivalence, and `residualStageIso`. Kind: PROVED. -/
def integralStageChainEquiv {C : ComplexStages I U} (D : IntegralMatrixStageData hI hU ρ ι C) :
    HomotopyEquiv (scalarComplex hI hU ((IsLocalRing.residue A).comp ρ) C).toCC
      (twoTermFiberComplex (IsLocalRing.residue A) D.stage) :=
  (HomotopyEquiv.ofIso (residualMatrixIso hI hU ρ C).symm).trans
    ((canonicalMatrixModel hI hU ρ C D.shape).residualEquivalence.trans
      (HomotopyEquiv.ofIso (residualStageIso (canonicalMatrixModel hI hU ρ C D.shape) D.stage
        rfl (canonicalMatrixModel hI hU ρ C D.shape).matrix_residue_zero)))

/-- **The chain-level equivalence of a derivative side with its stage** (tex 4391–4451,
5040–5054): the derivative Selmer cone (`derivativeMatrixIso`) and `integralStageChainEquiv`.
Kind: PROVED. -/
def derivativeSideChainEquiv (G : ComplexStages I U) (r : MapStages G (fullLocalStages I U))
    (s : ConditionKind)
    (D : IntegralMatrixStageData hI hU ρ ι (selmerStages (derivativeDiagram G r s))) :
    HomotopyEquiv
      (selCx (derivativeSideData hI hU ((IsLocalRing.residue A).comp ρ) G r s)).toCC
      (twoTermFiberComplex (IsLocalRing.residue A) D.stage) :=
  (HomotopyEquiv.ofIso
      (derivativeMatrixIso hI hU ((IsLocalRing.residue A).comp ρ) G r s).symm).trans
    (integralStageChainEquiv D)

end IntegralModels

section Retained

variable {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ cofinite) (P : Ideal Lambda) [P.IsPrime]
  (C : ComplexStages (R := Lambda) stageIdeal U) (D : RetainedLimitPairingStages U C)
  {F : Type} [Field F] {ι : Localization.AtPrime P →+* F}

/-- **The chain-level equivalence of a retained fibre side with its integral stage** (tex
4391–4451, 5040–5054): `derivativeSideChainEquiv` at `Λ → Λ_𝔭`, the residue of the localization
being the specialization `Λ → k(𝔭)` (`localizedResidue_comp`). Kind: PROVED. -/
def retainedFibreChainEquiv (s : ConditionKind)
    (D0 : IntegralMatrixStageData stageIdeal_tendsToZero hU
      (algebraMap Lambda (Localization.AtPrime P)) ι
      (selmerStages (derivativeDiagram C (retainedRestrictionStages D) s))) :
    HomotopyEquiv (selCx (retainedFibreData hU P C D s)).toCC
      (twoTermFiberComplex (resAt P) D0.stage) :=
  (HomotopyEquiv.ofIso (eqToIso (congrArg (fun f : Lambda →+* ResAt P =>
      (selCx (derivativeSideData stageIdeal_tendsToZero hU f C (retainedRestrictionStages D)
        s)).toCC) (localizedResidue_comp P).symm))).trans
    (derivativeSideChainEquiv C (retainedRestrictionStages D) s D0)

end Retained

section Step

variable {P : Ideal Lambda} [P.IsPrime] {F : Type} [Field F] {ι : Localization.AtPrime P →+* F}
  {S₀ S₁ : TwoTermStage ι}

/-- **The finite side of inner-limit step data is chain-level equivalent to its stage**, when an
integral model of the retained finite side computes that stage (tex 4391–4451, 5040–5086).
Kind: PROVED. -/
def stepFiniteSideChainEquiv (Y : InnerLimitStepData P S₀ S₁)
    (D0 : IntegralMatrixStageData stageIdeal_tendsToZero Y.hU
      (algebraMap Lambda (Localization.AtPrime P)) ι
      (selmerStages (derivativeDiagram Y.C (retainedRestrictionStages Y.D) .finite)))
    (hS0 : D0.stage = S₀) :
    HomotopyEquiv (selCx Y.toStep.SF.Dside).toCC (twoTermFiberComplex (resAt P) S₀) :=
  (HomotopyEquiv.ofIso (eqToIso (congrArg (fun X : SelData (ResAt P) => (selCx X).toCC)
      (step_finite_side_data Y)))).trans
    ((retainedFibreChainEquiv Y.hU P Y.C Y.D .finite D0).trans
      (HomotopyEquiv.ofIso (eqToIso (congrArg (twoTermFiberComplex (resAt P)) hS0))))

/-- **The singular side of inner-limit step data is chain-level equivalent to its stage**, when
an integral model of the retained singular side computes that stage (tex 4391–4451, 5040–5086).
Kind: PROVED. -/
def stepSingularSideChainEquiv (Y : InnerLimitStepData P S₀ S₁)
    (D1 : IntegralMatrixStageData stageIdeal_tendsToZero Y.hU
      (algebraMap Lambda (Localization.AtPrime P)) ι
      (selmerStages (derivativeDiagram Y.C (retainedRestrictionStages Y.D) .singular)))
    (hS1 : D1.stage = S₁) :
    HomotopyEquiv (selCx Y.toStep.SS.Dside).toCC (twoTermFiberComplex (resAt P) S₁) :=
  (HomotopyEquiv.ofIso (eqToIso (congrArg (fun X : SelData (ResAt P) => (selCx X).toCC)
      (step_singular_side_data Y)))).trans
    ((retainedFibreChainEquiv Y.hU P Y.C Y.D .singular D1).trans
      (HomotopyEquiv.ofIso (eqToIso (congrArg (twoTermFiberComplex (resAt P)) hS1))))

end Step

/-! **Switch models from integral side models** -/

section IntegralSides

variable {P : Ideal Lambda} [P.IsPrime] {F : Type} [Field F] {ι : Localization.AtPrime P →+* F}

/-- **Integral side models of inner-limit step data** (tex 4391–4451, 4976–4996, 5040–5086):
integral matrix models of the retained finite and singular sides of the step whose computed
stages are the old and the next stage. Kind: definition (inputs). -/
structure IntegralSideModels {S₀ S₁ : TwoTermStage ι} (Y : InnerLimitStepData P S₀ S₁) where
  /-- The integral model of the retained finite side. -/
  finite : IntegralMatrixStageData stageIdeal_tendsToZero Y.hU
    (algebraMap Lambda (Localization.AtPrime P)) ι
    (selmerStages (derivativeDiagram Y.C (retainedRestrictionStages Y.D) .finite))
  /-- The integral model of the retained singular side. -/
  singular : IntegralMatrixStageData stageIdeal_tendsToZero Y.hU
    (algebraMap Lambda (Localization.AtPrime P)) ι
    (selmerStages (derivativeDiagram Y.C (retainedRestrictionStages Y.D) .singular))
  /-- The computed finite stage is the old stage. -/
  finiteStage : finite.stage = S₀
  /-- The computed singular stage is the next stage. -/
  singularStage : singular.stage = S₁

variable {Φ : SwitchFamily (ResAt P) (Localization.AtPrime P)} {u : F}

/-- **The switch model from integral side models** (tex 4976–5195, 5027–5086): a frame and, at
each switch, step data with integral side models; the side models are the chain-level
side-to-stage equivalences followed by the inverse family models. Kind: PROVED. -/
def SwitchModelFrame.toInnerLimitSwitchModel (X : SwitchModelFrame Φ ι (resAt P) u)
    (step : ∀ c, Reach Φ.next Φ.actual c → 1 < (X.stage c).fiberDim (resAt P) →
      ∃ p : Φ.Prime, Nonempty (CoordStep ι (X.stage c).u (X.stage (Φ.next c p)).u) ∧
        ∃ Y : InnerLimitStepData P (X.stage c) (X.stage (Φ.next c p)),
          Nonempty (IntegralSideModels Y)) :
    InnerLimitSwitchModel P Φ ι u where
  toSwitchModelFrame := X
  step c hc h1 := by
    obtain ⟨p, hcs, Y, ⟨M⟩⟩ := step c hc h1
    exact ⟨p, hcs, Y,
      ⟨(stepFiniteSideChainEquiv Y M.finite M.finiteStage).trans (X.model c).symm⟩,
      ⟨(stepSingularSideChainEquiv Y M.singular M.singularStage).trans
        (X.model (Φ.next c p)).symm⟩⟩

end IntegralSides

/-! **The RC53 group's remaining inputs** -/

section Remaining

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
  {S : Set (HeightOneSpectrum (𝓞 K))} {E : WeierstrassCurve ℚ} [E.IsElliptic]
  [HasFullTwoTorsion K S (E⁄K)]
  {αStage : ∀ i : ℕ, GKS K S →* (Acoef i)ˣ} [∀ i, IsOpenKer (αStage i)]
  {Cn : ActualConj K S} {hW : (E⁄K).map (Cn.κ : K →+* K) = E⁄K}
  {U : Ultrafilter ℕ} {hU : (U : Filter ℕ) ≤ cofinite}
  {P : Ideal Lambda} [P.IsPrime] {e : AlgebraicClosure K ≃ₐ[ℚ] Qbar}
  {χ : GKS K S →* Lambdaˣ} [IsContChar χ]
  {F : Type} [Field F] {ι : Localization.AtPrime P →+* F} {u : F}

/-- **The finite side of a produced step is chain-level equivalent to the old stage**: the step
`toStepData` with its integral finite model and stage identification. Kind: PROVED. -/
def stepRemainingFiniteSideEquiv {T : RetentionRequest (E := E) αStage}
    {A : DetectionRemaining T Cn hW U hU P e χ} {S₀ S₁ : TwoTermStage ι}
    (X : StepRemainingInputs A ι S₀ S₁) :
    HomotopyEquiv (selCx X.toStepData.toStep.SF.Dside).toCC (twoTermFiberComplex (resAt P) S₀) :=
  stepFiniteSideChainEquiv X.toStepData X.finiteModel X.finiteStage

/-- **The singular side of a produced step is chain-level equivalent to the next stage**: the
step `toStepData` with its integral singular model and stage identification. Kind: PROVED. -/
def stepRemainingSingularSideEquiv {T : RetentionRequest (E := E) αStage}
    {A : DetectionRemaining T Cn hW U hU P e χ} {S₀ S₁ : TwoTermStage ι}
    (X : StepRemainingInputs A ι S₀ S₁) :
    HomotopyEquiv (selCx X.toStepData.toStep.SS.Dside).toCC (twoTermFiberComplex (resAt P) S₁) :=
  stepSingularSideChainEquiv X.toStepData X.singularModel X.singularStage

/-- **The RC53 group's remaining inputs give the switch model** (tex 4385–4451, 4976–5195,
5027–5114): the frame of `toInnerLimitSwitchInputsIso` (primitive classes are nonzero) and, at
each switch, the produced prime, its coordinate step, the step `toStepData`, and the side models:
the chain-level side-to-stage equivalences followed by the inverse family models. Kind: PROVED. -/
def RemainingInputsIso.toInnerLimitSwitchModel
    (X : ZInQ.Contrib.RC53Assist.SwitchInterface.RemainingInputsIso (E := E) αStage Cn e χ P ι u) :
    InnerLimitSwitchModel P X.atlas.family ι u where
  toSwitchModelFrame :=
    ZInQ.Manuscript.RC.Wiring.NonquadSwitchFrame.toModelFrame
      X.toInnerLimitSwitchInputsIso.toNonquadSwitchFrame
  step c hc h1 := by
    let T := X.switch c hc h1
    exact ⟨X.atlas.primeOfLabel T.detection.label, ⟨T.step.coordinate⟩, T.step.toStepData,
      ⟨(stepRemainingFiniteSideEquiv T.step).trans (X.frame.model c).symm⟩,
      ⟨(stepRemainingSingularSideEquiv T.step).trans
        (X.frame.model (X.atlas.next c (X.atlas.primeOfLabel T.detection.label))).symm⟩⟩

/-- **The original remaining inputs give the switch model**, through the adapted inputs
(`ofRemainingInputs`). Their original literal-source and residue-primitivity requirements remain;
this conversion does not enlarge the class of original inputs. Kind: PROVED. -/
def RemainingInputs.toInnerLimitSwitchModel
    (X : ZInQ.Contrib.RC53Assist.SwitchWiring.RemainingInputs (E := E) αStage Cn e χ P ι u) :
    InnerLimitSwitchModel P X.atlas.family ι u :=
  RemainingInputsIso.toInnerLimitSwitchModel
    (ZInQ.Contrib.RC53Assist.SwitchInterface.ofRemainingInputs X)

/-- **Regularity from the RC53 group's remaining inputs through the switch model** at a
height-one prime (`regular_of_innerLimitSwitchModel`). Kind: PROVED (from the inputs). -/
theorem RemainingInputsIso.regular_of_switchModel
    (X : ZInQ.Contrib.RC53Assist.SwitchInterface.RemainingInputsIso (E := E) αStage Cn e χ P ι u)
    (hP : P.height = 1) (hι : Function.Injective ι) : ∃ a, ι a = u :=
  regular_of_innerLimitSwitchModel hP hι (RemainingInputsIso.toInnerLimitSwitchModel X)

end Remaining

/-! **Literal side equalities** -/

section Literal

variable {P : Ideal Lambda} [P.IsPrime] {F : Type} [Field F]
  {Φ : SwitchFamily (ResAt P) (Localization.AtPrime P)} {ι : Localization.AtPrime P →+* F}
  {u : F}

/-- **Literal side equalities give side models**: the identity homotopy equivalences along the
equalities `hF`, `hS` of `InnerLimitSwitchInputs`. Kind: PROVED. -/
def InnerLimitSwitchInputs.toInnerLimitSwitchModel (X : InnerLimitSwitchInputs P Φ ι u) :
    InnerLimitSwitchModel P Φ ι u where
  stage := X.stage
  model := X.model
  hz0 := X.hz0
  hw0 := X.hw0
  hu0 := X.hu0
  hnq := X.hnq
  class_ne_zero c hc := by
    obtain ⟨i, hi⟩ := X.primitive c hc
    exact ⟨i, fun h => hi (by rw [h, map_zero])⟩
  step c hc h1 := by
    obtain ⟨p, hcs, Y, hF, hS⟩ := X.step c hc h1
    exact ⟨p, hcs, Y,
      ⟨HomotopyEquiv.ofIso (eqToIso (congrArg (fun D : SelData (ResAt P) => (selCx D).toCC) hF))⟩,
      ⟨HomotopyEquiv.ofIso (eqToIso (congrArg (fun D : SelData (ResAt P) => (selCx D).toCC) hS))⟩⟩

end Literal

/-! **The actual inputs from linked switches with integral side models** -/

section ActualSides

open ZInQ.Contrib.RC53Assist.InnerLimitArith (MilneLocalFiniteness MilneGlobalFiniteness)

variable {P : Ideal Lambda} [P.IsPrime] {F : Type} [Field F]
  {ι : Localization.AtPrime P →+* F} {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} {Cn : ActualConj K S}
  {W : WeierstrassCurve K} {hW : W.map (Cn.κ : K →+* K) = W}
  [W.IsElliptic] [HasFullTwoTorsion K S W]
  (hmloc : MilneLocalFiniteness) (hmglob : MilneGlobalFiniteness)
  {Φ : SwitchFamily (ResAt P) (Localization.AtPrime P)} {u : F}

/-- **`InnerLimitSwitchActual` from a frame and linked switches with integral side models**: the
side models are `stepFiniteSideChainEquiv`, `stepSingularSideChainEquiv` composed with the inverse
family models. Kind: PROVED. -/
def SwitchModelFrame.toInnerLimitSwitchActual (Xf : SwitchModelFrame Φ ι (resAt P) u)
    (step : ∀ c, Reach Φ.next Φ.actual c → 1 < (Xf.stage c).fiberDim (resAt P) →
      ∃ p : Φ.Prime, Nonempty (CoordStep ι (Xf.stage c).u (Xf.stage (Φ.next c p)).u) ∧
        ∃ X : ILStageStepLinked P Cn W hW (Xf.stage c) (Xf.stage (Φ.next c p)),
          Nonempty (IntegralSideModels (X.stepData hmloc hmglob))) :
    InnerLimitSwitchActual P Cn W hW hmloc hmglob Φ ι u where
  toSwitchModelFrame := Xf
  step c hc h1 := by
    obtain ⟨p, hcs, X, ⟨M⟩⟩ := step c hc h1
    exact ⟨p, hcs, X,
      ⟨(stepFiniteSideChainEquiv (X.stepData hmloc hmglob) M.finite M.finiteStage).trans
        (Xf.model c).symm⟩,
      ⟨(stepSingularSideChainEquiv (X.stepData hmloc hmglob) M.singular M.singularStage).trans
        (Xf.model (Φ.next c p)).symm⟩⟩

end ActualSides

end ZInQ.Manuscript.RC.Wiring
