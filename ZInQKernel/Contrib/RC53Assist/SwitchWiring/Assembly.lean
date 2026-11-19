import ZInQKernel.Contrib.RC53Assist.RetainedAssembly.Assembly
import ZInQKernel.Contrib.RC53Assist.StageStepDetection.Assembly
import ZInQKernel.Contrib.RC53Assist.ResidueIdentity.Arithmetic
import ZInQKernel.Contrib.RC53Assist.Detection.Inputs
import ZInQKernel.Contrib.RC53Assist.SwitchWiring.FibreColumns

/-!
# Arithmetic realization of inner-limit switching inputs

One application of the retained arithmetic producer fixes the complex,
localization, pairing, and global duality. Detection, the original local
cup calculation, and both integral side models refer to that same output.
The general residue certificate is used: a full equality of local pairing
structures is not assumed. The original coefficient-family presentation and
its finite-stage comparisons still have to be realized arithmetically.
The terminal-successor restriction of literal single-place family equality
is proved separately in `Boundary.lean`.

Sources: tex L4385–4451, L4809–4830, L4860–4868, L4976–5195,
L5027–5086, and L5087–5114.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.SwitchWiring

open CategoryTheory Filter NumberField IsDedekindDomain IsLocalRing
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.UniformSwitch
open ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.RC53Assist.InnerLimit
open ZInQ.Contrib.RC53Assist.InnerLimitMoving
open ZInQ.Contrib.RC53Assist.InnerLimitArith (MovingLabel finPlane_le_limitRelaxed_U)
open ZInQ.Contrib.RC53Assist.Detection
open ZInQ.Manuscript.RC.SelmerComplex (GKS clsAt)
open ZInQ.Manuscript.RC.CoefModules (ActualConj IsOpenKer)
open ZInQ.Manuscript.RC.LambdaCoef (HasFullTwoTorsion IsContChar)
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Manuscript.RC.PrintsArith (Qbar SerreThm3 HasNoCM)
open ZInQ.Manuscript.RC.Limits (stageIdeal stageIdeal_tendsToZero)
open ZInQ.Manuscript.RC.Uniform (Lambda finPlane)
open ZInQ.Manuscript.RC.FibreDuality (RetainedLimitPairingStages RetainedGlobalDualityStages)
open ZInQ.Manuscript.RC.Wiring (ResAt resAt)
open scoped WeierstrassCurve PowerSeries.WithPiTopology Matrix

section ArithmeticSetting

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
  {S : Set (HeightOneSpectrum (𝓞 K))} {E : WeierstrassCurve ℚ} [E.IsElliptic]
  [HasFullTwoTorsion K S (E⁄K)]
  (αStage : ∀ i : ℕ, GKS K S →* (Acoef i)ˣ) [∀ i, IsOpenKer (αStage i)]

/-- Kind: remaining-input structure. Original arithmetic data for the
retained producer, with no retained complex, pairing, or global-duality
output among its fields; tex L4385–4451, L5035–5071. -/
structure RetentionRequest where
  /-- Kind: hypothesis. Finite old support; tex L4391–4406. -/
  finiteSupport : S.Finite
  /-- Kind: hypothesis. The old support includes the dyadic places;
  tex L4391–4406, L5055–5059. -/
  dyadicSupport : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S
  /-- Kind: printed arithmetic input. The original finiteness, dimension,
  duality, and trace statements; tex L4385–4451, L5035–5071. -/
  prints : RetainedAssembly.ArithmeticPrints K
  /-- Kind: data. The original arithmetic cochains with one new place;
  tex L4391–4451, L4809–4830. -/
  family : RetainedAssembly.ActualStageFamily S (E⁄K) αStage
  /-- Kind: data. The original coefficient and old-condition dictionaries;
  tex L2743–2760, L5055–5059. -/
  old : RetainedAssembly.OldDualityData family
  /-- Kind: data. The fixed-support residual reference; tex L4401–4406. -/
  reference : RetainedAssembly.StandardOldReference S (E⁄K) αStage
  /-- Kind: data. The finite width of the residual support comparison;
  tex L4401–4406. -/
  width : ℕ
  /-- Kind: remaining arithmetic inputs. Original cochain comparisons and
  varying-support residual control; tex L4385–4451, L5035–5071. -/
  arithmetic : RetainedAssembly.ArithmeticInputs family old reference width

variable {αStage}

/-- Kind: constructed retained data. A single chosen output of the
arithmetic assembly supplies the common complex, pairing, global duality,
and conditional certificates; tex L4385–4451, L5035–5071. -/
def RetentionRequest.result (T : RetentionRequest (E := E) αStage)
    (Cn : ActualConj K S) (hW : (E⁄K).map (Cn.κ : K →+* K) = E⁄K)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite) :
    RetainedAssembly.AssembledLimit T.arithmetic U hU Cn hW :=
  Classical.choice (RetainedAssembly.assemble_inner_limit T.prints inferInstance
    T.finiteSupport T.dyadicSupport T.arithmetic U hU Cn hW)

/-- Kind: definition. The global fibre on the single chosen retained
output; tex L4391–4451. -/
def RetentionRequest.global (T : RetentionRequest (E := E) αStage)
    (Cn : ActualConj K S) (hW : (E⁄K).map (Cn.κ : K →+* K) = E⁄K)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite)
    (P : Ideal Lambda) [P.IsPrime] : GCx (ResAt P) :=
  fibreLimitGlobal U hU P (T.result Cn hW U hU).C

/-- Kind: remaining-input structure. Serre, dihedral kernel fields,
nonquadratic moving inertia, and an original cochain embedding are the
inputs. The induced coefficient action, coefficient dictionary, common
scalar, full coefficient span, partner, and detecting determinant are
constructed, not assumed; tex L4768–4830, L5087–5114. -/
structure DetectionRemaining (T : RetentionRequest (E := E) αStage)
    (Cn : ActualConj K S) (hW : (E⁄K).map (Cn.κ : K →+* K) = E⁄K)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite)
    (P : Ideal Lambda) [P.IsPrime]
    (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
    (χ : GKS K S →* Lambdaˣ) [IsContChar χ] where
  /-- Kind: hypothesis. The number field is quadratic; tex L4788–4830. -/
  degree : Module.finrank ℚ K = 2
  /-- Kind: hypothesis. The coefficient prime has height one;
  tex L4976–4991. -/
  height : P.height = 1
  /-- Kind: hypothesis. The coefficient prime is not the dyadic prime;
  tex L4976–4991. -/
  notTwo : P ≠ Ideal.span {2}
  /-- Kind: printed arithmetic input. The non-CM open-image theorem;
  tex L4768–4785. -/
  serre : SerreThm3
  /-- Kind: hypothesis. The rational curve has no complex multiplication;
  tex L4768–4785. -/
  nonCM : HasNoCM E
  /-- Kind: data. The arithmetic fields fixed by the common kernel;
  tex L4788–4830. -/
  B0 : ℕ → IntermediateField ℚ Qbar
  /-- Kind: hypothesis. The kernel fields are normal; tex L4788–4830. -/
  normalB : ∀ i, Normal ℚ (B0 i)
  /-- Kind: hypothesis. The kernel fields are finite; tex L4788–4830. -/
  finiteB : ∀ i, FiniteDimensional ℚ (B0 i)
  /-- Kind: arithmetic input. Actual conjugation acts by inversion on the
  specified character and kernel fields; tex L4768–4785, L4788–4830. -/
  dihedral : Detection.Inputs.DihedralKernelFields S e χ Cn B0
  /-- Kind: arithmetic input. A Tate-precision-fixing moving inertia
  sequence has inverse, nonquadratic scalar characters; tex L4779–4785. -/
  inertia : Detection.Inputs.NonquadraticInertiaInput
    (S := S) (e := e) (α := χ) (E := E) (C := Cn)
    (hdegree := degree) (U := U) (P := P)
  /-- Kind: data. Previously specified evaluation fields;
  tex L4809–4830, L5087–5114. -/
  F0 : ℕ → IntermediateField ℚ Qbar
  /-- Kind: hypothesis. The evaluation fields are finite;
  tex L4809–4830, L5087–5114. -/
  finiteF : ∀ i, FiniteDimensional ℚ (F0 i)
  /-- Kind: data. Finite sets of excluded rational primes;
  tex L4809–4830. -/
  excluded : ℕ → Finset ℕ
  /-- Kind: data. The number of original integral columns;
  tex L4391–4451, L5087–5114. -/
  n : ℕ
  /-- Kind: original cochain comparison. Degrees zero, one, and two,
  both differential identities, and original-basis normalization, on the
  same global retained fibre; tex L4391–4451, L5087–5114. -/
  embedding :
    letI := Detection.Inputs.inducedSequenceAction S e χ E Cn degree U P
    letI := Detection.Inputs.inducedSequenceScalarComm S e χ E Cn degree U P
    Detection.Inputs.RetainedCochainEmbedding
      (S := S) (e := e) (α := χ) (E := E) (U := U) (P := P)
      n (T.global Cn hW U hU P)
  /-- Kind: data. The prescribed global one-cycle; tex L5087–5114. -/
  cycle : LinearMap.ker ((T.global Cn hW U hU P).d 1 2 rfl)
  /-- Kind: hypothesis. The prescribed global cohomology class is nonzero;
  tex L5087–5114. -/
  cycle_nonzero : clsAt (T.global Cn hW U hU P) 1 2 rfl cycle ≠ 0
  /-- Kind: hypothesis. The global first cohomology has dimension greater
  than one; tex L4997–5003, L5087–5114. -/
  dimension : 1 < Module.finrank (ResAt P)
    ((T.global Cn hW U hU P).toCC.homology 1)

variable {T : RetentionRequest (E := E) αStage} {Cn : ActualConj K S}
  {hW : (E⁄K).map (Cn.κ : K →+* K) = E⁄K}
  {U : Ultrafilter ℕ} {hU : (U : Filter ℕ) ≤ cofinite}
  {P : Ideal Lambda} [P.IsPrime] {e : AlgebraicClosure K ≃ₐ[ℚ] Qbar}
  {χ : GKS K S →* Lambdaˣ} [IsContChar χ]

/-- Kind: constructed cochain evaluation. Boundary reflection follows from
an original cochain embedding; tex L4391–4451, L5087–5114. -/
def DetectionRemaining.evaluation (A : DetectionRemaining T Cn hW U hU P e χ) :
    letI := Detection.Inputs.inducedSequenceAction S e χ E Cn A.degree U P
    letI := Detection.Inputs.inducedSequenceScalarComm S e χ E Cn A.degree U P
    RetainedEvaluation (S := S) (e := e) (α := χ) (E := E) (U := U) (P := P)
      A.n (T.global Cn hW U hU P) := by
  letI := Detection.Inputs.inducedSequenceAction S e χ E Cn A.degree U P
  letI := Detection.Inputs.inducedSequenceScalarComm S e χ E Cn A.degree U P
  exact Detection.Inputs.retainedEvaluation_of_embedding S e χ E U P A.embedding

/-- Kind: constructed arithmetic detection. The existing arithmetic
producer constructs the coefficient inputs, partner, common-kernel
representatives, and normalized determinant; tex L4768–4830, L5087–5114. -/
def DetectionRemaining.detect (A : DetectionRemaining T Cn hW U hU P e χ) :
    letI := A.normalB
    letI := A.finiteB
    letI := A.finiteF
    letI := Detection.Inputs.inducedSequenceAction S e χ E Cn A.degree U P
    letI := Detection.Inputs.inducedSequenceScalarComm S e χ E Cn A.degree U P
    ArithmeticDetection S T.finiteSupport e χ E Cn U P A.B0 A.F0 A.excluded A.degree
      (T.global Cn hW U hU P) A.evaluation A.cycle := by
  letI := A.normalB
  letI := A.finiteB
  letI := A.finiteF
  letI := Detection.Inputs.inducedSequenceAction S e χ E Cn A.degree U P
  letI := Detection.Inputs.inducedSequenceScalarComm S e χ E Cn A.degree U P
  have : FiniteDimensional (ResAt P) ((T.global Cn hW U hU P).toCC.homology 1) :=
    StageStepDetection.fibre_h1_finite U hU P (T.result Cn hW U hU).C
  exact Detection.Inputs.detection_with_constructed_inputs S T.finiteSupport e χ E Cn A.degree
    U hU P A.height A.notTwo A.serre A.nonCM A.B0 A.dihedral A.inertia A.F0 A.excluded
    (T.global Cn hW U hU P) A.embedding A.cycle A.cycle_nonzero A.dimension

/-- Kind: constructed moving label. This is the label selected by the
normalized detection producer, not an independently chosen prime sequence;
tex L4809–4830, L5087–5114. -/
def DetectionRemaining.label (A : DetectionRemaining T Cn hW U hU P e χ) : MovingLabel K S := by
  letI := A.normalB
  letI := A.finiteB
  letI := A.finiteF
  letI := Detection.Inputs.inducedSequenceAction S e χ E Cn A.degree U P
  letI := Detection.Inputs.inducedSequenceScalarComm S e χ E Cn A.degree U P
  let r := A.detect
  let H := arithmeticKernelFamily E S e χ r.kernel
  exact (basisArithmeticLabel S T.finiteSupport e χ E Cn A.evaluation.original H
    (fun i => A.F0 i ⊔ A.B0 i) A.excluded A.degree).label

/-- Kind: proved theorem. Original finite-stage columns and a retained
singular null-homotopy turn the produced normalized determinant into the
finite-plane containment on this same localization;
tex L4391–4451, L5040–5072, L5087–5114. -/
theorem DetectionRemaining.hdet (A : DetectionRemaining T Cn hW U hU P e χ)
    (columns :
      letI := Detection.Inputs.inducedSequenceAction S e χ E Cn A.degree U P
      letI := Detection.Inputs.inducedSequenceScalarComm S e χ E Cn A.degree U P
      StageStepDetection.RetainedEvaluationColumns hU P (T.result Cn hW U hU).D
        A.evaluation A.label) :
    finPlane (ResAt P) (Vec2 (ResAt P)) (Vec2 (ResAt P)) ≤
      (limitRelaxed (T.global Cn hW U hU P) ((T.result Cn hW U hU).D.resLimit hU P)).U := by
  let : ∀ i, Normal ℚ (A.B0 i) := A.normalB
  let : ∀ i, FiniteDimensional ℚ (A.B0 i) := A.finiteB
  let : ∀ i, FiniteDimensional ℚ (A.F0 i) := A.finiteF
  let : DistribMulAction RationalSequences (FibrePair P) :=
    Detection.Inputs.inducedSequenceAction S e χ E Cn A.degree U P
  let : SMulCommClass RationalSequences (ResAt P) (FibrePair P) :=
    Detection.Inputs.inducedSequenceScalarComm S e χ E Cn A.degree U P
  let r := A.detect
  have htie := columns.toEvaluationTie
  exact finPlane_le_limitRelaxed_U (T.global Cn hW U hU P)
    ((T.result Cn hW U hU).D.resLimit hU P) A.cycle.property r.partner.property
    (htie A.cycle) (htie r.partner) r.detecting

/-- Kind: remaining-input structure. All remaining inputs for one switch
on the chosen arithmetic retained output. None of the fields is a retained
duality, residue certificate, detecting determinant, plane containment,
side cohomology equivalence, or Selmer-data equality;
tex L4385–4451, L5027–5086, L5087–5114. -/
structure StepRemainingInputs (A : DetectionRemaining T Cn hW U hU P e χ)
    {F : Type} [Field F] (ι : Localization.AtPrime P →+* F) (S₀ S₁ : TwoTermStage ι) where
  /-- Kind: original local arithmetic input. Unit lifts, oriented
  characters, and original transported cup comparisons on the same
  retained pairing; tex L4385–4451, L4860–4863, L5027–5043. -/
  localArithmetic : ResidueIdentity.RetainedLocalArithmetic U
    (T.result Cn hW U hU).C (T.result Cn hW U hU).D
  /-- Kind: finite-stage cochain input. Cleared original finite columns
  and a singular null-homotopy at the produced label;
  tex L4391–4451, L4809–4830, L5040–5072. -/
  columns :
    letI := Detection.Inputs.inducedSequenceAction S e χ E Cn A.degree U P
    letI := Detection.Inputs.inducedSequenceScalarComm S e χ E Cn A.degree U P
    StageStepDetection.RetainedEvaluationColumns hU P (T.result Cn hW U hU).D
      A.evaluation A.label
  /-- Kind: integral minimal-model input. Actual finite-side class,
  functional, residual shape, and generic degeneracy; tex L4391–4451, L4976–4996. -/
  finiteModel : IntegralMatrixStageData stageIdeal_tendsToZero hU
    (algebraMap Lambda (Localization.AtPrime P)) ι
    (selmerStages (derivativeDiagram (T.result Cn hW U hU).C
      (retainedRestrictionStages (T.result Cn hW U hU).D) .finite))
  /-- Kind: integral minimal-model input. The independent singular-side
  class, functional, residual shape, and generic degeneracy;
  tex L4391–4451, L4976–4996. -/
  singularModel : IntegralMatrixStageData stageIdeal_tendsToZero hU
    (algebraMap Lambda (Localization.AtPrime P)) ι
    (selmerStages (derivativeDiagram (T.result Cn hW U hU).C
      (retainedRestrictionStages (T.result Cn hW U hU).D) .singular))
  /-- Kind: stage identification. The computed finite stage is the specified
  old stage; tex L4391–4451, L5040–5054. -/
  finiteStage : finiteModel.stage = S₀
  /-- Kind: stage identification. The computed singular stage is the specified
  new stage; tex L4391–4451, L5040–5054. -/
  singularStage : singularModel.stage = S₁
  /-- Kind: coordinate input. The coordinate relation at the selected switch;
  tex L5072–5086. -/
  coordinate : CoordStep ι S₀.u S₁.u
  /-- Kind: original label identification. The actual retained arithmetic
  cochains were formed at the produced derivative places;
  tex L4809–4830, L5027–5032. -/
  places : T.family.q = A.label.q

/-- Kind: constructed switch data. The retained output is reused once;
the arithmetic residue calculation proves both residue fields, the
normalized detection proves containment, and the integral side models
construct both cohomology equivalences. The result is the exact general
step-data structure consumed by the family; tex L4385–4451, L5027–5086. -/
def StepRemainingInputs.toStepData {A : DetectionRemaining T Cn hW U hU P e χ}
    {F : Type} [Field F] {ι : Localization.AtPrime P →+* F} {S₀ S₁ : TwoTermStage ι}
    (X : StepRemainingInputs A ι S₀ S₁) : InnerLimitStepData P S₀ S₁ :=
  X.localArithmetic.toStepData hU (T.result Cn hW U hU).E P S₀ S₁
    (A.hdet X.columns)
    (StageStepDetection.finite_identification hU P (T.result Cn hW U hU).D
      X.finiteModel S₀ X.finiteStage)
    (StageStepDetection.singular_identification hU P (T.result Cn hW U hU).D
      X.singularModel S₁ X.singularStage)

/-- Kind: proved theorem. The residue certificate uses the same complex,
localization, and global duality as the constructed step;
tex L4385–4451, L4860–4863, L5027–5070. -/
theorem StepRemainingInputs.certificate {A : DetectionRemaining T Cn hW U hU P e χ}
    {F : Type} [Field F] {ι : Localization.AtPrime P →+* F} {S₀ S₁ : TwoTermStage ι}
    (X : StepRemainingInputs A ι S₀ S₁) :
    FibreInnerLimitPairingCertificate U hU P (T.result Cn hW U hU).C
      ((T.result Cn hW U hU).D.resLimit hU P)
      (X.localArithmetic.εAt P) 1 (X.localArithmetic.JAt P) :=
  X.localArithmetic.certificate hU (T.result Cn hW U hU).E P

/-- Kind: proved theorem. The constructed step retains the exact complex
chosen by the arithmetic assembly; tex L4391–4451. -/
theorem StepRemainingInputs.retained_C {A : DetectionRemaining T Cn hW U hU P e χ}
    {F : Type} [Field F] {ι : Localization.AtPrime P →+* F} {S₀ S₁ : TwoTermStage ι}
    (X : StepRemainingInputs A ι S₀ S₁) :
    X.toStepData.C = (T.result Cn hW U hU).C := rfl

/-- Kind: proved theorem. The constructed step retains the exact
localization and pairing chosen by the arithmetic assembly;
tex L4385–4451. -/
theorem StepRemainingInputs.retained_D {A : DetectionRemaining T Cn hW U hU P e χ}
    {F : Type} [Field F] {ι : Localization.AtPrime P →+* F} {S₀ S₁ : TwoTermStage ι}
    (X : StepRemainingInputs A ι S₀ S₁) :
    X.toStepData.D = (T.result Cn hW U hU).D := rfl

/-- Kind: proved theorem. The constructed step uses the global duality
on that same chosen retained pairing; tex L4385–4451. -/
theorem StepRemainingInputs.retained_E {A : DetectionRemaining T Cn hW U hU P e χ}
    {F : Type} [Field F] {ι : Localization.AtPrime P →+* F} {S₀ S₁ : TwoTermStage ι}
    (X : StepRemainingInputs A ι S₀ S₁) :
    X.toStepData.E = (T.result Cn hW U hU).E := rfl

end ArithmeticSetting

section FamilySetting

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
  {S : Set (HeightOneSpectrum (𝓞 K))} {E : WeierstrassCurve ℚ} [E.IsElliptic]
  [HasFullTwoTorsion K S (E⁄K)]
  {αStage : ∀ i : ℕ, GKS K S →* (Acoef i)ˣ} [∀ i, IsOpenKer (αStage i)]
  {Cn : ActualConj K S} {hW : (E⁄K).map (Cn.κ : K →+* K) = E⁄K}
  {U : Ultrafilter ℕ} {hU : (U : Filter ℕ) ≤ cofinite}
  {P : Ideal Lambda} [P.IsPrime] {e : AlgebraicClosure K ≃ₐ[ℚ] Qbar}
  {χ : GKS K S →* Lambdaˣ} [IsContChar χ]
  {F : Type} [Field F] {ι : Localization.AtPrime P →+* F} {u : F}

/-- Kind: remaining-input structure. A switch at one configuration is
specified by original arithmetic inputs, integral side models, coordinate
data, local-condition tags, and finite-stage differential and restriction
comparisons. The selected family prime is the produced arithmetic label.
No equality of a produced Selmer side with a family fibre is assumed;
tex L4391–4451, L4809–4830, L5027–5114. -/
structure ReachableSwitchRemaining (A : FibreAtlas S U hU P)
    (B : FamilyFrame A ι u) (c : A.Config) where
  /-- Kind: original arithmetic input. The retained assembly request;
  tex L4385–4451, L5035–5071. -/
  retention : RetentionRequest (E := E) αStage
  /-- Kind: original arithmetic and cochain input. The normalized detecting
  label is produced on this very retained global fibre;
  tex L4768–4830, L5087–5114. -/
  detection : DetectionRemaining retention Cn hW U hU P e χ
  /-- Kind: remaining step inputs. Both specified family stages occur in
  the side-model identification types at the produced prime;
  tex L4391–4451, L5027–5086. -/
  step : StepRemainingInputs detection ι (B.stage c)
    (B.stage (A.next c (A.primeOfLabel detection.label)))
  /-- Kind: finite-stage source comparison. Integral ranks, differentials,
  and restrictions compare the retained source with the old family fibre;
  tex L4391–4451, L5040–5054. -/
  finiteColumns : DiagramColumns (retention.result Cn hW U hU).C (A.diagram c)
    (retainedRestrictionStages (retention.result Cn hW U hU).D) (A.restriction c)
  /-- Kind: finite-stage source comparison. The same retained source is
  compared with the next family fibre at the produced prime;
  tex L4391–4451, L5040–5054. -/
  singularColumns : DiagramColumns (retention.result Cn hW U hU).C
    (A.diagram (A.next c (A.primeOfLabel detection.label)))
    (retainedRestrictionStages (retention.result Cn hW U hU).D)
    (A.restriction (A.next c (A.primeOfLabel detection.label)))
  /-- Kind: original condition input. The old coefficient presentation uses
  the finite local condition; tex L4834–4907, L5040–5054. -/
  finiteKind : A.kind c = .finite
  /-- Kind: original condition input. The next coefficient presentation uses
  the singular local condition; tex L4834–4907, L5040–5054. -/
  singularKind : A.kind (A.next c (A.primeOfLabel detection.label)) = .singular

/-- Kind: remaining-input structure. The common ultrafilter, the original
coefficient-family presentation and starting inputs, and one original
arithmetic request at every reachable configuration of dimension greater
than one. All targeted realization fields are constructed: there is no
retained complex or duality, certificate, determinant, containment, side
equivalence, or side-to-family equality among these input fields;
tex L4385–4451, L4976–5195. -/
structure RemainingInputs
    (αStage : ∀ i : ℕ, GKS K S →* (Acoef i)ˣ) [∀ i, IsOpenKer (αStage i)]
    (Cn : ActualConj K S) (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
    (χ : GKS K S →* Lambdaˣ) [IsContChar χ]
    (P : Ideal Lambda) [P.IsPrime] {F : Type} [Field F]
    (ι : Localization.AtPrime P →+* F) (u : F) where
  /-- Kind: original coefficient input. Actual conjugation preserves the
  rational curve over the number field; tex L2798–2805, L5027–5032. -/
  hW : (E⁄K).map (Cn.κ : K →+* K) = E⁄K
  /-- Kind: data. The single common inner-limit ultrafilter;
  tex L4391–4451, L5030–5032. -/
  U : Ultrafilter ℕ
  /-- Kind: hypothesis. The ultrafilter tends along increasing precision;
  tex L4391–4451, L5030–5032. -/
  hU : (U : Filter ℕ) ≤ cofinite
  /-- Kind: original coefficient data. The independently specified family
  of original retained cochain matrices; tex L4391–4451, L4976–5086. -/
  atlas : FibreAtlas S U hU P
  /-- Kind: starting inputs. The family models, original class and
  functional, starting coordinate, nonquadraticity, and primitivity;
  tex L4976–5003, L5072–5195. -/
  frame : FamilyFrame atlas ι u
  /-- Kind: original arithmetic and finite-stage cochain inputs. A produced
  derivative label and its source comparisons at every required switch;
  tex L4391–4451, L5027–5114. -/
  switch : ∀ c : atlas.Config, Reach atlas.next atlas.actual c →
    1 < (frame.stage c).fiberDim (resAt P) →
    ReachableSwitchRemaining (αStage := αStage) (Cn := Cn) (hW := hW)
      (e := e) (χ := χ) atlas frame c

/-- Kind: constructed family inputs. Arithmetic retained assembly,
normalized detection, arithmetic residues, and integral side models supply
each exact step. The two literal side-to-family equalities are proved
from original finite-stage column comparisons, not added as input fields;
tex L4385–4451, L4976–5195, L5027–5114. -/
def RemainingInputs.toInnerLimitSwitchInputs
    (X : RemainingInputs (E := E) αStage Cn e χ P ι u) :
    InnerLimitSwitchInputs P X.atlas.family ι u where
  stage := X.frame.stage
  model := X.frame.model
  hz0 := X.frame.hz0
  hw0 := X.frame.hw0
  hu0 := X.frame.hu0
  hnq := X.frame.hnq
  primitive := X.frame.primitive
  step c hc h1 := by
    let T := X.switch c hc h1
    let p := X.atlas.primeOfLabel T.detection.label
    let Y := T.step.toStepData
    refine ⟨p, ⟨T.step.coordinate⟩, Y, ?_, ?_⟩
    · change Y.toStep.SF.Dside = X.atlas.fibre c
      calc
        Y.toStep.SF.Dside = retainedFibreData X.hU P
            (T.retention.result Cn X.hW X.U X.hU).C
            (T.retention.result Cn X.hW X.U X.hU).D .finite :=
          step_finite_side_data Y
        _ = derivativeSideData stageIdeal_tendsToZero X.hU
            (algebraMap Lambda (ResAt P)) (X.atlas.diagram c)
            (X.atlas.restriction c) .finite :=
          T.finiteColumns.data_eq X.hU P .finite
        _ = X.atlas.fibre c := by
          unfold FibreAtlas.fibre
          rw [T.finiteKind]
    · change Y.toStep.SS.Dside = X.atlas.fibre (X.atlas.next c p)
      calc
        Y.toStep.SS.Dside = retainedFibreData X.hU P
            (T.retention.result Cn X.hW X.U X.hU).C
            (T.retention.result Cn X.hW X.U X.hU).D .singular :=
          step_singular_side_data Y
        _ = derivativeSideData stageIdeal_tendsToZero X.hU
            (algebraMap Lambda (ResAt P)) (X.atlas.diagram (X.atlas.next c p))
            (X.atlas.restriction (X.atlas.next c p)) .singular :=
          T.singularColumns.data_eq X.hU P .singular
        _ = X.atlas.fibre (X.atlas.next c p) := by
          unfold FibreAtlas.fibre
          rw [T.singularKind]

/-- Kind: proved theorem from the remaining arithmetic, original cochain,
and starting inputs. The existing family consumer yields regularity at
the coefficient prime; tex L4976–5195. -/
theorem RemainingInputs.regular (X : RemainingInputs (E := E) αStage Cn e χ P ι u)
    (hι : Function.Injective ι) : ∃ a, ι a = u :=
  regular_of_innerLimitSwitchInputs hι X.toInnerLimitSwitchInputs

end FamilySetting

end ZInQ.Contrib.RC53Assist.SwitchWiring
