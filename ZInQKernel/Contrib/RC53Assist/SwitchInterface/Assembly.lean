import ZInQKernel.Contrib.RC53Assist.SwitchInterface.Interface
import ZInQKernel.Contrib.RC53Assist.SwitchWiring.Assembly

/-!
# Arithmetic assembly for cohomological switching

The retained arithmetic output, detecting label, local residue calculation,
integral side models and coordinate step are unchanged. No local-condition
tag is equated with a different tag at a later switch. The side cohomology
identifications already constructed by the integral models suffice.

The original remaining-input structure maps to the new one, but still has
its original terminal-successor restriction. The new structure therefore
omits the old source-column comparisons and finite/singular tag equations,
rather than merely hiding them behind a conversion.

Sources: tex L4385–4451, L4976–5195, L5027–5114.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace ZInQ.Contrib.RC53Assist.SwitchInterface

open CategoryTheory Filter NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.UniformSwitch
open ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.RC53Assist.SwitchWiring
open ZInQ.Manuscript.RC.SelmerComplex (GKS)
open ZInQ.Manuscript.RC.CoefModules (ActualConj IsOpenKer)
open ZInQ.Manuscript.RC.LambdaCoef (HasFullTwoTorsion IsContChar)
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Manuscript.RC.PrintsArith (Qbar)
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.Wiring (ResAt resAt)
open scoped WeierstrassCurve

section ArithmeticSetting

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
  {S : Set (HeightOneSpectrum (𝓞 K))} {E : WeierstrassCurve ℚ} [E.IsElliptic]
  [HasFullTwoTorsion K S (E⁄K)]
  {αStage : ∀ i : ℕ, GKS K S →* (Acoef i)ˣ} [∀ i, IsOpenKer (αStage i)]
  {Cn : ActualConj K S} {hW : (E⁄K).map (Cn.κ : K →+* K) = E⁄K}
  {U : Ultrafilter ℕ} {hU : (U : Filter ℕ) ≤ cofinite}
  {P : Ideal Lambda} [P.IsPrime] {e : AlgebraicClosure K ≃ₐ[ℚ] Qbar}
  {χ : GKS K S →* Lambdaˣ} [IsContChar χ]
  {F : Type} [Field F] {ι : Localization.AtPrime P →+* F} {u : F}

/-- Kind: remaining-input structure. One original arithmetic request and
its produced detecting label, integral side models and coordinate step.
The specified family stages are retained; equalities of local-condition
tags and literal side-column comparisons are not required;
tex L4391–4451, L4809–4830, L5027–5114. -/
structure ReachableSwitchRemainingIso (A : FibreAtlas S U hU P)
    (B : FamilyFrame A ι u) (c : A.Config) where
  /-- Kind: arithmetic input. The original retained assembly request;
  tex L4385–4451, L5035–5071. -/
  retention : RetentionRequest (E := E) αStage
  /-- Kind: arithmetic and cochain input. Detection is produced on this
  same retained global fibre; tex L4768–4830, L5087–5114. -/
  detection : DetectionRemaining retention Cn hW U hU P e χ
  /-- Kind: integral-model and coordinate input. Both side models have the
  prescribed old and next stages at the produced derivative label;
  tex L4391–4451, L5027–5086. -/
  step : StepRemainingInputs detection ι (B.stage c)
    (B.stage (A.next c (A.primeOfLabel detection.label)))

/-- Kind: remaining-input structure. Original family and starting data,
with the weakened per-switch arithmetic request. No regularity conclusion,
terminal configuration, dimension-drop conclusion, retained duality,
detection determinant or side cohomology equivalence is an input field;
tex L4385–4451, L4976–5195. -/
structure RemainingInputsIso
    (αStage : ∀ i : ℕ, GKS K S →* (Acoef i)ˣ) [∀ i, IsOpenKer (αStage i)]
    (Cn : ActualConj K S) (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar)
    (χ : GKS K S →* Lambdaˣ) [IsContChar χ]
    (P : Ideal Lambda) [P.IsPrime] {F : Type} [Field F]
    (ι : Localization.AtPrime P →+* F) (u : F) where
  /-- Kind: coefficient hypothesis. Conjugation preserves the rational
  curve over the number field; tex L2798–2805, L5027–5032. -/
  hW : (E⁄K).map (Cn.κ : K →+* K) = E⁄K
  /-- Kind: data. The common inner-limit ultrafilter; tex L4391–4451. -/
  U : Ultrafilter ℕ
  /-- Kind: hypothesis. Precision tends to infinity;
  tex L4391–4451, L5030–5032. -/
  hU : (U : Filter ℕ) ≤ cofinite
  /-- Kind: original coefficient data. The prescribed cochain family;
  tex L4391–4451, L4976–5086. -/
  atlas : FibreAtlas S U hU P
  /-- Kind: starting and model input. The unchanged family models,
  starting identifications, nonquadraticity and primitivity;
  tex L4976–5003, L5072–5195. -/
  frame : FamilyFrame atlas ι u
  /-- Kind: per-switch arithmetic input. An original arithmetic request at
  every required reachable configuration; tex L4391–4451, L5027–5114. -/
  switch : ∀ c : atlas.Config, Reach atlas.next atlas.actual c →
    1 < (frame.stage c).fiberDim (resAt P) →
    ReachableSwitchRemainingIso (αStage := αStage) (Cn := Cn) (hW := hW)
      (e := e) (χ := χ) atlas frame c

/-- Kind: constructed weakened switching inputs. The same original
retained-step producer supplies duality, residues, detection and both
side-to-stage cohomology equivalences. No side-to-family Selmer-data
identity is proved or assumed; tex L4385–4451, L4976–5195, L5027–5114. -/
def RemainingInputsIso.toInnerLimitSwitchInputsIso
    (X : RemainingInputsIso (E := E) αStage Cn e χ P ι u) :
    InnerLimitSwitchInputsIso P X.atlas.family ι u where
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
    exact ⟨p, ⟨T.step.coordinate⟩, ⟨T.step.toStepData⟩⟩

/-- Kind: proved sufficiency theorem. The adapted arithmetic assembly has
the same conditional local regularity conclusion;
tex L4976–5195. -/
theorem RemainingInputsIso.regular
    (X : RemainingInputsIso (E := E) αStage Cn e χ P ι u)
    (hι : Function.Injective ι) : ∃ a, ι a = u :=
  regular_of_innerLimitSwitchInputsIso hι X.toInnerLimitSwitchInputsIso

/-- Kind: constructed compatibility map. An original per-switch request
supplies the weakened request by retaining its arithmetic and integral
models, while forgetting its source comparisons and local-condition tag
equalities; tex L4391–4451, L5027–5114. -/
def ofReachableSwitchRemaining {A : FibreAtlas S U hU P} {B : FamilyFrame A ι u}
    {c : A.Config}
    (X : ReachableSwitchRemaining (αStage := αStage) (Cn := Cn) (hW := hW)
      (e := e) (χ := χ) A B c) :
    ReachableSwitchRemainingIso (αStage := αStage) (Cn := Cn) (hW := hW)
      (e := e) (χ := χ) A B c where
  retention := X.retention
  detection := X.detection
  step := X.step

/-- Kind: constructed compatibility map. Original remaining inputs give
the adapted remaining inputs without changing any retained arithmetic
request, family model or selected prime; tex L4385–4451, L4976–5195. -/
def ofRemainingInputs (X : RemainingInputs (E := E) αStage Cn e χ P ι u) :
    RemainingInputsIso (E := E) αStage Cn e χ P ι u where
  hW := X.hW
  U := X.U
  hU := X.hU
  atlas := X.atlas
  frame := X.frame
  switch c hc h1 := ofReachableSwitchRemaining (X.switch c hc h1)

end ArithmeticSetting

end ZInQ.Contrib.RC53Assist.SwitchInterface

namespace ZInQ.Contrib.RC53Assist.SwitchWiring

open Filter NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.UniformSwitch
open ZInQ.Contrib.RC53Assist.SwitchInterface
open ZInQ.Manuscript.RC.SelmerComplex (GKS)
open ZInQ.Manuscript.RC.CoefModules (ActualConj IsOpenKer)
open ZInQ.Manuscript.RC.LambdaCoef (HasFullTwoTorsion IsContChar)
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Manuscript.RC.PrintsArith (Qbar)
open ZInQ.Manuscript.RC.Uniform (Lambda)
open scoped WeierstrassCurve

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
  {S : Set (HeightOneSpectrum (𝓞 K))} {E : WeierstrassCurve ℚ} [E.IsElliptic]
  [HasFullTwoTorsion K S (E⁄K)]
  {αStage : ∀ i : ℕ, GKS K S →* (Acoef i)ˣ} [∀ i, IsOpenKer (αStage i)]
  {Cn : ActualConj K S} {e : AlgebraicClosure K ≃ₐ[ℚ] Qbar}
  {χ : GKS K S →* Lambdaˣ} [IsContChar χ] {P : Ideal Lambda} [P.IsPrime]
  {F : Type} [Field F] {ι : Localization.AtPrime P →+* F} {u : F}

/-- Kind: adapted assembly map. The original remaining-input type also
produces the weakened interface. For nonterminal singular successors use
`RemainingInputsIso`, which does not impose the original literal-condition
comparisons; tex L4385–4451, L4976–5195, L5027–5114. -/
def RemainingInputs.toInnerLimitSwitchInputsIso
    (X : RemainingInputs (E := E) αStage Cn e χ P ι u) :
    InnerLimitSwitchInputsIso P X.atlas.family ι u :=
  (ofRemainingInputs X).toInnerLimitSwitchInputsIso

/-- Kind: proved sufficiency theorem. The original arithmetic request
passes through the adapted interface to the unchanged regularity
conclusion; tex L4976–5195. -/
theorem RemainingInputs.regularIso (X : RemainingInputs (E := E) αStage Cn e χ P ι u)
    (hι : Function.Injective ι) : ∃ a, ι a = u :=
  regular_of_innerLimitSwitchInputsIso hι X.toInnerLimitSwitchInputsIso

end ZInQ.Contrib.RC53Assist.SwitchWiring
