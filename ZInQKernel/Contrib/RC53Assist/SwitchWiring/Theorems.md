# Exact theorem statements and axiom reports

The statements below are the fully quantified Lean output with
proof arguments and universe parameters displayed. Axiom reports are
copied verbatim from the successful single-file audit.

## ghom_heq

```lean
@ZInQ.Contrib.RC53Assist.SwitchWiring.ghom_heq : ∀ {k : Type} [inst : Field.{0} k]
  {C C' D D' : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.{0} k},
  Eq.{2} C C' →
    Eq.{2} D D' →
      ∀ {f : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0} C D}
        {g : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0} C' D'},
        HEq.{1} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.f.{0} f)
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.f.{0} g) →
          HEq.{1} f g
```

```text
'ZInQ.Contrib.RC53Assist.SwitchWiring.ghom_heq' depends on axioms: [propext, Quot.sound.{u}]
```

## DiagramColumns.data_eq

```lean
@ZInQ.Contrib.RC53Assist.SwitchWiring.DiagramColumns.data_eq : ∀ {U : Ultrafilter.{0} ℕ}
  (hU : LE.le.{0} (↑U) Filter.cofinite.{0}) (P : Ideal.{0} ZInQ.Manuscript.RC.Uniform.Lambda)
  [inst : Ideal.IsPrime.{0} P]
  {C M : ZInQ.Contrib.RC53Assist.InnerLimit.ComplexStages ZInQ.Manuscript.RC.Limits.stageIdeal U}
  {rC :
    ZInQ.Contrib.RC53Assist.InnerLimit.MapStages C
      (ZInQ.Contrib.RC53Assist.InnerLimitMoving.fullLocalStages ZInQ.Manuscript.RC.Limits.stageIdeal U)}
  {rM :
    ZInQ.Contrib.RC53Assist.InnerLimit.MapStages M
      (ZInQ.Contrib.RC53Assist.InnerLimitMoving.fullLocalStages ZInQ.Manuscript.RC.Limits.stageIdeal U)},
  ZInQ.Contrib.RC53Assist.SwitchWiring.DiagramColumns C M rC rM →
    ∀ (s : ZInQ.Contrib.RC53Assist.InnerLimitMoving.ConditionKind),
      Eq.{2}
        (ZInQ.Contrib.RC53Assist.InnerLimitMoving.derivativeSideData ZInQ.Manuscript.RC.Limits.stageIdeal_tendsToZero hU
          (Algebra.algebraMap.{0, 0} ZInQ.Manuscript.RC.Uniform.Lambda (ZInQ.Manuscript.RC.Wiring.ResAt P)) C rC s)
        (ZInQ.Contrib.RC53Assist.InnerLimitMoving.derivativeSideData ZInQ.Manuscript.RC.Limits.stageIdeal_tendsToZero hU
          (Algebra.algebraMap.{0, 0} ZInQ.Manuscript.RC.Uniform.Lambda (ZInQ.Manuscript.RC.Wiring.ResAt P)) M rM s)
```

```text
'ZInQ.Contrib.RC53Assist.SwitchWiring.DiagramColumns.data_eq' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## finite_side_data

```lean
@ZInQ.Contrib.RC53Assist.SwitchWiring.finite_side_data : ∀ {U : Ultrafilter.{0} ℕ}
  (hU : LE.le.{0} (↑U) Filter.cofinite.{0}) (P : Ideal.{0} ZInQ.Manuscript.RC.Uniform.Lambda)
  [inst : Ideal.IsPrime.{0} P]
  (C : ZInQ.Contrib.RC53Assist.InnerLimit.ComplexStages ZInQ.Manuscript.RC.Limits.stageIdeal U)
  (D : ZInQ.Manuscript.RC.FibreDuality.RetainedLimitPairingStages U C),
  Eq.{2}
    (ZInQ.Contrib.RC53Assist.InnerLimit.finiteLimitSide (ZInQ.Contrib.RC53Assist.InnerLimit.fibreLimitGlobal U hU P C)
        (ZInQ.Manuscript.RC.FibreDuality.RetainedLimitPairingStages.resLimit hU D P)).Dside
    (ZInQ.Contrib.RC53Assist.SwitchWiring.retainedFibreData hU P C D
      ZInQ.Contrib.RC53Assist.InnerLimitMoving.ConditionKind.finite)
```

```text
'ZInQ.Contrib.RC53Assist.SwitchWiring.finite_side_data' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## singular_side_data

```lean
@ZInQ.Contrib.RC53Assist.SwitchWiring.singular_side_data : ∀ {U : Ultrafilter.{0} ℕ}
  (hU : LE.le.{0} (↑U) Filter.cofinite.{0}) (P : Ideal.{0} ZInQ.Manuscript.RC.Uniform.Lambda)
  [inst : Ideal.IsPrime.{0} P]
  (C : ZInQ.Contrib.RC53Assist.InnerLimit.ComplexStages ZInQ.Manuscript.RC.Limits.stageIdeal U)
  (D : ZInQ.Manuscript.RC.FibreDuality.RetainedLimitPairingStages U C),
  Eq.{2}
    (ZInQ.Contrib.RC53Assist.InnerLimit.singularLimitSide (ZInQ.Contrib.RC53Assist.InnerLimit.fibreLimitGlobal U hU P C)
        (ZInQ.Manuscript.RC.FibreDuality.RetainedLimitPairingStages.resLimit hU D P)).Dside
    (ZInQ.Contrib.RC53Assist.SwitchWiring.retainedFibreData hU P C D
      ZInQ.Contrib.RC53Assist.InnerLimitMoving.ConditionKind.singular)
```

```text
'ZInQ.Contrib.RC53Assist.SwitchWiring.singular_side_data' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## step_finite_side_data

```lean
@ZInQ.Contrib.RC53Assist.SwitchWiring.step_finite_side_data : ∀ {P : Ideal.{0} ZInQ.Manuscript.RC.Uniform.Lambda}
  [inst : Ideal.IsPrime.{0} P] {F : Type} [inst_1 : Field.{0} F] {ι : RingHom.{0, 0} (Localization.AtPrime.{0} P) F}
  {S₀ S₁ : ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.{0, 0} ι}
  (X : ZInQ.Contrib.CloudB3RC53.SwitchInputs.InnerLimitStepData P S₀ S₁),
  Eq.{2} X.toStep.SF.Dside
    (ZInQ.Contrib.RC53Assist.SwitchWiring.retainedFibreData X.hU P X.C X.D
      ZInQ.Contrib.RC53Assist.InnerLimitMoving.ConditionKind.finite)
```

```text
'ZInQ.Contrib.RC53Assist.SwitchWiring.step_finite_side_data' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## step_singular_side_data

```lean
@ZInQ.Contrib.RC53Assist.SwitchWiring.step_singular_side_data : ∀ {P : Ideal.{0} ZInQ.Manuscript.RC.Uniform.Lambda}
  [inst : Ideal.IsPrime.{0} P] {F : Type} [inst_1 : Field.{0} F] {ι : RingHom.{0, 0} (Localization.AtPrime.{0} P) F}
  {S₀ S₁ : ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.{0, 0} ι}
  (X : ZInQ.Contrib.CloudB3RC53.SwitchInputs.InnerLimitStepData P S₀ S₁),
  Eq.{2} X.toStep.SS.Dside
    (ZInQ.Contrib.RC53Assist.SwitchWiring.retainedFibreData X.hU P X.C X.D
      ZInQ.Contrib.RC53Assist.InnerLimitMoving.ConditionKind.singular)
```

```text
'ZInQ.Contrib.RC53Assist.SwitchWiring.step_singular_side_data' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## DetectionRemaining.hdet

```lean
@ZInQ.Contrib.RC53Assist.SwitchWiring.DetectionRemaining.hdet : ∀ {K : Type} [inst : Field.{0} K]
  [inst_1 : NumberField.{0} K] [inst_2 : NumberField.IsTotallyComplex.{0} K]
  {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {E : WeierstrassCurve.{0} ℚ}
  [inst_3 : WeierstrassCurve.IsElliptic.{0} E]
  [inst_4 : ZInQ.Manuscript.RC.LambdaCoef.HasFullTwoTorsion K S (WeierstrassCurve.baseChange.{0, 0} E K)]
  {αStage :
    (i : ℕ) →
      MonoidHom.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S)
        (Units.{0} (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i))}
  [inst_5 : ∀ (i : ℕ), ZInQ.Manuscript.RC.CoefModules.IsOpenKer (αStage i)]
  {T : ZInQ.Contrib.RC53Assist.SwitchWiring.RetentionRequest αStage}
  {Cn : ZInQ.Manuscript.RC.CoefModules.ActualConj K S}
  {hW :
    Eq.{1} (WeierstrassCurve.map.{0, 0} (WeierstrassCurve.baseChange.{0, 0} E K) ↑Cn.κ)
      (WeierstrassCurve.baseChange.{0, 0} E K)}
  {U : Ultrafilter.{0} ℕ} {hU : LE.le.{0} (↑U) Filter.cofinite.{0}} {P : Ideal.{0} ZInQ.Manuscript.RC.Uniform.Lambda}
  [inst_6 : Ideal.IsPrime.{0} P] {e : AlgEquiv.{0, 0, 0} ℚ (AlgebraicClosure.{0} K) ZInQ.Manuscript.RC.PrintsArith.Qbar}
  {χ : MonoidHom.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (Units.{0} ZInQ.Manuscript.RC.Uniform.Lambda)}
  [inst_7 : ZInQ.Manuscript.RC.LambdaCoef.IsContChar χ]
  (A : ZInQ.Contrib.RC53Assist.SwitchWiring.DetectionRemaining T Cn hW U hU P e χ)
  (columns :
    ZInQ.Contrib.RC53Assist.StageStepDetection.RetainedEvaluationColumns hU P (T.result Cn hW U hU).D A.evaluation
      A.label),
  LE.le.{0}
    (ZInQ.Manuscript.RC.Uniform.finPlane.{0, 0, 0} (ZInQ.Manuscript.RC.Wiring.ResAt P)
      (ZInQ.Contrib.RC53Assist.InnerLimit.Vec2 (ZInQ.Manuscript.RC.Wiring.ResAt P))
      (ZInQ.Contrib.RC53Assist.InnerLimit.Vec2 (ZInQ.Manuscript.RC.Wiring.ResAt P)))
    (ZInQ.Contrib.RC53Assist.InnerLimit.limitRelaxed (T.global Cn hW U hU P)
        (ZInQ.Manuscript.RC.FibreDuality.RetainedLimitPairingStages.resLimit hU (T.result Cn hW U hU).D P)).U
```

```text
'ZInQ.Contrib.RC53Assist.SwitchWiring.DetectionRemaining.hdet' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## StepRemainingInputs.certificate

```lean
@ZInQ.Contrib.RC53Assist.SwitchWiring.StepRemainingInputs.certificate : ∀ {K : Type} [inst : Field.{0} K]
  [inst_1 : NumberField.{0} K] [inst_2 : NumberField.IsTotallyComplex.{0} K]
  {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {E : WeierstrassCurve.{0} ℚ}
  [inst_3 : WeierstrassCurve.IsElliptic.{0} E]
  [inst_4 : ZInQ.Manuscript.RC.LambdaCoef.HasFullTwoTorsion K S (WeierstrassCurve.baseChange.{0, 0} E K)]
  {αStage :
    (i : ℕ) →
      MonoidHom.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S)
        (Units.{0} (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i))}
  [inst_5 : ∀ (i : ℕ), ZInQ.Manuscript.RC.CoefModules.IsOpenKer (αStage i)]
  {T : ZInQ.Contrib.RC53Assist.SwitchWiring.RetentionRequest αStage}
  {Cn : ZInQ.Manuscript.RC.CoefModules.ActualConj K S}
  {hW :
    Eq.{1} (WeierstrassCurve.map.{0, 0} (WeierstrassCurve.baseChange.{0, 0} E K) ↑Cn.κ)
      (WeierstrassCurve.baseChange.{0, 0} E K)}
  {U : Ultrafilter.{0} ℕ} {hU : LE.le.{0} (↑U) Filter.cofinite.{0}} {P : Ideal.{0} ZInQ.Manuscript.RC.Uniform.Lambda}
  [inst_6 : Ideal.IsPrime.{0} P] {e : AlgEquiv.{0, 0, 0} ℚ (AlgebraicClosure.{0} K) ZInQ.Manuscript.RC.PrintsArith.Qbar}
  {χ : MonoidHom.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (Units.{0} ZInQ.Manuscript.RC.Uniform.Lambda)}
  [inst_7 : ZInQ.Manuscript.RC.LambdaCoef.IsContChar χ]
  {A : ZInQ.Contrib.RC53Assist.SwitchWiring.DetectionRemaining T Cn hW U hU P e χ} {F : Type} [inst_8 : Field.{0} F]
  {ι : RingHom.{0, 0} (Localization.AtPrime.{0} P) F}
  {S₀ S₁ : ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.{0, 0} ι}
  (X : ZInQ.Contrib.RC53Assist.SwitchWiring.StepRemainingInputs A ι S₀ S₁),
  ZInQ.Contrib.RC53Assist.InnerLimit.FibreInnerLimitPairingCertificate U hU P (T.result Cn hW U hU).C
    (ZInQ.Manuscript.RC.FibreDuality.RetainedLimitPairingStages.resLimit hU (T.result Cn hW U hU).D P)
    (X.localArithmetic.εAt P) 1 (X.localArithmetic.JAt P)
```

```text
'ZInQ.Contrib.RC53Assist.SwitchWiring.StepRemainingInputs.certificate' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## StepRemainingInputs.retained_C

```lean
@ZInQ.Contrib.RC53Assist.SwitchWiring.StepRemainingInputs.retained_C : ∀ {K : Type} [inst : Field.{0} K]
  [inst_1 : NumberField.{0} K] [inst_2 : NumberField.IsTotallyComplex.{0} K]
  {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {E : WeierstrassCurve.{0} ℚ}
  [inst_3 : WeierstrassCurve.IsElliptic.{0} E]
  [inst_4 : ZInQ.Manuscript.RC.LambdaCoef.HasFullTwoTorsion K S (WeierstrassCurve.baseChange.{0, 0} E K)]
  {αStage :
    (i : ℕ) →
      MonoidHom.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S)
        (Units.{0} (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i))}
  [inst_5 : ∀ (i : ℕ), ZInQ.Manuscript.RC.CoefModules.IsOpenKer (αStage i)]
  {T : ZInQ.Contrib.RC53Assist.SwitchWiring.RetentionRequest αStage}
  {Cn : ZInQ.Manuscript.RC.CoefModules.ActualConj K S}
  {hW :
    Eq.{1} (WeierstrassCurve.map.{0, 0} (WeierstrassCurve.baseChange.{0, 0} E K) ↑Cn.κ)
      (WeierstrassCurve.baseChange.{0, 0} E K)}
  {U : Ultrafilter.{0} ℕ} {hU : LE.le.{0} (↑U) Filter.cofinite.{0}} {P : Ideal.{0} ZInQ.Manuscript.RC.Uniform.Lambda}
  [inst_6 : Ideal.IsPrime.{0} P] {e : AlgEquiv.{0, 0, 0} ℚ (AlgebraicClosure.{0} K) ZInQ.Manuscript.RC.PrintsArith.Qbar}
  {χ : MonoidHom.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (Units.{0} ZInQ.Manuscript.RC.Uniform.Lambda)}
  [inst_7 : ZInQ.Manuscript.RC.LambdaCoef.IsContChar χ]
  {A : ZInQ.Contrib.RC53Assist.SwitchWiring.DetectionRemaining T Cn hW U hU P e χ} {F : Type} [inst_8 : Field.{0} F]
  {ι : RingHom.{0, 0} (Localization.AtPrime.{0} P) F}
  {S₀ S₁ : ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.{0, 0} ι}
  (X : ZInQ.Contrib.RC53Assist.SwitchWiring.StepRemainingInputs A ι S₀ S₁),
  Eq.{1} X.toStepData.C (T.result Cn hW U hU).C
```

```text
'ZInQ.Contrib.RC53Assist.SwitchWiring.StepRemainingInputs.retained_C' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## StepRemainingInputs.retained_D

```lean
@ZInQ.Contrib.RC53Assist.SwitchWiring.StepRemainingInputs.retained_D : ∀ {K : Type} [inst : Field.{0} K]
  [inst_1 : NumberField.{0} K] [inst_2 : NumberField.IsTotallyComplex.{0} K]
  {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {E : WeierstrassCurve.{0} ℚ}
  [inst_3 : WeierstrassCurve.IsElliptic.{0} E]
  [inst_4 : ZInQ.Manuscript.RC.LambdaCoef.HasFullTwoTorsion K S (WeierstrassCurve.baseChange.{0, 0} E K)]
  {αStage :
    (i : ℕ) →
      MonoidHom.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S)
        (Units.{0} (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i))}
  [inst_5 : ∀ (i : ℕ), ZInQ.Manuscript.RC.CoefModules.IsOpenKer (αStage i)]
  {T : ZInQ.Contrib.RC53Assist.SwitchWiring.RetentionRequest αStage}
  {Cn : ZInQ.Manuscript.RC.CoefModules.ActualConj K S}
  {hW :
    Eq.{1} (WeierstrassCurve.map.{0, 0} (WeierstrassCurve.baseChange.{0, 0} E K) ↑Cn.κ)
      (WeierstrassCurve.baseChange.{0, 0} E K)}
  {U : Ultrafilter.{0} ℕ} {hU : LE.le.{0} (↑U) Filter.cofinite.{0}} {P : Ideal.{0} ZInQ.Manuscript.RC.Uniform.Lambda}
  [inst_6 : Ideal.IsPrime.{0} P] {e : AlgEquiv.{0, 0, 0} ℚ (AlgebraicClosure.{0} K) ZInQ.Manuscript.RC.PrintsArith.Qbar}
  {χ : MonoidHom.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (Units.{0} ZInQ.Manuscript.RC.Uniform.Lambda)}
  [inst_7 : ZInQ.Manuscript.RC.LambdaCoef.IsContChar χ]
  {A : ZInQ.Contrib.RC53Assist.SwitchWiring.DetectionRemaining T Cn hW U hU P e χ} {F : Type} [inst_8 : Field.{0} F]
  {ι : RingHom.{0, 0} (Localization.AtPrime.{0} P) F}
  {S₀ S₁ : ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.{0, 0} ι}
  (X : ZInQ.Contrib.RC53Assist.SwitchWiring.StepRemainingInputs A ι S₀ S₁),
  Eq.{1} X.toStepData.D (T.result Cn hW U hU).D
```

```text
'ZInQ.Contrib.RC53Assist.SwitchWiring.StepRemainingInputs.retained_D' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## StepRemainingInputs.retained_E

```lean
@ZInQ.Contrib.RC53Assist.SwitchWiring.StepRemainingInputs.retained_E : ∀ {K : Type} [inst : Field.{0} K]
  [inst_1 : NumberField.{0} K] [inst_2 : NumberField.IsTotallyComplex.{0} K]
  {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {E : WeierstrassCurve.{0} ℚ}
  [inst_3 : WeierstrassCurve.IsElliptic.{0} E]
  [inst_4 : ZInQ.Manuscript.RC.LambdaCoef.HasFullTwoTorsion K S (WeierstrassCurve.baseChange.{0, 0} E K)]
  {αStage :
    (i : ℕ) →
      MonoidHom.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S)
        (Units.{0} (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i))}
  [inst_5 : ∀ (i : ℕ), ZInQ.Manuscript.RC.CoefModules.IsOpenKer (αStage i)]
  {T : ZInQ.Contrib.RC53Assist.SwitchWiring.RetentionRequest αStage}
  {Cn : ZInQ.Manuscript.RC.CoefModules.ActualConj K S}
  {hW :
    Eq.{1} (WeierstrassCurve.map.{0, 0} (WeierstrassCurve.baseChange.{0, 0} E K) ↑Cn.κ)
      (WeierstrassCurve.baseChange.{0, 0} E K)}
  {U : Ultrafilter.{0} ℕ} {hU : LE.le.{0} (↑U) Filter.cofinite.{0}} {P : Ideal.{0} ZInQ.Manuscript.RC.Uniform.Lambda}
  [inst_6 : Ideal.IsPrime.{0} P] {e : AlgEquiv.{0, 0, 0} ℚ (AlgebraicClosure.{0} K) ZInQ.Manuscript.RC.PrintsArith.Qbar}
  {χ : MonoidHom.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (Units.{0} ZInQ.Manuscript.RC.Uniform.Lambda)}
  [inst_7 : ZInQ.Manuscript.RC.LambdaCoef.IsContChar χ]
  {A : ZInQ.Contrib.RC53Assist.SwitchWiring.DetectionRemaining T Cn hW U hU P e χ} {F : Type} [inst_8 : Field.{0} F]
  {ι : RingHom.{0, 0} (Localization.AtPrime.{0} P) F}
  {S₀ S₁ : ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.{0, 0} ι}
  (X : ZInQ.Contrib.RC53Assist.SwitchWiring.StepRemainingInputs A ι S₀ S₁),
  Eq.{1} X.toStepData.E (T.result Cn hW U hU).E
```

```text
'ZInQ.Contrib.RC53Assist.SwitchWiring.StepRemainingInputs.retained_E' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## RemainingInputs.regular

```lean
@ZInQ.Contrib.RC53Assist.SwitchWiring.RemainingInputs.regular : ∀ {K : Type} [inst : Field.{0} K]
  [inst_1 : NumberField.{0} K] [inst_2 : NumberField.IsTotallyComplex.{0} K]
  {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {E : WeierstrassCurve.{0} ℚ}
  [inst_3 : WeierstrassCurve.IsElliptic.{0} E]
  [inst_4 : ZInQ.Manuscript.RC.LambdaCoef.HasFullTwoTorsion K S (WeierstrassCurve.baseChange.{0, 0} E K)]
  {αStage :
    (i : ℕ) →
      MonoidHom.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S)
        (Units.{0} (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i))}
  [inst_5 : ∀ (i : ℕ), ZInQ.Manuscript.RC.CoefModules.IsOpenKer (αStage i)]
  {Cn : ZInQ.Manuscript.RC.CoefModules.ActualConj K S} {P : Ideal.{0} ZInQ.Manuscript.RC.Uniform.Lambda}
  [inst_6 : Ideal.IsPrime.{0} P] {e : AlgEquiv.{0, 0, 0} ℚ (AlgebraicClosure.{0} K) ZInQ.Manuscript.RC.PrintsArith.Qbar}
  {χ : MonoidHom.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (Units.{0} ZInQ.Manuscript.RC.Uniform.Lambda)}
  [inst_7 : ZInQ.Manuscript.RC.LambdaCoef.IsContChar χ] {F : Type} [inst_8 : Field.{0} F]
  {ι : RingHom.{0, 0} (Localization.AtPrime.{0} P) F} {u : F}
  (X : ZInQ.Contrib.RC53Assist.SwitchWiring.RemainingInputs αStage Cn e χ P ι u),
  Function.Injective.{1, 1} ⇑ι → ∃ a, Eq.{1} (ι a) u
```

```text
'ZInQ.Contrib.RC53Assist.SwitchWiring.RemainingInputs.regular' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## fixedLocalRange

```lean
@ZInQ.Contrib.RC53Assist.SwitchWiring.fixedLocalRange : ∀ {k : Type} [inst : Field.{0} k]
  {G G' U U' L : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.{0} k}
  {r : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0} G L}
  {r' : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0} G' L}
  {i : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0} U L}
  {i' : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0} U' L},
  Eq.{2} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData.mk.{0} G U L r i)
      (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData.mk.{0} G' U' L r' i') →
    Eq.{1} (LinearMap.range.{0, 0, 0, 0} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.f.{0} i 1 1 rfl.{1}))
      (LinearMap.range.{0, 0, 0, 0} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.f.{0} i' 1 1 rfl.{1}))
```

```text
'ZInQ.Contrib.RC53Assist.SwitchWiring.fixedLocalRange' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## finite_singular_ne

```lean
@ZInQ.Contrib.RC53Assist.SwitchWiring.finite_singular_ne : ∀ {k : Type} [inst : Field.{0} k]
  {G G' : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.{0} k}
  (r : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0} G (ZInQ.Contrib.RC53Assist.InnerLimit.splitLocalComplex k))
  (r' : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0} G' (ZInQ.Contrib.RC53Assist.InnerLimit.splitLocalComplex k)),
  Ne.{2} (ZInQ.Contrib.RC53Assist.InnerLimit.finiteLimitSide G r).Dside
    (ZInQ.Contrib.RC53Assist.InnerLimit.singularLimitSide G' r').Dside
```

```text
'ZInQ.Contrib.RC53Assist.SwitchWiring.finite_singular_ne' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## successor_dimension_le_one

```lean
@ZInQ.Contrib.RC53Assist.SwitchWiring.successor_dimension_le_one : ∀ {P : Ideal.{0} ZInQ.Manuscript.RC.Uniform.Lambda}
  [inst : Ideal.IsPrime.{0} P] {F : Type} [inst_1 : Field.{0} F] {ι : RingHom.{0, 0} (Localization.AtPrime.{0} P) F}
  {u : F}
  {Φ :
    ZInQ.Contrib.CloudB3RC53.SwitchInputs.SwitchFamily (ZInQ.Manuscript.RC.Wiring.ResAt P) (Localization.AtPrime.{0} P)}
  (X : ZInQ.Contrib.CloudB3RC53.SwitchInputs.InnerLimitSwitchInputs P Φ ι u) {c : Φ.Config} {p : Φ.Prime},
  ZInQ.Contrib.CloudB3RC53.SwitchInputs.Reach Φ.next Φ.actual c →
    ∀ (Y : ZInQ.Contrib.CloudB3RC53.SwitchInputs.InnerLimitStepData P (X.stage c) (X.stage (Φ.next c p))),
      Eq.{2} Y.toStep.SS.Dside (Φ.fibre (Φ.next c p)) →
        LE.le.{0}
          (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.fiberDim.{0, 0, 0} (ZInQ.Manuscript.RC.Wiring.resAt P)
            (X.stage (Φ.next c p)))
          1
```

```text
'ZInQ.Contrib.RC53Assist.SwitchWiring.successor_dimension_le_one' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## reachable_dimension_le_three

```lean
@ZInQ.Contrib.RC53Assist.SwitchWiring.reachable_dimension_le_three : ∀ {P : Ideal.{0} ZInQ.Manuscript.RC.Uniform.Lambda}
  [inst : Ideal.IsPrime.{0} P] {F : Type} [inst_1 : Field.{0} F] {ι : RingHom.{0, 0} (Localization.AtPrime.{0} P) F}
  {u : F}
  {Φ :
    ZInQ.Contrib.CloudB3RC53.SwitchInputs.SwitchFamily (ZInQ.Manuscript.RC.Wiring.ResAt P) (Localization.AtPrime.{0} P)}
  (X : ZInQ.Contrib.CloudB3RC53.SwitchInputs.InnerLimitSwitchInputs P Φ ι u) {c : Φ.Config},
  ZInQ.Contrib.CloudB3RC53.SwitchInputs.Reach Φ.next Φ.actual c →
    LE.le.{0}
      (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.fiberDim.{0, 0, 0} (ZInQ.Manuscript.RC.Wiring.resAt P)
        (X.stage c))
      3
```

```text
'ZInQ.Contrib.RC53Assist.SwitchWiring.reachable_dimension_le_three' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## no_inputs_of_large_actual_fibre

```lean
@ZInQ.Contrib.RC53Assist.SwitchWiring.no_inputs_of_large_actual_fibre : ∀
  {P : Ideal.{0} ZInQ.Manuscript.RC.Uniform.Lambda} [inst : Ideal.IsPrime.{0} P] {F : Type} [inst_1 : Field.{0} F]
  {ι : RingHom.{0, 0} (Localization.AtPrime.{0} P) F} {u : F}
  {Φ :
    ZInQ.Contrib.CloudB3RC53.SwitchInputs.SwitchFamily (ZInQ.Manuscript.RC.Wiring.ResAt P)
      (Localization.AtPrime.{0} P)},
  LT.lt.{0} 3
      (Module.finrank.{0, 0} (ZInQ.Manuscript.RC.Wiring.ResAt P)
        ↑(HomologicalComplex.homology.{0, 1, 0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.toCC.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} (Φ.fibre Φ.actual)))
            1)) →
    ¬Nonempty.{1} (ZInQ.Contrib.CloudB3RC53.SwitchInputs.InnerLimitSwitchInputs P Φ ι u)
```

```text
'ZInQ.Contrib.RC53Assist.SwitchWiring.no_inputs_of_large_actual_fibre' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```
