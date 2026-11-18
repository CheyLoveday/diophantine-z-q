# Registered declarations and axiom dependencies

These are the registered Lean types and the exact axiom-audit outputs for the verified source. All dependencies are contained in propext, Classical.choice and Quot.sound. No theorem below claims the integral cup/trace normalization or the final self-dual based comparison.

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.twoIdeal_pow

Source line: 35.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.twoIdeal_pow (a : ℕ) :
  Eq.{1} (HPow.hPow.{0, 0, 0} ZInQ.Contrib.RC53Assist.DerivedKummerActual.twoIdeal a)
    (Ideal.span.{0} (Singleton.singleton.{0, 0} ↑(HPow.hPow.{0, 0, 0} 2 a)))
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.twoIdeal_pow' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.twoIdeal_fg

Source line: 40.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.twoIdeal_fg :
  Ideal.FG.{0} ZInQ.Contrib.RC53Assist.DerivedKummerActual.twoIdeal
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.twoIdeal_fg' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.integerResidue_compatible

Source line: 52.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.integerResidue_compatible {m n : ℕ} (h : LE.le.{0} m n) :
  Eq.{1}
    (RingHom.comp.{0, 0, 0} (Ideal.Quotient.factorPow.{0} ZInQ.Contrib.RC53Assist.DerivedKummerActual.twoIdeal h)
      (ZInQ.Contrib.RC53Assist.DerivedKummerActual.integerResidue n))
    (ZInQ.Contrib.RC53Assist.DerivedKummerActual.integerResidue m)
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.integerResidue_compatible' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.mem_pointPowSub

Source line: 81.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.mem_pointPowSub.{u_1} (P : Type u_1) [AddCommGroup.{u_1} P] (a : ℕ)
  (x : P) :
  Membership.mem.{u_1, u_1} (ZInQ.Contrib.RC53Assist.DerivedKummerActual.pointPowSub.{u_1} P a) x ↔
    ∃ y, Eq.{u_1 + 1} (HSMul.hSMul.{0, u_1, u_1} (HPow.hPow.{0, 0, 0} 2 a) y) x
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.mem_pointPowSub' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.pointPowSub_toAddSubgroup

Source line: 88.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.pointPowSub_toAddSubgroup.{u_1} (P : Type u_1) [AddCommGroup.{u_1} P]
  (a : ℕ) :
  Eq.{u_1 + 1} (Submodule.toAddSubgroup.{0, u_1} (ZInQ.Contrib.RC53Assist.DerivedKummerActual.pointPowSub.{u_1} P a))
    (AddMonoidHom.range.{u_1, u_1} (nsmulAddMonoidHom.{u_1} (HPow.hPow.{0, 0, 0} 2 a)))
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.pointPowSub_toAddSubgroup' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.pointLevelEquiv_mk

Source line: 99.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.pointLevelEquiv_mk.{u_1} (P : Type u_1) [AddCommGroup.{u_1} P] (a : ℕ)
  (x : P) :
  Eq.{u_1 + 1}
    ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.pointLevelEquiv.{u_1} P a) (Submodule.Quotient.mk.{0, u_1} x)) ↑x
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.pointLevelEquiv_mk' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.completion_nSub_toAddSubgroup

Source line: 103.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.completion_nSub_toAddSubgroup.{u_1} (P : Type u_1) [AddCommGroup.{u_1} P]
  (a : ℕ) :
  Eq.{u_1 + 1}
    (Submodule.toAddSubgroup.{0, u_1}
      (ZInQ.Contrib.CloudB3RC53.Duality.nSub.{0, u_1} (HPow.hPow.{0, 0, 0} 2 a)
        (ZInQ.Contrib.RC53Assist.DerivedKummerActual.PointCompletion.{u_1} P)))
    (Submodule.toAddSubgroup.{0, u_1}
      (ZInQ.Contrib.RC53Assist.DerivedKummerActual.pointPowSub.{u_1}
        (ZInQ.Contrib.RC53Assist.DerivedKummerActual.PointCompletion.{u_1} P) a))
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.completion_nSub_toAddSubgroup' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.completion_eval_ker

Source line: 114.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.completion_eval_ker.{u_1} (P : Type u_1) [AddCommGroup.{u_1} P] (a : ℕ) :
  Eq.{u_1 + 1}
    (Submodule.toAddSubgroup.{0, u_1}
      (ZInQ.Contrib.CloudB3RC53.Duality.nSub.{0, u_1} (HPow.hPow.{0, 0, 0} 2 a)
        (ZInQ.Contrib.RC53Assist.DerivedKummerActual.PointCompletion.{u_1} P)))
    (AddMonoidHom.ker.{u_1, u_1}
      (LinearMap.toAddMonoidHom.{0, 0, u_1, u_1}
        (AdicCompletion.eval.{0, u_1} ZInQ.Contrib.RC53Assist.DerivedKummerActual.twoIdeal P a)))
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.completion_eval_ker' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.completionQuotientEquiv_mk

Source line: 130.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.completionQuotientEquiv_mk.{u_1} (P : Type u_1) [AddCommGroup.{u_1} P]
  (a : ℕ) (x : ZInQ.Contrib.RC53Assist.DerivedKummerActual.PointCompletion.{u_1} P) :
  Eq.{u_1 + 1}
    ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.completionQuotientEquiv.{u_1} P a) (Submodule.Quotient.mk.{0, u_1} x))
    ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.pointLevelEquiv.{u_1} P a) (↑x a))
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.completionQuotientEquiv_mk' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.completionQuotientEquiv_completePoint

Source line: 135.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.completionQuotientEquiv_completePoint.{u_1} (P : Type u_1)
  [AddCommGroup.{u_1} P] (a : ℕ) (x : P) :
  Eq.{u_1 + 1}
    ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.completionQuotientEquiv.{u_1} P a)
      (Submodule.Quotient.mk.{0, u_1} ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.completePoint.{u_1} P) x)))
    ↑x
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.completionQuotientEquiv_completePoint' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.etaOne_completePoint

Source line: 146.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.etaOne_completePoint {F : Type} [Field.{0} F] [DecidableEq.{1} F]
  (B : WeierstrassCurve.{0} F) (p : WeierstrassCurve.Affine.Point.{0} (WeierstrassCurve.toAffine.{0} B)) :
  Eq.{1}
    ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.etaOne B)
      (Submodule.Quotient.mk.{0, 0}
        ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.completePoint.{0}
            (WeierstrassCurve.Affine.Point.{0} (WeierstrassCurve.toAffine.{0} B)))
          p)))
    ↑p
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.etaOne_completePoint' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.twoPower_smul

Source line: 152.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.twoPower_smul.{u_1} (P : Type u_1) [AddCommGroup.{u_1} P]
  [Module.{0, u_1} ℤ_[2] P] (a : ℕ) (x : P) :
  Eq.{u_1 + 1} (HSMul.hSMul.{0, u_1, u_1} (HPow.hPow.{0, 0, 0} 2 a) x)
    (HSMul.hSMul.{0, u_1, u_1} (HPow.hPow.{0, 0, 0} 2 a) x)
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.twoPower_smul' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.point_torsion_mem_powSub_eq_zero

Source line: 158.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.point_torsion_mem_powSub_eq_zero.{u_1} (P : Type u_1) [AddCommGroup.{u_1} P]
  (e a : ℕ)
  (hbound :
    ∀ (k : ℕ) (x : P),
      Eq.{u_1 + 1} (HSMul.hSMul.{0, u_1, u_1} (HPow.hPow.{0, 0, 0} 2 k) x) 0 →
        Eq.{u_1 + 1} (HSMul.hSMul.{0, u_1, u_1} (HPow.hPow.{0, 0, 0} 2 e) x) 0)
  (x : P) (hx : Eq.{u_1 + 1} (HSMul.hSMul.{0, u_1, u_1} (HPow.hPow.{0, 0, 0} 2 a) x) 0)
  (hmem :
    Membership.mem.{u_1, u_1}
      (ZInQ.Contrib.RC53Assist.DerivedKummerActual.pointPowSub.{u_1} P (HAdd.hAdd.{0, 0, 0} e a)) x) :
  Eq.{u_1 + 1} x 0
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.point_torsion_mem_powSub_eq_zero' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.completion_torsion_detect

Source line: 168.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.completion_torsion_detect.{u_1} (P : Type u_1) [AddCommGroup.{u_1} P]
  (e a : ℕ)
  (hbound :
    ∀ (k : ℕ) (x : P),
      Eq.{u_1 + 1} (HSMul.hSMul.{0, u_1, u_1} (HPow.hPow.{0, 0, 0} 2 k) x) 0 →
        Eq.{u_1 + 1} (HSMul.hSMul.{0, u_1, u_1} (HPow.hPow.{0, 0, 0} 2 e) x) 0)
  (x : ZInQ.Contrib.RC53Assist.DerivedKummerActual.PointCompletion.{u_1} P)
  (hx : Eq.{u_1 + 1} (HSMul.hSMul.{0, u_1, u_1} (HPow.hPow.{0, 0, 0} 2 a) x) 0)
  (heval : Eq.{u_1 + 1} (↑x (HAdd.hAdd.{0, 0, 0} e a)) 0) : Eq.{u_1 + 1} x 0
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.completion_torsion_detect' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.torsionToCompletion_apply

Source line: 221.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.torsionToCompletion_apply.{u_1} (P : Type u_1) [AddCommGroup.{u_1} P]
  (a : ℕ) (t : ↥(AddSubgroup.torsionBy.{u_1} P ↑(HPow.hPow.{0, 0, 0} 2 a))) :
  Eq.{u_1 + 1} (↑((ZInQ.Contrib.RC53Assist.DerivedKummerActual.torsionToCompletion.{u_1} P a) t))
    ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.completePoint.{u_1} P) ↑t)
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.torsionToCompletion_apply' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.torsionToCompletion_injective

Source line: 226.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.torsionToCompletion_injective.{u_1} (P : Type u_1) [AddCommGroup.{u_1} P]
  (e a : ℕ)
  (hbound :
    ∀ (k : ℕ) (x : P),
      Eq.{u_1 + 1} (HSMul.hSMul.{0, u_1, u_1} (HPow.hPow.{0, 0, 0} 2 k) x) 0 →
        Eq.{u_1 + 1} (HSMul.hSMul.{0, u_1, u_1} (HPow.hPow.{0, 0, 0} 2 e) x) 0) :
  Function.Injective.{u_1 + 1, u_1 + 1} ⇑(ZInQ.Contrib.RC53Assist.DerivedKummerActual.torsionToCompletion.{u_1} P a)
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.torsionToCompletion_injective' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.torsionToCompletion_surjective

Source line: 243.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.torsionToCompletion_surjective.{u_1} (P : Type u_1) [AddCommGroup.{u_1} P]
  (e a : ℕ)
  (hbound :
    ∀ (k : ℕ) (x : P),
      Eq.{u_1 + 1} (HSMul.hSMul.{0, u_1, u_1} (HPow.hPow.{0, 0, 0} 2 k) x) 0 →
        Eq.{u_1 + 1} (HSMul.hSMul.{0, u_1, u_1} (HPow.hPow.{0, 0, 0} 2 e) x) 0) :
  Function.Surjective.{u_1 + 1, u_1 + 1} ⇑(ZInQ.Contrib.RC53Assist.DerivedKummerActual.torsionToCompletion.{u_1} P a)
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.torsionToCompletion_surjective' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.completionTorsionEquiv_symm_apply

Source line: 298.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.completionTorsionEquiv_symm_apply.{u_1} (P : Type u_1)
  [AddCommGroup.{u_1} P] (e a : ℕ)
  (hbound :
    ∀ (k : ℕ) (x : P),
      Eq.{u_1 + 1} (HSMul.hSMul.{0, u_1, u_1} (HPow.hPow.{0, 0, 0} 2 k) x) 0 →
        Eq.{u_1 + 1} (HSMul.hSMul.{0, u_1, u_1} (HPow.hPow.{0, 0, 0} 2 e) x) 0)
  (t : ↥(AddSubgroup.torsionBy.{u_1} P ↑(HPow.hPow.{0, 0, 0} 2 a))) :
  Eq.{u_1 + 1}
    ((AddEquiv.symm.{u_1, u_1} (ZInQ.Contrib.RC53Assist.DerivedKummerActual.completionTorsionEquiv.{u_1} P e a hbound))
      t)
    ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.torsionToCompletion.{u_1} P a) t)
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.completionTorsionEquiv_symm_apply' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.boundedTwoPrimary_of_finiteIndex

Source line: 304.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.boundedTwoPrimary_of_finiteIndex.{u_1} (P : Type u_1) [AddCommGroup.{u_1} P]
  (U : AddSubgroup.{u_1} P) [AddSubgroup.FiniteIndex.{u_1} U]
  (hU : ∀ (x : P), Membership.mem.{u_1, u_1} U x → Eq.{u_1 + 1} (HSMul.hSMul.{0, u_1, u_1} 2 x) 0 → Eq.{u_1 + 1} x 0) :
  ∃ e,
    ∀ (k : ℕ) (x : P),
      Eq.{u_1 + 1} (HSMul.hSMul.{0, u_1, u_1} (HPow.hPow.{0, 0, 0} 2 k) x) 0 →
        Eq.{u_1 + 1} (HSMul.hSMul.{0, u_1, u_1} (HPow.hPow.{0, 0, 0} 2 e) x) 0
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.boundedTwoPrimary_of_finiteIndex' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.boundedTwoPrimary_integral_local

Source line: 340.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.boundedTwoPrimary_integral_local (K : Type) [Field.{0} K]
  [NumberField.{0} K] (w : IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))
  [hdec : DecidableEq.{1} (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} K w)]
  (C : WeierstrassCurve.{0} ↥(IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.{0, 0} K w))
  [WeierstrassCurve.IsElliptic.{0}
      (WeierstrassCurve.baseChange.{0, 0} C (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} K w))] :
  ∃ e,
    ∀ (k : ℕ)
      (p :
        WeierstrassCurve.Affine.Point.{0}
          (WeierstrassCurve.toAffine.{0}
            (WeierstrassCurve.baseChange.{0, 0} C (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} K w)))),
      Eq.{1} (HSMul.hSMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} 2 k) p) 0 →
        Eq.{1} (HSMul.hSMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} 2 e) p) 0
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.boundedTwoPrimary_integral_local' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.boundedTwoPrimary_local

Source line: 369.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.boundedTwoPrimary_local (K : Type) [Field.{0} K] [NumberField.{0} K]
  (w : IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))
  [DecidableEq.{1} (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} K w)]
  (B : WeierstrassCurve.{0} (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} K w))
  [WeierstrassCurve.IsElliptic.{0} B] :
  ∃ e,
    ∀ (k : ℕ) (p : WeierstrassCurve.Affine.Point.{0} (WeierstrassCurve.toAffine.{0} B)),
      Eq.{1} (HSMul.hSMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} 2 k) p) 0 →
        Eq.{1} (HSMul.hSMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} 2 e) p) 0
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.boundedTwoPrimary_local' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.etaZero_symm_apply

Source line: 410.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.etaZero_symm_apply (K : Type) [Field.{0} K] [NumberField.{0} K]
  (w : IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))
  [DecidableEq.{1} (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} K w)]
  (B : WeierstrassCurve.{0} (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} K w))
  [WeierstrassCurve.IsElliptic.{0} B]
  (t : ↥(AddSubgroup.torsionBy.{0} (WeierstrassCurve.Affine.Point.{0} (WeierstrassCurve.toAffine.{0} B)) 2)) :
  Eq.{1} ((AddEquiv.symm.{0, 0} (ZInQ.Contrib.RC53Assist.DerivedKummerActual.etaZero K w B)) t)
    ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.torsionToCompletion.{0}
        (WeierstrassCurve.Affine.Point.{0} (WeierstrassCurve.toAffine.{0} B)) 1)
      t)
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.etaZero_symm_apply' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.etaZero_torsionToCompletion

Source line: 417.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.etaZero_torsionToCompletion (K : Type) [Field.{0} K] [NumberField.{0} K]
  (w : IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))
  [DecidableEq.{1} (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} K w)]
  (B : WeierstrassCurve.{0} (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} K w))
  [WeierstrassCurve.IsElliptic.{0} B]
  (t : ↥(AddSubgroup.torsionBy.{0} (WeierstrassCurve.Affine.Point.{0} (WeierstrassCurve.toAffine.{0} B)) 2)) :
  Eq.{1}
    ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.etaZero K w B)
      ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.torsionToCompletion.{0}
          (WeierstrassCurve.Affine.Point.{0} (WeierstrassCurve.toAffine.{0} B)) 1)
        t))
    t
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.etaZero_torsionToCompletion' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.completionTorsionToH0_torsionToCompletion

Source line: 433.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.completionTorsionToH0_torsionToCompletion (K : Type) [Field.{0} K]
  [NumberField.{0} K] (w : IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))
  [DecidableEq.{1} (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} K w)]
  (B : WeierstrassCurve.{0} (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} K w))
  [WeierstrassCurve.IsElliptic.{0} B]
  (t : ↥(AddSubgroup.torsionBy.{0} (WeierstrassCurve.Affine.Point.{0} (WeierstrassCurve.toAffine.{0} B)) 2)) :
  Eq.{1}
    (↑((ZInQ.Contrib.RC53Assist.DerivedKummerActual.completionTorsionToH0 K w B)
        ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.torsionToCompletion.{0}
            (WeierstrassCurve.Affine.Point.{0} (WeierstrassCurve.toAffine.{0} B)) 1)
          t)))
    ((WeierstrassCurve.baseTorsionCoeff.{0} B 2) t)
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.completionTorsionToH0_torsionToCompletion' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.pointCompletion_adicComplete

Source line: 457.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.pointCompletion_adicComplete.{u_1} (P : Type u_1) [AddCommGroup.{u_1} P] :
  IsAdicComplete.{0, u_1} ZInQ.Contrib.RC53Assist.DerivedKummerActual.scalarTwoIdeal
    (ZInQ.Contrib.RC53Assist.DerivedKummerActual.PointCompletion.{u_1} P)
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.pointCompletion_adicComplete' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.scalar_adicComplete

Source line: 467.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.scalar_adicComplete :
  IsAdicComplete.{0, 0} ZInQ.Contrib.RC53Assist.DerivedKummerActual.scalarTwoIdeal ℤ_[2]
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.scalar_adicComplete' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.scalarPi_precomplete

Source line: 472.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.scalarPi_precomplete (n : ℕ) :
  IsPrecomplete.{0, 0} ZInQ.Contrib.RC53Assist.DerivedKummerActual.scalarTwoIdeal (Fin n → ℤ_[2])
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.scalarPi_precomplete' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.scalarTwoIdeal_smul_top

Source line: 487.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.scalarTwoIdeal_smul_top.{u_1} (P : Type u_1) [AddCommGroup.{u_1} P]
  [Module.{0, u_1} ℤ_[2] P] :
  Eq.{u_1 + 1} (HSMul.hSMul.{0, u_1, u_1} ZInQ.Contrib.RC53Assist.DerivedKummerActual.scalarTwoIdeal Top.top.{u_1})
    (ZInQ.Contrib.CloudB3RC53.Duality.nSub.{0, u_1} 2 P)
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.scalarTwoIdeal_smul_top' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.pointCompletion_finite

Source line: 495.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.pointCompletion_finite.{u_1} (P : Type u_1) [AddCommGroup.{u_1} P]
  [Finite.{u_1 + 1} (ZInQ.Contrib.RC53Assist.DerivedKummer.TateDualityData.pointMod.{u_1} 2)] :
  Module.Finite.{0, u_1} ℤ_[2] (ZInQ.Contrib.RC53Assist.DerivedKummerActual.PointCompletion.{u_1} P)
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.pointCompletion_finite' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.finitePointPresentation_nonempty

Source line: 532.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.finitePointPresentation_nonempty.{u_1} (P : Type u_1) [AddCommGroup.{u_1} P]
  [Finite.{u_1 + 1} (ZInQ.Contrib.RC53Assist.DerivedKummer.TateDualityData.pointMod.{u_1} 2)] :
  Nonempty.{u_1 + 1} (ZInQ.Contrib.RC53Assist.DerivedKummerActual.FinitePointPresentation.{u_1} P)
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.finitePointPresentation_nonempty' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.finitePi_twoPower_regular

Source line: 554.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.finitePi_twoPower_regular (n a : ℕ) :
  IsSMulRegular.{0, 0} (Fin n → ℤ_[2]) (HPow.hPow.{0, 0, 0} 2 a)
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.finitePi_twoPower_regular' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.finite_submoduleTwoTorsion

Source line: 568.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.finite_submoduleTwoTorsion {F : Type} [Field.{0} F] [DecidableEq.{1} F]
  (B : WeierstrassCurve.{0} F) [WeierstrassCurve.IsElliptic.{0} B] :
  Finite.{1} ↥(Submodule.torsionBy.{0, 0} ℤ (WeierstrassCurve.Affine.Point.{0} (WeierstrassCurve.toAffine.{0} B)) 2)
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.finite_submoduleTwoTorsion' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.finite_pointModTwo_integral_local

Source line: 584.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.finite_pointModTwo_integral_local (K : Type) [Field.{0} K]
  [NumberField.{0} K] (w : IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))
  [hdec : DecidableEq.{1} (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} K w)]
  (C : WeierstrassCurve.{0} ↥(IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.{0, 0} K w))
  [WeierstrassCurve.IsElliptic.{0}
      (WeierstrassCurve.baseChange.{0, 0} C (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} K w))] :
  Finite.{1} (ZInQ.Contrib.RC53Assist.DerivedKummer.TateDualityData.pointMod.{0} 2)
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.finite_pointModTwo_integral_local' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.finite_pointModTwo_local

Source line: 619.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.finite_pointModTwo_local (K : Type) [Field.{0} K] [NumberField.{0} K]
  (w : IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))
  [DecidableEq.{1} (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} K w)]
  (B : WeierstrassCurve.{0} (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} K w))
  [WeierstrassCurve.IsElliptic.{0} B] :
  Finite.{1} (ZInQ.Contrib.RC53Assist.DerivedKummer.TateDualityData.pointMod.{0} 2)
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.finite_pointModTwo_local' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.actualPointCompletion_finite

Source line: 643.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.actualPointCompletion_finite (K : Type) [Field.{0} K] [NumberField.{0} K]
  (w : IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))
  [DecidableEq.{1} (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} K w)]
  (B : WeierstrassCurve.{0} (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} K w))
  [WeierstrassCurve.IsElliptic.{0} B] :
  Module.Finite.{0, 0} ℤ_[2]
    (ZInQ.Contrib.RC53Assist.DerivedKummerActual.PointCompletion.{0}
      (WeierstrassCurve.Affine.Point.{0} (WeierstrassCurve.toAffine.{0} B)))
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.actualPointCompletion_finite' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.actualDerived_modTwo_comparisons_of_print

Source line: 681.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.actualDerived_modTwo_comparisons_of_print (K : Type) [Field.{0} K]
  [NumberField.{0} K] (w : IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))
  [DecidableEq.{1} (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} K w)]
  (B : WeierstrassCurve.{0} (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} K w))
  [WeierstrassCurve.IsElliptic.{0} B]
  (I :
    ZInQ.Contrib.RC53Assist.DerivedKummerActual.FinitePointPresentation.{0}
      (WeierstrassCurve.Affine.Point.{0} (WeierstrassCurve.toAffine.{0} B)))
  (hM : ZInQ.Contrib.RC53Assist.DerivedKummer.MilneLocalDualityPrint)
  (hF : ZInQ.Contrib.RC53Assist.DerivedKummer.MilneFiniteLocalDualityPrint) (h2 : IsUnit.{0} 2) :
  (∃ e,
      ∀
        (y :
          TauCeti.ContCohomology.H1.{0, 0}
            (TauCeti.AbsoluteGaloisGroup.{0} (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} K w))
            (WeierstrassCurve.TorsionCoeff.{0} B 2))
        (r :
          ZInQ.Contrib.RC53Assist.DerivedKummer.reductionH1.{0, 0}
            (ZInQ.Contrib.RC53Assist.DerivedKummerActual.FinitePointPresentation.f.{0} I))
        (p : WeierstrassCurve.Affine.Point.{0} (WeierstrassCurve.toAffine.{0} B)),
        Eq.{1} ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.actualReductionH1Identification K w B I) r) ↑p →
          Eq.{1} ((e ↑y) r)
            (((ZInQ.Contrib.CloudB3RC53.Duality.localTatePairing B 2 h2) ((WeierstrassCurve.kummerMap.{0} B 2 h2) p))
              y)) ∧
    ∃ e,
      ∀
        (y :
          TauCeti.ContCohomology.H2.{0, 0}
            (TauCeti.AbsoluteGaloisGroup.{0} (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} K w))
            (WeierstrassCurve.TorsionCoeff.{0} B 2))
        (r :
          ↥(ZInQ.Contrib.RC53Assist.DerivedKummer.reductionH0.{0, 0}
              (ZInQ.Contrib.RC53Assist.DerivedKummerActual.FinitePointPresentation.f.{0} I))),
        Eq.{1} ((e y) r)
          (ZInQ.Contrib.RC53Assist.DerivedKummer.localH2TorsionValue B 2 h2 y
            ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.actualReductionH0Identification K w B I) r))
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.actualDerived_modTwo_comparisons_of_print' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.genuineScalarH1_completePoint

Source line: 713.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.genuineScalarH1_completePoint (K : Type) [Field.{0} K] [NumberField.{0} K]
  (w : IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))
  [DecidableEq.{1} (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} K w)]
  (B : WeierstrassCurve.{0} (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} K w))
  [WeierstrassCurve.IsElliptic.{0} B] (a : ℕ)
  (p : WeierstrassCurve.Affine.Point.{0} (WeierstrassCurve.toAffine.{0} B)) :
  Eq.{1}
    ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.genuineScalarH1 K w B a)
      (Submodule.Quotient.mk.{0, 0}
        ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.completePoint.{0}
            (WeierstrassCurve.Affine.Point.{0} (WeierstrassCurve.toAffine.{0} B)))
          p)))
    ((ZInQ.Manuscript.RC.CoefModules.kummerH1AddEquiv (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} K w) B
        (HPow.hPow.{0, 0, 0} 2 a))
      ↑p)
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.genuineScalarH1_completePoint' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.genuineCompletionKummerMap_completePoint

Source line: 747.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.genuineCompletionKummerMap_completePoint {K : Type} [Field.{0} K]
  [NumberField.{0} K] {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))}
  (W : WeierstrassCurve.{0} K) [WeierstrassCurve.IsElliptic.{0} W] (i : ℕ) (s : ZInQ.Manuscript.RC.CoefModules.KS K S)
  {h : K}
  (hs : Eq.{1} (HPow.hPow.{0, 0, 0} s 2) ((Algebra.algebraMap.{0, 0} K (ZInQ.Manuscript.RC.CoefModules.KS K S)) h))
  (hs0 : Ne.{1} s 0)
  (α :
    MonoidHom.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (Units.{0} (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)))
  [ZInQ.Manuscript.RC.CoefModules.IsOpenKer α]
  (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S W (HPow.hPow.{0, 0, 0} 2 i))
  (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S)
  (hα : ZInQ.Manuscript.RC.KummerMaps.IsLocallyQuadAt i α (ZInQ.Manuscript.RC.CoefModules.quadChar s hs hs0) ↑v)
  (p :
    WeierstrassCurve.Affine.Point.{0}
      (WeierstrassCurve.toAffine.{0} (ZInQ.Manuscript.RC.KummerMaps.localTwist W h ↑v))) :
  Eq.{1}
    ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.genuineCompletionKummerMap W i s hs hs0 α hFull v hα)
      (Submodule.Quotient.mk.{0, 0}
        ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.completePoint.{0}
            (WeierstrassCurve.Affine.Point.{0}
              (WeierstrassCurve.toAffine.{0} (ZInQ.Manuscript.RC.KummerMaps.localTwist W h ↑v))))
          p)))
    ((ZInQ.Manuscript.RC.KummerMaps.actualKummerMap W i s hs hs0 α hFull v hα) p)
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.genuineCompletionKummerMap_completePoint' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.genuineCompletionKummerMap_range

Source line: 753.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.genuineCompletionKummerMap_range {K : Type} [Field.{0} K]
  [NumberField.{0} K] {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))}
  (W : WeierstrassCurve.{0} K) [WeierstrassCurve.IsElliptic.{0} W] (i : ℕ) (s : ZInQ.Manuscript.RC.CoefModules.KS K S)
  {h : K}
  (hs : Eq.{1} (HPow.hPow.{0, 0, 0} s 2) ((Algebra.algebraMap.{0, 0} K (ZInQ.Manuscript.RC.CoefModules.KS K S)) h))
  (hs0 : Ne.{1} s 0)
  (α :
    MonoidHom.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (Units.{0} (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)))
  [ZInQ.Manuscript.RC.CoefModules.IsOpenKer α]
  (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S W (HPow.hPow.{0, 0, 0} 2 i))
  (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S)
  (hα : ZInQ.Manuscript.RC.KummerMaps.IsLocallyQuadAt i α (ZInQ.Manuscript.RC.CoefModules.quadChar s hs hs0) ↑v) :
  Eq.{1}
    (Set.range.{0, 1}
      ⇑(ZInQ.Contrib.RC53Assist.DerivedKummerActual.genuineCompletionKummerMap W i s hs hs0 α hFull v hα))
    (Set.range.{0, 1} ⇑(ZInQ.Manuscript.RC.KummerMaps.actualKummerMap W i s hs hs0 α hFull v hα))
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.genuineCompletionKummerMap_range' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.actualKummerAt_range_eq_completionSpan

Source line: 772.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.actualKummerAt_range_eq_completionSpan {K : Type} [Field.{0} K]
  [NumberField.{0} K] {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))}
  (W : WeierstrassCurve.{0} K) [WeierstrassCurve.IsElliptic.{0} W] (i : ℕ) (s : ZInQ.Manuscript.RC.CoefModules.KS K S)
  {h : K}
  (hs : Eq.{1} (HPow.hPow.{0, 0, 0} s 2) ((Algebra.algebraMap.{0, 0} K (ZInQ.Manuscript.RC.CoefModules.KS K S)) h))
  (hs0 : Ne.{1} s 0)
  (α :
    MonoidHom.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (Units.{0} (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)))
  [ZInQ.Manuscript.RC.CoefModules.IsOpenKer α]
  (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S W (HPow.hPow.{0, 0, 0} 2 i))
  (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S)
  (hα : ZInQ.Manuscript.RC.KummerMaps.IsLocallyQuadAt i α (ZInQ.Manuscript.RC.CoefModules.quadChar s hs hs0) ↑v) :
  Eq.{1}
    (LinearMap.range.{0, 0, 0, 0}
      (ModuleCat.Hom.hom.{0, 0}
        (HomologicalComplex.homologyMap.{0, 1, 0}
          (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC.{0}
            (ZInQ.Manuscript.RC.KummerMaps.actualKummerAt W i s hs hs0 α hFull v hα).i)
          1)))
    (Submodule.span.{0, 0} (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)
      (Set.range.{0, 1}
        ⇑(ZInQ.Contrib.RC53Assist.DerivedKummerActual.genuineCompletionKummerMap W i s hs hs0 α hFull v hα)))
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.actualKummerAt_range_eq_completionSpan' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.closureEquiv_apply

Source line: 814.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.closureEquiv_apply (F : Type) [Field.{0} F] [CharZero.{0} F]
  (x : SeparableClosure.{0} F) : Eq.{1} ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.closureEquiv F) x) ↑x
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.closureEquiv_apply' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.pointCoeffToAlg_base

Source line: 824.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.pointCoeffToAlg_base (F : Type) [Field.{0} F] [CharZero.{0} F]
  [DecidableEq.{1} F] (B : WeierstrassCurve.{0} F)
  (p : WeierstrassCurve.Affine.Point.{0} (WeierstrassCurve.toAffine.{0} B)) :
  Eq.{1}
    ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.pointCoeffToAlg F B)
      ((WeierstrassCurve.basePointCoeff.{0} B) p))
    ((ZInQ.Manuscript.RC.CoefModules.basePt F B) p)
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.pointCoeffToAlg_base' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.pointCoeffToAlg_smul

Source line: 839.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.pointCoeffToAlg_smul (F : Type) [Field.{0} F] [CharZero.{0} F]
  [DecidableEq.{1} F] (B : WeierstrassCurve.{0} F) (σ : Field.absoluteGaloisGroup.{0} F)
  (p : WeierstrassCurve.PointCoeff.{0} B) :
  Eq.{1}
    ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.pointCoeffToAlg F B)
      (HSMul.hSMul.{0, 0, 0} ((TauCeti.absoluteGaloisGroupRestrictEquiv.{0} F) σ) p))
    (HSMul.hSMul.{0, 0, 0} σ ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.pointCoeffToAlg F B) p))
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.pointCoeffToAlg_smul' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.torsionCoeffToAlg_coe

Source line: 859.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.torsionCoeffToAlg_coe (F : Type) [Field.{0} F] [CharZero.{0} F]
  [DecidableEq.{1} F] (B : WeierstrassCurve.{0} F) (n : ℕ) (t : WeierstrassCurve.TorsionCoeff.{0} B n) :
  Eq.{1} (↑((ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.torsionCoeffToAlg F B n) t))
    ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.pointCoeffToAlg F B) ↑t)
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.torsionCoeffToAlg_coe' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.torsionCoeffToAlg_smul

Source line: 863.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.torsionCoeffToAlg_smul (F : Type) [Field.{0} F] [CharZero.{0} F]
  [DecidableEq.{1} F] (B : WeierstrassCurve.{0} F) (n : ℕ) (σ : Field.absoluteGaloisGroup.{0} F)
  (t : WeierstrassCurve.TorsionCoeff.{0} B n) :
  Eq.{1}
    ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.torsionCoeffToAlg F B n)
      (HSMul.hSMul.{0, 0, 0} ((TauCeti.absoluteGaloisGroupRestrictEquiv.{0} F) σ) t))
    (HSMul.hSMul.{0, 0, 0} σ ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.torsionCoeffToAlg F B n) t))
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.torsionCoeffToAlg_smul' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.torsionCoeffToAlg_base

Source line: 869.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.torsionCoeffToAlg_base (F : Type) [Field.{0} F] [CharZero.{0} F]
  [DecidableEq.{1} F] (B : WeierstrassCurve.{0} F) (n : ℕ)
  (t : ↥(AddSubgroup.torsionBy.{0} (WeierstrassCurve.Affine.Point.{0} (WeierstrassCurve.toAffine.{0} B)) ↑n)) :
  Eq.{1}
    ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.torsionCoeffToAlg F B n)
      ((WeierstrassCurve.baseTorsionCoeff.{0} B n) t))
    ((ZInQ.Manuscript.RC.CoefModules.baseTors F B n) t)
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.torsionCoeffToAlg_base' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.hOneToAlg_kummerMap

Source line: 891.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.hOneToAlg_kummerMap (F : Type) [Field.{0} F] [CharZero.{0} F]
  [DecidableEq.{1} F] (B : WeierstrassCurve.{0} F) [WeierstrassCurve.IsElliptic.{0} B] (n : ℕ) [NeZero.{0} n]
  (hn : IsUnit.{0} ↑n) (p : WeierstrassCurve.Affine.Point.{0} (WeierstrassCurve.toAffine.{0} B)) :
  Eq.{1}
    ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.hOneToAlg F B n)
      ((WeierstrassCurve.kummerMap.{0} B n hn) p))
    (ZInQ.Manuscript.RC.SelmerComplex.kerToH1
      (Subtype.mk.{1} (ZInQ.Manuscript.RC.CoefModules.kummerCocycle F B n p)
        (ZInQ.Manuscript.RC.CoefModules.kummerCocycle_isCocycle F B n p)))
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.hOneToAlg_kummerMap' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.kummerCoeff_nsmul

Source line: 922.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.kummerCoeff_nsmul (F : Type) [Field.{0} F] (n : ℕ)
  (t : TauCeti.KummerCoeff.{0} F n) : Eq.{1} (HSMul.hSMul.{0, 0, 0} n t) 0
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.kummerCoeff_nsmul' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.kummerToBr_injective

Source line: 930.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.kummerToBr_injective (F : Type) [Field.{0} F] (n : ℕ)
  (hn : IsUnit.{0} ↑n) : Function.Injective.{1, 1} ⇑(ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr n)
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.kummerToBr_injective' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.kummerToBr_range

Source line: 945.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.kummerToBr_range (F : Type) [Field.{0} F] (n : ℕ)
  (hn : IsUnit.{0} ↑n) :
  Eq.{1} (AddMonoidHom.range.{0, 0} (ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr n))
    (AddSubgroup.torsionBy.{0} (TauCeti.ClassFieldTheory.Br.{0} F) ↑n)
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.kummerToBr_range' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.kummerBrauerEquiv_coe

Source line: 987.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.kummerBrauerEquiv_coe (F : Type) [Field.{0} F] (n : ℕ)
  (hn : IsUnit.{0} ↑n)
  (x : TauCeti.ContCohomology.H2.{0, 0} (TauCeti.AbsoluteGaloisGroup.{0} F) (TauCeti.KummerCoeff.{0} F n)) :
  Eq.{1} (↑((ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.kummerBrauerEquiv F n hn) x))
    ((ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr n) x)
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.kummerBrauerEquiv_coe' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteInvariant_toRat

Source line: 998.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteInvariant_toRat (F : Type) [Field.{0} F] (n : ℕ)
  (hn : IsUnit.{0} ↑n) [ValuativeRel.{0} F] [TopologicalSpace.{0} F] [IsNonarchimedeanLocalField.{0} F] [NeZero.{0} n]
  (x : TauCeti.ContCohomology.H2.{0, 0} (TauCeti.AbsoluteGaloisGroup.{0} F) (TauCeti.KummerCoeff.{0} F n)) :
  Eq.{1} ((ZMod.toRatAddCircle n) ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteInvariant F n hn) x))
    ((TauCeti.ClassFieldTheory.invMap F) ((ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr n) x))
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteInvariant_toRat' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteInvariant_eq_zero_iff

Source line: 1003.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteInvariant_eq_zero_iff (F : Type) [Field.{0} F] (n : ℕ)
  (hn : IsUnit.{0} ↑n) [ValuativeRel.{0} F] [TopologicalSpace.{0} F] [IsNonarchimedeanLocalField.{0} F] [NeZero.{0} n]
  (x : TauCeti.ContCohomology.H2.{0, 0} (TauCeti.AbsoluteGaloisGroup.{0} F) (TauCeti.KummerCoeff.{0} F n)) :
  Eq.{1} ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteInvariant F n hn) x) 0 ↔ Eq.{1} x 0
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteInvariant_eq_zero_iff' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.rationalCircle_injective

Source line: 1010.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.rationalCircle_injective :
  Module.Injective.{0, 0} ℤ ZInQ.Contrib.RC53Assist.DerivedKummer.RationalCircle
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.rationalCircle_injective' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteCochain_nsmul

Source line: 1052.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteCochain_nsmul (F : Type) [Field.{0} F]
  [ValuativeRel.{0} F] [TopologicalSpace.{0} F] [IsNonarchimedeanLocalField.{0} F] (n : ℕ) [NeZero.{0} n]
  (c :
    ↑(HomologicalComplex.X.{0, 1, 0} (ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteComplex F n) 2)) :
  Eq.{1} (HSMul.hSMul.{0, 0, 0} n c) 0
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteCochain_nsmul' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.traceCharacterExtension_torsion

Source line: 1056.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.traceCharacterExtension_torsion (F : Type) [Field.{0} F]
  [ValuativeRel.{0} F] [TopologicalSpace.{0} F] [IsNonarchimedeanLocalField.{0} F] (n : ℕ) [NeZero.{0} n]
  (c :
    ↑(HomologicalComplex.X.{0, 1, 0} (ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteComplex F n) 2)) :
  Eq.{1}
    (HSMul.hSMul.{0, 0, 0} n (↑(ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.traceCharacterExtension F n) c))
    0
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.traceCharacterExtension_torsion' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteCochainTrace_toRat

Source line: 1068.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteCochainTrace_toRat (F : Type) [Field.{0} F]
  [ValuativeRel.{0} F] [TopologicalSpace.{0} F] [IsNonarchimedeanLocalField.{0} F] (n : ℕ) [NeZero.{0} n]
  (c :
    ↑(HomologicalComplex.X.{0, 1, 0} (ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteComplex F n) 2)) :
  Eq.{1} ((ZMod.toRatAddCircle n) ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteCochainTrace F n) c))
    (↑(ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.traceCharacterExtension F n) c)
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteCochainTrace_toRat' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteCochainTrace_cocycle

Source line: 1073.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteCochainTrace_cocycle (F : Type) [Field.{0} F]
  [ValuativeRel.{0} F] [TopologicalSpace.{0} F] [IsNonarchimedeanLocalField.{0} F] (n : ℕ) [NeZero.{0} n]
  (hn : IsUnit.{0} ↑n)
  (c :
    ↥(LinearMap.ker.{0, 0, 0, 0}
        (ModuleCat.Hom.hom.{0, 0}
          (HomologicalComplex.d.{0, 1, 0} (ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteComplex F n) 2
            3)))) :
  Eq.{1} ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteCochainTrace F n) ↑c)
    ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteInvariant F n hn)
      (ZInQ.Manuscript.RC.SelmerComplex.kerToH2 c))
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteCochainTrace_cocycle' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteCochainTrace_boundary

Source line: 1082.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteCochainTrace_boundary (F : Type) [Field.{0} F]
  [ValuativeRel.{0} F] [TopologicalSpace.{0} F] [IsNonarchimedeanLocalField.{0} F] (n : ℕ) [NeZero.{0} n]
  (hn : IsUnit.{0} ↑n)
  (c :
    ↑(HomologicalComplex.X.{0, 1, 0} (ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteComplex F n) 1)) :
  Eq.{1}
    ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteCochainTrace F n)
      ((ModuleCat.Hom.hom.{0, 0}
          (HomologicalComplex.d.{0, 1, 0} (ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteComplex F n) 1
            2))
        c))
    0
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteCochainTrace_boundary' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteCochainTrace_kernel

Source line: 1096.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteCochainTrace_kernel (F : Type) [Field.{0} F]
  [ValuativeRel.{0} F] [TopologicalSpace.{0} F] [IsNonarchimedeanLocalField.{0} F] (n : ℕ) [NeZero.{0} n]
  (hn : IsUnit.{0} ↑n)
  (z : ↑(HomologicalComplex.X.{0, 1, 0} (ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteComplex F n) 2))
  (hz :
    Eq.{1}
      ((ModuleCat.Hom.hom.{0, 0}
          (HomologicalComplex.d.{0, 1, 0} (ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteComplex F n) 2
            3))
        z)
      0)
  (ht : Eq.{1} ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteCochainTrace F n) z) 0) :
  ∃ c,
    Eq.{1}
      ((ModuleCat.Hom.hom.{0, 0}
          (HomologicalComplex.d.{0, 1, 0} (ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteComplex F n) 1
            2))
        c)
      z
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteCochainTrace_kernel' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteCochainTrace_onto_one

Source line: 1106.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteCochainTrace_onto_one (F : Type) [Field.{0} F]
  [ValuativeRel.{0} F] [TopologicalSpace.{0} F] [IsNonarchimedeanLocalField.{0} F] (n : ℕ) [NeZero.{0} n]
  (hn : IsUnit.{0} ↑n) :
  ∃ z,
    Eq.{1}
        ((ModuleCat.Hom.hom.{0, 0}
            (HomologicalComplex.d.{0, 1, 0} (ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteComplex F n)
              2 3))
          z)
        0 ∧
      Eq.{1} ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteCochainTrace F n) z) 1
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteCochainTrace_onto_one' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteCochainTrace_inducesIsoH2

Source line: 1116.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteCochainTrace_inducesIsoH2 (F : Type) [Field.{0} F]
  [ValuativeRel.{0} F] [TopologicalSpace.{0} F] [IsNonarchimedeanLocalField.{0} F] (n : ℕ) [NeZero.{0} n]
  (hn : IsUnit.{0} ↑n) :
  ZInQ.Manuscript.RC.SelmerComplex.InducesIsoH2
    (ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteCochainTrace F n)
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.finiteCochainTrace_inducesIsoH2' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.coefficientProjection_smul

Source line: 1220.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.coefficientProjection_smul (G A : Type) [Group.{0} G]
  [AddCommGroup.{0} A] [DistribMulAction.{0, 0} G A] (a : ℕ) (σ : G)
  (x : ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.IntegralTateCoeff G A) :
  Eq.{1}
    ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.coefficientProjection G A a)
      (HSMul.hSMul.{0, 0, 0} σ x))
    (HSMul.hSMul.{0, 0, 0} σ
      ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.coefficientProjection G A a) x))
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.coefficientProjection_smul' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.coefficientProjection_scalar

Source line: 1224.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.coefficientProjection_scalar (G A : Type) [Group.{0} G]
  [AddCommGroup.{0} A] [DistribMulAction.{0, 0} G A] (a : ℕ) (r : ℤ_[2])
  (x : ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.IntegralTateCoeff G A) :
  Eq.{1}
    ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.coefficientProjection G A a)
      (HSMul.hSMul.{0, 0, 0} r x))
    (HSMul.hSMul.{0, 0, 0} ((PadicInt.toZModPow a) r)
      ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.coefficientProjection G A a) x))
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.coefficientProjection_scalar' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.coefficientProjection_continuous

Source line: 1229.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.coefficientProjection_continuous (G A : Type)
  [Group.{0} G] [AddCommGroup.{0} A] [DistribMulAction.{0, 0} G A] (a : ℕ) :
  Continuous.{0, 0} ⇑(ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.coefficientProjection G A a)
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.coefficientProjection_continuous' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.coefficientTransition_smul

Source line: 1248.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.coefficientTransition_smul (G A : Type) [Group.{0} G]
  [AddCommGroup.{0} A] [DistribMulAction.{0, 0} G A] (a : ℕ) (σ : G)
  (t : ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.FiniteTateCoeff G A (HAdd.hAdd.{0, 0, 0} a 1)) :
  Eq.{1}
    ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.coefficientTransition G A a)
      (HSMul.hSMul.{0, 0, 0} σ t))
    (HSMul.hSMul.{0, 0, 0} σ
      ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.coefficientTransition G A a) t))
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.coefficientTransition_smul' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.coefficientProjection_succ

Source line: 1256.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.coefficientProjection_succ (G A : Type) [Group.{0} G]
  [AddCommGroup.{0} A] [DistribMulAction.{0, 0} G A] (a : ℕ)
  (x : ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.IntegralTateCoeff G A) :
  Eq.{1}
    ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.coefficientTransition G A a)
      ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.coefficientProjection G A
          (HAdd.hAdd.{0, 0, 0} a 1))
        x))
    ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.coefficientProjection G A a) x)
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.coefficientProjection_succ' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.reduceCochains_apply

Source line: 1298.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.reduceCochains_apply (G A : Type) [Group.{0} G]
  [TopologicalSpace.{0} G] [IsTopologicalGroup.{0} G] [AddCommGroup.{0} A] [DistribMulAction.{0, 0} G A]
  [TopologicalSpace.{0} A] [DiscreteTopology.{0} A] [ContinuousSMul.{0, 0} G A] (a k : ℕ)
  (c :
    ↑(HomologicalComplex.X.{0, 1, 0} (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.integralComplex G A)
        k))
  (s : Fin k → G) :
  Eq.{1}
    (ZInQ.Manuscript.RC.CoefModules.cfun.{0}
      ((ModuleCat.Hom.hom.{0, 0}
          (HomologicalComplex.Hom.f.{0, 1, 0}
            (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.reduceCochains G A a) k))
        c)
      s)
    ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.coefficientProjection G A a)
      (ZInQ.Manuscript.RC.CoefModules.cfun.{0} c s))
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.reduceCochains_apply' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.reduceCochains_d

Source line: 1302.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.reduceCochains_d (G A : Type) [Group.{0} G]
  [TopologicalSpace.{0} G] [IsTopologicalGroup.{0} G] [AddCommGroup.{0} A] [DistribMulAction.{0, 0} G A]
  [TopologicalSpace.{0} A] [DiscreteTopology.{0} A] [ContinuousSMul.{0, 0} G A] (a k : ℕ)
  (c :
    ↑(HomologicalComplex.X.{0, 1, 0} (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.integralComplex G A)
        k)) :
  Eq.{1}
    ((ModuleCat.Hom.hom.{0, 0}
        (HomologicalComplex.Hom.f.{0, 1, 0}
          (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.reduceCochains G A a)
          (HAdd.hAdd.{0, 0, 0} k 1)))
      ((ModuleCat.Hom.hom.{0, 0}
          (HomologicalComplex.d.{0, 1, 0}
            (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.integralComplex G A) k
            (HAdd.hAdd.{0, 0, 0} k 1)))
        c))
    ((ModuleCat.Hom.hom.{0, 0}
        (HomologicalComplex.d.{0, 1, 0}
          (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.finiteIntegralComplex G A a) k
          (HAdd.hAdd.{0, 0, 0} k 1)))
      ((ModuleCat.Hom.hom.{0, 0}
          (HomologicalComplex.Hom.f.{0, 1, 0}
            (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.reduceCochains G A a) k))
        c))
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.reduceCochains_d' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.transitionCochains_d

Source line: 1360.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.transitionCochains_d (G A : Type) [Group.{0} G]
  [TopologicalSpace.{0} G] [IsTopologicalGroup.{0} G] [AddCommGroup.{0} A] [DistribMulAction.{0, 0} G A]
  [TopologicalSpace.{0} A] [DiscreteTopology.{0} A] [ContinuousSMul.{0, 0} G A] (a k : ℕ)
  (c :
    ↑(HomologicalComplex.X.{0, 1, 0}
        (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.finiteIntegralComplex G A
          (HAdd.hAdd.{0, 0, 0} a 1))
        k)) :
  Eq.{1}
    ((ModuleCat.Hom.hom.{0, 0}
        (HomologicalComplex.Hom.f.{0, 1, 0}
          (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.transitionCochains G A a)
          (HAdd.hAdd.{0, 0, 0} k 1)))
      ((ModuleCat.Hom.hom.{0, 0}
          (HomologicalComplex.d.{0, 1, 0}
            (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.finiteIntegralComplex G A
              (HAdd.hAdd.{0, 0, 0} a 1))
            k (HAdd.hAdd.{0, 0, 0} k 1)))
        c))
    ((ModuleCat.Hom.hom.{0, 0}
        (HomologicalComplex.d.{0, 1, 0}
          (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.finiteIntegralComplex G A a) k
          (HAdd.hAdd.{0, 0, 0} k 1)))
      ((ModuleCat.Hom.hom.{0, 0}
          (HomologicalComplex.Hom.f.{0, 1, 0}
            (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.transitionCochains G A a) k))
        c))
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.transitionCochains_d' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.reduceCochains_succ

Source line: 1368.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.reduceCochains_succ (G A : Type) [Group.{0} G]
  [TopologicalSpace.{0} G] [IsTopologicalGroup.{0} G] [AddCommGroup.{0} A] [DistribMulAction.{0, 0} G A]
  [TopologicalSpace.{0} A] [DiscreteTopology.{0} A] [ContinuousSMul.{0, 0} G A] (a k : ℕ)
  (c :
    ↑(HomologicalComplex.X.{0, 1, 0} (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.integralComplex G A)
        k)) :
  Eq.{1}
    ((ModuleCat.Hom.hom.{0, 0}
        (HomologicalComplex.Hom.f.{0, 1, 0}
          (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.transitionCochains G A a) k))
      ((ModuleCat.Hom.hom.{0, 0}
          (HomologicalComplex.Hom.f.{0, 1, 0}
            (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.reduceCochains G A (HAdd.hAdd.{0, 0, 0} a 1))
            k))
        c))
    ((ModuleCat.Hom.hom.{0, 0}
        (HomologicalComplex.Hom.f.{0, 1, 0}
          (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.reduceCochains G A a) k))
      c)
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.reduceCochains_succ' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.liftCompatibleCochains_projection

Source line: 1390.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.liftCompatibleCochains_projection (G A : Type)
  [Group.{0} G] [TopologicalSpace.{0} G] [IsTopologicalGroup.{0} G] [AddCommGroup.{0} A] [DistribMulAction.{0, 0} G A]
  [TopologicalSpace.{0} A] [DiscreteTopology.{0} A] [ContinuousSMul.{0, 0} G A] (k : ℕ)
  (c :
    (a : ℕ) →
      ↑(HomologicalComplex.X.{0, 1, 0}
          (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.finiteIntegralComplex G A a) k))
  (hc :
    ∀ (a : ℕ),
      Eq.{1}
        ((ModuleCat.Hom.hom.{0, 0}
            (HomologicalComplex.Hom.f.{0, 1, 0}
              (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.transitionCochains G A a) k))
          (c (HAdd.hAdd.{0, 0, 0} a 1)))
        (c a))
  (a : ℕ) :
  Eq.{1}
    ((ModuleCat.Hom.hom.{0, 0}
        (HomologicalComplex.Hom.f.{0, 1, 0}
          (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.reduceCochains G A a) k))
      (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.liftCompatibleCochains G A k c hc))
    (c a)
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.liftCompatibleCochains_projection' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.integralCochain_ext

Source line: 1398.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.integralCochain_ext (G A : Type) [Group.{0} G]
  [TopologicalSpace.{0} G] [IsTopologicalGroup.{0} G] [AddCommGroup.{0} A] [DistribMulAction.{0, 0} G A]
  [TopologicalSpace.{0} A] [DiscreteTopology.{0} A] [ContinuousSMul.{0, 0} G A] (k : ℕ)
  (c d :
    ↑(HomologicalComplex.X.{0, 1, 0} (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.integralComplex G A)
        k))
  (h :
    ∀ (a : ℕ),
      Eq.{1}
        ((ModuleCat.Hom.hom.{0, 0}
            (HomologicalComplex.Hom.f.{0, 1, 0}
              (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.reduceCochains G A a) k))
          c)
        ((ModuleCat.Hom.hom.{0, 0}
            (HomologicalComplex.Hom.f.{0, 1, 0}
              (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.reduceCochains G A a) k))
          d)) :
  Eq.{1} c d
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.integralCochain_ext' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.transitionH1_kerToH1

Source line: 1428.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.transitionH1_kerToH1 (G A : Type) [Group.{0} G]
  [TopologicalSpace.{0} G] [IsTopologicalGroup.{0} G] [AddCommGroup.{0} A] [DistribMulAction.{0, 0} G A]
  [TopologicalSpace.{0} A] [DiscreteTopology.{0} A] [ContinuousSMul.{0, 0} G A] (a : ℕ)
  (c :
    ↥(LinearMap.ker.{0, 0, 0, 0}
        (ModuleCat.Hom.hom.{0, 0}
          (HomologicalComplex.d.{0, 1, 0}
            (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.finiteIntegralComplex G A
              (HAdd.hAdd.{0, 0, 0} a 1))
            1 2)))) :
  Eq.{1}
    ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.transitionH1 G A a)
      (ZInQ.Manuscript.RC.SelmerComplex.kerToH1 c))
    (ZInQ.Manuscript.RC.SelmerComplex.kerToH1
      ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.transitionCycle G A a 1) c))
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.transitionH1_kerToH1' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.transitionCochains_surjective

Source line: 1434.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.transitionCochains_surjective (G A : Type) [Group.{0} G]
  [TopologicalSpace.{0} G] [IsTopologicalGroup.{0} G] [AddCommGroup.{0} A] [DistribMulAction.{0, 0} G A]
  [TopologicalSpace.{0} A] [DiscreteTopology.{0} A] [ContinuousSMul.{0, 0} G A] (a k : ℕ)
  (hcoeff :
    Function.Surjective.{1, 1}
      ⇑(ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.coefficientTransition G A a)) :
  Function.Surjective.{1, 1}
    ⇑(ModuleCat.Hom.hom.{0, 0}
        (HomologicalComplex.Hom.f.{0, 1, 0}
          (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.transitionCochains G A a) k))
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.transitionCochains_surjective' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.transitionOneCycle_surjective

Source line: 1444.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.transitionOneCycle_surjective (G A : Type) [Group.{0} G]
  [TopologicalSpace.{0} G] [IsTopologicalGroup.{0} G] [AddCommGroup.{0} A] [DistribMulAction.{0, 0} G A]
  [TopologicalSpace.{0} A] [DiscreteTopology.{0} A] [ContinuousSMul.{0, 0} G A] (a : ℕ)
  (hcoeff :
    Function.Surjective.{1, 1}
      ⇑(ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.coefficientTransition G A a))
  (hclass :
    Function.Surjective.{1, 1} ⇑(ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.transitionH1 G A a)) :
  Function.Surjective.{1, 1} ⇑(ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.transitionCycle G A a 1)
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.transitionOneCycle_surjective' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.integral_boundary_of_finite_boundaries

Source line: 1471.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.integral_boundary_of_finite_boundaries (G A : Type)
  [Group.{0} G] [TopologicalSpace.{0} G] [IsTopologicalGroup.{0} G] [AddCommGroup.{0} A] [DistribMulAction.{0, 0} G A]
  [TopologicalSpace.{0} A] [DiscreteTopology.{0} A] [ContinuousSMul.{0, 0} G A]
  (hlift :
    ∀ (a : ℕ),
      Function.Surjective.{1, 1}
        ⇑(ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.transitionCycle G A a 1))
  (z :
    ↑(HomologicalComplex.X.{0, 1, 0} (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.integralComplex G A)
        2))
  (hzero :
    ∀ (a : ℕ),
      ∃ b,
        Eq.{1}
          ((ModuleCat.Hom.hom.{0, 0}
              (HomologicalComplex.d.{0, 1, 0}
                (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.finiteIntegralComplex G A a) 1 2))
            b)
          ((ModuleCat.Hom.hom.{0, 0}
              (HomologicalComplex.Hom.f.{0, 1, 0}
                (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.reduceCochains G A a) 2))
            z)) :
  ∃ b,
    Eq.{1}
      ((ModuleCat.Hom.hom.{0, 0}
          (HomologicalComplex.d.{0, 1, 0}
            (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.integralComplex G A) 1 2))
        b)
      z
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.integral_boundary_of_finite_boundaries' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualLevelEquiv_smul

Source line: 1529.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualLevelEquiv_smul (F : Type) [Field.{0} F]
  [CharZero.{0} F] [DecidableEq.{1} F] (B : WeierstrassCurve.{0} F) (a : ℕ) (σ : Field.absoluteGaloisGroup.{0} F)
  (t :
    ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.FiniteTateCoeff (Field.absoluteGaloisGroup.{0} F)
      (ZInQ.Manuscript.RC.CoefModules.PtAlg F B) a) :
  Eq.{1}
    ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualLevelEquiv F B a) (HSMul.hSMul.{0, 0, 0} σ t))
    (HSMul.hSMul.{0, 0, 0} σ ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualLevelEquiv F B a) t))
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualLevelEquiv_smul' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualMuLevelEquiv_smul

Source line: 1595.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualMuLevelEquiv_smul (F : Type) [Field.{0} F] (a : ℕ)
  (σ : TauCeti.AbsoluteGaloisGroup.{0} F)
  (t :
    ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.FiniteTateCoeff (TauCeti.AbsoluteGaloisGroup.{0} F)
      (TauCeti.UnitsCoeff.{0} F) a) :
  Eq.{1}
    ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualMuLevelEquiv F a) (HSMul.hSMul.{0, 0, 0} σ t))
    (HSMul.hSMul.{0, 0, 0} σ ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualMuLevelEquiv F a) t))
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualMuLevelEquiv_smul' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualMuLevelEquiv_transition

Source line: 1631.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualMuLevelEquiv_transition (F : Type) [Field.{0} F]
  (a : ℕ)
  (t :
    ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.FiniteTateCoeff (TauCeti.AbsoluteGaloisGroup.{0} F)
      (TauCeti.UnitsCoeff.{0} F) (HAdd.hAdd.{0, 0, 0} a 1)) :
  Eq.{1}
    ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualMuLevelEquiv F a)
      ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.coefficientTransition
          (TauCeti.AbsoluteGaloisGroup.{0} F) (TauCeti.UnitsCoeff.{0} F) a)
        t))
    ((TauCeti.kummerCoeffPow.{0} F (pow_dvd_pow.{0} 2 (Nat.le_succ a)))
      ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualMuLevelEquiv F (HAdd.hAdd.{0, 0, 0} a 1))
        t))
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualMuLevelEquiv_transition' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualMuH1Equiv_transition

Source line: 1646.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualMuH1Equiv_transition (F : Type) [Field.{0} F]
  (a : ℕ)
  (y :
    TauCeti.ContCohomology.H1.{0, 0} (TauCeti.AbsoluteGaloisGroup.{0} F)
      (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.FiniteTateCoeff (TauCeti.AbsoluteGaloisGroup.{0} F)
        (TauCeti.UnitsCoeff.{0} F) (HAdd.hAdd.{0, 0, 0} a 1))) :
  Eq.{1}
    ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualMuH1Equiv F a)
      ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.transitionH1 (TauCeti.AbsoluteGaloisGroup.{0} F)
          (TauCeti.UnitsCoeff.{0} F) a)
        y))
    ((TauCeti.ContCohomology.explicitCoeff1.{0, 0, 0} (TauCeti.AbsoluteGaloisGroup.{0} F)
        (TauCeti.KummerCoeff.{0} F (HPow.hPow.{0, 0, 0} 2 (HAdd.hAdd.{0, 0, 0} a 1)))
        (TauCeti.kummerCoeffPow.{0} F (pow_dvd_pow.{0} 2 (Nat.le_succ a))) continuous_of_discreteTopology.{0, 0})
      ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualMuH1Equiv F (HAdd.hAdd.{0, 0, 0} a 1)) y))
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualMuH1Equiv_transition' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualMuTransition_surjective

Source line: 1664.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualMuTransition_surjective (F : Type) [Field.{0} F]
  [CharZero.{0} F] (a : ℕ) :
  Function.Surjective.{1, 1}
    ⇑(ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.coefficientTransition
        (TauCeti.AbsoluteGaloisGroup.{0} F) (TauCeti.UnitsCoeff.{0} F) a)
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualMuTransition_surjective' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualMuH1Transition_surjective

Source line: 1676.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualMuH1Transition_surjective (F : Type) [Field.{0} F]
  [CharZero.{0} F] (a : ℕ) :
  Function.Surjective.{1, 1}
    ⇑(ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.transitionH1 (TauCeti.AbsoluteGaloisGroup.{0} F)
        (TauCeti.UnitsCoeff.{0} F) a)
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualMuH1Transition_surjective' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualMuOneCycleTransition_surjective

Source line: 1688.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualMuOneCycleTransition_surjective (F : Type)
  [Field.{0} F] [CharZero.{0} F] (a : ℕ) :
  Function.Surjective.{1, 1}
    ⇑(ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.transitionCycle (TauCeti.AbsoluteGaloisGroup.{0} F)
        (TauCeti.UnitsCoeff.{0} F) a 1)
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualMuOneCycleTransition_surjective' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualMuH2Reduction_eq_zero_iff

Source line: 1694.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualMuH2Reduction_eq_zero_iff (F : Type) [Field.{0} F]
  [CharZero.{0} F] (a : ℕ)
  (z :
    ↥(LinearMap.ker.{0, 0, 0, 0}
        (ModuleCat.Hom.hom.{0, 0}
          (HomologicalComplex.d.{0, 1, 0}
            (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualTraceComplex F) 2 3)))) :
  Eq.{1} ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualMuH2Reduction F a) z) 0 ↔
    Eq.{1}
      (ZInQ.Manuscript.RC.SelmerComplex.kerToH2
        ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.reduceTwoCycle
            (TauCeti.AbsoluteGaloisGroup.{0} F) (TauCeti.UnitsCoeff.{0} F) a)
          z))
      0
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualMuH2Reduction_eq_zero_iff' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualMuH2Reduction_all_zero_iff_boundary

Source line: 1701.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualMuH2Reduction_all_zero_iff_boundary (F : Type)
  [Field.{0} F] [CharZero.{0} F]
  (z :
    ↥(LinearMap.ker.{0, 0, 0, 0}
        (ModuleCat.Hom.hom.{0, 0}
          (HomologicalComplex.d.{0, 1, 0}
            (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualTraceComplex F) 2 3)))) :
  (∀ (a : ℕ), Eq.{1} ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualMuH2Reduction F a) z) 0) ↔
    ∃ b,
      Eq.{1}
        ((ModuleCat.Hom.hom.{0, 0}
            (HomologicalComplex.d.{0, 1, 0}
              (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualTraceComplex F) 1 2))
          b)
        ↑z
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualMuH2Reduction_all_zero_iff_boundary' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.representatives_mk

Source line: 1742.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.representatives_mk.{u_1} (P : Type u_1)
  [AddCommGroup.{u_1} P] (x : ZInQ.Contrib.RC53Assist.DerivedKummerActual.PointCompletion.{u_1} P) (a : ℕ) :
  Eq.{u_1 + 1}
    (Submodule.Quotient.mk.{0, u_1}
      (↑(ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.representatives.{u_1} P x) a))
    (↑x a)
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.representatives_mk' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.stepPoint_mul

Source line: 1753.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.stepPoint_mul.{u_1} (P : Type u_1) [AddCommGroup.{u_1} P]
  (x : ZInQ.Contrib.RC53Assist.DerivedKummerActual.PointCompletion.{u_1} P) (a : ℕ) :
  Eq.{u_1 + 1}
    (HSMul.hSMul.{0, u_1, u_1} (HPow.hPow.{0, 0, 0} 2 a)
      (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.stepPoint.{u_1} P x a))
    (HSub.hSub.{u_1, u_1, u_1}
      (↑(ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.representatives.{u_1} P x)
        (HAdd.hAdd.{0, 0, 0} a 1))
      (↑(ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.representatives.{u_1} P x) a))
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.stepPoint_mul' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.two_halve

Source line: 1768.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.two_halve (F : Type) [Field.{0} F] [CharZero.{0} F]
  [DecidableEq.{1} F] (B : WeierstrassCurve.{0} F) [WeierstrassCurve.IsElliptic.{0} B]
  (Q : ZInQ.Manuscript.RC.CoefModules.PtAlg F B) :
  Eq.{1} (HSMul.hSMul.{0, 0, 0} 2 (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.halve F B Q)) Q
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.two_halve' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.divisionFamily_two

Source line: 1777.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.divisionFamily_two (F : Type) [Field.{0} F] [CharZero.{0} F]
  [DecidableEq.{1} F] (B : WeierstrassCurve.{0} F) [WeierstrassCurve.IsElliptic.{0} B]
  (x :
    ZInQ.Contrib.RC53Assist.DerivedKummerActual.PointCompletion.{0}
      (WeierstrassCurve.Affine.Point.{0} (WeierstrassCurve.toAffine.{0} B)))
  (a : ℕ) :
  Eq.{1}
    (HSMul.hSMul.{0, 0, 0} 2
      (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.divisionFamily F B x (HAdd.hAdd.{0, 0, 0} a 1)))
    (HAdd.hAdd.{0, 0, 0} (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.divisionFamily F B x a)
      ((ZInQ.Manuscript.RC.CoefModules.basePt F B)
        (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.stepPoint.{0}
          (WeierstrassCurve.Affine.Point.{0} (WeierstrassCurve.toAffine.{0} B)) x a)))
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.divisionFamily_two' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.divisionFamily_power

Source line: 1783.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.divisionFamily_power (F : Type) [Field.{0} F]
  [CharZero.{0} F] [DecidableEq.{1} F] (B : WeierstrassCurve.{0} F) [WeierstrassCurve.IsElliptic.{0} B]
  (x :
    ZInQ.Contrib.RC53Assist.DerivedKummerActual.PointCompletion.{0}
      (WeierstrassCurve.Affine.Point.{0} (WeierstrassCurve.toAffine.{0} B)))
  (a : ℕ) :
  Eq.{1}
    (HSMul.hSMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} 2 a)
      (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.divisionFamily F B x a))
    ((ZInQ.Manuscript.RC.CoefModules.basePt F B)
      (↑(ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.representatives.{0}
            (WeierstrassCurve.Affine.Point.{0} (WeierstrassCurve.toAffine.{0} B)) x)
        a))
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.divisionFamily_power' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.integralKummerValue_projection

Source line: 1803.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.integralKummerValue_projection (F : Type) [Field.{0} F]
  [CharZero.{0} F] [DecidableEq.{1} F] (B : WeierstrassCurve.{0} F) [WeierstrassCurve.IsElliptic.{0} B]
  (x :
    ZInQ.Contrib.RC53Assist.DerivedKummerActual.PointCompletion.{0}
      (WeierstrassCurve.Affine.Point.{0} (WeierstrassCurve.toAffine.{0} B)))
  (a : ℕ) (σ : Field.absoluteGaloisGroup.{0} F) :
  Eq.{1}
    ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualLevelEquiv F B a)
      ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.coefficientProjection
          (Field.absoluteGaloisGroup.{0} F) (ZInQ.Manuscript.RC.CoefModules.PtAlg F B) a)
        (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.integralKummerValue F B x σ)))
    (ZInQ.Manuscript.RC.CoefModules.kummerFunOf F B (HPow.hPow.{0, 0, 0} 2 a)
      (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.divisionFamily_power F B x a) σ)
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.integralKummerValue_projection' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.integralKummerCochain_isCycle

Source line: 1821.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.integralKummerCochain_isCycle (F : Type) [Field.{0} F]
  [CharZero.{0} F] [DecidableEq.{1} F] (B : WeierstrassCurve.{0} F) [WeierstrassCurve.IsElliptic.{0} B]
  (x :
    ZInQ.Contrib.RC53Assist.DerivedKummerActual.PointCompletion.{0}
      (WeierstrassCurve.Affine.Point.{0} (WeierstrassCurve.toAffine.{0} B))) :
  Eq.{1}
    ((ModuleCat.Hom.hom.{0, 0}
        (HomologicalComplex.d.{0, 1, 0}
          (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualIntegralComplex F B) 1 2))
      (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.integralKummerCochain F B x))
    0
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.integralKummerCochain_isCycle' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.integralKummerCochain_projection

Source line: 1845.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.integralKummerCochain_projection (F : Type) [Field.{0} F]
  [CharZero.{0} F] [DecidableEq.{1} F] (B : WeierstrassCurve.{0} F) [WeierstrassCurve.IsElliptic.{0} B]
  (x :
    ZInQ.Contrib.RC53Assist.DerivedKummerActual.PointCompletion.{0}
      (WeierstrassCurve.Affine.Point.{0} (WeierstrassCurve.toAffine.{0} B)))
  (a : ℕ) (s : Fin 1 → Field.absoluteGaloisGroup.{0} F) :
  Eq.{1}
    ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualLevelEquiv F B a)
      (ZInQ.Manuscript.RC.CoefModules.cfun.{0}
        ((ModuleCat.Hom.hom.{0, 0}
            (HomologicalComplex.Hom.f.{0, 1, 0}
              (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.reduceCochains
                (Field.absoluteGaloisGroup.{0} F) (ZInQ.Manuscript.RC.CoefModules.PtAlg F B) a)
              1))
          (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.integralKummerCochain F B x))
        s))
    (ZInQ.Manuscript.RC.CoefModules.cfun.{0}
      (ZInQ.Manuscript.RC.CoefModules.kummerCocycleOf F B (HPow.hPow.{0, 0, 0} 2 a)
        (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.divisionFamily_power F B x a))
      s)
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.integralKummerCochain_projection' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.integralKummerCycle_class

Source line: 1853.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.integralKummerCycle_class (F : Type) [Field.{0} F]
  [CharZero.{0} F] [DecidableEq.{1} F] (B : WeierstrassCurve.{0} F) [WeierstrassCurve.IsElliptic.{0} B]
  (x :
    ZInQ.Contrib.RC53Assist.DerivedKummerActual.PointCompletion.{0}
      (WeierstrassCurve.Affine.Point.{0} (WeierstrassCurve.toAffine.{0} B)))
  (a : ℕ) :
  Eq.{1}
    ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualH1Reduction F B a)
      (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.integralKummerCycle F B x))
    ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.hOneToAlg F B (HPow.hPow.{0, 0, 0} 2 a))
      ((WeierstrassCurve.kummerMap.{0} B (HPow.hPow.{0, 0, 0} 2 a)
          (isUnit_iff_ne_zero.{0}.mpr
            (ZInQ.Manuscript.RC.CoefModules.natCast_ne_zero_of_charZero F (HPow.hPow.{0, 0, 0} 2 a))))
        (↑(ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.representatives.{0}
              (WeierstrassCurve.Affine.Point.{0} (WeierstrassCurve.toAffine.{0} B)) x)
          a)))
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.integralKummerCycle_class' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.finiteCochain_smul_repr

Source line: 1881.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.finiteCochain_smul_repr (F : Type) [Field.{0} F]
  [CharZero.{0} F] [DecidableEq.{1} F] (B : WeierstrassCurve.{0} F) [WeierstrassCurve.IsElliptic.{0} B] (a k : ℕ)
  (r : ℤ_[2])
  (c :
    ↑(HomologicalComplex.X.{0, 1, 0}
        (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.finiteIntegralComplex
          (Field.absoluteGaloisGroup.{0} F) (ZInQ.Manuscript.RC.CoefModules.PtAlg F B) a)
        k)) :
  Eq.{1} (HSMul.hSMul.{0, 0, 0} r c) (HSMul.hSMul.{0, 0, 0} ((PadicInt.toZModPow a) r).val c)
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.finiteCochain_smul_repr' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.actualH1Reduction_smul

Source line: 1893.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.actualH1Reduction_smul (F : Type) [Field.{0} F]
  [CharZero.{0} F] [DecidableEq.{1} F] (B : WeierstrassCurve.{0} F) [WeierstrassCurve.IsElliptic.{0} B] (a : ℕ)
  (r : ℤ_[2])
  (c :
    ↥(LinearMap.ker.{0, 0, 0, 0}
        (ModuleCat.Hom.hom.{0, 0}
          (HomologicalComplex.d.{0, 1, 0}
            (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualIntegralComplex F B) 1 2)))) :
  Eq.{1}
    ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualH1Reduction F B a)
      (HSMul.hSMul.{0, 0, 0} r c))
    (HSMul.hSMul.{0, 0, 0} ((PadicInt.toZModPow a) r).val
      ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualH1Reduction F B a) c))
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.actualH1Reduction_smul' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.completionKummerClass_representatives

Source line: 1919.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.completionKummerClass_representatives (F : Type)
  [Field.{0} F] [CharZero.{0} F] [DecidableEq.{1} F] (B : WeierstrassCurve.{0} F) [WeierstrassCurve.IsElliptic.{0} B]
  (a : ℕ)
  (x :
    ZInQ.Contrib.RC53Assist.DerivedKummerActual.PointCompletion.{0}
      (WeierstrassCurve.Affine.Point.{0} (WeierstrassCurve.toAffine.{0} B))) :
  Eq.{1} ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.completionKummerClass F B a) x)
    ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.hOneToAlg F B (HPow.hPow.{0, 0, 0} 2 a))
      ((WeierstrassCurve.kummerMap.{0} B (HPow.hPow.{0, 0, 0} 2 a)
          (isUnit_iff_ne_zero.{0}.mpr
            (ZInQ.Manuscript.RC.CoefModules.natCast_ne_zero_of_charZero F (HPow.hPow.{0, 0, 0} 2 a))))
        (↑(ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.representatives.{0}
              (WeierstrassCurve.Affine.Point.{0} (WeierstrassCurve.toAffine.{0} B)) x)
          a)))
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.completionKummerClass_representatives' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.integralKummerCycle_reduction

Source line: 1930.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.integralKummerCycle_reduction (F : Type) [Field.{0} F]
  [CharZero.{0} F] [DecidableEq.{1} F] (B : WeierstrassCurve.{0} F) [WeierstrassCurve.IsElliptic.{0} B] (a : ℕ)
  (x :
    ZInQ.Contrib.RC53Assist.DerivedKummerActual.PointCompletion.{0}
      (WeierstrassCurve.Affine.Point.{0} (WeierstrassCurve.toAffine.{0} B))) :
  Eq.{1}
    ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualH1Reduction F B a)
      (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.integralKummerCycle F B x))
    ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.completionKummerClass F B a) x)
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.integralKummerCycle_reduction' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.completionKummerClass_smul

Source line: 1935.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.completionKummerClass_smul (F : Type) [Field.{0} F]
  [CharZero.{0} F] [DecidableEq.{1} F] (B : WeierstrassCurve.{0} F) [WeierstrassCurve.IsElliptic.{0} B] (a : ℕ)
  (r : ℤ_[2])
  (x :
    ZInQ.Contrib.RC53Assist.DerivedKummerActual.PointCompletion.{0}
      (WeierstrassCurve.Affine.Point.{0} (WeierstrassCurve.toAffine.{0} B))) :
  Eq.{1}
    ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.completionKummerClass F B a)
      (HSMul.hSMul.{0, 0, 0} r x))
    (HSMul.hSMul.{0, 0, 0} ((PadicInt.toZModPow a) r).val
      ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.completionKummerClass F B a) x))
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.completionKummerClass_smul' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.basedKummerOne_reduction

Source line: 1963.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.basedKummerOne_reduction (F : Type) [Field.{0} F]
  [CharZero.{0} F] [DecidableEq.{1} F] (B : WeierstrassCurve.{0} F) [WeierstrassCurve.IsElliptic.{0} B] (r : ℕ)
  (g :
    LinearMap.{0, 0, 0, 0} (RingHom.id.{0} ℤ_[2]) (Fin r → ℤ_[2])
      (ZInQ.Contrib.RC53Assist.DerivedKummerActual.PointCompletion.{0}
        (WeierstrassCurve.Affine.Point.{0} (WeierstrassCurve.toAffine.{0} B))))
  (a : ℕ) (u : Fin r → ℤ_[2]) :
  Eq.{1}
    ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualH1Reduction F B a)
      ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.basedKummerOne F B r g) u))
    ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.completionKummerClass F B a) (g u))
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.basedKummerOne_reduction' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.integral_one_boundary_of_finite_boundaries

Source line: 1991.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.integral_one_boundary_of_finite_boundaries (G A : Type)
  [Group.{0} G] [TopologicalSpace.{0} G] [IsTopologicalGroup.{0} G] [AddCommGroup.{0} A] [DistribMulAction.{0, 0} G A]
  [TopologicalSpace.{0} A] [DiscreteTopology.{0} A] [ContinuousSMul.{0, 0} G A]
  [CompactSpace.{0} (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.IntegralTateCoeff G A)]
  (hproj :
    ∀ (a : ℕ),
      Function.Surjective.{1, 1}
        ⇑(ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.coefficientProjection G A a))
  (c :
    ↑(HomologicalComplex.X.{0, 1, 0} (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.integralComplex G A)
        1))
  (hzero :
    ∀ (a : ℕ),
      ∃ b,
        Eq.{1}
          ((ModuleCat.Hom.hom.{0, 0}
              (HomologicalComplex.d.{0, 1, 0}
                (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.finiteIntegralComplex G A a) 0 1))
            b)
          ((ModuleCat.Hom.hom.{0, 0}
              (HomologicalComplex.Hom.f.{0, 1, 0}
                (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.reduceCochains G A a) 1))
            c)) :
  ∃ b,
    Eq.{1}
      ((ModuleCat.Hom.hom.{0, 0}
          (HomologicalComplex.d.{0, 1, 0}
            (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.integralComplex G A) 0 1))
        b)
      c
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.integral_one_boundary_of_finite_boundaries' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.geometricLevel_card

Source line: 2049.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.geometricLevel_card (F : Type) [Field.{0} F] [CharZero.{0} F]
  [DecidableEq.{1} F] (B : WeierstrassCurve.{0} F) [WeierstrassCurve.IsElliptic.{0} B] (a : ℕ) :
  Eq.{1} (Nat.card.{0} (TauCeti.TateModuleLevel.{0} 2 (ZInQ.Manuscript.RC.CoefModules.PtAlg F B) a))
    (HPow.hPow.{0, 0, 0} (HPow.hPow.{0, 0, 0} 2 a) 2)
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.geometricLevel_card' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.actualCoefficientProjection_surjective

Source line: 2058.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.actualCoefficientProjection_surjective (F : Type)
  [Field.{0} F] [CharZero.{0} F] [DecidableEq.{1} F] (B : WeierstrassCurve.{0} F) [WeierstrassCurve.IsElliptic.{0} B]
  (a : ℕ) :
  Function.Surjective.{1, 1}
    ⇑(ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.coefficientProjection
        (Field.absoluteGaloisGroup.{0} F) (ZInQ.Manuscript.RC.CoefModules.PtAlg F B) a)
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.actualCoefficientProjection_surjective' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.actualIntegralCoeff_compact

Source line: 2064.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.actualIntegralCoeff_compact (F : Type) [Field.{0} F]
  [CharZero.{0} F] [DecidableEq.{1} F] (B : WeierstrassCurve.{0} F) [WeierstrassCurve.IsElliptic.{0} B] :
  CompactSpace.{0}
    (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.IntegralTateCoeff (Field.absoluteGaloisGroup.{0} F)
      (ZInQ.Manuscript.RC.CoefModules.PtAlg F B))
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.actualIntegralCoeff_compact' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.actualH1Reduction_eq_zero_iff

Source line: 2071.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.actualH1Reduction_eq_zero_iff (F : Type) [Field.{0} F]
  [CharZero.{0} F] [DecidableEq.{1} F] (B : WeierstrassCurve.{0} F) [WeierstrassCurve.IsElliptic.{0} B] (a : ℕ)
  (c :
    ↥(LinearMap.ker.{0, 0, 0, 0}
        (ModuleCat.Hom.hom.{0, 0}
          (HomologicalComplex.d.{0, 1, 0}
            (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualIntegralComplex F B) 1 2)))) :
  Eq.{1} ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualH1Reduction F B a) c) 0 ↔
    Eq.{1}
      (ZInQ.Manuscript.RC.SelmerComplex.kerToH1
        ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.reduceOneCycle (Field.absoluteGaloisGroup.{0} F)
            (ZInQ.Manuscript.RC.CoefModules.PtAlg F B) a)
          c))
      0
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.actualH1Reduction_eq_zero_iff' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.actualH1Reduction_all_zero_iff_boundary

Source line: 2080.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.actualH1Reduction_all_zero_iff_boundary (F : Type)
  [Field.{0} F] [CharZero.{0} F] [DecidableEq.{1} F] (B : WeierstrassCurve.{0} F) [WeierstrassCurve.IsElliptic.{0} B]
  (c :
    ↥(LinearMap.ker.{0, 0, 0, 0}
        (ModuleCat.Hom.hom.{0, 0}
          (HomologicalComplex.d.{0, 1, 0}
            (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualIntegralComplex F B) 1 2)))) :
  (∀ (a : ℕ), Eq.{1} ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualH1Reduction F B a) c) 0) ↔
    ∃ b,
      Eq.{1}
        ((ModuleCat.Hom.hom.{0, 0}
            (HomologicalComplex.d.{0, 1, 0}
              (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualIntegralComplex F B) 0 1))
          b)
        ↑c
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.actualH1Reduction_all_zero_iff_boundary' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.basedKummerOne_relation

Source line: 2101.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.basedKummerOne_relation (F : Type) [Field.{0} F]
  [CharZero.{0} F] [DecidableEq.{1} F] (B : WeierstrassCurve.{0} F) [WeierstrassCurve.IsElliptic.{0} B] (r1 r0 : ℕ)
  (f : LinearMap.{0, 0, 0, 0} (RingHom.id.{0} ℤ_[2]) (Fin r1 → ℤ_[2]) (Fin r0 → ℤ_[2]))
  (g :
    LinearMap.{0, 0, 0, 0} (RingHom.id.{0} ℤ_[2]) (Fin r0 → ℤ_[2])
      (ZInQ.Contrib.RC53Assist.DerivedKummerActual.PointCompletion.{0}
        (WeierstrassCurve.Affine.Point.{0} (WeierstrassCurve.toAffine.{0} B))))
  (hfg : Eq.{1} (g ∘ₗ f) 0) (u : Fin r1 → ℤ_[2]) :
  ∃ b,
    Eq.{1}
      ((ModuleCat.Hom.hom.{0, 0}
          (HomologicalComplex.d.{0, 1, 0}
            (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualIntegralComplex F B) 0 1))
        b)
      ↑((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.basedKummerOne F B r0 g) (f u))
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.basedKummerOne_relation' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.relationPrimitive_d

Source line: 2122.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.relationPrimitive_d (F : Type) [Field.{0} F] [CharZero.{0} F]
  [DecidableEq.{1} F] (B : WeierstrassCurve.{0} F) [WeierstrassCurve.IsElliptic.{0} B] (r1 r0 : ℕ)
  (f : LinearMap.{0, 0, 0, 0} (RingHom.id.{0} ℤ_[2]) (Fin r1 → ℤ_[2]) (Fin r0 → ℤ_[2]))
  (g :
    LinearMap.{0, 0, 0, 0} (RingHom.id.{0} ℤ_[2]) (Fin r0 → ℤ_[2])
      (ZInQ.Contrib.RC53Assist.DerivedKummerActual.PointCompletion.{0}
        (WeierstrassCurve.Affine.Point.{0} (WeierstrassCurve.toAffine.{0} B))))
  (hfg : Eq.{1} (g ∘ₗ f) 0) (u : Fin r1 → ℤ_[2]) :
  Eq.{1}
    ((ModuleCat.Hom.hom.{0, 0}
        (HomologicalComplex.d.{0, 1, 0}
          (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualIntegralComplex F B) 0 1))
      (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.relationPrimitive F B r1 r0 f g hfg u))
    ↑((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.basedKummerOne F B r0 g) (f u))
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.relationPrimitive_d' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.basedKummerZero_d

Source line: 2139.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.basedKummerZero_d (F : Type) [Field.{0} F] [CharZero.{0} F]
  [DecidableEq.{1} F] (B : WeierstrassCurve.{0} F) [WeierstrassCurve.IsElliptic.{0} B] (r1 r0 : ℕ)
  (f : LinearMap.{0, 0, 0, 0} (RingHom.id.{0} ℤ_[2]) (Fin r1 → ℤ_[2]) (Fin r0 → ℤ_[2]))
  (g :
    LinearMap.{0, 0, 0, 0} (RingHom.id.{0} ℤ_[2]) (Fin r0 → ℤ_[2])
      (ZInQ.Contrib.RC53Assist.DerivedKummerActual.PointCompletion.{0}
        (WeierstrassCurve.Affine.Point.{0} (WeierstrassCurve.toAffine.{0} B))))
  (hfg : Eq.{1} (g ∘ₗ f) 0) (u : Fin r1 → ℤ_[2]) :
  Eq.{1}
    ((ModuleCat.Hom.hom.{0, 0}
        (HomologicalComplex.d.{0, 1, 0}
          (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualIntegralComplex F B) 0 1))
      ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.basedKummerZero F B r1 r0 f g hfg) u))
    ↑((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.basedKummerOne F B r0 g) (f u))
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.basedKummerZero_d' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.actualLocalKummerZero_d

Source line: 2184.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.actualLocalKummerZero_d (K : Type) [Field.{0} K]
  [NumberField.{0} K] (w : IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))
  [DecidableEq.{1} (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} K w)]
  (B : WeierstrassCurve.{0} (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} K w))
  [WeierstrassCurve.IsElliptic.{0} B]
  (u :
    Fin
        (ZInQ.Contrib.RC53Assist.DerivedKummerActual.FinitePointPresentation.rankOne.{0}
          (ZInQ.Contrib.RC53Assist.DerivedKummerActual.actualLocalPresentation K w B)) →
      ℤ_[2]) :
  Eq.{1}
    ((ModuleCat.Hom.hom.{0, 0}
        (HomologicalComplex.d.{0, 1, 0}
          (ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction.actualIntegralComplex
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} K w) B)
          0 1))
      ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.actualLocalKummerZero K w B) u))
    ↑((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.actualLocalKummerOne K w B)
        ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.FinitePointPresentation.f.{0}
            (ZInQ.Contrib.RC53Assist.DerivedKummerActual.actualLocalPresentation K w B))
          u))
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.actualLocalKummerZero_d' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.actualLocalReduction_apply

Source line: 2199.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.actualLocalReduction_apply (K : Type) [Field.{0} K]
  [NumberField.{0} K] (w : IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))
  [DecidableEq.{1} (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} K w)]
  (B : WeierstrassCurve.{0} (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} K w))
  [WeierstrassCurve.IsElliptic.{0} B] (a : ℕ)
  (u :
    Fin
        (ZInQ.Contrib.RC53Assist.DerivedKummerActual.FinitePointPresentation.rankZero.{0}
          (ZInQ.Contrib.RC53Assist.DerivedKummerActual.actualLocalPresentation K w B)) →
      ℤ_[2]) :
  Eq.{1} ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.actualLocalReduction K w B a) u)
    ((WeierstrassCurve.kummerMap.{0} B (HPow.hPow.{0, 0, 0} 2 a)
        (isUnit_iff_ne_zero.{0}.mpr
          (ZInQ.Manuscript.RC.CoefModules.natCast_ne_zero_of_charZero
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} K w) (HPow.hPow.{0, 0, 0} 2 a))))
      (↑(ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.representatives.{0}
            (WeierstrassCurve.Affine.Point.{0} (WeierstrassCurve.toAffine.{0} B))
            ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.FinitePointPresentation.g.{0}
                (ZInQ.Contrib.RC53Assist.DerivedKummerActual.actualLocalPresentation K w B))
              u))
        a))
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.actualLocalReduction_apply' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.actualLocalReduction_mem_genuine_Kummer

Source line: 2212.

```lean
ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.actualLocalReduction_mem_genuine_Kummer (K : Type)
  [Field.{0} K] [NumberField.{0} K] (w : IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))
  [DecidableEq.{1} (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} K w)]
  (B : WeierstrassCurve.{0} (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} K w))
  [WeierstrassCurve.IsElliptic.{0} B] (a : ℕ)
  (u :
    Fin
        (ZInQ.Contrib.RC53Assist.DerivedKummerActual.FinitePointPresentation.rankZero.{0}
          (ZInQ.Contrib.RC53Assist.DerivedKummerActual.actualLocalPresentation K w B)) →
      ℤ_[2]) :
  Membership.mem.{0, 0}
    (AddMonoidHom.range.{0, 0}
      (WeierstrassCurve.kummerMap.{0} B (HPow.hPow.{0, 0, 0} 2 a)
        (isUnit_iff_ne_zero.{0}.mpr
          (ZInQ.Manuscript.RC.CoefModules.natCast_ne_zero_of_charZero
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} K w) (HPow.hPow.{0, 0, 0} 2 a)))))
    ((ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.actualLocalReduction K w B a) u)
```

```text
'ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer.actualLocalReduction_mem_genuine_Kummer' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```
