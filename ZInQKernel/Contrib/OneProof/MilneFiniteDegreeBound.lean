import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import ZInQKernel.Contrib.CloudB3RC53.ContBridge.Discrete
import ZInQKernel.Contrib.RC53Assist.DerivedKummerActual.Resolution
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Local.CohomologicalDimension.AbsoluteGaloisGroup

/-!
# Higher-degree exactness of the actual finite Tate cochains

Both coefficient families are killed by a power of two at each finite level.
The local cohomological-dimension bound therefore makes every cocycle above
degree two a coboundary in the actual continuous cochain complex.
-/

set_option autoImplicit false

namespace ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteLocalDegreeBound

open CategoryTheory TauCeti
open ZInQ.Contrib.CloudB3RC53.ContBridge
  (contCohomologyLinearEquiv continuousSMul_of_discrete)
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteSupport (FiniteHigherExact)
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction
  (FiniteTateCoeff finiteIntegralComplex)

/-- The two-adic scalar action on the finite level factors through a discrete residue ring. -/
private theorem finiteContinuousScalar (G A : Type) [AddCommGroup A] (a : ℕ) :
    ContinuousSMul ℤ_[2] (FiniteTateCoeff G A a) := by
  letI := continuousSMul_of_discrete (ZMod (2 ^ a)) (FiniteTateCoeff G A a)
  refine ⟨?_⟩
  change Continuous (fun p : ℤ_[2] × FiniteTateCoeff G A a =>
    PadicInt.toZModPow a p.1 • p.2)
  exact ((PadicInt.continuous_toZModPow a).comp continuous_fst).smul continuous_snd

private theorem finiteHigherExact_of_cd_le_two (G A : Type)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [AddCommGroup A] [DistribMulAction G A] [TopologicalSpace A] [DiscreteTopology A]
    [ContinuousSMul G A] (hcd : CohomologicalDimensionLE.{0} 2 G 2) :
    FiniteHigherExact G A := by
  intro a k z hz
  let M := FiniteTateCoeff G A a
  letI : ContinuousSMul ℤ_[2] M := finiteContinuousScalar G A a
  have hprimary : IsPPrimaryTorsion 2 M :=
    isPPrimaryTorsion_iff.mpr fun x => ⟨a, finite_level_killed G A a x⟩
  have hdegree : 2 < k + 3 := by omega
  let X := ofDiscreteModule ℤ_[2] G M
  letI : Subsingleton (continuousCohomology (k + 3) X) :=
    (ContCohomology.subsingleton_continuousCohomology_ofDiscreteModule_iff X (k + 3)).mp
      (hcd M hprimary (k + 3) hdegree)
  let C := finiteIntegralComplex G A a
  letI : Subsingleton (C.homology (k + 3)) :=
    (contCohomologyLinearEquiv ℤ_[2] G M (k + 3)).symm.injective.subsingleton
  have hexact : C.ExactAt (k + 3) :=
    (C.exactAt_iff_isZero_homology (k + 3)).mpr (ModuleCat.isZero_of_subsingleton _)
  rw [HomologicalComplex.exactAt_iff' C (k + 2) (k + 3) (k + 4) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff] at hexact
  exact hexact z hz

/-- TauCeti's local cohomological-dimension bound supplies both finite support fields. -/
theorem milneFiniteDegreeBoundPrint_proof : MilneFiniteDegreeBoundPrint := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · intro F _ _ _ _ _ _ B _
    apply finiteHigherExact_of_cd_le_two
    exact (cohomologicalDimensionAt_le_iff 2 (Field.absoluteGaloisGroup F) 2).mp
      (ClassFieldTheory.cohomologicalDimensionAt_absoluteGaloisGroup_eq_two (K := F) 2).le
  · intro F _ _ _ _ _ _
    haveI : LocallyCompactSpace (AbsoluteGaloisGroup F) := by
      haveI : R1Space (AbsoluteGaloisGroup F) := @T2Space.r1Space _ _ krullTopology_t2
      haveI : WeaklyLocallyCompactSpace (AbsoluteGaloisGroup F) :=
        ⟨fun _ ↦ ⟨Set.univ, isCompact_univ, Filter.univ_mem⟩⟩
      exact WeaklyLocallyCompactSpace.locallyCompactSpace
    apply finiteHigherExact_of_cd_le_two
    have hunit : IsUnit (2 : F) := (show (2 : F) ≠ 0 by norm_num).isUnit
    exact (cohomologicalDimensionAt_le_iff 2 (AbsoluteGaloisGroup F) 2).mp
      (ClassFieldTheory.cohomologicalDimensionAt_absoluteGaloisGroup_le_two (ℓ := 2) hunit)

end ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteLocalDegreeBound
