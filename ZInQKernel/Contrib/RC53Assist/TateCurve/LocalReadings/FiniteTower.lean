import ZInQKernel.Contrib.RC53Assist.TateCurve.LocalReadings.FiniteExtensions

/-!
# Inertia restriction in finite local towers

For finite Galois subextensions `E ≤ M`, restriction carries the inertia group
of `M` onto that of `E`. The proof is the finite ring-theoretic inertia theorem,
with the actual integral closures and their field-compatible actions.

Kinds: definitions and proved statements only.
Locators: Serre, *Local Fields*, III, §5; finite Galois inertia restriction.
These refer to the book, not the chapter in Cassels--Fröhlich.
-/

noncomputable section

set_option maxHeartbeats 800000

namespace ZInQ.Contrib.RC53Assist.TateCurve

open ZInQ.Contrib.RC53Assist.GlobalTrace
open scoped WithZero

section Fields

variable {p : ℕ} {hp : p.Prime}

/-- **DEFINITION**: the field algebra structure given by a finite-subfield inclusion.
Locator: the intermediate-field inclusion homomorphism. -/
@[instance_reducible]
def finiteLocalFieldAlgebra (E M : LocalFiniteQ p hp) (h : E ≤ M) : Algebra E M :=
  (IntermediateField.inclusion h).toRingHom.toAlgebra

/-- **PROVED**: the inclusion respects the base-field algebra structures.
Locator: its commuting square. -/
theorem finiteLocalField_scalarTower (E M : LocalFiniteQ p hp) (h : E ≤ M) :
    letI := finiteLocalFieldAlgebra E M h
    IsScalarTower (LocalBaseQ p hp) E M := by
  letI := finiteLocalFieldAlgebra E M h
  exact IsScalarTower.of_algebraMap_eq fun a =>
    ((IntermediateField.inclusion h).commutes a).symm

/-- **PROVED**: the inclusions into the algebraic closure form a scalar tower.
Locator: the same underlying element of the two intermediate subfields. -/
theorem finiteLocalField_closureTower (E M : LocalFiniteQ p hp) (h : E ≤ M) :
    letI := finiteLocalFieldAlgebra E M h
    IsScalarTower E M (LocalClosureQ p hp) := by
  letI := finiteLocalFieldAlgebra E M h
  exact IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- **DEFINITION**: the finite restriction homomorphism along `E ≤ M`.
Locator: restriction to a normal subfield. -/
def finiteLocalRestrict (E M : LocalFiniteQ p hp) (h : E ≤ M) :
    (M ≃ₐ[LocalBaseQ p hp] M) →* (E ≃ₐ[LocalBaseQ p hp] E) := by
  letI := finiteLocalFieldAlgebra E M h
  haveI := finiteLocalField_scalarTower E M h
  exact AlgEquiv.restrictNormalHom E

/-- **PROVED**: finite restriction is onto. Locator: normal extension of automorphisms. -/
theorem finiteLocalRestrict_surjective (E M : LocalFiniteQ p hp) (h : E ≤ M) :
    Function.Surjective (finiteLocalRestrict E M h) := by
  letI := finiteLocalFieldAlgebra E M h
  haveI := finiteLocalField_scalarTower E M h
  exact AlgEquiv.restrictNormalHom_surjective M

/-- **PROVED**: successive finite and absolute restrictions commute.
Locator: the characterizing commuting squares for restrictions. -/
theorem finiteLocalRestrict_comp (E M : LocalFiniteQ p hp) (h : E ≤ M) :
    (finiteLocalRestrict E M h).comp
      (AlgEquiv.restrictNormalHom M : LocalGaloisQ p hp →* (M ≃ₐ[LocalBaseQ p hp] M)) =
        AlgEquiv.restrictNormalHom E := by
  letI := finiteLocalFieldAlgebra E M h
  haveI := finiteLocalField_scalarTower E M h
  haveI := finiteLocalField_closureTower E M h
  apply MonoidHom.ext
  intro σ
  apply AlgEquiv.ext
  intro x
  apply (algebraMap E (LocalClosureQ p hp)).injective
  have hEM : algebraMap E M
      (finiteLocalRestrict E M h (AlgEquiv.restrictNormalHom M σ) x) =
        AlgEquiv.restrictNormalHom M σ (algebraMap E M x) :=
    AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictNormalHom M σ) E x
  calc
    algebraMap E (LocalClosureQ p hp)
        (finiteLocalRestrict E M h (AlgEquiv.restrictNormalHom M σ) x) =
      algebraMap M (LocalClosureQ p hp) (algebraMap E M
        (finiteLocalRestrict E M h (AlgEquiv.restrictNormalHom M σ) x)) :=
          IsScalarTower.algebraMap_apply E M (LocalClosureQ p hp) _
    _ = algebraMap M (LocalClosureQ p hp)
        (AlgEquiv.restrictNormalHom M σ (algebraMap E M x)) := congrArg _ hEM
    _ = σ (algebraMap M (LocalClosureQ p hp) (algebraMap E M x)) :=
      AlgEquiv.restrictNormal_commutes σ M _
    _ = σ (algebraMap E (LocalClosureQ p hp) x) := by
      rw [← IsScalarTower.algebraMap_apply]
    _ = algebraMap E (LocalClosureQ p hp) (AlgEquiv.restrictNormalHom E σ x) :=
      (AlgEquiv.restrictNormal_commutes σ E x).symm

/-- **PROVED**: restriction from the absolute Galois group to a finite stage is
continuous. Locator: finite element lifts for the Krull topology. -/
theorem localFiniteRestriction_continuous (E : LocalFiniteQ p hp) :
    Continuous (AlgEquiv.restrictNormalHom E :
      LocalGaloisQ p hp →* (E ≃ₐ[LocalBaseQ p hp] E)) := by
  apply continuous_galoisHom_of_element_lifts
  intro y
  refine ⟨algebraMap E (LocalClosureQ p hp) y, fun σ hσ => ?_⟩
  apply (algebraMap E (LocalClosureQ p hp)).injective
  exact (AlgEquiv.restrictNormal_commutes σ E y).trans hσ

end Fields

section Integers

variable (p : ℕ) (hp : p.Prime) (Γ : Type) [LinearOrderedCommGroupWithZero Γ]
variable (w : Valuation (LocalClosureQ p hp) Γ)
variable (hw : (w.comap (algebraMap (LocalBaseQ p hp) (LocalClosureQ p hp))).IsEquiv
  (Valued.v : Valuation (LocalBaseQ p hp) ℤᵐ⁰))

include hw

/-- **DEFINITION**: the integer-ring algebra structure in a finite tower.
Locator: the equal restricted valuations on the common algebraic closure. -/
@[instance_reducible]
def finiteLocalTowerIntegerAlgebra (E M : LocalFiniteQ p hp) (h : E ≤ M) :
    Algebra (finiteLocalIntegers w E) (finiteLocalIntegers w M) := by
  letI := finiteLocalFieldAlgebra E M h
  haveI : (finiteLocalValuation w E).HasExtension (finiteLocalValuation w M) :=
    ⟨fun _ _ => Iff.rfl⟩
  exact Valuation.HasExtension.instAlgebra_valuationSubring
    (finiteLocalValuation w E) (finiteLocalValuation w M)

/-- **PROVED**: inertia restricts onto inertia in a finite local Galois tower.
Locator: the finite ring-theoretic inertia restriction theorem. -/
theorem finiteLocalInertia_map_of_le (E M : LocalFiniteQ p hp) (h : E ≤ M) :
    (finiteLocalInertia p hp Γ w hw M).map (finiteLocalRestrict E M h) =
      finiteLocalInertia p hp Γ w hw E := by
  letI := finiteLocalFieldAlgebra E M h
  haveI := finiteLocalField_scalarTower E M h
  haveI := finiteLocalField_closureTower E M h
  haveI : FaithfulSMul E M :=
    (faithfulSMul_iff_algebraMap_injective E M).mpr (algebraMap E M).injective
  letI : Algebra (finiteLocalIntegers w E) M :=
    ((algebraMap E M).comp (algebraMap (finiteLocalIntegers w E) E)).toAlgebra
  haveI : IsScalarTower (finiteLocalIntegers w E) E M :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (LocalBaseIntegersQ p hp) E M :=
    IsScalarTower.to₁₃₄ (LocalBaseIntegersQ p hp) (LocalBaseQ p hp) E M
  letI := finiteLocalIntegerAlgebra p hp Γ w hw E
  letI := finiteLocalIntegerAlgebra p hp Γ w hw M
  haveI := finiteLocalInteger_scalarTower p hp Γ w hw E
  haveI := finiteLocalInteger_scalarTower p hp Γ w hw M
  haveI := finiteLocal_integer_isIntegralClosure p hp Γ w hw E
  haveI := finiteLocal_integer_isIntegralClosure p hp Γ w hw M
  haveI := finiteLocal_integer_isDVR p hp Γ w hw E
  haveI : Algebra.IsIntegral (LocalBaseIntegersQ p hp) (finiteLocalIntegers w E) :=
    IsIntegralClosure.isIntegral_algebra (LocalBaseIntegersQ p hp) E
  haveI : Algebra.IsIntegral (LocalBaseIntegersQ p hp) (finiteLocalIntegers w M) :=
    IsIntegralClosure.isIntegral_algebra (LocalBaseIntegersQ p hp) M
  haveI : (finiteLocalValuation w E).HasExtension (finiteLocalValuation w M) :=
    ⟨fun _ _ => Iff.rfl⟩
  letI := finiteLocalTowerIntegerAlgebra p hp Γ w E M h
  haveI : IsScalarTower (finiteLocalIntegers w E) (finiteLocalIntegers w M) M :=
    Valuation.HasExtension.instIsScalarTower_valuationSubring'
      (finiteLocalValuation w E) (finiteLocalValuation w M)
  haveI : IsScalarTower (LocalBaseIntegersQ p hp)
      (finiteLocalIntegers w E) (finiteLocalIntegers w M) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI := finiteLocalIntegerAction p hp Γ w hw E
  letI := finiteLocalIntegerAction p hp Γ w hw M
  haveI : SMulDistribClass (M ≃ₐ[LocalBaseQ p hp] M) (finiteLocalIntegers w M) M :=
    inferInstance
  let H := fixingSubgroup (M ≃ₐ[LocalBaseQ p hp] M) (Set.range (algebraMap E M))
  haveI : IsGaloisGroup H E M :=
    IsGaloisGroup.of_isScalarTower (M ≃ₐ[LocalBaseQ p hp] M) (LocalBaseQ p hp) M E
  haveI : Algebra.IsIntegral (finiteLocalIntegers w E) (finiteLocalIntegers w M) :=
    Algebra.IsIntegral.tower_top (LocalBaseIntegersQ p hp)
  haveI : IsScalarTower (finiteLocalIntegers w E) E M :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsGaloisGroup H (finiteLocalIntegers w E) (finiteLocalIntegers w M) :=
    IsGaloisGroup.of_isFractionRing H _ _ E M
  haveI : Algebra.IsInvariant (finiteLocalIntegers w E) (finiteLocalIntegers w M) H :=
    inferInstance
  haveI : IsLocalHom (algebraMap (finiteLocalIntegers w E) (finiteLocalIntegers w M)) :=
    inferInstance
  let P : Ideal (finiteLocalIntegers w E) := IsLocalRing.maximalIdeal _
  let Q : Ideal (finiteLocalIntegers w M) := IsLocalRing.maximalIdeal _
  haveI : Q.LiesOver P := inferInstance
  let f := finiteLocalRestrict E M h
  have hfker : H ≤ f.ker := by
    intro g hg
    rw [MonoidHom.mem_ker]
    apply AlgEquiv.ext
    intro x
    apply (algebraMap E M).injective
    have hfix : g (algebraMap E M x) = algebraMap E M x :=
      (mem_fixingSubgroup_iff (M ≃ₐ[LocalBaseQ p hp] M)).mp hg _ ⟨x, rfl⟩
    exact (AlgEquiv.restrictNormal_commutes g E x).trans hfix
  have hf : ∀ (g : M ≃ₐ[LocalBaseQ p hp] M) (x : finiteLocalIntegers w E),
      algebraMap (finiteLocalIntegers w E) (finiteLocalIntegers w M) (f g • x) =
        g • algebraMap (finiteLocalIntegers w E) (finiteLocalIntegers w M) x := by
    intro g x
    apply IsFractionRing.injective (finiteLocalIntegers w M) M
    change algebraMap E M ((f g • x : finiteLocalIntegers w E) : E) =
      ((g • algebraMap (finiteLocalIntegers w E) (finiteLocalIntegers w M) x :
        finiteLocalIntegers w M) : M)
    rw [finiteLocalIntegerAction_coe, finiteLocalIntegerAction_coe]
    exact AlgEquiv.restrictNormal_commutes g E (x : E)
  exact Ideal.map_inertia_of_surjective f H P Q
    (finiteLocalRestrict_surjective E M h) hfker hf

/-- **PROVED**: an absolute automorphism which is inertial at a larger finite
stage is inertial at every smaller stage. Locator: finite inertia restriction. -/
theorem absolute_restrict_inertia_of_le (E M : LocalFiniteQ p hp) (h : E ≤ M)
    (σ : LocalGaloisQ p hp)
    (hσ : AlgEquiv.restrictNormalHom M σ ∈ finiteLocalInertia p hp Γ w hw M) :
    AlgEquiv.restrictNormalHom E σ ∈ finiteLocalInertia p hp Γ w hw E := by
  have hf : finiteLocalRestrict E M h (AlgEquiv.restrictNormalHom M σ) ∈
      (finiteLocalInertia p hp Γ w hw M).map (finiteLocalRestrict E M h) :=
    Subgroup.mem_map.mpr ⟨AlgEquiv.restrictNormalHom M σ, hσ, rfl⟩
  rw [finiteLocalInertia_map_of_le p hp Γ w hw E M h] at hf
  have hcomp := congrArg (fun f : LocalGaloisQ p hp →* (E ≃ₐ[LocalBaseQ p hp] E) => f σ)
    (finiteLocalRestrict_comp E M h)
  change finiteLocalRestrict E M h (AlgEquiv.restrictNormalHom M σ) =
    AlgEquiv.restrictNormalHom E σ at hcomp
  rwa [hcomp] at hf

end Integers

end ZInQ.Contrib.RC53Assist.TateCurve
