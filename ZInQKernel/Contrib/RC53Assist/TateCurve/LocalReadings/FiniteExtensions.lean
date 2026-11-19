import ZInQKernel.Contrib.RC53Assist.TateCurve.LocalReadings.LocalFrobenius

/-!
# Finite local extensions and their inertia

The restricted valuation ring of a finite Galois subextension is the integral
closure of the base DVR. It is finite, free over the base, and a DVR. Its inertia
is defined using the actual action on this integral closure, not an arbitrary
subgroup. Restriction of absolute inertia takes values in finite inertia.

Kinds: definitions and proved statements only.
Locators: Serre, *Local Fields*, II, §2 and III, §5; the finite inertia definition.
These refer to the book, not Serre's chapter in Cassels--Fröhlich.
-/

noncomputable section

set_option maxHeartbeats 800000

namespace ZInQ.Contrib.RC53Assist.TateCurve

open ZInQ.Contrib.RC53Assist.DecompositionGlue
open ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary
open ZInQ.Contrib.RC53Assist.GlobalTrace
open scoped WithZero

/-- **DEFINITION**: finite Galois subextensions of the local algebraic closure. -/
abbrev LocalFiniteQ (p : ℕ) (hp : p.Prime) :=
  FiniteGaloisIntermediateField (LocalBaseQ p hp) (LocalClosureQ p hp)

/-- **DEFINITION**: restriction of the specified valuation to a finite subextension. -/
abbrev finiteLocalValuation {p : ℕ} {hp : p.Prime} {Γ : Type}
    [LinearOrderedCommGroupWithZero Γ] (w : Valuation (LocalClosureQ p hp) Γ)
    (E : LocalFiniteQ p hp) : Valuation E Γ :=
  w.comap E.toIntermediateField.val.toRingHom

/-- **DEFINITION**: the ring of integers of that restricted valuation. -/
abbrev finiteLocalIntegers {p : ℕ} {hp : p.Prime} {Γ : Type}
    [LinearOrderedCommGroupWithZero Γ] (w : Valuation (LocalClosureQ p hp) Γ)
    (E : LocalFiniteQ p hp) := (finiteLocalValuation w E).valuationSubring

section Finite

variable (p : ℕ) (hp : p.Prime) (Γ : Type) [LinearOrderedCommGroupWithZero Γ]
variable (w : Valuation (LocalClosureQ p hp) Γ)
variable (hw : (w.comap (algebraMap (LocalBaseQ p hp) (LocalClosureQ p hp))).IsEquiv
  (Valued.v : Valuation (LocalBaseQ p hp) ℤᵐ⁰))

include hw

/-- **PROVED**: the restricted valuation extends the base valuation.
Locator: compatibility of the intermediate-field embeddings. -/
theorem finiteLocal_hasExtension (E : LocalFiniteQ p hp) :
    (Valued.v : Valuation (LocalBaseQ p hp) ℤᵐ⁰).HasExtension (finiteLocalValuation w E) := by
  constructor
  have he : (finiteLocalValuation w E).comap (algebraMap (LocalBaseQ p hp) E) =
      w.comap (algebraMap (LocalBaseQ p hp) (LocalClosureQ p hp)) := by
    ext a
    change w (E.toIntermediateField.val (algebraMap (LocalBaseQ p hp) E a)) =
      w (algebraMap (LocalBaseQ p hp) (LocalClosureQ p hp) a)
    exact congrArg w (E.toIntermediateField.val.commutes a)
  rw [he]
  exact hw.symm

/-- **PROVED**: the finite valuation ring is an integral closure of the base DVR.
Locator: integrality reflected along its embedding into the algebraic closure. -/
theorem finiteLocal_integer_isIntegralClosure (E : LocalFiniteQ p hp) :
    IsIntegralClosure (finiteLocalIntegers w E) (LocalBaseIntegersQ p hp) E where
  algebraMap_injective := Subtype.val_injective
  isIntegral_iff := by
    intro x
    have he : IsIntegral (LocalBaseIntegersQ p hp) (E.toIntermediateField.val x) ↔
        IsIntegral (LocalBaseIntegersQ p hp) x :=
      isIntegral_algHom_iff (E.toIntermediateField.val.restrictScalars
        (LocalBaseIntegersQ p hp)) E.toIntermediateField.val.injective
    rw [← he, local_integral_iff_le_one p hp Γ w hw]
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact y.2

/-- **DEFINITION**: the base-DVR algebra structure on the finite integer ring.
Locator: the restricted valuation extension. -/
@[instance_reducible]
def finiteLocalIntegerAlgebra (E : LocalFiniteQ p hp) :
    Algebra (LocalBaseIntegersQ p hp) (finiteLocalIntegers w E) := by
  let v : Valuation (LocalBaseQ p hp) ℤᵐ⁰ := Valued.v
  letI : v.HasExtension (finiteLocalValuation w E) := finiteLocal_hasExtension p hp Γ w hw E
  exact Valuation.HasExtension.instAlgebra_valuationSubring v (finiteLocalValuation w E)

/-- **PROVED**: the base and finite integer embeddings form a scalar tower.
Locator: their definitions as restrictions of the field embeddings. -/
theorem finiteLocalInteger_scalarTower (E : LocalFiniteQ p hp) :
    letI := finiteLocalIntegerAlgebra p hp Γ w hw E
    IsScalarTower (LocalBaseIntegersQ p hp) (finiteLocalIntegers w E) E := by
  letI := finiteLocalIntegerAlgebra p hp Γ w hw E
  exact IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- **PROVED**: the finite integer ring is finite over the base DVR.
Locator: finiteness of integral closure in a finite separable field extension. -/
theorem finiteLocal_integer_finite (E : LocalFiniteQ p hp) :
    letI := finiteLocalIntegerAlgebra p hp Γ w hw E
    Module.Finite (LocalBaseIntegersQ p hp) (finiteLocalIntegers w E) := by
  letI := finiteLocalIntegerAlgebra p hp Γ w hw E
  haveI := finiteLocalInteger_scalarTower p hp Γ w hw E
  haveI := finiteLocal_integer_isIntegralClosure p hp Γ w hw E
  exact IsIntegralClosure.finite (LocalBaseIntegersQ p hp) (LocalBaseQ p hp) E
    (finiteLocalIntegers w E)

/-- **PROVED**: the finite integer ring is a Dedekind domain.
Locator: integral closure of a Dedekind domain in a finite separable extension. -/
theorem finiteLocal_integer_isDedekindDomain (E : LocalFiniteQ p hp) :
    IsDedekindDomain (finiteLocalIntegers w E) := by
  letI := finiteLocalIntegerAlgebra p hp Γ w hw E
  haveI := finiteLocalInteger_scalarTower p hp Γ w hw E
  haveI := finiteLocal_integer_isIntegralClosure p hp Γ w hw E
  exact IsIntegralClosure.isDedekindDomain (LocalBaseIntegersQ p hp) (LocalBaseQ p hp) E
    (finiteLocalIntegers w E)

/-- **PROVED**: the finite integer ring is free over the base DVR.
Locator: torsion-free finite modules over a PID, or integral-closure freeness. -/
theorem finiteLocal_integer_free (E : LocalFiniteQ p hp) :
    letI := finiteLocalIntegerAlgebra p hp Γ w hw E
    Module.Free (LocalBaseIntegersQ p hp) (finiteLocalIntegers w E) := by
  letI := finiteLocalIntegerAlgebra p hp Γ w hw E
  haveI := finiteLocalInteger_scalarTower p hp Γ w hw E
  haveI := finiteLocal_integer_isIntegralClosure p hp Γ w hw E
  haveI : Module.IsTorsionFree (LocalBaseIntegersQ p hp) E :=
    Module.IsTorsionFree.trans_faithfulSMul (LocalBaseIntegersQ p hp) (LocalBaseQ p hp) E
  exact IsIntegralClosure.module_free (LocalBaseIntegersQ p hp) (LocalBaseQ p hp) E
    (finiteLocalIntegers w E)

/-- **PROVED**: the finite integer ring is a DVR, not a field.
Locator: a local nonfield Dedekind domain is a DVR; a base uniformizer stays a nonunit. -/
theorem finiteLocal_integer_isDVR (E : LocalFiniteQ p hp) :
    IsDiscreteValuationRing (finiteLocalIntegers w E) := by
  haveI := finiteLocal_integer_isDedekindDomain p hp Γ w hw E
  let v : Valuation (LocalBaseQ p hp) ℤᵐ⁰ := Valued.v
  letI : v.HasExtension (finiteLocalValuation w E) := finiteLocal_hasExtension p hp Γ w hw E
  have hNF : ¬ IsField (finiteLocalIntegers w E) := by
    intro hF
    letI := hF.toField
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.valuationSubring
    have hvπ : v (π : LocalBaseQ p hp) < 1 :=
      (Valuation.valuationSubring.integers v).valuation_irreducible_lt_one hπ
    let y : finiteLocalIntegers w E :=
      ⟨algebraMap (LocalBaseQ p hp) E (π : LocalBaseQ p hp),
        (Valuation.HasExtension.val_map_le_one_iff v (finiteLocalValuation w E) _).mpr π.2⟩
    have hπ0 : (π : LocalBaseQ p hp) ≠ 0 := Subtype.coe_injective.ne hπ.ne_zero
    have hy0 : y ≠ 0 := by
      intro hy
      apply hπ0
      apply (algebraMap (LocalBaseQ p hp) E).injective
      simpa only [y, ZeroMemClass.coe_zero, map_zero] using congrArg Subtype.val hy
    have hny : ¬ IsUnit y :=
      (Valuation.Integer.not_isUnit_iff_valuation_lt_one
        (v := finiteLocalValuation w E)).mpr
          ((Valuation.HasExtension.val_map_lt_one_iff v (finiteLocalValuation w E) _).mpr hvπ)
    exact hny (isUnit_iff_ne_zero.mpr hy0)
  exact ((IsDiscreteValuationRing.TFAE (finiteLocalIntegers w E) hNF).out 1 3 rfl rfl).mpr
    inferInstance

/-- **DEFINITION**: the genuine Galois action on the finite integral closure.
Locator: restriction of field automorphisms to integral elements. -/
@[instance_reducible]
def finiteLocalIntegerAction (E : LocalFiniteQ p hp) :
    MulSemiringAction (E ≃ₐ[LocalBaseQ p hp] E) (finiteLocalIntegers w E) := by
  letI := finiteLocalIntegerAlgebra p hp Γ w hw E
  haveI := finiteLocalInteger_scalarTower p hp Γ w hw E
  haveI := finiteLocal_integer_isIntegralClosure p hp Γ w hw E
  exact IsIntegralClosure.MulSemiringAction (LocalBaseIntegersQ p hp) (LocalBaseQ p hp) E
    (finiteLocalIntegers w E)

/-- **PROVED**: this action is the restriction of the displayed field automorphism.
Locator: the commuting square for integral-closure restriction. -/
theorem finiteLocalIntegerAction_coe (E : LocalFiniteQ p hp)
    (σ : E ≃ₐ[LocalBaseQ p hp] E) (y : finiteLocalIntegers w E) :
    letI := finiteLocalIntegerAction p hp Γ w hw E
    ((σ • y : finiteLocalIntegers w E) : E) = σ (y : E) := by
  letI := finiteLocalIntegerAlgebra p hp Γ w hw E
  haveI := finiteLocalInteger_scalarTower p hp Γ w hw E
  haveI := finiteLocal_integer_isIntegralClosure p hp Γ w hw E
  exact algebraMap_galRestrict_apply (LocalBaseIntegersQ p hp) σ y

/-- **DEFINITION**: inertia in a finite subextension, using its maximal ideal and
its actual integral-closure action. Locator: finite inertia acts trivially modulo the prime. -/
def finiteLocalInertia (E : LocalFiniteQ p hp) : Subgroup (E ≃ₐ[LocalBaseQ p hp] E) :=
  letI := finiteLocalIntegerAction p hp Γ w hw E
  (IsLocalRing.maximalIdeal (finiteLocalIntegers w E)).inertia (E ≃ₐ[LocalBaseQ p hp] E)

/-- **PROVED**: the finite inertia definition is the usual elementwise residue
condition. Locator: membership in inertia and in the valuation maximal ideal. -/
theorem mem_finiteLocalInertia (E : LocalFiniteQ p hp) (σ : E ≃ₐ[LocalBaseQ p hp] E) :
    σ ∈ finiteLocalInertia p hp Γ w hw E ↔
      ∀ x : E, finiteLocalValuation w E x ≤ 1 → finiteLocalValuation w E (σ x - x) < 1 := by
  letI := finiteLocalIntegerAction p hp Γ w hw E
  rw [finiteLocalInertia, Ideal.mem_inertia]
  constructor
  · intro h x hx
    have he := h (⟨x, hx⟩ : finiteLocalIntegers w E)
    rw [Valuation.mem_maximalIdeal_iff] at he
    change finiteLocalValuation w E
      (((σ • (⟨x, hx⟩ : finiteLocalIntegers w E) : finiteLocalIntegers w E) : E) - x) < 1 at he
    rwa [finiteLocalIntegerAction_coe] at he
  · intro h x
    rw [Valuation.mem_maximalIdeal_iff]
    change finiteLocalValuation w E (((σ • x : finiteLocalIntegers w E) : E) - (x : E)) < 1
    rw [finiteLocalIntegerAction_coe]
    exact h x x.2

/-- **PROVED**: restricting absolute inertia gives finite inertia.
Locator: the same residue congruence read along the finite-field embedding. -/
theorem localInertia_restrict_mem (E : LocalFiniteQ p hp) (σ : LocalGaloisQ p hp)
    (hσ : σ ∈ localInertia w) :
    AlgEquiv.restrictNormalHom E σ ∈ finiteLocalInertia p hp Γ w hw E := by
  apply (mem_finiteLocalInertia p hp Γ w hw E _).mpr
  intro x hx
  have hi := (mem_map_inertiaSubgroup_iff w.valuationSubring σ).mp hσ
  have hsmall := (mem_valuationSubring_nonunits_iff w).mp (hi.2
    (algebraMap E (LocalClosureQ p hp) x) hx)
  have hcomm : algebraMap E (LocalClosureQ p hp) (AlgEquiv.restrictNormalHom E σ x) =
      σ (algebraMap E (LocalClosureQ p hp) x) :=
    AlgEquiv.restrictNormal_commutes σ E x
  change w (algebraMap E (LocalClosureQ p hp) (AlgEquiv.restrictNormalHom E σ x - x)) < 1
  rw [map_sub, hcomm]
  exact hsmall

end Finite

end ZInQ.Contrib.RC53Assist.TateCurve
