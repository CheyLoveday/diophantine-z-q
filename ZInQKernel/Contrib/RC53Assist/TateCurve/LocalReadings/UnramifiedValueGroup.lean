import ZInQKernel.Contrib.RC53Assist.TateCurve.LocalReadings.InertiaRestriction

/-!
# Values of inertia-fixed algebraic elements

Finite inertia has cardinality equal to the ramification index. If absolute
inertia restricts onto finite inertia, every finite Galois subextension of its
fixed field has trivial inertia and ramification index one. The valuation
comparison at a prime lying over the base prime then gives the required base
value for every nonzero element.

The conditional reduction uses only finite inertia lifting, an assertion about
a restriction homomorphism rather than the value-group target. Finite inertia
lifting is proved by inverse-limit compactness, so the final theorem has no
remaining local-field hypothesis.

Kinds: proved statements and the explicitly named conditional implication.
Locators: Serre, *Local Fields*, III, §5; finite inertia cardinality and valuation
comparison at primes. This is the book, not Serre's chapter in Cassels--Fröhlich.
-/

noncomputable section

set_option maxHeartbeats 800000

namespace ZInQ.Contrib.RC53Assist.TateCurve

open ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary
open ZInQ.Contrib.RC53Assist.GlobalTrace
open IsDedekindDomain
open scoped WithZero

section FiniteValues

variable (p : ℕ) (hp : p.Prime) (Γ : Type) [LinearOrderedCommGroupWithZero Γ]
variable (w : Valuation (LocalClosureQ p hp) Γ)
variable (hw : (w.comap (algebraMap (LocalBaseQ p hp) (LocalClosureQ p hp))).IsEquiv
  (Valued.v : Valuation (LocalBaseQ p hp) ℤᵐ⁰))

include hw

/-- **PROVED**: trivial inertia of a finite Galois local extension implies
ramification index one. Locator: the finite inertia-cardinality theorem. -/
theorem finiteLocal_ramification_eq_one_of_inertia_bot (E : LocalFiniteQ p hp)
    (hI : finiteLocalInertia p hp Γ w hw E = ⊥) :
    letI := finiteLocalIntegerAlgebra p hp Γ w hw E
    (IsLocalRing.maximalIdeal (finiteLocalIntegers w E)).ramificationIdx
      (LocalBaseIntegersQ p hp) = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  let v : Valuation (LocalBaseQ p hp) ℤᵐ⁰ := Valued.v
  letI : v.HasExtension (finiteLocalValuation w E) := finiteLocal_hasExtension p hp Γ w hw E
  letI := finiteLocalIntegerAlgebra p hp Γ w hw E
  haveI := finiteLocalInteger_scalarTower p hp Γ w hw E
  haveI := finiteLocal_integer_isIntegralClosure p hp Γ w hw E
  haveI := finiteLocal_integer_finite p hp Γ w hw E
  haveI := finiteLocal_integer_free p hp Γ w hw E
  haveI := finiteLocal_integer_isDVR p hp Γ w hw E
  letI := finiteLocalIntegerAction p hp Γ w hw E
  haveI : Algebra.IsIntegral (LocalBaseIntegersQ p hp) (finiteLocalIntegers w E) :=
    IsIntegralClosure.isIntegral_algebra (LocalBaseIntegersQ p hp) E
  haveI : SMulDistribClass (E ≃ₐ[LocalBaseQ p hp] E) (finiteLocalIntegers w E) E :=
    inferInstance
  haveI : IsGaloisGroup (E ≃ₐ[LocalBaseQ p hp] E)
      (LocalBaseIntegersQ p hp) (finiteLocalIntegers w E) :=
    IsGaloisGroup.of_isFractionRing _ _ _ (LocalBaseQ p hp) E
  let P₀ : Ideal (LocalBaseIntegersQ p hp) := IsLocalRing.maximalIdeal _
  let P : Ideal (finiteLocalIntegers w E) := IsLocalRing.maximalIdeal _
  haveI : IsLocalHom (algebraMap (LocalBaseIntegersQ p hp) (finiteLocalIntegers w E)) :=
    inferInstance
  haveI : P.LiesOver P₀ := inferInstance
  let e : IsLocalRing.ResidueField (LocalBaseIntegersQ p hp) ≃+* ZMod p :=
    residueFieldEquivZModQ p hp
  haveI : Finite (IsLocalRing.ResidueField (LocalBaseIntegersQ p hp)) :=
    Finite.of_equiv (ZMod p) e.symm.toEquiv
  haveI : Finite P₀.ResidueField :=
    Module.finite_of_finite (IsLocalRing.ResidueField (LocalBaseIntegersQ p hp))
  haveI : Algebra.HasSeparableResidueFieldsAt
      (LocalBaseIntegersQ p hp) (finiteLocalIntegers w E) P₀ := inferInstance
  have hc := Ideal.card_inertia_eq_ramificationIdxIn
    (G := E ≃ₐ[LocalBaseQ p hp] E) P₀ P
  have he : Ideal.ramificationIdxIn P₀ (finiteLocalIntegers w E) = 1 := by
    rw [← hc]
    change Nat.card (finiteLocalInertia p hp Γ w hw E) = 1
    rw [hI]
    simp
  exact (Ideal.ramificationIdxIn_eq_ramificationIdx P₀ P
    (E ≃ₐ[LocalBaseQ p hp] E)).symm.trans he

/-- **PROVED**: in a finite extension with trivial inertia, every nonzero value
is already a base-field value. Locator: ramification index one and the
normalized valuation comparison at primes lying over one another. -/
theorem finiteLocal_unit_value_eq_of_inertia_bot (E : LocalFiniteQ p hp)
    (hI : finiteLocalInertia p hp Γ w hw E = ⊥) (y : Eˣ) :
    ∃ a : (LocalBaseQ p hp)ˣ,
      finiteLocalValuation w E (y : E) =
        finiteLocalValuation w E (algebraMap (LocalBaseQ p hp) E (a : LocalBaseQ p hp)) := by
  let v : Valuation (LocalBaseQ p hp) ℤᵐ⁰ := Valued.v
  letI : v.HasExtension (finiteLocalValuation w E) := finiteLocal_hasExtension p hp Γ w hw E
  letI := finiteLocalIntegerAlgebra p hp Γ w hw E
  haveI := finiteLocalInteger_scalarTower p hp Γ w hw E
  haveI := finiteLocal_integer_isDVR p hp Γ w hw E
  haveI : Module.IsTorsionFree (LocalBaseIntegersQ p hp) E :=
    Module.IsTorsionFree.trans_faithfulSMul (LocalBaseIntegersQ p hp) (LocalBaseQ p hp) E
  haveI : IsIntegralClosure (finiteLocalIntegers w E) (LocalBaseIntegersQ p hp) E :=
    finiteLocal_integer_isIntegralClosure p hp Γ w hw E
  haveI : Module.IsTorsionFree (LocalBaseIntegersQ p hp) (finiteLocalIntegers w E) :=
    IsIntegralClosure.isTorsionFree (LocalBaseIntegersQ p hp) E
  haveI : IsLocalHom (algebraMap (LocalBaseIntegersQ p hp) (finiteLocalIntegers w E)) :=
    inferInstance
  let v₀ := IsDiscreteValuationRing.maximalIdeal (LocalBaseIntegersQ p hp)
  let vE := IsDiscreteValuationRing.maximalIdeal (finiteLocalIntegers w E)
  let d₀ := v₀.valuation (LocalBaseQ p hp)
  let dE := vE.valuation E
  haveI : vE.asIdeal.LiesOver v₀.asIdeal := by
    change (IsLocalRing.maximalIdeal (finiteLocalIntegers w E)).LiesOver
      (IsLocalRing.maximalIdeal (LocalBaseIntegersQ p hp))
    infer_instance
  have he := finiteLocal_ramification_eq_one_of_inertia_bot p hp Γ w hw E hI
  have hdE : dE.IsEquiv (finiteLocalValuation w E) :=
    (Valuation.isEquiv_iff_valuationSubring _ _).mpr
      (maximalIdeal_valuationSubring_eq (finiteLocalIntegers w E))
  have hmap : ∀ a : LocalBaseQ p hp, d₀ a = dE (algebraMap (LocalBaseQ p hp) E a) := by
    intro a
    have h := HeightOneSpectrum.valuation_liesOver E v₀ vE a
    change d₀ a ^ (IsLocalRing.maximalIdeal (finiteLocalIntegers w E)).ramificationIdx
      (LocalBaseIntegersQ p hp) = dE (algebraMap (LocalBaseQ p hp) E a) at h
    rwa [he, pow_one] at h
  obtain ⟨a, ha⟩ := v₀.valuation_surjective (LocalBaseQ p hp) (dE (y : E))
  have hvalue : dE (y : E) = dE (algebraMap (LocalBaseQ p hp) E a) :=
    ha.symm.trans (hmap a)
  have ha0 : a ≠ 0 := by
    intro hz
    have hy0 : dE (y : E) = 0 := by simpa only [hz, map_zero] using hvalue
    exact y.ne_zero ((dE.zero_iff).mp hy0)
  exact ⟨Units.mk0 a ha0, hdE.eq_iff.mp hvalue⟩

/-- **PROVED**: local inertia is normal in the full local Galois group.
Locator: the full local residue-action kernel. -/
theorem localInertia_normal : (localInertia w).Normal := by
  letI := localResidueAlgebra p hp Γ w hw
  rw [← localResidueHom_ker p hp Γ w hw]
  infer_instance

/-- **PROVED**: an inertia-fixed algebraic element is in a finite Galois
subextension of the inertia-fixed field. No unramifiedness is assumed.
Locator: closed normal subgroups in infinite Galois theory and finite normal closure. -/
theorem inertia_fixed_finiteGalois_exists (x : LocalClosureQ p hp)
    (hx : ∀ σ ∈ localInertia w, σ x = x) :
    ∃ E : LocalFiniteQ p hp, x ∈ E.toIntermediateField ∧
      E.toIntermediateField ≤ IntermediateField.fixedField (localInertia w) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI := localResidueAlgebra p hp Γ w hw
  haveI := localInertia_normal p hp Γ w hw
  haveI : Algebra.IsAlgebraic (ZMod p) (LocalResidueQ w) :=
    local_residue_isAlgebraic p hp Γ w hw
  have hclosed : IsClosed (localInertia w : Set (LocalGaloisQ p hp)) := by
    rw [← localResidueHom_ker p hp Γ w hw]
    exact isClosed_singleton.preimage (localResidueHom_continuous p hp Γ w hw)
  let C : ClosedSubgroup (LocalGaloisQ p hp) := ⟨localInertia w, hclosed⟩
  let N := IntermediateField.fixedField (localInertia w)
  have hfix : N.fixingSubgroup = localInertia w := InfiniteGalois.fixingSubgroup_fixedField C
  have hnormal : N.fixingSubgroup.Normal := by
    rw [hfix]
    infer_instance
  haveI : IsGalois (LocalBaseQ p hp) N :=
    (InfiniteGalois.normal_iff_isGalois N).mp hnormal
  have hxN : x ∈ N := (IntermediateField.mem_fixedField_iff _ _).mpr hx
  let E := FiniteGaloisIntermediateField.adjoin (LocalBaseQ p hp) ({x} : Set _)
  refine ⟨E, FiniteGaloisIntermediateField.subset_adjoin (LocalBaseQ p hp) {x}
    (Set.mem_singleton x), ?_⟩
  change IntermediateField.normalClosure (LocalBaseQ p hp)
    (IntermediateField.adjoin (LocalBaseQ p hp) {x}) (LocalClosureQ p hp) ≤ N
  exact IntermediateField.normalClosure_le_iff_of_normal.mpr
    (IntermediateField.adjoin_simple_le_iff.mpr hxN)

end FiniteValues

/-- **PROVED CONDITIONAL REDUCTION**: finite inertia lifting alone implies the
exact unramified value-group target. The input concerns only a restriction
homomorphism; no value equality or target statement is supplied.
Locator: Serre, *Local Fields*, III, §5, and the preceding finite valuation comparison. -/
theorem localUnramifiedValueGroupPrint_of_finite_inertia_lifting
    (hLift : LocalFiniteInertiaLifting) : LocalUnramifiedValueGroupPrint := by
  intro p hp Γ _ w hw x hx
  have hxF : ∀ σ ∈ localInertia w, σ (x : LocalClosureQ p hp) = x := by
    intro σ hσ
    exact congrArg Units.val (hx σ hσ)
  obtain ⟨E, hxE, hE⟩ := inertia_fixed_finiteGalois_exists p hp Γ w hw (x : _) hxF
  have hI : finiteLocalInertia p hp Γ w hw E = ⊥ := by
    apply bot_unique
    intro τ hτ
    rw [Subgroup.mem_bot]
    obtain ⟨σ, hσ, hres⟩ := hLift p hp Γ w hw E τ hτ
    rw [← hres]
    apply AlgEquiv.ext
    intro y
    apply E.toIntermediateField.val.injective
    have hfix : σ (algebraMap E (LocalClosureQ p hp) y) =
        algebraMap E (LocalClosureQ p hp) y :=
      (IntermediateField.mem_fixedField_iff _ _).mp (hE y.2) σ hσ
    exact (AlgEquiv.restrictNormal_commutes σ E y).trans hfix
  let y : Eˣ := Units.mk0 (⟨(x : LocalClosureQ p hp), hxE⟩ : E) (by
    intro h
    exact x.ne_zero (congrArg Subtype.val h))
  obtain ⟨a, ha⟩ := finiteLocal_unit_value_eq_of_inertia_bot p hp Γ w hw E hI y
  refine ⟨a, ?_⟩
  change w (x : LocalClosureQ p hp) =
    w (E.toIntermediateField.val (algebraMap (LocalBaseQ p hp) E (a : LocalBaseQ p hp))) at ha
  rwa [E.toIntermediateField.val.commutes] at ha

/-- **PROVED**: the exact `LocalUnramifiedValueGroupPrint` target. Every
inertia-fixed nonzero algebraic element has the value of a base-field unit.
No unramified-extension or value-group statement is assumed as an input.
Locator: Serre, *Local Fields*, III, §5. -/
theorem localUnramifiedValueGroupPrint : LocalUnramifiedValueGroupPrint :=
  localUnramifiedValueGroupPrint_of_finite_inertia_lifting localFiniteInertiaLifting

end ZInQ.Contrib.RC53Assist.TateCurve
