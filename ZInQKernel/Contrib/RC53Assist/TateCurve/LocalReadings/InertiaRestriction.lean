import ZInQKernel.Contrib.RC53Assist.TateCurve.LocalReadings.FiniteTower

/-!
# Restriction of absolute inertia to finite subextensions

The finite restriction assertion below concerns only the genuine inertia groups
and the canonical restriction homomorphism. It contains no value-group assertion.

Kinds: definitions and proved statements only.
Locators: Serre, *Local Fields*, III, §5, and the inverse-limit description of
absolute Galois groups. The book is distinct from the chapter in Cassels--Fröhlich.
-/

noncomputable section

set_option maxHeartbeats 800000

namespace ZInQ.Contrib.RC53Assist.TateCurve

open ZInQ.Contrib.RC53Assist.GlobalTrace
open scoped WithZero

/-- **DEFINITION**: the finite-level inertia lifting assertion. Every inertia
automorphism of a finite Galois subextension lifts to absolute inertia.
Locator: finite inertia restriction and inverse-limit Galois theory.
This is a proposition, not an axiom or a value-group hypothesis. -/
def LocalFiniteInertiaLifting : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (Γ : Type) [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (LocalClosureQ p hp) Γ)
    (hw : (w.comap (algebraMap (LocalBaseQ p hp) (LocalClosureQ p hp))).IsEquiv
      (Valued.v : Valuation (LocalBaseQ p hp) ℤᵐ⁰))
    (E : LocalFiniteQ p hp) (τ : E ≃ₐ[LocalBaseQ p hp] E),
    τ ∈ finiteLocalInertia p hp Γ w hw E →
      ∃ σ : LocalGaloisQ p hp, σ ∈ localInertia w ∧ AlgEquiv.restrictNormalHom E σ = τ

section Lifting

open ZInQ.Contrib.RC53Assist.DecompositionGlue

variable (p : ℕ) (hp : p.Prime) (Γ : Type) [LinearOrderedCommGroupWithZero Γ]
variable (w : Valuation (LocalClosureQ p hp) Γ)
variable (hw : (w.comap (algebraMap (LocalBaseQ p hp) (LocalClosureQ p hp))).IsEquiv
  (Valued.v : Valuation (LocalBaseQ p hp) ℤᵐ⁰))

include hw

/-- **PROVED**: compatible finite inertia conditions lift to absolute inertia.
The finite lifts are glued by compactness of the absolute Galois group.
Locator: finite inertia restriction, Serre III, §5, and infinite Galois theory. -/
theorem local_inertia_lift (E : LocalFiniteQ p hp) (τ : E ≃ₐ[LocalBaseQ p hp] E)
    (hτ : τ ∈ finiteLocalInertia p hp Γ w hw E) :
    ∃ σ : LocalGaloisQ p hp, σ ∈ localInertia w ∧ AlgEquiv.restrictNormalHom E σ = τ := by
  let C : LocalFiniteQ p hp → Set (LocalGaloisQ p hp) := fun M =>
    {σ | AlgEquiv.restrictNormalHom E σ = τ ∧
      AlgEquiv.restrictNormalHom M σ ∈ finiteLocalInertia p hp Γ w hw M}
  have hCne : ∀ M, (C M).Nonempty := by
    intro M
    let V := E ⊔ M
    have hmap := finiteLocalInertia_map_of_le p hp Γ w hw E V
      (le_sup_left : E ≤ E ⊔ M)
    have ht : τ ∈ (finiteLocalInertia p hp Γ w hw V).map
        (finiteLocalRestrict E V (le_sup_left : E ≤ E ⊔ M)) := by
      rw [hmap]
      exact hτ
    obtain ⟨μ, hμ, hμτ⟩ := Subgroup.mem_map.mp ht
    obtain ⟨σ, hσμ⟩ := AlgEquiv.restrictNormalHom_surjective (LocalClosureQ p hp) μ
    have hVσ : AlgEquiv.restrictNormalHom V σ ∈ finiteLocalInertia p hp Γ w hw V := by
      rwa [hσμ]
    have hEσ : AlgEquiv.restrictNormalHom E σ = τ := by
      have hcomp := congrArg
        (fun f : LocalGaloisQ p hp →* (E ≃ₐ[LocalBaseQ p hp] E) => f σ)
        (finiteLocalRestrict_comp E V (le_sup_left : E ≤ E ⊔ M))
      change finiteLocalRestrict E V (le_sup_left : E ≤ E ⊔ M)
        (AlgEquiv.restrictNormalHom V σ) = AlgEquiv.restrictNormalHom E σ at hcomp
      rw [hσμ] at hcomp
      exact hcomp.symm.trans hμτ
    exact ⟨σ, hEσ, absolute_restrict_inertia_of_le p hp Γ w hw M V
      (le_sup_right : M ≤ E ⊔ M) σ hVσ⟩
  have hCdir : Directed (· ⊇ ·) C := by
    intro M₁ M₂
    refine ⟨M₁ ⊔ M₂, ?_, ?_⟩
    · intro σ hσ
      exact ⟨hσ.1, absolute_restrict_inertia_of_le p hp Γ w hw M₁ (M₁ ⊔ M₂)
        le_sup_left σ hσ.2⟩
    · intro σ hσ
      exact ⟨hσ.1, absolute_restrict_inertia_of_le p hp Γ w hw M₂ (M₁ ⊔ M₂)
        le_sup_right σ hσ.2⟩
  have hCcl : ∀ M, IsClosed (C M) := by
    intro M
    have h₁ : IsClosed ((AlgEquiv.restrictNormalHom E :
        LocalGaloisQ p hp →* (E ≃ₐ[LocalBaseQ p hp] E)) ⁻¹' {τ}) :=
      isClosed_singleton.preimage (localFiniteRestriction_continuous E)
    have h₂ := (Set.toFinite (finiteLocalInertia p hp Γ w hw M :
      Set (M ≃ₐ[LocalBaseQ p hp] M))).isClosed.preimage (localFiniteRestriction_continuous M)
    exact h₁.inter h₂
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hCdir
    hCne (fun M => (hCcl M).isCompact) hCcl
  have hall : ∀ M, σ ∈ C M := Set.mem_iInter.mp hσ
  have hI : σ ∈ localInertia w := by
    apply (mem_map_inertiaSubgroup_iff w.valuationSubring σ).mpr
    refine ⟨local_mem_decomposition p hp Γ w hw σ, fun x hx => ?_⟩
    apply (mem_valuationSubring_nonunits_iff w).mpr
    let M := FiniteGaloisIntermediateField.adjoin (LocalBaseQ p hp) ({x} : Set _)
    have hxM : x ∈ M.toIntermediateField :=
      FiniteGaloisIntermediateField.subset_adjoin (LocalBaseQ p hp) {x} (Set.mem_singleton x)
    let y : M := ⟨x, hxM⟩
    have hsmall := (mem_finiteLocalInertia p hp Γ w hw M
      (AlgEquiv.restrictNormalHom M σ)).mp (hall M).2 y hx
    change w (algebraMap M (LocalClosureQ p hp)
      (AlgEquiv.restrictNormalHom M σ y - y)) < 1 at hsmall
    have hcomm : algebraMap M (LocalClosureQ p hp) (AlgEquiv.restrictNormalHom M σ y) =
        σ (algebraMap M (LocalClosureQ p hp) y) := AlgEquiv.restrictNormal_commutes σ M y
    rwa [map_sub, hcomm] at hsmall
  exact ⟨σ, hI, (hall E).1⟩

end Lifting

/-- **PROVED**: the finite inertia lifting assertion, with no extra local-field input.
Locator: finite inertia restriction and the preceding compactness argument. -/
theorem localFiniteInertiaLifting : LocalFiniteInertiaLifting := by
  intro p hp Γ _ w hw E τ hτ
  exact local_inertia_lift p hp Γ w hw E τ hτ

end ZInQ.Contrib.RC53Assist.TateCurve
