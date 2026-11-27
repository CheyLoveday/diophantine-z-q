import ZInQKernel.Contrib.RC53Assist.TateCurve.LocalReadings.LocalResidue
import ZInQKernel.Contrib.RC53Assist.TateCurve.LocalReadings.GaloisTopology

/-!
# Local arithmetic Frobenius generates the unramified quotient

Reduction has inertia as kernel. The image of an open subgroup is closed by
compactness. If that subgroup contains arithmetic Frobenius, its residue image
has fixed field equal to the prime field, hence is the full residue Galois group.
Pullback proves the original local open-subgroup statement, without normality
of the subgroup or a surjectivity hypothesis.

Kinds: proved statements only.
Locators: Serre, *Local Fields*, I, §8 and III, §5; infinite Galois theory.
The cited book is distinct from the chapter in Cassels--Fröhlich.
-/

noncomputable section

set_option maxHeartbeats 800000

namespace ZInQ.Contrib.RC53Assist.TateCurve

open ZInQ.Contrib.RC53Assist.DecompositionGlue
open ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary
open ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion
open ZInQ.Contrib.RC53Assist.GlobalTrace
open scoped WithZero

section Frobenius

variable (p : ℕ) (hp : p.Prime) (Γ : Type) [LinearOrderedCommGroupWithZero Γ]
variable (w : Valuation (LocalClosureQ p hp) Γ)
variable (hw : (w.comap (algebraMap (LocalBaseQ p hp) (LocalClosureQ p hp))).IsEquiv
  (Valued.v : Valuation (LocalBaseQ p hp) ℤᵐ⁰))

include hw

/-- **PROVED**: the local residue homomorphism is continuous for the Krull
topologies. Locator: residue lifts and finite element stabilizers. -/
theorem localResidueHom_continuous :
    letI : Fact p.Prime := ⟨hp⟩
    letI := localResidueAlgebra p hp Γ w hw
    Continuous (localResidueHom p hp Γ w hw) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI := localResidueAlgebra p hp Γ w hw
  apply continuous_galoisHom_of_element_lifts
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  refine ⟨(x : LocalClosureQ p hp), fun σ hσ => ?_⟩
  change localResidueRingHom p hp Γ w hw σ (IsLocalRing.residue w.valuationSubring x) =
    IsLocalRing.residue w.valuationSubring x
  rw [localResidueRingHom_apply]
  apply congrArg (IsLocalRing.residue w.valuationSubring)
  apply Subtype.ext
  exact hσ

/-- **PROVED NON-VACUITY**: arithmetic Frobenius exists for every extending
valuation in the local reading, not only for a chosen normalization.
Locator: existence of Frobenius at a rational prime and valuation uniqueness. -/
theorem local_arithmeticFrobenius_exists :
    ∃ σ : LocalGaloisQ p hp,
      IsArithmeticFrobeniusOnClosureQ (primeIdealQ p hp) Γ w σ := by
  let D := Classical.choice (localArithmeticFrobenius_nonempty p hp)
  obtain ⟨Γ₀, hΓ₀, w₀, _, _, hw₀, _, _, σ, hσ, _⟩ :=
    decompositionGroupLocalGlobalGlue p hp D
  letI : LinearOrderedCommGroupWithZero Γ₀ := hΓ₀
  letI := padicNontriviallyNormedField p hp
  have he : w.IsEquiv w₀ := (local_valuation_isEquiv_spectral p hp Γ w hw).trans
    (local_valuation_isEquiv_spectral p hp Γ₀ w₀ hw₀).symm
  exact ⟨σ, fun x hx => he.lt_one_iff_lt_one.mpr (hσ x (he.le_one_iff_le_one.mp hx))⟩

/-- **PROVED**: the residue homomorphism is onto the residue Galois group.
Locator: compact image containing arithmetic Frobenius, Serre I, §8 and III, §5. -/
theorem localResidueHom_surjective :
    letI := localResidueAlgebra p hp Γ w hw
    Function.Surjective (localResidueHom p hp Γ w hw) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI := localResidueAlgebra p hp Γ w hw
  haveI : Algebra.IsAlgebraic (ZMod p) (LocalResidueQ w) :=
    local_residue_isAlgebraic p hp Γ w hw
  haveI : IsGalois (ZMod p) (LocalResidueQ w) :=
    finiteField_isGalois_algebraic (ZMod p) (LocalResidueQ w)
  obtain ⟨σ, hσ⟩ := local_arithmeticFrobenius_exists p hp Γ w hw
  have hr : IsClosed ((localResidueHom p hp Γ w hw).range :
      Set (LocalResidueQ w ≃ₐ[ZMod p] LocalResidueQ w)) := by
    simpa only [MonoidHom.coe_range, Set.image_univ] using
      (isCompact_univ.image (localResidueHom_continuous p hp Γ w hw)).isClosed
  apply MonoidHom.range_eq_top.mp
  exact primeField_closed_subgroup_eq_top p (LocalResidueQ w)
    (localResidueHom p hp Γ w hw σ) (localResidueHom_frobenius p hp Γ w hw σ hσ)
    _ hr ⟨σ, rfl⟩

end Frobenius

/-- **PROVED**: the exact `LocalFrobeniusGenerationPrint` target, for every prime,
every extending valuation, and every open subgroup. No local-field bridge or
Frobenius-generation hypothesis is assumed.
Locator: Serre, *Local Fields*, I, §8 and III, §5. -/
theorem localFrobeniusGenerationPrint : LocalFrobeniusGenerationPrint := by
  intro p hp Γ _ w hw σ hσ H hH hI hmem
  letI : Fact p.Prime := ⟨hp⟩
  letI := localResidueAlgebra p hp Γ w hw
  haveI : Algebra.IsAlgebraic (ZMod p) (LocalResidueQ w) :=
    local_residue_isAlgebraic p hp Γ w hw
  haveI : IsGalois (ZMod p) (LocalResidueQ w) :=
    finiteField_isGalois_algebraic (ZMod p) (LocalResidueQ w)
  apply compact_subgroup_eq_top_of_residue_frobenius p
    (localResidueHom p hp Γ w hw) (localResidueHom_continuous p hp Γ w hw) σ
    (localResidueHom_frobenius p hp Γ w hw σ hσ) H hH _ hmem
  rwa [localResidueHom_ker]

end ZInQ.Contrib.RC53Assist.TateCurve
