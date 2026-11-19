import Mathlib.Algebra.Module.Injective
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Injectivity of arbitrary free modules

Over a Noetherian self-injective ring, a fixed ideal map into a direct sum of copies of
that ring has finitely many nonzero coordinate maps. Extend those coordinates and assemble
an extension of the same ideal map. Baer's criterion and a basis equivalence then give
injectivity of every free module, without any restriction on its rank.
-/

set_option autoImplicit false

namespace ZInQ.Contrib.RC53Assist.NoetherianInjective

/-- Baer's extension property for an arbitrary direct sum of copies of the coefficient ring. -/
theorem baer_finsupp_noetherian {R ι : Type} [CommRing R] [IsNoetherianRing R]
    [Module.Injective R R] : Module.Baer R (ι →₀ R) := by
  classical
  rw [Module.Baer.iff_surjective]
  intro I g
  obtain ⟨a, ha⟩ :=
    (LinearMap.finsuppLinearMap_bijective_of_moduleFinite R I R ι R).2 g
  let restrict : (R →ₗ[R] R) →ₗ[R] (I →ₗ[R] R) := LinearMap.lcomp R R I.subtype
  have hrestrict : Function.Surjective restrict :=
    (Module.Baer.iff_surjective.mp
      (Module.Baer.of_injective (inferInstance : Module.Injective R R))) I
  obtain ⟨b, hb⟩ := Finsupp.mapRange_surjective restrict restrict.map_zero hrestrict a
  refine ⟨LinearMap.finsuppLinearMap R b, ?_⟩
  apply LinearMap.ext
  intro x
  apply Finsupp.ext
  intro i
  change (b i) (x : R) = g x i
  have hbi := congrArg (fun c : ι →₀ (I →ₗ[R] R) => c i x) hb
  change (b i) (x : R) = a i x at hbi
  have hai := congrArg (fun f : I →ₗ[R] (ι →₀ R) => f x i) ha
  change a i x = g x i at hai
  exact hbi.trans hai

/-- Any free module over a Noetherian self-injective commutative ring is injective. -/
theorem injective_of_free_noetherian {R M : Type} [CommRing R] [IsNoetherianRing R]
    [Module.Injective R R] [AddCommGroup M] [Module R M] [Module.Free R M] :
    Module.Injective R M := by
  apply Module.Baer.injective
  exact Module.Baer.of_equiv (Module.Free.chooseBasis R M).repr.symm
    (baer_finsupp_noetherian (R := R))

end ZInQ.Contrib.RC53Assist.NoetherianInjective
