import Mathlib

/-!
# RC53 PairedFunctional: derived scalar extension of the old-support comparisons

Proof of Proposition `ex:arith-paired-functional`, tex L3797–3812:

> Every allowed `K` splits at `2N`. [...] All old-place diagrams over `A_i[G]` are thus derived
> scalar extensions of this finite fixed list. Tensoring the chosen free models and their homotopy
> identities preserves all these identities. [...] Neither requires a new lattice comparison when
> a prime is added.

The old-support comparisons are fixed homotopy equivalences of bounded free `ℤ₂`-complexes, chosen
once (tex L3772–3794, with `QuasiIsoFreeHomotopyInverse` of `ConeInverse.lean`). Their use over
`A_i[G]`, `𝒪[G]` or `Λ_𝔭` is by extension of scalars along a ring map `f : S → S'`. For complexes
of free modules extension of scalars is the derived scalar extension, and it is an additive functor,
so it carries homotopies, homotopy equivalences and contractions to the same over `S'`.

Nodes (PROVED):
* `ScalarExtensionHomotopyEquiv` (tex L3804–3810): a homotopy equivalence over `S` extends to a
  homotopy equivalence over `S'` whose forward map is the extended forward map; a contraction over
  `S` extends to a contraction over `S'`.
* `ScalarExtensionFree`: the extension of scalars of a free `S`-module is a free `S'`-module, so the
  extended models are again free (tex L3772–3776, "bounded free models").
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.PairedFunctional

open CategoryTheory Limits

/-- Extension of scalars `ModuleCat S ⥤ ModuleCat S'` is additive (it is a left adjoint, so it
preserves binary biproducts). -/
theorem extendScalars_additive {S S' : Type} [CommRing S] [CommRing S'] (f : S →+* S') :
    (ModuleCat.extendScalars.{0, 0, 0} f).Additive := by
  haveI := (ModuleCat.extendRestrictScalarsAdj.{0, 0, 0} f).leftAdjoint_preservesColimits
  have : PreservesBinaryBiproducts (ModuleCat.extendScalars.{0, 0, 0} f) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- **Scalar extension preserves the integral homotopy identities** (tex L3804–3810: "Tensoring
the chosen free models and their homotopy identities preserves all these identities"). For every
ring map `f : S → S'` of commutative rings, extension of scalars sends a homotopy equivalence
`K ≃ L` of cochain complexes of `S`-modules to a homotopy equivalence of the extended complexes
with the extended forward map, and a contraction of `K` to a contraction of the extended complex.
Classification: PROVED. -/
def ScalarExtensionHomotopyEquiv : Prop :=
  ∀ (S S' : Type) [CommRing S] [CommRing S'] (f : S →+* S')
    (K L : CochainComplex (ModuleCat.{0} S) ℤ),
    (∀ e : HomotopyEquiv K L,
      ∃ e' : HomotopyEquiv (((ModuleCat.extendScalars.{0, 0, 0} f).mapHomologicalComplex _).obj K)
          (((ModuleCat.extendScalars.{0, 0, 0} f).mapHomologicalComplex _).obj L),
        e'.hom = ((ModuleCat.extendScalars.{0, 0, 0} f).mapHomologicalComplex _).map e.hom ∧
        e'.inv = ((ModuleCat.extendScalars.{0, 0, 0} f).mapHomologicalComplex _).map e.inv) ∧
    (Nonempty (Homotopy (𝟙 K) 0) →
      Nonempty (Homotopy
        (𝟙 (((ModuleCat.extendScalars.{0, 0, 0} f).mapHomologicalComplex _).obj K)) 0))

theorem scalarExtensionHomotopyEquiv_proof : ScalarExtensionHomotopyEquiv := by
  intro S S' _ _ f K L
  have := extendScalars_additive f
  refine ⟨fun e => ⟨(ModuleCat.extendScalars f).mapHomotopyEquiv e, rfl, rfl⟩, ?_⟩
  rintro ⟨h⟩
  have h' := (ModuleCat.extendScalars f).mapHomotopy h
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero] at h'
  exact ⟨h'⟩

/-- **Scalar extension of a free module is free** (tex L3772–3776: the extended old-support models
are again bounded free models). Classification: PROVED. -/
def ScalarExtensionFree : Prop :=
  ∀ (S S' : Type) [CommRing S] [CommRing S'] (f : S →+* S') (M : ModuleCat.{0} S),
    Module.Free S M → Module.Free S' ((ModuleCat.extendScalars.{0, 0, 0} f).obj M)

theorem scalarExtensionFree_proof : ScalarExtensionFree := by
  intro S S' _ _ f M hM
  let _ := f.toAlgebra
  change Module.Free S' (TensorProduct S S' M)
  infer_instance

end ZInQ.Contrib.CloudB3RC53.PairedFunctional
