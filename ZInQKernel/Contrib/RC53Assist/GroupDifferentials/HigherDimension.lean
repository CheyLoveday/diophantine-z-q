import ZInQKernel.Contrib.RC53Assist.GroupDifferentials.Trivialization

/-!
# Invariant differentials in every dimension

Milne, *Abelian varieties*, version 2.00 (2008), Chapter IV, Proposition 6.4, printed p. 152
(verbatim text and file checksum in `Trivialization.lean`), states for a smooth variety `V` of
dimension `g` over a field that `Ω¹_{V/k}` is locally free of rank `g`, and that it is free if
`V` is a group variety. This file proves the combination for group schemes in every
dimension: for a group scheme over a field which is smooth of relative dimension `g`, the
sheaf of relative differentials is isomorphic to the free sheaf `𝒪^g`.

The proof is that of the rank-one case in `Trivialization.lean`: translation invariance
`Ω ≅ π^* e^* Ω`, together with a trivialization of rank `g` near the identity point coming
from a standard-smooth chart. The rank-one theorem used by S2a does not depend on this file.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.GroupDifferentials

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

/-- PROVED. Milne IV.6.4(a) in the form used here: for a morphism smooth of relative dimension
`d`, every point has an open neighbourhood on which the sheaf of relative differentials is
free of rank `d`. On an affine standard-smooth chart `Spec B ⟶ Spec A` it is `Ω_{B/A}^~` and
`Ω_{B/A} ≅ B^d`. Locator: Mathlib's `exists_isStandardSmoothOfRelativeDimension`,
`nonempty_linearEquiv_kaehlerDifferential` and `tildeFinsupp`; vendored Jacobian-Challenge
`relativeDifferentialsRestrictIso`, `relativeDifferentialsSpecIso` and `pullbackFreeIso`. This
is the rank-`d` analogue of the vendored `nonempty_restrict_relativeDifferentials_iso_unit`. -/
theorem nonempty_restrict_relativeDifferentials_iso_free {X S : Scheme.{u}} (f : X ⟶ S)
    (d : ℕ) [SmoothOfRelativeDimension d f] (x : X) :
    ∃ V : X.Opens, x ∈ V ∧
      Nonempty (f.relativeDifferentials.restrict V.ι ≅
        SheafOfModules.free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin d))) := by
  obtain ⟨U, hU, V, hV, hx, e, hsm⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := d) (f := f) x
  let := (f.appLE U V e).hom.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension d Γ(S, U) Γ(X, V) := hsm
  obtain ⟨eΩ⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.nonempty_linearEquiv_kaehlerDifferential
      (R := Γ(S, U)) (S := Γ(X, V)) d
  refine ⟨V, hx, ⟨?_⟩⟩
  let eM : CommRingCat.KaehlerDifferential (f.appLE U V e) ≅
      ModuleCat.of Γ(X, V) (ULift.{u} (Fin d) →₀ Γ(X, V)) :=
    (eΩ ≪≫ₗ (Finsupp.linearEquivFunOnFinite Γ(X, V) Γ(X, V) (Fin d)).symm ≪≫ₗ
      (Finsupp.domLCongr Equiv.ulift.symm)).toModuleIso
  let T : f.relativeDifferentials.restrict hV.fromSpec ≅
      SheafOfModules.free (R := (Spec Γ(X, V)).ringCatSheaf) (ULift.{u} (Fin d)) :=
    f.relativeDifferentialsRestrictIso hV.fromSpec ≪≫
      Scheme.Hom.relativeDifferentialsCongr _
        (IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e).symm ≪≫
      Scheme.Hom.relativeDifferentialsCompIso _ _ ≪≫ relativeDifferentialsSpecIso _ ≪≫
      (tilde.functor _).mapIso eM ≪≫ tildeFinsupp _
  exact (Scheme.Modules.restrictFunctorCongr hV.isoSpec_hom_fromSpec.symm).app _ ≪≫
    (Scheme.Modules.restrictFunctorComp hV.isoSpec.hom hV.fromSpec).app _ ≪≫
    (Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapIso T ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback hV.isoSpec.hom).app _ ≪≫
    Scheme.Modules.pullbackFreeIso _ _

/-- PROVED. For a morphism smooth of relative dimension `d`, the pullback of the sheaf of
relative differentials along a point `Spec K ⟶ X` with values in a field is free of rank `d`.
Locator: `nonempty_restrict_relativeDifferentials_iso_free`; as in
`nonempty_pullback_relativeDifferentials_iso_unit`. -/
theorem nonempty_pullback_relativeDifferentials_iso_free {X S : Scheme.{u}} (f : X ⟶ S)
    (d : ℕ) [SmoothOfRelativeDimension d f] {K : Type u} [Field K] (e : Spec (.of K) ⟶ X) :
    Nonempty ((Scheme.Modules.pullback e).obj f.relativeDifferentials ≅
      SheafOfModules.free (R := (Spec (.of K)).ringCatSheaf) (ULift.{u} (Fin d))) := by
  obtain ⟨V, hV, ⟨i⟩⟩ :=
    nonempty_restrict_relativeDifferentials_iso_free f d (e (IsLocalRing.closedPoint K))
  have H : Set.range e ⊆ Set.range V.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι, Subsingleton.elim y (IsLocalRing.closedPoint K)]
    exact hV
  let e' := IsOpenImmersion.lift V.ι e H
  have he : e' ≫ V.ι = e := IsOpenImmersion.lift_fac _ _ _
  exact ⟨(Scheme.Modules.pullbackCongr he.symm).app _ ≪≫
    ((Scheme.Modules.pullbackComp e' V.ι).app _).symm ≪≫
    (Scheme.Modules.pullback e').mapIso
      (((Scheme.Modules.restrictFunctorIsoPullback V.ι).app _).symm ≪≫ i) ≪≫
    Scheme.Modules.pullbackFreeIso e' _⟩

/-- PROVED. Milne IV.6.4(a)–(b) for group schemes in every dimension: the sheaf of relative
differentials of a group scheme over a field which is smooth of relative dimension `d` is
isomorphic to the free sheaf of rank `d`. Locator: Milne, *Abelian varieties* (2008), IV,
Proposition 6.4, printed p. 152; `differentialsIsoPullbackIdentity` and
`nonempty_pullback_relativeDifferentials_iso_free`. -/
theorem nonempty_relativeDifferentials_iso_free_of_grpObj {k : Type u} [Field k]
    {G : Scheme.{u}} (f : G ⟶ Spec (.of k)) [GrpObj (Over.mk f)] (d : ℕ)
    [SmoothOfRelativeDimension d f] :
    Nonempty (f.relativeDifferentials ≅
      SheafOfModules.free (R := G.ringCatSheaf) (ULift.{u} (Fin d))) := by
  obtain ⟨i⟩ := nonempty_pullback_relativeDifferentials_iso_free f d (groupIdentity f)
  exact ⟨differentialsIsoPullbackIdentity f ≪≫
    (Scheme.Modules.pullback f).mapIso i ≪≫ Scheme.Modules.pullbackFreeIso f _⟩

end ZInQ.Contrib.RC53Assist.GroupDifferentials
