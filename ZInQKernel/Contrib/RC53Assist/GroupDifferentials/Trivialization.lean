import ZInQKernel.Contrib.RC53Assist.GroupDifferentials.Comparison

/-!
# Invariant differentials: the differential sheaf of a group scheme over a field is free

This file proves `AbelianCurve.InvariantDifferentialTrivialization`, the only remaining input
of S2a: the actual differential sheaf `AbelianCurve.differentialSheaf G.hom` of a smooth
integral finite-type group curve over the rationals is isomorphic to the structure sheaf.

Literature: J. S. Milne, *Abelian varieties*, version 2.00 (March 16, 2008), Chapter IV,
Proposition 6.4, printed page 152 (page 158 of the file
<https://www.jmilne.org/math/CourseNotes/AV.pdf>, 1291594 bytes, SHA-256
`f5ca4e63e5092a4b102daad1470e4cbed5fe8f82115e3a28c8881e3f67f6aaef`), manuscript bibitem
`milne-av`. Verbatim:

> PROPOSITION 6.4. Let V be a smooth algebraic variety of dimension g over a field k.
> (a) The sheaf of differentials Ω¹_{V/k} on V is a locally free sheaf of O_V-modules of rank g.
> (b) If V is a group variety, then Ω¹ is free.

Nothing printed is assumed here: part (a) is proved for `g = 1` (for every `g` in
`HigherDimension.lean`) and part (b) in general.

## Proof

* Translation invariance (the shearing argument). For a group scheme `π : G ⟶ S` with identity
  `e`, there is an isomorphism `Ω_{G/S} ≅ π^* e^* Ω_{G/S}`. The shearing automorphism
  `(g, h) ↦ (g h, h)` of `G ×_S G` over the second factor identifies `μ^* Ω_{G/S}` and
  `pr₁^* Ω_{G/S}` with `Ω_{(G ×_S G)/G}` (base change of differentials, Stacks Project,
  Lemma 29.33.10, Tag 01V0), and pulling back along `g ↦ (e(π g), g)` gives the claim. This is
  proved in the vendored AxiomMath/Stacks formalization
  (`ZInQKernel/Contrib/CloudB3W16Cartier/GroupDifferentials.lean`,
  `relativeDifferentialsIsoPullbackIdentity`, and its base-change theorem
  `isIso_relativeDifferentialsMap_of_isPullback`) for the sheaf construction of `Ω`; the file
  `Comparison.lean` transports it to the sheaf used by the reduction.
* The fibre at the identity. If `π` is smooth of relative dimension one, `Ω_{G/S}` is trivial
  on a neighbourhood of every point (vendored Jacobian-Challenge
  `nonempty_restrict_relativeDifferentials_iso_unit`, which uses a standard-smooth chart).
  The identity of a group scheme over a field is a point `Spec k ⟶ G`, which factors through
  such a neighbourhood, so `e^* Ω` is trivial; pullback preserves the structure sheaf.
* A smooth integral group curve over the rationals is smooth of relative dimension one
  (`AbelianCurve.smooth_relativeDimension_one`).
-/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.GroupDifferentials

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

/-- DEFINITION. The identity section `S ⟶ G` of a group scheme `f : G ⟶ S`, as a morphism of
schemes. Locator: vendored `GroupSchemeDifferentials.identity`, in
`ZInQKernel/Contrib/CloudB3W16Cartier/GroupDifferentials.lean`. -/
abbrev groupIdentity {S G : Scheme.{u}} (f : G ⟶ S) [GrpObj (Over.mk f)] : S ⟶ G :=
  ZInQ.Contrib.CloudB3W16Cartier.Vendor.AlgebraicGeometry.GroupSchemeDifferentials.identity f

open ZInQ.Contrib.CloudB3W16Cartier.Vendor.AlgebraicGeometry.GroupSchemeDifferentials in
/-- DEFINITION (an isomorphism, PROVED by the shearing argument). Translation invariance of
differentials: for every group scheme `f : G ⟶ S`, the sheaf of relative differentials is the
pullback along `f` of its restriction along the identity section, `Ω_{G/S} ≅ f^* e^* Ω_{G/S}`.
Locator: vendored `relativeDifferentialsIsoPullbackIdentity`
(`ZInQKernel/Contrib/CloudB3W16Cartier/GroupDifferentials.lean`), transported by
`differentialsComparison`; Stacks, Lemma 29.33.10 (Tag 01V0). -/
def differentialsIsoPullbackIdentity {S G : Scheme.{u}} (f : G ⟶ S)
    [GrpObj (Over.mk f)] :
    f.relativeDifferentials ≅
      (Scheme.Modules.pullback f).obj
        ((Scheme.Modules.pullback (groupIdentity f)).obj f.relativeDifferentials) :=
  differentialsComparison f ≪≫ relativeDifferentialsIsoPullbackIdentity f ≪≫
    (Scheme.Modules.pullback f).mapIso
      ((Scheme.Modules.pullback (groupIdentity f)).mapIso (differentialsComparison f).symm)

/-- PROVED. For a morphism smooth of relative dimension one, the pullback of the sheaf of
relative differentials along any point `Spec K ⟶ X` with values in a field is trivial: the
point factors through an open neighbourhood on which the sheaf is trivial.
Locator: vendored Jacobian-Challenge `nonempty_restrict_relativeDifferentials_iso_unit`
(`.../Jacobian/AlgebraicGeometry/Modules/Differentials.lean`) and `pullbackObjUnitIso`
(`.../Jacobian/AlgebraicGeometry/Modules/Invertible.lean`); Mathlib's `pullbackComp` and
`restrictFunctorIsoPullback`. -/
theorem nonempty_pullback_relativeDifferentials_iso_unit {X S : Scheme.{u}} (f : X ⟶ S)
    [SmoothOfRelativeDimension 1 f] {K : Type u} [Field K] (e : Spec (.of K) ⟶ X) :
    Nonempty ((Scheme.Modules.pullback e).obj f.relativeDifferentials ≅
      SheafOfModules.unit (Spec (.of K)).ringCatSheaf) := by
  obtain ⟨V, hV, ⟨i⟩⟩ :=
    f.nonempty_restrict_relativeDifferentials_iso_unit (e (IsLocalRing.closedPoint K))
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
    Scheme.Modules.pullbackObjUnitIso e'⟩

/-- PROVED. Milne IV.6.4(a)–(b) in rank one, over an arbitrary field: the sheaf of relative
differentials of a group scheme over a field which is smooth of relative dimension one is
isomorphic to the structure sheaf. Locator: Milne, *Abelian varieties* (2008), IV,
Proposition 6.4, printed p. 152; `differentialsIsoPullbackIdentity` and
`nonempty_pullback_relativeDifferentials_iso_unit` above. -/
theorem nonempty_relativeDifferentials_iso_unit_of_grpObj {k : Type u} [Field k]
    {G : Scheme.{u}} (f : G ⟶ Spec (.of k)) [GrpObj (Over.mk f)]
    [SmoothOfRelativeDimension 1 f] :
    Nonempty (f.relativeDifferentials ≅ SheafOfModules.unit G.ringCatSheaf) := by
  obtain ⟨i⟩ := nonempty_pullback_relativeDifferentials_iso_unit f (groupIdentity f)
  exact ⟨differentialsIsoPullbackIdentity f ≪≫
    (Scheme.Modules.pullback f).mapIso i ≪≫ Scheme.Modules.pullbackObjUnitIso f⟩

open ZInQ.Contrib.CloudB3W16Cartier.Vendor.AlgebraicGeometry.GroupSchemeDifferentials in
/-- PROVED. Milne IV.6.4(b) as printed ("Ω¹ is free"), for every group scheme over a field,
with no smoothness or finiteness hypothesis: the sheaf of relative differentials is a free
sheaf of modules. Locator: Milne, *Abelian varieties* (2008), IV, Proposition 6.4(b), printed
p. 152; vendored `exists_free_iso_relativeDifferentials_of_field`
(`ZInQKernel/Contrib/CloudB3W16Cartier/GroupDifferentials.lean`), transported by
`differentialsComparison`. -/
theorem exists_free_iso_relativeDifferentials_of_grpObj {k : Type u} [Field k]
    {G : Scheme.{u}} (f : G ⟶ Spec (.of k)) [GrpObj (Over.mk f)] :
    ∃ I : Type u,
      Nonempty (f.relativeDifferentials ≅ SheafOfModules.free (R := G.ringCatSheaf) I) := by
  obtain ⟨I, ⟨e⟩⟩ := exists_free_iso_relativeDifferentials_of_field k G f
  exact ⟨I, ⟨differentialsComparison f ≪≫ e⟩⟩

/-- PROVED. **The remaining S2a input.** For every smooth integral group curve of finite type
over the rationals, the actual differential sheaf `AbelianCurve.differentialSheaf G.hom` is a
trivial line sheaf. This is the proposition `AbelianCurve.InvariantDifferentialTrivialization`
of `ZInQKernel/Contrib/RC53Assist/AbelianCurve/DifferentialLine.lean`, proved, not assumed.
Locator: Milne, *Abelian varieties*, version 2.00 (2008), IV, Proposition 6.4(a)–(b), printed
p. 152; `nonempty_relativeDifferentials_iso_unit_of_grpObj` and
`AbelianCurve.smooth_relativeDimension_one`. The quasi-compactness hypothesis is not used. -/
theorem invariantDifferentialTrivialization :
    AbelianCurve.InvariantDifferentialTrivialization := by
  intro G _ _ _ _ hdim
  letI : GrpObj (Over.mk G.hom) := inferInstanceAs (GrpObj G)
  haveI := AbelianCurve.smooth_relativeDimension_one G.hom hdim
  exact nonempty_relativeDifferentials_iso_unit_of_grpObj G.hom

end ZInQ.Contrib.RC53Assist.GroupDifferentials
