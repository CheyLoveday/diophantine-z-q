/-
Adapted from AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b.
Source: StacksFrontier/AlgebraicGeometry/Morphisms/Differentials/BaseChange.lean
Source SHA256: 31a2295135cdc08c60026552b7fa3d8055d5350255bfa1021552be4d59bd35aa
Apache-2.0; see LICENSE and NOTICE.md.
Changes: isolated vendor namespaces and import paths; citation attributes removed.
-/
import ZInQKernel.Contrib.CloudB3W16Cartier.Vendor.StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Stalk
import ZInQKernel.Contrib.CloudB3W16Cartier.Vendor.StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeStalkCartesian
import ZInQKernel.Contrib.CloudB3W16Cartier.Vendor.StacksFrontier.RingTheory.Kaehler.PushoutBaseChange

namespace ZInQ.Contrib.CloudB3W16Cartier.Vendor
open _root_.AlgebraicGeometry _root_.CategoryTheory

/-!
# Relative differentials under base change and of a fibre product

For a cartesian square of schemes

```
X <--g'-- X'
|         |
f         f'
v         v
S <--g--- S'
```

the canonical map `g'^* Ω_{X/S} ⟶ Ω_{X'/S'}` of Stacks Project, Tag 01UV is an isomorphism: the
sheaf of relative differentials is compatible with base change. For two morphisms `f : X ⟶ S` and
`g : Y ⟶ S` with the same target and the two projections `p`, `q` of a fibre product `W` of `f`
and `g`, the two canonical maps exhibit `Ω_{W/S}` as the direct sum of `p^* Ω_{X/S}` and
`q^* Ω_{Y/S}`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap_pullbackSection`: the canonical map on
  relative differentials, evaluated on a pulled-back universal differential. This is the defining
  compatibility of Tag 01UV, untransposed.
* `AlgebraicGeometry.Scheme.Hom.isIso_relativeDifferentialsMap_of_isPullback`: **Stacks Project,
  Tag 01V0.**
* `AlgebraicGeometry.Scheme.Hom.isIso_biprodDesc_relativeDifferentialsMap`: **Stacks Project,
  Tag 01V1.**

## Implementation notes

Base change is proved on local rings, through
`AlgebraicGeometry.Scheme.Hom.isIso_relativeDifferentialsMap_of_stalk`. At a point `x'` of `X'`
the local ring `𝒪_{X',x'}` is a localization of `𝒪_{X,g' x'} ⊗_{𝒪_{S,f(g' x')}} 𝒪_{S',f' x'}`, by
`AlgebraicGeometry.BaseChangeStalk.cartesian_stalk_isLocalization`, hence formally étale over
that tensor product; so the required equivalence of Kähler differentials is
`KaehlerDifferential.tensorKaehlerEquivOfFormallyEtalePushout`. No affine-local reduction is
needed: the two inputs are both statements about an arbitrary cartesian square.

The fibre product statement is then deduced from base change rather than the other way round,
which inverts the dependency of the source — there Tag 01V1 is proved from Tag 01V0 and Tag 01UX.
Base change at a point is available directly from commutative algebra, whereas the splitting of
the direct sum is not, so this order needs no third input. Concretely: `p^* Ω_{X/S} ⟶ Ω_{W/S}` is
a monomorphism because its composite with `Ω_{W/S} ⟶ Ω_{W/Y}` is the base change isomorphism for
the square `(p, q, f, g)`, and `q^* Ω_{Y/S} ⟶ Ω_{W/S} ⟶ Ω_{W/X}` is the base change isomorphism
for the flipped square, which splits the exact sequence
`p^* Ω_{X/S} ⟶ Ω_{W/S} ⟶ Ω_{W/X} ⟶ 0` of Tag 01UX. Both composites are identified with canonical
maps by `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap_comp`, so no compatibility of
choices is checked by hand.

The structure morphism `W ⟶ S` is written as `p ≫ f`; the pullback condition identifies it with
`q ≫ g`, and `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap_comp` takes the intermediate
structure morphism as a parameter precisely so that this identification never has to be
transported along.

## References

* [Stacks Project, Tag 01V0](https://stacks.math.columbia.edu/tag/01V0)
* [Stacks Project, Tag 01V1](https://stacks.math.columbia.edu/tag/01V1)
* [Stacks Project, Tag 00RV](https://stacks.math.columbia.edu/tag/00RV)
-/

section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- **The canonical map on relative differentials, evaluated on a pulled-back universal
differential.** For a commutative square of schemes, an open `U` of `X` and an open
`U' ≤ f ⁻¹ᵁ U` of `X'`, the canonical map `f^*Ω_{X/S} ⟶ Ω_{X'/S'}` carries the pullback of the
universal differential of a section `a` over `U` to the universal differential of the image of
`a` in `Γ(X', U')`.

This is the defining compatibility of the canonical map with the universal derivations,
`AlgebraicGeometry.Scheme.Hom.IsRelativeDifferentialsMap`, untransposed: the adjoint transpose
is the unit of the adjunction followed by the map, and the unit followed by a restriction is
`AlgebraicGeometry.Scheme.Modules.pullbackSection`. -/
theorem relativeDifferentialsMap_pullbackSection {X' X S' S : Scheme.{u}} (f : X' ⟶ X)
    (p : X ⟶ S) (p' : X' ⟶ S') (g : S' ⟶ S) (hcomm : f ≫ p = p' ≫ g)
    (U : X.Opens) (U' : X'.Opens) (h : U' ≤ f ⁻¹ᵁ U) (a : Γ(X, U)) :
    (relativeDifferentialsMap f p p' g hcomm).val.app (op U')
        (Scheme.Modules.pullbackSection f (relativeDifferentials p) U U' h
          ((universalRelativeDerivation p).d a)) =
      (universalRelativeDerivation p').d (f.appLE U U' h a) := by
  set c := relativeDifferentialsMap f p p' g hcomm
  have hkey : ((((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv
      (relativeDifferentials p) (relativeDifferentials p') c).val.app (op U)).hom
        ((universalRelativeDerivation p).d a)) =
      (universalRelativeDerivation p').d ((f.app U).hom a) :=
    (isRelativeDifferentialsMap_iff_eq f p p' g hcomm c).mpr rfl U a
  have hadj : (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv
      (relativeDifferentials p) (relativeDifferentials p') c).val.app (op U)).hom
        ((universalRelativeDerivation p).d a) =
      c.val.app (op (f ⁻¹ᵁ U))
        ((((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
          (relativeDifferentials p)).val.app (op U)) ((universalRelativeDerivation p).d a)) := rfl
  refine (PresheafOfModules.naturality_apply c.val (homOfLE h).op _).trans ?_
  refine (congrArg (fun z => ((relativeDifferentials p').val.map (homOfLE h).op) z)
    (hadj.symm.trans hkey)).trans ?_
  exact ((universalRelativeDerivation p').d_map (homOfLE h).op ((f.app U).hom a)).symm

/-- **Stacks Project, Tag 01V0.** For a cartesian square of schemes with left edge `f' : X' ⟶ S'`,
right edge `f : X ⟶ S` and top edge `g' : X' ⟶ X`, the canonical map
`g'^* Ω_{X/S} ⟶ Ω_{X'/S'}` of Tag 01UV is an isomorphism. -/
theorem isIso_relativeDifferentialsMap_of_isPullback {X' X S' S : Scheme.{u}} (g' : X' ⟶ X)
    (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (h : IsPullback g' f' f g) :
    IsIso (relativeDifferentialsMap g' f f' g h.w) := by
  refine isIso_relativeDifferentialsMap_of_stalk g' f f' g h.w fun x => ?_
  intro R A B C
  let : Algebra R A := (f.stalkMap (g'.base x)).hom.toAlgebra
  let : Algebra A C := (g'.stalkMap x).hom.toAlgebra
  let : Algebra B C := (f'.stalkMap x).hom.toAlgebra
  let : Algebra R B :=
    (eqToHom (congrArg (fun z => S.presheaf.stalk z)
        (congrArg (fun k : X' ⟶ S => k.base x) h.w)) ≫ g.stalkMap (f'.base x)).hom.toAlgebra
  obtain ⟨φ, hleft, hright, M, hloc⟩ :=
    BaseChangeStalk.cartesian_stalk_isLocalization g' f' f g h x
  let T : Type u := TensorProduct R A B
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let : Algebra T C := φ.toAlgebra
  let : IsScalarTower A T C :=
    IsScalarTower.of_algebraMap_eq fun a => (DFunLike.congr_fun hleft a).symm
  let : IsScalarTower B T C :=
    IsScalarTower.of_algebraMap_eq fun b => (DFunLike.congr_fun hright b).symm
  let : Algebra.IsPushout R B A T :=
    (inferInstance : Algebra.IsPushout R A B (TensorProduct R A B)).symm
  let M' : Submonoid T := M
  let : IsLocalization M' C := hloc
  let : Algebra.FormallyEtale T C := Algebra.FormallyEtale.of_isLocalization M'
  exact ⟨KaehlerDifferential.tensorKaehlerEquivOfFormallyEtalePushout R A B T C,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtalePushout_tmul_D R A B T C⟩

end AlgebraicGeometry.Scheme.Hom
end
end ZInQ.Contrib.CloudB3W16Cartier.Vendor
