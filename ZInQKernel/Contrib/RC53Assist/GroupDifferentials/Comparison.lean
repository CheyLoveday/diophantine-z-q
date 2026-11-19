import ZInQKernel.Contrib.RC53Assist.AbelianCurve.DifferentialLine
import ZInQKernel.Contrib.CloudB3W16Cartier.GroupDifferentials
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.Differentials

/-!
# Two constructions of the sheaf of relative differentials agree

For a morphism of schemes `f : X ⟶ S`, the repository contains two formal constructions of
the sheaf `Ω_{X/S}` of the Stacks Project, Definition 29.33.1 (Tag 01UM), namely the sheaf of
differentials of the structure map `f⁻¹𝒪_S ⟶ 𝒪_X`.

* The *presheaf construction*: `AbelianCurve.differentialSheaf f`, which is by definition the
  same term as `Scheme.Hom.relativeDifferentials f` of the vendored Jacobian-Challenge library.
  It is the sheafification of the presheaf `U ↦ Ω_{𝒪_X(U) / (f⁻¹𝒪_S)(U)}`, where `f⁻¹𝒪_S` is
  the *presheaf* inverse image.
* The *sheaf construction* of the vendored AxiomMath/Stacks library (adapted in
  `ZInQKernel/Contrib/CloudB3W16Cartier`): the sheaf of `𝒪_X`-modules representing derivations
  of `𝒪_X` relative to the *sheaf* inverse image `f⁻¹𝒪_S` (Stacks, Lemma 17.28.2, Tag 08RM).

This file proves that the two sheaves are isomorphic. Both represent derivations of `𝒪_X`
into sheaves of modules; the only point is that a derivation into a *sheaf* of modules which
kills the image of the presheaf inverse image also kills the image of the sheaf inverse image.
This is proved with the square-zero extension `𝒪_X ⊕ M`, a sheaf of rings: the derivation is a
section `a ↦ (a, D a)` of the projection, and the two composites with the structure map out of
the sheaf inverse image agree because their adjuncts under the inverse-image/pushforward
adjunction of sheaves of rings agree, which is the statement that `D` kills every `f^♯ a`.

All declarations are proved; nothing is assumed.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.GroupDifferentials

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open ZInQ.Contrib.CloudB3W16Cartier.Vendor.AlgebraicGeometry.SheafOfModules
open scoped ZInQ.Contrib.CloudB3W16Cartier.Vendor.AlgebraicGeometry.SheafOfModules

attribute [local instance] ZInQ.Contrib.CloudB3W16Cartier.Vendor.Stacks.Smooth.moduleMulOpposite

universe u

/-- GLUE (definitional). The presheaf construction used by the abelian-curve reduction is the
vendored Jacobian-Challenge sheaf of relative differentials, as the same term.
Locators: `AbelianCurve.differentialSheaf` in
`ZInQKernel/Contrib/RC53Assist/AbelianCurve/DifferentialLine.lean`;
`Scheme.Hom.relativeDifferentials` in
`ZInQKernel/Contrib/CloudW07JacobiansCurves/Jacobian/AlgebraicGeometry/Modules/Differentials.lean`.
-/
theorem differentialSheaf_eq_relativeDifferentials {X S : Scheme.{0}} (f : X ⟶ S) :
    AbelianCurve.differentialSheaf f = f.relativeDifferentials :=
  rfl

/-- DEFINITION. The structure map `f⁻¹𝒪_S ⟶ 𝒪_X` out of the sheaf inverse image, the adjunct
of `f^♯` under the inverse-image/pushforward adjunction of sheaves of commutative rings.
Locator: vendored `inverseImageStructureMap`, file
`StacksFrontier/AlgebraicGeometry/Morphisms/Affine/Over.lean` of the vendored library under
`ZInQKernel/Contrib/CloudB3W16Cartier/Vendor`. -/
abbrev sheafInverseImageMap {X S : Scheme.{u}} (f : X ⟶ S) :
    (TopCat.Sheaf.pullback CommRingCat f.base).obj S.sheaf ⟶ X.sheaf :=
  ZInQ.Contrib.CloudB3W16Cartier.Vendor.AlgebraicGeometry.inverseImageStructureMap f

/-- DEFINITION. The sheaf construction of `Ω_{X/S}`: the sheaf of modules representing
derivations relative to `sheafInverseImageMap f`. Locator: vendored `relativeDifferentials`,
file `StacksFrontier/AlgebraicGeometry/Morphisms/Differentials/Relative.lean` of the vendored
library under `ZInQKernel/Contrib/CloudB3W16Cartier/Vendor`; Stacks, Definition 29.33.1
(Tag 01UM) and Lemma 17.28.2 (Tag 08RM). -/
abbrev sheafDifferentials {X S : Scheme.{u}} (f : X ⟶ S) : X.Modules :=
  ZInQ.Contrib.CloudB3W16Cartier.Vendor.AlgebraicGeometry.Scheme.Hom.relativeDifferentials f

/-- DEFINITION. The universal derivation of the sheaf construction. Locator: vendored
`universalRelativeDerivation`, in the same file as `sheafDifferentials`. -/
abbrev sheafUniversalDerivation {X S : Scheme.{u}} (f : X ⟶ S) :
    SheafDerivation (sheafInverseImageMap f) (sheafDifferentials f) :=
  ZInQ.Contrib.CloudB3W16Cartier.Vendor.AlgebraicGeometry.Scheme.Hom.universalRelativeDerivation f

/-- DEFINITION. Over one open set, the ring map `a ↦ (a, D a)` into the square-zero extension
`𝒪_X(V) ⊕ M(V)`, for a derivation `D` relative to the presheaf inverse image. Locator: the
vendored `sqZeroRingHom` (`.../AlgebraicGeometry/Smooth/SqZeroAlgebra.lean`). -/
def derivationSectionApp {X S : Scheme.{u}} (f : X ⟶ S)
    (M : SheafOfModules (underlyingRingSheaf X.sheaf))
    (D : PresheafOfModulesOfCommRing.Derivation' M.val f.pullbackPresheafToPresheaf)
    (V : X.Opensᵒᵖ) :
    X.sheaf.obj.obj V ⟶ (sqZeroPresheaf X.sheaf M).obj V :=
  CommRingCat.ofHom (ZInQ.Contrib.CloudB3W16Cartier.Vendor.Stacks.Smooth.sqZeroRingHom
    (RingHom.id _) D.d fun a b ↦ D.d_mul a b)

/-- PROVED. The first component of `derivationSectionApp` is the identity.
Locator: vendored `sqZeroRingHom_fst`. -/
theorem derivationSectionApp_fst {X S : Scheme.{u}} (f : X ⟶ S)
    (M : SheafOfModules (underlyingRingSheaf X.sheaf))
    (D : PresheafOfModulesOfCommRing.Derivation' M.val f.pullbackPresheafToPresheaf)
    (V : X.Opensᵒᵖ) (a : X.sheaf.obj.obj V) :
    ((derivationSectionApp f M D V).hom a).fst = a :=
  (ZInQ.Contrib.CloudB3W16Cartier.Vendor.Stacks.Smooth.sqZeroRingHom_fst _ _
    (fun a b ↦ D.d_mul a b) a).trans (RingHom.id_apply a)

/-- PROVED. The second component of `derivationSectionApp` is the derivation.
Locator: vendored `sqZeroRingHom_snd`. -/
theorem derivationSectionApp_snd {X S : Scheme.{u}} (f : X ⟶ S)
    (M : SheafOfModules (underlyingRingSheaf X.sheaf))
    (D : PresheafOfModulesOfCommRing.Derivation' M.val f.pullbackPresheafToPresheaf)
    (V : X.Opensᵒᵖ) (a : X.sheaf.obj.obj V) :
    ((derivationSectionApp f M D V).hom a).snd = D.d a :=
  ZInQ.Contrib.CloudB3W16Cartier.Vendor.Stacks.Smooth.sqZeroRingHom_snd _ _
    (fun a b ↦ D.d_mul a b) a

/-- DEFINITION. The morphism of sheaves of commutative rings `𝒪_X ⟶ 𝒪_X ⊕ M`,
`a ↦ (a, D a)`; naturality is the compatibility of `D` with restriction. Locator: the vendored
`sqZeroSheaf` (`.../Topology/Sheaves/Modules/SquareZeroExtension.lean`). -/
def derivationSection {X S : Scheme.{u}} (f : X ⟶ S)
    (M : SheafOfModules (underlyingRingSheaf X.sheaf))
    (D : PresheafOfModulesOfCommRing.Derivation' M.val f.pullbackPresheafToPresheaf) :
    X.sheaf ⟶ sqZeroSheaf X.sheaf M :=
  ObjectProperty.homMk
    { app := derivationSectionApp f M D
      naturality := fun V V' h ↦ CommRingCat.hom_ext (RingHom.ext fun a ↦ by
        change (derivationSectionApp f M D V').hom ((X.sheaf.obj.map h).hom a)
            = ((sqZeroPresheaf X.sheaf M).map h).hom ((derivationSectionApp f M D V).hom a)
        refine TrivSqZeroExt.ext ?_ ?_
        · rw [derivationSectionApp_fst, sqZeroPresheaf_map_fst, derivationSectionApp_fst]
        · exact (derivationSectionApp_snd f M D V' _).trans
            ((D.d_map h a).trans
              ((sqZeroPresheaf_map_snd X.sheaf M h _).trans
                (congrArg (sectionRestrict M h)
                  (derivationSectionApp_snd f M D V a))).symm)) }

/-- PROVED. The section `a ↦ (a, D a)` splits the projection of the square-zero extension.
Locator: vendored `sqZeroProj`; `derivationSectionApp_fst`. -/
theorem derivationSection_comp_proj {X S : Scheme.{u}} (f : X ⟶ S)
    (M : SheafOfModules (underlyingRingSheaf X.sheaf))
    (D : PresheafOfModulesOfCommRing.Derivation' M.val f.pullbackPresheafToPresheaf) :
    derivationSection f M D ≫ sqZeroProj X.sheaf M = 𝟙 X.sheaf :=
  Sheaf.hom_ext (NatTrans.ext (funext fun V ↦ CommRingCat.hom_ext (RingHom.ext fun a ↦
    derivationSectionApp_fst f M D V a)))

/-- PROVED. On the sheaf inverse image the section `a ↦ (a, D a)` agrees with the zero section.
Both composites are adjuncts; after transposition they are maps `𝒪_S ⟶ f_*(𝒪_X ⊕ M)`, which
agree because `D` kills every `f^♯ a` (vendored Jacobian-Challenge `Derivation'.d_app_app`). -/
theorem derivationSection_triv {X S : Scheme.{u}} (f : X ⟶ S)
    (M : SheafOfModules (underlyingRingSheaf X.sheaf))
    (D : PresheafOfModulesOfCommRing.Derivation' M.val f.pullbackPresheafToPresheaf) :
    sheafInverseImageMap f ≫ derivationSection f M D =
      sheafInverseImageMap f ≫ sqZeroInl X.sheaf M := by
  let A := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat f.base
  let c : S.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat f.base).obj X.sheaf := ⟨f.c⟩
  have key : c ≫ (TopCat.Sheaf.pushforward CommRingCat f.base).map (derivationSection f M D) =
      c ≫ (TopCat.Sheaf.pushforward CommRingCat f.base).map (sqZeroInl X.sheaf M) := by
    refine Sheaf.hom_ext (NatTrans.ext (funext fun V ↦ CommRingCat.hom_ext
      (RingHom.ext fun a ↦ ?_)))
    exact TrivSqZeroExt.ext
      ((derivationSectionApp_fst f M D _ _).trans (sqZeroInl_app_apply_fst X.sheaf M _ _).symm)
      ((derivationSectionApp_snd f M D _ _).trans
        ((D.d_app_app V.unop a).trans (sqZeroInl_app_apply_snd X.sheaf M _ _).symm))
  have h1 := A.homEquiv_naturality_right_symm c (derivationSection f M D)
  have h2 := A.homEquiv_naturality_right_symm c (sqZeroInl X.sheaf M)
  exact h1.symm.trans ((congrArg (A.homEquiv _ _).symm key).trans h2)

/-- DEFINITION. A derivation into a sheaf of modules relative to the presheaf inverse image,
read as a derivation relative to the sheaf inverse image (the second component of the split
section `derivationSection`). Locator: vendored `derivationOfSqZeroSection`. -/
def sheafDerivationOf {X S : Scheme.{u}} (f : X ⟶ S)
    (M : SheafOfModules (underlyingRingSheaf X.sheaf))
    (D : PresheafOfModulesOfCommRing.Derivation' M.val f.pullbackPresheafToPresheaf) :
    SheafDerivation (sheafInverseImageMap f) M :=
  derivationOfSqZeroSection X.sheaf M (sheafInverseImageMap f) (derivationSection f M D)
    (derivationSection_comp_proj f M D) (derivationSection_triv f M D)

/-- PROVED. `sheafDerivationOf` does not change the derivation on sections.
Locator: vendored `derivationOfSqZeroSection_d`; `derivationSectionApp_snd`. -/
theorem sheafDerivationOf_d {X S : Scheme.{u}} (f : X ⟶ S)
    (M : SheafOfModules (underlyingRingSheaf X.sheaf))
    (D : PresheafOfModulesOfCommRing.Derivation' M.val f.pullbackPresheafToPresheaf)
    {V : X.Opensᵒᵖ} (a : X.sheaf.obj.obj V) :
    (sheafDerivationOf f M D).d a = D.d a :=
  (derivationOfSqZeroSection_d _ _ _ _ _ _ a).trans (derivationSectionApp_snd f M D V a)

open ZInQ.Contrib.CloudB3W16Cartier.Vendor.AlgebraicGeometry.Scheme.Hom in
/-- PROVED (vendored). The universal derivation of the sheaf construction kills every `f^♯ a`.
Locator: vendored `universalRelativeDerivation_d_app_eq_zero`, in the file of
`sheafDifferentials`. -/
theorem sheafUniversalDerivation_d_app {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens)
    (a : Γ(S, V)) : (sheafUniversalDerivation f).d ((f.app V).hom a) = 0 :=
  universalRelativeDerivation_d_app_eq_zero f V a

/-- DEFINITION. The comparison from the presheaf construction to the sheaf construction, given
by the universal property of the presheaf construction applied to the universal derivation of
the sheaf construction. Locator: vendored Jacobian-Challenge `relativeDifferentialsHomEquiv` and
`derivationMk`; `sheafUniversalDerivation_d_app`. -/
def toSheafDifferentials {X S : Scheme.{u}} (f : X ⟶ S) :
    f.relativeDifferentials ⟶ sheafDifferentials f :=
  (f.relativeDifferentialsHomEquiv _).symm
    (f.derivationMk (sheafUniversalDerivation f).d
      (fun a b ↦ (sheafUniversalDerivation f).d_mul a b)
      (fun i x ↦ (sheafUniversalDerivation f).d_map i x)
      (fun V a ↦ sheafUniversalDerivation_d_app f V a))

/-- PROVED. `toSheafDifferentials` sends `d x` to `d x`.
Locator: vendored Jacobian-Challenge `relativeDifferentialsHomEquiv_symm_app_d`. -/
theorem toSheafDifferentials_app_d {X S : Scheme.{u}} (f : X ⟶ S) {U : X.Opensᵒᵖ}
    (x : X.presheaf.obj U) :
    (toSheafDifferentials f).val.app U (f.relativeDifferentialsDerivation.d x) =
      (sheafUniversalDerivation f).d x :=
  f.relativeDifferentialsHomEquiv_symm_app_d _ x

/-- PROVED. The universal property of the sheaf construction (Stacks, Lemma 17.28.2,
Tag 08RM; vendored `universalDerivation_isUniversal`) applied to the universal derivation of the
presheaf construction, read relative to the sheaf inverse image by `sheafDerivationOf`. -/
theorem existsUnique_fromSheafDifferentials {X S : Scheme.{u}} (f : X ⟶ S) :
    ∃! g : sheafDifferentials f ⟶ f.relativeDifferentials,
      (sheafUniversalDerivation f).postcomp g.val =
        sheafDerivationOf f f.relativeDifferentials f.relativeDifferentialsDerivation :=
  universalDerivation_isUniversal.{u, u, u} (sheafInverseImageMap f) f.relativeDifferentials
    (sheafDerivationOf f f.relativeDifferentials f.relativeDifferentialsDerivation)

/-- DEFINITION. The comparison from the sheaf construction to the presheaf construction, the
morphism of `existsUnique_fromSheafDifferentials` (chosen; it is unique).
Locator: `existsUnique_fromSheafDifferentials`. -/
def fromSheafDifferentials {X S : Scheme.{u}} (f : X ⟶ S) :
    sheafDifferentials f ⟶ f.relativeDifferentials :=
  Classical.choose (existsUnique_fromSheafDifferentials f)

/-- PROVED. `fromSheafDifferentials` sends `d x` to `d x`.
Locator: `existsUnique_fromSheafDifferentials` and `sheafDerivationOf_d`. -/
theorem fromSheafDifferentials_app_d {X S : Scheme.{u}} (f : X ⟶ S) {U : X.Opensᵒᵖ}
    (x : X.presheaf.obj U) :
    (fromSheafDifferentials f).val.app U ((sheafUniversalDerivation f).d x) =
      f.relativeDifferentialsDerivation.d x :=
  (PresheafOfModulesOfCommRing.Derivation.congr_d
    (Classical.choose_spec (existsUnique_fromSheafDifferentials f)).1 x).trans
    (sheafDerivationOf_d f _ _ x)

/-- DEFINITION (with proved inverse laws). The presheaf construction and the sheaf construction
of `Ω_{X/S}` are isomorphic, compatibly with the universal derivations. The two inverse laws
follow from the uniqueness parts of the two universal properties. Locators: vendored
Jacobian-Challenge `relativeDifferentialsHomEquiv`; vendored `universalDerivation_isUniversal`
(Stacks, Lemma 17.28.2, Tag 08RM). -/
def differentialsComparison {X S : Scheme.{u}} (f : X ⟶ S) :
    f.relativeDifferentials ≅ sheafDifferentials f where
  hom := toSheafDifferentials f
  inv := fromSheafDifferentials f
  hom_inv_id := by
    apply (f.relativeDifferentialsHomEquiv _).injective
    refine PresheafOfModulesOfCommRing.Derivation.ext
      (funext fun U ↦ AddMonoidHom.ext fun x ↦ ?_)
    change (fromSheafDifferentials f).val.app U
        ((toSheafDifferentials f).val.app U (f.relativeDifferentialsDerivation.d x)) =
      f.relativeDifferentialsDerivation.d x
    exact (congrArg (fun y ↦ (fromSheafDifferentials f).val.app U y)
      (toSheafDifferentials_app_d f x)).trans (fromSheafDifferentials_app_d f x)
  inv_hom_id := by
    refine (universalDerivation_isUniversal.{u, u, u} (sheafInverseImageMap f)
      (sheafDifferentials f) (sheafUniversalDerivation f)).unique ?_ ?_
    · refine PresheafOfModulesOfCommRing.Derivation.ext
        (funext fun U ↦ AddMonoidHom.ext fun x ↦ ?_)
      change (toSheafDifferentials f).val.app U
          ((fromSheafDifferentials f).val.app U ((sheafUniversalDerivation f).d x)) =
        (sheafUniversalDerivation f).d x
      exact (congrArg (fun y ↦ (toSheafDifferentials f).val.app U y)
        (fromSheafDifferentials_app_d f x)).trans (toSheafDifferentials_app_d f x)
    · rfl

end ZInQ.Contrib.RC53Assist.GroupDifferentials
