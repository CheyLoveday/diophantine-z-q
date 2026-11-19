import ZInQKernel.Contrib.RC53Assist.G0Prints.Shimura
import Mathlib.RingTheory.Kaehler.JacobiZariski
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Smooth.Field

/-!
# Injectivity of differential pullback from a genuine quotient

A dominant morphism in characteristic zero pulls rational differentials
injectively. The map on actual global differential sheaf sections is the
existing universal-derivation pullback. Its generic stalk is identified with
the actual Kähler map, not an independently chosen vector-space map.

This gives the dimension of Shimura's quotient directly from clause (iv),
without any assertion identifying holomorphic and algebraic differentials
and without an invariant-differential trivialization.

Locators: Shimura 1973, Theorem 1(iv), p. 526; Stacks Tags 01UM and 00S2;
Silverman II.4, pullback of rational differentials in characteristic zero.
-/

noncomputable section

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ZInQ.Contrib.RC53Assist.G0Prints

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open Module KaehlerDifferential
open ZInQ.Contrib.RC53Assist.AbelianCurve
open ZInQ.Contrib.RC53Assist.AbelianCurveInputs
open scoped TensorProduct

/-- **PROVED**, the rational Kähler map of an essentially finite type
characteristic-zero field extension is injective. The Jacobi–Zariski
sequence has zero left term because the extension is formally smooth.
Locator: Stacks Tag 00S2 and characteristic-zero separability. -/
theorem kaehlerMap_injective_of_essFiniteType
    {K F L : Type} [Field K] [Field F] [Field L]
    [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L]
    [CharZero F] [Algebra.EssFiniteType F L] :
    Function.Injective (KaehlerDifferential.map K K F L) := by
  have : Algebra.FormallySmooth F L := inferInstance
  have hbc : Function.Injective (KaehlerDifferential.mapBaseChange K F L) := by
    rw [← LinearMap.ker_eq_bot]
    rw [LinearMap.exact_iff.mp (Algebra.H1Cotangent.exact_δ_mapBaseChange (R := K)
      (S := F) (T := L))]
    apply LinearMap.range_eq_bot.mpr
    ext x
    rw [Subsingleton.elim x 0, map_zero, LinearMap.zero_apply]
  rw [injective_iff_map_eq_zero]
  intro ω hω
  have ht : (1 : L) ⊗ₜ[F] ω = 0 := hbc (by
    rw [KaehlerDifferential.mapBaseChange_tmul, one_smul, hω, map_zero])
  exact (Module.FaithfullyFlat.one_tmul_eq_zero_iff F (KaehlerDifferential K F) ω).mp ht

/-- **PROVED SCALAR LAW**, the actual sheaf germ respects multiplication
by a scalar germ. Locator: local-ring actions on sheaf stalks. -/
theorem moduleGerm_smul {Z : Scheme.{0}} (M : Z.Modules) (p : Z)
    (U : Z.Opens) (hp : p ∈ U) (a : Γ(Z, U)) (s : Γ(M, U)) :
    M.presheaf.germ U p hp (a • s) =
      Z.presheaf.germ U p hp a • M.presheaf.germ U p hp s :=
  PresheafOfModules.germ_smul (R := Z.presheaf) M.val p U hp a s

/-- **PROVED CONSTRUCTION**, a compatible germ scalar law gives linearity
on the actual stalk. Locator: local-ring actions on sheaf stalks. -/
def stalkLinearMapFromGerms {Z : Scheme.{0}} {M : Z.Modules} (p : Z)
    (N : Type) [AddCommGroup N] [Module (Z.presheaf.stalk p) N]
    (l : M.presheaf.stalk p →+ N)
    (hl : ∀ (U : Z.Opens) (hp : p ∈ U) (a : Γ(Z, U)) (s : Γ(M, U)),
      l (M.presheaf.germ U p hp (a • s)) =
        Z.presheaf.germ U p hp a • l (M.presheaf.germ U p hp s)) :
    M.presheaf.stalk p →ₗ[Z.presheaf.stalk p] N where
  __ := l
  map_smul' r ξ := by
    obtain ⟨U, hpU, a, rfl⟩ := Z.presheaf.exists_germ_eq r
    obtain ⟨V, hpV, s, rfl⟩ := M.presheaf.exists_germ_eq ξ
    have hpUV : p ∈ U ⊓ V := ⟨hpU, hpV⟩
    rw [← Z.presheaf.germ_res_apply (homOfLE (inf_le_left : U ⊓ V ≤ U)) p hpUV a,
      ← M.presheaf.germ_res_apply (homOfLE (inf_le_right : U ⊓ V ≤ V)) p hpUV s,
      ← moduleGerm_smul M p (U ⊓ V) hpUV]
    exact hl _ hpUV _ _

section Dominant

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

/-- **DEFINITION**, the actual pullback of rational functions, with its
rational scalar compatibility. Locator: a dominant morphism on generic stalks. -/
def dominantFunctionFieldMap (f : X ⟶ Spec (.of ℚ)) (g : Y ⟶ Spec (.of ℚ))
    (i : X ⟶ Y) [IsDominant i] :
    letI := functionFieldAlgebra f
    letI := functionFieldAlgebra g
    Y.functionField →ₐ[ℚ] X.functionField := by
  letI := functionFieldAlgebra f
  letI := functionFieldAlgebra g
  exact { i.functionFieldMap.hom with
    commutes' := fun r => RingHom.map_rat_algebraMap i.functionFieldMap.hom r }

/-- **PROVED**, the actual generic pullback of a locally finite type
morphism is essentially finite type. Locator: finite type on local stalks. -/
theorem functionFieldMap_essFiniteType (i : X ⟶ Y) [IsDominant i]
    [LocallyOfFiniteType i] : i.functionFieldMap.hom.EssFiniteType := by
  let h := i.genericPoint_eq_of_isDominant
  let s := Y.presheaf.stalkSpecializes (specializes_of_eq h)
  letI : IsIso s :=
    ⟨Y.presheaf.stalkSpecializes (specializes_of_eq h.symm), by
      rw [TopCat.Presheaf.stalkSpecializes_comp]
      exact TopCat.Presheaf.stalkSpecializes_refl _ _, by
      rw [TopCat.Presheaf.stalkSpecializes_comp]
      exact TopCat.Presheaf.stalkSpecializes_refl _ _⟩
  change ((i.stalkMap (genericPoint X)).hom.comp s.hom).EssFiniteType
  exact (RingHom.FiniteType.of_surjective s.hom
    (ConcreteCategory.bijective_of_isIso s).2).essFiniteType.comp
      (LocallyOfFiniteType.stalkMap i (genericPoint X))

/-- **PROVED**, generic neighborhoods pull back to generic neighborhoods.
Locator: a dominant morphism sends the generic point to the generic point. -/
theorem generic_mem_dominant_preimage (i : X ⟶ Y) [IsDominant i]
    (U : Y.Opens) (hp : genericPoint Y ∈ U) : genericPoint X ∈ i ⁻¹ᵁ U := by
  change i (genericPoint X) ∈ U
  rw [i.genericPoint_eq_of_isDominant]
  exact hp

/-- **DEFINITION**, the compatible germ maps of the actual sheaf pullback.
Locator: the stalk colimit of the sheaf of relative differentials. -/
def dominantDifferentialCocone (f : X ⟶ Spec (.of ℚ)) (g : Y ⟶ Spec (.of ℚ))
    (i : X ⟶ Y) [IsDominant i] (hi : i ≫ g = f) :
    Cocone ((OpenNhds.inclusion (genericPoint Y)).op ⋙ (differentialSheaf g).presheaf) where
  pt := (differentialSheaf f).presheaf.stalk (genericPoint X)
  ι :=
    { app := fun U => (differentialPullbackSheaf f g i hi).app U.unop.1 ≫
        (differentialSheaf f).presheaf.germ (i ⁻¹ᵁ U.unop.1) (genericPoint X)
          (generic_mem_dominant_preimage i U.unop.1 U.unop.2)
      naturality := by
        intro U V j
        ext s
        have hα := (differentialPullbackSheaf f g i hi).mapPresheaf.naturality_apply
          ((OpenNhds.inclusion (genericPoint Y)).op.map j) s
        have hres := (differentialSheaf f).presheaf.germ_res_apply'
          ((Opens.map i.base).map
            (((OpenNhds.inclusion (genericPoint Y)).op.map j).unop)).op
          (genericPoint X) (generic_mem_dominant_preimage i V.unop.1 V.unop.2)
          ((differentialPullbackSheaf f g i hi).app U.unop.1 s)
        exact (congrArg ((differentialSheaf f).presheaf.germ (i ⁻¹ᵁ V.unop.1)
          (genericPoint X) (generic_mem_dominant_preimage i V.unop.1 V.unop.2)) hα).trans hres }

/-- **DEFINITION**, generic-stalk pullback induced by the actual sheaf map.
Locator: the universal property of the stalk colimit. -/
def dominantDifferentialPullbackAdd (f : X ⟶ Spec (.of ℚ))
    (g : Y ⟶ Spec (.of ℚ)) (i : X ⟶ Y) [IsDominant i] (hi : i ≫ g = f) :
    (differentialSheaf g).presheaf.stalk (genericPoint Y) →+
      (differentialSheaf f).presheaf.stalk (genericPoint X) :=
  ConcreteCategory.hom (colimit.desc _ (dominantDifferentialCocone f g i hi))

/-- **PROVED**, the generic pullback is the actual sheaf map on every germ.
Locator: the stalk colimit's factorization identity. -/
theorem dominantDifferentialPullbackAdd_germ (f : X ⟶ Spec (.of ℚ))
    (g : Y ⟶ Spec (.of ℚ)) (i : X ⟶ Y) [IsDominant i] (hi : i ≫ g = f)
    (U : Y.Opens) (hp : genericPoint Y ∈ U) (s : Γ(differentialSheaf g, U)) :
    dominantDifferentialPullbackAdd f g i hi
      ((differentialSheaf g).presheaf.germ U (genericPoint Y) hp s) =
      (differentialSheaf f).presheaf.germ (i ⁻¹ᵁ U) (genericPoint X)
        (generic_mem_dominant_preimage i U hp) ((differentialPullbackSheaf f g i hi).app U s) := by
  have hc := (colimit.isColimit
    ((OpenNhds.inclusion (genericPoint Y)).op ⋙ (differentialSheaf g).presheaf)).fac
      (dominantDifferentialCocone f g i hi) (op ⟨U, hp⟩)
  exact ConcreteCategory.congr_hom hc s

/-- **DEFINITION**, linearity over the source function field is inherited
from the actual rational-function pullback and the germ scalar law.
Locator: pullback of rational functions and sheaf differentials. -/
def dominantDifferentialPullback (f : X ⟶ Spec (.of ℚ))
    (g : Y ⟶ Spec (.of ℚ)) (i : X ⟶ Y) [IsDominant i] (hi : i ≫ g = f) :
    letI := functionFieldAlgebra f
    letI := functionFieldAlgebra g
    letI : Module Y.functionField ((differentialSheaf f).presheaf.stalk (genericPoint X)) :=
      Module.compHom _ i.functionFieldMap.hom
    (differentialSheaf g).presheaf.stalk (genericPoint Y) →ₗ[Y.functionField]
      (differentialSheaf f).presheaf.stalk (genericPoint X) := by
  letI := functionFieldAlgebra f
  letI := functionFieldAlgebra g
  let σ := dominantFunctionFieldMap f g i
  letI : Module Y.functionField ((differentialSheaf f).presheaf.stalk (genericPoint X)) :=
    Module.compHom _ i.functionFieldMap.hom
  refine stalkLinearMapFromGerms (genericPoint Y)
    ((differentialSheaf f).presheaf.stalk (genericPoint X))
      (dominantDifferentialPullbackAdd f g i hi) ?_
  intro U hp a s
  let : Nonempty U := ⟨⟨genericPoint Y, hp⟩⟩
  rw [dominantDifferentialPullbackAdd_germ, dominantDifferentialPullbackAdd_germ,
    (differentialPullbackSheaf f g i hi).app_smul]
  let t : Γ(differentialSheaf f, i ⁻¹ᵁ U) := (differentialPullbackSheaf f g i hi).app U s
  change (differentialSheaf f).presheaf.germ (i ⁻¹ᵁ U) (genericPoint X)
      (generic_mem_dominant_preimage i U hp) (i.app U a • t) =
    σ (Y.presheaf.germ U (genericPoint Y) hp a) •
      (differentialSheaf f).presheaf.germ (i ⁻¹ᵁ U) (genericPoint X)
        (generic_mem_dominant_preimage i U hp) t
  rw [moduleGerm_smul (differentialSheaf f)]
  exact congrArg (fun r : X.functionField => r •
    (differentialSheaf f).presheaf.germ (i ⁻¹ᵁ U) (genericPoint X)
      (generic_mem_dominant_preimage i U hp) t)
    (ConcreteCategory.congr_hom (i.germToFunctionField_functionFieldMap U) a).symm

/-- **PROVED**, the generic pullback computes on a sheaf section germ.
Locator: the stalk colimit and universal sheaf pullback. -/
theorem dominantDifferentialPullback_germ (f : X ⟶ Spec (.of ℚ))
    (g : Y ⟶ Spec (.of ℚ)) (i : X ⟶ Y) [IsDominant i] (hi : i ≫ g = f)
    (U : Y.Opens) (hp : genericPoint Y ∈ U) (s : Γ(differentialSheaf g, U)) :
    letI := functionFieldAlgebra f
    letI := functionFieldAlgebra g
    letI : Module Y.functionField ((differentialSheaf f).presheaf.stalk (genericPoint X)) :=
      Module.compHom _ i.functionFieldMap.hom
    dominantDifferentialPullback f g i hi
      ((differentialSheaf g).presheaf.germ U (genericPoint Y) hp s) =
      (differentialSheaf f).presheaf.germ (i ⁻¹ᵁ U) (genericPoint X)
        (generic_mem_dominant_preimage i U hp) ((differentialPullbackSheaf f g i hi).app U s) :=
  dominantDifferentialPullbackAdd_germ f g i hi U hp s

/-- **PROVED NATURALITY**, generic sheaf pullback is the actual Kähler map
of the rational-function pullback. The proof checks universal derivatives
of section germs, not a vector-space dimension.
Locator: Stacks Tag 01UM, the universal derivation. -/
theorem dominantDifferentialPullback_kaehler (f : X ⟶ Spec (.of ℚ))
    (g : Y ⟶ Spec (.of ℚ)) (i : X ⟶ Y) [IsDominant i] (hi : i ≫ g = f) :
    letI := functionFieldAlgebra f
    letI := functionFieldAlgebra g
    letI : Algebra Y.functionField X.functionField := i.functionFieldMap.hom.toAlgebra
    letI : IsScalarTower ℚ Y.functionField X.functionField :=
      IsScalarTower.of_algebraMap_eq fun c =>
        ((dominantFunctionFieldMap f g i).commutes c).symm
    letI : Module Y.functionField ((differentialSheaf f).presheaf.stalk (genericPoint X)) :=
      Module.compHom _ i.functionFieldMap.hom
    ∀ η : KaehlerDifferential ℚ Y.functionField,
      dominantDifferentialPullback f g i hi (stalkKaehlerEquiv g (genericPoint Y) η) =
        stalkKaehlerEquiv f (genericPoint X)
          (KaehlerDifferential.map ℚ ℚ Y.functionField X.functionField η) := by
  letI := functionFieldAlgebra f
  letI := functionFieldAlgebra g
  let σ := dominantFunctionFieldMap f g i
  letI : Algebra Y.functionField X.functionField := i.functionFieldMap.hom.toAlgebra
  letI : IsScalarTower ℚ Y.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq fun c => (σ.commutes c).symm
  let M := differentialSheaf f
  letI : Module ℚ (M.presheaf.stalk (genericPoint X)) :=
    Module.compHom _ (algebraMap ℚ X.functionField)
  letI : Module Y.functionField (M.presheaf.stalk (genericPoint X)) :=
    Module.compHom _ i.functionFieldMap.hom
  letI : IsScalarTower Y.functionField X.functionField (M.presheaf.stalk (genericPoint X)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : IsScalarTower ℚ Y.functionField (M.presheaf.stalk (genericPoint X)) :=
    IsScalarTower.of_algebraMap_smul fun c ξ => by
      change σ (algebraMap ℚ Y.functionField c) • ξ = algebraMap ℚ X.functionField c • ξ
      rw [σ.commutes]
  let L := dominantDifferentialPullback f g i hi ∘ₗ
    (stalkKaehlerEquiv g (genericPoint Y)).toLinearMap
  let R := ((stalkKaehlerEquiv f (genericPoint X)).restrictScalars Y.functionField).toLinearMap
    ∘ₗ KaehlerDifferential.map ℚ ℚ Y.functionField X.functionField
  have heq : L = R := by
    apply Derivation.liftKaehlerDifferential_unique
    ext z
    obtain ⟨U, hp, a, rfl⟩ := Y.presheaf.exists_germ_eq z
    letI : Nonempty U := ⟨⟨genericPoint Y, hp⟩⟩
    change dominantDifferentialPullback f g i hi
        (stalkKaehlerEquiv g (genericPoint Y)
          (D ℚ Y.functionField (Y.presheaf.germ U (genericPoint Y) hp a))) =
      stalkKaehlerEquiv f (genericPoint X)
        (KaehlerDifferential.map ℚ ℚ Y.functionField X.functionField
          (D ℚ Y.functionField (Y.presheaf.germ U (genericPoint Y) hp a)))
    rw [stalkKaehlerEquiv_D_germ, dominantDifferentialPullback_germ,
      differentialPullbackSheaf_D, KaehlerDifferential.map_D]
    change M.presheaf.germ (i ⁻¹ᵁ U) (genericPoint X)
        (generic_mem_dominant_preimage i U hp)
        ((differentialDerivation f).d (X := op (i ⁻¹ᵁ U)) (i.app U a)) =
      stalkKaehlerEquiv f (genericPoint X)
        (D ℚ X.functionField (σ (Y.presheaf.germ U (genericPoint Y) hp a)))
    rw [show σ (Y.presheaf.germ U (genericPoint Y) hp a) =
        X.presheaf.germ (i ⁻¹ᵁ U) (genericPoint X)
          (generic_mem_dominant_preimage i U hp) (i.app U a) from
      ConcreteCategory.congr_hom (i.germToFunctionField_functionFieldMap U) a]
    exact (stalkKaehlerEquiv_D_germ f (genericPoint X) (i ⁻¹ᵁ U)
      (generic_mem_dominant_preimage i U hp) (i.app U a)).symm
  intro η
  exact LinearMap.congr_fun heq η

/-- **PROVED**, the global and generic sheaf pullbacks have the same germ
at the generic point. Locator: naturality of restriction to the top open. -/
theorem dominantDifferentialPullback_global_germ (f : X ⟶ Spec (.of ℚ))
    (g : Y ⟶ Spec (.of ℚ)) (i : X ⟶ Y) [IsDominant i] (hi : i ≫ g = f) :
    letI := functionFieldAlgebra f
    letI := functionFieldAlgebra g
    letI := globalSectionsModule g (differentialSheaf g)
    letI := globalSectionsModule f (differentialSheaf f)
    letI : Module Y.functionField ((differentialSheaf f).presheaf.stalk (genericPoint X)) :=
      Module.compHom _ i.functionFieldMap.hom
    ∀ s : Γ(differentialSheaf g, ⊤),
      dominantDifferentialPullback f g i hi
        ((differentialSheaf g).presheaf.germ ⊤ (genericPoint Y) trivial s) =
        (differentialSheaf f).presheaf.germ ⊤ (genericPoint X) trivial
          (globalDifferentialPullback f g i hi s) := by
  letI := functionFieldAlgebra f
  letI := functionFieldAlgebra g
  letI := globalSectionsModule g (differentialSheaf g)
  letI := globalSectionsModule f (differentialSheaf f)
  letI : Module Y.functionField ((differentialSheaf f).presheaf.stalk (genericPoint X)) :=
    Module.compHom _ i.functionFieldMap.hom
  intro s
  rw [dominantDifferentialPullback_germ]
  change (differentialSheaf f).presheaf.germ (i ⁻¹ᵁ ⊤) (genericPoint X)
      (generic_mem_dominant_preimage i ⊤ trivial) ((differentialPullbackSheaf f g i hi).app ⊤ s) =
    (differentialSheaf f).presheaf.germ ⊤ (genericPoint X) trivial
      ((differentialSheaf f).presheaf.map (eqToHom (Opens.map_top i.base).symm).op
        ((differentialPullbackSheaf f g i hi).app ⊤ s))
  exact ((differentialSheaf f).presheaf.germ_res_apply
    (eqToHom (Opens.map_top i.base).symm) (genericPoint X) trivial _).symm

/-- **PROVED NATURALITY**, actual global sheaf pullback commutes with
restriction to rational Kähler differentials along a dominant morphism.
Locator: the universal derivation and the generic-stalk calculation. -/
theorem dominantRationalRestriction_pullback (f : X ⟶ Spec (.of ℚ))
    (g : Y ⟶ Spec (.of ℚ)) (i : X ⟶ Y) [IsDominant i] (hi : i ≫ g = f) :
    letI := functionFieldAlgebra f
    letI := functionFieldAlgebra g
    letI := globalSectionsModule g (differentialSheaf g)
    letI := globalSectionsModule f (differentialSheaf f)
    letI : Algebra Y.functionField X.functionField := i.functionFieldMap.hom.toAlgebra
    letI : IsScalarTower ℚ Y.functionField X.functionField :=
      IsScalarTower.of_algebraMap_eq fun c =>
        ((dominantFunctionFieldMap f g i).commutes c).symm
    ∀ s : Γ(differentialSheaf g, ⊤),
      canonicalRationalRestriction f (globalDifferentialPullback f g i hi s) =
        KaehlerDifferential.map ℚ ℚ Y.functionField X.functionField
          (canonicalRationalRestriction g s) := by
  letI := functionFieldAlgebra f
  letI := functionFieldAlgebra g
  letI := globalSectionsModule g (differentialSheaf g)
  letI := globalSectionsModule f (differentialSheaf f)
  letI : Algebra Y.functionField X.functionField := i.functionFieldMap.hom.toAlgebra
  letI : IsScalarTower ℚ Y.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq fun c =>
      ((dominantFunctionFieldMap f g i).commutes c).symm
  letI : Module Y.functionField ((differentialSheaf f).presheaf.stalk (genericPoint X)) :=
    Module.compHom _ i.functionFieldMap.hom
  intro s
  apply (stalkKaehlerEquiv f (genericPoint X)).injective
  rw [canonicalRationalRestriction_generic, ← dominantDifferentialPullback_kaehler,
    canonicalRationalRestriction_generic, dominantDifferentialPullback_global_germ]

/-- **PROVED INJECTIVITY**, a dominant locally finite type morphism in
characteristic zero pulls global differentials of a smooth integral curve
injectively. The domain of the morphism need not be a curve.
Locator: separability, Stacks Tag 00S2, and generic restriction. -/
theorem globalDifferentialPullback_injective_of_dominant
    (f : X ⟶ Spec (.of ℚ)) (g : Y ⟶ Spec (.of ℚ)) [Smooth g]
    (hdY : topologicalKrullDim Y = 1) (i : X ⟶ Y) [IsDominant i]
    [LocallyOfFiniteType i] (hi : i ≫ g = f) :
    letI := globalSectionsModule g (differentialSheaf g)
    letI := globalSectionsModule f (differentialSheaf f)
    Function.Injective (globalDifferentialPullback f g i hi) := by
  letI := functionFieldAlgebra f
  letI := functionFieldAlgebra g
  letI := globalSectionsModule g (differentialSheaf g)
  letI := globalSectionsModule f (differentialSheaf f)
  letI : Algebra Y.functionField X.functionField := i.functionFieldMap.hom.toAlgebra
  letI : IsScalarTower ℚ Y.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq fun c =>
      ((dominantFunctionFieldMap f g i).commutes c).symm
  have hEss : Algebra.EssFiniteType Y.functionField X.functionField :=
    (RingHom.essFiniteType_algebraMap).mp (functionFieldMap_essFiniteType i)
  let : CharZero Y.functionField := algebraRat.charZero Y.functionField
  have hR := rationalRestriction_injective g (canonicalDifferentialStalkData g)
    (stalkKaehlerMap_injective LocalFacts.localUniformizerBasis g hdY)
  intro s t hst
  apply hR
  change canonicalRationalRestriction g s = canonicalRationalRestriction g t
  apply kaehlerMap_injective_of_essFiniteType (K := ℚ)
    (F := Y.functionField) (L := X.functionField)
  rw [← dominantRationalRestriction_pullback f g i hi,
    ← dominantRationalRestriction_pullback f g i hi, hst]

end Dominant

/-- **PROVED INJECTIVITY**, the actual complex differential pullback from a
one-dimensional quotient abelian variety is injective. Surjectivity and
finite type are properties of the actual morphism; scalar extension is flat.
Locator: Shimura 1973, Theorem 1(i),(iv), p. 526. -/
theorem shimuraDelta_injective {J A : PkgI3.AbVar ℚ}
    (ν : PkgI3.AbVar.Hom J A) (hν : Surjective ν.hom.left) (hdim : A.dim = 1) :
    Function.Injective (shimuraDelta ν) := by
  letI := abelian_scheme_integral J.X
  letI := abelian_scheme_integral A.X
  letI : Surjective ν.hom.left := hν
  have : LocallyOfFiniteType (ν.hom.left ≫ A.X.hom) := by
    rw [ν.hom.w]
    infer_instance
  have : LocallyOfFiniteType ν.hom.left := locallyOfFiniteType_of_comp _ A.X.hom
  have h := globalDifferentialPullback_injective_of_dominant J.X.hom A.X.hom
    hdim ν.hom.left ν.hom.w
  unfold shimuraDelta
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := ℂ) _ h

end ZInQ.Contrib.RC53Assist.G0Prints
