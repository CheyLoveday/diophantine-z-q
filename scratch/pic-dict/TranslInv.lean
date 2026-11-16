import ZInQKernel.Contrib.OneProof.PicDictionary
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Picard.Descent

/-! # pic-dict: `PicZeroPtsTranslInv` from two printed leaves (rigidity on `A × Pic⁰`) -/

noncomputable section

set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory Limits
open scoped CategoryTheory.MonObj

namespace PicDict

open T09Pic PkgI3 PkgI3.AbVar HDec.WeilPairing

variable {K : Type} [Field K]

/-- **LEAF (`𝒪_T = f_{T*}𝒪_{A_T}` universally).** For an abelian variety `A` over `K` (proper, flat, with
geometrically integral fibre) and every `K`-scheme `T`, the unit `𝒪_T → (A_T → T)_* 𝒪_{A_T}` is an isomorphism.
EGA III 7.8.6 (cohomology and base change in degree 0); Kleiman, *The Picard scheme*, Ex. 9.3.11 (`𝒪_S = f_*𝒪_X`
holds universally for `f` proper flat with geometrically integral fibres); over a field also flat base change
(Stacks 02KH) with `Γ(A, 𝒪) = K`. Locators UNVERIFIED. -/
def PushforwardUnitUniversal : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (T : Over (Spec (CommRingCat.of K))),
    IsIso (pushforwardUnitMap (pullback.snd A.X.hom T.hom))

/-- **LEAF (products of geometrically integral schemes).** If `X` and `Y` are geometrically integral over a field
`K`, so is `X ×_K Y`. EGA IV 4.6.5 / Stacks, *Varieties*, products of geometrically irreducible and geometrically
reduced schemes (locators UNVERIFIED). Instance for two abelian varieties. -/
def GeomIntegralProd : Prop :=
  ∀ (K : Type) [Field K] (A B : AbVar K), GeometricallyIntegral (A.X ⊗ B.X).hom

section Setup

variable (A : AbVar K)

/-- The zero section `Spec K → A`. -/
abbrev zs : Spec (CommRingCat.of K) ⟶ A.X.left := η[A.X].left

lemma zs_comp : zs A ≫ A.X.hom = 𝟙 _ := Over.w η[A.X]

/-- Translation by a `T`-point `a` on `A ×_K T`. -/
def translT {T : Over (Spec (CommRingCat.of K))} (a : T ⟶ A.X) : A.X ⊗ T ⟶ A.X ⊗ T :=
  CartesianMonoidalCategory.lift
    (CartesianMonoidalCategory.lift (CartesianMonoidalCategory.fst _ _)
      (CartesianMonoidalCategory.snd _ _ ≫ a) ≫ μ[A.X])
    (CartesianMonoidalCategory.snd _ _)

/-- `t_a` on the scheme `A ×_K T`. -/
abbrev trT {T : Over (Spec (CommRingCat.of K))} (a : T ⟶ A.X) :
    pullback A.X.hom T.hom ⟶ pullback A.X.hom T.hom := (translT A a).left

/-- The normalized subfunctor (classes trivial along the zero section). -/
abbrev Nrm : Subfunctor (picardPresheaf A.X.hom) := picardFunctorNormalized A.X.hom (zs A) (zs_comp A)

/-- Kleiman 9.2.5, proved in the vendored library: normalized classes ≅ the Picard sheaf. -/
def Θ (hU : PushforwardUnitUniversal) : (Nrm A).toFunctor ≅ (picardFunctor A.X.hom).obj :=
  picardFunctorNormalizedIso A.X.hom (zs A) (zs_comp A) (hU K A)

lemma Θ_hom_app (hU : PushforwardUnitUniversal) (T) (x) :
    (Θ A hU).hom.app T x = (toPicardFunctor A.X.hom).app T x.1 := rfl

/-- The `T`-section of `A_T` along `0`. -/
abbrev zT (T : Over (Spec (CommRingCat.of K))) : T.left ⟶ pullback A.X.hom T.hom :=
  sectionBaseChange A.X.hom (zs A) (zs_comp A) T

/-- `t_a^*c ⊗ (pr^* 0^* t_a^* c)⁻¹ ⊗ c⁻¹`, the renormalized `φ_c(a)`. -/
def dT {T : Over (Spec (CommRingCat.of K))} (a : T ⟶ A.X) (c : (pullback A.X.hom T.hom).Pic) :
    (pullback A.X.hom T.hom).Pic :=
  Scheme.Pic.map (trT A a) c *
    (Scheme.Pic.map (pullback.snd A.X.hom T.hom) (Scheme.Pic.map (zT A T)
      (Scheme.Pic.map (trT A a) c)))⁻¹ * c⁻¹

lemma dT_mem {T : Over (Spec (CommRingCat.of K))} (a : T ⟶ A.X) (c : (pullback A.X.hom T.hom).Pic)
    (hc : Scheme.Pic.map (zT A T) c = 1) : Scheme.Pic.map (zT A T) (dT A a c) = 1 := by
  have h1 : Scheme.Pic.map (zT A T) (Scheme.Pic.map (pullback.snd A.X.hom T.hom)
      (Scheme.Pic.map (zT A T) (Scheme.Pic.map (trT A a) c))) =
      Scheme.Pic.map (zT A T) (Scheme.Pic.map (trT A a) c) := by
    rw [← Scheme.Pic.map_comp, sectionBaseChange_snd, Scheme.Pic.map_id]
  rw [dT, ← Scheme.Pic.mapHom_apply, map_mul, map_mul, map_inv, map_inv]
  simp only [Scheme.Pic.mapHom_apply]
  rw [h1, hc]
  group

lemma bcm_eq {T T' : Over (Spec (CommRingCat.of K))} (g : T' ⟶ T) :
    JacobianChallenge.baseChangeMap A.X.hom g = (A.X ◁ g).left := by
  apply pullback.hom_ext <;> simp [JacobianChallenge.baseChangeMap]

lemma translT_whisker {T T' : Over (Spec (CommRingCat.of K))} (g : T' ⟶ T) (a : T ⟶ A.X) :
    (A.X ◁ g) ≫ translT A a = translT A (g ≫ a) ≫ (A.X ◁ g) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [translT, CartesianMonoidalCategory.comp_lift_assoc]
  · simp [translT]

lemma dT_natural {T T' : Over (Spec (CommRingCat.of K))} (g : T' ⟶ T) (a : T ⟶ A.X)
    (c : (pullback A.X.hom T.hom).Pic) :
    Scheme.Pic.map (JacobianChallenge.baseChangeMap A.X.hom g) (dT A a c) =
      dT A (g ≫ a) (Scheme.Pic.map (JacobianChallenge.baseChangeMap A.X.hom g) c) := by
  have n1 : JacobianChallenge.baseChangeMap A.X.hom g ≫ trT A a =
      trT A (g ≫ a) ≫ JacobianChallenge.baseChangeMap A.X.hom g := by
    rw [bcm_eq, ← Over.comp_left, ← Over.comp_left, translT_whisker]
  have n2 : JacobianChallenge.baseChangeMap A.X.hom g ≫ pullback.snd A.X.hom T.hom =
      pullback.snd A.X.hom T'.hom ≫ g.left := pullback.lift_snd _ _ _
  have n3 : zT A T' ≫ JacobianChallenge.baseChangeMap A.X.hom g = g.left ≫ zT A T :=
    sectionBaseChange_comp_baseChangeMap _ _ _ g
  rw [dT, dT, ← Scheme.Pic.mapHom_apply, map_mul, map_mul, map_inv, map_inv]
  simp only [Scheme.Pic.mapHom_apply]
  rw [← Scheme.Pic.map_comp, n1, Scheme.Pic.map_comp, ← Scheme.Pic.map_comp _ (pullback.snd _ _), n2,
    Scheme.Pic.map_comp, ← Scheme.Pic.map_comp g.left, ← n3, Scheme.Pic.map_comp,
    ← Scheme.Pic.map_comp _ (trT A a), n1, Scheme.Pic.map_comp]

end Setup

section Psi

variable {A : AbVar K} {P : Over (Spec (CommRingCat.of K))}
  (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (hU : PushforwardUnitUniversal)

/-- The morphism classifying the renormalized `φ_c(a)`. -/
def PsiT {T : Over (Spec (CommRingCat.of K))} (a : T ⟶ A.X) (c : (Nrm A).toFunctor.obj (op T)) :
    T ⟶ P :=
  rep.homEquiv.symm ((Θ A hU).hom.app (op T) ⟨dT A a c.1, dT_mem A a c.1 c.2⟩)

lemma PsiT_natural {T T' : Over (Spec (CommRingCat.of K))} (g : T' ⟶ T) (a : T ⟶ A.X)
    (c : (Nrm A).toFunctor.obj (op T)) :
    g ≫ PsiT rep hU a c = PsiT rep hU (g ≫ a) ((Nrm A).toFunctor.map g.op c) := by
  rw [PsiT, PsiT, rep.comp_homEquiv_symm]
  congr 1
  rw [← NatTrans.naturality_apply]
  congr 1
  apply Subtype.ext
  exact dT_natural A g a c.1

/-- `η ≫ (classifying map of 1)`: the class `1` classifies the unit. -/
lemma homEquiv_symm_one {T : Over (Spec (CommRingCat.of K))} :
    letI := picardFunctorCommGrpObj A.X.hom rep
    rep.homEquiv.symm ((toPicardFunctor A.X.hom).app (op T) (1 : (pullback A.X.hom T.hom).Pic)) =
      CartesianMonoidalCategory.toUnit T ≫ η[P] := by
  letI := picardFunctorCommGrpObj A.X.hom rep
  have h := (picardClassifyingHom A.X.hom rep T).map_one
  rw [picardClassifyingHom_apply] at h
  exact h

lemma dT_one {T : Over (Spec (CommRingCat.of K))} (a : T ⟶ A.X) : dT A a 1 = 1 := by
  simp [dT, Scheme.Pic.map_one]

lemma translT_zero {T : Over (Spec (CommRingCat.of K))} :
    translT A (CartesianMonoidalCategory.toUnit T ≫ η[A.X]) = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [translT, CartesianMonoidalCategory.lift_fst, Category.id_comp]
    rw [← Category.assoc, CartesianMonoidalCategory.toUnit_unique (CartesianMonoidalCategory.snd A.X T ≫
        CartesianMonoidalCategory.toUnit T) (CartesianMonoidalCategory.toUnit _),
      ← CategoryTheory.Hom.one_def, ← CategoryTheory.Hom.mul_def, mul_one]
  · simp [translT]

end Psi

end PicDict
