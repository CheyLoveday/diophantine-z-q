import ZInQKernel.Contrib.OneProof.KleimanPicZeroProperQuot
import ZInQKernel.Contrib.OneProof.PicLocFinType
import ZInQKernel.Contrib.OneProof.IdentityComponentLFT

open CategoryTheory AlgebraicGeometry Limits Opposite MonoidalCategory
open scoped CategoryTheory.MonObj

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace KleimanSection2

open Scheme T09Pic PkgI3 PkgI3.AbVar PicDict PicFix

universe u

/-- **Locally Noetherian `S`-schemes**, the test category of Kleiman's representability statements. -/
def LocNoeth (S : Scheme.{u}) : ObjectProperty (Over S) := fun T => IsLocallyNoetherian T.left

/-- The tree's Picard functor restricted to locally Noetherian test schemes. -/
def picardFunctorLN {X S : Scheme.{u}} (f : X ⟶ S) : (LocNoeth S).FullSubcategoryᵒᵖ ⥤ Type (u + 1) :=
  (LocNoeth S).ι.op ⋙ (picardFunctor f).obj

/-- An `S`-scheme locally of finite type over a locally Noetherian `S` is locally Noetherian. -/
lemma locNoeth_of_lft {S : Scheme.{u}} [IsLocallyNoetherian S] {P : Over S} (hP : LocallyOfFiniteType P.hom) :
    LocNoeth S P :=
  LocallyOfFiniteType.isLocallyNoetherian P.hom

/-- The final object `Spec K` as a locally Noetherian test scheme. -/
def unitLN (K : Type) [Field K] : (LocNoeth (Spec (CommRingCat.of K))).FullSubcategory :=
  ⟨𝟙_ (Over (Spec (CommRingCat.of K))),
    (inferInstance : IsLocallyNoetherian (Spec (CommRingCat.of K)))⟩

/-- The identity point of a scheme representing the restricted Picard functor: the point classifying the trivial
class (the class of `𝒪`). -/
def unitPt {K : Type} [Field K] {X : Over (Spec (CommRingCat.of K))} {P : Over (Spec (CommRingCat.of K))}
    {hP : LocNoeth _ P} (rep : (picardFunctorLN X.hom).RepresentableBy ⟨P, hP⟩) :
    𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P :=
  (rep.homEquiv (X := unitLN K)).symm
    ((toSheafify (fppfTopology.over _) (picardPresheaf X.hom)).app (op (𝟙_ _))
      (1 : (pullback X.hom (𝟙_ (Over (Spec (CommRingCat.of K)))).hom).Pic)) |>.hom

/-- The identity component of a representing scheme: the connected component of its identity point. -/
def identityComponentLN {K : Type} [Field K] {X : Over (Spec (CommRingCat.of K))}
    {P : Over (Spec (CommRingCat.of K))} {hP : LocNoeth _ P}
    (rep : (picardFunctorLN X.hom).RepresentableBy ⟨P, hP⟩) : Set P.left :=
  {x | ∃ s : (𝟙_ (Over (Spec (CommRingCat.of K)))).left, x ∈ connectedComponent ((unitPt rep).left s)}

/-- Restriction of a representation to locally Noetherian test schemes. -/
def repLN {X S : Scheme.{u}} {f : X ⟶ S} {P : Over S} (rep : (picardFunctor f).obj.RepresentableBy P)
    (hP : LocNoeth S P) : (picardFunctorLN f).RepresentableBy ⟨P, hP⟩ where
  homEquiv {T} := (InducedCategory.homEquiv).trans (rep.homEquiv (X := T.obj))
  homEquiv_comp g φ := rep.homEquiv_comp g.hom φ.hom

/-- The identity components agree. -/
lemma identityComponentLN_repLN {K : Type} [Field K] {X : Over (Spec (CommRingCat.of K))}
    {P : Over (Spec (CommRingCat.of K))} (rep : (picardFunctor X.hom).obj.RepresentableBy P)
    (hP : LocNoeth _ P) :
    identityComponentLN (repLN rep hP) =
      (letI := picardFunctorCommGrpObj X.hom rep; identityComponent P) := by
  rfl

/-- `IsProper ∧ immersion into ℙ^N over K` gives a closed immersion. -/
lemma isClosedImmersion_of_proper {K : Type} [Field K] {X : Scheme.{0}} {N : Type} [Finite N]
    (i : X ⟶ ℙ(N; Spec (CommRingCat.of K))) [IsImmersion i]
    [IsProper (i ≫ ℙ(N; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K))] : IsClosedImmersion i := by
  haveI : IsProper i := IsProper.of_comp i (ℙ(N; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K))
  refine .of_isPreimmersion _ ?_
  rw [← Set.image_univ]
  exact i.isClosedMap _ isClosed_univ

/-- **LEAF.** Kleiman 9.5.4. -/
def KleimanPicZeroProper954 : Prop :=
  ∀ (K : Type) [Field K] (X : Over (Spec (CommRingCat.of K))),
    (∃ (N : Type) (_ : Finite N) (i : X.left ⟶ ℙ(N; Spec (CommRingCat.of K))),
      IsClosedImmersion i ∧ i ≫ ℙ(N; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K) = X.hom) →
    GeometricallyIntegral X.hom → geometrically IsNormalScheme X.hom →
    (∃ σ : Spec (CommRingCat.of K) ⟶ X.left, σ ≫ X.hom = 𝟙 _) →
    ∀ (P : Over (Spec (CommRingCat.of K))) (hP : LocallyOfFiniteType P.hom)
      (rep : (picardFunctorLN X.hom).RepresentableBy ⟨P, locNoeth_of_lft hP⟩) (V : P.left.Opens),
      (V : Set P.left) = identityComponentLN rep → IsProper (V.ι ≫ P.hom)

theorem picZeroProperAt_of_954 (h : KleimanPicZeroProper954) (K : Type) [Field K] :
    PicZeroChar0.PicZeroProperAt K := by
  intro A P rep V hV
  obtain ⟨N, hN, i, hi, hover⟩ :=
    GrpObj.exists_isImmersion_projectiveSpace_of_smooth_of_geometricallyIntegral A.X
  have : IsProper (i ≫ ℙ(N; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K)) := by
    rw [hover]; infer_instance
  have hP := PicLFT.picLocFinType_proof K A P rep
  exact h K A.X ⟨N, hN, i, isClosedImmersion_of_proper i, hover⟩ inferInstance
    (geometricallyNormal_of_smooth A.X.hom) ⟨η[A.X].left, Over.w η[A.X]⟩ P hP (repLN rep _) V
    (by rw [identityComponentLN_repLN]; exact hV)

theorem picZeroAbVar0_of_954 (h : KleimanPicZeroProper954) : PicZeroChar0.PicZeroAbVar0 := fun K _ _ =>
  PicZeroChar0.picZeroAbVarAt_of PicLFT.picLocFinType_proof IdCompLFT.identityComponentLFT_proof K
    (PicZeroChar0.picZeroSmoothAt_charZero ZInQ.Contrib.OneProof.CartierSmooth.cartierSmooth_proof
      PicLFT.picLocFinType_proof K)
    (picZeroProperAt_of_954 h K)

end KleimanSection2

end

#print axioms KleimanSection2.picZeroAbVar0_of_954
