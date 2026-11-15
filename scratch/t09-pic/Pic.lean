import ZInQKernel.OneProof.H.TailB
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Picard.RepresentableGroup
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Picard.Field
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Group.QuasiProjective
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpace.Twist
import ZInQKernel.Contrib.FrobChain.Rigidity

/-!
# t09-pic: `t09SymmIsogenyExists` over the genuine Picard functor

Task t09-pic (2026-11-14). Field `t09SymmIsogenyExists : HDec.WeilPairing.T09_SymmIsogenyExists`.

Genuine objects used (none invented for the purpose):
* `PkgI3.AbVar` (`ZInQKernel/HDecomp/Objects.lean`);
* the relative Picard fppf sheaf `picardFunctor` and its group law `picardFunctorCommGrpObj`
  (vendored Jacobian-Challenge, `ZInQKernel/Contrib/CloudW07JacobiansCurves/.../Picard/`);
* `Scheme.Pic` (classes of invertible sheaves), `Scheme.Pic.map` (pull-back);
* the twisting sheaf `𝒪(1)` on `ℙ(ι; S)` (`ProjectiveSpace.twist`, vendored);
* Mathlib's `connectedComponent`, `IsOpenImmersion`, `IsImmersion`.

New definitions here: the Mumford bundle `Λ(L)`, `φ_L : A → Pic_{A/K}` (Yoneda), the identity
component of a group scheme over `K`, very ample classes, "`(B, ι)` is `Pic⁰`".
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory Opposite
open scoped CategoryTheory.MonObj

namespace T09Pic

open PkgI3 PkgI3.AbVar

/-! ## §0. The field, verbatim -/

section Verbatim

open HDec.WeilPairing

/-- Copied verbatim from `scratch/weil-pairing/WeilPairing.lean` (`HDec.WeilPairing` in
`ZInQKernel/OneProof/H/TailB.lean`). -/
def T09_SymmIsogenyExists : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K), Nonempty (SymmIsogeny A)

example : T09_SymmIsogenyExists = HDec.WeilPairing.T09_SymmIsogenyExists := rfl

end Verbatim

variable {K : Type} [Field K]

/-! ## §1. Genuine definitions -/

/-- **The Mumford bundle** `Λ(L) = m^*L ⊗ p₁^*L⁻¹ ⊗ p₂^*L⁻¹` on `A ×_K A` (Mumford, *Abelian
varieties*, §8, (iv); UNVERIFIED numbering). -/
def mumfordBundle (A : AbVar K) (L : A.X.left.Pic) : (pullback A.X.hom A.X.hom).Pic :=
  (show (pullback A.X.hom A.X.hom).Pic from Scheme.Pic.map (μ[A.X]).left L) * (Scheme.Pic.map (pullback.fst A.X.hom A.X.hom) L)⁻¹ *
    (Scheme.Pic.map (pullback.snd A.X.hom A.X.hom) L)⁻¹

/-- **`φ_L : A → Pic_{A/K}`**: the morphism classifying the family `Λ(L)` on `A ×_K A` over the
second factor, through a representation of the Picard functor (Yoneda). On points,
`φ_L(x) = [t_x^*L ⊗ L⁻¹]` (Mumford §8). -/
def phiL {A : AbVar K} {P : Over (Spec (CommRingCat.of K))}
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (L : A.X.left.Pic) : A.X ⟶ P :=
  rep.homEquiv.symm ((toPicardFunctor A.X.hom).app (op A.X) (mumfordBundle A L))

/-- **The identity component** of a group scheme `G` over `K`: the connected component of the
identity point (the image of the unit section `Spec K → G`). -/
def identityComponent (G : Over (Spec (CommRingCat.of K))) [GrpObj G] : Set G.left :=
  {x | ∃ s : (𝟙_ (Over (Spec (CommRingCat.of K)))).left, x ∈ connectedComponent (η[G].left s)}

/-- **`(B, ι)` is the identity component `Pic⁰` of the Picard scheme `P`** (`P` represents the Picard
functor of `A` through `rep`, with its group law `picardFunctorCommGrpObj`): `ι : B → P` is an open
immersion onto the identity component and a homomorphism. This pins `(B, ι)` down up to unique
isomorphism. -/
def IsPicZero {A : AbVar K} {P : Over (Spec (CommRingCat.of K))}
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (B : AbVar K) (j : B.X ⟶ P) : Prop :=
  letI := picardFunctorCommGrpObj A.X.hom rep
  IsOpenImmersion j.left ∧ Set.range j.left = identityComponent P ∧ IsMonHom j

/-- **Very ample** (relative to `K`, finitely many coordinates): `L ≅ i^*𝒪(1)` for an immersion
`i : A → ℙ^N_K` over `K` (EGA II 4.4.2, Hartshorne II §7; UNVERIFIED numbering). Very ample implies
ample (Hartshorne II Thm 7.6; UNVERIFIED). -/
def IsVeryAmple (A : AbVar K) (L : A.X.left.Pic) : Prop :=
  ∃ (N : Type) (_ : Finite N) (i : A.X.left ⟶ ℙ(N; Spec (CommRingCat.of K))),
    IsImmersion i ∧ i ≫ ℙ(N; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K) = A.X.hom ∧
    L = Scheme.Pic.map i (Scheme.Pic.mk (ProjectiveSpace.twist N (Spec (CommRingCat.of K)) 1))

/-! ## §2. Glue (proved) -/

/-- **Every abelian variety over `K` has a very ample class** (proved from the vendored
`GrpObj.exists_isImmersion_projectiveSpace_of_smooth_of_geometricallyIntegral`). -/
theorem exists_isVeryAmple (A : AbVar K) : ∃ L, IsVeryAmple A L := by
  obtain ⟨N, hN, i, hi, hover⟩ :=
    GrpObj.exists_isImmersion_projectiveSpace_of_smooth_of_geometricallyIntegral A.X
  exact ⟨_, N, hN, i, hi, hover, rfl⟩


/-- Precomposition with `f : T' ⟶ T` classifies the pulled-back class (Yoneda + naturality of the
sheafification map). -/
lemma comp_classify {A : AbVar K} {P : Over (Spec (CommRingCat.of K))}
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) {T T' : Over (Spec (CommRingCat.of K))}
    (f : T' ⟶ T) (c : (pullback A.X.hom T.hom).Pic) :
    f ≫ rep.homEquiv.symm ((toPicardFunctor A.X.hom).app (op T) c) =
      rep.homEquiv.symm ((toPicardFunctor A.X.hom).app (op T')
        (Scheme.Pic.map (JacobianChallenge.baseChangeMap A.X.hom f) c)) := by
  rw [rep.comp_homEquiv_symm]
  congr 1
  exact ((toPicardFunctor A.X.hom).naturality_apply f.op c).symm

/-- `Λ(L)` restricted to `A × {0}` is trivial. -/
lemma mumfordBundle_restrict_zero (A : AbVar K) (L : A.X.left.Pic) :
    Scheme.Pic.map (JacobianChallenge.baseChangeMap A.X.hom η[A.X]) (mumfordBundle A L) = 1 := by
  have h1 : JacobianChallenge.baseChangeMap A.X.hom η[A.X] = (A.X ◁ η[A.X]).left := by
    apply pullback.hom_ext <;> simp [JacobianChallenge.baseChangeMap]
  have hμ : JacobianChallenge.baseChangeMap A.X.hom η[A.X] ≫ (μ[A.X]).left =
      JacobianChallenge.baseChangeMap A.X.hom η[A.X] ≫ pullback.fst A.X.hom A.X.hom := by
    rw [h1, ← Over.comp_left, MonObj.mul_one]
    simp
  have hsnd : JacobianChallenge.baseChangeMap A.X.hom η[A.X] ≫ pullback.snd A.X.hom A.X.hom =
      pullback.snd _ _ ≫ η[A.X].left := pullback.lift_snd _ _ _
  have hS : Scheme.Pic.map η[A.X].left L = 1 :=
    Subsingleton.elim (α := (Spec (CommRingCat.of K)).Pic) _ _
  rw [mumfordBundle, ← Scheme.Pic.mapHom_apply]
  simp only [map_mul, map_inv, Scheme.Pic.mapHom_apply, ← Scheme.Pic.map_comp, hμ, hsnd]
  rw [Scheme.Pic.map_comp (pullback.snd _ _) η[A.X].left, hS, Scheme.Pic.map_one]
  simp

/-- **`φ_L(0) = 0`**: `η_A ≫ φ_L = η_P` for the group law of the Picard scheme. -/
lemma eta_comp_phiL {A : AbVar K} {P : Over (Spec (CommRingCat.of K))}
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (L : A.X.left.Pic) :
    letI := picardFunctorCommGrpObj A.X.hom rep
    η[A.X] ≫ phiL rep L = η[P] := by
  letI := picardFunctorCommGrpObj A.X.hom rep
  rw [phiL, comp_classify, mumfordBundle_restrict_zero]
  have h := (picardClassifyingHom A.X.hom rep (𝟙_ _)).map_one
  rw [picardClassifyingHom_apply] at h
  rw [h, show (1 : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P) = CartesianMonoidalCategory.toUnit _ ≫ η from rfl]
  simp

end T09Pic
