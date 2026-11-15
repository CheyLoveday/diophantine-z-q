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


/-- **`φ_L` factors through `Pic⁰` by a homomorphism** `λ_L : A → B`: `A` is connected and
`φ_L(0) = 0` (so the image lies in the identity component), `ι` is an open immersion onto it, and
the lift preserves `0`, hence is a homomorphism by rigidity
(`MulRigidity.isMonHom_of_geometricallyIntegral`, Mumford §4 Cor. 1). -/
theorem exists_hom_comp_eq_phiL {A : AbVar K} {P : Over (Spec (CommRingCat.of K))}
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) {B : AbVar K} {j : B.X ⟶ P}
    (hj : IsPicZero rep B j) (L : A.X.left.Pic) :
    ∃ lam : Hom A B, lam.hom ≫ j = phiL rep L := by
  letI := picardFunctorCommGrpObj A.X.hom rep
  obtain ⟨hopen, hrange, hmon⟩ := hj
  have h0 := eta_comp_phiL rep L
  haveI : IsIntegral A.X.left := GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
  have hsub : Set.range (phiL rep L).left ⊆ Set.range j.left := by
    rw [hrange]
    rintro _ ⟨a, rfl⟩
    refine ⟨A.X.hom a, ?_⟩
    have he : η[P].left (A.X.hom a) = (phiL rep L).left (η[A.X].left (A.X.hom a)) := by
      rw [← h0]; rfl
    rw [he]
    exact (isPreconnected_range (phiL rep L).left.continuous).subset_connectedComponent
      ⟨_, rfl⟩ ⟨a, rfl⟩
  let l : A.X.left ⟶ B.X.left := IsOpenImmersion.lift j.left (phiL rep L).left hsub
  have hl : l ≫ j.left = (phiL rep L).left := IsOpenImmersion.lift_fac _ _ _
  have hw : l ≫ B.X.hom = A.X.hom := by
    rw [← Over.w j, ← Category.assoc, hl, Over.w]
  let lam : A.X ⟶ B.X := Over.homMk l hw
  have hlam : lam ≫ j = phiL rep L := Over.OverMorphism.ext hl
  have hη : η[A.X] ≫ lam = η[B.X] := by
    apply Over.OverMorphism.ext
    apply (cancel_mono j.left).1
    rw [Over.comp_left, Category.assoc]
    change η[A.X].left ≫ lam.left ≫ j.left = η[B.X].left ≫ j.left
    rw [← Over.comp_left, hlam, ← Over.comp_left, h0, ← Over.comp_left _ _ _ η[B.X] j, IsMonHom.one_hom]
  have : IsMonHom lam := MulRigidity.isMonHom_of_geometricallyIntegral A.X B.X lam hη
  exact ⟨Hom.mk' lam, hlam⟩


/-! ## §2b. The dual morphism `f^∨` on the Picard scheme and on `Pic⁰` (genuine, proved) -/

/-- `f × id_T : A ×_K T → A' ×_K T`. -/
abbrev famMap {A A' : AbVar K} (f : A.X ⟶ A'.X) (T : Over (Spec (CommRingCat.of K))) :
    pullback A.X.hom T.hom ⟶ pullback A'.X.hom T.hom :=
  pullback.map _ _ _ _ f.left (𝟙 _) (𝟙 _) (by simp) (by simp)

/-- Pull-back of families along `f × id`: `Pic(A'_T) → Pic(A_T)`, natural in `T`. -/
def picPresheafMap {A A' : AbVar K} (f : A.X ⟶ A'.X) :
    picardPresheaf A'.X.hom ⟶ picardPresheaf A.X.hom where
  app T := TypeCat.ofHom (Scheme.Pic.map (famMap f T.unop))
  naturality T T' φ := by
    ext c
    change Scheme.Pic.map (famMap f T'.unop)
        (Scheme.Pic.map (JacobianChallenge.baseChangeMap A'.X.hom φ.unop) c) =
      Scheme.Pic.map (JacobianChallenge.baseChangeMap A.X.hom φ.unop)
        (Scheme.Pic.map (famMap f T.unop) c)
    have e : famMap f T'.unop ≫ JacobianChallenge.baseChangeMap A'.X.hom φ.unop =
        JacobianChallenge.baseChangeMap A.X.hom φ.unop ≫ famMap f T.unop := by
      apply pullback.hom_ext <;> simp [JacobianChallenge.baseChangeMap]
    exact (Scheme.Pic.map_comp _ _ (show (pullback A'.X.hom T.unop.hom).Pic from c)).symm.trans
      ((congrArg (fun g => Scheme.Pic.map g (show (pullback A'.X.hom T.unop.hom).Pic from c)) e).trans
        (Scheme.Pic.map_comp _ _ _))

/-- The sheafified pull-back `f^* : Pic_{A/K} → Pic_{A/K}`. -/
def dualSheafMap {A : AbVar K} (f : A.X ⟶ A.X) :
    (picardFunctor A.X.hom).obj ⟶ (picardFunctor A.X.hom).obj :=
  sheafifyMap (Scheme.fppfTopology.over (Spec (CommRingCat.of K))) (picPresheafMap f)

lemma toPicardFunctor_comp_dualSheafMap {A : AbVar K} (f : A.X ⟶ A.X) :
    toPicardFunctor A.X.hom ≫ dualSheafMap f = picPresheafMap f ≫ toPicardFunctor A.X.hom :=
  (toSheafify_naturality (Scheme.fppfTopology.over (Spec (CommRingCat.of K))) (picPresheafMap f)).symm

/-- **The dual morphism on the Picard scheme**, `f^∨ : P → P` for `f : A → A` (Yoneda applied to
`f^* : Pic_{A/K} → Pic_{A/K}`, the sheafified pull-back of families; Mumford §8). -/
def dualP {A : AbVar K} {P : Over (Spec (CommRingCat.of K))}
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (f : A.X ⟶ A.X) : P ⟶ P :=
  rep.homEquiv.symm ((dualSheafMap f).app (op P) (rep.homEquiv (𝟙 P)))

lemma comp_dualP {A : AbVar K} {P : Over (Spec (CommRingCat.of K))}
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (f : A.X ⟶ A.X)
    {T : Over (Spec (CommRingCat.of K))} (g : T ⟶ P) :
    g ≫ dualP rep f = rep.homEquiv.symm ((dualSheafMap f).app (op T) (rep.homEquiv g)) := by
  rw [dualP, rep.comp_homEquiv_symm]
  congr 1
  rw [← NatTrans.naturality_apply, ← rep.homEquiv_comp, Category.comp_id]

/-- `f^∨(0) = 0`. -/
lemma eta_comp_dualP {A : AbVar K} {P : Over (Spec (CommRingCat.of K))}
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (f : A.X ⟶ A.X) :
    letI := picardFunctorCommGrpObj A.X.hom rep
    η[P] ≫ dualP rep f = η[P] := by
  letI := picardFunctorCommGrpObj A.X.hom rep
  have h := (picardClassifyingHom A.X.hom rep (𝟙_ _)).map_one
  rw [picardClassifyingHom_apply,
    show (1 : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P) = CartesianMonoidalCategory.toUnit _ ≫ η
      from rfl] at h
  simp only [CartesianMonoidalCategory.toUnit_unique (CartesianMonoidalCategory.toUnit _) (𝟙 _),
    Category.id_comp] at h
  rw [comp_dualP, ← h, Equiv.apply_symm_apply]
  congr 1
  have := congrArg (fun τ => τ.app (op (𝟙_ (Over (Spec (CommRingCat.of K)))))
    (1 : (pullback A.X.hom (𝟙_ (Over (Spec (CommRingCat.of K)))).hom).Pic))
    (toPicardFunctor_comp_dualSheafMap f)
  simp only [NatTrans.comp_app] at this
  exact this.trans (congrArg _ (Scheme.Pic.map_one _))

/-- **The dual endomorphism on `Pic⁰`**: `f^∨` restricts to `B = Pic⁰` (B is connected and
`f^∨(0) = 0`), as a homomorphism (rigidity). -/
theorem exists_dual_on_picZero {A : AbVar K} {P : Over (Spec (CommRingCat.of K))}
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) {B : AbVar K} {j : B.X ⟶ P}
    (hj : IsPicZero rep B j) (f : A.X ⟶ A.X) :
    ∃ fv : End B, fv.hom ≫ j = j ≫ dualP rep f := by
  letI := picardFunctorCommGrpObj A.X.hom rep
  obtain ⟨hopen, hrange, hmon⟩ := hj
  have h0 := eta_comp_dualP rep f
  haveI : IsIntegral B.X.left := GeometricallyIntegral.isIntegral_of_subsingleton B.X.hom
  have hjη : η[B.X] ≫ j = η[P] := IsMonHom.one_hom j
  have h2 : η[B.X] ≫ j ≫ dualP rep f = η[P] := by rw [← Category.assoc, hjη, h0]
  have hsub : Set.range (j ≫ dualP rep f).left ⊆ Set.range j.left := by
    rw [hrange]
    rintro _ ⟨b, rfl⟩
    refine ⟨B.X.hom b, ?_⟩
    have he : η[P].left (B.X.hom b) = (j ≫ dualP rep f).left (η[B.X].left (B.X.hom b)) := by
      rw [← h2]; rfl
    rw [he]
    exact (isPreconnected_range (j ≫ dualP rep f).left.continuous).subset_connectedComponent
      ⟨_, rfl⟩ ⟨b, rfl⟩
  let l : B.X.left ⟶ B.X.left := IsOpenImmersion.lift j.left (j ≫ dualP rep f).left hsub
  have hl : l ≫ j.left = (j ≫ dualP rep f).left := IsOpenImmersion.lift_fac _ _ _
  have hw : l ≫ B.X.hom = B.X.hom :=
    calc l ≫ B.X.hom = l ≫ j.left ≫ P.hom := by rw [Over.w j]
      _ = (j ≫ dualP rep f).left ≫ P.hom := by rw [← Category.assoc, hl]
      _ = B.X.hom := Over.w _
  let fv : B.X ⟶ B.X := Over.homMk l hw
  have hfv : fv ≫ j = j ≫ dualP rep f := Over.OverMorphism.ext hl
  have hη : η[B.X] ≫ fv = η[B.X] := by
    apply Over.OverMorphism.ext
    apply (cancel_mono j.left).1
    rw [Over.comp_left, Category.assoc]
    change η[B.X].left ≫ fv.left ≫ j.left = η[B.X].left ≫ j.left
    rw [← Over.comp_left, hfv, ← Over.comp_left, ← Category.assoc, hjη, h0,
      ← Over.comp_left _ _ _ η[B.X] j, hjη]
  have : IsMonHom fv := MulRigidity.isMonHom_of_geometricallyIntegral B.X B.X fv hη
  exact ⟨Hom.mk' fv, hfv⟩

/-! ## §3. Leaves (printed statements over the genuine objects of §1) -/

section Leaves

open HDec.WeilPairing

/-- **LEAF L1 (representability of the Picard functor).** For an abelian variety `A` over a field `K`
the relative Picard fppf sheaf `Pic_{A/K}` is representable. Published: Murre (1964) and Oort (1962)
for `X` proper over a field; Grothendieck, FGA Exp. 232, Thm 3.1, and Kleiman, *The Picard scheme*
(FGA Explained, 2005), Thm 9.4.8 (with Thm 9.2.5: the étale and fppf sheaves agree since
`𝒪_K = f_*𝒪_A` universally), for `X` projective with geometrically integral fibres — abelian
varieties are projective (Mumford §6, Application 1; cf. the vendored
`GrpObj.exists_isImmersion_projectiveSpace_of_smooth_of_geometricallyIntegral`). UNVERIFIED
numbering. Statement copied from `scratch/c-to-printed2/T09Roadmap.lean`. -/
def PicRepresentableAbVar : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K),
    ∃ P : Over (Spec (CommRingCat.of K)), Nonempty ((picardFunctor A.X.hom).obj.RepresentableBy P)

/-- **LEAF L2 (`Pic⁰_{A/K}` is an abelian variety).** The identity component of the Picard scheme
of an abelian variety is open, and with the induced group law it is an abelian variety (the dual
abelian variety `Â`). Published: Mumford, *Abelian varieties*, §13 (`Â = Pic⁰` is an abelian
variety of dimension `g`, reduced: §13 Cor. 3 / Thm 1) over `K̄`; Kleiman, *The Picard scheme*,
Prop. 9.5.3 (`Pic⁰` open and closed, of finite type) and Prop. 9.5.1 (compatible with field
extension), so smoothness, properness and geometric integrality descend to `K`; Milne, *Abelian
varieties* (1986), §9-10. UNVERIFIED numbering. Stated over every representation `rep`; it is
invariant under the unique isomorphism of representing objects. -/
def PicZeroAbVar : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P),
    ∃ (B : AbVar K) (j : B.X ⟶ P), IsPicZero rep B j

/-- **LEAF L3 (`φ_L` is an isogeny for ample `L`).** If `L` is (very) ample, `λ_L : A → Pic⁰`
(the map with `λ_L ≫ ι = φ_L`) is finite and surjective. Published: Mumford §6, Application 1
(`L` ample `⇒ K(L) = ker φ_L` finite) and §8, Thm 1 (`φ_L` surjective onto `Â`, `Â ≅ A/K(L)`);
very ample `⇒` ample (Hartshorne II, Thm 7.6 / EGA II 4.5.10); over a non-closed `K`, finiteness and
surjectivity descend from `K̄` (fpqc descent, EGA IV 2.6.4 / 2.7.1). UNVERIFIED numbering. Quantified
over every `(B, ι)` with `IsPicZero` (unique up to unique isomorphism) and every lift `λ`. -/
def PhiVeryAmpleIsogeny : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (B : AbVar K) (j : B.X ⟶ P),
    IsPicZero rep B j → ∀ L : A.X.left.Pic, IsVeryAmple A L →
      ∀ lam : A.X ⟶ B.X, lam ≫ j = phiL rep L → IsIsogenyMor lam

/-- **LEAF L4 (Mumford's Weil pairing `ē_n : A[n] × Â[n] → μ_n` at `Â = Pic⁰`).** There are pairings
`e_n : A[n] × Pic⁰[n] → μ_n` (on `K̄`-points) which, for `n ≥ 1` invertible in `K`, are perfect,
`G_K`-equivariant (`e_n` is defined over `K`), compatible (`e_{mn}(x, y) = e_n(m x, y)` for
`y ∈ Â[n]`), under which every endomorphism `f` of `A` has an adjoint on `Pic⁰` (its dual `f^∨`:
`e_n(x, f^∨ y) = e_n(f x, y)`), and with `e_n(x, φ_L(x)) = 1` for very ample `L`. Published:
Mumford §20 (definition of `ē_n` and its properties: bilinear, perfect, `e_{nm}(x, y) = e_n(mx, y)`,
`e_n(x, f^∨ y) = e_n(f x, y)`) and §23 (`e^L_n(x, y) := ē_n(x, φ_L(y))` is skew-symmetric with
`e^L_n(x, x) = 1`); Galois equivariance: Milne, *Abelian varieties* (1986), §16 (`e_n` is defined
over `K`). UNVERIFIED numbering. The pairing is existential (Mumford's `ē_n` witnesses it), so this is
a consequence of the printed statements, never stronger. -/
def WeilPairingPicZero : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (B : AbVar K) (j : B.X ⟶ P),
    IsPicZero rep B j →
    ∃ e : ∀ n : ℕ, Pairing A B n,
      (∀ n : ℕ, 0 < n → (n : K) ≠ 0 → IsPerfect (e n)) ∧
      (∀ n : ℕ, 0 < n → (n : K) ≠ 0 → HDec.WeilPairing.IsGalEquivariant (e n)) ∧
      (∀ m n : ℕ, 0 < m → 0 < n → ((m * n : ℕ) : K) ≠ 0 →
        ∀ (x : tors A (m * n)) (y : tors B n),
          (e (m * n) x (torsIncl B (dvd_mul_left n m) y)).val = (e n (torsSmul A m n x) y).val) ∧
      (∀ f : End A, ∃ fv : End B, ∀ n : ℕ, 0 < n → (n : K) ≠ 0 →
        ∀ x y, e n x (torsMap fv n y) = e n (torsMap f n x) y) ∧
      (∀ L : A.X.left.Pic, IsVeryAmple A L → ∀ lam : Hom A B, lam.hom ≫ j = phiL rep L →
        ∀ n : ℕ, 0 < n → (n : K) ≠ 0 → ∀ x : tors A n, e n x (torsMap lam n x) = 0)

/-- **Ample** (Stacks, *Properties of schemes*, Def. 28.26.1, Tag 01PS; EGA II 4.5.3; UNVERIFIED
numbering): `X` is quasi-compact and every point lies in an affine `X_s = {s ≠ 0}` for some global
section `s` of some `L^{⊗n}`, `n ≥ 1` (`X_s` = complement of the support of the zero locus of `s`,
vendored `Scheme.Modules.Hom.zeroLocus`). -/
def IsAmple (X : Scheme.{0}) (L : X.Pic) : Prop :=
  CompactSpace X ∧ ∀ x : X, ∃ (n : ℕ) (_ : 0 < n)
    (s : 𝟙_ X.Modules ⟶ ((fromSkeleton X.Modules).obj L.val).tensorPow n),
    x ∈ (Scheme.Modules.Hom.zeroLocus s).support.compl ∧
      IsAffineOpen (Scheme.Modules.Hom.zeroLocus s).support.compl

/-- **LEAF L0 (very ample ⇒ ample).** Hartshorne, *Algebraic Geometry*, II Thm 7.6 (with II §5 for
`X` proper over a field); EGA II 4.5.10; Stacks Tag 01VM-01VS (UNVERIFIED numbering). -/
def VeryAmpleIsAmple : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : A.X.left.Pic), IsVeryAmple A L → IsAmple A.X.left L

/-- **LEAF L3, printed form (`φ_L` is an isogeny for ample `L`).** As `PhiVeryAmpleIsogeny`, for every
ample `L` (Mumford §6 Application 1 and §8 Thm 1; UNVERIFIED numbering). -/
def PhiAmpleIsogeny : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (B : AbVar K) (j : B.X ⟶ P),
    IsPicZero rep B j → ∀ L : A.X.left.Pic, IsAmple A.X.left L →
      ∀ lam : A.X ⟶ B.X, lam ≫ j = phiL rep L → IsIsogenyMor lam

/-- **LEAF L4, printed form.** As `WeilPairingPicZero`, with the *genuine* dual `f^∨` (any lift
`fv : Pic⁰ → Pic⁰` of `dualP rep f`; it exists by `exists_dual_on_picZero` and is unique since `ι` is
a monomorphism) in `ē_n(x, f^∨ y) = ē_n(f x, y)` (Mumford §20, (5)), and `ē_n(x, φ_L(x)) = 1` for
every ample `L` (Mumford §23). UNVERIFIED numbering. -/
def WeilPairingPicZeroPrinted : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (B : AbVar K) (j : B.X ⟶ P),
    IsPicZero rep B j →
    ∃ e : ∀ n : ℕ, Pairing A B n,
      (∀ n : ℕ, 0 < n → (n : K) ≠ 0 → IsPerfect (e n)) ∧
      (∀ n : ℕ, 0 < n → (n : K) ≠ 0 → HDec.WeilPairing.IsGalEquivariant (e n)) ∧
      (∀ m n : ℕ, 0 < m → 0 < n → ((m * n : ℕ) : K) ≠ 0 →
        ∀ (x : tors A (m * n)) (y : tors B n),
          (e (m * n) x (torsIncl B (dvd_mul_left n m) y)).val = (e n (torsSmul A m n x) y).val) ∧
      (∀ (f : End A) (fv : End B), fv.hom ≫ j = j ≫ dualP rep f.hom → ∀ n : ℕ, 0 < n →
        (n : K) ≠ 0 → ∀ x y, e n x (torsMap fv n y) = e n (torsMap f n x) y) ∧
      (∀ L : A.X.left.Pic, IsAmple A.X.left L → ∀ lam : Hom A B, lam.hom ≫ j = phiL rep L →
        ∀ n : ℕ, 0 < n → (n : K) ≠ 0 → ∀ x : tors A n, e n x (torsMap lam n x) = 0)

end Leaves

/-- Glue: the printed L3 and L0 give L3 for very ample classes. -/
theorem phiVeryAmpleIsogeny_of_printed (h0 : VeryAmpleIsAmple) (h3 : PhiAmpleIsogeny) :
    PhiVeryAmpleIsogeny := fun K _ A P rep B j hj L hL lam hlam =>
  h3 K A P rep B j hj L (h0 K A L hL) lam hlam

/-- Glue: the printed L4 (genuine `f^∨`, ample `L`) and L0 give L4. -/
theorem weilPairingPicZero_of_printed (h0 : VeryAmpleIsAmple) (h4 : WeilPairingPicZeroPrinted) :
    WeilPairingPicZero := by
  intro K _ A P rep B j hj
  obtain ⟨e, hperf, hgal, hcompat, hdual, halt⟩ := h4 K A P rep B j hj
  refine ⟨e, hperf, hgal, hcompat, fun f => ?_, fun L hL => halt L (h0 K A L hL)⟩
  obtain ⟨fv, hfv⟩ := exists_dual_on_picZero rep hj f.hom
  exact ⟨fv, hdual f fv hfv⟩

/-! ## §4. `t09SymmIsogenyExists` from the four leaves -/

/-- **Main result.** The field `t09SymmIsogenyExists` follows from the four printed leaves L1-L4 over
the genuine Picard functor; the glue (existence of a very ample class, `φ_L(0) = 0`, `φ_L` lands in
`Pic⁰`, the lift is a homomorphism) is proved above. -/
theorem t09SymmIsogenyExists_of_leaves (h1 : PicRepresentableAbVar) (h2 : PicZeroAbVar)
    (h3 : PhiVeryAmpleIsogeny) (h4 : WeilPairingPicZero) :
    HDec.WeilPairing.T09_SymmIsogenyExists := by
  intro K _ A
  obtain ⟨P, ⟨rep⟩⟩ := h1 K A
  obtain ⟨B, j, hj⟩ := h2 K A P rep
  obtain ⟨L, hL⟩ := exists_isVeryAmple A
  obtain ⟨lam, hlam⟩ := exists_hom_comp_eq_phiL rep hj L
  obtain ⟨e, hperf, hgal, hcompat, hdual, halt⟩ := h4 K A P rep B j hj
  exact ⟨{ D := { dual := B, e := e, perfect := hperf, galois := hgal, compat := hcompat,
                  dualEnd := hdual }
           lam := lam
           isogeny := h3 K A P rep B j hj L hL lam.hom hlam
           symm := fun n hn hnK x => by
             rw [HDec.WeilPairing.weil_apply]
             exact halt L hL lam hlam n hn hnK x }⟩

/-! ## §5. Non-vacuity of `IsAmple` -/

/-- Over an algebraically closed field every abelian variety has an ample class in the sense of
`IsAmple` (from the vendored `GrpObj.hasAmpleFamily_of_smooth_of_irreducibleSpace`, `n = 1`). A check
that `IsAmple` is not inert, so `VeryAmpleIsAmple` is not refuted by the definition. -/
theorem exists_isAmple_of_isAlgClosed [IsAlgClosed K] (A : AbVar K) : ∃ L, IsAmple A.X.left L := by
  haveI : IsIntegral A.X.left := GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
  obtain ⟨M, hM, I, hI, s, haff, hcov⟩ :=
    GrpObj.hasAmpleFamily_of_smooth_of_irreducibleSpace (baseField := K) A.X
  letI := hM
  haveI : CompactSpace A.X.left := QuasiCompact.compactSpace_of_compactSpace A.X.hom
  let N := (fromSkeleton A.X.left.Modules).obj (Scheme.Pic.mk M).val
  let e : M ≅ N.tensorPow 1 := (Scheme.Pic.mkIso M).symm ≪≫ (ρ_ N).symm
  refine ⟨Scheme.Pic.mk M, inferInstance, fun x => ?_⟩
  have hx : x ∈ ⨆ i, (Scheme.Modules.Hom.zeroLocus (s i)).support.compl := by
    rw [hcov]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  have hz : Scheme.Modules.Hom.zeroLocus (s i ≫ e.hom) = Scheme.Modules.Hom.zeroLocus (s i) :=
    Scheme.Modules.Hom.zeroLocus_eq_of_arrowIso (s i ≫ e.hom) (s i)
      (Arrow.isoMk (Iso.refl _) e.symm (by simp))
  exact ⟨1, one_pos, s i ≫ e.hom, by rw [hz]; exact hi, by rw [hz]; exact haff i⟩

/-! ## §6. Mumford's `ē_n` as a genuine definition, and the leaf in fully genuine form -/

/-- `Spec K̄` as a `K`-scheme. -/
abbrev ptK (K : Type) [Field K] : Over (Spec (CommRingCat.of K)) :=
  ptObj (K := K) (AlgebraicClosure K)

/-- **Translation by `x ∈ A(K̄)` on `A_K̄`**, as a `K`-morphism `A ×_K K̄ → A ×_K K̄`,
`(a, s) ↦ (a + x(s), s)` (`t_x`, Mumford §2). -/
def transl {A : AbVar K} (x : A.Pt (AlgebraicClosure K)) : A.X ⊗ ptK K ⟶ A.X ⊗ ptK K :=
  CartesianMonoidalCategory.lift
    (CartesianMonoidalCategory.lift (CartesianMonoidalCategory.fst _ _)
      (CartesianMonoidalCategory.snd _ _ ≫ x) ≫ μ[A.X])
    (CartesianMonoidalCategory.snd _ _)

/-- **Multiplication by `n` on `A_K̄`** (`n_A = id^n` in the group of `K`-endomorphisms of the
scheme, base-changed to `K̄`). -/
def mulN (A : AbVar K) (n : ℕ) : A.X ⊗ ptK K ⟶ A.X ⊗ ptK K :=
  ((𝟙 A.X) ^ n) ▷ ptK K

/-- **The class `M_y ∈ Pic(A_K̄)` of a point `y ∈ Pic⁰(K̄)`**: a class whose image in
`Pic_{A/K}(K̄)` is the point `y ≫ ι` (exists by Kleiman Thm 9.2.5, `A` having a section; unique since
`Pic(K̄) = 1`). Defined by choice (`1` if no such class existed). -/
def picClass {A : AbVar K} {P : Over (Spec (CommRingCat.of K))}
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) {B : AbVar K} (j : B.X ⟶ P)
    (y : B.Pt (AlgebraicClosure K)) : (pullback A.X.hom (ptK K).hom).Pic := by
  classical
  exact if h : ∃ c, (toPicardFunctor A.X.hom).app (op (ptK K)) c = rep.homEquiv (y ≫ j)
    then h.choose else 1

/-- **Mumford's `ē_n(x, y)`, genuine** (Mumford §20 via the descent description of §§12, 15;
UNVERIFIED numbering): for `y ∈ Pic⁰[n](K̄)` with class `M`, choose `ψ : 𝒪 ≅ n_A^*M` (exists: Mumford
§8 (iv)); for `x ∈ A[n](K̄)`, `n_A ∘ t_x = n_A`, so `t_x^*ψ` is a second trivialization and
`t_x^*ψ ∘ ψ⁻¹ ∈ Aut(𝒪_{A_K̄}) = Γ(A_K̄, 𝒪)^× = K̄^×` is the value (independent of the choices). Defined
by choice; `1` if a condition fails (it never does for `x ∈ A[n]`, `y ∈ Pic⁰[n]`). -/
def weilScalar {A : AbVar K} {P : Over (Spec (CommRingCat.of K))}
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) {B : AbVar K} (j : B.X ⟶ P) (n : ℕ)
    (x : A.Pt (AlgebraicClosure K)) (y : B.Pt (AlgebraicClosure K)) :
    Γ(pullback A.X.hom (ptK K).hom, ⊤) := by
  classical
  let X := pullback A.X.hom (ptK K).hom
  let t : X ⟶ X := (transl x).left
  let m : X ⟶ X := (mulN A n).left
  let M : X.Modules := (fromSkeleton X.Modules).obj (picClass rep j y).val
  exact if h : t ≫ m = m then
    if hψ : Nonempty (Scheme.Modules.unit X ≅ (Scheme.Modules.pullback m).obj M) then
      Scheme.Modules.unitHomAddEquiv (Scheme.Modules.unit X)
        ((Scheme.Modules.pullbackObjUnitIso t).inv ≫ (Scheme.Modules.pullback t).map hψ.some.hom ≫
          (Scheme.Modules.pullbackComp t m).hom.app M ≫
            (Scheme.Modules.pullbackCongr h).hom.app M ≫ hψ.some.inv)
    else 1
  else 1

/-- `K̄ → Γ(A_K̄, 𝒪)` (constants; a bijection, vendored
`bijective_appTop_of_isProper_of_geometricallyIntegral`). -/
def constK (A : AbVar K) : AlgebraicClosure K →+* Γ(pullback A.X.hom (ptK K).hom, ⊤) :=
  (pullback.snd A.X.hom (ptK K).hom).appTop.hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure K))).inv.hom

section LeafMumford

open HDec.WeilPairing

/-- **LEAF L4, fully genuine form (Mumford's `ē_n`).** As `WeilPairingPicZeroPrinted`, with the
pairing pinned to Mumford's genuine `ē_n` (`weilScalar`): its values, as constants of
`Γ(A_K̄, 𝒪)`, are `weilScalar`. Published: Mumford §20 and §23 (the properties), Kleiman Thm 9.2.5
(points of `Pic⁰` over `K̄` are line bundles on `A_K̄`), Mumford §8 (iv) (`n_A^*M ≅ 𝒪` for
`M ∈ Pic⁰[n]`), `Γ(A_K̄, 𝒪) = K̄`; UNVERIFIED numbering. Every clause is invariant under
`e ↦ -e`, so the leaf holds whichever sign convention for `ē_n` (`t_x^*ψ ψ⁻¹` or its inverse). -/
def WeilPairingMumford : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (B : AbVar K) (j : B.X ⟶ P),
    IsPicZero rep B j →
    ∃ e : ∀ n : ℕ, Pairing A B n,
      (∀ n : ℕ, 0 < n → (n : K) ≠ 0 → IsPerfect (e n)) ∧
      (∀ n : ℕ, 0 < n → (n : K) ≠ 0 → HDec.WeilPairing.IsGalEquivariant (e n)) ∧
      (∀ m n : ℕ, 0 < m → 0 < n → ((m * n : ℕ) : K) ≠ 0 →
        ∀ (x : tors A (m * n)) (y : tors B n),
          (e (m * n) x (torsIncl B (dvd_mul_left n m) y)).val = (e n (torsSmul A m n x) y).val) ∧
      (∀ (f : End A) (fv : End B), fv.hom ≫ j = j ≫ dualP rep f.hom → ∀ n : ℕ, 0 < n →
        (n : K) ≠ 0 → ∀ x y, e n x (torsMap fv n y) = e n (torsMap f n x) y) ∧
      (∀ L : A.X.left.Pic, IsAmple A.X.left L → ∀ lam : Hom A B, lam.hom ≫ j = phiL rep L →
        ∀ n : ℕ, 0 < n → (n : K) ≠ 0 → ∀ x : tors A n, e n x (torsMap lam n x) = 0) ∧
      (∀ n : ℕ, 0 < n → (n : K) ≠ 0 → ∀ (x : tors A n) (y : tors B n),
        constK A ((e n x y).val : AlgebraicClosure K) =
          weilScalar rep j n (Additive.toMul (x : HDec.WeilPairing.P A))
            (Additive.toMul (y : HDec.WeilPairing.P B)))

end LeafMumford

/-- The fully genuine L4 implies the printed L4 (forget the identification with `weilScalar`). -/
theorem weilPairingPicZeroPrinted_of_mumford (h : WeilPairingMumford) : WeilPairingPicZeroPrinted := by
  intro K _ A P rep B j hj
  obtain ⟨e, h1, h2, h3, h4, h5, -⟩ := h K A P rep B j hj
  exact ⟨e, h1, h2, h3, h4, h5⟩

/-- **Main result, fully genuine form.** -/
theorem t09SymmIsogenyExists_of_mumford (h0 : VeryAmpleIsAmple) (h1 : PicRepresentableAbVar)
    (h2 : PicZeroAbVar) (h3 : PhiAmpleIsogeny) (h4 : WeilPairingMumford) :
    HDec.WeilPairing.T09_SymmIsogenyExists :=
  t09SymmIsogenyExists_of_leaves h1 h2 (phiVeryAmpleIsogeny_of_printed h0 h3)
    (weilPairingPicZero_of_printed h0 (weilPairingPicZeroPrinted_of_mumford h4))

/-- **Main result, printed form.** `t09SymmIsogenyExists` from the five printed leaves
L0 (very ample ⇒ ample), L1 (Picard representability), L2 (`Pic⁰` is an abelian variety),
L3 (`φ_L` isogeny for ample `L`), L4 (Mumford's `ē_n` with the genuine `f^∨`). -/
theorem t09SymmIsogenyExists_of_printed (h0 : VeryAmpleIsAmple) (h1 : PicRepresentableAbVar)
    (h2 : PicZeroAbVar) (h3 : PhiAmpleIsogeny) (h4 : WeilPairingPicZeroPrinted) :
    HDec.WeilPairing.T09_SymmIsogenyExists :=
  t09SymmIsogenyExists_of_leaves h1 h2 (phiVeryAmpleIsogeny_of_printed h0 h3)
    (weilPairingPicZero_of_printed h0 h4)

end T09Pic

#print axioms T09Pic.exists_dual_on_picZero
#print axioms T09Pic.t09SymmIsogenyExists_of_mumford
#print axioms T09Pic.exists_isAmple_of_isAlgClosed
#print axioms T09Pic.t09SymmIsogenyExists_of_printed
#print axioms T09Pic.exists_isVeryAmple
#print axioms T09Pic.eta_comp_phiL
#print axioms T09Pic.exists_hom_comp_eq_phiL
#print axioms T09Pic.t09SymmIsogenyExists_of_leaves
