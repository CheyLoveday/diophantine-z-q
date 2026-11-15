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

end Leaves

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

end T09Pic

#print axioms T09Pic.exists_isVeryAmple
#print axioms T09Pic.eta_comp_phiL
#print axioms T09Pic.exists_hom_comp_eq_phiL
#print axioms T09Pic.t09SymmIsogenyExists_of_leaves
