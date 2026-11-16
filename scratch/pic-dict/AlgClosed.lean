import ZInQKernel.Contrib.OneProof.PicDictionary

/-! # pic-dict: Mumford's statements over an algebraically closed field, and the bridge to `A_K̄` -/

noncomputable section

set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory Limits
open scoped CategoryTheory.MonObj

namespace PicDict.AC

open PkgI3 PkgI3.AbVar

variable {k : Type} [Field k]

/-- `X(k)`: sections of `X → Spec k`. -/
abbrev Kpt (X : AbVar k) : Type := 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X.X

/-- Mumford's translation `t_x : X → X`. -/
def tr {X : AbVar k} (x : Kpt X) : X.X ⟶ X.X :=
  CartesianMonoidalCategory.lift (𝟙 _) (CartesianMonoidalCategory.toUnit _ ≫ x) ≫ μ[X.X]

/-- `n_X`. -/
def mul (X : AbVar k) (n : ℕ) : X.X ⟶ X.X := (𝟙 X.X) ^ n

end PicDict.AC

namespace PicDict

open T09Pic PkgI3 PkgI3.AbVar HDec.WeilPairing

variable {K : Type} [Field K]

/-- `A_K̄ = A ×_K K̄` over `K̄` (Mathlib's `Over.pullback`; group law transported by the monoidal functor). -/
abbrev bcX (A : AbVar K) : Over (Spec (CommRingCat.of (AlgebraicClosure K))) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))).obj A.X

instance (A : AbVar K) : GrpObj (bcX A) := Functor.grpObjObj

instance (A : AbVar K) : IsProper (bcX A).hom := by dsimp; infer_instance
instance (A : AbVar K) : Smooth (bcX A).hom := by dsimp; infer_instance
instance (A : AbVar K) : GeometricallyIntegral (bcX A).hom := by dsimp; infer_instance

/-- `A_K̄` as an abelian variety over `K̄`. -/
abbrev AKbar (A : AbVar K) : AbVar (AlgebraicClosure K) := AbVar.mk (bcX A)

example (A : AbVar K) : (AKbar A).X.left = AK A := rfl

/-- `A(K̄) → A_K̄(K̄)`. -/
def pts {A : AbVar K} (x : A.Pt (AlgebraicClosure K)) : AC.Kpt (AKbar A) :=
  Over.homMk (pullback.lift x.left (𝟙 _) (by rw [Category.id_comp]; exact Over.w x))
    (pullback.lift_snd _ _ _)

lemma pts_left_fst {A : AbVar K} (x : A.Pt (AlgebraicClosure K)) :
    (pts x).left ≫ pullback.fst A.X.hom (ptK K).hom = x.left := pullback.lift_fst _ _ _

lemma mu_AKbar (A : AbVar K) : μ[(AKbar A).X] =
    Functor.LaxMonoidal.μ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))))
        A.X A.X ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))).map μ[A.X] :=
  rfl

lemma tr_pts {A : AbVar K} (x : A.Pt (AlgebraicClosure K)) :
    (AC.tr (pts x)).left = (transl x).left := by
  apply pullback.hom_ext
  · rw [AC.tr, mu_AKbar]
    simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, pullback.lift_fst]
    have key : (CartesianMonoidalCategory.lift (𝟙 (bcX A))
          (CartesianMonoidalCategory.toUnit (bcX A) ≫ pts x)).left ≫
        (Functor.LaxMonoidal.μ (Over.pullback (Spec.map (CommRingCat.ofHom
          (algebraMap K (AlgebraicClosure K))))) A.X A.X).left ≫
        pullback.fst (A.X ⊗ A.X).hom (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) =
        (CartesianMonoidalCategory.lift (CartesianMonoidalCategory.fst A.X (ptK K))
          (CartesianMonoidalCategory.snd A.X (ptK K) ≫ x)).left := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, Over.μ_pullback_left_fst_fst]
        simp
        exact (pullback.lift_fst _ _ _).symm
      · rw [Category.assoc, Category.assoc, Over.μ_pullback_left_fst_snd]
        simp
        exact (congrArg (_ ≫ ·) (pts_left_fst x)).trans (pullback.lift_snd _ _ _).symm
    rw [reassoc_of% key]
    simp [transl]
    exact (pullback.lift_fst _ _ _).symm
  · have h1 := Over.w (AC.tr (pts x))
    have h2 : (transl x).left ≫ pullback.snd A.X.hom (ptK K).hom = pullback.snd A.X.hom (ptK K).hom := by
      have := congrArg Over.Hom.left (CartesianMonoidalCategory.lift_snd
        (CartesianMonoidalCategory.lift (CartesianMonoidalCategory.fst A.X (ptK K))
          (CartesianMonoidalCategory.snd A.X (ptK K) ≫ x) ≫ μ[A.X]) (CartesianMonoidalCategory.snd A.X (ptK K)))
      simpa [transl] using this
    exact h1.trans h2.symm

end PicDict
