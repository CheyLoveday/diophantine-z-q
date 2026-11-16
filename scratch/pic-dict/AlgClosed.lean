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

lemma tr_comp_tr {X : AbVar k} (z x : Kpt X) : tr z ≫ tr x = tr (z * x) := by
  simp only [tr, ← CategoryTheory.Hom.mul_def]
  rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc,
    CartesianMonoidalCategory.toUnit_unique (_ ≫ CartesianMonoidalCategory.toUnit X.X)
      (CartesianMonoidalCategory.toUnit X.X), mul_assoc, ← MonObj.comp_mul]

lemma tr_comp_mul {X : AbVar k} {n : ℕ} (x : Kpt X) (hx : x ^ n = 1) : tr x ≫ mul X n = mul X n := by
  simp only [tr, mul, ← CategoryTheory.Hom.mul_def]
  rw [MonObj.comp_pow, Category.comp_id, mul_pow, ← MonObj.comp_pow, hx, MonObj.comp_one, mul_one]

/-- Mumford's `Pic⁰(X)`: classes invariant under every `t_x`, `x ∈ X(k)`. -/
def IsTI {X : AbVar k} (c : X.X.left.Pic) : Prop := ∀ x : Kpt X, Scheme.Pic.map (tr x).left c = c

/-- `X̂_n`. -/
def IsDT {X : AbVar k} (n : ℕ) (c : X.X.left.Pic) : Prop := IsTI c ∧ c ^ n = 1

/-- `φ_L(x) = t_x^*L ⊗ L⁻¹`. -/
def phi {X : AbVar k} (c : X.X.left.Pic) (x : Kpt X) : X.X.left.Pic :=
  Scheme.Pic.map (tr x).left c * c⁻¹

/-- The module of a class. -/
abbrev modX {X : AbVar k} (c : X.X.left.Pic) : X.X.left.Modules :=
  (fromSkeleton X.X.left.Modules).obj c.val

/-- Trivializations of `n_X^*M`. -/
abbrev Triv (X : AbVar k) (n : ℕ) (c : X.X.left.Pic) :=
  Scheme.Modules.unit X.X.left ≅ (Scheme.Modules.pullback (mul X n).left).obj (modX c)

/-- **Mumford's formula** `ē_n(x, M) = t_x^*ψ ∘ ψ⁻¹` (§20). -/
def formula {X : AbVar k} {n : ℕ} (x : Kpt X) (hx : x ^ n = 1) (c : X.X.left.Pic) (ψ : Triv X n c) :
    Γ(X.X.left, ⊤) :=
  Transport.wf (tr x).left (mul X n).left (by rw [← Over.comp_left, tr_comp_mul x hx]) (modX c) ψ

/-- Constants `k → Γ(X, 𝒪)`. -/
def const (X : AbVar k) (u : k) : Γ(X.X.left, ⊤) :=
  X.X.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom u)

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
    (pts x).left ≫ pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) =
      x.left := pullback.lift_fst _ _ _

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

lemma mul_AKbar (A : AbVar K) (n : ℕ) : (AC.mul (AKbar A) n).left = (mulN A n).left := by
  have h1 : AC.mul (AKbar A) n =
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))).map
        ((𝟙 A.X) ^ n) := by
    rw [AC.mul]
    have := map_pow (Functor.homMonoidHom (Over.pullback (Spec.map (CommRingCat.ofHom
      (algebraMap K (AlgebraicClosure K)))))) (𝟙 A.X) n
    simp only [Functor.homMonoidHom_apply, CategoryTheory.Functor.map_id] at this
    exact this.symm
  rw [h1, mulN]
  apply pullback.hom_ext
  · simp
    exact (congrArg Over.Hom.left (CartesianMonoidalCategory.whiskerRight_fst ((𝟙 A.X) ^ n) (ptK K))).symm
  · simp
    exact (congrArg Over.Hom.left (CartesianMonoidalCategory.whiskerRight_snd ((𝟙 A.X) ^ n) (ptK K))).symm

lemma pts_mul {A : AbVar K} (x y : A.Pt (AlgebraicClosure K)) : pts (x * y) = pts x * pts y := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · rw [pts_left_fst]
    change _ = (CartesianMonoidalCategory.lift (pts x) (pts y) ≫ μ[bcX A]).left ≫ _
    rw [mu_AKbar]
    simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, pullback.lift_fst]
    have key : (CartesianMonoidalCategory.lift (pts x) (pts y)).left ≫
        (Functor.LaxMonoidal.μ (Over.pullback (Spec.map (CommRingCat.ofHom
          (algebraMap K (AlgebraicClosure K))))) A.X A.X).left ≫
        pullback.fst (A.X ⊗ A.X).hom (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) =
        (CartesianMonoidalCategory.lift x y).left := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, Over.μ_pullback_left_fst_fst]
        simp
        exact (pts_left_fst x).trans (pullback.lift_fst _ _ _).symm
      · rw [Category.assoc, Category.assoc, Over.μ_pullback_left_fst_snd]
        simp
        exact (pts_left_fst y).trans (pullback.lift_snd _ _ _).symm
    rw [reassoc_of% key]
    rfl
  · exact (Over.w (pts (x * y))).trans (Over.w (pts x * pts y)).symm

/-- `A_K̄(K̄) → A(K̄)`, inverse of `pts`. -/
def unpts {A : AbVar K} (σ : AC.Kpt (AKbar A)) : A.Pt (AlgebraicClosure K) :=
  Over.homMk (σ.left ≫ pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))))
    (by
      change (σ.left ≫ pullback.fst _ _) ≫ A.X.hom = _
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      have := Over.w σ
      simp only [Functor.id_obj, Functor.const_obj_obj] at this
      exact (congrArg (· ≫ _) this).trans (Category.id_comp _))

lemma pts_unpts {A : AbVar K} (σ : AC.Kpt (AKbar A)) : pts (unpts σ) = σ := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact pts_left_fst _
  · exact (Over.w (pts (unpts σ))).trans (Over.w σ).symm

lemma pts_injective {A : AbVar K} : Function.Injective (pts (A := A)) := by
  intro x y h
  apply Over.OverMorphism.ext
  rw [← pts_left_fst x, ← pts_left_fst y, h]

lemma pts_surjective {A : AbVar K} : Function.Surjective (pts (A := A)) :=
  fun σ => ⟨unpts σ, pts_unpts σ⟩

/-- `pts` as a group isomorphism. -/
def ptsHom (A : AbVar K) : A.Pt (AlgebraicClosure K) →* AC.Kpt (AKbar A) :=
  MonoidHom.mk' pts pts_mul

end PicDict
