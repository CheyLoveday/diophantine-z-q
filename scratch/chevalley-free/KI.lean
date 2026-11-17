import ZInQKernel.Contrib.OneProof.SemiAbelianDescendsPerfect
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.AbelianVariety.RationalCurves
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Birational.ValuativeExtension
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Curve.Dimension
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Descent.LocalSections
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Geometrically.Smooth
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Descent.Finite
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.CategoryTheory.Limits.Shapes.Pullback.Map

/-! # chevalley-free, step R: morphisms from `𝔾_m` to an abelian variety are constant -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open AlgebraicGeometry.ProjectiveLine AlgebraicGeometry.ProjectiveSpace ZInQ.SemiAbDescend
open DictModels.RaynaudOr ZInQ.HeightSplit

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ZInQ.ChevFree


section Descent

variable {S S' : Scheme.{0}} (q : S' ⟶ S) {U : Over S} {X₁ : Over S'}
  (π₁ : (Over.pullback q).obj U ⟶ X₁)

/-- `X₁ ×_S S'`. -/
abbrev PP := pullback (X₁.hom ≫ q) q

/-- `U_{S'} ×_S S'`. -/
abbrev YY := pullback (π₁.left ≫ X₁.hom ≫ q) q

/-- `π₁ × id : U_{S'} ×_S S' → X₁ ×_S S'`. -/
abbrev αα : YY q π₁ ⟶ PP q (X₁ := X₁) :=
  pullback.map (π₁.left ≫ X₁.hom ≫ q) q (X₁.hom ≫ q) q π₁.left (𝟙 _) (𝟙 _) (by simp) (by simp)

theorem isPullback_αα :
    IsPullback (pullback.fst _ _) (αα q π₁) π₁.left (pullback.fst (X₁.hom ≫ q) q) :=
  isPullback_pullback_map_left π₁.left (X₁.hom ≫ q) q

theorem w_π₁ : π₁.left ≫ X₁.hom = pullback.snd U.hom q := Over.w π₁

/-- The `U`-coordinate of a point of `U_{S'} ×_S S'`. -/
abbrev uPart : YY q π₁ ⟶ U.left := pullback.fst _ _ ≫ pullback.fst U.hom q

theorem uPart_cond : uPart q π₁ ≫ U.hom = pullback.snd (π₁.left ≫ X₁.hom ≫ q) q ≫ q := by
  rw [Category.assoc, pullback.condition, ← w_π₁ q π₁, ← Category.assoc, ← Category.assoc]
  simp only [Category.assoc]
  exact pullback.condition

/-- `(u, a, b) ↦ π₁(u, b)`. -/
abbrev ββ : YY q π₁ ⟶ X₁.left :=
  pullback.lift (uPart q π₁) (pullback.snd _ _) (uPart_cond q π₁) ≫ π₁.left

/-- **The transport condition `KI`**: if `u, v` have the same image under `π₁` over `a`, they have the same image
over every `b` with the same image in `S`. -/
def KI : Prop :=
  ∀ (Z : Scheme.{0}) (u v : Z ⟶ U.left) (a b : Z ⟶ S') (hu : u ≫ U.hom = a ≫ q)
    (hv : v ≫ U.hom = a ≫ q) (hb : a ≫ q = b ≫ q),
    pullback.lift u a hu ≫ π₁.left = pullback.lift v a hv ≫ π₁.left →
    pullback.lift u b (hu.trans hb) ≫ π₁.left = pullback.lift v b (hv.trans hb) ≫ π₁.left

variable {q π₁}

theorem ββ_coeq (hKI : KI q π₁) {Z : Scheme.{0}} (g h : Z ⟶ YY q π₁)
    (hgh : g ≫ αα q π₁ = h ≫ αα q π₁) : g ≫ ββ q π₁ = h ≫ ββ q π₁ := by
  have h1 : g ≫ pullback.fst _ _ ≫ π₁.left = h ≫ pullback.fst _ _ ≫ π₁.left := by
    have := congrArg (· ≫ pullback.fst (X₁.hom ≫ q) q) hgh
    simpa only [Category.assoc, pullback.lift_fst] using this
  have h2 : g ≫ pullback.snd _ _ = h ≫ pullback.snd _ _ := by
    have := congrArg (· ≫ pullback.snd (X₁.hom ≫ q) q) hgh
    simpa only [Category.assoc, pullback.lift_snd, Category.comp_id] using this
  have h3 : g ≫ pullback.fst _ _ ≫ pullback.snd U.hom q = h ≫ pullback.fst _ _ ≫ pullback.snd U.hom q := by
    have := congrArg (· ≫ X₁.hom) h1
    simpa only [Category.assoc, w_π₁] using this
  set a := g ≫ pullback.fst _ _ ≫ pullback.snd U.hom q
  set b := g ≫ pullback.snd (π₁.left ≫ X₁.hom ≫ q) q
  have hu : (g ≫ uPart q π₁) ≫ U.hom = a ≫ q := by
    simp only [a, Category.assoc, pullback.condition]
  have hv : (h ≫ uPart q π₁) ≫ U.hom = a ≫ q := by
    rw [h3]; simp only [Category.assoc, pullback.condition]
  have hb : a ≫ q = b ≫ q := by
    have := congrArg (g ≫ ·) (uPart_cond q π₁)
    simp only [Category.assoc] at this
    simp only [a, b, Category.assoc]
    rw [show pullback.snd U.hom q ≫ q = pullback.fst U.hom q ≫ U.hom from pullback.condition.symm]
    exact this
  have eg : g ≫ pullback.fst _ _ = pullback.lift (g ≫ uPart q π₁) a hu := by
    apply pullback.hom_ext <;> simp [a]
  have eh : h ≫ pullback.fst _ _ = pullback.lift (h ≫ uPart q π₁) a hv := by
    apply pullback.hom_ext
    · simp
    · simp [a, h3]
  have key := hKI Z (g ≫ uPart q π₁) (h ≫ uPart q π₁) a b hu hv hb (by
    rw [← eg, ← eh]; simpa only [Category.assoc] using h1)
  have eg' : g ≫ pullback.lift (uPart q π₁) (pullback.snd _ _) (uPart_cond q π₁) =
      pullback.lift (g ≫ uPart q π₁) b (hu.trans hb) := by
    apply pullback.hom_ext <;> simp [b]
  have eh' : h ≫ pullback.lift (uPart q π₁) (pullback.snd _ _) (uPart_cond q π₁) =
      pullback.lift (h ≫ uPart q π₁) b (hv.trans hb) := by
    apply pullback.hom_ext
    · simp
    · simp [b, h2]
  simp only [ββ, ← Category.assoc, eg', eh']
  exact key

variable [Flat π₁.left] [Surjective π₁.left] [QuasiCompact π₁.left]

instance : Flat (αα q π₁) := MorphismProperty.of_isPullback (P := @Flat) (isPullback_αα q π₁) inferInstance
instance : Surjective (αα q π₁) :=
  MorphismProperty.of_isPullback (P := @Surjective) (isPullback_αα q π₁) inferInstance
instance : QuasiCompact (αα q π₁) :=
  MorphismProperty.of_isPullback (P := @QuasiCompact) (isPullback_αα q π₁) inferInstance

/-- **The descent datum in universal form**: `ψ : X₁ ×_S S' → X₁`, `(π₁(u, a), b) ↦ π₁(u, b)`. -/
def ψψ (hKI : KI q π₁) : PP q (X₁ := X₁) ⟶ X₁.left :=
  EffectiveEpi.desc (αα q π₁) (ββ q π₁) (fun g h hgh => ββ_coeq hKI g h hgh)

theorem ψ_fac (hKI : KI q π₁) : αα q π₁ ≫ ψψ hKI = ββ q π₁ := EffectiveEpi.fac _ _ _

/-- The transport of `π₁(u₁)` to `c` is `π₁(u, c)`. -/
theorem ψ_π (hKI : KI q π₁) {Z : Scheme.{0}} (u₁ : Z ⟶ ((Over.pullback q).obj U).left) (c : Z ⟶ S')
    (h : (u₁ ≫ π₁.left) ≫ X₁.hom ≫ q = c ≫ q) :
    pullback.lift (u₁ ≫ π₁.left) c h ≫ ψψ hKI =
      pullback.lift (u₁ ≫ pullback.fst U.hom q) c (by
        rw [Category.assoc, pullback.condition, ← Category.assoc, ← h, ← w_π₁ q π₁]
        simp only [Category.assoc]) ≫ π₁.left := by
  have e : pullback.lift (u₁ ≫ π₁.left) c h = pullback.lift u₁ c (by simpa only [Category.assoc] using h) ≫
      αα q π₁ := by
    apply pullback.hom_ext <;> simp
  rw [e, Category.assoc, ψ_fac]
  simp only [ββ, ← Category.assoc]
  congr 1
  apply pullback.hom_ext <;> simp

theorem ψ_snd (hKI : KI q π₁) : ψψ hKI ≫ X₁.hom = pullback.snd (X₁.hom ≫ q) q := by
  rw [← cancel_epi (αα q π₁), ← Category.assoc, ψ_fac]
  simp only [ββ, Category.assoc, w_π₁, pullback.lift_snd, Category.comp_id]

theorem ψ_unit (hKI : KI q π₁) :
    (pullback.lift (𝟙 X₁.left) X₁.hom (by simp) : X₁.left ⟶ PP q (X₁ := X₁)) ≫ ψψ hKI = 𝟙 X₁.left := by
  rw [← cancel_epi π₁.left, ← Category.assoc, Category.comp_id]
  have e : π₁.left ≫ (pullback.lift (𝟙 X₁.left) X₁.hom (by simp) : X₁.left ⟶ PP q (X₁ := X₁)) =
      pullback.lift (𝟙 _ ≫ π₁.left) (pullback.snd U.hom q)
        (by rw [Category.id_comp, reassoc_of% (w_π₁ q π₁)]) := by
    apply pullback.hom_ext
    · simp
    · simp only [Category.assoc, pullback.lift_snd]; exact w_π₁ q π₁
  rw [e, ψ_π hKI (𝟙 _)]
  conv_rhs => rw [← Category.id_comp π₁.left]
  congr 1
  apply pullback.hom_ext <;> simp

/-- `(X₁ ×_S S') ×_S S'`. -/
abbrev TT := pullback (pullback.snd (X₁.hom ≫ q) q ≫ q) q

/-- `(U_{S'} ×_S S') ×_S S'`. -/
abbrev TU := pullback (αα q π₁ ≫ pullback.snd (X₁.hom ≫ q) q ≫ q) q

abbrev α₃ : TU (q := q) (π₁ := π₁) ⟶ TT (q := q) (X₁ := X₁) :=
  pullback.map (αα q π₁ ≫ pullback.snd (X₁.hom ≫ q) q ≫ q) q (pullback.snd (X₁.hom ≫ q) q ≫ q) q
    (αα q π₁) (𝟙 _) (𝟙 _) (by simp) (by simp)

theorem isPullback_α₃ :
    IsPullback (pullback.fst _ _) (α₃ (q := q) (π₁ := π₁)) (αα q π₁) (pullback.fst _ _) :=
  isPullback_pullback_map_left (αα q π₁) (pullback.snd (X₁.hom ≫ q) q ≫ q) q

instance : Flat (α₃ (q := q) (π₁ := π₁)) :=
  MorphismProperty.of_isPullback (P := @Flat) isPullback_α₃ inferInstance
instance : Surjective (α₃ (q := q) (π₁ := π₁)) :=
  MorphismProperty.of_isPullback (P := @Surjective) isPullback_α₃ inferInstance
instance : QuasiCompact (α₃ (q := q) (π₁ := π₁)) :=
  MorphismProperty.of_isPullback (P := @QuasiCompact) isPullback_α₃ inferInstance

theorem ψ_coassoc_univ (hKI : KI q π₁) :
    pullback.lift (pullback.fst (pullback.snd (X₁.hom ≫ q) q ≫ q) q ≫ ψψ hKI)
      (pullback.snd (pullback.snd (X₁.hom ≫ q) q ≫ q) q) (by
        rw [Category.assoc, reassoc_of% (ψ_snd hKI), pullback.condition]) ≫ ψψ hKI =
    pullback.lift (pullback.fst (pullback.snd (X₁.hom ≫ q) q ≫ q) q ≫ pullback.fst (X₁.hom ≫ q) q)
      (pullback.snd (pullback.snd (X₁.hom ≫ q) q ≫ q) q) (by
        rw [Category.assoc, pullback.condition]; exact pullback.condition) ≫ ψψ hKI := by
  rw [← cancel_epi (α₃ (q := q) (π₁ := π₁))]
  refine (Category.assoc _ _ _).symm.trans (Eq.trans ?_ (Category.assoc _ _ _))
  let y := pullback.fst (αα q π₁ ≫ pullback.snd (X₁.hom ≫ q) q ≫ q) q
  let c' := pullback.snd (αα q π₁ ≫ pullback.snd (X₁.hom ≫ q) q ≫ q) q
  let u₁ := y ≫ pullback.lift (uPart q π₁) (pullback.snd _ _) (uPart_cond q π₁)
  have hc : y ≫ (αα q π₁ ≫ pullback.snd (X₁.hom ≫ q) q ≫ q) = c' ≫ q := pullback.condition
  have hαs : αα q π₁ ≫ pullback.snd (X₁.hom ≫ q) q = pullback.snd (π₁.left ≫ X₁.hom ≫ q) q := by
    simp
  have hαs' : αα q π₁ ≫ pullback.snd (X₁.hom ≫ q) q ≫ q =
      pullback.snd (π₁.left ≫ X₁.hom ≫ q) q ≫ q := by rw [← Category.assoc, hαs]
  have w' : π₁.left ≫ X₁.hom ≫ q = pullback.snd U.hom q ≫ q := by rw [← Category.assoc, w_π₁]
  have h1 : (u₁ ≫ π₁.left) ≫ X₁.hom ≫ q = c' ≫ q := by
    have e : (u₁ ≫ π₁.left) ≫ X₁.hom ≫ q = y ≫ (pullback.snd (π₁.left ≫ X₁.hom ≫ q) q ≫ q) := by
      simp only [u₁, Category.assoc, w', pullback.lift_snd_assoc]
    exact e.trans ((congrArg (y ≫ ·) hαs').symm.trans hc)
  have h2 : ((y ≫ pullback.fst _ _) ≫ π₁.left) ≫ X₁.hom ≫ q = c' ≫ q := by
    have e : ((y ≫ pullback.fst _ _) ≫ π₁.left) ≫ X₁.hom ≫ q =
        y ≫ (pullback.snd (π₁.left ≫ X₁.hom ≫ q) q ≫ q) := by
      simp only [Category.assoc]; exact congrArg (y ≫ ·) pullback.condition
    exact e.trans ((congrArg (y ≫ ·) hαs').symm.trans hc)
  have e1 : α₃ (q := q) (π₁ := π₁) ≫ pullback.lift (pullback.fst (pullback.snd (X₁.hom ≫ q) q ≫ q) q ≫ ψψ hKI)
      (pullback.snd (pullback.snd (X₁.hom ≫ q) q ≫ q) q) (by
        rw [Category.assoc, reassoc_of% (ψ_snd hKI), pullback.condition]) =
      pullback.lift (u₁ ≫ π₁.left) c' h1 := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, u₁, y]
      rw [pullback.lift_fst_assoc, Category.assoc, ψ_fac]
    · simp [c']
  have e2 : α₃ (q := q) (π₁ := π₁) ≫ pullback.lift
      (pullback.fst (pullback.snd (X₁.hom ≫ q) q ≫ q) q ≫ pullback.fst (X₁.hom ≫ q) q)
      (pullback.snd (pullback.snd (X₁.hom ≫ q) q ≫ q) q) (by
        rw [Category.assoc, pullback.condition]; exact pullback.condition) =
      pullback.lift ((y ≫ pullback.fst _ _) ≫ π₁.left) c' h2 := by
    apply pullback.hom_ext
    · simp [y]
    · simp [c']
  rw [e1, e2, ψ_π hKI, ψ_π hKI]
  congr 2
  simp [u₁, uPart]

theorem ψ_coassoc (hKI : KI q π₁) {Z : Scheme.{0}} (x : Z ⟶ X₁.left) (b c : Z ⟶ S')
    (hb : x ≫ X₁.hom ≫ q = b ≫ q) (hc : x ≫ X₁.hom ≫ q = c ≫ q) :
    pullback.lift (pullback.lift x b hb ≫ ψψ hKI) c (by
      rw [Category.assoc, reassoc_of% (ψ_snd hKI), pullback.lift_snd_assoc, ← hb, hc]) ≫ ψψ hKI =
      pullback.lift x c hc ≫ ψψ hKI := by
  let t : Z ⟶ TT (q := q) (X₁ := X₁) := pullback.lift (pullback.lift x b hb) c (by
    rw [pullback.lift_snd_assoc, ← hb, hc])
  have := congrArg (t ≫ ·) (ψ_coassoc_univ (q := q) (π₁ := π₁) hKI)
  simp only [← Category.assoc] at this
  convert this using 2
  · apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, t]; rw [pullback.lift_fst_assoc]
    · simp [t]
  · apply pullback.hom_ext
    · simp [t]
    · simp [t]

/-- **The descent datum on `X₁`** (transport form): a point `x` over `f₁` goes to `ψ(x, f₂)`. -/
def dd (hKI : KI q π₁) : Over.DescentDatum q X₁ where
  transport f₁ f₂ e p := Over.homMk (pullback.lift p.left f₂ (by rw [← Category.assoc, Over.w p]; exact e) ≫
    ψψ hKI) (by
      change (pullback.lift p.left f₂ _ ≫ ψψ hKI) ≫ X₁.hom = f₂
      rw [Category.assoc, ψ_snd, pullback.lift_snd])
  transport_homMk_comp c f₁ f₂ e p := by
    ext
    change pullback.lift (c ≫ p.left) (c ≫ f₂) _ ≫ ψψ hKI = c ≫ (pullback.lift p.left f₂ _ ≫ ψψ hKI)
    refine Eq.trans ?_ (Category.assoc _ _ _)
    congr 1
    apply pullback.hom_ext <;> simp
  transport_self f p := by
    ext
    simp only [Over.homMk_left]
    have : pullback.lift p.left f (by rw [← Category.assoc, Over.w p]; rfl) =
        p.left ≫ (pullback.lift (𝟙 X₁.left) X₁.hom (by simp) : X₁.left ⟶ PP q (X₁ := X₁)) := by
      apply pullback.hom_ext
      · simp
      · simp only [Category.assoc, pullback.lift_snd]; exact (Over.w p).symm
    rw [this, Category.assoc, ψ_unit, Category.comp_id]
  transport_transport f₁ f₂ f₃ h₁₂ h₂₃ p := by
    ext
    simp only [Over.homMk_left]
    exact ψ_coassoc hKI p.left f₂ f₃ _ _

/-- **Descent of the quotient**: with `KI`, finite sets of `X₁` in affine opens, and `q` finite flat surjective
of finite presentation, `X₁` descends to `B₀` over `S` and `π₁` to `π : U → B₀`. -/
theorem exists_descent (hKI : KI q π₁) [IsFinite q] [Flat q] [LocallyOfFinitePresentation q] [Surjective q]
    (hfin : ∀ s : Set X₁.left, s.Finite → ∃ V : X₁.left.Opens, IsAffineOpen V ∧ s ⊆ V) :
    ∃ (B₀ : Over S) (d : X₁.left ⟶ B₀.left) (π : U.left ⟶ B₀.left),
      IsPullback d X₁.hom B₀.hom q ∧ pullback.fst U.hom q ≫ π = π₁.left ≫ d ∧ π ≫ B₀.hom = U.hom := by
  obtain ⟨B₀, d, hsq, hinv⟩ := (dd hKI).isEffective_of_isFinite hfin
  have hψd : ψψ hKI ≫ d = pullback.fst (X₁.hom ≫ q) q ≫ d := by
    have := hinv (pullback.fst (X₁.hom ≫ q) q ≫ X₁.hom) (pullback.snd _ _)
      (by rw [Category.assoc]; exact pullback.condition) (Over.homMk (pullback.fst _ _) rfl)
    change (pullback.lift (pullback.fst (X₁.hom ≫ q) q) (pullback.snd (X₁.hom ≫ q) q) _ ≫ ψψ hKI) ≫ d =
      pullback.fst (X₁.hom ≫ q) q ≫ d at this
    rwa [pullback.lift_fst_snd, Category.id_comp] at this
  have hcoeq : ∀ {Z : Scheme.{0}} (g h : Z ⟶ pullback U.hom q),
      g ≫ pullback.fst U.hom q = h ≫ pullback.fst U.hom q → g ≫ π₁.left ≫ d = h ≫ π₁.left ≫ d := by
    intro Z g h hgh
    have hc : (g ≫ π₁.left) ≫ X₁.hom ≫ q = (h ≫ pullback.snd U.hom q) ≫ q :=
      calc (g ≫ π₁.left) ≫ X₁.hom ≫ q = g ≫ pullback.snd U.hom q ≫ q := by
            rw [Category.assoc, ← Category.assoc π₁.left, w_π₁]
        _ = g ≫ pullback.fst U.hom q ≫ U.hom := by rw [pullback.condition]
        _ = h ≫ pullback.fst U.hom q ≫ U.hom := by rw [← Category.assoc, hgh, Category.assoc]
        _ = (h ≫ pullback.snd U.hom q) ≫ q := by rw [pullback.condition, Category.assoc]
    have e := ψ_π hKI g (h ≫ pullback.snd U.hom q) hc
    have e' : pullback.lift (g ≫ pullback.fst U.hom q) (h ≫ pullback.snd U.hom q) (by
        rw [hgh, Category.assoc, Category.assoc, pullback.condition]) = h := by
      apply pullback.hom_ext
      · simp [hgh]
      · simp
    rw [e'] at e
    rw [← Category.assoc h, ← e, Category.assoc, hψd, pullback.lift_fst_assoc, Category.assoc]
  refine ⟨B₀, d, EffectiveEpi.desc (pullback.fst U.hom q) (π₁.left ≫ d) (fun g h hgh => hcoeq g h hgh),
    hsq, EffectiveEpi.fac _ _ _, ?_⟩
  rw [← cancel_epi (pullback.fst U.hom q), ← Category.assoc, EffectiveEpi.fac, Category.assoc, hsq.w,
    ← Category.assoc, w_π₁, pullback.condition]

end Descent



section Rig

variable (K : Type) [Field K]

/-- `Spec K`. -/
abbrev PK : Scheme := Spec (CommRingCat.of K)

/-- The overlap `𝔾_m ⊆ ℙ¹_K` of the two standard charts. -/
abbrev Ov : Scheme := (relativeOverlap (PK K)).toScheme

/-- An element of `K` as a global section of `Spec K`. -/
abbrev secK (s : K) : Γ(PK K, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of K)).inv s

theorem mem_overlap (s : Kˣ) (x : PK K) :
    normalized (𝟙 (PK K)) ⟨1⟩ (secK K s) x ∈ relativeOverlap (PK K) := by
  have hc : ∀ c : ULift.{0} (Fin 2),
      normalized (𝟙 (PK K)) ⟨1⟩ (secK K s) x ∈ standardOpen (ULift.{0} (Fin 2)) (PK K) c := by
    intro c
    change x ∈ normalized (𝟙 (PK K)) ⟨1⟩ (secK K s) ⁻¹ᵁ standardOpen (ULift.{0} (Fin 2)) (PK K) c
    rw [normalized, homOfSections_preimage_standardOpen]
    have hu : IsUnit (normalizedSections (source := PK K) ⟨1⟩ (secK K s) c) := by
      unfold normalizedSections
      split_ifs
      · exact isUnit_one
      · exact (s.isUnit.map _)
    rw [Scheme.basicOpen_of_isUnit _ hu]
    trivial
  exact ⟨hc ⟨0⟩, hc ⟨1⟩⟩

/-- The `K`-point `[s : 1]` of the overlap. -/
def ovPt (s : Kˣ) : PK K ⟶ Ov K :=
  IsOpenImmersion.lift (relativeOverlap (PK K)).ι (normalized (𝟙 (PK K)) ⟨1⟩ (secK K s)) (by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact mem_overlap K s x)

@[reassoc (attr := simp)]
theorem ovPt_ι (s : Kˣ) : ovPt K s ≫ (relativeOverlap (PK K)).ι = normalized (𝟙 (PK K)) ⟨1⟩ (secK K s) :=
  IsOpenImmersion.lift_fac ..

theorem ovPt_over (s : Kˣ) : ovPt K s ≫ overlapToBase K = 𝟙 (PK K) := by
  rw [overlapToBase, ovPt_ι_assoc, normalized_over]

theorem ovPt_coordinate (s : Kˣ) : (ovPt K s).appTop (scalingCoordinate K ⟨1⟩) = secK K s := by
  have chartEquation : ovPt K s ≫ ((relativeLine (PK K))).homOfLE
      (relativeOverlap_le_standardOpen (PK K) ⟨1⟩) =
      relativeChartPoint (𝟙 (PK K)) ⟨1⟩ (secK K s) := by
    apply (cancel_mono (standardOpen (ULift.{0} (Fin 2)) (PK K) ⟨1⟩).ι).mp
    simp
  rw [scalingCoordinate, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    chartEquation, relativeChartPoint_coordinate]

/-- `ℙ¹_K` is smooth of relative dimension one. -/
instance line_smooth : SmoothOfRelativeDimension 1 (relativeLine (PK K) ↘ PK K) := by
  haveI : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} 1) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  apply IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension.{0} 1) (relativeChartCover (PK K))
  intro (c : ULift.{0} (Fin 2))
  change SmoothOfRelativeDimension 1
    ((standardOpen (ULift.{0} (Fin 2)) (PK K) c).ι ≫ relativeLine (PK K) ↘ PK K)
  rw [← standardOpenIso_hom_over]
  have : Nat.card {o : ULift.{0} (Fin 2) // o ≠ c} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => ?_⟩, ⟨⟨⟨c.down.rev⟩, ?_⟩⟩⟩
    · rcases a with ⟨⟨a⟩, ha⟩; rcases b with ⟨⟨b⟩, hb⟩; rcases c with ⟨c⟩
      ext; simp only [ne_eq, ULift.ext_iff] at ha hb ⊢; omega
    · rcases c with ⟨c⟩; simp only [ne_eq, ULift.ext_iff]; fin_cases c <;> decide
  rw [MorphismProperty.cancel_left_of_respectsIso (P := @SmoothOfRelativeDimension.{0} 1)]
  exact AffineSpace.smoothOfRelativeDimension_of_card_eq (n := {o : ULift.{0} (Fin 2) // o ≠ c})
    (PK K) this


variable {K}

theorem genericPoint_mem_overlap : genericPoint (relativeLine (PK K)) ∈ relativeOverlap (PK K) := by
  rw [← SetLike.mem_coe,
    (genericPoint_spec (relativeLine (PK K))).mem_open_set_iff (relativeOverlap (PK K)).isOpen]
  simpa using (Scheme.Opens.nonempty_iff _).mp (inferInstance : Nonempty (Ov K))

/-- `Spec K(ℙ¹) → 𝔾_m`. -/
abbrev ξg : Spec (relativeLine (PK K)).functionField ⟶ Ov K :=
  (relativeOverlap (PK K)).fromSpecStalkOfMem _ (genericPoint_mem_overlap (K := K))

theorem ξg_ι : ξg (K := K) ≫ (relativeOverlap (PK K)).ι = (relativeLine (PK K)).fromSpecFunctionField :=
  Scheme.Opens.fromSpecStalkOfMem_ι _ _ _

instance : IsDominant (ξg (K := K)) := by
  constructor
  let p : Spec (relativeLine (PK K)).functionField :=
    IsLocalRing.closedPoint ((relativeLine (PK K)).functionField)
  let z := (ξg (K := K)) p
  have hz : (relativeOverlap (PK K)).ι z = genericPoint (relativeLine (PK K)) := by
    show (relativeOverlap (PK K)).ι ((ξg (K := K)) p) = _
    rw [← Scheme.Hom.comp_apply, ξg_ι]
    exact Scheme.fromSpecStalk_closedPoint
  have hd : Dense ({z} : Set (Ov K)) := by
    rw [dense_iff_closure_eq,
      (relativeOverlap (PK K)).ι.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image,
      Set.image_singleton, hz, genericPoint_closure]
    rfl
  exact hd.mono (by rintro _ rfl; exact ⟨_, rfl⟩)

/-- Every morphism `ℙ¹_K → B` to an abelian variety takes the same value at all `K`-points
(vendored `RationalCurves.eq_zero_comp`, commutativity from Mathlib). -/
theorem line_const (B : PkgI3.AbVar K) (E : relativeLineOver K ⟶ B.X)
    (a b : 𝟙_ (Over (PK K)) ⟶ relativeLineOver K) : a ≫ E = b ≫ E := by
  letI := B.grp
  haveI := B.proper
  haveI := B.smooth
  haveI := B.geomInt
  haveI : IsCommMonObj B.X := isCommMonObj_of_isProper_of_geometricallyIntegral B.X
  let V : AlgebraicGeometry.AbelianVariety K := ⟨CommGrp.mk B.X⟩
  have hE := AlgebraicGeometry.AbelianVariety.RationalCurves.eq_zero_comp V E
  have ha : a ≫ E = ProjectiveLine.zeroPointOver K ≫ E := by
    conv_lhs => rw [hE]
    rw [← Category.assoc, ← Category.assoc, Subsingleton.elim (a ≫ toUnit _) (𝟙 _), Category.id_comp]
  have hb : b ≫ E = ProjectiveLine.zeroPointOver K ≫ E := by
    conv_lhs => rw [hE]
    rw [← Category.assoc, ← Category.assoc, Subsingleton.elim (b ≫ toUnit _) (𝟙 _), Category.id_comp]
  rw [ha, hb]

/-- **Rigidity for `𝔾_m`**: a morphism from the overlap `𝔾_m ⊆ ℙ¹_K` to an abelian variety over `K` takes
the same value at all the points `[s : 1]`. -/
theorem overlap_const (B : PkgI3.AbVar K) (h : Ov K ⟶ B.X.left) (hh : h ≫ B.X.hom = overlapToBase K)
    (s t : Kˣ) : ovPt K s ≫ h = ovPt K t ≫ h := by
  letI : (B.X.left).Over (PK K) := ⟨B.X.hom⟩
  haveI : IsProper (B.X.left ↘ PK K) := B.proper
  haveI : B.X.left.IsSeparated := ⟨by
    rw [← terminal.comp_from B.X.hom]
    haveI : IsSeparated B.X.hom := inferInstanceAs (IsSeparated (B.X.left ↘ PK K))
    infer_instance⟩
  have hval : ∀ x, ValuationRing ((relativeLine (PK K)).presheaf.stalk x) :=
    Scheme.valuationRing_stalk (relativeLine (PK K) ↘ PK K)
  obtain ⟨E, hEo, hE⟩ := Scheme.exists_hom_of_valuationRing_stalk (base := PK K) hval (ξg ≫ h) (by
    change ξg ≫ h ≫ B.X.hom = _
    rw [hh, overlapToBase, ← Category.assoc, ξg_ι])
  have hEo' : E ≫ B.X.hom = relativeLine (PK K) ↘ PK K := hEo.comp_over
  have hagree : (relativeOverlap (PK K)).ι ≫ E = h := by
    apply ext_of_isDominant_of_isSeparated B.X.hom ?_ (ξg (K := K)) ?_
    · rw [Category.assoc, hEo', hh, overlapToBase]
    · rw [← Category.assoc, ξg_ι, hE]
  let Em : relativeLineOver K ⟶ B.X := Over.homMk E hEo'
  let pt : Kˣ → (𝟙_ (Over (PK K)) ⟶ relativeLineOver K) := fun s =>
    Over.homMk (ovPt K s ≫ (relativeOverlap (PK K)).ι) (by
      change (ovPt K s ≫ (relativeOverlap (PK K)).ι) ≫ relativeLine (PK K) ↘ PK K = 𝟙 _
      rw [Category.assoc, ← overlapToBase, ovPt_over])
  have := congrArg CommaMorphism.left (line_const B Em (pt s) (pt t))
  simp only [Over.comp_left, Over.homMk_left, Em, pt] at this
  rw [← hagree, ← Category.assoc, ← Category.assoc]
  simpa only [Category.assoc] using this

/-- The `K`-algebra structure of `Γ(𝔾_m)`. -/
@[reducible] def ovAlg : Algebra K Γ(Ov K, ⊤) :=
  ((overlapToBase K).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra

/-- The coordinate `u = X₀/X₁` of `𝔾_m`, a unit. -/
def uOv : Γ(Ov K, ⊤)ˣ :=
  ⟨scalingCoordinate K ⟨1⟩, scalingCoordinate K ⟨0⟩, scalingCoordinate_mul K ⟨1⟩ ⟨0⟩ (by decide),
    scalingCoordinate_mul K ⟨0⟩ ⟨1⟩ (by decide)⟩

/-- `𝔾_m ⊆ ℙ¹ → Spec K[x^{±1}]`, `x ↦ u`. -/
def mOv : Ov K ⟶ Spec (CommRingCat.of (TorusRing K 1)) :=
  letI := ovAlg (K := K)
  (Ov K).toSpecΓ ≫ Spec.map (CommRingCat.ofHom (torusLift (K := K) (fun _ => uOv (K := K))).toRingHom)

theorem ovPt_mOv (s : Kˣ) :
    ovPt K s ≫ mOv = Spec.map (CommRingCat.ofHom (torusLift (K := K) (R := K) (fun _ => s)).toRingHom) := by
  letI := ovAlg (K := K)
  rw [mOv, Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext1
  apply IsLocalization.ringHom_ext (Submonoid.powers (∏ i : Fin 1, MvPolynomial.X i :
    MvPolynomial (Fin 1) K))
  apply MvPolynomial.ringHom_ext
  · intro a
    have h1 : (ovPt K s).appTop ((overlapToBase K).appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a)) =
        (Scheme.ΓSpecIso (CommRingCat.of K)).inv a := by
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ovPt_over]; rfl
    simp only [RingHom.comp_apply, CommRingCat.hom_comp, CommRingCat.hom_ofHom, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe]
    rw [show (algebraMap (MvPolynomial (Fin 1) K) (TorusRing K 1)) (MvPolynomial.C a) =
      algebraMap K (TorusRing K 1) a from rfl, AlgHom.commutes, AlgHom.commutes]
    change (Scheme.ΓSpecIso (CommRingCat.of K)).hom ((ovPt K s).appTop
      ((overlapToBase K).appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a))) = a
    rw [h1, ← CommRingCat.comp_apply, Iso.inv_hom_id]; rfl
  · intro i
    have hi : (algebraMap (MvPolynomial (Fin 1) K) (TorusRing K 1)) (MvPolynomial.X i) =
        ((tUniv 1 i : (TorusRing K 1)ˣ) : TorusRing K 1) := by simp [tUniv]
    simp only [RingHom.comp_apply, CommRingCat.hom_comp, CommRingCat.hom_ofHom, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe]
    rw [hi, torusLift_tUniv, torusLift_tUniv]
    change (Scheme.ΓSpecIso (CommRingCat.of K)).hom ((ovPt K s).appTop (scalingCoordinate K ⟨1⟩)) = s
    rw [ovPt_coordinate, secK, ← CommRingCat.comp_apply, Iso.inv_hom_id]; rfl

theorem mOv_over : mOv (K := K) ≫ (algPt K (TorusRing K 1)).hom = overlapToBase K := by
  letI := ovAlg (K := K)
  change ((Ov K).toSpecΓ ≫ Spec.map _) ≫ Spec.map (CommRingCat.ofHom (algebraMap K (TorusRing K 1))) = _
  rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [show ((torusLift (K := K) (fun _ => uOv (K := K))).toRingHom.comp (algebraMap K (TorusRing K 1))) =
    algebraMap K Γ(Ov K, ⊤) from (torusLift (K := K) (fun _ => uOv (K := K))).comp_algebraMap]
  change (Ov K).toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (overlapToBase K).appTop) = _
  rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- **Rigidity for `𝔾_m`, torus form**: a morphism `Spec K[x^{±1}] → B` to an abelian variety over a field `K`
takes the same value at all `K`-points `x ↦ s`. -/
theorem torus1_const (B : PkgI3.AbVar K) (g : algPt K (TorusRing K 1) ⟶ B.X) (s : Kˣ) :
    algPtMap (torusLift (K := K) (R := K) (fun _ => s)) ≫ g =
      algPtMap (torusLift (K := K) (R := K) (fun _ => (1 : Kˣ))) ≫ g := by
  have hh : (mOv (K := K) ≫ g.left) ≫ B.X.hom = overlapToBase K := by
    rw [Category.assoc, Over.w g, mOv_over]
  have := overlap_const B (mOv ≫ g.left) hh s 1
  apply Over.OverMorphism.ext
  simp only [Over.comp_left]
  rw [← Category.assoc, ovPt_mOv, ← Category.assoc, ovPt_mOv] at this
  exact this

end Rig


section TorusR

set_option maxHeartbeats 300000

variable {K : Type} [Field K]

theorem algPtMap_comp {R S T : Type} [CommRing R] [Algebra K R] [CommRing S] [Algebra K S] [CommRing T]
    [Algebra K T] (f : R →ₐ[K] S) (g : S →ₐ[K] T) :
    algPtMap (k := K) g ≫ algPtMap f = algPtMap (g.comp f) := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- One coordinate of a torus point can be moved to `1`. -/
theorem torus_update_const (B : PkgI3.AbVar K) {r : ℕ} (g : algPt K (TorusRing K r) ⟶ B.X)
    (c : Fin r → Kˣ) (j : Fin r) (s : Kˣ) :
    algPtMap (torusLift (K := K) (R := K) (Function.update c j s)) ≫ g =
      algPtMap (torusLift (K := K) (R := K) (Function.update c j 1)) ≫ g := by
  let φ : TorusRing K r →ₐ[K] TorusRing K 1 := torusLift (K := K)
    (fun i => if i = j then tUniv 1 0 else Units.map (algebraMap K (TorusRing K 1) : K →* TorusRing K 1) (c i))
  have key : ∀ s' : Kˣ, (torusLift (K := K) (R := K) (fun _ => s')).comp φ =
      torusLift (K := K) (R := K) (Function.update c j s') := by
    intro s'
    apply algHom_ext_torus
    intro i
    rw [AlgHom.comp_apply, torusLift_tUniv, torusLift_tUniv]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, torusLift_tUniv, Function.update_self]
    · rw [if_neg hij, Function.update_of_ne hij]
      change (torusLift (K := K) (R := K) (fun _ => s')) (algebraMap K (TorusRing K 1) (c i : K)) = (c i : K)
      rw [AlgHom.commutes]; rfl
  have h := torus1_const B (algPtMap φ ≫ g) s
  rw [← Category.assoc, ← Category.assoc, algPtMap_comp, algPtMap_comp, key, key] at h
  exact h

/-- **Rigidity for `𝔾_m^r`**: a morphism `Spec K[x₁^{±1}, …, x_r^{±1}] → B` to an abelian variety takes the same
value at all `K`-points. -/
theorem torusR_const (B : PkgI3.AbVar K) {r : ℕ} (g : algPt K (TorusRing K r) ⟶ B.X) (t : Fin r → Kˣ) :
    algPtMap (torusLift (K := K) (R := K) t) ≫ g =
      algPtMap (torusLift (K := K) (R := K) (fun _ => (1 : Kˣ))) ≫ g := by
  classical
  have hs : ∀ s : Finset (Fin r), algPtMap (torusLift (K := K) (R := K)
      (fun i => if i ∈ s then t i else 1)) ≫ g =
      algPtMap (torusLift (K := K) (R := K) (fun _ => (1 : Kˣ))) ≫ g := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      have e1 : (fun i => if i ∈ insert j s then t i else 1) =
          Function.update (fun i => if i ∈ s then t i else 1) j (t j) := by
        funext i
        by_cases hij : i = j
        · subst hij; simp
        · simp [hij, Function.update_of_ne hij]
      have e2 : (fun i => if i ∈ s then t i else (1 : Kˣ)) =
          Function.update (fun i => if i ∈ s then t i else 1) j 1 := by
        funext i
        by_cases hij : i = j
        · subst hij; simp [hj]
        · simp [Function.update_of_ne hij]
      rw [e1, torus_update_const, ← e2, ih]
  have := hs Finset.univ
  simpa using this

end TorusR

section KbarKI

set_option synthInstance.maxHeartbeats 400000

variable {k : Type} [Field k] {U : Over (Spec (CommRingCat.of k))} [GrpObj U]
  {B' : PkgI3.AbVar (AlgebraicClosure k)}

/-- The base change of an abelian variety along a field extension `ρ : K → L`. -/
def abVarBC {K L : Type} [Field K] [Field L] (ρ : K →+* L) (B : PkgI3.AbVar K) : PkgI3.AbVar L :=
  letI := B.grp
  haveI := B.proper
  haveI := B.smooth
  haveI := B.geomInt
  { X := (Over.pullback (sφ ρ)).obj B.X
    grp := Functor.grpObjObj
    proper := by change IsProper (pullback.snd B.X.hom (sφ ρ)); infer_instance
    smooth := by change Smooth (pullback.snd B.X.hom (sφ ρ)); infer_instance
    geomInt := by change GeometricallyIntegral (pullback.snd B.X.hom (sφ ρ)); infer_instance }

/-- **Rigidity, raw form**: for a field `L` with `ρ : k̄ → L` and a `U`-point `W` of the torus
`Spec L[x^{±1}]` (structure through `ρ`), `π'(W, ρ)` takes the same value at all `L`-points of the torus. -/
theorem rig_raw (π' : (Over.pullback (sφ (φbar k))).obj U ⟶ B'.X) (L : Type) [Field L]
    (ρ : AlgebraicClosure k →+* L) (r : ℕ) (W : Spec (CommRingCat.of (TorusRing L r)) ⟶ U.left)
    (hW : W ≫ U.hom = Spec.map (CommRingCat.ofHom ((algebraMap L (TorusRing L r)).comp ρ)) ≫ sφ (φbar k))
    (t : Fin r → Lˣ) :
    Spec.map (CommRingCat.ofHom (torusLift (K := L) (R := L) t).toRingHom) ≫
        (pullback.lift W _ hW ≫ π'.left) =
      Spec.map (CommRingCat.ofHom (torusLift (K := L) (R := L) (fun _ => (1 : Lˣ))).toRingHom) ≫
        (pullback.lift W _ hW ≫ π'.left) := by
  letI := B'.grp
  letI Ib0 : Algebra (AlgebraicClosure k) (TorusRing L r) := algK ρ (TorusRing L r)
  letI : GrpObj ((Over.pullback (sφ ρ)).obj B'.X) := Functor.grpObjObj
  let g : algPt (AlgebraicClosure k) (TorusRing L r) ⟶ B'.X :=
    Over.homMk (pullback.lift W _ hW ≫ π'.left) (by
      change (pullback.lift W _ hW ≫ π'.left) ≫ B'.X.hom = _
      rw [Category.assoc, Over.w π']
      exact pullback.lift_snd _ _ _)
  let g' := (Φ ρ B'.X (TorusRing L r)).symm g
  have hc := torusR_const (abVarBC ρ B') g' t
  have h2 := congrArg (Φ ρ B'.X L) hc
  rw [Φ_natural, Φ_natural, MulEquiv.apply_symm_apply] at h2
  exact congrArg (fun z => Over.Hom.left z) h2


/-- The unit of `U_{k̄}` at a `k̄`-algebra `L`, on `U`. -/
theorem one_left_fst (L : Type) [CommRing L] [Algebra (AlgebraicClosure k) L] :
    letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
    (1 : algPt (AlgebraicClosure k) L ⟶ (Over.pullback (sφ (φbar k))).obj U).left ≫
        pullback.fst U.hom (sφ (φbar k)) =
      (algPt (AlgebraicClosure k) L).hom ≫ sφ (φbar k) ≫ (η[U] : 𝟙_ _ ⟶ U).left := by
  letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
  rw [Hom.one_def, Over.comp_left, Category.assoc, CToPrinted.unit_bc_fst]
  rfl

/-- `η` of `U_{k̄}` composed with a point `ρ`, as a lift. -/
theorem lift_unit (L : Type) [CommRing L] (ρ : CommRingCat.of (AlgebraicClosure k) ⟶ CommRingCat.of L)
    (x : Spec (CommRingCat.of L) ⟶ U.left) (hx : x = Spec.map ρ ≫ sφ (φbar k) ≫ (η[U] : 𝟙_ _ ⟶ U).left)
    (h : x ≫ U.hom = Spec.map ρ ≫ sφ (φbar k)) :
    letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
    pullback.lift x (Spec.map ρ) h =
      Spec.map ρ ≫ (η[(Over.pullback (sφ (φbar k))).obj U] : 𝟙_ _ ⟶ _).left := by
  letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
  apply pullback.hom_ext
  · rw [pullback.lift_fst, Category.assoc, CToPrinted.unit_bc_fst, hx]
  · rw [pullback.lift_snd, Category.assoc]
    have := Over.w (η[(Over.pullback (sφ (φbar k))).obj U] : 𝟙_ _ ⟶ _)
    change _ ≫ pullback.snd U.hom (sφ (φbar k)) = 𝟙 _ at this
    rw [this, Category.comp_id]

/-- **Torus kernels are transport-stable**: a point of the torus `ker π'` for the `k̄`-structure `ra` on `L` maps to
the unit under `π'` for any other `k̄`-structure `rb` with the same restriction to `k` (rigidity). -/
theorem torus_kernel_transfer (π' : (Over.pullback (sφ (φbar k))).obj U ⟶ B'.X)
    (hπ : letI := B'.grp; letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      IsMonHom π') (r : ℕ)
    (e : letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
      (Fin r → Rˣ) →* (algPt (AlgebraicClosure k) R ⟶ (Over.pullback (sφ (φbar k))).obj U))
    (he_nat : ∀ (R S : Type) [CommRing R] [Algebra (AlgebraicClosure k) R] [CommRing S]
      [Algebra (AlgebraicClosure k) S] (f : R →ₐ[AlgebraicClosure k] S) (t : Fin r → Rˣ),
      e S (fun i => Units.map (f : R →* S) (t i)) = algPtMap f ≫ e R t)
    (L : Type) [Field L] (ra rb : AlgebraicClosure k →+* L) (hab : ra.comp (φbar k) = rb.comp (φbar k))
    (t : Fin r → Lˣ) :
    letI := ra.toAlgebra
    ∀ (hcond : ((e L t).left ≫ pullback.fst U.hom (sφ (φbar k))) ≫ U.hom =
        Spec.map (CommRingCat.ofHom rb) ≫ sφ (φbar k)),
    pullback.lift ((e L t).left ≫ pullback.fst U.hom (sφ (φbar k))) _ hcond ≫ π'.left =
      Spec.map (CommRingCat.ofHom rb) ≫ (η[B'.X] : 𝟙_ _ ⟶ B'.X).left := by
  letI Ia := ra.toAlgebra
  intro hcond
  letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
  letI := B'.grp
  haveI := hπ
  letI Ia0 : Algebra (AlgebraicClosure k) (TorusRing L r) := algK ra (TorusRing L r)
  let fl : (Fin r → Lˣ) → (TorusRing L r →ₐ[AlgebraicClosure k] L) := fun t' =>
    { (torusLift (K := L) (R := L) t').toRingHom with
      commutes' := fun x => (torusLift (K := L) (R := L) t').commutes (ra x) }
  have hnat : ∀ t' : Fin r → Lˣ, e L t' = algPtMap (fl t') ≫ e (TorusRing L r) (tUniv r) := by
    intro t'
    have := he_nat (TorusRing L r) L (fl t') (tUniv r)
    have hmap : (fun i => Units.map ((fl t' : TorusRing L r →ₐ[AlgebraicClosure k] L) :
        TorusRing L r →* L) (tUniv r i)) = t' := by
      funext i; ext; exact torusLift_tUniv t' i
    rwa [hmap] at this
  let W := (e (TorusRing L r) (tUniv r)).left ≫ pullback.fst U.hom (sφ (φbar k))
  have hW : W ≫ U.hom =
      Spec.map (CommRingCat.ofHom ((algebraMap L (TorusRing L r)).comp rb)) ≫ sφ (φbar k) := by
    simp only [W, Category.assoc]
    have hw : (e (TorusRing L r) (tUniv r)).left ≫ pullback.snd U.hom (sφ (φbar k)) =
        (algPt (AlgebraicClosure k) (TorusRing L r)).hom := Over.w (e (TorusRing L r) (tUniv r))
    rw [pullback.condition, ← Category.assoc, hw]
    change Spec.map (CommRingCat.ofHom ((algebraMap L (TorusRing L r)).comp ra)) ≫ sφ (φbar k) = _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      RingHom.comp_assoc, RingHom.comp_assoc, hab]
  have hlift : ∀ (t' : Fin r → Lˣ) (h' : ((e L t').left ≫ pullback.fst U.hom (sφ (φbar k))) ≫ U.hom =
      Spec.map (CommRingCat.ofHom rb) ≫ sφ (φbar k)),
      pullback.lift ((e L t').left ≫ pullback.fst U.hom (sφ (φbar k))) _ h' =
        Spec.map (CommRingCat.ofHom (torusLift (K := L) (R := L) t').toRingHom) ≫ pullback.lift W _ hW := by
    intro t' h'
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, hnat t']
      rfl
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp]
      congr 2
      ext x
      exact ((torusLift (K := L) (R := L) t').commutes (rb x)).symm
  have h1 : e L (fun _ => (1 : Lˣ)) = 1 := map_one (e L)
  have hc1 : ((e L (fun _ => (1 : Lˣ))).left ≫ pullback.fst U.hom (sφ (φbar k))) ≫ U.hom =
      Spec.map (CommRingCat.ofHom rb) ≫ sφ (φbar k) := by
    have hw : (e L (fun _ => (1 : Lˣ))).left ≫ pullback.snd U.hom (sφ (φbar k)) =
        Spec.map (CommRingCat.ofHom ra) := Over.w (e L _)
    rw [Category.assoc, pullback.condition, ← Category.assoc, hw]
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hab]
  rw [hlift t hcond, Category.assoc, rig_raw π' L rb r W hW t, ← Category.assoc, ← hlift _ hc1]
  have hx : (e L (fun _ => (1 : Lˣ))).left ≫ pullback.fst U.hom (sφ (φbar k)) =
      Spec.map (CommRingCat.ofHom rb) ≫ sφ (φbar k) ≫ (η[U] : 𝟙_ _ ⟶ U).left := by
    rw [h1, one_left_fst, ← Category.assoc, ← Category.assoc]
    congr 1
    change Spec.map (CommRingCat.ofHom ra) ≫ sφ (φbar k) = _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hab]
  rw [lift_unit L (CommRingCat.ofHom rb) _ hx hc1, Category.assoc, ← Over.comp_left, IsMonHom.one_hom]

theorem overMk_inv_mul_left {X S : Scheme.{0}} {f g : X ⟶ S} (hfg : f = g) {V : Over S} [GrpObj V]
    (a b : X ⟶ V.left) (ha : a ≫ V.hom = f) (hb : b ≫ V.hom = f) :
    ((Over.homMk a ha : Over.mk f ⟶ V)⁻¹ * Over.homMk b hb).left =
      ((Over.homMk a (ha.trans hfg) : Over.mk g ⟶ V)⁻¹ * Over.homMk b (hb.trans hfg)).left := by
  subst hfg; rfl

theorem homEquiv_left {S S' : Scheme.{0}} (g : S' ⟶ S) (X : Over S') (V : Over S)
    (p : (Over.map g).obj X ⟶ V) :
    ((Over.mapPullbackAdj g).homEquiv X V p).left =
      pullback.lift p.left X.hom (by simpa using Over.w p) := by
  apply pullback.hom_ext
  · simp [Adjunction.homEquiv_unit]
  · simp [Adjunction.homEquiv_unit]

theorem homEquiv_inv {K K' : Type} [Field K] [Field K'] (φ : K →+* K')
    (X : Over (Spec (CommRingCat.of K'))) (V : Over (Spec (CommRingCat.of K))) [GrpObj V]
    (p : (Over.map (sφ φ)).obj X ⟶ V) :
    letI : GrpObj ((Over.pullback (sφ φ)).obj V) := Functor.grpObjObj
    (Over.mapPullbackAdj (sφ φ)).homEquiv X V p⁻¹ = ((Over.mapPullbackAdj (sφ φ)).homEquiv X V p)⁻¹ := by
  letI : GrpObj ((Over.pullback (sφ φ)).obj V) := Functor.grpObjObj
  let m : ((Over.map (sφ φ)).obj X ⟶ V) →* (X ⟶ (Over.pullback (sφ φ)).obj V) :=
    MonoidHom.mk' ((Over.mapPullbackAdj (sφ φ)).homEquiv X V) (homEquiv_mul' φ X V)
  exact map_inv m p

/-- **Kernel pairs are transport-stable** (`k̄`-level form of `KI`): if two `U`-points `u, v` over a field `L` have
the same image under `π'` for the `k̄`-structure `ra`, they have the same image for every `rb` with the same
restriction to `k`. -/
theorem kbar_KI (π' : (Over.pullback (sφ (φbar k))).obj U ⟶ B'.X)
    (hπ : letI := B'.grp; letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      IsMonHom π') (r : ℕ)
    (e : letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
      (Fin r → Rˣ) →* (algPt (AlgebraicClosure k) R ⟶ (Over.pullback (sφ (φbar k))).obj U))
    (he_ker : letI := B'.grp; letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R]
      (u : algPt (AlgebraicClosure k) R ⟶ (Over.pullback (sφ (φbar k))).obj U),
      u ≫ π' = 1 ↔ u ∈ (e R).range)
    (he_nat : ∀ (R S : Type) [CommRing R] [Algebra (AlgebraicClosure k) R] [CommRing S]
      [Algebra (AlgebraicClosure k) S] (f : R →ₐ[AlgebraicClosure k] S) (t : Fin r → Rˣ),
      e S (fun i => Units.map (f : R →* S) (t i)) = algPtMap f ≫ e R t)
    (L : Type) [Field L] (ra rb : AlgebraicClosure k →+* L) (hab : ra.comp (φbar k) = rb.comp (φbar k))
    (u v : Spec (CommRingCat.of L) ⟶ U.left)
    (hu : u ≫ U.hom = Spec.map (CommRingCat.ofHom ra) ≫ sφ (φbar k))
    (hv : v ≫ U.hom = Spec.map (CommRingCat.ofHom ra) ≫ sφ (φbar k))
    (hb : Spec.map (CommRingCat.ofHom ra) ≫ sφ (φbar k) = Spec.map (CommRingCat.ofHom rb) ≫ sφ (φbar k))
    (h : pullback.lift u _ hu ≫ π'.left = pullback.lift v _ hv ≫ π'.left) :
    pullback.lift u _ (hu.trans hb) ≫ π'.left = pullback.lift v _ (hv.trans hb) ≫ π'.left := by
  letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
  letI := B'.grp
  haveI := hπ
  let Φa := (Over.mapPullbackAdj (sφ (φbar k))).homEquiv (Over.mk (Spec.map (CommRingCat.ofHom ra))) U
  let Φb := (Over.mapPullbackAdj (sφ (φbar k))).homEquiv (Over.mk (Spec.map (CommRingCat.ofHom rb))) U
  let ua : Over.mk (Spec.map (CommRingCat.ofHom ra) ≫ sφ (φbar k)) ⟶ U := Over.homMk u hu
  let va : Over.mk (Spec.map (CommRingCat.ofHom ra) ≫ sφ (φbar k)) ⟶ U := Over.homMk v hv
  let ub : Over.mk (Spec.map (CommRingCat.ofHom rb) ≫ sφ (φbar k)) ⟶ U := Over.homMk u (hu.trans hb)
  let vb : Over.mk (Spec.map (CommRingCat.ofHom rb) ≫ sφ (φbar k)) ⟶ U := Over.homMk v (hv.trans hb)
  -- a-side
  have ha1 : Φa ua ≫ π' = Φa va ≫ π' := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, homEquiv_left, Φa]
    exact h
  have ha2 : Φa (ua⁻¹ * va) ≫ π' = 1 := by
    rw [homEquiv_mul', homEquiv_inv, MonObj.mul_comp, GrpObj.inv_comp, ha1, _root_.inv_mul_cancel]
  letI Ia := ra.toAlgebra
  obtain ⟨t, ht⟩ := (he_ker L (Φa (ua⁻¹ * va))).mp ha2
  have hraw : (e L t).left ≫ pullback.fst U.hom (sφ (φbar k)) = (ua⁻¹ * va).left := by
    rw [ht]
    change (Φa (ua⁻¹ * va)).left ≫ _ = _
    rw [homEquiv_left, pullback.lift_fst]
  -- transfer
  have htr := torus_kernel_transfer π' hπ r e he_nat L ra rb hab t (by
    rw [hraw, Over.w (ua⁻¹ * va)]; exact hb)
  -- b-side
  have hrawb : (ua⁻¹ * va).left = (ub⁻¹ * vb).left := overMk_inv_mul_left hb u v hu hv
  have hb2 : Φb (ub⁻¹ * vb) ≫ π' = 1 := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, homEquiv_left]
    show pullback.lift (ub⁻¹ * vb).left (Spec.map (CommRingCat.ofHom rb)) (Over.w (ub⁻¹ * vb)) ≫ π'.left = _
    have e1 : pullback.lift (ub⁻¹ * vb).left (Spec.map (CommRingCat.ofHom rb)) (Over.w (ub⁻¹ * vb)) =
        pullback.lift ((e L t).left ≫ pullback.fst U.hom (sφ (φbar k))) (Spec.map (CommRingCat.ofHom rb))
          (by rw [hraw, Over.w (ua⁻¹ * va)]; exact hb) := by
      congr 1; rw [hraw, hrawb]
    rw [e1, htr, Hom.one_def, Over.comp_left]
    rfl
  have hb3 : Φb ub ≫ π' = Φb vb ≫ π' := by
    rw [homEquiv_mul', homEquiv_inv, MonObj.mul_comp, GrpObj.inv_comp] at hb2
    exact (inv_mul_eq_one.mp hb2)
  have := congrArg (fun z => Over.Hom.left z) hb3
  simp only [Φb, Over.comp_left, homEquiv_left] at this
  exact this

end KbarKI

section KI1

set_option synthInstance.maxHeartbeats 400000

variable {k : Type} [Field k] {U : Over (Spec (CommRingCat.of k))} [GrpObj U]
  {B' : PkgI3.AbVar (AlgebraicClosure k)}
  {k₁ : Type} [Field k₁] [Algebra k k₁] [Algebra k₁ (AlgebraicClosure k)]
  [IsScalarTower k k₁ (AlgebraicClosure k)]

/-- `Spec k₁ → Spec k`. -/
abbrev qq (k k₁ : Type) [Field k] [Field k₁] [Algebra k k₁] :
    Spec (CommRingCat.of k₁) ⟶ Spec (CommRingCat.of k) := Spec.map (CommRingCat.ofHom (algebraMap k k₁))

/-- `Spec k̄ → Spec k₁`. -/
abbrev q₂ (k k₁ : Type) [Field k] [Field k₁] [Algebra k₁ (AlgebraicClosure k)] :
    Spec (CommRingCat.of (AlgebraicClosure k)) ⟶ Spec (CommRingCat.of k₁) :=
  Spec.map (CommRingCat.ofHom (algebraMap k₁ (AlgebraicClosure k)))

omit [GrpObj U] in
theorem q₂_qq : q₂ k k₁ ≫ qq k k₁ = sφ (φbar k) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

/-- `U_{k̄} → U_{k₁}`. -/
abbrev rr (U : Over (Spec (CommRingCat.of k))) (k₁ : Type) [Field k₁] [Algebra k k₁]
    [Algebra k₁ (AlgebraicClosure k)] [IsScalarTower k k₁ (AlgebraicClosure k)] :
    pullback U.hom (sφ (φbar k)) ⟶ pullback U.hom (qq k k₁) :=
  pullback.map U.hom (sφ (φbar k)) U.hom (qq k k₁) (𝟙 _) (q₂ k k₁) (𝟙 _) (by simp)
    (by rw [Category.comp_id, q₂_qq])

omit [GrpObj U] in
theorem exists_ext_point [Algebra.IsAlgebraic k₁ (AlgebraicClosure k)] (L : Type) [Field L] [IsAlgClosed L]
    (a : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k₁)) :
    ∃ ra : AlgebraicClosure k →+* L, Spec.map (CommRingCat.ofHom ra) ≫ q₂ k k₁ = a := by
  let a' : k₁ →+* L := (Spec.preimage a).hom
  letI : Algebra k₁ L := a'.toAlgebra
  refine ⟨(IsAlgClosed.lift (R := k₁) (S := AlgebraicClosure k) (M := L)).toRingHom, ?_⟩
  rw [← Spec.map_comp]
  conv_rhs => rw [← Spec.map_preimage a]
  congr 1
  ext x
  exact (IsAlgClosed.lift (R := k₁) (S := AlgebraicClosure k) (M := L)).commutes x

/-- `KI` at points with values in an algebraically closed field. -/
theorem algclosed_KI [Algebra.IsAlgebraic k₁ (AlgebraicClosure k)]
    (π' : (Over.pullback (sφ (φbar k))).obj U ⟶ B'.X)
    (hπ : letI := B'.grp; letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      IsMonHom π') (r : ℕ)
    (e : letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
      (Fin r → Rˣ) →* (algPt (AlgebraicClosure k) R ⟶ (Over.pullback (sφ (φbar k))).obj U))
    (he_ker : letI := B'.grp; letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R]
      (u : algPt (AlgebraicClosure k) R ⟶ (Over.pullback (sφ (φbar k))).obj U),
      u ≫ π' = 1 ↔ u ∈ (e R).range)
    (he_nat : ∀ (R S : Type) [CommRing R] [Algebra (AlgebraicClosure k) R] [CommRing S]
      [Algebra (AlgebraicClosure k) S] (f : R →ₐ[AlgebraicClosure k] S) (t : Fin r → Rˣ),
      e S (fun i => Units.map (f : R →* S) (t i)) = algPtMap f ≫ e R t)
    (X₁ : Over (Spec (CommRingCat.of k₁))) (π₁ : (Over.pullback (qq k k₁)).obj U ⟶ X₁)
    (c : B'.X.left ⟶ X₁.left) (hc : IsPullback c B'.X.hom X₁.hom (q₂ k k₁))
    (hcompat : π'.left ≫ c = rr U k₁ ≫ π₁.left)
    (L : Type) [Field L] [IsAlgClosed L] (u v : Spec (CommRingCat.of L) ⟶ U.left)
    (a b : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k₁))
    (hu : u ≫ U.hom = a ≫ qq k k₁) (hv : v ≫ U.hom = a ≫ qq k k₁) (hb : a ≫ qq k k₁ = b ≫ qq k k₁)
    (h : pullback.lift u a hu ≫ π₁.left = pullback.lift v a hv ≫ π₁.left) :
    pullback.lift u b (hu.trans hb) ≫ π₁.left = pullback.lift v b (hv.trans hb) ≫ π₁.left := by
  obtain ⟨ra, hra⟩ := exists_ext_point (k := k) (k₁ := k₁) L a
  obtain ⟨rb, hrb⟩ := exists_ext_point (k := k) (k₁ := k₁) L b
  have hua : u ≫ U.hom = Spec.map (CommRingCat.ofHom ra) ≫ sφ (φbar k) := by
    rw [hu, ← hra, Category.assoc, q₂_qq]
  have hva : v ≫ U.hom = Spec.map (CommRingCat.ofHom ra) ≫ sφ (φbar k) := by
    rw [hv, ← hra, Category.assoc, q₂_qq]
  have hbb : Spec.map (CommRingCat.ofHom ra) ≫ sφ (φbar k) = Spec.map (CommRingCat.ofHom rb) ≫ sφ (φbar k) := by
    rw [← q₂_qq (k₁ := k₁), ← Category.assoc, hra, hb, ← hrb, Category.assoc]
  have hab : ra.comp (φbar k) = rb.comp (φbar k) := by
    have := hbb
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp] at this
    have := Spec.map_injective this
    exact congrArg CommRingCat.Hom.hom this
  have hlift : ∀ (w : Spec (CommRingCat.of L) ⟶ U.left) (ρ : AlgebraicClosure k →+* L)
      (x : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k₁)) (hρ : Spec.map (CommRingCat.ofHom ρ) ≫ q₂ k k₁ = x)
      (hw : w ≫ U.hom = x ≫ qq k k₁) (hw' : w ≫ U.hom = Spec.map (CommRingCat.ofHom ρ) ≫ sφ (φbar k)),
      pullback.lift w x hw ≫ π₁.left = (pullback.lift w _ hw' ≫ π'.left) ≫ c := by
    intro w ρ x hρ hw hw'
    rw [Category.assoc, hcompat, ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · simp
    · simp [hρ]
  have hst : ∀ (w : Spec (CommRingCat.of L) ⟶ U.left) (ρ : AlgebraicClosure k →+* L)
      (hw' : w ≫ U.hom = Spec.map (CommRingCat.ofHom ρ) ≫ sφ (φbar k)),
      (pullback.lift w _ hw' ≫ π'.left) ≫ B'.X.hom = Spec.map (CommRingCat.ofHom ρ) := by
    intro w ρ hw'
    rw [Category.assoc, Over.w π']
    exact pullback.lift_snd _ _ _
  have hk : pullback.lift u _ hua ≫ π'.left = pullback.lift v _ hva ≫ π'.left := by
    apply hc.hom_ext
    · rw [← hlift u ra a hra hu hua, ← hlift v ra a hra hv hva, h]
    · rw [hst, hst]
  have hk2 := kbar_KI π' hπ r e he_ker he_nat L ra rb hab u v hua hva hbb hk
  rw [hlift u rb b hrb (hu.trans hb) (hua.trans hbb), hlift v rb b hrb (hv.trans hb) (hva.trans hbb), hk2]

theorem fpqc_specField (L M : Type) [Field L] [Field M] [Algebra L M] :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap L M))) ∧ Surjective (Spec.map (CommRingCat.ofHom (algebraMap L M))) := by
  have h := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap L M))).mpr
    ((RingHom.faithfullyFlat_algebraMap_iff).mpr inferInstance)
  exact h

theorem lift_comp_left {X Y S Z' Z : Scheme.{0}} (f : X ⟶ S) (g : Y ⟶ S) (ρ : Z' ⟶ Z) (x : Z ⟶ X) (y : Z ⟶ Y)
    (h : x ≫ f = y ≫ g) :
    pullback.lift (ρ ≫ x) (ρ ≫ y) (by rw [Category.assoc, Category.assoc, h]) = ρ ≫ pullback.lift x y h := by
  apply pullback.hom_ext <;> simp

/-- `KI` at points with values in any field (pass to an algebraic closure). -/
theorem field_KI [Algebra.IsAlgebraic k₁ (AlgebraicClosure k)]
    (π' : (Over.pullback (sφ (φbar k))).obj U ⟶ B'.X)
    (hπ : letI := B'.grp; letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      IsMonHom π') (r : ℕ)
    (e : letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
      (Fin r → Rˣ) →* (algPt (AlgebraicClosure k) R ⟶ (Over.pullback (sφ (φbar k))).obj U))
    (he_ker : letI := B'.grp; letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R]
      (u : algPt (AlgebraicClosure k) R ⟶ (Over.pullback (sφ (φbar k))).obj U),
      u ≫ π' = 1 ↔ u ∈ (e R).range)
    (he_nat : ∀ (R S : Type) [CommRing R] [Algebra (AlgebraicClosure k) R] [CommRing S]
      [Algebra (AlgebraicClosure k) S] (f : R →ₐ[AlgebraicClosure k] S) (t : Fin r → Rˣ),
      e S (fun i => Units.map (f : R →* S) (t i)) = algPtMap f ≫ e R t)
    (X₁ : Over (Spec (CommRingCat.of k₁))) (π₁ : (Over.pullback (qq k k₁)).obj U ⟶ X₁)
    (c : B'.X.left ⟶ X₁.left) (hc : IsPullback c B'.X.hom X₁.hom (q₂ k k₁))
    (hcompat : π'.left ≫ c = rr U k₁ ≫ π₁.left)
    (L : Type) [Field L] (u v : Spec (CommRingCat.of L) ⟶ U.left)
    (a b : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k₁))
    (hu : u ≫ U.hom = a ≫ qq k k₁) (hv : v ≫ U.hom = a ≫ qq k k₁) (hb : a ≫ qq k k₁ = b ≫ qq k k₁)
    (h : pullback.lift u a hu ≫ π₁.left = pullback.lift v a hv ≫ π₁.left) :
    pullback.lift u b (hu.trans hb) ≫ π₁.left = pullback.lift v b (hv.trans hb) ≫ π₁.left := by
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure L)))
  obtain ⟨hfl, hsu⟩ := fpqc_specField L (AlgebraicClosure L)
  haveI : Flat ρ := hfl
  haveI : Surjective ρ := hsu
  haveI : QuasiCompact ρ := inferInstance
  rw [← cancel_epi ρ, ← Category.assoc, ← Category.assoc,
    ← lift_comp_left U.hom (qq k k₁) ρ u b (hu.trans hb), ← lift_comp_left U.hom (qq k k₁) ρ v b (hv.trans hb)]
  refine algclosed_KI π' hπ r e he_ker he_nat X₁ π₁ c hc hcompat (AlgebraicClosure L) (ρ ≫ u) (ρ ≫ v)
    (ρ ≫ a) (ρ ≫ b) (by rw [Category.assoc, hu, ← Category.assoc])
    (by rw [Category.assoc, hv, ← Category.assoc]) (by rw [Category.assoc, hb, ← Category.assoc]) ?_
  rw [lift_comp_left U.hom (qq k k₁) ρ u a hu, lift_comp_left U.hom (qq k k₁) ρ v a hv, Category.assoc,
    Category.assoc, h]

/-- **`KI` for `π₁`**, from the field case, on a smooth (hence reduced) universal source. -/
theorem KI_of [Algebra.IsAlgebraic k₁ (AlgebraicClosure k)]
    (π' : (Over.pullback (sφ (φbar k))).obj U ⟶ B'.X)
    (hπ : letI := B'.grp; letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      IsMonHom π') (r : ℕ)
    (e : letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
      (Fin r → Rˣ) →* (algPt (AlgebraicClosure k) R ⟶ (Over.pullback (sφ (φbar k))).obj U))
    (he_ker : letI := B'.grp; letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R]
      (u : algPt (AlgebraicClosure k) R ⟶ (Over.pullback (sφ (φbar k))).obj U),
      u ≫ π' = 1 ↔ u ∈ (e R).range)
    (he_nat : ∀ (R S : Type) [CommRing R] [Algebra (AlgebraicClosure k) R] [CommRing S]
      [Algebra (AlgebraicClosure k) S] (f : R →ₐ[AlgebraicClosure k] S) (t : Fin r → Rˣ),
      e S (fun i => Units.map (f : R →* S) (t i)) = algPtMap f ≫ e R t)
    (X₁ : Over (Spec (CommRingCat.of k₁))) (π₁ : (Over.pullback (qq k k₁)).obj U ⟶ X₁)
    (c : B'.X.left ⟶ X₁.left) (hc : IsPullback c B'.X.hom X₁.hom (q₂ k k₁))
    (hcompat : π'.left ≫ c = rr U k₁ ≫ π₁.left)
    [Smooth π₁.left] [Smooth U.hom] [Smooth (qq k k₁)] [IsSeparated X₁.hom] :
    KI (qq k k₁) π₁ := by
  intro Z u v a b hu hv hb h
  -- the universal source
  let W := pullback U.hom (qq k k₁)
  let Rel := pullback π₁.left π₁.left
  let aR : Rel ⟶ Spec (CommRingCat.of k₁) := pullback.fst π₁.left π₁.left ≫ pullback.snd U.hom (qq k k₁)
  let Z₀ := pullback (aR ≫ qq k k₁) (qq k k₁)
  have haR : pullback.snd π₁.left π₁.left ≫ pullback.snd U.hom (qq k k₁) = aR := by
    have := congrArg (· ≫ X₁.hom) (pullback.condition (f := π₁.left) (g := π₁.left))
    simp only [Category.assoc, w_π₁] at this
    exact this.symm
  let u₀ : Z₀ ⟶ U.left := pullback.fst _ _ ≫ pullback.fst π₁.left π₁.left ≫ pullback.fst U.hom (qq k k₁)
  let v₀ : Z₀ ⟶ U.left := pullback.fst _ _ ≫ pullback.snd π₁.left π₁.left ≫ pullback.fst U.hom (qq k k₁)
  let a₀ : Z₀ ⟶ Spec (CommRingCat.of k₁) := pullback.fst _ _ ≫ aR
  let b₀ : Z₀ ⟶ Spec (CommRingCat.of k₁) := pullback.snd _ _
  have hWc : pullback.fst U.hom (qq k k₁) ≫ U.hom = pullback.snd U.hom (qq k k₁) ≫ qq k k₁ :=
    pullback.condition
  have hu₀ : u₀ ≫ U.hom = a₀ ≫ qq k k₁ := by
    simp only [u₀, a₀, aR, Category.assoc]; rw [hWc]
  have hv₀ : v₀ ≫ U.hom = a₀ ≫ qq k k₁ := by
    simp only [v₀, a₀, Category.assoc]; rw [hWc, ← Category.assoc (pullback.snd π₁.left π₁.left), haR]
  have hb₀ : a₀ ≫ qq k k₁ = b₀ ≫ qq k k₁ := by
    simp only [a₀, b₀, Category.assoc]; exact pullback.condition
  have h₀ : pullback.lift u₀ a₀ hu₀ ≫ π₁.left = pullback.lift v₀ a₀ hv₀ ≫ π₁.left := by
    have e1 : pullback.lift u₀ a₀ hu₀ = pullback.fst _ _ ≫ pullback.fst π₁.left π₁.left := by
      apply pullback.hom_ext <;> simp [u₀, a₀, aR]
    have e2 : pullback.lift v₀ a₀ hv₀ = pullback.fst _ _ ≫ pullback.snd π₁.left π₁.left := by
      apply pullback.hom_ext
      · simp [v₀]
      · simp only [a₀, pullback.lift_snd, Category.assoc]; rw [haR]
    rw [e1, e2]
    simp only [Category.assoc]
    exact congrArg (pullback.fst (aR ≫ qq k k₁) (qq k k₁) ≫ ·) pullback.condition
  -- reducedness of the universal source
  haveI : Smooth (pullback.fst (aR ≫ qq k k₁) (qq k k₁)) := inferInstance
  haveI : Smooth aR := inferInstance
  haveI : Smooth (b₀ ≫ qq k k₁) := by
    rw [← hb₀]; simp only [a₀]; infer_instance
  haveI : IsReduced Z₀ := Smooth.isReduced_of_field (b₀ ≫ qq k k₁)
  -- field tests
  have huniv : pullback.lift u₀ b₀ (hu₀.trans hb₀) ≫ π₁.left = pullback.lift v₀ b₀ (hv₀.trans hb₀) ≫ π₁.left := by
    let src : Over (Spec (CommRingCat.of k₁)) := Over.mk b₀
    let f₁ : src ⟶ X₁ := Over.homMk (pullback.lift u₀ b₀ (hu₀.trans hb₀) ≫ π₁.left) (by
      change (pullback.lift u₀ b₀ _ ≫ π₁.left) ≫ X₁.hom = b₀
      rw [Category.assoc, w_π₁, pullback.lift_snd])
    let f₂ : src ⟶ X₁ := Over.homMk (pullback.lift v₀ b₀ (hv₀.trans hb₀) ≫ π₁.left) (by
      change (pullback.lift v₀ b₀ _ ≫ π₁.left) ≫ X₁.hom = b₀
      rw [Category.assoc, w_π₁, pullback.lift_snd])
    haveI : IsReduced src.left := (inferInstance : IsReduced Z₀)
    have := Scheme.over_hom_eq_of_field_tests f₁ f₂ (fun L _ β p => by
      apply Over.OverMorphism.ext
      simp only [Over.comp_left, f₁, f₂, Over.homMk_left]
      rw [← Category.assoc, ← Category.assoc,
        ← lift_comp_left U.hom (qq k k₁) p.left u₀ b₀ (hu₀.trans hb₀),
        ← lift_comp_left U.hom (qq k k₁) p.left v₀ b₀ (hv₀.trans hb₀)]
      refine field_KI π' hπ r e he_ker he_nat X₁ π₁ c hc hcompat L (p.left ≫ u₀) (p.left ≫ v₀)
        (p.left ≫ a₀) (p.left ≫ b₀) (by rw [Category.assoc, hu₀, ← Category.assoc])
        (by rw [Category.assoc, hv₀, ← Category.assoc]) (by rw [Category.assoc, hb₀, ← Category.assoc]) ?_
      rw [lift_comp_left U.hom (qq k k₁) p.left u₀ a₀ hu₀, lift_comp_left U.hom (qq k k₁) p.left v₀ a₀ hv₀,
        Category.assoc, Category.assoc, h₀])
    exact congrArg (fun z => Over.Hom.left z) this
  -- specialize
  let t : Z ⟶ Z₀ := pullback.lift (pullback.lift (pullback.lift u a hu) (pullback.lift v a hv) h) b (by
    simp only [aR, Category.assoc]; rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, hb])
  have := congrArg (t ≫ ·) huniv
  simp only [← Category.assoc] at this
  convert this using 2
  · apply pullback.hom_ext <;> simp [t, u₀, b₀]
  · apply pullback.hom_ext <;> simp [t, v₀, b₀]

end KI1

end ZInQ.ChevFree

#print axioms ZInQ.ChevFree.rig_raw
#print axioms ZInQ.ChevFree.torus_kernel_transfer
#print axioms ZInQ.ChevFree.kbar_KI
#print axioms ZInQ.ChevFree.algclosed_KI
#print axioms ZInQ.ChevFree.KI_of
