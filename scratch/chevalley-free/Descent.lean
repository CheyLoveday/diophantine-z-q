import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Descent.Finite
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.CategoryTheory.Limits.Shapes.Pullback.Map
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # chevalley-free, step D: descent of a quotient along a finite flat cover

`U` over `S`, `q : S' → S` finite, flat, surjective, locally of finite presentation, and an fpqc morphism
`π₁ : U_{S'} → X₁` over `S'` whose fibres are stable under the canonical transport of points of `U_{S'}`
(`KI`). If finite sets of `X₁` lie in affine opens, `X₁` descends to `B₀` over `S` and `π₁` to `π : U → B₀`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

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

end ZInQ.ChevFree

#print axioms ZInQ.ChevFree.exists_descent
