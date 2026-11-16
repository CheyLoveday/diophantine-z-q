import ZInQKernel.Contrib.OneProof.PicDictionary

/-! weil-proof, step 1: generic lemmas on the Weil formula `wf t m h M ψ` (any scheme). -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite

namespace WeilProof

open Scheme.Modules PicDict.Transport

universe u

variable {X : Scheme.{u}}

/-- The value at `1` of an endomorphism of `𝒪_X`, in `Γ(X, ⊤)`. -/
def val (g : unit X ⟶ unit X) : Γ(X, ⊤) := g.app ⊤ (1 : Γ(X, ⊤))

/-- An endomorphism of `𝒪_X` is multiplication by its value at `1`. -/
lemma endo_app_top (g : unit X ⟶ unit X) (r : Γ(X, ⊤)) :
    (show Γ(X, ⊤) from g.app ⊤ r) = r * val g := by
  have h := Hom.app_smul g r (1 : Γ(X, ⊤))
  simp only [smul_eq_mul, mul_one] at h
  exact h

/-- Composition of endomorphisms of `𝒪_X` is multiplication of values. -/
lemma comp_val (f g : unit X ⟶ unit X) : val (f ≫ g) = val f * val g := by
  unfold val
  rw [Hom.comp_app]
  exact endo_app_top g _

lemma id_val : val (𝟙 (unit X)) = 1 := rfl

/-- The automorphism of `𝒪_X` whose value is the Weil formula. -/
def alpha (t m : X ⟶ X) (h : t ≫ m = m) (M : X.Modules)
    (ψ : unit X ≅ (Scheme.Modules.pullback m).obj M) : unit X ⟶ unit X :=
  (pOU t).inv ≫ (Scheme.Modules.pullback t).map ψ.hom ≫ (pullbackComp t m).hom.app M ≫
    (pullbackCongr h).hom.app M ≫ ψ.inv

/-- Its inverse. -/
def alphaInv (t m : X ⟶ X) (h : t ≫ m = m) (M : X.Modules)
    (ψ : unit X ≅ (Scheme.Modules.pullback m).obj M) : unit X ⟶ unit X :=
  ψ.hom ≫ (pullbackCongr h).inv.app M ≫ (pullbackComp t m).inv.app M ≫
    (Scheme.Modules.pullback t).map ψ.inv ≫ (pOU t).hom

lemma wf_eq_alpha (t m : X ⟶ X) (h : t ≫ m = m) (M : X.Modules)
    (ψ : unit X ≅ (Scheme.Modules.pullback m).obj M) :
    wf t m h M ψ = val (alpha t m h M ψ) := rfl

lemma alpha_alphaInv (t m : X ⟶ X) (h : t ≫ m = m) (M : X.Modules)
    (ψ : unit X ≅ (Scheme.Modules.pullback m).obj M) :
    alpha t m h M ψ ≫ alphaInv t m h M ψ = 𝟙 _ := by
  simp only [alpha, alphaInv, Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_app_assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id]

/-- The Weil formula is a unit of `Γ(X, 𝒪)`. -/
lemma wf_isUnit (t m : X ⟶ X) (h : t ≫ m = m) (M : X.Modules)
    (ψ : unit X ≅ (Scheme.Modules.pullback m).obj M) : IsUnit (wf t m h M ψ) := by
  refine IsUnit.of_mul_eq_one (val (alphaInv t m h M ψ)) ?_
  rw [wf_eq_alpha, ← comp_val, alpha_alphaInv]
  rfl

lemma wf_congr_t {t t' m : X ⟶ X} (e : t = t') (h : t ≫ m = m) (h' : t' ≫ m = m) (M : X.Modules)
    (ψ : unit X ≅ (Scheme.Modules.pullback m).obj M) : wf t m h M ψ = wf t' m h' M ψ := by
  subst e; rfl

/-- The comparison `θ_t : t^* m^* M ≅ m^* M` for `t ≫ m = m` is a cocycle. -/
lemma theta_comp (t₁ t₂ m : X ⟶ X) (h₁ : t₁ ≫ m = m) (h₂ : t₂ ≫ m = m) (h₁₂ : (t₁ ≫ t₂) ≫ m = m)
    (M : X.Modules) :
    (pullbackComp t₁ t₂).hom.app ((Scheme.Modules.pullback m).obj M) ≫
        (pullbackComp (t₁ ≫ t₂) m).hom.app M ≫ (pullbackCongr h₁₂).hom.app M =
      (Scheme.Modules.pullback t₁).map ((pullbackComp t₂ m).hom.app M ≫ (pullbackCongr h₂).hom.app M) ≫
        (pullbackComp t₁ m).hom.app M ≫ (pullbackCongr h₁).hom.app M := by
  simp only [pullbackCongr_hom_app, Functor.map_comp, Category.assoc]
  rw [reassoc_of% (map_eqToHom_comp_pullbackComp t₁ h₂ M)]
  rw [reassoc_of% (pullbackComp_assoc_app t₁ t₂ m M)]
  simp

/-- **Cocycle relation for `α`**: `α_{t₁ t₂} = t₁^♯(α_{t₂}) ∘ α_{t₁}`. -/
lemma alpha_comp (t₁ t₂ m : X ⟶ X) (h₁ : t₁ ≫ m = m) (h₂ : t₂ ≫ m = m) (h₁₂ : (t₁ ≫ t₂) ≫ m = m)
    (M : X.Modules) (ψ : unit X ≅ (Scheme.Modules.pullback m).obj M) :
    alpha (t₁ ≫ t₂) m h₁₂ M ψ =
      ((pOU t₁).inv ≫ (Scheme.Modules.pullback t₁).map (alpha t₂ m h₂ M ψ) ≫ (pOU t₁).hom) ≫
        alpha t₁ m h₁ M ψ := by
  have nat := (pullbackComp t₁ t₂).hom.naturality ψ.hom
  simp only [Functor.comp_map] at nat
  have hθ := theta_comp t₁ t₂ m h₁ h₂ h₁₂ M
  simp only [alpha, pOU_inv_comp t₁ t₂, Category.assoc]
  rw [← reassoc_of% nat, reassoc_of% hθ]
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc (Scheme.Modules.pullback t₁) ψ.inv ψ.hom, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- **Cocycle relation for the Weil formula**: `wf_{t₁ t₂} = t₁^*(wf_{t₂}) · wf_{t₁}`. -/
theorem wf_comp (t₁ t₂ m : X ⟶ X) (h₁ : t₁ ≫ m = m) (h₂ : t₂ ≫ m = m) (h₁₂ : (t₁ ≫ t₂) ≫ m = m)
    (M : X.Modules) (ψ : unit X ≅ (Scheme.Modules.pullback m).obj M) :
    wf (t₁ ≫ t₂) m h₁₂ M ψ = t₁.appTop (wf t₂ m h₂ M ψ) * wf t₁ m h₁ M ψ := by
  rw [wf_eq_alpha, alpha_comp t₁ t₂ m h₁ h₂ h₁₂ M ψ, comp_val]
  exact congrArg (· * _) (pOU_conj t₁ (alpha t₂ m h₂ M ψ))

/-- `wf_𝟙 = 1`. -/
theorem wf_id (m : X ⟶ X) (h : 𝟙 X ≫ m = m) (M : X.Modules)
    (ψ : unit X ≅ (Scheme.Modules.pullback m).obj M) : wf (𝟙 X) m h M ψ = 1 := by
  have h2 : (𝟙 X ≫ 𝟙 X) ≫ m = m := by simp
  have e := wf_comp (𝟙 X) (𝟙 X) m h h h2 M ψ
  rw [wf_congr_t (Category.id_comp (𝟙 X)) h2 h] at e
  have e' : wf (𝟙 X) m h M ψ * 1 = wf (𝟙 X) m h M ψ * wf (𝟙 X) m h M ψ := by
    rw [mul_one]; exact e.trans (by simp)
  exact ((wf_isUnit _ _ h M ψ).mul_left_cancel e').symm

/-- **Change of trivialization**: if the ratio `a = ψ' ψ⁻¹` has a `t`-invariant value, the Weil
formula does not change. -/
theorem wf_change (t m : X ⟶ X) (h : t ≫ m = m) (M : X.Modules)
    (ψ ψ' : unit X ≅ (Scheme.Modules.pullback m).obj M)
    (ha : t.appTop (val (ψ'.hom ≫ ψ.inv)) = val (ψ'.hom ≫ ψ.inv)) :
    wf t m h M ψ' = wf t m h M ψ := by
  have key : alpha t m h M ψ' =
      ((pOU t).inv ≫ (Scheme.Modules.pullback t).map (ψ'.hom ≫ ψ.inv) ≫ (pOU t).hom) ≫
        alpha t m h M ψ ≫ (ψ.hom ≫ ψ'.inv) := by
    simp only [alpha, Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
    rw [← Functor.map_comp_assoc (Scheme.Modules.pullback t) ψ.inv ψ.hom, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have hab : val (ψ'.hom ≫ ψ.inv) * val (ψ.hom ≫ ψ'.inv) = 1 := by
    rw [← comp_val]; simp [id_val]
  have hc : val ((pOU t).inv ≫ (Scheme.Modules.pullback t).map (ψ'.hom ≫ ψ.inv) ≫ (pOU t).hom) =
      val (ψ'.hom ≫ ψ.inv) := (pOU_conj t _).trans ha
  rw [wf_eq_alpha, key, comp_val, comp_val, hc, wf_eq_alpha]
  calc _ = val (alpha t m h M ψ) * (val (ψ'.hom ≫ ψ.inv) * val (ψ.hom ≫ ψ'.inv)) := by ring
    _ = _ := by rw [hab, mul_one]

end WeilProof
