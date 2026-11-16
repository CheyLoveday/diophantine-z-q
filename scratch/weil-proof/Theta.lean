import ZInQKernel.Contrib.OneProof.WeilFormula

/-! weil-proof, §23 attempt, part 1: lifts over endomorphisms and their commutators (generic). -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite

namespace WeilProof.Theta

open Scheme.Modules PicDict.Transport

variable {X : Scheme.{0}} (N : X.Modules)

/-- The product of a lift `α` over `t` and a lift `β` over `s`: a lift over `t ≫ s`. -/
def prod {t s : X ⟶ X} (α : (Scheme.Modules.pullback t).obj N ⟶ N)
    (β : (Scheme.Modules.pullback s).obj N ⟶ N) : (Scheme.Modules.pullback (t ≫ s)).obj N ⟶ N :=
  (pullbackComp t s).inv.app N ≫ (Scheme.Modules.pullback t).map β ≫ α

/-- Moving a lift along an equality of morphisms. -/
def mv {t t' : X ⟶ X} (e : t = t') (α : (Scheme.Modules.pullback t).obj N ⟶ N) :
    (Scheme.Modules.pullback t').obj N ⟶ N :=
  eqToHom (by rw [e]) ≫ α

variable {N}

@[simp] lemma mv_rfl {t : X ⟶ X} (α : (Scheme.Modules.pullback t).obj N ⟶ N) : mv N rfl α = α := by
  simp [mv]

lemma mv_mv {t t' t'' : X ⟶ X} (e : t = t') (e' : t' = t'') (α : (Scheme.Modules.pullback t).obj N ⟶ N) :
    mv N e' (mv N e α) = mv N (e.trans e') α := by
  subst e e'; simp

lemma mv_comp_smul {t t' : X ⟶ X} (e : t = t') (α : (Scheme.Modules.pullback t).obj N ⟶ N)
    (κ : Γ(X, ⊤)) : mv N e (α ≫ N.smulHom κ) = mv N e α ≫ N.smulHom κ := by
  simp [mv]

lemma prod_mv_left {t t' s : X ⟶ X} (e : t = t') (α : (Scheme.Modules.pullback t).obj N ⟶ N)
    (β : (Scheme.Modules.pullback s).obj N ⟶ N) :
    prod N (mv N e α) β = mv N (by rw [e]) (prod N α β) := by
  subst e; simp

lemma prod_mv_right {t s s' : X ⟶ X} (e : s = s') (α : (Scheme.Modules.pullback t).obj N ⟶ N)
    (β : (Scheme.Modules.pullback s).obj N ⟶ N) :
    prod N α (mv N e β) = mv N (by rw [e]) (prod N α β) := by
  subst e; simp

lemma prod_smul_left {t s : X ⟶ X} (α : (Scheme.Modules.pullback t).obj N ⟶ N)
    (β : (Scheme.Modules.pullback s).obj N ⟶ N) (κ : Γ(X, ⊤)) :
    prod N (α ≫ N.smulHom κ) β = prod N α β ≫ N.smulHom κ := by
  simp [prod]

lemma prod_smul_right {t s : X ⟶ X} (ht : ∀ r : Γ(X, ⊤), t.appTop r = r)
    (α : (Scheme.Modules.pullback t).obj N ⟶ N)
    (β : (Scheme.Modules.pullback s).obj N ⟶ N) (κ : Γ(X, ⊤)) :
    prod N α (β ≫ N.smulHom κ) = prod N α β ≫ N.smulHom κ := by
  simp only [prod, Functor.map_comp, pullback_map_smulHom, ht, Category.assoc]
  rw [smulHom_naturality]

lemma assoc_inv (t s r : X ⟶ X) (M : X.Modules) :
    (pullbackComp (t ≫ s) r).inv.app M ≫ (pullbackComp t s).inv.app ((Scheme.Modules.pullback r).obj M) =
      eqToHom (by rw [Category.assoc]) ≫ (pullbackComp t (s ≫ r)).inv.app M ≫
        (Scheme.Modules.pullback t).map ((pullbackComp s r).inv.app M) := by
  have h := pullbackComp_assoc_app t s r M
  rw [← cancel_mono ((Scheme.Modules.pullback t).map ((pullbackComp s r).hom.app M) ≫
    (pullbackComp t (s ≫ r)).hom.app M)]
  simp only [Category.assoc]
  conv_lhs => rw [h]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id_app]
  simp

/-- **Associativity** of the product of lifts. -/
lemma prod_assoc {t s r : X ⟶ X} (α : (Scheme.Modules.pullback t).obj N ⟶ N)
    (β : (Scheme.Modules.pullback s).obj N ⟶ N) (γ : (Scheme.Modules.pullback r).obj N ⟶ N) :
    prod N (prod N α β) γ = mv N (Category.assoc t s r).symm (prod N α (prod N β γ)) := by
  have nat := (pullbackComp t s).inv.naturality γ
  simp only [Functor.comp_map] at nat
  have hA := pullbackComp_assoc_inv₁ t s r N
  simp only [prod, mv, Functor.map_comp, Category.assoc]
  rw [reassoc_of% nat, reassoc_of% (assoc_inv t s r N)]

lemma prod_assoc' {t s r : X ⟶ X} (α : (Scheme.Modules.pullback t).obj N ⟶ N)
    (β : (Scheme.Modules.pullback s).obj N ⟶ N) (γ : (Scheme.Modules.pullback r).obj N ⟶ N) :
    prod N α (prod N β γ) = mv N (Category.assoc t s r) (prod N (prod N α β) γ) := by
  rw [prod_assoc, mv_mv, mv_rfl]

variable (N) in
/-- `α` (over `t`) and `β` (over `s`) commute up to the scalar `κ`. -/
def Comm {t s : X ⟶ X} (h : s ≫ t = t ≫ s) (α : (Scheme.Modules.pullback t).obj N ⟶ N)
    (β : (Scheme.Modules.pullback s).obj N ⟶ N) (κ : Γ(X, ⊤)) : Prop :=
  prod N α β = mv N h (prod N β α) ≫ N.smulHom κ

/-- **Multiplicativity of the commutator in the first variable.** -/
lemma comm_prod_left {t t' s : X ⟶ X} (ht : ∀ r : Γ(X, ⊤), t.appTop r = r)
    (hs : ∀ r : Γ(X, ⊤), s.appTop r = r)
    {h₁ : s ≫ t = t ≫ s} {h₂ : s ≫ t' = t' ≫ s} (h₃ : s ≫ (t ≫ t') = (t ≫ t') ≫ s)
    {α : (Scheme.Modules.pullback t).obj N ⟶ N} {α' : (Scheme.Modules.pullback t').obj N ⟶ N}
    {β : (Scheme.Modules.pullback s).obj N ⟶ N} {κ κ' : Γ(X, ⊤)}
    (c₁ : Comm N h₁ α β κ) (c₂ : Comm N h₂ α' β κ') : Comm N h₃ (prod N α α') β (κ' * κ) := by
  unfold Comm at *
  rw [prod_assoc, c₂, prod_smul_right ht, prod_mv_right, prod_assoc', mv_comp_smul, mv_mv, mv_mv, c₁,
    prod_smul_left, prod_mv_left, prod_assoc]
  simp only [mv_comp_smul, mv_mv, smulHom_mul, Category.assoc]

end WeilProof.Theta
