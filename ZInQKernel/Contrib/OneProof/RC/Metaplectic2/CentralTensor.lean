import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.FiniteSign

/-! The product of local signs is the scalar on a restricted tensor.
This is the on-the-spot (c) algebraic descent in tex 8798–8807 and
8996–9004. -/

noncomputable section

namespace ZInQ.Manuscript.RC.Metaplectic2

open Intertwine Intertwine2 Metaplectic Visibility
open scoped BigOperators Classical

private theorem pure_of_finite_scaling (s : Finset Place) (z : Place → ℂ)
    (f g : Elementary) (hg : ∀ p, g p = if p ∈ s then z p • f p else f p) :
    pure g = (∏ p ∈ s, z p) • pure f := by
  induction s using Finset.induction_on generalizing g with
  | empty =>
    have e : g = f := by
      apply RestrictedProduct.ext
      intro p
      simpa using hg p
    rw [e, Finset.prod_empty, one_smul]
  | insert p s hp ih =>
    let k := replace g p (f p)
    have hk (q : Place) : k q = if q ∈ s then z q • f q else f q := by
      change Function.update (⇑g) p (f p) q = _
      by_cases hq : q = p
      · subst q
        simp [hp]
      · rw [Function.update_of_ne hq, hg q]
        simp [hq]
    have h₁ : g = replace k p (z p • f p) := by
      apply RestrictedProduct.ext
      intro q
      change g q = Function.update (⇑k) p (z p • f p) q
      by_cases hq : q = p
      · subst q
        simpa using hg p
      · rw [Function.update_of_ne hq]
        change g q = Function.update (⇑g) p (f p) q
        rw [Function.update_of_ne hq]
    have h₂ : replace k p (f p) = k := by
      apply RestrictedProduct.ext
      intro q
      change Function.update (⇑k) p (f p) q = k q
      by_cases hq : q = p
      · subst q
        simp [hk, hp]
      · rw [Function.update_of_ne hq]
    calc
      pure g = z p • pure (replace k p (f p)) := by
        calc
          pure g = pure (replace k p (z p • f p)) := congrArg pure h₁
          _ = _ := pure_smul _ _ _ _
      _ = _ := by rw [h₂, ih k hk, smul_smul, Finset.prod_insert hp]

/-- A finitely supported tuple of scalar operators acts by their product. -/
theorem restrictedAction_scalar (T : RestrictedOperators) (z : Place → ℂˣ)
    (hz : z.HasFiniteMulSupport) (hT : ∀ p f, T p f = (z p : ℂ) • f) :
    restrictedAction T = ((∏ᶠ p, z p : ℂˣ) : ℂ) • (1 : Module.End ℂ RestrictedTensor) := by
  apply tensor_ext
  intro f
  rw [show restrictedAction T (pure f) = pure (actFamily T f) from act_pure _ _]
  rw [finprod_eq_prod _ hz]
  change pure (actFamily T f) = ((↑(∏ p ∈ hz.toFinset, z p) : ℂ)) • pure f
  rw [show (↑(∏ p ∈ hz.toFinset, z p) : ℂ) = ∏ p ∈ hz.toFinset, (z p : ℂ) from
    map_prod (Units.coeHom ℂ) _ _]
  apply pure_of_finite_scaling
  intro p
  change T p (f p) = _
  rw [hT]
  by_cases hp : p ∈ hz.toFinset
  · rw [ite_eq_left hp]
  · have e : z p = 1 := by simpa [Function.mulSupport] using hp
    rw [ite_eq_right hp, e, Units.val_one, one_smul]

variable (a b : Fin 3 → ℕ) [∀ i, NeZero (2 * a i)] [∀ i, NeZero (2 * b i)]

theorem firstTensorAction_center (z : FiniteCenter a b) :
    firstTensorAction a b z = (centralProduct a b z : ℂ) • (1 : Module.End ℂ RestrictedTensor) := by
  apply restrictedAction_scalar _ _ (centralScalar_finite a b z)
  intro p f
  change (localFirst p a b ((z : FiniteLocalCover a b) p) : LocalEnd p) f =
    (centralScalar a b z p : ℂ) • f
  rcases finiteCenter_cases a b z p with h | h
  · rw [h, map_one, centralScalar, ite_eq_left h]
    change f = (1 : ℂ) • f
    exact (one_smul ℂ f).symm
  · rw [centralScalar, ite_eq_right (h ▸ (localProjection_kernel p a b).1), h]
    change (negativeOperator p : LocalEnd p) f = (-1 : ℂ) • f
    rw [negativeOperator_apply]
    exact (neg_one_smul ℂ f).symm

theorem secondTensorAction_center (z : FiniteCenter a b) :
    secondTensorAction a b z = (centralProduct a b z : ℂ) • (1 : Module.End ℂ RestrictedTensor) := by
  apply restrictedAction_scalar _ _ (centralScalar_finite a b z)
  intro p f
  change (localSecond p a b ((z : FiniteLocalCover a b) p) : LocalEnd p) f =
    (centralScalar a b z p : ℂ) • f
  rcases finiteCenter_cases a b z p with h | h
  · rw [h, map_one, centralScalar, ite_eq_left h]
    change f = (1 : ℂ) • f
    exact (one_smul ℂ f).symm
  · rw [centralScalar, ite_eq_right (h ▸ (localProjection_kernel p a b).1), h]
    change (negativeOperator p : LocalEnd p) f = (-1 : ℂ) • f
    rw [negativeOperator_apply]
    exact (neg_one_smul ℂ f).symm

def commonFirst : FiniteCommon a b →* Module.End ℂ RestrictedTensor :=
  QuotientGroup.lift _ (firstTensorAction a b) (by
    rintro _ ⟨z, hz, rfl⟩
    change centralProduct a b z = 1 at hz
    change firstTensorAction a b z = 1
    rw [firstTensorAction_center, hz, Units.val_one, one_smul])

def commonSecond : FiniteCommon a b →* Module.End ℂ RestrictedTensor :=
  QuotientGroup.lift _ (secondTensorAction a b) (by
    rintro _ ⟨z, hz, rfl⟩
    change centralProduct a b z = 1 at hz
    change secondTensorAction a b z = 1
    rw [secondTensorAction_center, hz, Units.val_one, one_smul])

theorem commonFirst_sign :
    commonFirst a b (finiteSign a b) = -(1 : Module.End ℂ RestrictedTensor) := by
  change firstTensorAction a b (singleSign a b) = _
  rw [firstTensorAction_center, centralProduct_singleSign]
  exact neg_one_smul _ _

theorem commonSecond_sign :
    commonSecond a b (finiteSign a b) = -(1 : Module.End ℂ RestrictedTensor) := by
  change secondTensorAction a b (singleSign a b) = _
  rw [secondTensorAction_center, centralProduct_singleSign]
  exact neg_one_smul _ _

#print axioms pure_of_finite_scaling
#print axioms restrictedAction_scalar
#print axioms firstTensorAction_center
#print axioms secondTensorAction_center
#print axioms commonFirst_sign
#print axioms commonSecond_sign

end ZInQ.Manuscript.RC.Metaplectic2
