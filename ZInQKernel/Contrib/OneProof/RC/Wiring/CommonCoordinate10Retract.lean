import ZInQKernel.Contrib.OneProof.RC.Limits.SplitModel
import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.SelmerLink
import ZInQKernel.Contrib.OneProof.RC.Wiring.KmCoordBilinear

/-!
# Retracts onto isomorphic models; coordinate vectors of classes and functionals

Manuscript `diophantine_zq.tex`, the support triangle of Lemma `ex:arith-common-coordinate`
(tex 4157–4194) and the graded models of Lemma `ex:limits-inner-limit` (tex 4391–4451: "every
fixed finite diagram of maps and homotopies … transports to these models").

* `retractOfModelEquiv`: a normalized graded deformation retract of `X` onto `Y` and a
  degreewise isomorphism of complexes `Y' ≃ Y` give a retract of `X` onto `Y'` (inclusion
  `i ∘ e`, projection `e⁻¹ ∘ p`, the same homotopy).
* `funVec φ`: the coordinate vector `k ↦ φ(e_k)` of a linear functional on `A^ι`;
  `φ v = funVec φ ⬝ᵥ v` (`funVec_dotProduct`).
* A retract carries cycles to cycles (`retract_p_cycle`) and closed functionals to closed
  functionals (`retract_closed_comp_i`); on a matrix model the coordinate vector of a closed
  functional is a left null vector of the differential (`funVec_vecMul_eq_zero`).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix ZInQ.Manuscript.RC.Limits ZInQ.Contrib.CloudB3RC53.PairedFunctional

section Retract

variable {A : Type} [CommRing A]

/-- **A retract onto an isomorphic model** (tex 4423–4437, 5398–5403): from a normalized graded
deformation retract `R` of `X` onto `Y` and a degreewise isomorphism `e : Y' ≃ Y` commuting with
the differentials, the retract of `X` onto `Y'` with inclusion `i ∘ e`, projection `e⁻¹ ∘ p` and
the homotopy of `R`. Kind: definition (PROVED identities). -/
def retractOfModelEquiv {X Y Y' : GCx A} (R : GRetract X Y) (e : ∀ n, Y'.X n ≃ₗ[A] Y.X n)
    (he : ∀ a b (h : a + 1 = b) (y : Y'.X a), Y.d a b h (e a y) = e b (Y'.d a b h y)) :
    GRetract X Y' where
  i :=
    { f := fun a b h => by
        subst h
        exact R.i.f a a rfl ∘ₗ (e a).toLinearMap
      comm := by
        intro i i₁ j j₁ hij h₁ h₂ hj y
        subst hij hj h₁
        change R.i.f (i + 1) (i + 1) rfl (e (i + 1) (Y'.d i (i + 1) rfl y)) =
          X.d i (i + 1) rfl (R.i.f i i rfl (e i y))
        rw [← he, R.i_d] }
  p :=
    { f := fun a b h => by
        subst h
        exact (e a).symm.toLinearMap ∘ₗ R.p.f a a rfl
      comm := by
        intro i i₁ j j₁ hij h₁ h₂ hj x
        subst hij hj h₁
        change (e (i + 1)).symm (R.p.f (i + 1) (i + 1) rfl (X.d i (i + 1) rfl x)) =
          Y'.d i (i + 1) rfl ((e i).symm (R.p.f i i rfl x))
        have hc := he i (i + 1) rfl ((e i).symm (R.p.f i i rfl x))
        rw [LinearEquiv.apply_symm_apply] at hc
        rw [R.p_d, hc, LinearEquiv.symm_apply_apply] }
  h := R.h
  p_i n y := by
    change (e n).symm (R.p.f n n rfl (R.i.f n n rfl (e n y))) = y
    rw [R.p_i, LinearEquiv.symm_apply_apply]
  homotopy n x := by
    change x - R.i.f n n rfl (e n ((e n).symm (R.p.f n n rfl x))) = _
    rw [LinearEquiv.apply_symm_apply]
    exact R.homotopy n x
  h_h := R.h_h
  h_i a b hab y := by
    change R.h a b hab (R.i.f a a rfl (e a y)) = 0
    exact R.h_i a b hab _
  p_h a b hab x := by
    change (e b).symm (R.p.f b b rfl (R.h a b hab x)) = 0
    rw [R.p_h, map_zero]

/-- The inclusion of `retractOfModelEquiv` is `i ∘ e`. (tex 4423–4437)
Kind: PROVED (definitional). -/
theorem retractOfModelEquiv_i {X Y Y' : GCx A} (R : GRetract X Y) (e : ∀ n, Y'.X n ≃ₗ[A] Y.X n)
    (he : ∀ a b (h : a + 1 = b) (y : Y'.X a), Y.d a b h (e a y) = e b (Y'.d a b h y)) (n : ℤ)
    (y : Y'.X n) : (retractOfModelEquiv R e he).i.f n n rfl y = R.i.f n n rfl (e n y) :=
  rfl

/-- The projection of `retractOfModelEquiv` is `e⁻¹ ∘ p`. (tex 4423–4437)
Kind: PROVED (definitional). -/
theorem retractOfModelEquiv_p {X Y Y' : GCx A} (R : GRetract X Y) (e : ∀ n, Y'.X n ≃ₗ[A] Y.X n)
    (he : ∀ a b (h : a + 1 = b) (y : Y'.X a), Y.d a b h (e a y) = e b (Y'.d a b h y)) (n : ℤ)
    (x : X.X n) : (retractOfModelEquiv R e he).p.f n n rfl x = (e n).symm (R.p.f n n rfl x) :=
  rfl

/-- A retract carries cycles to cycles. (tex 4423–4437) Kind: PROVED. -/
theorem retract_p_cycle {X Y : GCx A} (R : GRetract X Y) {a b : ℤ} (h : a + 1 = b) {x : X.X a}
    (hx : X.d a b h x = 0) : Y.d a b h (R.p.f a a rfl x) = 0 := by
  rw [← R.p_d, hx, map_zero]

/-- A retract carries closed functionals to closed functionals: `λ ∘ i ∘ d = λ ∘ d ∘ i = 0`.
(tex 4423–4437, 4166–4172) Kind: PROVED. -/
theorem retract_closed_comp_i {X Y : GCx A} (R : GRetract X Y) {a b : ℤ} (h : a + 1 = b)
    (lam : X.X b →ₗ[A] A) (hlam : lam ∘ₗ X.d a b h = 0) :
    (lam ∘ₗ R.i.f b b rfl) ∘ₗ Y.d a b h = 0 := by
  apply LinearMap.ext
  intro y
  change lam (R.i.f b b rfl (Y.d a b h y)) = 0
  rw [R.i_d]
  exact LinearMap.congr_fun hlam _

end Retract

section FunVec

variable {A : Type} [CommRing A] {ι κ : Type} [DecidableEq ι]

/-- **The coordinate vector of a linear functional** on `A^ι`: `k ↦ φ(e_k)` (tex 3877–3892:
the functional `λ` as a row vector). Kind: definition. -/
def funVec (φ : (ι → A) →ₗ[A] A) : ι → A := fun k => φ (Pi.single k 1)

/-- `φ v = funVec φ ⬝ᵥ v`. (tex 3877–3892) Kind: PROVED. -/
theorem funVec_dotProduct [Fintype ι] (φ : (ι → A) →ₗ[A] A) (v : ι → A) : φ v = funVec φ ⬝ᵥ v := by
  conv_lhs => rw [pi_eq_sum_univ v]
  simp only [map_sum, map_smul, smul_eq_mul, dotProduct, funVec]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm]
  congr 2
  funext j
  simp [Pi.single_apply, eq_comm]

/-- The coordinate vector of `c • φ`. (tex 3877–3892) Kind: PROVED. -/
theorem funVec_smul (c : A) (φ : (ι → A) →ₗ[A] A) : funVec (c • φ) = c • funVec φ := by
  funext k
  rfl

/-- **On a matrix model a closed functional is a left null vector**: if `φ ∘ M = 0` then
`funVec φ ᵥ* M = 0`. (tex 3877–3892) Kind: PROVED. -/
theorem funVec_vecMul_eq_zero [Fintype ι] [Fintype κ] [DecidableEq κ] (φ : (ι → A) →ₗ[A] A)
    (M : Matrix ι κ A) (h : φ ∘ₗ M.mulVecLin = 0) : funVec φ ᵥ* M = 0 := by
  funext j
  have hj := LinearMap.congr_fun h (Pi.single j 1)
  change φ (M *ᵥ Pi.single j 1) = 0 at hj
  rw [funVec_dotProduct, dotProduct_mulVec, dotProduct_single, mul_one] at hj
  exact hj

end FunVec

end ZInQ.Manuscript.RC.Wiring
