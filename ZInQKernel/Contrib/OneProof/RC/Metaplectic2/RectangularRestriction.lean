import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.TensorFaithful
import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.TensorComparison

/-! Once the cylinder outputs are identified with the rectangular
table outputs, faithful evaluation promotes the equalities to tensor
identities. Restriction to the image is on-the-spot (c), tex 8991–9004. -/

noncomputable section

namespace ZInQ.Manuscript.RC.Metaplectic2

open Intertwine Intertwine2 Metaplectic WeilIndex OldStageLaw RelativeAction
open scoped MatrixGroups BigOperators

variable (a : Fin 3 → ℕ) [∀ i, NeZero (2 * a i)]

abbrev GridImage := LinearMap.range (gridTensor a)

def gridEmbedding : (Grid a → ℂ) →ₗ[ℂ] GridImage a := (gridTensor a).rangeRestrict

def gridEvaluation : GridImage a →ₗ[ℂ] (FiniteVectors → ℂ) :=
  evaluate.comp (GridImage a).subtype

theorem gridEmbedding_surjective : Function.Surjective (gridEmbedding a) := by
  intro x
  obtain ⟨w, hw⟩ := x.property
  exact ⟨w, Subtype.ext hw⟩

theorem gridEvaluation_injective : Function.Injective (gridEvaluation a) :=
  fun _ _ h => Subtype.ext (evaluate_injective h)

theorem gridEvaluation_embedding (w : Grid a → ℂ) :
    gridEvaluation a (gridEmbedding a w) = J rationalFiniteModel w :=
  evaluate_gridTensor a w

private def gridUpper (n : ℤ) : (Grid a → ℂ) →ₗ[ℂ] (Grid a → ℂ) where
  toFun := twist n
  map_add' v w := by funext r; simp [twist, mul_add]
  map_smul' c v := by funext r; simp [twist, mul_left_comm]

private def gridFourier : (Grid a → ℂ) →ₗ[ℂ] (Grid a → ℂ) where
  toFun := finiteFourier
  map_add' v w := by funext s; simp [finiteFourier, add_mul, Finset.sum_add_distrib, mul_add]
  map_smul' c v := by
    funext s
    simp [finiteFourier, smul_eq_mul, mul_assoc, ← Finset.mul_sum, mul_left_comm]

private theorem grid_linear_ext {V : Type*} [AddCommGroup V] [Module ℂ V]
    {F G : (Grid a → ℂ) →ₗ[ℂ] V} (h : ∀ r, F (classDelta r) = G (classDelta r)) : F = G := by
  classical
  apply LinearMap.ext
  intro w
  have hw : (∑ r, w r • classDelta r) = w := by
    unfold classDelta
    simp_rw [← Pi.single_smul', smul_eq_mul, mul_one]
    exact Finset.univ_sum_single w
  rw [← hw]
  simp only [map_sum, map_smul, h]

variable {G : Type*} [Group G] (R : G →* Module.End ℂ RestrictedTensor)

/-- The actual generator tests imply preservation on the rectangular grid
image. The Weyl scalar here is the finite index product. -/
theorem grid_generator_preserves (lift : Step → G) (γ : Place → ℂˣ)
    (hγ : γ.HasFiniteMulSupport) (h : GeneratorTensorAction (gridTensor a) evaluate R lift γ) :
    ∀ s z, z ∈ GridImage a → R (lift s) z ∈ GridImage a := by
  have hU (n : ℤ) :
      (R (lift (.trans n))).comp (gridTensor a) = (gridTensor a).comp (gridUpper a n) := by
    apply grid_linear_ext a
    intro r
    apply evaluate_injective
    funext x
    change evaluate (R (lift (.trans n)) (gridTensor a (classDelta r))) x =
      evaluate (gridTensor a (twist n (classDelta r))) x
    rw [h.1, evaluate_gridTensor, ← upper_tensor, upper_description, J_twist, classDelta_eval]
  have hW : (R (lift .inv)).comp (gridTensor a) =
      ((∏ᶠ p, γ p : ℂˣ) : ℂ) • ((gridTensor a).comp (gridFourier a)) := by
    apply grid_linear_ext a
    intro r
    apply evaluate_injective
    funext y
    change evaluate (R (lift .inv) (gridTensor a (classDelta r))) y =
      evaluate (((∏ᶠ p, γ p : ℂˣ) : ℂ) • gridTensor a (finiteFourier (classDelta r))) y
    rw [h.2, map_smul, evaluate_gridTensor, ← weyl_tensor γ hγ, weyl_description,
      ← classDelta_eval, ← adelic_fourier]
  rintro s _ ⟨w, rfl⟩
  cases s with
  | inv =>
    refine ⟨((∏ᶠ p, γ p : ℂˣ) : ℂ) • finiteFourier w, ?_⟩
    rw [map_smul]
    exact (LinearMap.congr_fun hW w).symm
  | trans n =>
    exact ⟨twist n w, (LinearMap.congr_fun (hU n) w).symm⟩

private theorem action_inv_apply (g : G) (v : RestrictedTensor) :
    R g⁻¹ (R g v) = v := by
  change (R g⁻¹ * R g) v = v
  rw [← map_mul, inv_mul_cancel, map_one]
  rfl

private def preservingGrid : Subgroup G where
  carrier := {g | ∀ v ∈ GridImage a, R g v ∈ GridImage a}
  one_mem' := by
    intro v hv
    change R 1 v ∈ GridImage a
    simpa only [map_one, Module.End.one_apply] using hv
  mul_mem' {x y} hx hy := by
    intro v hv
    rw [map_mul]
    exact hx _ (hy _ hv)
  inv_mem' {x} hx := by
    let : FiniteDimensional ℂ (GridImage a) :=
      FiniteDimensional.of_surjective (gridEmbedding a) (gridEmbedding_surjective a)
    let T : GridImage a →ₗ[ℂ] GridImage a := (R x).restrict hx
    have hi : Function.Injective T := by
      intro u v e
      have h : R x u.1 = R x v.1 := congrArg Subtype.val e
      apply Subtype.ext
      simpa only [action_inv_apply] using congrArg (R x⁻¹) h
    intro v hv
    obtain ⟨u, hu⟩ := (LinearMap.injective_iff_surjective.mp hi) ⟨v, hv⟩
    have h : R x u.1 = v := congrArg Subtype.val hu
    change R x⁻¹ v ∈ GridImage a
    rw [← h, action_inv_apply]
    exact u.property

/-- Invariance for the whole group follows from the two inverse generators
and the scalar action of elements above the identity. -/
theorem grid_invariant (π : G →* SL(2, ℤ)) (lift : Step → G)
    (hlift : ∀ s, π (lift s) = s.matrix⁻¹)
    (hker : ∀ g, π g = 1 → R g = 1 ∨ R g = -1)
    (γ : Place → ℂˣ) (hγ : γ.HasFiniteMulSupport)
    (h : GeneratorTensorAction (gridTensor a) evaluate R lift γ) :
    ∀ g v, v ∈ GridImage a → R g v ∈ GridImage a := by
  let H := preservingGrid a R
  have hgen (s : Step) : lift s ∈ H := grid_generator_preserves a R lift γ hγ h s
  have hS : ModularGroup.S ∈ H.map π := by
    refine ⟨(lift .inv)⁻¹, H.inv_mem (hgen .inv), ?_⟩
    rw [map_inv, hlift, inv_inv, Step.matrix]
  have hT : ModularGroup.T ∈ H.map π := by
    refine ⟨(lift (.trans 1))⁻¹, H.inv_mem (hgen (.trans 1)), ?_⟩
    rw [map_inv, hlift, inv_inv, Step.matrix, zpow_one]
  have htop : ⊤ ≤ H.map π := by
    rw [← SpecialLinearGroup.SL2Z_generators, Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact hS
    · exact hT
  intro g
  have hmem : π g ∈ H.map π := htop (Subgroup.mem_top (π g))
  obtain ⟨x, hx, he⟩ := hmem
  have hz : π (x⁻¹ * g) = 1 := by rw [map_mul, map_inv, he, inv_mul_cancel]
  have hbound : x⁻¹ * g ∈ H := by
    intro v hv
    change R (x⁻¹ * g) v ∈ GridImage a
    rcases hker _ hz with h' | h'
    · rw [h']
      exact hv
    · rw [h', LinearMap.neg_apply]
      exact (GridImage a).neg_mem hv
  have hh := H.mul_mem hx hbound
  rwa [← mul_assoc, mul_inv_cancel, one_mul] at hh

def restrictGridAction (h : ∀ g v, v ∈ GridImage a → R g v ∈ GridImage a) :
    G →* Module.End ℂ (GridImage a) where
  toFun g := (R g).restrict (h g)
  map_one' := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change R 1 v.1 = v.1
    rw [map_one]
    rfl
  map_mul' x y := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact LinearMap.congr_fun (map_mul R x y) v.1

theorem restricted_grid_tests (lift : Step → G) (γ : Place → ℂˣ)
    (h : GeneratorTensorAction (gridTensor a) evaluate R lift γ)
    (hi : ∀ g v, v ∈ GridImage a → R g v ∈ GridImage a) :
    GeneratorTensorAction (gridEmbedding a) (gridEvaluation a) (restrictGridAction a R hi) lift γ :=
  h


end ZInQ.Manuscript.RC.Metaplectic2
