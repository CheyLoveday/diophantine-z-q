import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.Projective
import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.Restricted
import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.Splitting

/-! The literal finite tensor tests of tex 8996–8999, before the common
lift is constructed. The linear map from class tables is on-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.Metaplectic2

open Intertwine Intertwine2 Metaplectic OldStageLaw Filter
open scoped BigOperators

def localUnitAction (p : Place) : (LocalEnd p)ˣ →* LocalEnd p where
  toFun := Units.val
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Restricted product of linear automorphism groups relative to the
subgroups fixing the reference vectors. -/
abbrev RestrictedUnits :=
  RestrictedProduct (fun p => (LocalEnd p)ˣ)
    (fun p => (sphericalStabilizer p (localUnitAction p) : Set _)) cofinite

def forgetUnits : RestrictedUnits →* RestrictedOperators where
  toFun T := ⟨fun p => (T p : LocalEnd p), T.2⟩
  map_one' := by ext p; rfl
  map_mul' _ _ := by ext p; rfl

variable (a : Fin 3 → ℕ) [∀ i, NeZero (2 * a i)]

/-- The actual operator tuple for each inverse generator, before
identification with a common central extension. -/
def operatorStep : Step → RestrictedUnits
  | .trans n => ⟨fun p => upperUnit p a (-(n : ℚ_[p.val])), (upperTuple a n).2⟩
  | .inv => ⟨fun p => weylUnit p a, by
      filter_upwards [(weylTuple a).2] with p hp
      change (weylUnit p a : LocalEnd p) (spherical p) = _
      rwa [coe_weylUnit]⟩

private theorem forget_operatorStep (s : Step) :
    forgetUnits (operatorStep a s) = match s with
      | .trans n => upperTuple a n
      | .inv => weylTuple a := by
  cases s
  · apply RestrictedProduct.ext
    intro p
    exact coe_weylUnit p a
  · rfl

/-- Send each class delta to its elementary coset tensor. -/
def gridTensor : (Grid a → ℂ) →ₗ[ℂ] RestrictedTensor where
  toFun w := ∑ r, w r • pure (elementaryFamily (center r))
  map_add' v w := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c w := by simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, smul_smul,
    smul_eq_mul]

theorem gridTensor_delta (r : Grid a) :
    gridTensor a (classDelta r) = pure (elementaryFamily (center r)) := by
  classical
  change (∑ s, (Pi.single (M := fun _ : Grid a => ℂ) r 1) s • pure (elementaryFamily (center s))) = _
  rw [Finset.sum_eq_single r]
  · simp
  · intro s _ hs
    simp [Pi.single_eq_of_ne hs]
  · simp

theorem evaluate_gridTensor (w : Grid a → ℂ) :
    evaluate (gridTensor a w) = J rationalFiniteModel w := by
  classical
  have he (r : Grid a) : evaluate (pure (elementaryFamily (center r))) =
      J rationalFiniteModel (classDelta r) := by
    rw [classDelta_eval]
    exact funext (elementary_grid r)
  change evaluate (∑ r, w r • pure (elementaryFamily (center r))) = _
  simp_rw [map_sum, map_smul, he, ← map_smul, ← map_sum]
  congr 1
  unfold classDelta
  simp_rw [← Pi.single_smul', smul_eq_mul, mul_one]
  exact Finset.univ_sum_single w

theorem gridTensor_injective : Function.Injective (gridTensor a) := by
  intro v w h
  apply J_injective rationalFiniteModel
  rw [← evaluate_gridTensor a, ← evaluate_gridTensor a, h]

/-- The cylinder condition is realized on the full restricted tensor
space for the group of local operator tuples of a single form. -/
theorem restricted_generatorTensorAction :
    GeneratorTensorAction (gridTensor a) evaluate (restrictedAction.comp forgetUnits)
      (operatorStep a) (fun p => gaussIndex a p) := by
  constructor
  · intro n r x
    change evaluate (restrictedAction (forgetUnits (operatorStep a (.trans n)))
      (gridTensor a (classDelta r))) x = _
    rw [gridTensor_delta, forget_operatorStep]
    exact restricted_upper n r x
  · intro r y
    change evaluate (restrictedAction (forgetUnits (operatorStep a .inv))
      (gridTensor a (classDelta r))) y = _
    rw [gridTensor_delta, forget_operatorStep]
    exact restricted_weyl r y

#print axioms forget_operatorStep
#print axioms gridTensor_delta
#print axioms evaluate_gridTensor
#print axioms gridTensor_injective
#print axioms restricted_generatorTensorAction

end ZInQ.Manuscript.RC.Metaplectic2
