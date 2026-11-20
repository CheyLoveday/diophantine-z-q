import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.IntegerLifts
import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.RectangularRestriction

/-! Common finite lifts on the two rectangular spaces, tex 8991–9004.
The action on the image, and its use in the comparison, are
on-the-spot (c). No stage or archimedean operator is used here. -/

noncomputable section

namespace ZInQ.Manuscript.RC.Metaplectic2

open Intertwine Intertwine2 Metaplectic WeilIndex GaussSign OldStageLaw RelativeAction

variable (a b : Fin 3 → ℕ) [∀ i, NeZero (2 * a i)] [∀ i, NeZero (2 * b i)]

private theorem first_invariant :
    ∀ g v, v ∈ GridImage a → integerFirst a b g v ∈ GridImage a := by
  refine grid_invariant a (integerFirst a b) (integerProjection a b) (integerLiftStep a b)
    (integerLiftStep_projection a b) ?_ _ (gaussGamma_productFormula (rationalDiagonal a)).1
    (common_first_generatorTensorAction a b)
  intro g hg
  rcases ((integerProjection_kernel a b).2 g).mp hg with rfl | rfl
  · exact Or.inl (map_one _)
  · exact Or.inr (integerSign_actions a b).1

private theorem second_invariant :
    ∀ g v, v ∈ GridImage b → integerSecond a b g v ∈ GridImage b := by
  refine grid_invariant b (integerSecond a b) (integerProjection a b) (integerLiftStep a b)
    (integerLiftStep_projection a b) ?_ _ (gaussGamma_productFormula (rationalDiagonal b)).1
    (common_second_generatorTensorAction a b)
  intro g hg
  rcases ((integerProjection_kernel a b).2 g).mp hg with rfl | rfl
  · exact Or.inl (map_one _)
  · exact Or.inr (integerSign_actions a b).2

/-- Restrict the first action of the common integer cover to the first
rectangular tensor image. -/
def rectangularFirst : IntegerCommon a b →* Module.End ℂ (GridImage a) :=
  restrictGridAction a (integerFirst a b) (first_invariant a b)

/-- Restrict the second action of the same cover to the second image. -/
def rectangularSecond : IntegerCommon a b →* Module.End ℂ (GridImage b) :=
  restrictGridAction b (integerSecond a b) (second_invariant a b)

theorem rectangular_first_tests :
    GeneratorTensorAction (gridEmbedding a) (gridEvaluation a) (rectangularFirst a b)
      (integerLiftStep a b) (fun p => gaussIndex a p) :=
  restricted_grid_tests a (integerFirst a b) _ _ (common_first_generatorTensorAction a b) _

theorem rectangular_second_tests :
    GeneratorTensorAction (gridEmbedding b) (gridEvaluation b) (rectangularSecond a b)
      (integerLiftStep a b) (fun p => gaussIndex b p) :=
  restricted_grid_tests b (integerSecond a b) _ _ (common_second_generatorTensorAction a b) _

theorem rectangular_sign_actions :
    rectangularFirst a b (integerSign a b) = -(1 : Module.End ℂ (GridImage a)) ∧
    rectangularSecond a b (integerSign a b) = -(1 : Module.End ℂ (GridImage b)) := by
  constructor
  · apply LinearMap.ext
    intro v
    apply Subtype.ext
    change integerFirst a b (integerSign a b) v.1 = -v.1
    rw [(integerSign_actions a b).1]
    rfl
  · apply LinearMap.ext
    intro v
    apply Subtype.ext
    change integerSecond a b (integerSign a b) v.1 = -v.1
    rw [(integerSign_actions a b).2]
    rfl

omit [∀ i, NeZero (2 * b i)] in
/-- The literal common inverse lifts give both generator comparisons
with the same scalar, for the rectangular form and the reference form. -/
theorem common_rectangular_comparison :
    (∀ s, integerProjection a referenceForm (integerLiftStep a referenceForm s) = s.matrix⁻¹) ∧
    (Function.Injective (gridEmbedding a) ∧
      IntertwinesGenerators (gridEmbedding a) (rectangularFirst a referenceForm)
        (integerLiftStep a referenceForm) (generatorScalar (realIndex (rationalDiagonal a)))) ∧
    (Function.Injective (gridEmbedding referenceForm) ∧
      IntertwinesGenerators (gridEmbedding referenceForm) (rectangularSecond a referenceForm)
        (integerLiftStep a referenceForm) (generatorScalar (realIndex (rationalDiagonal a)))) :=
  pair_of_tensor_generators (gridEmbedding a) (gridEmbedding referenceForm)
    (gridEvaluation a) (gridEvaluation referenceForm)
    (gridEvaluation_injective a) (gridEvaluation_injective referenceForm)
    (gridEvaluation_embedding a) (gridEvaluation_embedding referenceForm)
    (gridEmbedding_surjective a) (gridEmbedding_surjective referenceForm)
    (rectangularFirst a referenceForm) (rectangularSecond a referenceForm)
    (integerProjection a referenceForm) (integerLiftStep a referenceForm)
    (integerLiftStep_projection a referenceForm) gaussGamma gaussGamma_productFormula
    (rectangular_first_tests a referenceForm) (rectangular_second_tests a referenceForm)


end ZInQ.Manuscript.RC.Metaplectic2
