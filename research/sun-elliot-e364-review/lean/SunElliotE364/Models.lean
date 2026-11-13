import Mathlib

/-! Exact real-embedding form of the `Q(√2)` curve-model identification. -/

namespace SunElliotE364

/-- A fixed real square root of two. -/
noncomputable def rho : ℝ := Real.sqrt 2

noncomputable def modelD : ℝ := 3 - rho
noncomputable def modelEpsilon : ℝ := 3 - 2 * rho
noncomputable def modelD0 : ℝ := 75 - 53 * rho

/-- The source generator in the `d` model. -/
noncomputable def sourceX : ℝ := 57 / 8 - (7 / 2) * rho
noncomputable def sourceY : ℝ := -165 / 8 + (417 / 32) * rho

/-- Its displayed coordinates in the unit-transported model. -/
noncomputable def targetX : ℝ := 1641 / 8 - 1160 / 8 * rho
noncomputable def targetY : ℝ := -123720 / 32 + 87483 / 32 * rho

lemma rho_sq : rho ^ 2 = 2 := by
  unfold rho
  norm_num

lemma modelEpsilon_norm_one : modelEpsilon * (3 + 2 * rho) = 1 := by
  unfold modelEpsilon
  nlinarith [rho_sq]

lemma model_parameter_transport : modelEpsilon ^ 2 * modelD = modelD0 := by
  unfold modelEpsilon modelD modelD0
  nlinarith [rho_sq]

lemma source_on_curve : sourceY ^ 2 = sourceX ^ 3 - modelD ^ 2 * sourceX := by
  unfold sourceX sourceY modelD
  nlinarith [rho_sq]

lemma source_x_transport : modelEpsilon ^ 2 * sourceX = targetX := by
  unfold modelEpsilon sourceX targetX
  nlinarith [rho_sq]

lemma source_y_transport : modelEpsilon ^ 3 * sourceY = targetY := by
  unfold modelEpsilon sourceY targetY
  linear_combination (-417 / 4 * rho ^ 2 + 5073 / 8 * rho - 26475 / 16) * rho_sq

/-- The transported point has the transported curve equation. -/
theorem transported_model :
    modelEpsilon * (3 + 2 * rho) = 1 ∧
    modelEpsilon ^ 2 * modelD = modelD0 ∧
    modelEpsilon ^ 2 * sourceX = targetX ∧
    modelEpsilon ^ 3 * sourceY = targetY ∧
    targetY ^ 2 = targetX ^ 3 - modelD0 ^ 2 * targetX := by
  refine ⟨modelEpsilon_norm_one, model_parameter_transport, source_x_transport,
    source_y_transport, ?_⟩
  rw [← source_x_transport, ← source_y_transport, ← model_parameter_transport]
  calc
    (modelEpsilon ^ 3 * sourceY) ^ 2 =
        modelEpsilon ^ 6 * sourceY ^ 2 := by ring
    _ = modelEpsilon ^ 6 * (sourceX ^ 3 - modelD ^ 2 * sourceX) := by rw [source_on_curve]
    _ = (modelEpsilon ^ 2 * sourceX) ^ 3 -
        (modelEpsilon ^ 2 * modelD) ^ 2 * (modelEpsilon ^ 2 * sourceX) := by ring

end SunElliotE364
