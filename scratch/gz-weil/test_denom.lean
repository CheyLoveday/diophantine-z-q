import Mathlib.NumberTheory.ModularForms.SlashActions
open UpperHalfPlane ModularGroup
open scoped MatrixGroups
example (τ : ℍ) : UpperHalfPlane.denom (ModularGroup.T : GL (Fin 2) ℝ) τ = 1 := by
  rw [ModularGroup.denom_apply]
  simp [ModularGroup.coe_T]
