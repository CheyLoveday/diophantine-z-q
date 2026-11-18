import Mathlib

/-!
# RC53 PairedFunctional: the central Frobenius determinants at the moving prime are nonzero

Proof of Proposition `ex:arith-paired-functional`, tex L3763–3764 ("at `(t)` the nonzero central
Frobenius determinants give integral adjugate contractions"), and tex L5185–5186 ("at `(t)`, where
the central Frobenius determinants are nonzero and hence units in `R`").

At `t = 0` the moving character is trivial, so at the moving prime `r` the Frobenius `Φ` acts on
the rank-two coefficient module through `±Frob_r` on `T₂E`, with characteristic polynomial
`x² − a x + r`, `a = ±a_r`, and inertia acts trivially (`g = 1`, so `N_r(g) = r`). The two central
determinants of the model (4.4) are `det(Φ − 1) = 1 − a + r` and `det(Φ − r) = r (r + 1 − a)`.

`ELLIOT` (gap, tex L3763–3764, L5185–5186): the text asserts that these determinants are nonzero
without giving the reason. We fill it with the Hasse bound `a_r² ≤ 4r` (Hasse's theorem for the
good reduction of `E` at `r`; this is not cited at these lines; locator UNVERIFIED), taken as an
explicit hypothesis `hHasse` below: for `r ≥ 2`, `(r + 1)² − 4r = (r − 1)² > 0`, so `a ≠ r + 1`.

Node (PROVED from the stated Hasse hypothesis):
* `CentralFrobeniusDeterminantsNonzero`: for `Φ ∈ M₂(ℤ)` with `det Φ = r ≥ 2` and
  `(tr Φ)² ≤ 4r`, `det(Φ − 1) ≠ 0` and `det(Φ − r) ≠ 0`.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.PairedFunctional

open Matrix

/-- For a `2 × 2` matrix, `det(Φ − x) = x² − (tr Φ) x + det Φ`. -/
theorem det_sub_scalar_fin_two (Φ : Matrix (Fin 2) (Fin 2) ℤ) (x : ℤ) :
    (Φ - x • (1 : Matrix (Fin 2) (Fin 2) ℤ)).det = x ^ 2 - Φ.trace * x + Φ.det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two, Matrix.trace_fin_two]
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
    Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1), Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0),
    mul_zero, sub_zero]
  ring

/-- **The central Frobenius determinants at the moving prime are nonzero** (tex L3763–3764,
L5185–5186; `ELLIOT` gap filled by the Hasse bound, taken as the hypothesis `hHasse`). For
`Φ ∈ M₂(ℤ)` with `det Φ = r`, `r ≥ 2` and `(tr Φ)² ≤ 4r`: `det(Φ − 1) = 1 − tr Φ + r ≠ 0` and
`det(Φ − r) = r (r + 1 − tr Φ) ≠ 0`. Classification: PROVED (from `hHasse`). -/
def CentralFrobeniusDeterminantsNonzero : Prop :=
  ∀ (Φ : Matrix (Fin 2) (Fin 2) ℤ) (r : ℤ), Φ.det = r → 2 ≤ r → (hHasse : Φ.trace ^ 2 ≤ 4 * r) →
    (Φ - (1 : Matrix (Fin 2) (Fin 2) ℤ)).det ≠ 0 ∧
    (Φ - r • (1 : Matrix (Fin 2) (Fin 2) ℤ)).det ≠ 0

theorem centralFrobeniusDeterminantsNonzero_proof : CentralFrobeniusDeterminantsNonzero := by
  intro Φ r hdet hr hHasse
  have key : Φ.trace ≠ r + 1 := by
    intro h
    rw [h] at hHasse
    nlinarith
  have h1 : (Φ - (1 : Matrix (Fin 2) (Fin 2) ℤ)).det = 1 - Φ.trace + r := by
    have := det_sub_scalar_fin_two Φ 1
    rw [one_smul] at this
    rw [this, hdet]; ring
  refine ⟨?_, ?_⟩
  · rw [h1]; intro h; exact key (by linarith)
  · rw [det_sub_scalar_fin_two, hdet]
    have : r ^ 2 - Φ.trace * r + r = r * (r + 1 - Φ.trace) := by ring
    rw [this]
    exact mul_ne_zero (by omega) (fun h => key (by linarith))

/-- Non-vacuity: `Φ = [[0, −2], [1, 0]]` (trace `0`, determinant `2`) satisfies the hypotheses. -/
theorem centralFrobenius_example :
    (!![0, -2; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).det = 2 ∧
    (!![0, -2; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 ≤ 4 * 2 := by
  constructor
  · rw [Matrix.det_fin_two_of]; norm_num
  · rw [Matrix.trace_fin_two_of]; norm_num

end ZInQ.Contrib.CloudB3RC53.PairedFunctional
