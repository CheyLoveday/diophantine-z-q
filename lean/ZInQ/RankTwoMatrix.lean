module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# A nonsingular element of a spanning additive subgroup of `2 × 2` matrices

Let `R` be a nontrivial commutative ring and let `S` be an additive subgroup of
`Matrix (Fin 2) (Fin 2) R` whose `R`-linear span is the whole matrix module.  Then some element
of `S` has nonzero determinant.  In particular this holds over every field `K`, with no
restriction on the characteristic (`RankTwoMatrix.exists_mem_det_ne_zero`).

This is the "span to a single element" step (lines 600-614) of the lemma `rd:rank-two` of the
frozen source `ring-determinants-frozen-4eaee875.tex`.  The arithmetic interface premises of that
lemma (additivity of the restricted evaluation image and fullness of its linear span) are the
hypotheses here; they are *not* proved in this file.

## Proof

The polar form of the `2 × 2` determinant,
`detPolar A B = A 0 0 * B 1 1 + B 0 0 * A 1 1 - A 0 1 * B 1 0 - B 0 1 * A 1 0`,
is bilinear (`detPolarBilin`) and satisfies `detPolar A B = det (A + B) - det A - det B`.
If every element of `S` had determinant zero, additive closure of `S` would make `detPolar`
vanish on `S × S`; bilinearity extends this to `span S × span S`, i.e. to all pairs of matrices,
contradicting the explicit evaluation `detPolar E₀₀ E₁₁ = 1`.  No division by `2` occurs, so the
argument is valid in characteristic `2`.

## Negative control

Additive closure cannot be dropped: the four matrix units span the matrix module, but each of them
is singular (`RankTwoMatrix.not_forall_set_span_eq_top_exists_det_ne_zero`).
-/

public section

namespace RankTwoMatrix

variable {R : Type*} [CommRing R]

/-- The polar (bilinear) form of the `2 × 2` determinant:
`detPolar A B = det (A + B) - det A - det B` (see `detPolar_eq`). -/
@[expose] def detPolar (A B : Matrix (Fin 2) (Fin 2) R) : R :=
  A 0 0 * B 1 1 + B 0 0 * A 1 1 - A 0 1 * B 1 0 - B 0 1 * A 1 0

/-- Polarization identity for the `2 × 2` determinant, valid over any commutative ring. -/
theorem detPolar_eq (A B : Matrix (Fin 2) (Fin 2) R) :
    detPolar A B = (A + B).det - A.det - B.det := by
  simp only [detPolar, Matrix.det_fin_two, Matrix.add_apply]
  ring

theorem detPolar_add_left (A A' B : Matrix (Fin 2) (Fin 2) R) :
    detPolar (A + A') B = detPolar A B + detPolar A' B := by
  simp only [detPolar, Matrix.add_apply]
  ring

theorem detPolar_add_right (A B B' : Matrix (Fin 2) (Fin 2) R) :
    detPolar A (B + B') = detPolar A B + detPolar A B' := by
  simp only [detPolar, Matrix.add_apply]
  ring

theorem detPolar_smul_left (r : R) (A B : Matrix (Fin 2) (Fin 2) R) :
    detPolar (r • A) B = r • detPolar A B := by
  simp only [detPolar, Matrix.smul_apply, smul_eq_mul]
  ring

theorem detPolar_smul_right (r : R) (A B : Matrix (Fin 2) (Fin 2) R) :
    detPolar A (r • B) = r • detPolar A B := by
  simp only [detPolar, Matrix.smul_apply, smul_eq_mul]
  ring

theorem detPolar_zero_left (B : Matrix (Fin 2) (Fin 2) R) : detPolar 0 B = 0 := by
  simp only [detPolar, Matrix.zero_apply]
  ring

theorem detPolar_zero_right (A : Matrix (Fin 2) (Fin 2) R) : detPolar A 0 = 0 := by
  simp only [detPolar, Matrix.zero_apply]
  ring

variable (R) in
/-- `detPolar` bundled as an `R`-bilinear map, certifying its bilinearity. -/
@[expose] def detPolarBilin :
    Matrix (Fin 2) (Fin 2) R →ₗ[R] Matrix (Fin 2) (Fin 2) R →ₗ[R] R :=
  LinearMap.mk₂ R detPolar detPolar_add_left detPolar_smul_left detPolar_add_right
    detPolar_smul_right

@[simp]
theorem detPolarBilin_apply (A B : Matrix (Fin 2) (Fin 2) R) :
    detPolarBilin R A B = detPolar A B :=
  rfl

/-- The explicit evaluation `detPolar E₀₀ E₁₁ = 1`, which holds over every commutative ring
(in particular in characteristic `2`). -/
theorem detPolar_E00_E11 :
    detPolar (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) R) !![0, 0; 0, 1] = 1 := by
  simp [detPolar]

/-- If every element of the additive subgroup `S` is singular, then the polar form of the
determinant vanishes on `span S × span S`. -/
theorem detPolar_eq_zero_of_mem_span (S : AddSubgroup (Matrix (Fin 2) (Fin 2) R))
    (hS : ∀ A ∈ S, A.det = 0) {A B : Matrix (Fin 2) (Fin 2) R}
    (hA : A ∈ Submodule.span R (S : Set (Matrix (Fin 2) (Fin 2) R)))
    (hB : B ∈ Submodule.span R (S : Set (Matrix (Fin 2) (Fin 2) R))) :
    detPolar A B = 0 := by
  induction hA, hB using Submodule.span_induction₂ with
  | mem_mem x y hx hy =>
    rw [detPolar_eq, hS x hx, hS y hy, hS (x + y) (S.add_mem hx hy), sub_zero, sub_zero]
  | zero_left y _ => exact detPolar_zero_left y
  | zero_right x _ => exact detPolar_zero_right x
  | add_left x y z _ _ _ h₁ h₂ => rw [detPolar_add_left, h₁, h₂, add_zero]
  | add_right x y z _ _ _ h₁ h₂ => rw [detPolar_add_right, h₁, h₂, add_zero]
  | smul_left r x y _ _ h => rw [detPolar_smul_left, h, smul_zero]
  | smul_right r x y _ _ h => rw [detPolar_smul_right, h, smul_zero]

/-- Commutative-ring version: over a nontrivial commutative ring, an additive subgroup of
`2 × 2` matrices with full linear span contains a matrix of nonzero determinant. -/
theorem exists_mem_det_ne_zero_of_commRing [Nontrivial R]
    (S : AddSubgroup (Matrix (Fin 2) (Fin 2) R))
    (hS : Submodule.span R (S : Set (Matrix (Fin 2) (Fin 2) R)) = ⊤) :
    ∃ A ∈ S, Matrix.det A ≠ 0 := by
  refine Classical.byContradiction fun h => ?_
  have hdet : ∀ A ∈ S, A.det = 0 := fun A hA =>
    Classical.byContradiction fun hne => h ⟨A, hA, hne⟩
  have hmem : ∀ A : Matrix (Fin 2) (Fin 2) R,
      A ∈ Submodule.span R (S : Set (Matrix (Fin 2) (Fin 2) R)) := by
    intro A
    rw [hS]
    exact Submodule.mem_top
  have h1 := detPolar_eq_zero_of_mem_span S hdet (hmem !![1, 0; 0, 0]) (hmem !![0, 0; 0, 1])
  rw [detPolar_E00_E11] at h1
  exact one_ne_zero h1

/-- **Main helper (field version).**  Let `K` be any field (no characteristic restriction) and
`S` an additive subgroup of the `2 × 2` matrices over `K`.  If the `K`-linear span of `S` is the
whole matrix space, then `S` contains a matrix with nonzero determinant. -/
theorem exists_mem_det_ne_zero {K : Type*} [Field K]
    (S : AddSubgroup (Matrix (Fin 2) (Fin 2) K)) :
    Submodule.span K (S : Set (Matrix (Fin 2) (Fin 2) K)) = ⊤ →
    ∃ A ∈ S, Matrix.det A ≠ 0 :=
  exists_mem_det_ne_zero_of_commRing S

/-- The assigned target proposition, verbatim, as a closed statement.  It is proved by the bare
constant `@exists_mem_det_ne_zero`, so this declaration elaborates only because the type of
`exists_mem_det_ne_zero` is exactly the assigned type. -/
theorem rank_two_target :
    ∀ {K : Type*} [Field K]
      (S : AddSubgroup (Matrix (Fin 2) (Fin 2) K)),
      Submodule.span K (S : Set (Matrix (Fin 2) (Fin 2) K)) = ⊤ →
      ∃ A ∈ S, Matrix.det A ≠ 0 :=
  @exists_mem_det_ne_zero

/-! ### Negative control: additive closure is essential -/

/-- The set of the four matrix units `E₀₀, E₀₁, E₁₀, E₁₁`. -/
@[expose] def matrixUnits : Set (Matrix (Fin 2) (Fin 2) R) :=
  {!![1, 0; 0, 0], !![0, 1; 0, 0], !![0, 0; 1, 0], !![0, 0; 0, 1]}

/-- Every matrix unit is singular. -/
theorem det_eq_zero_of_mem_matrixUnits {A : Matrix (Fin 2) (Fin 2) R}
    (hA : A ∈ matrixUnits (R := R)) : A.det = 0 := by
  simp only [matrixUnits, Set.mem_insert_iff, Set.mem_singleton_iff] at hA
  rcases hA with rfl | rfl | rfl | rfl <;> simp

/-- The four matrix units span the matrix module. -/
theorem span_matrixUnits : Submodule.span R (matrixUnits (R := R)) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun A => ?_
  have hA : A = A 0 0 • !![1, 0; 0, 0] + A 0 1 • !![0, 1; 0, 0] + A 1 0 • !![0, 0; 1, 0]
      + A 1 1 • !![0, 0; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hA]
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_ <;>
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_) <;>
    simp [matrixUnits]

/-- Negative control: the analogue of the main helper for arbitrary spanning *sets* is false,
for every commutative ring, because the matrix units span but are all singular.  The missing
property is additive closure. -/
theorem not_forall_set_span_eq_top_exists_det_ne_zero :
    ¬ ∀ T : Set (Matrix (Fin 2) (Fin 2) R), Submodule.span R T = ⊤ → ∃ A ∈ T, A.det ≠ 0 := by
  intro h
  obtain ⟨A, hA, hdet⟩ := h matrixUnits span_matrixUnits
  exact hdet (det_eq_zero_of_mem_matrixUnits hA)

end RankTwoMatrix
