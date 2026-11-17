import Mathlib

/-!
# RC53 PairedFunctional: the closed functional in matrix form

Definition `ex:arith-coordinate` (tex L3882–3892) and its consumers use the paired functional of
Proposition `ex:arith-paired-functional` (tex L3704–3880) on a complex whose degrees one and two
are free of rank `n`, with degree-one differential a matrix `D`: a closed degree-two functional is a
row vector `w` with `w D = 0` ("`λ D = 0`"). This file records that translation, and its
compatibility with ring maps (integral representatives specialize to the generic functional).

Nodes (PROVED):
* `ClosedFunctionalMatrixForm` (tex L3752–3754, L3882–3886): an `S`-linear functional `λ` on `Sⁿ`
  vanishing on the image of `D` is `x ↦ w · x` for the integral row vector `w = (λ(e_i))_i`, and
  `w D = 0`; conversely such a `w` gives a closed functional.
* `ClosedFunctionalBaseChange` (tex L3755–3758, "representatives built at distinct localizations
  define the same generic functional"): under a ring map `φ : S → K`, an integral closed row vector
  maps to a closed row vector for `φ(D)`.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.PairedFunctional

open Matrix

/-- **A closed functional on `Sⁿ` is an integral row vector `w` with `w D = 0`** (tex L3752–3754,
L3882–3886). For every commutative ring `S`, matrix `D : Sⁿˣⁿ` (the differential from degree one to
degree two) and `S`-linear `λ : Sⁿ → S` with `λ(D x) = 0` for all `x`, the vector
`w = (λ(e_i))_i` has entries in `S`, satisfies `w ᵥ* D = 0`, and `λ x = w ⬝ᵥ x`; conversely every
`w` with `w ᵥ* D = 0` defines such a closed functional. Classification: PROVED. -/
def ClosedFunctionalMatrixForm : Prop :=
  ∀ (S : Type) [CommRing S] (n : ℕ) (D : Matrix (Fin n) (Fin n) S),
    (∀ lam : (Fin n → S) →ₗ[S] S, (∀ x, lam (D *ᵥ x) = 0) →
      ∃ w : Fin n → S, w ᵥ* D = 0 ∧ ∀ x, lam x = w ⬝ᵥ x) ∧
    (∀ w : Fin n → S, w ᵥ* D = 0 → ∀ x, w ⬝ᵥ (D *ᵥ x) = 0)

theorem closedFunctionalMatrixForm_proof : ClosedFunctionalMatrixForm := by
  intro S _ n D
  refine ⟨fun lam hlam => ?_, fun w hw x => ?_⟩
  · set w : Fin n → S := fun i => lam (Pi.single i 1) with hwdef
    have hrep : ∀ x, lam x = w ⬝ᵥ x := by
      intro x
      conv_lhs => rw [show x = ∑ i, x i • Pi.single i (1 : S) from by
        ext j; simp [Finset.sum_apply, Pi.single_apply]]
      simp only [map_sum, map_smul, smul_eq_mul, dotProduct, hwdef]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    refine ⟨w, ?_, hrep⟩
    ext j
    have h := hlam (Pi.single j 1)
    rw [hrep, dotProduct_mulVec] at h
    simpa [Matrix.vecMul, dotProduct, Pi.single_apply] using h
  · rw [dotProduct_mulVec, hw, zero_dotProduct]

/-- **Closed integral row vectors specialize** (tex L3755–3758): for a ring map `φ : S → K` and a
closed integral row vector `w` (`w ᵥ* D = 0`), the image `φ ∘ w` is closed for `φ(D)`.
Classification: PROVED. -/
def ClosedFunctionalBaseChange : Prop :=
  ∀ (S K : Type) [CommRing S] [CommRing K] (φ : S →+* K) (n : ℕ) (D : Matrix (Fin n) (Fin n) S)
    (w : Fin n → S), w ᵥ* D = 0 → (fun i => φ (w i)) ᵥ* D.map φ = 0

theorem closedFunctionalBaseChange_proof : ClosedFunctionalBaseChange := by
  intro S K _ _ φ n D w hw
  have : (fun i => φ (w i)) ᵥ* D.map φ = fun j => φ ((w ᵥ* D) j) := by
    ext j
    simp [Matrix.vecMul, dotProduct, map_sum, map_mul]
  rw [this, hw]
  ext j; simp

end ZInQ.Contrib.CloudB3RC53.PairedFunctional
