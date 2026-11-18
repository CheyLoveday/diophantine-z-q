import ZInQKernel.Contrib.CloudB3RC53.PairedFunctional.LocalModel
import ZInQKernel.Contrib.CloudB3RC53.PairedFunctional.Lambda

/-!
# RC53 PairedFunctional: the primitive local contractions at every height-one prime `𝔭 ≠ (2)`

Proof of Proposition `ex:arith-paired-functional`, tex L3753–3765 (the scalar height-one
assertion), and its reuse in the height-one regularity paragraph of
`ex:limits-uniform-lower-bound`, tex L5183–5188:

> For the height-one assertion take the scalar primitive constituent. Its active primes are
> precisely the primes ramified in that constituent, so inertia minus one is `−2`, a unit at
> `𝔭 ≠ (2)`. At the moving prime inertia minus one is invertible unless `𝔭 = (t)`; at `(t)` the
> nonzero central Frobenius determinants give integral adjugate contractions. In particular
> `(t+2)` is treated by the inertia contraction.

The local models (4.4) are taken over `Λ = ℤ₂[[t]]` with matrices `A = Φ − 1`, `C = g − 1`,
`D = Φ − N(g)` acting on `Λⁿ`, subject to `DC = CA`, and base-changed to `R = Λ_𝔭`.

Nodes (PROVED):
* `ActivePlaceContraction` (tex L3755–3757): if `C = −2`, the base change to `Λ_𝔭` is contracted
  by the inertia contraction at every height-one prime `𝔭 ≠ (2)`.
* `MovingPlaceContraction` (tex L3757–3760): if `C = t · U` with `U` invertible over `Λ`, the base
  change to `Λ_𝔭` is contracted at every height-one prime `𝔭 ≠ (2)`: by the inertia contraction if
  `𝔭 ≠ (t)`, and by the adjugate Frobenius contraction at `𝔭 = (t)` provided the central Frobenius
  determinants `det A(0)`, `det D(0)` are nonzero.
* `QuadraticSpecializationsCovered` (tex L3760, non-vacuity): both nodes apply at `(t)` and `(t+2)`,
  and at `(t+2)` the moving place uses the inertia contraction.

Unused good primes keep the unramified condition and need no contraction (tex L3760–3763); they do
not enter here.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.PairedFunctional

open PowerSeries

/-- The tame local model over a commutative ring `R`, given by matrices, is contracted by the
inertia contraction when `det C` is a unit (matrix form of `InertiaContraction`). -/
theorem matrix_inertia_contraction {R : Type} [CommRing R] {n : ℕ}
    (A C D : Matrix (Fin n) (Fin n) R) (hC : IsUnit C.det) (hDC : D * C = C * A) :
    IsContraction (tameD0 (Matrix.toLin' A) (Matrix.toLin' C))
      (tameD1 (Matrix.toLin' C) (Matrix.toLin' D))
      (inertH1 (Matrix.toLin' C)) (inertH2 (Matrix.toLin' C)) := by
  have uC : IsUnit (Matrix.toLin' C) :=
    Matrix.isUnit_toLin'_iff.mpr ((Matrix.isUnit_iff_isUnit_det C).mpr hC)
  have hDC' : Matrix.toLin' D * Matrix.toLin' C = Matrix.toLin' C * Matrix.toLin' A := by
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul,
      hDC]
  exact inertiaContraction_proof R (Fin n → R) _ _ _ uC hDC'

/-- **Active places of the primitive constituent** (tex L3755–3757; L5184–5185): if inertia minus
one is `C = −2`, then at every height-one prime `𝔭 ≠ (2)` of `Λ` the local model base-changed to
`Λ_𝔭` is contracted by the inertia contraction `h¹(v, w) = C⁻¹w`, `h²(u) = (−C⁻¹u, 0)`.
Classification: PROVED. -/
def ActivePlaceContraction : Prop :=
  ∀ (p : Ideal Lam) [p.IsPrime], p.height = 1 → p ≠ Ideal.span {(2 : Lam)} →
    ∀ (n : ℕ) (A C D : Matrix (Fin n) (Fin n) Lam), D * C = C * A → C = (-2 : Lam) • 1 →
      let φ := algebraMap Lam (Localization.AtPrime p)
      IsContraction (tameD0 (Matrix.toLin' (A.map φ)) (Matrix.toLin' (C.map φ)))
        (tameD1 (Matrix.toLin' (C.map φ)) (Matrix.toLin' (D.map φ)))
        (inertH1 (Matrix.toLin' (C.map φ))) (inertH2 (Matrix.toLin' (C.map φ)))

theorem activePlaceContraction_proof : ActivePlaceContraction := by
  intro p _ hp hne n A C D hDC hC φ
  obtain ⟨-, -, h2⟩ := activeInertiaUnit_proof p hp hne
  apply matrix_inertia_contraction
  · have : (C.map φ).det = φ C.det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply]
    rw [this, hC, Matrix.det_smul, Matrix.det_one, mul_one, map_pow]
    exact h2.pow _
  · rw [← Matrix.map_mul, ← Matrix.map_mul, hDC]

/-- **The moving place of the primitive constituent** (tex L3757–3760; L5185–5187): if inertia
minus one is `C = t · U` with `U` invertible over `Λ` ("moving-prime inertia minus one is `t` times
a unit", tex L3753–3754), then at every height-one prime `𝔭 ≠ (2)` of `Λ` the local model
base-changed to `Λ_𝔭` has an integral contraction: the inertia contraction if `𝔭 ≠ (t)`, and the
adjugate Frobenius contraction at `𝔭 = (t)` when the central Frobenius determinants are nonzero
(`det A` and `det D` have nonzero constant coefficient). Classification: PROVED. -/
def MovingPlaceContraction : Prop :=
  ∀ (p : Ideal Lam) [p.IsPrime], p.height = 1 → p ≠ Ideal.span {(2 : Lam)} →
    ∀ (n : ℕ) (A C D U : Matrix (Fin n) (Fin n) Lam), D * C = C * A → IsUnit U.det →
      C = (X : Lam) • U →
      (p = Ideal.span {(X : Lam)} → constantCoeff A.det ≠ 0 ∧ constantCoeff D.det ≠ 0) →
      let φ := algebraMap Lam (Localization.AtPrime p)
      ∃ (h1 : (Fin n → Localization.AtPrime p) × (Fin n → Localization.AtPrime p) →ₗ[_]
          (Fin n → Localization.AtPrime p))
        (h2 : (Fin n → Localization.AtPrime p) →ₗ[Localization.AtPrime p]
          (Fin n → Localization.AtPrime p) × (Fin n → Localization.AtPrime p)),
        IsContraction (tameD0 (Matrix.toLin' (A.map φ)) (Matrix.toLin' (C.map φ)))
          (tameD1 (Matrix.toLin' (C.map φ)) (Matrix.toLin' (D.map φ))) h1 h2

theorem movingPlaceContraction_proof : MovingPlaceContraction := by
  intro p _ hp hne n A C D U hDC hU hC hcen φ
  have hDC' : D.map φ * C.map φ = C.map φ * A.map φ := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hDC]
  have hdet : ∀ M : Matrix (Fin n) (Fin n) Lam, (M.map φ).det = φ M.det := fun M => by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
  by_cases ht : p = Ideal.span {(X : Lam)}
  · -- at `(t)`: the adjugate Frobenius contraction
    obtain ⟨hA0, hD0⟩ := hcen ht
    subst ht
    obtain ⟨-, hmat⟩ := centralDeterminantUnit_proof
    have uA : IsUnit (A.map φ).det := (Matrix.isUnit_iff_isUnit_det _).mp (hmat n A hA0)
    have uD : IsUnit (D.map φ).det := (Matrix.isUnit_iff_isUnit_det _).mp (hmat n D hD0)
    obtain ⟨-, -, hc⟩ := matrixFrobeniusContraction_proof _ (Fin n) _ _ _ uA uD hDC'
    exact ⟨_, _, hc⟩
  · -- `𝔭 ≠ (t)`: `t` is a unit, so `C` is invertible
    obtain ⟨-, hX⟩ := movingInertiaUnit_proof p hp ht
    refine ⟨_, _, matrix_inertia_contraction _ _ _ ?_ hDC'⟩
    rw [hdet, hC, Matrix.det_smul, map_mul, map_pow]
    exact (hX.pow _).mul (hU.map φ)

/-- **Non-vacuity: both quadratic specializations are covered** (tex L3760: "In particular `(t+2)`
is treated by the inertia contraction"; L5190–5191). The primes `(t)` and `(t+2)` are height-one
primes `≠ (2)`, so `ActivePlaceContraction` and `MovingPlaceContraction` apply there; at `(t+2)` the
moving place is contracted by the inertia contraction (no central determinant hypothesis), for
every model with `C = t · U`. Classification: PROVED. -/
def QuadraticSpecializationsCovered : Prop :=
  letI : (Ideal.span {(X + 2 : Lam)}).IsPrime := span_X_add_two_isPrime
  ∀ (n : ℕ) (A C D U : Matrix (Fin n) (Fin n) Lam), D * C = C * A → IsUnit U.det →
    C = (X : Lam) • U →
    let φ := algebraMap Lam (Localization.AtPrime (Ideal.span {(X + 2 : Lam)}))
    IsContraction (tameD0 (Matrix.toLin' (A.map φ)) (Matrix.toLin' (C.map φ)))
      (tameD1 (Matrix.toLin' (C.map φ)) (Matrix.toLin' (D.map φ)))
      (inertH1 (Matrix.toLin' (C.map φ))) (inertH2 (Matrix.toLin' (C.map φ)))

theorem quadraticSpecializationsCovered_proof : QuadraticSpecializationsCovered := by
  let _ : (Ideal.span {(X + 2 : Lam)}).IsPrime := span_X_add_two_isPrime
  intro n A C D U hDC hU hC φ
  obtain ⟨-, -, -, -, -, hX⟩ := quadraticPrimesHeightOne_proof
  apply matrix_inertia_contraction
  · have : (C.map φ).det = φ C.det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply]
    rw [this, hC, Matrix.det_smul, map_mul, map_pow]
    exact (hX.pow _).mul (hU.map φ)
  · rw [← Matrix.map_mul, ← Matrix.map_mul, hDC]

end ZInQ.Contrib.CloudB3RC53.PairedFunctional
