import ZInQKernel.Contrib.CloudB3RC53.PairedFunctional.Proposition
import ZInQKernel.Contrib.CloudB3RC53.PairedFunctional.HeightOneLocal

/-!
# RC53 PairedFunctional: the primitive functional is integral at every height-one prime `𝔭 ≠ (2)`

Proposition `ex:arith-paired-functional`, second assertion (tex L3715–3719):

> For a scalar constituent with its primitive local conditions, its paired functional has an
> integral representative at every height-one prime `𝔭 ≠ (2)` of `Λ`, including `(t)` and `(t+2)`.
> These representatives have the same generic value for that primitive constituent.

proved in tex L3753–3765 (see `HeightOneLocal.lean`) and used again at tex L5183–5191.

Node:
* `PairedFunctionalHeightOne` (PROVED from the same `ELLIOT`/`GLUE` cone hypothesis as
  `PairedFunctionalIntegral`): at every height-one prime `𝔭 ≠ (2)` of `Λ`, over `R = Λ_𝔭`, if the
  cone of the comparison is homotopy equivalent to the sum of the base-changed local models at the
  active places (inertia minus one `−2`) and the moving place (inertia minus one `t` times a unit,
  with nonzero central Frobenius determinants), then the paired functional has an integral closed
  representative over `Λ_𝔭`, unique up to a coboundary.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.PairedFunctional

open CategoryTheory Limits PowerSeries

/-- The base change of a relation `DC = CA` of matrices along a ring map, for the associated
endomorphisms. -/
theorem toLin'_map_comm {R K : Type} [CommRing R] [CommRing K] (φ : R →+* K) {m : ℕ}
    {A C D : Matrix (Fin m) (Fin m) R} (hDC : D * C = C * A) :
    Matrix.toLin' (D.map φ) * Matrix.toLin' (C.map φ) =
      Matrix.toLin' (C.map φ) * Matrix.toLin' (A.map φ) := by
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul,
    ← Matrix.map_mul, ← Matrix.map_mul, hDC]

theorem isUnit_toLin'_of_det {K : Type} [CommRing K] {m : ℕ} {M : Matrix (Fin m) (Fin m) K}
    (h : IsUnit M.det) : IsUnit (Matrix.toLin' M) :=
  Matrix.isUnit_toLin'_iff.mpr ((Matrix.isUnit_iff_isUnit_det M).mpr h)

/-- The local hypothesis at a place of the primitive scalar constituent (tex L3755–3760): either
an active place (inertia minus one `C = −2`) or the moving place (inertia minus one `C = t · U`, `U`
invertible over `Λ`, with nonzero central Frobenius determinants if `𝔭 = (t)`). -/
def PrimitivePlace (p : Ideal Lam) {m : ℕ} (A C D : Matrix (Fin m) (Fin m) Lam) : Prop :=
  C = (-2 : Lam) • 1 ∨
    ∃ U : Matrix (Fin m) (Fin m) Lam, IsUnit U.det ∧ C = (X : Lam) • U ∧
      (p = Ideal.span {(X : Lam)} → constantCoeff A.det ≠ 0 ∧ constantCoeff D.det ≠ 0)

/-- At a place of the primitive constituent, the base change to `Λ_𝔭` (`𝔭 ≠ (2)` of height one)
has Frobenius units or an inertia unit (tex L3755–3760). PROVED. -/
theorem primitivePlace_units (p : Ideal Lam) [p.IsPrime] (hp : p.height = 1)
    (hne : p ≠ Ideal.span {(2 : Lam)}) {m : ℕ} {A Cm D : Matrix (Fin m) (Fin m) Lam}
    (hplace : PrimitivePlace p A Cm D) :
    let φ := algebraMap Lam (Localization.AtPrime p)
    (IsUnit (Matrix.toLin' (A.map φ)) ∧ IsUnit (Matrix.toLin' (D.map φ))) ∨
      IsUnit (Matrix.toLin' (Cm.map φ)) := by
  intro φ
  have hdet : ∀ (M : Matrix (Fin m) (Fin m) Lam), (M.map φ).det = φ M.det := fun M => by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
  rcases hplace with hC | ⟨U, hU, hC, hcen⟩
  · obtain ⟨-, -, h2⟩ := activeInertiaUnit_proof p hp hne
    refine Or.inr (isUnit_toLin'_of_det ?_)
    rw [hdet, hC, Matrix.det_smul, Matrix.det_one, mul_one, map_pow]
    exact h2.pow _
  · by_cases ht : p = Ideal.span {(X : Lam)}
    · obtain ⟨hA0, hD0⟩ := hcen ht
      subst ht
      obtain ⟨hf, -⟩ := centralDeterminantUnit_proof
      refine Or.inl ⟨isUnit_toLin'_of_det ?_, isUnit_toLin'_of_det ?_⟩
      · rw [hdet]; exact hf _ hA0
      · rw [hdet]; exact hf _ hD0
    · obtain ⟨-, hX⟩ := movingInertiaUnit_proof p hp ht
      refine Or.inr (isUnit_toLin'_of_det ?_)
      rw [hdet, hC, Matrix.det_smul, map_mul, map_pow]
      exact (hX.pow _).mul (hU.map φ)

/-- **The primitive paired functional is integral at every height-one prime `𝔭 ≠ (2)`, including
`(t)` and `(t+2)`** (tex L3715–3719, proof L3753–3765; reused at L5183–5191). Let `𝔭 ≠ (2)` be a
height-one prime of `Λ`, `R = Λ_𝔭`, and let the comparison `j : C' → C` over `R` have cone homotopy
equivalent to the sum of the (shifted) base changes to `R` of finitely many tame local models over
`Λ` at the places of the primitive constituent (`PrimitivePlace`; `ELLIOT`/`GLUE` cone hypothesis,
tex L3842–3846, as in `PairedFunctionalIntegral`). Then there is a homotopy equivalence `e` over
`R` with `e.hom = j`, `z^⊥ = e.inv(c z)` is a cocycle, `j z^⊥ − c z` is a boundary, `λ_z` is closed,
and any other such `e'` changes `λ_z` by a coboundary (the same generic value).
Classification: PROVED (from the stated cone hypothesis). -/
def PairedFunctionalHeightOne : Prop :=
  ∀ (p : Ideal Lam) [p.IsPrime], p.height = 1 → p ≠ Ideal.span {(2 : Lam)} →
    let R := Localization.AtPrime p
    let φ := algebraMap Lam R
    ∀ (CU C' C Z : CochainComplex (ModuleCat.{0} R) ℤ) (j : C' ⟶ C) (c : Z ⟶ C) (z : Z.X 1)
      (pd1 : CU.X 1 →ₗ[R] C'.X 2 →ₗ[R] R) (pd2 : CU.X 2 →ₗ[R] C'.X 1 →ₗ[R] R)
      (pd3 : CU.X 3 →ₗ[R] C'.X 0 →ₗ[R] R) (ε ε' : R)
      (ι : Type) [Fintype ι] (m : ι → ℕ) (A Cm D : ∀ v, Matrix (Fin (m v)) (Fin (m v)) Lam)
      (hDC : ∀ v, D v * Cm v = Cm v * A v) (n : ι → ℤ),
      (∀ v, PrimitivePlace p (A v) (Cm v) (D v)) →
      Nonempty (HomotopyEquiv (CochainComplex.mappingCone j)
        (⨁ fun v => (tameComplex (Matrix.toLin' ((A v).map φ)) (Matrix.toLin' ((Cm v).map φ))
          (Matrix.toLin' ((D v).map φ)) (toLin'_map_comm φ (hDC v)))⟦n v⟧)) →
      (Z.d 1 2).hom z = 0 →
      (∀ w y, pd2 ((CU.d 1 2).hom w) y = ε * pd1 w ((C'.d 1 2).hom y)) →
      (∀ w y, pd2 w ((C'.d 0 1).hom y) = ε' * pd3 ((CU.d 2 3).hom w) y) →
      ∃ e : HomotopyEquiv C' C, e.hom = j ∧
        (C'.d 1 2).hom ((e.inv.f 1).hom ((c.f 1).hom z)) = 0 ∧
        (∃ b : C.X 0,
          (j.f 1).hom ((e.inv.f 1).hom ((c.f 1).hom z)) - (c.f 1).hom z = (C.d 0 1).hom b) ∧
        (∀ w : CU.X 1, pairedFunctional pd2 e.inv ((c.f 1).hom z) ((CU.d 1 2).hom w) = 0) ∧
        ∀ e' : HomotopyEquiv C' C, e'.hom = j → ∃ y : C'.X 0, ∀ w : CU.X 2,
          pairedFunctional pd2 e.inv ((c.f 1).hom z) w -
            pairedFunctional pd2 e'.inv ((c.f 1).hom z) w = ε' * pd3 ((CU.d 2 3).hom w) y

theorem pairedFunctionalHeightOne_proof : PairedFunctionalHeightOne := by
  intro p _ hp hne R φ CU C' C Z j c z pd1 pd2 pd3 ε ε' ι _ m A Cm D hDC n hplace hcone hz hL1 hL2
  have hunit := fun v => primitivePlace_units p hp hne (hplace v)
  exact pairedFunctionalIntegral_proof R CU C' C Z j c z pd1 pd2 pd3 ε ε' ι
    (fun v => Fin (m v) → R) (fun v => Matrix.toLin' ((A v).map φ))
    (fun v => Matrix.toLin' ((Cm v).map φ)) (fun v => Matrix.toLin' ((D v).map φ))
    (fun v => toLin'_map_comm φ (hDC v)) n hunit hcone hz hL1 hL2

/-- **Non-vacuity of the cone hypothesis of `PairedFunctionalHeightOne`**: at every height-one
prime `𝔭 ≠ (2)` and for every family of primitive places, the comparison `j = 𝟙` satisfies it
(both sides are contractible). PROVED. -/
theorem heightOne_cone_hypothesis_satisfiable (p : Ideal Lam) [p.IsPrime] (hp : p.height = 1)
    (hne : p ≠ Ideal.span {(2 : Lam)}) (C : CochainComplex (ModuleCat.{0} (Localization.AtPrime p)) ℤ)
    (ι : Type) [Fintype ι] (m : ι → ℕ) (A Cm D : ∀ v, Matrix (Fin (m v)) (Fin (m v)) Lam)
    (hDC : ∀ v, D v * Cm v = Cm v * A v) (n : ι → ℤ) (hplace : ∀ v, PrimitivePlace p (A v) (Cm v) (D v)) :
    Nonempty (HomotopyEquiv (CochainComplex.mappingCone (𝟙 C))
      (⨁ fun v => (tameComplex (Matrix.toLin' ((A v).map (algebraMap Lam (Localization.AtPrime p))))
        (Matrix.toLin' ((Cm v).map (algebraMap Lam (Localization.AtPrime p))))
        (Matrix.toLin' ((D v).map (algebraMap Lam (Localization.AtPrime p))))
        (toLin'_map_comm _ (hDC v)))⟦n v⟧)) :=
  cone_hypothesis_satisfiable _ C ι _ _ _ _ _
    (fun v => primitivePlace_units p hp hne (hplace v)) n

end ZInQ.Contrib.CloudB3RC53.PairedFunctional
