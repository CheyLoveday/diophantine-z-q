import ZInQKernel.Contrib.RC53Assist.NewformPeriodsDictionary.Dictionary

/-!
# RC53 ModularWeil: the Frobenius trace dictionary at good reduction

The proposition `GoodReductionFrobeniusTraceDictionaryQ` says the following. Let `E/ℚ` be
elliptic with good reduction at `p`, and let `ℓ ≠ p`. Then the Tate-module matrix of an
arithmetic Frobenius at `p` has trace `p + 1 − #Ẽ(𝔽_p)` and determinant `p`, in every basis.
This file reduces that proposition to two sharply named classical inputs, stated in the library's
own objects.

* (R) `TateReductionComparison`: the reduction comparison of Tate modules. At good reduction an
  arithmetic Frobenius acts on `T_ℓ(E/\bar ℚ_p)` as the `p`-power Frobenius acts on
  `T_ℓ(Ẽ/\bar 𝔽_p)`.
* (FD) `FrobeniusTateDetForm`: the determinant form of Frobenius on `T_ℓ` of an elliptic curve
  over `𝔽_p`, `det(m − n π) = m² − a m n + p n²` with `a = p + 1 − #Ẽ(𝔽_p)`. It is the combination
  of two facts:
  * (D) the determinant of an endomorphism on `T_ℓ` is its degree;
  * (F) the degree form of `m − n π`.

## Results

* `trace_det_of_detForm` (`PROVED`): the linear algebra. For a `2 × 2` matrix `A`, if
  `det(m − n A) = m² − a m n + d n²` for all integers `m, n`, then `tr A = a` and `det A = d`.
* `redTate`, `frobTate`: the Tate module of a curve over `𝔽_p` over `\bar 𝔽_p`, and the `p`-power
  Frobenius on it. The latter is the Tate map of `Point.map` along `FiniteField.frobeniusAlgHom`.
* `goodReductionFrobeniusTraceDictionaryQ_of` (`PROVED` from (R) and (FD)): the target exactly as
  stated. The Tate matrix of `σ` is conjugate, through (R), to `π`, so the determinant form
  transfers. The linear algebra gives the trace and the determinant in every basis.

## The missing classical pieces

* (R): reduction on `E[ℓⁿ]` at good reduction is injective (prime-to-`p` torsion), bijective by
  counting, and Galois-equivariant. The arithmetic Frobenius acts on reduced coordinates as
  `x ↦ x^p`, by `IsArithmeticFrobeniusOnClosureQ`.
* (D): the Weil pairing compatibility `e(αP, αQ) = e(P, Q)^{deg α}`, through dual isogenies. The
  library has the Weil pairing for multiplication by `n`, but not dual isogenies.
* (F): the Frobenius isogeny with `deg π = p`, the separability of `1 − π` (its differential is
  `1`), `#ker(1 − π) = #Ẽ(𝔽_p)`, and the quadratic form `deg(m − n π)`. The library has isogeny
  degree, kernels, `card_ker_eq_degree_iff` and the group of homomorphisms with additive point
  maps.

Classification: `PROVED` from the named inputs; (R) and (FD) are stated, not proved.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ModularWeil

open Module NumberField IsDedekindDomain ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary
open scoped WeierstrassCurve WithZero

/-! ### Linear algebra: trace and determinant from the determinant form -/

/-- **Trace and determinant of a `2 × 2` matrix from `det(m − n A)`** (`PROVED`): if
`det(m • 1 − n • A) = m² − a m n + d n²` for all integers `m, n`, then `tr A = a` and
`det A = d`. -/
theorem trace_det_of_detForm {R : Type*} [CommRing R] (A : Matrix (Fin 2) (Fin 2) R) (a d : R)
    (h : ∀ m n : ℤ, Matrix.det ((m : R) • (1 : Matrix (Fin 2) (Fin 2) R) - (n : R) • A) =
      (m : R) ^ 2 - a * m * n + d * n ^ 2) :
    Matrix.trace A = a ∧ Matrix.det A = d := by
  have key : ∀ m n : ℤ, Matrix.det ((m : R) • (1 : Matrix (Fin 2) (Fin 2) R) - (n : R) • A) =
      (m : R) ^ 2 - Matrix.trace A * m * n + Matrix.det A * n ^ 2 := by
    intro m n
    rw [Matrix.det_fin_two, Matrix.det_fin_two, Matrix.trace_fin_two]
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
      Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
      Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), smul_eq_mul, mul_one, mul_zero]
    ring
  have hd : Matrix.det A = d := by
    have h1 := h 0 1
    rw [key] at h1
    simpa using h1
  refine ⟨?_, hd⟩
  have h2 := h 1 1
  rw [key, hd] at h2
  simp only [Int.cast_one, one_pow, mul_one] at h2
  linear_combination -h2

/-! ### The Frobenius endomorphism of the Tate module of a curve over `𝔽_p` -/

section Frobenius

open scoped Classical

variable (p : ℕ) [Fact p.Prime] (Et : WeierstrassCurve (ZMod p)) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The `ℓ`-adic Tate module of a curve over `𝔽_p`, over an algebraic closure of `𝔽_p`. -/
abbrev redTate : Type :=
  TauCeti.TateModule ℓ (Et.baseChange (AlgebraicClosure (ZMod p))).toAffine.Point

/-- **The `p`-power Frobenius endomorphism on the Tate module** of a curve over `𝔽_p`: the
coordinates of every torsion point are raised to the `p`-th power. -/
def frobTate : Module.End ℤ_[ℓ] (redTate p Et ℓ) :=
  TauCeti.TateModule.mapLinearMap
    (WeierstrassCurve.Affine.Point.map (W' := Et)
      (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p))))

end Frobenius

/-! ### The named inputs -/

open scoped Classical in
/-- **(FD) The determinant form of Frobenius on the Tate module** of an elliptic curve `Et` over
`𝔽_p` (Silverman, *The Arithmetic of Elliptic Curves*, V.2.3.1 and III.8.6). For `ℓ ≠ p` and all
integers `m, n`, `det(m − n π | T_ℓ Et) = m² − a m n + p n²` with `a = p + 1 − #Et(𝔽_p)`. It is the
combination of two classical facts:
* (D) the determinant of an endomorphism on `T_ℓ` is its degree (Weil pairing compatibility
  `e(αP, αQ) = e(P, Q)^{deg α}`);
* (F) the degree form `deg(m − n π) = m² − a m n + p n²`, from `deg π = p`, the separability of
  `1 − π`, `#ker(1 − π) = #Et(𝔽_p)` and the quadratic nature of the degree.

Stated, not proved. -/
def FrobeniusTateDetForm : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (Et : WeierstrassCurve (ZMod p)), Et.IsElliptic →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ p → ∀ m n : ℤ,
      LinearMap.det ((m : ℤ_[ℓ]) • (1 : Module.End ℤ_[ℓ] (redTate p Et ℓ)) -
          (n : ℤ_[ℓ]) • frobTate p Et ℓ) =
        (m : ℤ_[ℓ]) ^ 2 - (((p : ℤ) + 1 - (Nat.card Et.toAffine.Point : ℤ) : ℤ) : ℤ_[ℓ]) * m * n +
          (p : ℤ_[ℓ]) * n ^ 2

open scoped Classical in
/-- **(R) The reduction comparison of Tate modules** at a good prime `p ≠ ℓ` (Silverman VII.3.1
and VII.7.1): an arithmetic Frobenius `σ` of `ℚ_p` acts on `T_ℓ(E/\bar ℚ_p)` as the `p`-power
Frobenius `π` acts on `T_ℓ` of the reduction `Et/\bar 𝔽_p`, through a `ℤ_ℓ`-linear isomorphism.
(Reduction is injective on prime-to-`p` torsion at good reduction, bijective by counting, and
carries the arithmetic Frobenius to the `p`-power map on coordinates.) Stated, not proved. -/
def TateReductionComparison : Prop :=
  ∀ (E : WeierstrassCurve ℚ), E.IsElliptic →
    ∀ (p : ℕ) (hp : p.Prime), GoodReductionAt E (primeIdealQ p hp) →
      ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ p →
        ∀ (Γ : Type) [LinearOrderedCommGroupWithZero Γ]
          (w : Valuation (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)) Γ),
          (w.comap (algebraMap ((primeIdealQ p hp).adicCompletion ℚ)
            (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)))).IsEquiv
            (Valued.v : Valuation ((primeIdealQ p hp).adicCompletion ℚ) ℤᵐ⁰) →
          ∀ σ : AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ) ≃ₐ[
            (primeIdealQ p hp).adicCompletion ℚ]
              AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ),
            IsArithmeticFrobeniusOnClosureQ (primeIdealQ p hp) Γ w σ →
            ∃ e : TauCeti.TateModule ℓ
                ((E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).baseChange
                  (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ))).toAffine.Point ≃ₗ[ℤ_[ℓ]]
                @redTate p ⟨hp⟩ (reducedCurveModP E p hp) ℓ,
              ∀ x, e (WeierstrassCurve.tateModuleGaloisRepresentation
                  (E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)) ℓ σ x) =
                @frobTate p ⟨hp⟩ (reducedCurveModP E p hp) ℓ _ (e x)

/-! ### The dictionary from (R) and (FD) -/

open scoped Classical in
/-- **`GoodReductionFrobeniusTraceDictionaryQ` from the reduction comparison and the Frobenius
determinant form** (`PROVED` from (R) and (FD)). The trace and determinant of the Tate matrix of
an arithmetic Frobenius are computed through (R) from `π` on the reduction, and the linear algebra
`trace_det_of_detForm` turns the determinant form (FD) into `tr = p + 1 − #Et(𝔽_p)`, `det = p`. -/
theorem goodReductionFrobeniusTraceDictionaryQ_of (hR : TateReductionComparison)
    (hFD : FrobeniusTateDetForm) : GoodReductionFrobeniusTraceDictionaryQ := by
  intro E hE p hp hgood ℓ _ hℓ Γ _ w hw σ hσ b
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨e, he⟩ := hR E hE p hp hgood ℓ hℓ Γ w hw σ hσ
  set ρ := (E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).tateModuleGaloisRepresentation ℓ σ
  have hconj : (frobTate p (reducedCurveModP E p hp) ℓ) =
      (e : _ →ₗ[ℤ_[ℓ]] _) ∘ₗ ρ ∘ₗ (e.symm : _ →ₗ[ℤ_[ℓ]] _) := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := e.surjective y
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    exact (he x).symm
  refine trace_det_of_detForm _ _ _ fun m n => ?_
  have hm : (m : ℤ_[ℓ]) • (1 : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) -
      (n : ℤ_[ℓ]) • localTateMatrixQ E (primeIdealQ p hp) ℓ σ b =
      LinearMap.toMatrix b b ((m : ℤ_[ℓ]) • (1 : Module.End ℤ_[ℓ] _) - (n : ℤ_[ℓ]) • ρ) := by
    rw [map_sub, map_smul, map_smul, LinearMap.toMatrix_one]
    rfl
  rw [hm, LinearMap.det_toMatrix]
  have hc : (m : ℤ_[ℓ]) • (1 : Module.End ℤ_[ℓ] (redTate p (reducedCurveModP E p hp) ℓ)) -
      (n : ℤ_[ℓ]) • frobTate p (reducedCurveModP E p hp) ℓ =
      (e : _ →ₗ[ℤ_[ℓ]] _) ∘ₗ ((m : ℤ_[ℓ]) • (1 : Module.End ℤ_[ℓ] _) - (n : ℤ_[ℓ]) • ρ) ∘ₗ
        (e.symm : _ →ₗ[ℤ_[ℓ]] _) := by
    rw [hconj]
    refine LinearMap.ext fun y => ?_
    simp
  have hFD' := hFD p (reducedCurveModP E p hp) (reducedCurveModP_isElliptic E p hp hgood) ℓ hℓ m n
  rw [hc, LinearMap.det_conj] at hFD'
  rw [hFD']
  push_cast
  ring

end ZInQ.Contrib.CloudB3RC53.ModularWeil
