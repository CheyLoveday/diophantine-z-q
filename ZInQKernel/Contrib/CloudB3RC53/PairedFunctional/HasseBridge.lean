import ZInQKernel.Contrib.CloudB3RC53.PairedFunctional.CentralDeterminants
import ZInQKernel.Contrib.CloudB3RC53.WeilIsogeny.HasseProof

/-!
# The Hasse hypothesis of `CentralDeterminants.lean` from the proved Hasse bound

`CentralFrobeniusDeterminantsNonzero` takes the hypothesis `hHasse : (tr Φ)² ≤ 4r`. For the
Frobenius matrix of an elliptic curve over a finite field with `r` elements, `tr Φ = ±a` with
`a = r + 1 − #W(𝔽)`, and the Hasse bound `|#W(𝔽) − r − 1| ≤ 2√r` is PROVED in the project
(`WeilIsogeny.hasseBoundProved_proof`). This file derives `hHasse` from it.

* `hHasse_of_trace` (PROVED): if `tr Φ = ±(r + 1 − #W(𝔽))` for an elliptic curve `W` over a finite
  field with `r` elements, then `(tr Φ)² ≤ 4r`.
* `centralFrobeniusDeterminants_of_trace` (PROVED): the conclusion of
  `centralFrobeniusDeterminantsNonzero_proof` with `hHasse` discharged.

**Classification.** PROVED.
-/

namespace ZInQ.Contrib.CloudB3RC53.PairedFunctional

/-- **`hHasse` from the proved Hasse bound** (PROVED). -/
theorem hHasse_of_trace (F : Type) [Field F] [Fintype F] (W : WeierstrassCurve F) [W.IsElliptic]
    (Φ : Matrix (Fin 2) (Fin 2) ℤ)
    (htr : Φ.trace = (Fintype.card F : ℤ) + 1 - Nat.card W.toAffine.Point ∨
      Φ.trace = -((Fintype.card F : ℤ) + 1 - Nat.card W.toAffine.Point)) :
    Φ.trace ^ 2 ≤ 4 * (Fintype.card F : ℤ) := by
  have h := ZInQ.Contrib.CloudB3RC53.WeilIsogeny.hasseBoundProved_proof F W
  have hsq : ((Nat.card W.toAffine.Point : ℝ) - Fintype.card F - 1) ^ 2 ≤
      4 * (Fintype.card F : ℝ) := by
    have h2 := sq_le_sq' (abs_le.mp h).1 (abs_le.mp h).2
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)] at h2
    linarith
  have key : (((Fintype.card F : ℤ) + 1 - Nat.card W.toAffine.Point) ^ 2 : ℤ) ≤
      4 * (Fintype.card F : ℤ) := by
    have : ((((Fintype.card F : ℤ) + 1 - Nat.card W.toAffine.Point) ^ 2 : ℤ) : ℝ) ≤
        ((4 * (Fintype.card F : ℤ) : ℤ) : ℝ) := by
      push_cast
      nlinarith [hsq]
    exact_mod_cast this
  rcases htr with h' | h'
  · rw [h']; exact key
  · rw [h', neg_sq]; exact key

/-- **The central Frobenius determinants with `hHasse` discharged** (PROVED). -/
theorem centralFrobeniusDeterminants_of_trace (F : Type) [Field F] [Fintype F]
    (W : WeierstrassCurve F) [W.IsElliptic] (Φ : Matrix (Fin 2) (Fin 2) ℤ)
    (hdet : Φ.det = Fintype.card F) (hr : 2 ≤ (Fintype.card F : ℤ))
    (htr : Φ.trace = (Fintype.card F : ℤ) + 1 - Nat.card W.toAffine.Point ∨
      Φ.trace = -((Fintype.card F : ℤ) + 1 - Nat.card W.toAffine.Point)) :
    (Φ - (1 : Matrix (Fin 2) (Fin 2) ℤ)).det ≠ 0 ∧
      (Φ - (Fintype.card F : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ)).det ≠ 0 :=
  centralFrobeniusDeterminantsNonzero_proof Φ _ hdet hr (hHasse_of_trace F W Φ htr)

end ZInQ.Contrib.CloudB3RC53.PairedFunctional
