import ZInQKernel.Contrib.OneProof.RC.Height.Transfer
import ZInQKernel.Contrib.OneProof.RC.Height.FieldBaseChange
import ZInQKernel.Contrib.OneProof.RC.Height.FieldGalois
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Weierstrass

/-!
# Lane RC19 (height): base change from `ℚ`, Galois conjugation and descent

For a Weierstrass curve `W` over `ℚ` and a number field `K`, this file compares the canonical
heights of `W(ℚ)` and `W(K)` and records the Galois invariance of the height on `W(K)`. Heights are
the vendored Tau Ceti canonical heights, each relative to its own field (Mathlib's normalization
of `Height.AdmissibleAbsValues` on a number field counts every place with its local degree).

Used at (3.4) (tex 2427–2439: "conjugation fixes the free class, and the norm makes twice the
class rational"), at (4.6) (tex 4022–4025, 4082–4091: the heights on `Res_{K/ℚ} E^{(h)}_K` and on
`E^{(h)} × E^{(hk)}` that enter `Reg_B / Reg_A`) and by the sum/difference isogenies
(`SumDifference.lean`).

Every declaration in this file is PROVED.

* `canonicalHeight_baseChange`: `ĥ_K(P_K) = [K : ℚ] · ĥ_ℚ(P)` for `P ∈ W(ℚ)` (from
  `logHeight₁_algebraMap_rat`, `FieldBaseChange.lean`), and `neronTatePairing_baseChange`.
* `canonicalHeight_map_algEquiv`: `ĥ_K(σ P) = ĥ_K(P)` for `σ ∈ Aut(K/ℚ)` (from
  `logHeight₁_algEquiv`, `FieldGalois.lean`), `neronTatePairing_map_algEquiv`, and the adjoint form
  `neronTatePairing_map_algEquiv_left`.
* `mem_range_algebraMap_of_fixed`, `exists_baseChange_eq_of_map_eq`: Galois descent for a quadratic
  extension: a point of `W(K)` fixed by the nontrivial automorphism is rational.
* `baseChange_injective`: `W(ℚ) → W(K)` is injective.
-/

open Height

namespace ZInQ.Manuscript.RC.Height

open WeierstrassCurve WeierstrassCurve.Affine

variable {K : Type*} [Field K] [NumberField K] [DecidableEq K]

/-! ### Base change from `ℚ` -/

/-- **Heights of rational points grow by the degree under base change**:
`ĥ_K(P_K) = [K : ℚ] · ĥ_ℚ(P)` for `P ∈ W(ℚ)`; the naïve heights satisfy the same identity
exactly (`logHeight₁_algebraMap_rat`). PROVED. -/
theorem canonicalHeight_baseChange (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (P : (W.baseChange ℚ).toAffine.Point) :
    (Point.baseChange ℚ K P).canonicalHeight =
      (Module.finrank ℚ K : ℝ) * P.canonicalHeight := by
  refine canonicalHeight_map_eq_of_abs_naiveHeight_sub_le (Point.baseChange ℚ K)
    (Module.finrank ℚ K : ℝ) 0 (fun Q => ?_) P
  rcases Q with _ | ⟨x, y, h⟩
  · simp [← Point.zero_def]
  · rw [Point.baseChange, Point.map_some, naiveHeight_some, naiveHeight_some, Algebra.ofId_apply,
      logHeight₁_algebraMap_rat, sub_self, abs_zero]

/-- **The pairing of rational points grows by the degree under base change.** PROVED. -/
theorem neronTatePairing_baseChange (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (P Q : (W.baseChange ℚ).toAffine.Point) :
    (W.baseChange K).toAffine.neronTatePairing (Point.baseChange ℚ K P)
        (Point.baseChange ℚ K Q) =
      (Module.finrank ℚ K : ℝ) * (W.baseChange ℚ).toAffine.neronTatePairing P Q :=
  neronTatePairing_map_eq_of_canonicalHeight (Point.baseChange ℚ K) _
    (canonicalHeight_baseChange W) P Q

/-- The base change `W(ℚ) → W(K)` is injective. PROVED. -/
theorem baseChange_injective (W : WeierstrassCurve ℚ) :
    Function.Injective (Point.baseChange (W' := W) ℚ K) :=
  Point.map_injective _

/-! ### Galois invariance -/

/-- **The canonical height is Galois invariant**: `ĥ_K(σ P) = ĥ_K(P)` for `σ ∈ Aut(K/ℚ)` and a
curve `W` over `ℚ`; the naïve heights agree exactly (`logHeight₁_algEquiv`). PROVED. -/
theorem canonicalHeight_map_algEquiv (W : WeierstrassCurve ℚ) [W.IsElliptic] (σ : K ≃ₐ[ℚ] K)
    (P : (W.baseChange K).toAffine.Point) :
    (Point.map σ.toAlgHom P).canonicalHeight = P.canonicalHeight := by
  have := canonicalHeight_map_eq_of_abs_naiveHeight_sub_le (Point.map σ.toAlgHom) 1 0
    (fun Q => ?_) P
  · simpa using this
  rcases Q with _ | ⟨x, y, h⟩
  · simp [← Point.zero_def]
  · rw [Point.map_some, naiveHeight_some, naiveHeight_some]
    show |logHeight₁ (σ x) - 1 * logHeight₁ x| ≤ 0
    rw [logHeight₁_algEquiv, one_mul, sub_self, abs_zero]

/-- **The Néron–Tate pairing is Galois invariant**: `⟨σ P, σ Q⟩ = ⟨P, Q⟩`. PROVED. -/
theorem neronTatePairing_map_algEquiv (W : WeierstrassCurve ℚ) [W.IsElliptic] (σ : K ≃ₐ[ℚ] K)
    (P Q : (W.baseChange K).toAffine.Point) :
    (W.baseChange K).toAffine.neronTatePairing (Point.map σ.toAlgHom P) (Point.map σ.toAlgHom Q) =
      (W.baseChange K).toAffine.neronTatePairing P Q := by
  have := neronTatePairing_map_eq_of_canonicalHeight (Point.map σ.toAlgHom) 1
    (fun P => by rw [canonicalHeight_map_algEquiv, one_mul]) P Q
  simpa using this

/-- **Adjoint form of Galois invariance**: if `σ Q' = Q` then `⟨σ P, Q⟩ = ⟨P, Q'⟩`. PROVED. -/
theorem neronTatePairing_map_algEquiv_left (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (σ : K ≃ₐ[ℚ] K) (P Q Q' : (W.baseChange K).toAffine.Point)
    (hQ : Point.map σ.toAlgHom Q' = Q) :
    (W.baseChange K).toAffine.neronTatePairing (Point.map σ.toAlgHom P) Q =
      (W.baseChange K).toAffine.neronTatePairing P Q' := by
  rw [← hQ, neronTatePairing_map_algEquiv]

/-! ### Galois descent for a quadratic extension -/

variable [Algebra.IsQuadraticExtension ℚ K]

omit [DecidableEq K] in
/-- **An element fixed by the nontrivial automorphism of a quadratic extension of `ℚ` is
rational.** PROVED. -/
theorem mem_range_algebraMap_of_fixed {σ : K ≃ₐ[ℚ] K} (hσ : σ ≠ 1) {x : K} (hx : σ x = x) :
    x ∈ Set.range (algebraMap ℚ K) := by
  have hcard : Nat.card (K ≃ₐ[ℚ] K) = 2 := by
    rw [IsGalois.card_aut_eq_finrank]
    exact Algebra.IsQuadraticExtension.finrank_eq_two ℚ K
  rw [IsGalois.mem_range_algebraMap_iff_fixed]
  intro φ
  rcases eq_or_ne φ 1 with h1 | h1
  · rw [h1, AlgEquiv.one_apply]
  · rw [((Nat.card_eq_two_iff' 1).mp hcard).unique h1 hσ, hx]

/-- **Galois descent for points**: a point of `W(K)` fixed by the nontrivial automorphism `σ` of
the quadratic extension `K/ℚ` is the base change of a point of `W(ℚ)`. (The same argument as the
vendored quadratic descent lemma for points, over `ℚ`.) PROVED. -/
theorem exists_baseChange_eq_of_map_eq {W : WeierstrassCurve ℚ} {σ : K ≃ₐ[ℚ] K} (hσ : σ ≠ 1)
    {R : (W.baseChange K).toAffine.Point} (hR : Point.map σ.toAlgHom R = R) :
    ∃ Q : (W.baseChange ℚ).toAffine.Point, Point.baseChange ℚ K Q = R := by
  rcases R with _ | ⟨x, y, h⟩
  · exact ⟨0, map_zero _⟩
  · rw [Point.map_some] at hR
    injection hR with hx hy
    obtain ⟨x₀, rfl⟩ := mem_range_algebraMap_of_fixed hσ hx
    obtain ⟨y₀, rfl⟩ := mem_range_algebraMap_of_fixed hσ hy
    simp only [← Algebra.ofId_apply] at h ⊢
    exact ⟨.some x₀ y₀ ((Affine.baseChange_nonsingular W (f := Algebra.ofId ℚ K)
      (FaithfulSMul.algebraMap_injective ℚ K) x₀ y₀).mp h), Point.map_some _ _⟩

end ZInQ.Manuscript.RC.Height
