import ZInQKernel.Contrib.OneProof.RC.TwistDictionary.Invariance

/-!
# Lane RC27 (item 7): the `L`-series of an elliptic curve does not depend on the model

Mathlib's `WeierstrassCurve.LFunction W` (an Euler product over the primes `v` of the number field)
is computed at `v` from a minimal model of `W` over the completion `K_v`, chosen by
`Classical.choice` (`WeierstrassCurve.minimal`), through the reduction type and the number of points
of the reduction (`WeierstrassCurve.localPolynomial`). This file proves that for an **elliptic**
`W` (`Δ ≠ 0`) the result does not depend on the Weierstrass model: an admissible change of
variables `C` over the number field leaves the `L`-function and the `L`-series unchanged.

* `LFunction_smul`, `LSeries_smul`: `L(C • W, s) = L(W, s)` over any number field, for `Δ(W) ≠ 0`.
* `LSeries_qtwist_one`: `L(E^{(1)}, s) = L(E, s)` for the shared top layer's twist `qtwist`
  (`qtwist E 1` is the completed-square model of `E`, the change of variables
  `(1, 0, −a₁/2, −a₃/2)`).
* `LSeries_qtwist_mul_sq`, `LSeries_qtwist_of_eq_mul_sq`: `L(E^{(d e²)}, s) = L(E^{(d)}, s)` for
  `e ≠ 0` (the change of variables `(e⁻¹, 0, 0, 0)`): the twist only depends on the square class.

**Local input.** The local statement — two minimal models of an elliptic curve over the fraction
field of a discrete valuation ring differ by a change of variables whose `u` is a unit, which
therefore descends to the ring (`variableChange_integral_of_u_integral`); the integral models, and
the reductions, then differ by a change of variables over the ring, resp. the residue field; so the
two models have the same valuations of `Δ` and `c₄`, the same split condition (the node's slope
polynomial `c₄T² + a₁c₄T − (54b₆ − 3b₂b₄ + a₂c₄)` becomes `u⁻⁶ P(uT + s)`), and reductions with the
same number of points — is lane RC18's PROVED `TwistDictionary.localPolynomial_smul`
(`TwistDictionary/Invariance.lean`), resting on the PROVED lemmas `vK_u_eq_one`,
`exists_reduction_variableChange`, `natCard_point_variableChange` of `RouteK/Rank/LFunctionCd`.
This file adds the global statement (base change to `K_v` commutes with the change of variables,
`WeierstrassCurve.map_variableChange`) and the two twist identities.

**The hypothesis `Δ ≠ 0` cannot be dropped.** For a singular `W` every integral model has
`v(Δ) = v(0)`, so every integral model is "minimal" and `WeierstrassCurve.minimal` is an arbitrary
choice among them; for a nodal cubic, integral models with `v(c₄) = 0` (multiplicative) and with
`v(c₄) > 0` (additive) both exist, so the local polynomial of `W` and of `C • W` are given by
unrelated choices and their equality is not provable.

Every theorem in this file is PROVED. (No hypothesis bundle is introduced.)
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Height

open WeierstrassCurve IsDedekindDomain NumberField

section NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **Mathlib's `L`-function is a model invariant** (PROVED): for a Weierstrass curve `W` over a
number field with `Δ(W) ≠ 0` and an admissible change of variables `C` over the same field,
`L(C • W) = L(W)` as formal Dirichlet series. Prime by prime: the base change of `C • W` to the
completion `K_v` is `C_v • W_{K_v}`, and lane RC18's `TwistDictionary.localPolynomial_smul` gives
the same local polynomial for the two models. -/
theorem LFunction_smul (W : WeierstrassCurve K) (hΔ : W.Δ ≠ 0) (C : VariableChange K) :
    (C • W).LFunction = W.LFunction := by
  unfold LFunction
  congr 1
  funext v
  have hΔv : (W.baseChange (v.adicCompletion K)).Δ ≠ 0 := by
    rw [baseChange, map_Δ]
    exact (map_ne_zero _).mpr hΔ
  have hloc : ((C • W).baseChange (v.adicCompletion K)).localPolynomial
      (v.adicCompletionIntegers K) =
      (W.baseChange (v.adicCompletion K)).localPolynomial (v.adicCompletionIntegers K) := by
    rw [baseChange, ← map_variableChange]
    exact ZInQ.Manuscript.RC.TwistDictionary.localPolynomial_smul _ hΔv _
  unfold localEulerFactor localPowerSeries
  rw [hloc]

/-- **Mathlib's `L`-series is a model invariant** (PROVED): `L(C • W, s) = L(W, s)` for every `s`,
when `Δ(W) ≠ 0`. -/
theorem LSeries_smul (W : WeierstrassCurve K) (hΔ : W.Δ ≠ 0) (C : VariableChange K) :
    (C • W).LSeries = W.LSeries := by
  funext s
  simp only [WeierstrassCurve.LSeries, LFunction_smul W hΔ C]

/-- `LFunction_smul` for an elliptic curve (PROVED). -/
theorem LFunction_smul_of_isElliptic (W : WeierstrassCurve K) [W.IsElliptic]
    (C : VariableChange K) : (C • W).LFunction = W.LFunction :=
  LFunction_smul W W.isUnit_Δ.ne_zero C

/-- `LSeries_smul` for an elliptic curve (PROVED). -/
theorem LSeries_smul_of_isElliptic (W : WeierstrassCurve K) [W.IsElliptic]
    (C : VariableChange K) : (C • W).LSeries = W.LSeries :=
  LSeries_smul W W.isUnit_Δ.ne_zero C

end NumberField

section Twist

open ZInQ.Contrib.CloudB3RC53 ZInQ.Manuscript.RC.TwistDictionary

/-- **`L(E^{(1)}, s) = L(E, s)`** (PROVED): the shared top layer's `qtwist E 1` is the
completed-square model `y² = x³ + (b₂/4)x² + (b₄/2)x + b₆/4` of `E`, the change of variables
`(1, 0, −a₁/2, −a₃/2)` of `E` (lane RC18's `twistK_one`), so it has the same `L`-series. -/
theorem LSeries_qtwist_one (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (qtwist E 1).LSeries = E.LSeries := by
  rw [qtwist_eq_twistK, twistK_one E two_ne_zero]
  exact LSeries_smul_of_isElliptic E _

/-- **`L(E^{(d e²)}, s) = L(E^{(d)}, s)` for `e ≠ 0`** (PROVED): `qtwist E (d e²)` is the change of
variables `(e⁻¹, 0, 0, 0)` of `qtwist E d` (lane RC18's `twistK_mul_sq`); for `d ≠ 0` the twist is
elliptic (`Δ(E^{(d)}) = d⁶ Δ(E)`, `twistK_Δ`), and for `d = 0` both sides are the same curve. -/
theorem LSeries_qtwist_mul_sq (E : WeierstrassCurve ℚ) [E.IsElliptic] (d : ℚ) {e : ℚ}
    (he : e ≠ 0) : (qtwist E (d * e ^ 2)).LSeries = (qtwist E d).LSeries := by
  by_cases hd : d = 0
  · subst hd
    rw [zero_mul]
  rw [qtwist_eq_twistK, qtwist_eq_twistK, twistK_mul_sq E two_ne_zero d he]
  apply LSeries_smul
  rw [twistK_Δ E two_ne_zero]
  exact mul_ne_zero (pow_ne_zero _ hd) E.isUnit_Δ.ne_zero

/-- **The twist `L`-series only depends on the square class** (PROVED): if `d' = d q²` with
`q ≠ 0`, then `L(E^{(d')}, s) = L(E^{(d)}, s)`. -/
theorem LSeries_qtwist_of_eq_mul_sq (E : WeierstrassCurve ℚ) [E.IsElliptic] {d d' q : ℚ}
    (hq : q ≠ 0) (h : d' = d * q ^ 2) : (qtwist E d').LSeries = (qtwist E d).LSeries := by
  rw [h]
  exact LSeries_qtwist_mul_sq E d hq

end Twist

end ZInQ.Manuscript.RC.Height
