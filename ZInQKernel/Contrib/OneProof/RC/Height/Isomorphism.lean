import ZInQKernel.Contrib.OneProof.RC.Height.Transfer
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.VariableChange
import ZInQKernel.Contrib.CloudB3RC53.Basic

/-!
# Lane RC19 (height): isomorphisms and the quadratic-twist isomorphism

The manuscript (`diophantine_zq.tex`, 11/5 version) compares Néron–Tate heights of points that live
on different quadratic twists: at (3.4) (lines 2427–2439, "each rational free line has index at
most two in its native rank-one lattice") the rational points of `E^{(h)}` are read inside the
points of a twist over a quadratic field, and at (4.6) (lines 4022–4025, 4082–4091) the
sum/difference isogenies between `Res_{K/ℚ} E^{(h)}_K` and `E^{(h)} × E^{(hk)}` pass through the
twist isomorphism `E^{(hk)} ≅ E^{(h)}` over `K = ℚ(√k)`. This file proves that an isomorphism of
Weierstrass curves preserves the canonical height (functoriality in degree one), constructs the
twist isomorphism over a field containing a square root of `k`, and records how it interacts with
the Galois conjugation `√k ↦ −√k`.

The twist is the blueprint's `ZInQ.Contrib.CloudB3RC53.qtwist`:
`qtwist E d : y² = x³ + d (b₂/4) x² + d² (b₄/2) x + d³ (b₆/4)`.

Every declaration in this file is PROVED.

* `canonicalHeight_addEquivVariableChange`, `neronTatePairing_addEquivVariableChange`: a change of
  variables `(x, y) ↦ (u²x + r, …)` preserves `ĥ` and `⟨·,·⟩` (the naïve heights differ boundedly,
  `abs_logHeight₁_mul_add_sub_le`; then `canonicalHeight_map_eq_of_abs_naiveHeight_sub_le` with
  `d = 1`).
* `canonicalHeight_cast`: transport along an equality of curves preserves `ĥ`.
* `twistChange`, `qtwist_mul_baseChange`: over a field `K` with `s ∈ K`, `s² = e`, the base change
  of `qtwist E (d e)` is the change of variables `u = s⁻¹` of the base change of `qtwist E d`.
* `twistAddEquiv`: the resulting group isomorphism `E^{(de)}(K) ≃ E^{(d)}(K)`,
  `(X, Y) ↦ (X/s², Y/s³)` (`twistAddEquiv_some`), and `canonicalHeight_twistAddEquiv`,
  `neronTatePairing_twistAddEquiv`: it preserves heights and pairings.
* `map_twistAddEquiv`: for a `ℚ`-automorphism `σ` of `K` with `σ s = −s`,
  `σ(ι P) = −ι(σ P)` (the twist isomorphism is anti-equivariant).
* `map_baseChange_eq`: a `ℚ`-automorphism fixes the base change of a rational point.
-/

open Height

namespace ZInQ.Manuscript.RC.Height

open WeierstrassCurve WeierstrassCurve.Affine ZInQ.Contrib.CloudB3RC53

/-! ### Changes of variables preserve the canonical height -/

section VariableChange

variable {F : Type*} [Field F] [AdmissibleAbsValues F] [DecidableEq F]

/-- **A change of variables preserves the canonical height** (functoriality for isomorphisms,
degree one): for the group isomorphism `(C • W)(F) ≃ W(F)`, `(x, y) ↦ (u²x + r, u³y + u²sx + t)`,
`ĥ_W(φ P) = ĥ_{C • W}(P)`. PROVED. -/
theorem canonicalHeight_addEquivVariableChange (W : WeierstrassCurve F) [W.IsElliptic]
    (C : VariableChange F) (P : (C • W).toAffine.Point) :
    (Point.addEquivVariableChange W C P).canonicalHeight = P.canonicalHeight := by
  obtain ⟨D, hD⟩ := abs_logHeight₁_mul_add_sub_le ((C.u : F) ^ 2) C.r
    (pow_ne_zero 2 C.u.ne_zero)
  have key := canonicalHeight_map_eq_of_abs_naiveHeight_sub_le
    (Point.addEquivVariableChange W C).toAddMonoidHom 1 D ?_ P
  · simpa using key
  · intro Q
    rcases Q with _ | ⟨x, y, h⟩
    · have h0 := hD 0
      simp only [← Point.zero_def, map_zero, Point.naiveHeight_zero, mul_zero, sub_zero,
        abs_zero]
      exact (abs_nonneg _).trans h0
    · rw [AddEquiv.coe_toAddMonoidHom, Point.coe_addEquivVariableChange,
        Point.equivVariableChange_some, naiveHeight_some, naiveHeight_some, one_mul]
      exact hD x

/-- **A change of variables preserves the Néron–Tate pairing.** PROVED. -/
theorem neronTatePairing_addEquivVariableChange (W : WeierstrassCurve F) [W.IsElliptic]
    (C : VariableChange F) (P Q : (C • W).toAffine.Point) :
    W.toAffine.neronTatePairing (Point.addEquivVariableChange W C P)
        (Point.addEquivVariableChange W C Q) =
      (C • W).toAffine.neronTatePairing P Q := by
  have := neronTatePairing_map_eq_of_canonicalHeight
    (Point.addEquivVariableChange W C).toAddMonoidHom 1
    (fun P => by simpa using canonicalHeight_addEquivVariableChange W C P) P Q
  simpa using this

/-- **Transport along an equality of curves preserves the canonical height.** PROVED. -/
theorem canonicalHeight_cast {V V' : WeierstrassCurve F} (h : V = V') (P : V.toAffine.Point) :
    (cast (congrArg (fun V : WeierstrassCurve F => V.toAffine.Point) h) P).canonicalHeight =
      P.canonicalHeight := by
  subst h
  rfl

end VariableChange

/-! ### The quadratic-twist isomorphism -/

section Twist

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- The change of variables `u = s⁻¹`, `r = s = t = 0`, i.e. `(x, y) ↦ (x/s², y/s³)` on points of
the transformed curve. -/
def twistChange (s : K) (hs : s ≠ 0) : VariableChange K :=
  ⟨Units.mk0 s⁻¹ (inv_ne_zero hs), 0, 0, 0⟩

/-- **The twist by `d e` is the twist by `d` changed by `u = s⁻¹`** over a field containing a square
root `s` of `e`: `(qtwist E (d e))_K = twistChange s • (qtwist E d)_K`. PROVED. -/
theorem qtwist_mul_baseChange (E : WeierstrassCurve ℚ) (d e : ℚ) (s : K) (hs : s ≠ 0)
    (hse : s ^ 2 = algebraMap ℚ K e) :
    (qtwist E (d * e)).baseChange K = twistChange s hs • (qtwist E d).baseChange K := by
  have hu : (((twistChange s hs).u⁻¹ : Kˣ) : K) = s := by
    simp [twistChange]
  ext
  · rw [variableChange_a₁, hu]
    simp [qtwist, twistChange, WeierstrassCurve.baseChange]
  · rw [variableChange_a₂, hu]
    simp only [qtwist, twistChange, WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₂, map_mul, map_div₀, map_ofNat, map_zero, mul_zero, sub_zero,
      add_zero, zero_pow two_ne_zero]
    rw [hse]
    ring
  · rw [variableChange_a₃, hu]
    simp [qtwist, twistChange, WeierstrassCurve.baseChange]
  · rw [variableChange_a₄, hu]
    simp only [qtwist, twistChange, WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, map_mul,
      map_div₀, map_pow, map_ofNat, map_zero, mul_zero, sub_zero, add_zero, zero_mul,
      zero_pow two_ne_zero]
    rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, hse]
    ring
  · rw [variableChange_a₆, hu]
    simp only [qtwist, twistChange, WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
      WeierstrassCurve.map_a₆, map_mul, map_div₀, map_pow, map_ofNat, map_zero, mul_zero,
      sub_zero, add_zero, zero_mul, zero_pow two_ne_zero, zero_pow (by norm_num : 3 ≠ 0)]
    rw [show s ^ 6 = (s ^ 2) ^ 3 by ring, hse]
    ring

variable [DecidableEq K]

/-- **The quadratic-twist isomorphism** `ι : E^{(de)}(K) ≃ E^{(d)}(K)` over a field `K` containing
a square root `s` of `e`: the transport along `qtwist_mul_baseChange` followed by the change of
variables `u = s⁻¹`. On affine points it is `(X, Y) ↦ (X/s², Y/s³)` (`twistAddEquiv_some`). -/
noncomputable def twistAddEquiv (E : WeierstrassCurve ℚ) (d e : ℚ) (s : K) (hs : s ≠ 0)
    (hse : s ^ 2 = algebraMap ℚ K e) :
    ((qtwist E (d * e)).baseChange K).toAffine.Point ≃+
      ((qtwist E d).baseChange K).toAffine.Point :=
  (AddEquiv.cast (M := fun V : WeierstrassCurve K => V.toAffine.Point)
    (qtwist_mul_baseChange E d e s hs hse)).trans
    (Point.addEquivVariableChange ((qtwist E d).baseChange K) (twistChange s hs))

/-- The coordinates of the twist isomorphism: `(X, Y) ↦ (s⁻² X, s⁻³ Y)`. PROVED. -/
theorem twistAddEquiv_some (E : WeierstrassCurve ℚ) (d e : ℚ) (s : K) (hs : s ≠ 0)
    (hse : s ^ 2 = algebraMap ℚ K e) {X Y : K}
    (h : ((qtwist E (d * e)).baseChange K).toAffine.Nonsingular X Y) :
    ∃ h' : ((qtwist E d).baseChange K).toAffine.Nonsingular (s⁻¹ ^ 2 * X) (s⁻¹ ^ 3 * Y),
      twistAddEquiv E d e s hs hse (Point.some X Y h) = Point.some _ _ h' := by
  refine ⟨?_, ?_⟩
  · have h2 := (Affine.variableChange_nonsingular ((qtwist E d).baseChange K) (twistChange s hs)
      X Y).mpr ((qtwist_mul_baseChange E d e s hs hse) ▸ h)
    simpa [twistChange] using h2
  · simp only [twistAddEquiv, AddEquiv.trans_apply, AddEquiv.cast_apply]
    rw [Point.cast_some (qtwist_mul_baseChange E d e s hs hse), Point.coe_addEquivVariableChange,
      Point.equivVariableChange_some]
    simp [twistChange]

/-- The twist isomorphism fixes the point at infinity. PROVED. -/
theorem twistAddEquiv_zero (E : WeierstrassCurve ℚ) (d e : ℚ) (s : K) (hs : s ≠ 0)
    (hse : s ^ 2 = algebraMap ℚ K e) :
    twistAddEquiv E d e s hs hse 0 = 0 :=
  map_zero _

variable [AdmissibleAbsValues K]

/-- **The twist isomorphism preserves the canonical height**: `ĥ_{E^{(d)}/K}(ι P) =
ĥ_{E^{(de)}/K}(P)`. PROVED. -/
theorem canonicalHeight_twistAddEquiv (E : WeierstrassCurve ℚ) (d e : ℚ)
    [(qtwist E d).IsElliptic] (s : K) (hs : s ≠ 0) (hse : s ^ 2 = algebraMap ℚ K e)
    (P : ((qtwist E (d * e)).baseChange K).toAffine.Point) :
    (twistAddEquiv E d e s hs hse P).canonicalHeight = P.canonicalHeight := by
  simp only [twistAddEquiv, AddEquiv.trans_apply, AddEquiv.cast_apply]
  rw [canonicalHeight_addEquivVariableChange,
    canonicalHeight_cast (qtwist_mul_baseChange E d e s hs hse)]

/-- **The twist isomorphism preserves the Néron–Tate pairing.** PROVED. -/
theorem neronTatePairing_twistAddEquiv (E : WeierstrassCurve ℚ) (d e : ℚ)
    [(qtwist E d).IsElliptic] [(qtwist E (d * e)).IsElliptic] (s : K) (hs : s ≠ 0)
    (hse : s ^ 2 = algebraMap ℚ K e) (P Q : ((qtwist E (d * e)).baseChange K).toAffine.Point) :
    ((qtwist E d).baseChange K).toAffine.neronTatePairing (twistAddEquiv E d e s hs hse P)
        (twistAddEquiv E d e s hs hse Q) =
      ((qtwist E (d * e)).baseChange K).toAffine.neronTatePairing P Q := by
  have := neronTatePairing_map_eq_of_canonicalHeight (twistAddEquiv E d e s hs hse).toAddMonoidHom
    1 (fun P => by simpa using canonicalHeight_twistAddEquiv E d e s hs hse P) P Q
  simpa using this

end Twist

/-! ### Galois conjugation and the twist -/

section Galois

variable {K : Type*} [Field K] [Algebra ℚ K] [DecidableEq K]

/-- **The twist isomorphism is anti-equivariant**: for a `ℚ`-algebra map `σ : K → K` with
`σ s = −s`, `σ(ι P) = −ι(σ P)`. This is the computation behind "conjugation fixes the free class"
and behind the sum/difference isogenies (tex 2433–2434, 4022–4023). PROVED. -/
theorem map_twistAddEquiv (E : WeierstrassCurve ℚ) (d e : ℚ) (s : K) (hs : s ≠ 0)
    (hse : s ^ 2 = algebraMap ℚ K e) (σ : K →ₐ[ℚ] K) (hσ : σ s = -s)
    (P : ((qtwist E (d * e)).baseChange K).toAffine.Point) :
    Point.map σ (twistAddEquiv E d e s hs hse P) =
      -twistAddEquiv E d e s hs hse (Point.map σ P) := by
  rcases P with _ | ⟨X, Y, h⟩
  · simp only [← Point.zero_def, map_zero, neg_zero]
  · obtain ⟨h', e1⟩ := twistAddEquiv_some E d e s hs hse h
    rw [e1, Point.map_some, Point.map_some]
    obtain ⟨h'', e2⟩ := twistAddEquiv_some E d e s hs hse
      ((Affine.baseChange_nonsingular (qtwist E (d * e)) σ.injective X Y).mpr h)
    rw [e2, Point.neg_some]
    have hσi : σ s⁻¹ = -s⁻¹ := by rw [map_inv₀, hσ, inv_neg]
    simp only [Point.some.injEq, map_mul, map_pow, hσi]
    refine ⟨by ring, ?_⟩
    simp only [Affine.negY, WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₃, qtwist, map_zero, zero_mul, sub_zero]
    ring

/-- **A `ℚ`-automorphism fixes rational points**: `σ(R_K) = R_K`. PROVED. -/
theorem map_baseChange_eq {W : WeierstrassCurve ℚ} (σ : K →ₐ[ℚ] K)
    (R : (W.baseChange ℚ).toAffine.Point) :
    Point.map σ (Point.baseChange ℚ K R) = Point.baseChange ℚ K R :=
  Point.map_baseChange σ R

end Galois

end ZInQ.Manuscript.RC.Height
