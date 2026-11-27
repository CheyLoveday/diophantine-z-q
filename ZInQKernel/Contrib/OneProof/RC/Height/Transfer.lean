import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.CanonicalHeight.Basic

/-!
# Lane RC19 (height): moving the canonical height along additive maps

The canonical height `ĥ(P) = lim h(2ⁿ P) / 4ⁿ` of the vendored Tau Ceti library is normalized
against the naïve height `h(P) = h(x(P))` of the `x`-coordinate, relative to the field of
definition (Mathlib's `Height.AdmissibleAbsValues`; for a number field `K` the places carry their
local degrees, so `ĥ` is the height relative to `K`).

The functoriality facts used by the manuscript (`diophantine_zq.tex`, the 11/5 version) at (3.4)
(lines 2427–2439), at the calibration (4.6) (lines 3987–4141) and in the base-zero lemma (lines
4330–4376) all have the same shape: an additive map of point groups multiplies the naïve height by
a constant `d` up to a bounded error, hence multiplies the canonical height by `d` exactly. This
file proves that principle once (`canonicalHeight_map_eq_of_abs_naiveHeight_sub_le`), its polarized
form for the Néron–Tate pairing, and the elementary facts every application needs.

Every declaration in this file is PROVED.

* `canonicalHeight_map_eq_of_abs_naiveHeight_sub_le`: if `|h(φ P) − d h(P)| ≤ C` for all `P`, then
  `ĥ(φ P) = d ĥ(P)`. (Tate's limit argument along `[2ⁿ]`, as in the construction of the canonical
  height in Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Chapter VIII, §9; textbook
  reference, locator not re-read: UNVERIFIED.)
* `neronTatePairing_map_eq_of_canonicalHeight`: then `⟨φ P, φ Q⟩ = d ⟨P, Q⟩`.
* `neronTatePairing_adjoint`: if moreover `φ ∘ ψ = [d]`, `d ≠ 0`, then `⟨φ P, Q⟩ = ⟨P, ψ Q⟩` (the
  adjunction of an isogeny and its dual).
* `canonicalHeight_zsmul'`, `neronTatePairing_zsmul_left`: functoriality for `[n]` (degree `n²`).
* `neronTatePairing_add_left`, `neronTatePairing_add_right`, `neronTatePairing_neg_left`, …:
  bilinearity in the form the applications use.
* `canonicalHeight_add_of_isOfFinAddOrder`: `ĥ(P + T) = ĥ(P)` for a torsion point `T`.
* `naiveHeight_some`: the naïve height of an affine point is the height of its `x`-coordinate.
* `abs_logHeight₁_mul_add_sub_le`: an affine substitution `x ↦ a x + b` (`a ≠ 0`) changes the height
  of a field element by a bounded amount.
-/

open Filter Topology Height

namespace ZInQ.Manuscript.RC.Height

open WeierstrassCurve WeierstrassCurve.Affine

/-! ### Heights of field elements under affine substitutions -/

/-- **An affine substitution changes heights boundedly**: for `a ≠ 0` there is `C` with
`|h(a x + b) − h(x)| ≤ C` for every `x`. PROVED. -/
theorem abs_logHeight₁_mul_add_sub_le {K : Type*} [Field K] [AdmissibleAbsValues K] (a b : K)
    (ha : a ≠ 0) : ∃ C : ℝ, ∀ x : K, |logHeight₁ (a * x + b) - logHeight₁ x| ≤ C := by
  refine ⟨totalWeight K * Real.log 2 + logHeight₁ a + logHeight₁ b,
    fun x => abs_sub_le_iff.mpr ⟨?_, ?_⟩⟩
  · have h1 := logHeight₁_add_le (a * x) b
    have h2 := logHeight₁_mul_le a x
    linarith
  · have hx : x = a⁻¹ * ((a * x + b) - b) := by
      rw [add_sub_cancel_right, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
    have h1 := logHeight₁_mul_le a⁻¹ ((a * x + b) - b)
    have h2 := logHeight₁_sub_le (a * x + b) b
    rw [logHeight₁_inv, ← hx] at h1
    linarith

/-! ### The naïve height of an affine point -/

section Naive

variable {F : Type*} [Field F] [AdmissibleAbsValues F] {W : Affine F}

/-- The naïve height of an affine point `(x, y)` is the height of `x`. PROVED. -/
theorem naiveHeight_some {x y : F} (h : W.Nonsingular x y) :
    (Point.some x y h).naiveHeight = logHeight₁ x := by
  rw [Point.naiveHeight_eq_logHeight₁, Point.xRep_some]
  rfl

end Naive

/-! ### The transfer principle -/

section Transfer

variable {F₁ F₂ : Type*} [Field F₁] [Field F₂] [AdmissibleAbsValues F₁] [AdmissibleAbsValues F₂]
  [DecidableEq F₁] [DecidableEq F₂] {W₁ : Affine F₁} {W₂ : Affine F₂}
  [W₁.toAffine.IsElliptic] [W₂.toAffine.IsElliptic]

/-- **Functoriality of the canonical height from a naïve-height estimate.** Let `φ` be an additive
map between the point groups of two elliptic curves (over possibly different fields with
admissible absolute values). If `φ` multiplies the naïve height by `d` up to a bounded error,
`|h(φ P) − d h(P)| ≤ C`, then it multiplies the canonical height by `d` exactly:
`ĥ(φ P) = d ĥ(P)`. Since `φ` commutes with `[2ⁿ]`, the error divided by `4ⁿ` tends to zero along
the defining sequences. PROVED. -/
theorem canonicalHeight_map_eq_of_abs_naiveHeight_sub_le (φ : W₁.Point →+ W₂.Point) (d C : ℝ)
    (h : ∀ P : W₁.Point, |(φ P).naiveHeight - d * P.naiveHeight| ≤ C) (P : W₁.Point) :
    (φ P).canonicalHeight = d * P.canonicalHeight := by
  have h₂ := (φ P).tendsto_naiveHeight_two_pow_nsmul_div_four_pow
  have h₁ := (P.tendsto_naiveHeight_two_pow_nsmul_div_four_pow).const_mul d
  have hdiff : Tendsto (fun n : ℕ => ((2 ^ n) • φ P).naiveHeight / 4 ^ n
      - d * (((2 ^ n) • P).naiveHeight / 4 ^ n)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) ((tendsto_const_nhds (x := C)).div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 4)))
    rw [← map_nsmul, Real.norm_eq_abs]
    have hn := h ((2 ^ n) • P)
    rw [show (φ ((2 ^ n) • P)).naiveHeight / 4 ^ n - d * (((2 ^ n) • P).naiveHeight / 4 ^ n)
        = ((φ ((2 ^ n) • P)).naiveHeight - d * ((2 ^ n) • P).naiveHeight) / 4 ^ n by ring,
      abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 ^ n)]
    exact div_le_div_of_nonneg_right hn (by positivity)
  have h₃ : Tendsto (fun n : ℕ => ((2 ^ n) • φ P).naiveHeight / 4 ^ n) atTop
      (𝓝 (d * P.canonicalHeight)) := by
    have := h₁.add hdiff
    rw [add_zero] at this
    exact Tendsto.congr (fun n => by ring) this
  exact tendsto_nhds_unique h₂ h₃

/-- **The polarized form**: if `ĥ(φ P) = d ĥ(P)` for every `P`, then
`⟨φ P, φ Q⟩ = d ⟨P, Q⟩` for the Néron–Tate pairings. PROVED. -/
theorem neronTatePairing_map_eq_of_canonicalHeight (φ : W₁.Point →+ W₂.Point) (d : ℝ)
    (h : ∀ P : W₁.Point, (φ P).canonicalHeight = d * P.canonicalHeight) (P Q : W₁.Point) :
    W₂.neronTatePairing (φ P) (φ Q) = d * W₁.neronTatePairing P Q := by
  rw [neronTatePairing_apply, neronTatePairing_apply, ← map_add, h, h, h]
  ring

/-- **The adjunction for an isogeny and its dual**: if `ĥ(φ P) = d ĥ(P)` for every `P` and
`φ ∘ ψ = [d]` with `d ≠ 0` (as for an isogeny of degree `d` and its dual), then
`⟨φ P, Q⟩ = ⟨P, ψ Q⟩`. Indeed `d ⟨φ P, Q⟩ = ⟨φ P, φ (ψ Q)⟩ = d ⟨P, ψ Q⟩`. PROVED. -/
theorem neronTatePairing_adjoint (φ : W₁.Point →+ W₂.Point) (ψ : W₂.Point →+ W₁.Point) (d : ℤ)
    (hd : d ≠ 0) (h : ∀ P : W₁.Point, (φ P).canonicalHeight = d * P.canonicalHeight)
    (hφψ : ∀ Q : W₂.Point, φ (ψ Q) = d • Q) (P : W₁.Point) (Q : W₂.Point) :
    W₂.neronTatePairing (φ P) Q = W₁.neronTatePairing P (ψ Q) := by
  have h1 := neronTatePairing_map_eq_of_canonicalHeight φ d h P (ψ Q)
  rw [hφψ, map_zsmul, zsmul_eq_mul] at h1
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  exact mul_left_cancel₀ hd' h1

end Transfer

/-! ### Bilinearity, `[n]` and torsion -/

section Pairing

variable {F : Type*} [Field F] [AdmissibleAbsValues F] [DecidableEq F] {W : Affine F}
  [W.toAffine.IsElliptic]

/-- Additivity of the pairing in the first argument. PROVED. -/
theorem neronTatePairing_add_left (P P' Q : W.Point) :
    W.neronTatePairing (P + P') Q = W.neronTatePairing P Q + W.neronTatePairing P' Q := by
  rw [map_add, LinearMap.add_apply]

/-- Additivity of the pairing in the second argument. PROVED. -/
theorem neronTatePairing_add_right (P Q Q' : W.Point) :
    W.neronTatePairing P (Q + Q') = W.neronTatePairing P Q + W.neronTatePairing P Q' := by
  rw [map_add]

/-- The pairing in the first argument is odd. PROVED. -/
theorem neronTatePairing_neg_left (P Q : W.Point) :
    W.neronTatePairing (-P) Q = -W.neronTatePairing P Q := by
  rw [map_neg, LinearMap.neg_apply]

/-- The pairing in the second argument is odd. PROVED. -/
theorem neronTatePairing_neg_right (P Q : W.Point) :
    W.neronTatePairing P (-Q) = -W.neronTatePairing P Q := by
  rw [map_neg]

/-- Subtraction in the first argument. PROVED. -/
theorem neronTatePairing_sub_left (P P' Q : W.Point) :
    W.neronTatePairing (P - P') Q = W.neronTatePairing P Q - W.neronTatePairing P' Q := by
  rw [map_sub, LinearMap.sub_apply]

/-- Subtraction in the second argument. PROVED. -/
theorem neronTatePairing_sub_right (P Q Q' : W.Point) :
    W.neronTatePairing P (Q - Q') = W.neronTatePairing P Q - W.neronTatePairing P Q' := by
  rw [map_sub]

/-- `ℤ`-linearity in the first argument. PROVED. -/
theorem neronTatePairing_zsmul_left (n : ℤ) (P Q : W.Point) :
    W.neronTatePairing (n • P) Q = n * W.neronTatePairing P Q := by
  rw [map_zsmul, LinearMap.smul_apply, zsmul_eq_mul]

/-- `ℤ`-linearity in the second argument. PROVED. -/
theorem neronTatePairing_zsmul_right (n : ℤ) (P Q : W.Point) :
    W.neronTatePairing P (n • Q) = n * W.neronTatePairing P Q := by
  rw [map_zsmul, zsmul_eq_mul]

/-- **Functoriality for `[n]`** (degree `n²`): `ĥ(nP) = n² ĥ(P)`, the vendored
`canonicalHeight_zsmul`, restated in the form `deg [n] · ĥ`. PROVED. -/
theorem canonicalHeight_zsmul' (n : ℤ) (P : W.Point) :
    (n • P).canonicalHeight = ((n ^ 2 : ℤ) : ℝ) * P.canonicalHeight := by
  rw [Point.canonicalHeight_zsmul]
  push_cast
  ring

/-- **`ĥ` is constant on torsion cosets**: `ĥ(P + T) = ĥ(P)` for a torsion point `T`; the
pairing kills torsion (the vendored `neronTatePairing_eq_zero_of_isOfFinAddOrder_*`). PROVED. -/
theorem canonicalHeight_add_of_isOfFinAddOrder (P : W.Point) {T : W.Point}
    (hT : IsOfFinAddOrder T) : (P + T).canonicalHeight = P.canonicalHeight := by
  rw [← neronTatePairing_self, ← neronTatePairing_self, neronTatePairing_add_left,
    neronTatePairing_add_right, neronTatePairing_add_right,
    neronTatePairing_eq_zero_of_isOfFinAddOrder_left hT P,
    neronTatePairing_eq_zero_of_isOfFinAddOrder_left hT T,
    neronTatePairing_eq_zero_of_isOfFinAddOrder_right P hT]
  ring

/-- The pairing only sees classes modulo torsion, in the first argument. PROVED. -/
theorem neronTatePairing_add_torsion_left (P Q : W.Point) {T : W.Point} (hT : IsOfFinAddOrder T) :
    W.neronTatePairing (P + T) Q = W.neronTatePairing P Q := by
  rw [neronTatePairing_add_left, neronTatePairing_eq_zero_of_isOfFinAddOrder_left hT, add_zero]

/-- The pairing only sees classes modulo torsion, in the second argument. PROVED. -/
theorem neronTatePairing_add_torsion_right (P Q : W.Point) {T : W.Point}
    (hT : IsOfFinAddOrder T) : W.neronTatePairing P (Q + T) = W.neronTatePairing P Q := by
  rw [neronTatePairing_add_right, neronTatePairing_eq_zero_of_isOfFinAddOrder_right _ hT,
    add_zero]

end Pairing

end ZInQ.Manuscript.RC.Height
