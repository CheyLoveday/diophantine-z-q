import ZInQKernel.Contrib.OneProof.RC.TwistDictionary.Model
import ZInQKernel.RouteK.Rank.LFunctionCd
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# Lane RC18-twist: points of quadratic twists over finite fields

* `natCard_point_twistInt_of_ringChar_ne_two`: over a finite field `𝔽_q` of odd characteristic,
  `|W^{(D)}(𝔽_q)| = q + 1 − χ(D) (q + 1 − |W(𝔽_q)|)` (points at infinity included), i.e.
  `a(W^{(D)}) = χ(D) a(W)` for the quadratic character `χ` of `𝔽_q`.
* `natCard_point_twistInt_zmod_two`: over `𝔽₂`, the Artin–Schreier twist `twistInt W 1 c` has
  `|W^{tw}(𝔽₂)| = 3 − ε (3 − |W(𝔽₂)|)`, `ε = 1` if `c = 0` and `ε = −1` if `c = 1`.

## Method

* Odd characteristic: a curve `y² = g(x)` has `q + 1 + Σ_x χ(g(x))` points
  (`natCard_point_eq_sum_quadraticChar`). The cubic of `twistK W d` is `d³ f(x/d)` with
  `f(x) = x³ + (b₂/4) x² + (b₄/2) x + b₆/4`, so substituting `x = d x'` gives
  `#(twistK W d)(𝔽_q) = q + 1 + χ(d) Σ_x χ(f(x))` (`natCard_point_twistK`). Finally `twistInt W D c`
  is a change of variables of `twistK W D` and `W` one of `twistK W 1`.
* Characteristic two: both counts are `1 + #{affine solutions}`
  (`natCard_point_zmod_two_eq_card_filter`), and the identity between the affine counts is a finite
  computation over the `2⁶` choices of `(a₁, a₂, a₃, a₄, a₆, c)` (`card_filter_twistInt_zmod_two`).
-/

namespace ZInQ.Manuscript.RC.TwistDictionary

open WeierstrassCurve

section OddCharacteristic

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k]

/-- The number of square roots of `a` in a finite field of odd characteristic is `χ(a) + 1`. -/
theorem natCard_sq_eq_eq_quadraticChar_add_one (hk : ringChar k ≠ 2) (a : k) :
    (Nat.card {y : k // y ^ 2 = a} : ℤ) = quadraticChar k a + 1 := by
  rw [← quadraticChar_card_sqrts hk a, ← Nat.card_eq_card_toFinset]
  rfl

/-- **Points of `y² = g(x)`**: an elliptic curve with `a₁ = a₃ = 0` over a finite field of odd
characteristic has `q + 1 + Σ_x χ(x³ + a₂ x² + a₄ x + a₆)` points (point at infinity included). -/
theorem natCard_point_eq_sum_quadraticChar (hk : ringChar k ≠ 2) (E : WeierstrassCurve k)
    [E.IsElliptic] (h₁ : E.a₁ = 0) (h₃ : E.a₃ = 0) :
    (Nat.card E.toAffine.Point : ℤ) =
      Fintype.card k + 1 + ∑ x : k, quadraticChar k (x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆) := by
  have e : {xy : k × k // E.toAffine.Equation xy.1 xy.2} ≃
      Σ x : k, {y : k // y ^ 2 = x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆} :=
    (Equiv.subtypeEquivRight fun xy => by
      rw [Affine.equation_iff, h₁, h₃, zero_mul, zero_mul, add_zero, add_zero]).trans
      (Equiv.subtypeProdEquivSigmaSubtype fun x y => y ^ 2 = x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆)
  rw [Nat.card_congr (ZInQ.Literature.pointEquivOption E), Finite.card_option, Nat.card_congr e,
    Nat.card_sigma]
  push_cast
  simp only [natCard_sq_eq_eq_quadraticChar_add_one hk, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one]
  ring

omit [Fintype k] [DecidableEq k] in
/-- The twist `twistK W d` of an elliptic curve by `d ≠ 0` is elliptic (when `2 ≠ 0`). -/
theorem twistK_isElliptic_of_ne_zero (h2 : (2 : k) ≠ 0) (W : WeierstrassCurve k) [W.IsElliptic]
    {d : k} (hd : d ≠ 0) : (twistK W d).IsElliptic :=
  ⟨by rw [twistK_Δ W h2]; exact ((Ne.isUnit hd).pow 6).mul W.isUnit_Δ⟩

/-- **Points of `twistK W d`**: with `f(x) = x³ + (b₂/4) x² + (b₄/2) x + b₆/4`, the cubic of
`twistK W d` is `d³ f(x/d)`, so `#(twistK W d)(𝔽_q) = q + 1 + χ(d) Σ_x χ(f(x))` for `d ≠ 0`. -/
theorem natCard_point_twistK (hk : ringChar k ≠ 2) (W : WeierstrassCurve k) {d : k} (hd : d ≠ 0)
    [(twistK W d).IsElliptic] :
    (Nat.card (twistK W d).toAffine.Point : ℤ) = Fintype.card k + 1 + quadraticChar k d *
      ∑ x : k, quadraticChar k (x ^ 3 + W.b₂ / 4 * x ^ 2 + W.b₄ / 2 * x + W.b₆ / 4) := by
  rw [natCard_point_eq_sum_quadraticChar hk (twistK W d) rfl rfl, Finset.mul_sum]
  congr 1
  refine (Fintype.sum_bijective _ (mulLeft_bijective₀ d hd) _ _ fun x => ?_).symm
  have hx : (d * x) ^ 3 + (twistK W d).a₂ * (d * x) ^ 2 + (twistK W d).a₄ * (d * x) +
      (twistK W d).a₆ = d ^ 3 * (x ^ 3 + W.b₂ / 4 * x ^ 2 + W.b₄ / 2 * x + W.b₆ / 4) := by
    simp only [twistK]; ring
  have h3 : quadraticChar k d ^ 3 = quadraticChar k d := by
    rw [pow_succ, quadraticChar_sq_one hd, one_mul]
  rw [hx, map_mul, map_pow, h3]

end OddCharacteristic

/-- **Points of a quadratic twist over a finite field of odd characteristic** (PROVED):
`|W^{(D)}(𝔽_q)| = q + 1 − χ(D) (q + 1 − |W(𝔽_q)|)` for `D = 1 + 4c ≠ 0`, `χ` the quadratic character
of `𝔽_q` (points at infinity included). -/
theorem natCard_point_twistInt_of_ringChar_ne_two {k : Type*} [Field k] [Fintype k]
    [DecidableEq k] (hk : ringChar k ≠ 2) (W : WeierstrassCurve k) [W.IsElliptic] {D c : k}
    (h : D = 1 + 4 * c) (hD : D ≠ 0) :
    (Nat.card (twistInt W D c).toAffine.Point : ℤ) =
      Fintype.card k + 1 - quadraticChar k D * (Fintype.card k + 1 - Nat.card W.toAffine.Point) := by
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hk
  have := twistK_isElliptic_of_ne_zero h2 W hD
  have := twistK_isElliptic_of_ne_zero h2 W one_ne_zero
  have eD : Nat.card (twistInt W D c).toAffine.Point = Nat.card (twistK W D).toAffine.Point := by
    calc Nat.card (twistInt W D c).toAffine.Point
        = Nat.card ((sqChange (twistInt W D c))⁻¹ • twistK W D).toAffine.Point := by
          rw [← twistInt_eq_smul_twistK W h2 h]
      _ = Nat.card (twistK W D).toAffine.Point :=
          ZInQ.Literature.natCard_point_variableChange _ _
  have e1 : Nat.card W.toAffine.Point = Nat.card (twistK W 1).toAffine.Point := by
    rw [twistK_one W h2, ZInQ.Literature.natCard_point_variableChange]
  rw [eD, e1, natCard_point_twistK hk W hD, natCard_point_twistK hk W one_ne_zero, MulChar.map_one]
  ring

section CharacteristicTwo

/-- Over `𝔽₂`, the points of an elliptic curve are its affine solutions and the point at
infinity. -/
theorem natCard_point_zmod_two_eq_card_filter (V : WeierstrassCurve (ZMod 2)) [V.IsElliptic] :
    Nat.card V.toAffine.Point = (Finset.univ.filter (fun xy : ZMod 2 × ZMod 2 =>
      xy.2 ^ 2 + V.a₁ * xy.1 * xy.2 + V.a₃ * xy.2 =
        xy.1 ^ 3 + V.a₂ * xy.1 ^ 2 + V.a₄ * xy.1 + V.a₆)).card + 1 := by
  have e : {xy : ZMod 2 × ZMod 2 // V.toAffine.Equation xy.1 xy.2} ≃
      {xy : ZMod 2 × ZMod 2 // xy.2 ^ 2 + V.a₁ * xy.1 * xy.2 + V.a₃ * xy.2 =
        xy.1 ^ 3 + V.a₂ * xy.1 ^ 2 + V.a₄ * xy.1 + V.a₆} :=
    Equiv.subtypeEquivRight fun xy => Affine.equation_iff xy.1 xy.2
  rw [Nat.card_congr (ZInQ.Literature.pointEquivOption V), Finite.card_option, Nat.card_congr e,
    Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- The affine count behind `natCard_point_twistInt_zmod_two`, for all `2⁶` choices of the
coefficients of `W` and of `c` (the coefficients of `twistInt W 1 c` are written out). -/
theorem card_filter_twistInt_zmod_two : ∀ a₁ a₂ a₃ a₄ a₆ c : ZMod 2,
    (((Finset.univ.filter (fun xy : ZMod 2 × ZMod 2 =>
      xy.2 ^ 2 + a₁ * xy.1 * xy.2 + (1 * a₃) * xy.2 =
        xy.1 ^ 3 + (1 * a₂ + c * a₁ ^ 2) * xy.1 ^ 2 + (1 ^ 2 * a₄ + 2 * c * 1 * a₁ * a₃) * xy.1 +
          (1 ^ 3 * a₆ + c * 1 ^ 2 * a₃ ^ 2))).card + 1 : ℕ) : ℤ) =
      3 - (if c = 0 then 1 else -1) * (3 - ((Finset.univ.filter (fun xy : ZMod 2 × ZMod 2 =>
        xy.2 ^ 2 + a₁ * xy.1 * xy.2 + a₃ * xy.2 =
          xy.1 ^ 3 + a₂ * xy.1 ^ 2 + a₄ * xy.1 + a₆)).card + 1 : ℕ)) := by
  decide

end CharacteristicTwo

/-- **The Artin–Schreier twist over `𝔽₂`** (PROVED): over `ZMod 2`, `twistInt W 1 c` has
`|W^{tw}(𝔽₂)| = 3 − ε (3 − |W(𝔽₂)|)` with `ε = 1` for `c = 0` and `ε = −1` for `c = 1`. -/
theorem natCard_point_twistInt_zmod_two (W : WeierstrassCurve (ZMod 2)) [W.IsElliptic]
    (c : ZMod 2) :
    (Nat.card (twistInt W 1 c).toAffine.Point : ℤ) =
      3 - (if c = 0 then 1 else -1) * (3 - Nat.card W.toAffine.Point) := by
  have h1 : (1 : ZMod 2) = 1 + 4 * c := by
    have h4 : (4 : ZMod 2) = 0 := by decide
    rw [h4, zero_mul, add_zero]
  have := twistInt_isElliptic W h1 isUnit_one
  rw [natCard_point_zmod_two_eq_card_filter (twistInt W 1 c),
    natCard_point_zmod_two_eq_card_filter W]
  exact card_filter_twistInt_zmod_two W.a₁ W.a₂ W.a₃ W.a₄ W.a₆ c

end ZInQ.Manuscript.RC.TwistDictionary
