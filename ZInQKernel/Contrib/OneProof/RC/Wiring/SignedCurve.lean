import ZInQKernel.Contrib.OneProof.RC.Wiring.CalibrationLitArithmetic

/-!
# Theorem 5.3, Lane RC36: the family curves at a signed parameter

The calibration (Proposition `ex:arith-central-calibration`, tex 3987–4141) works at an address `x`
of a binary family with `h = h_x = ∏_q (q*)^{λ_q(x)}`, `q* = (−1)^{(q−1)/2} q`. The text's families
have one real sign and `h_0 = 1`, so `h_x > 0` (tex 1864–1869, 2685–2688), but Lean's `Family.h`
allows `h_x < 0` and `FinalFamilyAt` does not record the sign. The arithmetic statements of the
calibration discharge bind the central twist to a curve `Ecurve ℓ'` with `ℓ' : ℕ`, which reaches an
address only when `h_x > 0`. This file records the geometry of the curves
`E_t : y² = x(x − t)(x + 3t)` (`curve t`, tex 1761–1763) for a rational parameter `t` of either
sign, as the first layer of a signed restatement. No positivity is assumed anywhere, `t` is never
replaced by `|t|`, and `E_t` is never identified with `E_{|t|}`.

* `etw_eq_curve_mul`, `qtwist_curve_mul_eq_etw`: `E_ℓ^{(h)} = E_{ℓh}` and
  `E_{ℓh}^{(k)} = E_ℓ^{(hk)}` literally, for every integer `h` (the twist identity `curve_qtwist`
  holds for all rational parameters);
* `curve_isElliptic_iff`, `baseChange_curve_isElliptic_iff`: `E_t` is elliptic exactly when
  `t ≠ 0` (`Δ = 2304 t⁶`), also after base change to any field of characteristic zero;
* `centralCurve_eq_curve_mul`: the central twist of Kummer data `G` of an address is the base change
  of `E_{ℓh}`, for `h` of either sign; `isElliptic_curve_mul_of_genuineKummerData`,
  `ne_zero_of_genuineKummerData`: the existence of `G` forces `ℓh ≠ 0`, hence `E_{ℓh}` elliptic;
* why the sign cannot be dropped: `curve_c₆` (`c₆ = −2240 t³`), `variableChange_curve_ne_of_mul_neg`
  (no change of variables over `ℚ` carries `E_t` to `E_{t'}` when `t t' < 0`; in particular
  `E_t ≇ E_{|t|}` over `ℚ` for `t < 0`, `variableChange_curve_ne_curve_abs`), and
  `ecurve_mul_toNat_of_neg` (at `h < 0` the natural-number encoding `ℓ · h.toNat` gives the singular
  curve `E_0`, `not_isElliptic_curve_zero`).

Every declaration below is PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 WeierstrassCurve
open ZInQ.Manuscript.RC.TwistDictionary
open ZInQ.Contrib.RC53Assist.Calibration ZInQ.Contrib.RC53Assist.CalibrationIntegral

/-! **The twist identities, for every sign** -/

/-- **`E_ℓ^{(h)} = E_{ℓh}` for every integer `h`** (tex 1761–1763, 1829–1830): the twist `Etw ℓ h`
is, literally as a Weierstrass curve, the family curve with the signed parameter `ℓ h`. No sign
condition: the twist identity `curve_qtwist` holds for all rational parameters. Kind: PROVED. -/
theorem etw_eq_curve_mul (ℓ : ℕ) (h : ℤ) : Etw ℓ h = curve ((ℓ : ℚ) * h) :=
  ZInQ.Manuscript.RC.Wiring.curve_qtwist (ℓ : ℚ) (h : ℚ)

/-- **`E_{ℓh}^{(k)} = E_ℓ^{(hk)}` for all integers `h`, `k`**: the companion twist of the address
curve is the twist `E^{(hk)}` of the calibration's hypotheses (tex 3988–3991), as in the
sum-and-difference identity at the address (tex 2616–2626), with no sign condition.
Kind: PROVED. -/
theorem qtwist_curve_mul_eq_etw (ℓ : ℕ) (h k : ℤ) :
    qtwist (curve ((ℓ : ℚ) * h)) (k : ℚ) = Etw ℓ (h * k) := by
  rw [ZInQ.Manuscript.RC.Wiring.curve_qtwist, etw_eq_curve_mul, Int.cast_mul, mul_assoc]

/-! **Ellipticity exactly off `t = 0`** -/

/-- **`E_t` is elliptic exactly when `t ≠ 0`** (tex 1761–1765: `Δ(E_t) = 2304 t⁶`), for `t` of
either sign. Kind: PROVED. -/
theorem curve_isElliptic_iff (t : ℚ) : (curve t).IsElliptic ↔ t ≠ 0 := by
  constructor
  · intro h ht
    have hu := h.isUnit
    rw [curve_Δ, ht] at hu
    norm_num at hu
  · intro ht
    refine ⟨?_⟩
    rw [curve_Δ]
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero (by norm_num) (pow_ne_zero 6 ht))

/-- `E_t` is elliptic for every nonzero rational `t`, of either sign. Kind: PROVED. -/
theorem curve_isElliptic_of_ne {t : ℚ} (ht : t ≠ 0) : (curve t).IsElliptic :=
  (curve_isElliptic_iff t).mpr ht

/-- `E_0 : y² = x³` is singular. Kind: PROVED. -/
theorem not_isElliptic_curve_zero : ¬ (curve 0).IsElliptic :=
  fun h => (curve_isElliptic_iff 0).mp h rfl

/-- **Ellipticity after base change** to any field `K` of characteristic zero (for instance
`K = ℚ(√k)`): `(E_t)_K` is elliptic exactly when `t ≠ 0`. Kind: PROVED. -/
theorem baseChange_curve_isElliptic_iff (K : Type*) [Field K] [CharZero K] (t : ℚ) :
    ((curve t).baseChange K).IsElliptic ↔ t ≠ 0 := by
  rw [← curve_isElliptic_iff]
  constructor
  · intro h
    have hu := h.isUnit
    rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ] at hu
    refine ⟨isUnit_iff_ne_zero.mpr fun h0 => ?_⟩
    rw [h0, map_zero] at hu
    exact not_isUnit_zero hu
  · intro h
    infer_instance

/-! **The central twist of an address, for either sign** -/

/-- **The central curve at an address, for `h` of either sign** (tex 3987–3991, 4006–4013): for
Kummer data `G : GenuineKummerData K (Ecurve ℓ) h` over any number field `K`, the central twist
`E^{(h)} ⊗ K` is, literally, the base change of `E_{ℓh}` to `K`. This is the curve binding of the
signed arithmetic statements with the rational parameter `t = ℓ h`; unlike
`centralCurve_eq_of_pos` it needs no sign condition and no natural-number encoding of `h`.
Kind: PROVED. -/
theorem centralCurve_eq_curve_mul {K : Type} [Field K] [NumberField K] {ℓ : ℕ} {h : ℤ}
    (G : GenuineKummerData K (Ecurve ℓ) h) :
    centralCurve G = (curve ((ℓ : ℚ) * h)).baseChange K := by
  have hW : G.W = (Ecurve ℓ).map (algebraMap ℚ K) := G.hW
  have hd : ((h : ℤ) : K) = algebraMap ℚ K (h : ℚ) := (map_intCast (algebraMap ℚ K) h).symm
  have key : centralCurve G = (Etw ℓ h).baseChange K := by
    change twistK G.W ((h : ℤ) : K) = (twistK (Ecurve ℓ) (h : ℚ)).map (algebraMap ℚ K)
    rw [hW, hd, twistK_map]
  rw [key, etw_eq_curve_mul]

/-- **The signed parameter of an address is nonzero**: the existence of Kummer data `G` of the
address forces `ℓ h ≠ 0`, since the central twist is elliptic (`centralCurve_elliptic`).
Kind: PROVED. -/
theorem mul_ne_zero_of_genuineKummerData {K : Type} [Field K] [NumberField K] {ℓ : ℕ} {h : ℤ}
    (G : GenuineKummerData K (Ecurve ℓ) h) : (ℓ : ℚ) * h ≠ 0 := by
  have hE : ((curve ((ℓ : ℚ) * h)).baseChange K).IsElliptic := by
    rw [← centralCurve_eq_curve_mul G]
    infer_instance
  exact (baseChange_curve_isElliptic_iff K _).mp hE

/-- **`E_{ℓh}` is elliptic as soon as Kummer data of the address exist**, for `h` of either sign.
This discharges the ellipticity instance of the signed statements at an address. Kind: PROVED. -/
theorem isElliptic_curve_mul_of_genuineKummerData {K : Type} [Field K] [NumberField K] {ℓ : ℕ}
    {h : ℤ} (G : GenuineKummerData K (Ecurve ℓ) h) : (curve ((ℓ : ℚ) * h)).IsElliptic :=
  curve_isElliptic_of_ne (mul_ne_zero_of_genuineKummerData G)

/-- An address with Kummer data has `h ≠ 0` (of either sign). Kind: PROVED. -/
theorem ne_zero_of_genuineKummerData {K : Type} [Field K] [NumberField K] {ℓ : ℕ} {h : ℤ}
    (G : GenuineKummerData K (Ecurve ℓ) h) : h ≠ 0 := by
  intro h0
  apply mul_ne_zero_of_genuineKummerData G
  rw [h0, Int.cast_zero, mul_zero]

/-! **Why the sign is kept** -/

/-- `c₆(E_t) = −2240 t³`. Kind: PROVED. -/
theorem curve_c₆ (t : ℚ) : (curve t).c₆ = -2240 * t ^ 3 := by
  simp only [curve, WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆]
  ring

/-- `E_{−t}` is the twist of `E_t` by `−1`. Kind: PROVED. -/
theorem curve_neg_eq_qtwist (t : ℚ) : curve (-t) = qtwist (curve t) (-1) := by
  rw [ZInQ.Manuscript.RC.Wiring.curve_qtwist, mul_neg_one]

/-- **Opposite signs give curves that are not isomorphic over `ℚ`**: if `t t' < 0`, no change of
variables over `ℚ` carries `E_t` to `E_{t'}`. A change of variables multiplies `c₆` by `u⁻⁶ > 0`,
while `c₆(E_t) = −2240 t³` and `c₆(E_{t'})` have opposite signs. Kind: PROVED. -/
theorem variableChange_curve_ne_of_mul_neg {t t' : ℚ} (htt : t * t' < 0)
    (C : VariableChange ℚ) : C • curve t ≠ curve t' := by
  intro hC
  have h6 := congrArg WeierstrassCurve.c₆ hC
  rw [variableChange_c₆, curve_c₆, curve_c₆] at h6
  have ht : t ≠ 0 := by rintro rfl; simp at htt
  have ht' : t' ≠ 0 := by rintro rfl; simp at htt
  have hpos : 0 < ((C.u⁻¹ : ℚˣ) : ℚ) ^ 6 := Even.pow_pos (by decide) (Units.ne_zero _)
  have h1 : t * t' ^ 3 = ((C.u⁻¹ : ℚˣ) : ℚ) ^ 6 * t ^ 4 := by
    have hcube : ((C.u⁻¹ : ℚˣ) : ℚ) ^ 6 * t ^ 3 = t' ^ 3 := by linarith
    rw [← hcube]
    ring
  have h2 : 0 < ((C.u⁻¹ : ℚˣ) : ℚ) ^ 6 * t ^ 4 := mul_pos hpos (Even.pow_pos (by decide) ht)
  have h3 : t * t' ^ 3 < 0 := by
    have : t * t' ^ 3 = (t * t') * t' ^ 2 := by ring
    rw [this]
    exact mul_neg_of_neg_of_pos htt (by positivity)
  linarith

/-- **`E_t ≇ E_{|t|}` over `ℚ` for `t < 0`**: replacing a negative parameter by its absolute value
changes the rational isomorphism class of the curve. Kind: PROVED. -/
theorem variableChange_curve_ne_curve_abs {t : ℚ} (ht : t < 0) (C : VariableChange ℚ) :
    C • curve t ≠ curve |t| := by
  apply variableChange_curve_ne_of_mul_neg
  rw [abs_of_neg ht]
  nlinarith

/-- `E_{−t} ≠ E_t` for `t ≠ 0`. Kind: PROVED. -/
theorem curve_neg_ne {t : ℚ} (ht : t ≠ 0) : curve (-t) ≠ curve t := by
  intro h
  have h2 := congrArg WeierstrassCurve.a₂ h
  simp only [curve] at h2
  apply ht
  linarith

/-- **The natural-number encoding fails at negative addresses**: for `h < 0`, `h.toNat = 0`, so the
curve `Ecurve (ℓ · h.toNat)` of the positive route is the singular curve `E_0`, not the address
curve. Kind: PROVED. -/
theorem ecurve_mul_toNat_of_neg {ℓ : ℕ} {h : ℤ} (hh : h < 0) :
    Ecurve (ℓ * h.toNat) = curve 0 := by
  rw [Int.toNat_of_nonpos hh.le, mul_zero]
  show curve ((0 : ℕ) : ℚ) = curve 0
  rw [Nat.cast_zero]

end ZInQ.Manuscript.RC
