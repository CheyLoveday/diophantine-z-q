import Mathlib

/-!
# Calibration (4.6): the moving-prime fields of `CalibrationModel`

RC0's `CalibrationModel` (`RC/Wiring/Central.lean`) takes the moving prime `r_i` (tex L4066–4074)
through the fields

```
hchi : chimov = 1 ∨ chimov = -1
hmne : amov - 2 * chimov ≠ 0
hrmov : (2 : ℤ) ^ Bexp ∣ rmov - 1
hBexp : padicValInt 2 (amov - 2 * chimov) < Bexp
```

(owner RC4 / RC17). Lane RC17's `moving_character_genuine` / `moving_character_ecurve_genuine`
(`RC/TateWiring/Kummer.lean`) produces, for every `B`, a prime `r` with `2^B ∣ r − 1` and
`2^{c_E + 1} ∤ a_r − 2χ` for both signs `χ = ±1`. `movingFields_of_nondiv` turns exactly that
output, with `B ≥ c_E + 1`, into the four fields above (with `chimov` the actual quadratic sign
`χ_h(r_i)`, which is `±1`): `v₂(a_r − 2χ) ≤ c_E < B` ("`v₂ m_i ≤ c_E < B_i`", tex L4068–4070).

**Classification.** PROVED (GLUE to RC17's output).
-/

namespace ZInQ.Contrib.CloudB3RC53.Calibration

/-- **The moving-prime fields from RC17's non-divisibility** (tex L4066–4074). -/
theorem movingFields_of_nondiv (r a χ : ℤ) (c B : ℕ) (hχ : χ = 1 ∨ χ = -1)
    (hnd : ¬ (2 : ℤ) ^ (c + 1) ∣ a - 2 * χ) (hr : (2 : ℤ) ^ B ∣ r - 1) (hB : c + 1 ≤ B) :
    (χ = 1 ∨ χ = -1) ∧ a - 2 * χ ≠ 0 ∧ (2 : ℤ) ^ B ∣ r - 1 ∧ padicValInt 2 (a - 2 * χ) < B := by
  have hne : a - 2 * χ ≠ 0 := by
    intro h0
    exact hnd (by rw [h0]; exact dvd_zero _)
  refine ⟨hχ, hne, hr, ?_⟩
  have : padicValInt 2 (a - 2 * χ) < c + 1 := by
    by_contra hle
    rw [not_lt] at hle
    have := (padicValInt_dvd_iff (p := 2) (c + 1) (a - 2 * χ)).2 (Or.inr hle)
    exact hnd (by exact_mod_cast this)
  omega

end ZInQ.Contrib.CloudB3RC53.Calibration
