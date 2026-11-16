import ZInQKernel.Contrib.OneProof.CdOptimal.Structure
import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.WeilJacobi

/-!
# cd-optimal: the periods of `Φ₁` over `Γ₀(32) ∩ {d ≡ ±1 mod 8}` lie in every lattice of `C₁`

Task cd-optimal (2026-11-16). Report: `docs/research/cd-optimal.md`; log: `scratch/cd-optimal/log.md`.

On x0-32's eta model `y² = x³ + 4x` of `X₀(32) = 32a1`, `w = η(16τ)³/(η(8τ)η(32τ)²)` satisfies
`w² = x` (tyz-cm's `xC_eq_even`), so `s = −y/w` satisfies `s² = x² + 4` and `x₁ = (x + s)/2`,
`y₁ = y x₁²/(1 + x₁²)` satisfy `y₁² = x₁³ − x₁` (`C₁ = 32a2`) and `dx₁/2y₁ = dx/2y = 2πi f₁ dτ`
(`x₁ ↦ x₁ − 1/x₁` is the 2-isogeny `C₁ → 32a1`). `w` has the character `(2/d)` on `Γ₀(32)` (the
eta-quotient transformation law; printed leaf `EtaW32Character`), so `x₁, y₁` are invariant under
the `γ ∈ Γ₀(32)` with `(2/d) = 1`, and gz-weil's argument (`Unif.lean`, `period_mem_gen`) puts the
periods of `Φ₁` over those `γ` into every lattice `L₁` of `C₁` (`period_mem_C1`).

Then the twist (`LamCd_le_of_etaW32`): for `γ ∈ Γ₀(32 d²)`, `g (Φ_d(γτ) − Φ_d(τ)) =
Σ_a χ_d(a) ρ(γ'_a)` with all `γ'_a` sharing `d ≡ D (mod 32)`; `ρ(γ'_a) − ρ(γ'_0) ∈ L₁` and
`Σ_a χ_d(a) = 0`, so `Λ_d ⊆ g⁻¹ L₁ = L` for every lattice `L` of `C_d`. No `sorry`, no `axiom`.
-/

noncomputable section

open Complex CongruenceSubgroup Filter Topology
open scoped UpperHalfPlane MatrixGroups ComplexConjugate ZMod
open ZInQ.Contrib.TYZGenus
open ZInQ.GZWeil (eichlerCd moeb)
open Matrix.GeneralLinearGroup (upperRightHom)
open Matrix.SpecialLinearGroup (mapGL)

namespace ZInQ.CdOpt

/-! ## §1. The eta quotient `w` and the printed leaf -/

/-- `w(τ) = η(16τ)³ / (η(8τ) η(32τ)²)`. -/
def wC (z : ℂ) : ℂ := X0.etaD 16 z ^ 3 / (X0.etaD 8 z * X0.etaD 32 z ^ 2)

/-- **The transformation law of the eta quotient `w = η(16τ)³/(η(8τ)η(32τ)²)` on `Γ₀(32)`**
(printed leaf; Gordon–Hughes–Newman): `w(γτ) = (2/d) w(τ)` for `γ = [a, b; c, d] ∈ Γ₀(32)`.

The theorem of Newman (1957, 1959) and Gordon–Hughes (1981), as stated in K. Ono, *The web of
modularity*, Thm 1.64 (UNVERIFIED locator): for `f = ∏_{δ ∣ N} η(δτ)^{r_δ}` with `k = ½ Σ r_δ ∈ ℤ`,
`Σ δ r_δ ≡ 0` and `Σ (N/δ) r_δ ≡ 0 (mod 24)`, `f(γτ) = χ(d) (cτ + d)^k f(τ)` for `γ ∈ Γ₀(N)`, with
`χ(d) = ((−1)^k s / d)`, `s = ∏ δ^{r_δ}`. Here `N = 32`, `r₈ = −1`, `r₁₆ = 3`, `r₃₂ = −2`: `k = 0`,
`Σ δ r_δ = −24`, `Σ (32/δ) r_δ = 0`, `s = 2⁻¹`, so `χ(d) = (2/d)` (the symbol of `s = 2⁻¹ · 2²`;
`d` odd). Stated with Mathlib's `χ₈ = (2/·)` on `ℤ/8`, for every `γ` including `d < 0` (`χ₈` is even,
and `−γ` acts as `γ`). Checked numerically for 602 matrices (`scratch/cd-optimal/py/wchar.gp`). -/
def EtaW32Character : Prop :=
  ∀ γ : SL(2, ℤ), γ ∈ Gamma0 32 → ∀ τ : ℍ,
    wC ((γ • τ : ℍ) : ℂ) = ((ZMod.χ₈ ((γ 1 1 : ℤ) : ZMod 8) : ℤ) : ℂ) * wC τ

theorem wC_ne_zero (τ : ℍ) : wC τ ≠ 0 := by
  unfold wC
  have := X0.etaD_ne_zero (d := 8) (by norm_num) τ
  have := X0.etaD_ne_zero (d := 16) (by norm_num) τ
  have := X0.etaD_ne_zero (d := 32) (by norm_num) τ
  positivity

theorem wC_sq (τ : ℍ) : wC τ ^ 2 = X0.xC τ := by
  rw [ZInQ.Contrib.TYZGenus.Shimura.xC_eq_even τ, wC]
  ring

theorem differentiableAt_wC (τ : ℍ) : DifferentiableAt ℂ wC τ := by
  unfold wC
  refine DifferentiableAt.div ?_ ?_ ?_
  · exact (X0.differentiableAt_etaD (by norm_num) τ).pow 3
  · exact (X0.differentiableAt_etaD (by norm_num) τ).mul
      ((X0.differentiableAt_etaD (by norm_num) τ).pow 2)
  · exact mul_ne_zero (X0.etaD_ne_zero (by norm_num) τ)
      (pow_ne_zero 2 (X0.etaD_ne_zero (by norm_num) τ))

/-! ## §2. The model `x₁, y₁` of `C₁ : y² = x³ − x` -/

/-- `s = −y/w`, `s² = x² + 4`. -/
def sC (z : ℂ) : ℂ := -X0.yC z / wC z

/-- `x₁ = (x + s)/2`, a root of `X² − x X − 1`. -/
def x1C (z : ℂ) : ℂ := (X0.xC z + sC z) / 2

/-- `y₁ = y x₁² / (1 + x₁²)`. -/
def y1C (z : ℂ) : ℂ := X0.yC z * x1C z ^ 2 / (1 + x1C z ^ 2)

theorem xC_ne_zero (τ : ℍ) : X0.xC τ ≠ 0 := by
  rw [← wC_sq]; exact pow_ne_zero 2 (wC_ne_zero τ)

theorem sC_sq (τ : ℍ) : sC τ ^ 2 = X0.xC τ ^ 2 + 4 := by
  have hw := wC_ne_zero τ
  have hx := xC_ne_zero τ
  have he := ZInQ.Contrib.TYZGenus.Shimura.etaModelEquation τ
  have hw2 := wC_sq τ
  unfold sC
  rw [div_pow, neg_sq, he, hw2]
  field_simp

theorem x1_quad (τ : ℍ) : x1C τ ^ 2 - X0.xC τ * x1C τ - 1 = 0 := by
  have h := sC_sq τ
  unfold x1C
  linear_combination h / 4

theorem x1_ne_zero (τ : ℍ) : x1C τ ≠ 0 := by
  intro h; have := x1_quad τ; rw [h] at this; norm_num at this

theorem one_add_x1_sq_ne_zero (τ : ℍ) : 1 + x1C τ ^ 2 ≠ 0 := by
  intro h
  have hq := x1_quad τ
  have hx1 := x1_ne_zero τ
  -- then `x = 2 x₁` and `s = 0`, so `y = 0`
  have hx : X0.xC τ = 2 * x1C τ := by
    have : x1C τ * (X0.xC τ - 2 * x1C τ) = 0 := by linear_combination -hq - h
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 hx1
    · linear_combination h1
  have hs : sC τ = 0 := by
    have : sC τ = 2 * x1C τ - X0.xC τ := by unfold x1C; ring
    rw [this, hx]; ring
  have hy := X0.yC_ne_zero τ
  apply hy
  have hw := wC_ne_zero τ
  unfold sC at hs
  rw [div_eq_zero_iff] at hs
  rcases hs with h1 | h1
  · exact neg_eq_zero.mp h1
  · exact absurd h1 hw

theorem y1_sq (τ : ℍ) : y1C τ ^ 2 = x1C τ ^ 3 - x1C τ := by
  have hq := x1_quad τ
  have he := ZInQ.Contrib.TYZGenus.Shimura.etaModelEquation τ
  have hd := one_add_x1_sq_ne_zero τ
  have hx1 := x1_ne_zero τ
  -- `x = (x₁² − 1)/x₁`
  have hx : X0.xC τ * x1C τ = x1C τ ^ 2 - 1 := by linear_combination -hq
  unfold y1C
  rw [div_pow, mul_pow, he]
  rw [div_eq_iff (pow_ne_zero 2 hd)]
  have : (X0.xC τ ^ 3 + 4 * X0.xC τ) * x1C τ ^ 3 = (x1C τ ^ 2 - 1) * (1 + x1C τ ^ 2) ^ 2 := by
    have e : (X0.xC τ * x1C τ) ^ 3 + 4 * (X0.xC τ * x1C τ) * x1C τ ^ 2 =
        (x1C τ ^ 2 - 1) * (1 + x1C τ ^ 2) ^ 2 := by rw [hx]; ring
    linear_combination e
  linear_combination x1C τ * this

theorem y1_ne_zero (τ : ℍ) : y1C τ ≠ 0 := by
  unfold y1C
  exact div_ne_zero (mul_ne_zero (X0.yC_ne_zero τ) (pow_ne_zero 2 (x1_ne_zero τ)))
    (one_add_x1_sq_ne_zero τ)

theorem sC_eq (τ : ℍ) : sC τ * x1C τ = x1C τ ^ 2 + 1 := by
  have hq := x1_quad τ
  have : sC τ = 2 * x1C τ - X0.xC τ := by unfold x1C; ring
  rw [this]; linear_combination hq

/-! ## §3. Analyticity and the differential -/

theorem U_mem {σ : ℂ} (hσ : 0 < σ.im) : (⟨σ, hσ⟩ : ℍ) = (⟨σ, hσ⟩ : ℍ) := rfl

theorem differentiableAt_sC {σ : ℂ} (hσ : 0 < σ.im) : DifferentiableAt ℂ sC σ := by
  have h1 := X0.differentiableAt_yC ⟨σ, hσ⟩
  have h2 := differentiableAt_wC ⟨σ, hσ⟩
  exact h1.neg.div h2 (wC_ne_zero ⟨σ, hσ⟩)

theorem differentiableAt_x1C {σ : ℂ} (hσ : 0 < σ.im) : DifferentiableAt ℂ x1C σ :=
  ((X0.differentiableAt_xC ⟨σ, hσ⟩).add (differentiableAt_sC hσ)).div_const 2

theorem differentiableAt_y1C {σ : ℂ} (hσ : 0 < σ.im) : DifferentiableAt ℂ y1C σ := by
  have h1 := X0.differentiableAt_yC ⟨σ, hσ⟩
  have h2 := differentiableAt_x1C hσ
  exact (h1.mul (h2.pow 2)).div ((differentiableAt_const _).add (h2.pow 2))
    (one_add_x1_sq_ne_zero ⟨σ, hσ⟩)

theorem analyticAt_of_diff {f : ℂ → ℂ} (hf : ∀ σ : ℂ, 0 < σ.im → DifferentiableAt ℂ f σ)
    {σ : ℂ} (hσ : 0 < σ.im) : AnalyticAt ℂ f σ := by
  have hd : DifferentiableOn ℂ f {w : ℂ | 0 < w.im} := fun w hw => (hf w hw).differentiableWithinAt
  exact hd.analyticAt (ZInQ.GZWeil.U_open.mem_nhds hσ)

/-- `dx₁/dτ = 2 y₁ · 2πi f₁`. -/
theorem hasDerivAt_x1C {σ : ℂ} (hσ : 0 < σ.im) :
    HasDerivAt x1C (2 * y1C σ * (2 * Real.pi * I * X0.fC σ)) σ := by
  set τ : ℍ := ⟨σ, hσ⟩
  have hx : HasDerivAt X0.xC (4 * Real.pi * I * X0.fC σ * X0.yC σ) σ :=
    ZInQ.GZWeil.etaModelDifferential τ
  have hs := (differentiableAt_sC hσ).hasDerivAt
  set s' := deriv sC σ
  -- `2 s s' = 2 x x'` from `s² = x² + 4` near `σ`
  have hev : (fun z => sC z ^ 2) =ᶠ[𝓝 σ] (fun z => X0.xC z ^ 2 + 4) := by
    filter_upwards [ZInQ.GZWeil.U_open.mem_nhds hσ] with z hz
    exact sC_sq ⟨z, hz⟩
  have h1 : HasDerivAt (fun z => sC z ^ 2) (2 * sC σ * s') σ := by
    have := hs.pow 2; convert this using 1; push_cast; ring
  have h2 : HasDerivAt (fun z => X0.xC z ^ 2 + 4)
      (2 * X0.xC σ * (4 * Real.pi * I * X0.fC σ * X0.yC σ)) σ := by
    have := (hx.pow 2).add_const 4; convert this using 1; push_cast; ring
  have hss : 2 * sC σ * s' = 2 * X0.xC σ * (4 * Real.pi * I * X0.fC σ * X0.yC σ) :=
    (h1.congr_of_eventuallyEq hev.symm).unique h2
  have hd := (hx.add hs).div_const 2
  have hgoal : (4 * Real.pi * I * X0.fC σ * X0.yC σ + s') / 2 =
      2 * y1C σ * (2 * Real.pi * I * X0.fC σ) := by
    have hq := x1_quad τ
    have hse := sC_eq τ
    have hden := one_add_x1_sq_ne_zero τ
    have hx1 : x1C σ = (X0.xC σ + sC σ) / 2 := rfl
    have key : (4 * Real.pi * I * X0.fC σ * X0.yC σ + s') * (1 + x1C σ ^ 2) =
        2 * (4 * Real.pi * I * X0.fC σ * X0.yC σ) * x1C σ ^ 2 := by
      have hse' : sC σ * x1C σ = x1C σ ^ 2 + 1 := hse
      linear_combination x1C σ * hss / 2 - (4 * Real.pi * I * X0.fC σ * X0.yC σ + s') * hse' -
        (4 * Real.pi * I * X0.fC σ * X0.yC σ) * x1C σ * 2 * hx1
    have hden' : 1 + x1C σ ^ 2 ≠ 0 := hden
    unfold y1C
    field_simp
    linear_combination key
  unfold x1C
  exact hd.congr_deriv hgoal

end ZInQ.CdOpt
