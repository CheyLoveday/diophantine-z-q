import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.JacobiLambdaDeriv
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.NumberTheory.ModularForms.Identities
import ZInQKernel.Contrib.TYZGenus.ShimuraThetaDup

/-!
# h33-fix: `j(τ)` and `j(32τ)` as rational functions of the eta model of `X₀(32)`

Task h33-fix (2026-11-17). Report: `docs/research/h33-fix.md`; scratch: `scratch/h33-fix/`.

* `E₄ = ½(θ₂⁸ + θ₃⁸ + θ₄⁸)`, `E₆ = ½(θ₃⁴ + θ₄⁴)(θ₂⁴ + θ₃⁴)(θ₄⁴ − θ₂⁴)` (`e4T_eq`, `e6T_eq`): the theta
  expressions are level-one modular forms (Mathlib's S/T generation), and Mathlib's spaces of weight 4, 6 have rank one;
* `j = 1728 E₄³/(E₄³ − E₆²)` (`j_theta`, Mathlib's `Δ = (E₄³ − E₆²)/1728`);
* Landen (jacobi-lambda) and the kernel's `x = 2θ₃(16τ)/θ₂(16τ)`, `y = −θ₂(4τ)²/θ₂(16τ)²` give
  `j(τ)·jDen(x, y) = jNum(x, y)` (`j_eta`) and `j(32τ)·j32Den(x) = j32Num(x)` (`j32_eta`), with nonzero denominators.

No `sorry`, no `axiom`.
-/

open UpperHalfPlane hiding I
open Complex Filter ModularForm SlashInvariantForm
open scoped MatrixGroups Real Topology Manifold

noncomputable section

namespace ZInQ.H33Fix

open ZInQ.GZWeil (thetaTwo thetaThree thetaFour)
open ZInQ.JacobiLambda

/-! ## T and S transformations -/

theorem exp_pi_I_sq (n : ℤ) : cexp (π * I * (n : ℂ) ^ 2) = cexp (π * I * n) := by
  obtain ⟨m, hm⟩ := Int.even_mul_pred_self n
  have : (n : ℂ) ^ 2 = n + 2 * m := by
    have h : (n : ℂ) * (n - 1) = m + m := by exact_mod_cast hm
    linear_combination h
  rw [this, show π * I * ((n : ℂ) + 2 * m) = π * I * n + m * (2 * π * I) by ring, Complex.exp_add,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem jacobiTheta₂_add_one_right (z τ : ℂ) :
    jacobiTheta₂ z (τ + 1) = jacobiTheta₂ (z + 1 / 2) τ := by
  unfold jacobiTheta₂
  congr 1 with n
  unfold jacobiTheta₂_term
  rw [show 2 * π * I * n * z + π * I * n ^ 2 * (τ + 1) =
      (2 * π * I * n * z + π * I * n ^ 2 * τ) + π * I * (n : ℂ) ^ 2 by ring,
    show 2 * π * I * n * (z + 1 / 2) + π * I * n ^ 2 * τ =
      (2 * π * I * n * z + π * I * n ^ 2 * τ) + π * I * n by ring,
    Complex.exp_add, Complex.exp_add, exp_pi_I_sq]
  simp only [Complex.exp_add]

theorem thetaThree_add_one (τ : ℂ) : thetaThree (τ + 1) = thetaFour τ := by
  simp only [ZInQ.GZWeil.thetaThree, ZInQ.GZWeil.thetaFour, jacobiTheta₂_add_one_right, zero_add]

theorem thetaFour_add_one (τ : ℂ) : thetaFour (τ + 1) = thetaThree τ := by
  simp only [ZInQ.GZWeil.thetaThree, ZInQ.GZWeil.thetaFour, jacobiTheta₂_add_one_right]
  rw [show (1 / 2 : ℂ) + 1 / 2 = 0 + 1 by norm_num, jacobiTheta₂_add_left]

theorem thetaTwo_add_one (τ : ℂ) : thetaTwo (τ + 1) = cexp (π * I / 4) * thetaTwo τ := by
  simp only [ZInQ.GZWeil.thetaTwo, jacobiTheta₂_add_one_right]
  rw [show (τ + 1) / 2 + 1 / 2 = τ / 2 + 1 by ring, jacobiTheta₂_add_left,
    show π * I * (τ + 1) / 4 = π * I / 4 + π * I * τ / 4 by ring, Complex.exp_add]
  ring

/-- `r(τ) = (-iτ)^{1/2}`. -/
def rS (τ : ℂ) : ℂ := (-I * τ) ^ (1 / 2 : ℂ)

theorem rS_pow_four (τ : ℂ) : rS τ ^ 4 = -τ ^ 2 := by
  unfold rS
  rw [← Complex.cpow_nat_mul]
  norm_num
  rw [mul_pow, I_sq]; ring

theorem rS_ne_zero {τ : ℂ} (hτ : τ ≠ 0) : rS τ ≠ 0 := by
  intro h
  have h4 := rS_pow_four τ
  rw [h, zero_pow (by norm_num)] at h4
  have : τ ^ 2 = 0 := by linear_combination h4
  exact hτ (pow_eq_zero_iff two_ne_zero |>.mp this)

theorem thetaThree_S {τ : ℂ} (hτ : τ ≠ 0) : thetaThree (-1 / τ) = rS τ * thetaThree τ := by
  have h := jacobiTheta₂_functional_equation 0 τ
  simp only [ZInQ.GZWeil.thetaThree]
  rw [h]
  have hr := rS_ne_zero hτ
  simp only [rS] at hr ⊢
  field_simp
  simp

theorem thetaTwo_S {τ : ℂ} (hτ : τ ≠ 0) : thetaTwo (-1 / τ) = rS τ * thetaFour τ := by
  have h := jacobiTheta₂_functional_equation (1 / 2) τ
  simp only [ZInQ.GZWeil.thetaTwo, ZInQ.GZWeil.thetaFour]
  rw [h]
  have hr := rS_ne_zero hτ
  simp only [rS] at hr ⊢
  have e1 : (-1 / τ) / 2 = -((1 / 2) / τ) := by ring
  rw [e1, jacobiTheta₂_neg_left]
  have e2 : cexp (π * I * (-1 / τ) / 4) = cexp (-π * I * (1 / 2) ^ 2 / τ) := by
    congr 1; field_simp; ring
  rw [e2]
  field_simp

theorem thetaFour_S {τ : ℂ} (hτ : τ ≠ 0) : thetaFour (-1 / τ) = rS τ * thetaTwo τ := by
  have h := jacobiTheta₂_functional_equation (τ / 2) τ
  simp only [ZInQ.GZWeil.thetaTwo, ZInQ.GZWeil.thetaFour]
  rw [h]
  have hr := rS_ne_zero hτ
  simp only [rS] at hr ⊢
  have e1 : τ / 2 / τ = 1 / 2 := by field_simp
  rw [e1]
  have e2 : cexp (π * I * τ / 4) * cexp (-π * I * (τ / 2) ^ 2 / τ) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]; congr 1; field_simp; ring
  rw [show ∀ a b c d : ℂ, a * (b * (1 / a * c * d)) = (a * (1 / a)) * (b * c) * d from
    fun a b c d => by ring, mul_one_div_cancel hr, e2, one_mul, one_mul]

/-! ## The theta forms -/

/-- `A = θ₂⁴`, `B = θ₃⁴`, `C = θ₄⁴`. -/
def tA (τ : ℂ) : ℂ := thetaTwo τ ^ 4
def tB (τ : ℂ) : ℂ := thetaThree τ ^ 4
def tC (τ : ℂ) : ℂ := thetaFour τ ^ 4

theorem tA_add_one (τ : ℂ) : tA (τ + 1) = -tA τ := by
  unfold tA; rw [thetaTwo_add_one, mul_pow, ← Complex.exp_nat_mul]
  rw [show ((4 : ℕ) : ℂ) * (π * I / 4) = π * I by push_cast; ring, Complex.exp_pi_mul_I]; ring
theorem tB_add_one (τ : ℂ) : tB (τ + 1) = tC τ := by unfold tB tC; rw [thetaThree_add_one]
theorem tC_add_one (τ : ℂ) : tC (τ + 1) = tB τ := by unfold tB tC; rw [thetaFour_add_one]

theorem tA_S {τ : ℂ} (hτ : τ ≠ 0) : tA (-1 / τ) = -τ ^ 2 * tC τ := by
  unfold tA tC; rw [thetaTwo_S hτ, mul_pow, rS_pow_four]
theorem tB_S {τ : ℂ} (hτ : τ ≠ 0) : tB (-1 / τ) = -τ ^ 2 * tB τ := by
  unfold tB; rw [thetaThree_S hτ, mul_pow, rS_pow_four]
theorem tC_S {τ : ℂ} (hτ : τ ≠ 0) : tC (-1 / τ) = -τ ^ 2 * tA τ := by
  unfold tA tC; rw [thetaFour_S hτ, mul_pow, rS_pow_four]

/-- `½(θ₂⁸ + θ₃⁸ + θ₄⁸)`. -/
def e4T (τ : ℂ) : ℂ := (tA τ ^ 2 + tB τ ^ 2 + tC τ ^ 2) / 2
/-- `½(θ₃⁴ + θ₄⁴)(θ₂⁴ + θ₃⁴)(θ₄⁴ − θ₂⁴)`. -/
def e6T (τ : ℂ) : ℂ := (tB τ + tC τ) * (tA τ + tB τ) * (tC τ - tA τ) / 2

theorem e4T_add_one (τ : ℂ) : e4T (τ + 1) = e4T τ := by
  unfold e4T; rw [tA_add_one, tB_add_one, tC_add_one]; ring
theorem e6T_add_one (τ : ℂ) : e6T (τ + 1) = e6T τ := by
  unfold e6T; rw [tA_add_one, tB_add_one, tC_add_one]; ring
theorem e4T_S {τ : ℂ} (hτ : τ ≠ 0) : e4T (-1 / τ) = τ ^ 4 * e4T τ := by
  unfold e4T; rw [tA_S hτ, tB_S hτ, tC_S hτ]; ring
theorem e6T_S {τ : ℂ} (hτ : τ ≠ 0) : e6T (-1 / τ) = τ ^ 6 * e6T τ := by
  unfold e6T; rw [tA_S hτ, tB_S hτ, tC_S hτ]; ring

/-! ## Slash invariance -/

set_option backward.isDefEq.respectTransparency.types false in
theorem slash_T_of {f : ℂ → ℂ} {k : ℤ} (hf : ∀ τ, f (τ + 1) = f τ) :
    ((fun τ : ℍ => f τ) ∣[k] ModularGroup.T) = fun τ : ℍ => f τ := by
  ext z
  rw [SL_slash_apply, denom, modular_T_smul, ModularGroup.T]
  simp
  rw [add_comm]; exact hf _

set_option backward.isDefEq.respectTransparency.types false in
theorem slash_S_of {f : ℂ → ℂ} {k : ℕ} (hf : ∀ τ : ℂ, τ ≠ 0 → f (-1 / τ) = τ ^ k * f τ) :
    ((fun τ : ℍ => f τ) ∣[(k : ℤ)] ModularGroup.S) = fun τ : ℍ => f τ := by
  ext z
  rw [slash_S_apply]
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  have e : (-(z : ℂ))⁻¹ = -1 / (z : ℂ) := by rw [neg_div, one_div, inv_neg]
  change f ((-(z : ℂ))⁻¹) * (z : ℂ) ^ (-(k : ℤ)) = f z
  rw [e, hf _ hz, zpow_neg, zpow_natCast]
  field_simp

/-! ## Holomorphy and limits -/

theorem mdiff_of {f : ℂ → ℂ} (hf : ∀ τ : ℂ, 0 < τ.im → DifferentiableAt ℂ f τ) :
    MDiff (fun τ : ℍ => f τ) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine DifferentiableOn.congr (f := f) (fun z hz => (hf z hz).differentiableWithinAt) ?_
  intro z hz
  simp [Function.comp, ofComplex_apply_of_im_pos hz]

theorem diff_thetaFour {s : ℂ} (hs : 0 < s.im) : DifferentiableAt ℂ thetaFour s :=
  differentiableAt_jacobiTheta₂_snd _ hs

theorem diff_e4T {s : ℂ} (hs : 0 < s.im) : DifferentiableAt ℂ e4T s := by
  have h2 := differentiableAt_thetaTwo' hs
  have h3 := differentiableAt_thetaThree' hs
  have h4 := diff_thetaFour hs
  unfold e4T tA tB tC
  fun_prop

theorem diff_e6T {s : ℂ} (hs : 0 < s.im) : DifferentiableAt ℂ e6T s := by
  have h2 := differentiableAt_thetaTwo' hs
  have h3 := differentiableAt_thetaThree' hs
  have h4 := diff_thetaFour hs
  unfold e6T tA tB tC
  fun_prop

theorem tendsto_of_bound {f : ℍ → ℂ} {l : ℂ} {C : ℝ}
    (h : ∀ τ : ℍ, 1 ≤ τ.im → ‖f τ - l‖ ≤ C * Real.exp (-π * τ.im / 4)) :
    Tendsto f atImInfty (𝓝 l) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hlim : Tendsto (fun t : ℝ => C * Real.exp (-π * t / 4)) atTop (𝓝 0) := by
    have : Tendsto (fun t : ℝ => Real.exp (-π * t / 4)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun t : ℝ => -π * t / 4) atTop atBot := by
        have : Tendsto (fun t : ℝ => (-π / 4) * t) atTop atBot :=
          Filter.Tendsto.const_mul_atTop_of_neg (by nlinarith [Real.pi_pos]) tendsto_id
        refine this.congr fun t => by ring
      exact Real.tendsto_exp_atBot.comp h1
    simpa using this.const_mul C
  obtain ⟨T, hT⟩ := (hlim.eventually (gt_mem_nhds hε)).exists_forall_of_atTop
  rw [Filter.eventually_iff, UpperHalfPlane.atImInfty_mem]
  refine ⟨max T 1, fun z hz => ?_⟩
  have h1 := h z (le_trans (le_max_right _ _) hz)
  have h2 := hT z.im (le_trans (le_max_left _ _) hz)
  simp only [Set.mem_setOf_eq, dist_eq_norm]
  linarith


theorem tendsto_thetaThree : Tendsto (fun τ : ℍ => thetaThree τ) atImInfty (𝓝 1) := by
  refine tendsto_of_bound (C := 3) fun τ hτ => ?_
  have := τ.im_pos
  refine (norm_thetaThree_sub_one_le hτ).trans ?_
  gcongr
  simp only [UpperHalfPlane.coe_im]
  nlinarith [Real.pi_pos]

theorem tendsto_thetaFour : Tendsto (fun τ : ℍ => thetaFour τ) atImInfty (𝓝 1) := by
  refine tendsto_of_bound (C := 3) fun τ hτ => ?_
  have := τ.im_pos
  refine (norm_thetaFour_sub_one_le hτ).trans ?_
  gcongr
  simp only [UpperHalfPlane.coe_im]
  nlinarith [Real.pi_pos]

theorem tendsto_thetaTwo : Tendsto (fun τ : ℍ => thetaTwo τ) atImInfty (𝓝 0) := by
  refine tendsto_of_bound (C := 5) fun τ hτ => ?_
  have h := norm_thT_sub_two_le hτ
  have hT : ‖thT τ‖ ≤ 5 := by
    have h1 : 3 * Real.exp (-π * (τ : ℂ).im) ≤ 3 := by
      have : Real.exp (-π * (τ : ℂ).im) ≤ 1 := Real.exp_le_one_iff.mpr (by
        have := τ.im_pos; simp only [UpperHalfPlane.coe_im]; nlinarith [Real.pi_pos])
      linarith
    calc ‖thT τ‖ = ‖(thT τ - 2) + 2‖ := by ring_nf
      _ ≤ ‖thT τ - 2‖ + ‖(2 : ℂ)‖ := norm_add_le _ _
      _ ≤ 5 := by
        have : ‖(2 : ℂ)‖ = 2 := by simp
        linarith
  rw [sub_zero, thetaTwo_eq, norm_mul]
  have he : ‖cexp (π * I * (τ : ℂ) / 4)‖ = Real.exp (-π * τ.im / 4) := by
    rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]
  rw [he, mul_comm]
  gcongr

theorem tendsto_e4T : Tendsto (fun τ : ℍ => e4T τ) atImInfty (𝓝 1) := by
  have h := ((tendsto_thetaTwo.pow 4).pow 2).add (((tendsto_thetaThree.pow 4).pow 2).add
    ((tendsto_thetaFour.pow 4).pow 2))
  have h' := h.div_const 2
  convert h' using 2 with τ
  · simp [e4T, tA, tB, tC]; ring
  · norm_num

theorem tendsto_e6T : Tendsto (fun τ : ℍ => e6T τ) atImInfty (𝓝 1) := by
  have h2 := tendsto_thetaTwo.pow 4
  have h3 := tendsto_thetaThree.pow 4
  have h4 := tendsto_thetaFour.pow 4
  have h := (((h3.add h4).mul (h2.add h3)).mul (h4.sub h2)).div_const 2
  convert h using 2 with τ
  · simp [e6T, tA, tB, tC]
  · norm_num

/-! ## The modular forms and the identification with `E₄`, `E₆` -/

theorem e4T_slash (γ : SL(2, ℤ)) : (fun τ : ℍ => e4T τ) ∣[(4 : ℤ)] γ = fun τ : ℍ => e4T τ :=
  slash_action_generators_SL2Z (slash_S_of (k := 4) fun τ hτ => e4T_S hτ)
    (slash_T_of e4T_add_one) γ

theorem e6T_slash (γ : SL(2, ℤ)) : (fun τ : ℍ => e6T τ) ∣[(6 : ℤ)] γ = fun τ : ℍ => e6T τ :=
  slash_action_generators_SL2Z (slash_S_of (k := 6) fun τ hτ => e6T_S hτ)
    (slash_T_of e6T_add_one) γ

/-- `½(θ₂⁸ + θ₃⁸ + θ₄⁸)` as a modular form of weight 4, level one. -/
def e4TForm : ModularForm 𝒮ℒ 4 where
  toFun := fun τ : ℍ => e4T τ
  slash_action_eq' := fun _ ⟨γ, hγ⟩ ↦ hγ ▸ e4T_slash γ
  holo' := mdiff_of fun _ hs => diff_e4T hs
  bdd_at_cusps' hc := (OnePoint.isBoundedAt_iff_forall_SL2Z hc).mpr fun γ _ ↦
    (e4T_slash γ).symm ▸ (tendsto_e4T.isBigO_one ℝ)

def e6TForm : ModularForm 𝒮ℒ 6 where
  toFun := fun τ : ℍ => e6T τ
  slash_action_eq' := fun _ ⟨γ, hγ⟩ ↦ hγ ▸ e6T_slash γ
  holo' := mdiff_of fun _ hs => diff_e6T hs
  bdd_at_cusps' hc := (OnePoint.isBoundedAt_iff_forall_SL2Z hc).mpr fun γ _ ↦
    (e6T_slash γ).symm ▸ (tendsto_e6T.isBigO_one ℝ)

theorem eq_of_rank_one {k : ℤ} (hrank : Module.rank ℂ (ModularForm 𝒮ℒ k) = 1)
    {g F : ModularForm 𝒮ℒ k} (hg1 : Tendsto g atImInfty (𝓝 1)) (hF1 : Tendsto F atImInfty (𝓝 1)) :
    ⇑F = ⇑g := by
  have hg : g ≠ 0 := fun h ↦ one_ne_zero (tendsto_nhds_unique (h ▸ hg1) tendsto_const_nhds)
  obtain ⟨c, hc⟩ :=
    (finrank_eq_one_iff_of_nonzero' g hg).mp (Module.rank_eq_one_iff_finrank_eq_one.mp hrank) F
  have hfg : ⇑F = c • ⇑g := (congrArg DFunLike.coe hc).symm
  have hlim : Tendsto (c • ⇑g) atImInfty (𝓝 (c * 1)) := hg1.const_mul c
  rw [hfg] at hF1
  have : c * 1 = 1 := tendsto_nhds_unique hlim hF1
  rw [hfg, show c = 1 by simpa using this, one_smul]

theorem e4T_eq (τ : ℍ) : e4T τ = E₄ τ :=
  congrFun (eq_of_rank_one (F := e4TForm) levelOne_weight_four_rank_one
    EisensteinSeries.tendsto_E_atImInfty tendsto_e4T) τ

theorem e6T_eq (τ : ℍ) : e6T τ = E₆ τ :=
  congrFun (eq_of_rank_one (F := e6TForm) levelOne_weight_six_rank_one
    EisensteinSeries.tendsto_E_atImInfty tendsto_e6T) τ

/-- **`j = E₄³/Δ = 1728 E₄³/(E₄³ − E₆²)` in theta constants.** -/
theorem j_theta (τ : ℍ) :
    E₄ τ ^ 3 / discriminant τ = 1728 * e4T τ ^ 3 / (e4T τ ^ 3 - e6T τ ^ 2) := by
  rw [e4T_eq, e6T_eq, discriminant_eq_E₄_cube_sub_E₆_sq]
  have h := discriminant_ne_zero τ
  rw [discriminant_eq_E₄_cube_sub_E₆_sq] at h
  have h' : E₄ τ ^ 3 - E₆ τ ^ 2 ≠ 0 := fun e => h (by rw [e]; simp)
  field_simp


/-! ## Landen chain: `j(τ)` and `j(32τ)` from the eta model -/

section Landen

open ZInQ.Contrib.TYZGenus

theorem im_mul_pos {c : ℝ} (hc : 0 < c) (τ : ℍ) : 0 < ((c : ℂ) * τ).im := by
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  exact mul_pos hc τ.im_pos

theorem x_theta (τ : ℍ) : X0.xC τ = 2 * thetaThree (16 * τ) / thetaTwo (16 * τ) := by
  rw [Shimura.xC_theta, Shimura.Qt_def]
  simp only [ZInQ.GZWeil.thetaThree, ZInQ.GZWeil.thetaTwo]
  rw [show (16 : ℂ) * τ / 2 = 8 * τ by ring, ← Complex.exp_nat_mul]
  congr 3; push_cast; ring

theorem y_theta (τ : ℍ) : X0.yC τ = -(thetaTwo (4 * τ) ^ 2 / thetaTwo (16 * τ) ^ 2) := by
  rw [Shimura.yC_theta, Shimura.Qt_def]
  simp only [ZInQ.GZWeil.thetaTwo]
  rw [show (16 : ℂ) * τ / 2 = 8 * τ by ring, show (4 : ℂ) * τ / 2 = 2 * τ by ring]
  have h1 : cexp (π * I * (4 * τ) / 4) ^ 2 = cexp (2 * π * I * τ) := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have h2 : cexp (π * I * (16 * τ) / 4) ^ 2 = cexp (2 * π * I * τ) ^ 3 * cexp (2 * π * I * τ) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]; congr 1; push_cast; ring
  rw [mul_pow, mul_pow, h1, h2]
  have h0 : cexp (2 * π * I * τ) ≠ 0 := Complex.exp_ne_zero _
  field_simp

/-- The integer polynomial expressions (scaled by 16 against the text). -/
def a2E {R : Type*} [CommRing R] (x y : R) : R := -16 * y * (x + 2) ^ 2
def b2E {R : Type*} [CommRing R] (x y : R) : R := ((x + 2) ^ 2 - 4 * y) ^ 2
def e4E {R : Type*} [CommRing R] (x y : R) : R :=
  a2E x y ^ 2 + 14 * a2E x y * b2E x y + b2E x y ^ 2
def e6E {R : Type*} [CommRing R] (x y : R) : R :=
  (a2E x y + b2E x y) * ((a2E x y + b2E x y) ^ 2 - 36 * a2E x y * b2E x y)
/-- `j(τ)·jDen(x, y) = jNum(x, y)`. -/
def jDen {R : Type*} [CommRing R] (x y : R) : R := e4E x y ^ 3 - e6E x y ^ 2
def jNum {R : Type*} [CommRing R] (x y : R) : R := 1728 * e4E x y ^ 3

/-- level `32τ`: `S = x²` (scaled by 4). -/
def f4E {R : Type*} [CommRing R] (x : R) : R :=
  x ^ 8 + 14 * x ^ 4 * (x ^ 4 - 16) + (x ^ 4 - 16) ^ 2
def f6E {R : Type*} [CommRing R] (x : R) : R :=
  (2 * x ^ 4 - 16) * ((2 * x ^ 4 - 16) ^ 2 - 36 * x ^ 4 * (x ^ 4 - 16))
def j32Den {R : Type*} [CommRing R] (x : R) : R := f4E x ^ 3 - f6E x ^ 2
def j32Num {R : Type*} [CommRing R] (x : R) : R := 1728 * f4E x ^ 3

theorem e4T_e6T_landen {τ : ℂ} (hτ : 0 < τ.im) :
    e4T τ = (thetaTwo (2 * τ) ^ 4) ^ 2 + 14 * thetaTwo (2 * τ) ^ 4 * thetaThree (2 * τ) ^ 4 +
      (thetaThree (2 * τ) ^ 4) ^ 2 ∧
    e6T τ = (thetaTwo (2 * τ) ^ 4 + thetaThree (2 * τ) ^ 4) *
      ((thetaTwo (2 * τ) ^ 4 + thetaThree (2 * τ) ^ 4) ^ 2 -
        36 * thetaTwo (2 * τ) ^ 4 * thetaThree (2 * τ) ^ 4) := by
  have h2 := landen_two hτ
  have h3 := landen_three hτ
  have h4 := landen_four hτ
  have eA : tA τ = 4 * thetaTwo (2 * τ) ^ 2 * thetaThree (2 * τ) ^ 2 := by
    unfold tA; rw [show thetaTwo τ ^ 4 = (thetaTwo τ ^ 2) ^ 2 by ring, h2]; ring
  have eB : tB τ = (thetaThree (2 * τ) ^ 2 + thetaTwo (2 * τ) ^ 2) ^ 2 := by
    unfold tB; rw [show thetaThree τ ^ 4 = (thetaThree τ ^ 2) ^ 2 by ring, h3]
  have eC : tC τ = (thetaThree (2 * τ) ^ 2 - thetaTwo (2 * τ) ^ 2) ^ 2 := by
    unfold tC; rw [show thetaFour τ ^ 4 = (thetaFour τ ^ 2) ^ 2 by ring, h4]
  constructor
  · unfold e4T; rw [eA, eB, eC]; ring
  · unfold e6T; rw [eA, eB, eC]; ring

theorem e4T_e6T_up {w : ℂ} (hw : 0 < w.im) :
    16 * e4T (2 * w) = (thetaThree w ^ 2) ^ 4 + 14 * (thetaThree w ^ 2) ^ 2 * thetaFour w ^ 4 +
      (thetaFour w ^ 4) ^ 2 ∧
    -64 * e6T (2 * w) = ((thetaThree w ^ 2) ^ 2 + thetaFour w ^ 4) *
      (((thetaThree w ^ 2) ^ 2 + thetaFour w ^ 4) ^ 2 - 36 * (thetaThree w ^ 2) ^ 2 * thetaFour w ^ 4) := by
  have h3 := landen_three hw
  have h4 := landen_four hw
  have h34 := landen_three_four hw
  have eB : thetaThree (2 * w) ^ 2 = (thetaThree w ^ 2 + thetaFour w ^ 2) / 2 := by
    rw [h3, h4]; ring
  have eA : thetaTwo (2 * w) ^ 2 = (thetaThree w ^ 2 - thetaFour w ^ 2) / 2 := by
    rw [h3, h4]; ring
  have tA' : tA (2 * w) = ((thetaThree w ^ 2 - thetaFour w ^ 2) / 2) ^ 2 := by
    unfold tA; rw [show thetaTwo (2 * w) ^ 4 = (thetaTwo (2 * w) ^ 2) ^ 2 by ring, eA]
  have tB' : tB (2 * w) = ((thetaThree w ^ 2 + thetaFour w ^ 2) / 2) ^ 2 := by
    unfold tB; rw [show thetaThree (2 * w) ^ 4 = (thetaThree (2 * w) ^ 2) ^ 2 by ring, eB]
  have tC' : tC (2 * w) = thetaThree w ^ 2 * thetaFour w ^ 2 := by
    unfold tC; rw [show thetaFour (2 * w) ^ 4 = (thetaFour (2 * w) ^ 2) ^ 2 by ring, ← h34]; ring
  constructor
  · unfold e4T; rw [tA', tB', tC']; ring
  · unfold e6T; rw [tA', tB', tC']; ring

/-- **`j(τ)` as a rational function of the eta model.** -/
theorem j_eta (τ : ℍ) :
    E₄ τ ^ 3 / discriminant τ * jDen (X0.xC τ) (X0.yC τ) = jNum (X0.xC τ) (X0.yC τ) ∧
      jDen (X0.xC τ) (X0.yC τ) ≠ 0 := by
  have hτ := τ.im_pos
  have h2 : 0 < (2 * (τ : ℂ)).im := by simpa using im_mul_pos (c := 2) (by norm_num) τ
  have h4 : 0 < (4 * (τ : ℂ)).im := by simpa using im_mul_pos (c := 4) (by norm_num) τ
  have h8 : 0 < (8 * (τ : ℂ)).im := by simpa using im_mul_pos (c := 8) (by norm_num) τ
  have h16 : 0 < (16 * (τ : ℂ)).im := by simpa using im_mul_pos (c := 16) (by norm_num) τ
  obtain ⟨e4, e6⟩ := e4T_e6T_landen hτ
  -- level 2τ from level 4τ
  have l2 := landen_two h2
  have l3 := landen_three h2
  rw [show 2 * (2 * (τ : ℂ)) = 4 * τ by ring] at l2 l3
  -- level 4τ from level 16τ
  have m3 := landen_three h4
  have n3 := landen_three h8
  have n2 := landen_two h8
  rw [show 2 * (4 * (τ : ℂ)) = 8 * τ by ring] at m3
  rw [show 2 * (8 * (τ : ℂ)) = 16 * τ by ring] at n3 n2
  have hx := x_theta τ
  have hy := y_theta τ
  set u := thetaTwo (16 * τ)
  have hu : u ≠ 0 := thetaTwo_ne_zero h16
  set x := X0.xC τ
  set y := X0.yC τ
  have hv : thetaThree (16 * τ) = x * u / 2 := by rw [hx]; field_simp
  have ha : thetaTwo (4 * τ) ^ 2 = -y * u ^ 2 := by rw [hy]; field_simp
  have hb : thetaThree (4 * τ) ^ 2 = u ^ 2 * (x + 2) ^ 2 / 4 := by
    rw [m3, n3, n2, hv]; ring
  have hA2 : thetaTwo (2 * τ) ^ 4 = u ^ 4 * a2E x y / 16 := by
    rw [show thetaTwo (2 * τ) ^ 4 = (thetaTwo (2 * τ) ^ 2) ^ 2 by ring, l2,
      show (2 * thetaTwo (4 * τ) * thetaThree (4 * τ)) ^ 2 =
        4 * thetaTwo (4 * τ) ^ 2 * thetaThree (4 * τ) ^ 2 by ring, ha, hb]
    unfold a2E; ring
  have hB2 : thetaThree (2 * τ) ^ 4 = u ^ 4 * b2E x y / 16 := by
    rw [show thetaThree (2 * τ) ^ 4 = (thetaThree (2 * τ) ^ 2) ^ 2 by ring, l3, ha, hb]
    unfold b2E; ring
  have hE4 : e4T τ = u ^ 8 * e4E x y / 256 := by rw [e4, hA2, hB2]; unfold e4E; ring
  have hE6 : e6T τ = u ^ 12 * e6E x y / 4096 := by rw [e6, hA2, hB2]; unfold e6E; ring
  have hj := j_theta τ
  have hD : e4T τ ^ 3 - e6T τ ^ 2 ≠ 0 := by
    rw [e4T_eq, e6T_eq]
    intro h
    apply discriminant_ne_zero τ
    rw [discriminant_eq_E₄_cube_sub_E₆_sq, h, zero_div]
  have hDu : e4T τ ^ 3 - e6T τ ^ 2 = u ^ 24 * jDen x y / 2 ^ 24 := by
    rw [hE4, hE6]; unfold jDen; ring
  have hden : jDen x y ≠ 0 := by
    intro h; apply hD; rw [hDu, h]; ring
  refine ⟨?_, hden⟩
  rw [hj, hDu, hE4]
  unfold jNum
  field_simp
  ring

/-- **`j(32τ)` as a rational function of `x`.** -/
theorem j32_eta (τ : ℍ) (τ32 : ℍ) (h32 : (τ32 : ℂ) = 32 * τ) :
    E₄ τ32 ^ 3 / discriminant τ32 * j32Den (X0.xC τ) = j32Num (X0.xC τ) ∧
      j32Den (X0.xC τ) ≠ 0 := by
  have h16 : 0 < (16 * (τ : ℂ)).im := by simpa using im_mul_pos (c := 16) (by norm_num) τ
  obtain ⟨e4, e6⟩ := e4T_e6T_up h16
  rw [show 2 * (16 * (τ : ℂ)) = 32 * τ by ring, ← h32] at e4 e6
  have hq := jacobi_quartic h16
  have hx := x_theta τ
  set u := thetaTwo (16 * τ)
  have hu : u ≠ 0 := thetaTwo_ne_zero h16
  set x := X0.xC τ
  have hv : thetaThree (16 * τ) = x * u / 2 := by rw [hx]; field_simp
  have hs : thetaThree (16 * τ) ^ 2 = u ^ 2 * x ^ 2 / 4 := by rw [hv]; ring
  have ht : thetaFour (16 * τ) ^ 4 = u ^ 4 * (x ^ 4 - 16) / 16 := by
    have : thetaFour (16 * τ) ^ 4 = thetaThree (16 * τ) ^ 4 - u ^ 4 := by rw [hq]; ring
    rw [this, show thetaThree (16 * τ) ^ 4 = (thetaThree (16 * τ) ^ 2) ^ 2 by ring, hs]; ring
  have hE4 : e4T τ32 = u ^ 8 * f4E x / 4096 := by
    have := e4; rw [hs, ht] at this; unfold f4E; linear_combination this / 16
  have hE6 : e6T τ32 = -(u ^ 12 * f6E x / 2 ^ 18) := by
    have := e6; rw [hs, ht] at this; unfold f6E; linear_combination -this / 64
  have hj := j_theta τ32
  have hD : e4T τ32 ^ 3 - e6T τ32 ^ 2 ≠ 0 := by
    rw [e4T_eq, e6T_eq]
    intro h
    apply discriminant_ne_zero τ32
    rw [discriminant_eq_E₄_cube_sub_E₆_sq, h, zero_div]
  have hDu : e4T τ32 ^ 3 - e6T τ32 ^ 2 = u ^ 24 * j32Den x / 2 ^ 36 := by
    rw [hE4, hE6]; unfold j32Den; ring
  have hden : j32Den x ≠ 0 := by
    intro h; apply hD; rw [hDu, h]; ring
  refine ⟨?_, hden⟩
  rw [hj, hDu, hE4]
  unfold j32Num
  field_simp
  ring

end Landen

end ZInQ.H33Fix
