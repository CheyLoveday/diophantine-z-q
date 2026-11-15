import ZInQKernel.Contrib.OneProof.GrossZagierHeegner
import ZInQKernel.Contrib.OneProof.RingClassLattice

/-! gz-heegner development: the analytic glue (copies of the definitions of `Heegner.lean`). -/

noncomputable section

open UpperHalfPlane Complex
open ZInQ.Contrib.TYZGenus.CM (HeegnerForm cmPoint)
open scoped MatrixGroups
open ZInQ.Contrib.TYZGenus.Shimura ZInQ.Contrib.TYZGenus.CM HeckeRing.GL2 WeierstrassCurve
  ZInQ.Contrib.TYZDecomp.CurveA
open scoped WeierstrassCurve.Affine Manifold

namespace ZInQ.GZHeegner

/-- `g` is **regular at `τ`** (holomorphic in a neighbourhood, with value `g τ`). -/
def RegularAt (g : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) : Prop :=
  AnalyticAt ℂ (g ∘ UpperHalfPlane.ofComplex) (τ : ℂ)

section Param

variable (E : WeierstrassCurve ℚ) (L : PeriodPair) {N : ℕ} [NeZero N] (f : Newform N 2) (c : ℚ)

/-- `z(τ) = c·φ_f(τ) ∈ ℂ`, the parameter of `φ(τ) ∈ ℂ/L`. -/
def zPar (τ : UpperHalfPlane) : ℂ := (c : ℂ) * ZInQ.GZHL3.eichler f τ

/-- `x(φ(τ)) = ℘_L(c φ_f(τ)) − b₂/12` (junk at the poles `c φ_f(τ) ∈ L`). -/
def xPar (τ : UpperHalfPlane) : ℂ := L.weierstrassP (zPar f c τ) - (E⁄ℂ).b₂ / 12

/-- `y(φ(τ)) = (℘'_L(c φ_f(τ)) − a₁x − a₃)/2`. -/
def yPar (τ : UpperHalfPlane) : ℂ :=
  (L.derivWeierstrassP (zPar f c τ) - (E⁄ℂ).a₁ * xPar E L f c τ - (E⁄ℂ).a₃) / 2

open Classical in
/-- `1/(x(φ(τ)) − t)`, `0` at the poles of `x∘φ`. -/
def gPar (t : ℚ) (τ : UpperHalfPlane) : ℂ :=
  if zPar f c τ ∈ L.lattice then 0 else (xPar E L f c τ - t)⁻¹

end Param

/-- The hypotheses shared by the analytic glue: `E/ℚ` with the L-series of the newform `f` of
level `N`, trivial character, `L` the period lattice of `E`, `c ∈ ℚ^×` with `c Λ_f ⊆ L`. -/
def ParamSetting (E : WeierstrassCurve ℚ) {N : ℕ} [NeZero N] (f : Newform N 2) (L : PeriodPair)
    (c : ℚ) : Prop :=
  f.χ = 1 ∧ (∀ n : ℕ, n ≠ 0 → ZInQ.GZDecomp.coeff f n = (E.LFunction n : ℂ)) ∧
    ZInQ.GZHL3.IsPeriodLattice E L ∧ c ≠ 0 ∧ ZInQ.GZHL3.PeriodsIn f c L

/-- **(GLUE, analysis) Meromorphy and regularity of the coordinates of `φ`.** `x∘φ`, `y∘φ` and
`1/(x∘φ − t)` are meromorphic on `ℍ`; `x∘φ`, `y∘φ` are regular where `c φ_f(τ) ∉ L`, and
`1/(x∘φ − t)` (value `0` at the poles of `x∘φ`) is regular where `c φ_f(τ) ∈ L` or `x(φ(τ)) ≠ t`.
Content: `φ_f` is holomorphic on `ℍ` (Hecke's bound `aₙ(f) = O(n)`; Mathlib
`ModularForms/Bounds.lean`), `℘_L` is holomorphic off `L` with a double pole at each point of `L`
(Mathlib `Analysis/SpecialFunctions/Elliptic/Weierstrass.lean`). -/
def ParamRegular : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (N : ℕ) [NeZero N] (f : Newform N 2)
    (L : PeriodPair) (c : ℚ), ParamSetting E f L c →
    (∀ τ : UpperHalfPlane, MeromorphicAt (xPar E L f c ∘ UpperHalfPlane.ofComplex) (τ : ℂ) ∧
      MeromorphicAt (yPar E L f c ∘ UpperHalfPlane.ofComplex) (τ : ℂ) ∧
      ∀ t : ℚ, MeromorphicAt (gPar E L f c t ∘ UpperHalfPlane.ofComplex) (τ : ℂ)) ∧
    (∀ τ : UpperHalfPlane, zPar f c τ ∉ L.lattice →
      RegularAt (xPar E L f c) τ ∧ RegularAt (yPar E L f c) τ) ∧
    (∀ (t : ℚ) (τ : UpperHalfPlane), (zPar f c τ ∈ L.lattice ∨ xPar E L f c τ ≠ t) →
      RegularAt (gPar E L f c t) τ)

/-- `q = e^{2πiτ}` as a function of `w ∈ ℂ`. -/
def qC (w : ℂ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * w)

theorem norm_qC_lt_one {w : ℂ} (hw : 0 < w.im) : ‖qC w‖ < 1 := by
  rw [qC, Complex.norm_exp]
  have : (2 * Real.pi * Complex.I * w).re = -(2 * Real.pi * w.im) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this]
  calc Real.exp (-(2 * Real.pi * w.im)) < Real.exp 0 :=
        Real.exp_lt_exp.2 (by nlinarith [Real.pi_pos])
    _ = 1 := Real.exp_zero

/-- Every `r ∈ [0, 1)` is `|q(τ)|` for some `τ ∈ ℍ`... (for `r > 0`). -/
theorem exists_qC_norm {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ τ : UpperHalfPlane, ‖qC τ‖ = r := by
  have hl : 0 < -Real.log r := by
    have := Real.log_neg hr0 hr1; linarith
  refine ⟨⟨Complex.I * ((-Real.log r / (2 * Real.pi) : ℝ) : ℂ), ?_⟩, ?_⟩
  · simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, one_mul, zero_add]
    exact div_pos hl (by positivity)
  · rw [qC, Complex.norm_exp]
    show Real.exp (2 * Real.pi * Complex.I * (Complex.I * ((-Real.log r / (2 * Real.pi) : ℝ) : ℂ))).re = r
    have : (2 * Real.pi * Complex.I * (Complex.I * ((-Real.log r / (2 * Real.pi) : ℝ) : ℂ))).re =
        Real.log r := by
      have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
      simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat]
      field_simp
      ring
    rw [this, Real.exp_log hr0]


/-! ## The Weierstrass side: `℘`, `℘'` and `1/(℘ − c₀)` as functions on `ℂ` -/

section Wp

variable (L : PeriodPair)

theorem analyticAt_wp {z : ℂ} (hz : z ∉ L.lattice) : AnalyticAt ℂ L.weierstrassP z :=
  L.differentiableOn_weierstrassP.analyticAt (L.isClosed_lattice.isOpen_compl.mem_nhds hz)

theorem analyticAt_dwp {z : ℂ} (hz : z ∉ L.lattice) : AnalyticAt ℂ L.derivWeierstrassP z :=
  L.analyticOnNhd_derivWeierstrassP z hz

theorem meromorphicAt_inv_pow (z₀ : ℂ) (n : ℕ) : MeromorphicAt (fun z : ℂ => 1 / (z - z₀) ^ n) z₀ :=
  (MeromorphicAt.const 1 z₀).div (((MeromorphicAt.id z₀).sub (MeromorphicAt.const z₀ z₀)).pow n)

theorem meromorphicAt_wp (z₀ : ℂ) : MeromorphicAt L.weierstrassP z₀ := by
  by_cases h : z₀ ∈ L.lattice
  · have e : L.weierstrassP =
        fun z => L.weierstrassPExcept z₀ z + (1 / (z - z₀) ^ 2 - 1 / z₀ ^ 2) :=
      funext fun z => (L.weierstrassPExcept_add ⟨z₀, h⟩ z).symm
    rw [e]
    exact (L.analyticAt_weierstrassPExcept z₀).meromorphicAt.add
      ((meromorphicAt_inv_pow z₀ 2).sub (MeromorphicAt.const _ z₀))
  · exact (analyticAt_wp L h).meromorphicAt

theorem meromorphicAt_dwp (z₀ : ℂ) : MeromorphicAt L.derivWeierstrassP z₀ := by
  by_cases h : z₀ ∈ L.lattice
  · have e : L.derivWeierstrassP =
        fun z => L.derivWeierstrassPExcept z₀ z - 2 * (1 / (z - z₀) ^ 3) :=
      funext fun z => by rw [← L.derivWeierstrassPExcept_sub ⟨z₀, h⟩ z]; ring
    rw [e]
    exact (L.analyticAt_derivWeierstrassPExcept z₀).meromorphicAt.sub
      ((MeromorphicAt.const 2 z₀).mul (meromorphicAt_inv_pow z₀ 3))
  · exact (analyticAt_dwp L h).meromorphicAt

open Classical in
/-- `z ↦ 1/(℘(z) − c₀)`, `0` on `L`. -/
def phiT (c₀ : ℂ) (z : ℂ) : ℂ := if z ∈ L.lattice then 0 else (L.weierstrassP z - c₀)⁻¹

theorem analyticAt_phiT_of_mem (c₀ : ℂ) {z₀ : ℂ} (h : z₀ ∈ L.lattice) :
    AnalyticAt ℂ (phiT L c₀) z₀ := by
  set A : ℂ → ℂ := fun z => L.weierstrassPExcept z₀ z - 1 / z₀ ^ 2 - c₀ with hAdef
  have hA : AnalyticAt ℂ A z₀ := (L.analyticAt_weierstrassPExcept z₀).sub analyticAt_const
    |>.sub analyticAt_const
  set R : ℂ → ℂ := fun z => (z - z₀) ^ 2 / (1 + (z - z₀) ^ 2 * A z) with hRdef
  have hR : AnalyticAt ℂ R z₀ := by
    apply AnalyticAt.div
    · fun_prop
    · exact analyticAt_const.add (((analyticAt_id.sub analyticAt_const).pow 2).mul hA)
    · simp
  apply hR.congr
  filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds z₀] with z hz
  by_cases hzz : z = z₀
  · subst hzz; simp [phiT, h, R]
  · have hzL : z ∉ L.lattice := fun hz' => hz ⟨hz', hzz⟩
    have hw : z - z₀ ≠ 0 := sub_ne_zero.2 hzz
    simp only [phiT, hzL, if_false, R, A]
    rw [← L.weierstrassPExcept_add ⟨z₀, h⟩ z]
    have : L.weierstrassPExcept z₀ z + (1 / (z - z₀) ^ 2 - 1 / z₀ ^ 2) - c₀ =
        (1 + (z - z₀) ^ 2 * (L.weierstrassPExcept z₀ z - 1 / z₀ ^ 2 - c₀)) / (z - z₀) ^ 2 := by
      field_simp; ring
    rw [this, inv_div]

theorem phiT_eventuallyEq {c₀ z₀ : ℂ} (h : z₀ ∉ L.lattice) :
    phiT L c₀ =ᶠ[nhds z₀] fun z => (L.weierstrassP z - c₀)⁻¹ := by
  filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds h] with z hz
  simp only [phiT, if_neg (show z ∉ L.lattice from hz)]

theorem analyticAt_phiT_of_ne (c₀ : ℂ) {z₀ : ℂ} (h : z₀ ∉ L.lattice)
    (hne : L.weierstrassP z₀ ≠ c₀) : AnalyticAt ℂ (phiT L c₀) z₀ :=
  (((analyticAt_wp L h).sub analyticAt_const).inv (sub_ne_zero.2 hne)).congr
    (phiT_eventuallyEq L h).symm

theorem meromorphicAt_phiT (c₀ z₀ : ℂ) : MeromorphicAt (phiT L c₀) z₀ := by
  by_cases h : z₀ ∈ L.lattice
  · exact (analyticAt_phiT_of_mem L c₀ h).meromorphicAt
  · exact (((meromorphicAt_wp L z₀).sub (MeromorphicAt.const c₀ z₀)).inv).congr
      ((phiT_eventuallyEq L h).symm.filter_mono nhdsWithin_le_nhds)

end Wp

/-! ## The Eichler integral is holomorphic on `ℍ` -/

section Eichler

variable {N : ℕ} [NeZero N] (f : Newform N 2)

/-- The coefficients of `φ_f = Σ aₙ/n qⁿ`. -/
def eCoeff (n : ℕ) : ℂ := if n = 0 then 0 else ZInQ.GZDecomp.coeff f n / n

/-- `φ_f` as a power series in `q`. -/
def eSeries : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ (eCoeff f)

theorem hasSum_newform (τ : UpperHalfPlane) :
    HasSum (fun n => ZInQ.GZDecomp.coeff f n * qC τ ^ n) (f.toCuspForm τ) := by
  have h := ModularForm.hasSum_qExpansion f.toCuspForm one_pos
    (TauCeti.one_mem_strictPeriods_Gamma1_map N) τ
  have hq : Function.Periodic.qParam 1 (τ : ℂ) = qC τ := by
    simp [Function.Periodic.qParam, qC]
  rw [hq] at h
  exact h

theorem coeff_zero_newform : ZInQ.GZDecomp.coeff f 0 = 0 :=
  CuspFormClass.qExpansion_coeff_zero f.toCuspForm one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map N)

theorem eSeries_radius (r : NNReal) (hr : (r : ℝ) < 1) : (r : ENNReal) ≤ (eSeries f).radius := by
  rcases eq_or_lt_of_le r.2 with h0 | h0
  · have : r = 0 := by ext; exact h0.symm
    rw [this]; simp
  obtain ⟨σ, hσ⟩ := exists_qC_norm h0 hr
  apply (eSeries f).le_radius_of_tendsto (l := 0)
  have ht := ((hasSum_newform f σ).summable.tendsto_atTop_zero).norm
  simp only [norm_zero] at ht
  refine squeeze_zero (fun n => by positivity) (fun n => ?_) ht
  rw [eSeries, FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow, hσ]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  unfold eCoeff
  split_ifs with hn
  · simp
  · rw [norm_div]
    have h1 : (1 : ℝ) ≤ ‖(n : ℂ)‖ := by
      rw [Complex.norm_natCast]; exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
    exact div_le_self (norm_nonneg _) h1

theorem eSeries_mem_ball {w : ℂ} (hw : ‖w‖ < 1) : w ∈ Metric.eball (0 : ℂ) (eSeries f).radius := by
  obtain ⟨r, hr1, hr2⟩ := exists_between hw
  have hr0 : 0 ≤ r := le_trans (norm_nonneg _) hr1.le
  set r' : NNReal := ⟨r, hr0⟩
  rw [Metric.mem_eball, edist_zero_right]
  calc (‖w‖₊ : ENNReal) < (r' : ENNReal) := by rw [ENNReal.coe_lt_coe]; exact_mod_cast hr1
    _ ≤ _ := eSeries_radius f r' hr2

theorem eSeries_radius_pos : 0 < (eSeries f).radius := by
  have := eSeries_mem_ball f (w := 0) (by simp)
  rw [Metric.mem_eball] at this; exact lt_of_le_of_lt bot_le this

theorem eichler_eq (τ : UpperHalfPlane) : ZInQ.GZHL3.eichler f τ = (eSeries f).sum (qC τ) := by
  have hs := (eSeries f).hasSum (eSeries_mem_ball f (norm_qC_lt_one τ.im_pos))
  simp only [eSeries, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] at hs
  have h1 := (hasSum_nat_add_iff' 1).mpr hs
  simp only [Finset.range_one, Finset.sum_singleton, eCoeff] at h1
  unfold ZInQ.GZHL3.eichler
  refine (HasSum.tsum_eq ?_)
  convert h1 using 1
  · funext n
    rw [if_neg (Nat.succ_ne_zero n), qC, ← Complex.exp_nat_mul]
    push_cast
    ring_nf
  · simp [eSeries]

theorem analyticAt_eSum {w : ℂ} (hw : ‖w‖ < 1) : AnalyticAt ℂ (eSeries f).sum w :=
  ((eSeries f).hasFPowerSeriesOnBall (eSeries_radius_pos f)).analyticAt_of_mem
    (eSeries_mem_ball f hw)

theorem analyticAt_qC (w : ℂ) : AnalyticAt ℂ qC w := by unfold qC; fun_prop

theorem eichler_ofComplex_eventuallyEq (τ : UpperHalfPlane) :
    (ZInQ.GZHL3.eichler f ∘ UpperHalfPlane.ofComplex) =ᶠ[nhds (τ : ℂ)]
      fun w => (eSeries f).sum (qC w) := by
  have hopen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  filter_upwards [hopen.mem_nhds τ.im_pos] with w hw
  simp only [Function.comp_apply]
  rw [eichler_eq, UpperHalfPlane.ofComplex_apply_of_im_pos hw]

theorem analyticAt_eichler (τ : UpperHalfPlane) :
    AnalyticAt ℂ (ZInQ.GZHL3.eichler f ∘ UpperHalfPlane.ofComplex) τ :=
  ((analyticAt_eSum f (norm_qC_lt_one τ.im_pos)).comp (analyticAt_qC _)).congr
    (eichler_ofComplex_eventuallyEq f τ).symm

theorem analyticAt_zPar (c : ℚ) (τ : UpperHalfPlane) :
    AnalyticAt ℂ (zPar f c ∘ UpperHalfPlane.ofComplex) τ :=
  show AnalyticAt ℂ (fun w => (c : ℂ) * (ZInQ.GZHL3.eichler f ∘ UpperHalfPlane.ofComplex) w) τ from
    analyticAt_const.mul (analyticAt_eichler f τ)

theorem zPar_ofComplex (c : ℚ) (τ : UpperHalfPlane) :
    (zPar f c ∘ UpperHalfPlane.ofComplex) (τ : ℂ) = zPar f c τ := by
  simp [UpperHalfPlane.ofComplex_apply]

end Eichler

/-- **`ParamRegular`, proved.** -/
theorem paramRegular : ParamRegular := by
  intro E _ N _ f L c _
  set b : ℂ := (E⁄ℂ).b₂ / 12 with hb
  have hz := analyticAt_zPar f c
  have hval := zPar_ofComplex f c
  have ex : xPar E L f c ∘ UpperHalfPlane.ofComplex =
      (fun z => L.weierstrassP z - b) ∘ (zPar f c ∘ UpperHalfPlane.ofComplex) := rfl
  have ey : yPar E L f c ∘ UpperHalfPlane.ofComplex =
      (fun z => (L.derivWeierstrassP z - (E⁄ℂ).a₁ * (L.weierstrassP z - b) - (E⁄ℂ).a₃) / 2) ∘
        (zPar f c ∘ UpperHalfPlane.ofComplex) := rfl
  have eg : ∀ t : ℚ, gPar E L f c t ∘ UpperHalfPlane.ofComplex =
      phiT L (b + t) ∘ (zPar f c ∘ UpperHalfPlane.ofComplex) := by
    intro t; funext w; simp only [Function.comp_apply, gPar, phiT, xPar, sub_sub, hb]
  have mx : ∀ z₀, MeromorphicAt (fun z => L.weierstrassP z - b) z₀ := fun z₀ =>
    (meromorphicAt_wp L z₀).sub (MeromorphicAt.const _ _)
  have my : ∀ z₀, MeromorphicAt (fun z => (L.derivWeierstrassP z - (E⁄ℂ).a₁ *
      (L.weierstrassP z - b) - (E⁄ℂ).a₃) / 2) z₀ := fun z₀ =>
    (((meromorphicAt_dwp L z₀).sub ((MeromorphicAt.const _ _).mul (mx z₀))).sub
      (MeromorphicAt.const _ _)).div (MeromorphicAt.const _ _)
  refine ⟨fun τ => ⟨?_, ?_, fun t => ?_⟩, fun τ hτ => ⟨?_, ?_⟩, fun t τ h => ?_⟩
  · rw [ex]; exact (mx _).comp_analyticAt (hz τ)
  · rw [ey]; exact (my _).comp_analyticAt (hz τ)
  · rw [eg]; exact (meromorphicAt_phiT L _ _).comp_analyticAt (hz τ)
  · show AnalyticAt ℂ _ _
    rw [ex]
    refine AnalyticAt.comp ?_ (hz τ)
    rw [hval]
    exact (analyticAt_wp L hτ).sub analyticAt_const
  · show AnalyticAt ℂ _ _
    rw [ey]
    refine AnalyticAt.comp ?_ (hz τ)
    rw [hval]
    exact ((((analyticAt_dwp L hτ).sub (analyticAt_const.mul ((analyticAt_wp L hτ).sub
      analyticAt_const))).sub analyticAt_const).div analyticAt_const two_ne_zero)
  · show AnalyticAt ℂ _ _
    rw [eg]
    refine AnalyticAt.comp ?_ (hz τ)
    rw [hval]
    rcases h with h | h
    · exact analyticAt_phiT_of_mem L _ h
    · by_cases hm : zPar f c τ ∈ L.lattice
      · exact analyticAt_phiT_of_mem L _ hm
      · refine analyticAt_phiT_of_ne L _ hm ?_
        intro he; apply h; simp only [xPar, ← hb, he]; ring


/-! ## Power series converging on the unit disc -/

section PSeries

/-- A power series converging on the unit disc has `‖cₙ‖ rⁿ` bounded for each `r < 1`. -/
theorem pseries_bound (c : ℕ → ℂ) (hc : ∀ q : ℂ, ‖q‖ < 1 → Summable (fun n => c n * q ^ n))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) : ∃ C, ∀ n, ‖c n‖ * r ^ n ≤ C := by
  have hs := (hc (r : ℂ) (by rw [Complex.norm_real, Real.norm_of_nonneg hr0]; exact hr1))
  have ht := hs.tendsto_atTop_zero.norm
  simp only [norm_zero] at ht
  obtain ⟨C, hC⟩ := ht.bddAbove_range
  refine ⟨C, fun n => ?_⟩
  have := hC ⟨n, rfl⟩
  simpa [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr0] using this

/-- Absolute convergence of a dominated power series inside the unit disc. -/
theorem pseries_summable_norm (c d : ℕ → ℂ) (hc : ∀ q : ℂ, ‖q‖ < 1 → Summable (fun n => c n * q ^ n))
    (K : ℝ) (hK : 0 ≤ K) (k : ℕ) (hd : ∀ n, ‖d n‖ ≤ K * (n : ℝ) ^ k * ‖c n‖) {q : ℂ}
    (hq : ‖q‖ < 1) : Summable (fun n => ‖d n‖ * ‖q‖ ^ n) := by
  obtain ⟨r, hr1, hr2⟩ := exists_between hq
  have hr0 : 0 < r := lt_of_le_of_lt (norm_nonneg _) hr1
  obtain ⟨C, hC⟩ := pseries_bound c hc hr0.le hr2
  have hρ : ‖‖q‖ / r‖ < 1 := by
    rw [Real.norm_of_nonneg (div_nonneg (norm_nonneg _) hr0.le), div_lt_one hr0]; exact hr1
  have hgeo := (summable_pow_mul_geometric_of_norm_lt_one k hρ).mul_left (K * C)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hgeo
  have h1 : ‖c n‖ * ‖q‖ ^ n ≤ C * (‖q‖ / r) ^ n := by
    rw [div_pow, mul_div_assoc', le_div_iff₀ (pow_pos hr0 n)]
    calc ‖c n‖ * ‖q‖ ^ n * r ^ n = (‖c n‖ * r ^ n) * ‖q‖ ^ n := by ring
      _ ≤ C * ‖q‖ ^ n := by gcongr; exact hC n
  calc ‖d n‖ * ‖q‖ ^ n ≤ (K * (n : ℝ) ^ k * ‖c n‖) * ‖q‖ ^ n := by gcongr; exact hd n
    _ = K * (n : ℝ) ^ k * (‖c n‖ * ‖q‖ ^ n) := by ring
    _ ≤ K * (n : ℝ) ^ k * (C * (‖q‖ / r) ^ n) := by gcongr
    _ = K * C * ((n : ℝ) ^ k * (‖q‖ / r) ^ n) := by ring

/-- **Termwise differentiation** of a power series converging on the unit disc. -/
theorem hasDerivAt_pseries (c : ℕ → ℂ) (hc : ∀ q : ℂ, ‖q‖ < 1 → Summable (fun n => c n * q ^ n))
    {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (fun w => ∑' n, c n * w ^ n) (∑' n, c n * ((n : ℂ) * z ^ (n - 1))) z := by
  obtain ⟨r, hr1, hr2⟩ := exists_between hz
  have hr0 : 0 < r := lt_of_le_of_lt (norm_nonneg _) hr1
  have hrr : ‖(r : ℂ)‖ < 1 := by rw [Complex.norm_real, Real.norm_of_nonneg hr0.le]; exact hr2
  have hs := pseries_summable_norm c (fun n => (n : ℂ) * c n) hc 1 zero_le_one 1
    (fun n => by simp [norm_mul]) hrr
  have hu : Summable (fun n => ‖c n‖ * (n : ℝ) * r ^ (n - 1)) := by
    refine (hs.mul_left r⁻¹).congr fun n => ?_
    rw [Complex.norm_real, Real.norm_of_nonneg hr0.le, norm_mul, Complex.norm_natCast]
    rcases n with _ | n
    · simp
    · rw [pow_succ]; field_simp; simp
  refine hasDerivAt_tsum_of_isPreconnected (g := fun n w => c n * w ^ n)
    (g' := fun n w => c n * ((n : ℂ) * w ^ (n - 1))) hu Metric.isOpen_ball
    (convex_ball (0 : ℂ) r).isPreconnected (fun n y _ => (hasDerivAt_pow n y).const_mul (c n))
    (fun n y hy => ?_) (Metric.mem_ball_self hr0) (hc 0 (by simp)) (by simpa using hr1)
  rw [Metric.mem_ball, dist_zero_right] at hy
  rw [norm_mul, norm_mul, Complex.norm_natCast, norm_pow, ← mul_assoc]
  gcongr

end PSeries

/-! ## The derivative of the Eichler integral -/

section EichlerDeriv

variable {N : ℕ} [NeZero N] (f : Newform N 2)

theorem eCoeff_summable (q : ℂ) (hq : ‖q‖ < 1) : Summable (fun n => eCoeff f n * q ^ n) := by
  have hs := (eSeries f).hasSum (eSeries_mem_ball f hq)
  simp only [eSeries, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] at hs
  exact hs.summable

theorem eSum_eq_tsum (q : ℂ) : (eSeries f).sum q = ∑' n, eCoeff f n * q ^ n := by
  rw [eSeries, ← FormalMultilinearSeries.ofScalarsSum, FormalMultilinearSeries.ofScalarsSum_eq_tsum]
  simp

theorem hasDerivAt_qC (w : ℂ) : HasDerivAt qC (2 * Real.pi * Complex.I * qC w) w := by
  unfold qC
  have := ((hasDerivAt_id w).const_mul (2 * Real.pi * Complex.I)).cexp
  simpa [mul_comm] using this

theorem hasDerivAt_eichler (τ : UpperHalfPlane) :
    HasDerivAt (ZInQ.GZHL3.eichler f ∘ UpperHalfPlane.ofComplex)
      (2 * Real.pi * Complex.I * f.toCuspForm τ) τ := by
  have hq := norm_qC_lt_one τ.im_pos
  have h1 := (hasDerivAt_pseries (eCoeff f) (eCoeff_summable f) hq).comp (τ : ℂ) (hasDerivAt_qC τ)
  have hev : (ZInQ.GZHL3.eichler f ∘ UpperHalfPlane.ofComplex) =ᶠ[nhds (τ : ℂ)]
      ((fun w => ∑' n, eCoeff f n * w ^ n) ∘ qC) := by
    filter_upwards [eichler_ofComplex_eventuallyEq f τ] with w hw
    rw [hw, Function.comp_apply, eSum_eq_tsum]
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  convert h1 using 1
  have key : ∀ n : ℕ, eCoeff f n * ((n : ℂ) * qC τ ^ (n - 1)) * (2 * Real.pi * Complex.I * qC τ) =
      2 * Real.pi * Complex.I * (ZInQ.GZDecomp.coeff f n * qC τ ^ n) := by
    intro n
    rcases n with _ | n
    · simp [eCoeff, coeff_zero_newform]
    · simp only [eCoeff, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel]
      have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      rw [pow_succ]
      field_simp
  show _ = (∑' n, eCoeff f n * ((n : ℂ) * qC τ ^ (n - 1))) * (2 * Real.pi * Complex.I * qC τ)
  rw [← tsum_mul_right, funext key, tsum_mul_left, (hasSum_newform f τ).tsum_eq]

theorem mdiff_eichler : MDiff (ZInQ.GZHL3.eichler f) := fun τ =>
  UpperHalfPlane.mdifferentiableAt_iff.2 (hasDerivAt_eichler f τ).differentiableAt

theorem D_eichler : Derivative.normalizedDerivOfComplex (ZInQ.GZHL3.eichler f) = ⇑f.toCuspForm := by
  funext τ
  rw [Derivative.normalizedDerivOfComplex, (hasDerivAt_eichler f τ).deriv]
  field_simp

end EichlerDeriv

end ZInQ.GZHeegner
