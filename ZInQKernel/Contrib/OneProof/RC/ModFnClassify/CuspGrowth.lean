import ZInQKernel.Contrib.OneProof.RC.ModFnClassify.LevelOne

/-! Growth and removable singularities in a cusp parameter. Provenance (c). -/

noncomputable section

open Filter Topology Function UpperHalfPlane Complex

namespace ZInQ.Manuscript.RC.ModFnClassify

/-- At most exponential growth, measured in a specified positive-width
cusp parameter. The growth condition itself imposes no invariance. -/
abbrev CuspGrowth (h : ℝ) (f : ℍ → ℂ) : Prop :=
  ∃ d : ℕ, IsBoundedAtImInfty (fun τ => Periodic.qParam h τ ^ d * f τ)

theorem cuspGerm_growth {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ}
    (hf : CuspGerm h f) : CuspGrowth h f := by
  obtain ⟨G, T, hG, hval⟩ := hf
  obtain ⟨d, ha⟩ := hG
  refine ⟨d, ?_⟩
  have ht := ha.continuousAt.tendsto.comp (qParam_tendsto_atImInfty hh)
  apply (ht.isBigO_one ℝ).congr'
  · exact ((eventually_gt_atTop T).comap UpperHalfPlane.im).mono fun τ hτ => by
      simp only [Function.comp_apply, sub_zero, smul_eq_mul, hval τ hτ]
  · rfl

/-- The choice of positive width in an exponential bound is immaterial. -/
theorem cuspGrowth_changeWidth {h k : ℝ} (hh : 0 < h) (hk : 0 < k)
    {f : ℍ → ℂ} (hf : CuspGrowth h f) : CuspGrowth k f := by
  obtain ⟨d, hd⟩ := hf
  obtain ⟨e, he⟩ := exists_nat_gt ((d : ℝ) * k / h)
  have hde : (d : ℝ) / h ≤ (e : ℝ) / k := by
    apply (div_le_div_iff₀ hh hk).mpr
    have h' := (div_lt_iff₀ hh).mp he
    exact h'.le
  obtain ⟨M, T, hT⟩ := isBoundedAtImInfty_iff.mp hd
  refine ⟨e, isBoundedAtImInfty_iff.mpr ⟨M, T, fun τ hτ => ?_⟩⟩
  refine le_trans ?_ (hT τ hτ)
  simp only [norm_mul, norm_pow, Periodic.norm_qParam, ← Real.exp_nat_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rw [Real.exp_le_exp]
  have hm : 0 ≤ 2 * Real.pi * τ.im := by positivity
  calc
    (e : ℝ) * (-2 * Real.pi * τ.im / k) =
        -(2 * Real.pi * τ.im) * ((e : ℝ) / k) := by ring
    _ ≤ -(2 * Real.pi * τ.im) * ((d : ℝ) / h) :=
      mul_le_mul_of_nonpos_left hde (by linarith)
    _ = (d : ℝ) * (-2 * Real.pi * τ.im / h) := by ring

theorem cuspGrowth_const {h : ℝ} (c : ℂ) :
    CuspGrowth h (fun _ => c) :=
  ⟨0, isBoundedAtImInfty_iff.mpr ⟨‖c‖, 0, fun _ _ => by simp⟩⟩

theorem cuspGrowth_mul {h : ℝ} {f g : ℍ → ℂ}
    (hf : CuspGrowth h f) (hg : CuspGrowth h g) :
    CuspGrowth h (fun τ => f τ * g τ) := by
  obtain ⟨d, hd⟩ := hf
  obtain ⟨e, he⟩ := hg
  refine ⟨d + e, (hd.mul he).congr' (Eventually.of_forall ?_) (by rfl)⟩
  intro τ
  simp only [Pi.mul_apply, pow_add]
  ring

theorem cuspGrowth_sub {h : ℝ} (hh : 0 < h) {f g : ℍ → ℂ}
    (hf : CuspGrowth h f) (hg : CuspGrowth h g) :
    CuspGrowth h (fun τ => f τ - g τ) := by
  obtain ⟨d, hd⟩ := hf
  obtain ⟨e, he⟩ := hg
  have hb (n : ℕ) :
      IsBoundedAtImInfty (fun τ => Periodic.qParam h τ ^ n) :=
    isBoundedAtImInfty_iff.mpr ⟨1, 0, fun τ _ => by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (Periodic.norm_qParam_lt_one hh τ.im_pos).le⟩
  have h₁ : IsBoundedAtImInfty (fun τ => Periodic.qParam h τ ^ (d + e) * f τ) :=
    (hd.mul (hb e)).congr' (Eventually.of_forall fun τ => by simp [pow_add]; ring) (by rfl)
  have h₂ : IsBoundedAtImInfty (fun τ => Periodic.qParam h τ ^ (d + e) * g τ) :=
    ((hb d).mul he).congr' (Eventually.of_forall fun τ => by simp [pow_add]; ring) (by rfl)
  refine ⟨d + e, (h₁.sub h₂).congr' (Eventually.of_forall ?_) (by rfl)⟩
  intro τ
  simp only [mul_sub]

private theorem qParam_add_period {h : ℝ} (hh : h ≠ 0) (z : ℂ) :
    Periodic.qParam h (z + (h : ℂ)) = Periodic.qParam h z := by
  have hhc : (h : ℂ) ≠ 0 := ofReal_ne_zero.mpr hh
  unfold Periodic.qParam
  rw [show 2 * Real.pi * Complex.I * (z + (h : ℂ)) / h =
      2 * Real.pi * Complex.I * z / h + 2 * Real.pi * Complex.I by
        field_simp]
  rw [exp_add, exp_two_pi_mul_I, mul_one]

/-- Periodicity and exponential growth imply meromorphy in the periodic
parameter, provided the function is holomorphic on a tail. This descends a
period-one orbit coefficient without a separate fractional-power calculation. -/
theorem cuspGerm_of_periodic_growth {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ}
    (hp : Periodic (f ∘ ofComplex) h)
    (ha : ∀ᶠ z : ℂ in comap Complex.im atTop, DifferentiableAt ℂ (f ∘ ofComplex) z)
    (hg : CuspGrowth h f) : CuspGerm h f := by
  obtain ⟨d, hd⟩ := hg
  let F : ℂ → ℂ := fun z => Periodic.qParam h z ^ d * f (ofComplex z)
  have hFp : Periodic F h := fun z => by
    simp only [F, qParam_add_period hh.ne', show f (ofComplex (z + (h : ℂ))) =
      f (ofComplex z) from hp z]
  have hFa : ∀ᶠ z in comap Complex.im atTop, DifferentiableAt ℂ F z :=
    ha.mono fun z hz => (Periodic.differentiable_qParam.differentiableAt.pow d).mul hz
  have he : (fun τ : ℍ => Periodic.qParam h τ ^ d * f τ) ∘ ofComplex
      =ᶠ[comap Complex.im atTop] F := by
    filter_upwards [(eventually_gt_atTop (0 : ℝ)).comap Complex.im] with z hz
    simp [F, ofComplex_apply_of_im_pos hz]
  have hFb : BoundedAtFilter (comap Complex.im atTop) F :=
    (hd.comp_tendsto tendsto_comap_im_ofComplex).congr' he (by rfl)
  let G := Periodic.cuspFunction h F
  have hGa : AnalyticAt ℂ G 0 := by
    have h0 := Periodic.differentiableAt_cuspFunction_zero hh hFp hFa hFb
    have he := Periodic.eventually_differentiableAt_cuspFunction_nhds_ne_zero hh hFp hFa
    have hnh : ∀ᶠ q in 𝓝 (0 : ℂ), DifferentiableAt ℂ G q := by
      rw [← nhdsNE_sup_pure]
      simpa [eventually_sup, G] using And.intro he h0
    obtain ⟨s, hs, hso, hmem⟩ := eventually_nhds_iff.mp hnh
    have hdG : DifferentiableOn ℂ G s :=
      fun z hz => (hs z hz).differentiableWithinAt
    exact hdG.analyticAt (hso.mem_nhds hmem)
  refine ⟨fun q => G q / q ^ d, 0, hGa.meromorphicAt.div ((MeromorphicAt.id 0).pow d),
    fun τ _ => ?_⟩
  simp only [G, Periodic.eq_cuspFunction hh.ne' hFp, F, ofComplex_apply]
  exact mul_div_cancel_left₀ _ (pow_ne_zero d (Periodic.qParam_ne_zero (τ : ℂ)))


end ZInQ.Manuscript.RC.ModFnClassify
