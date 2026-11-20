import ZInQKernel.Contrib.OneProof.RC.X0Model.Section
import ZInQKernel.Contrib.OneProof.RC.X0Model2.LaurentConvergence

/-! The analytic continuation on the rational model has the specified Laurent
coefficients at the cusp (tex 2837–2838 and 2915–2919, provenance (c)). -/

noncomputable section

open AlgebraicGeometry CategoryTheory Filter ModularCurve ShimuraPointDict
open scoped Topology

namespace ZInQ.Manuscript.RC.X0Model2

private abbrev cuspQ (τ : UpperHalfPlane) : ℂ :=
  Function.Periodic.qParam 1 (τ : ℂ)

private theorem cuspQ_zpow (z : ℂ) (n : ℤ) :
    Function.Periodic.qParam 1 z ^ n =
      Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * z) := by
  rw [Function.Periodic.qParam, Complex.ofReal_one, div_one, ← Complex.exp_int_mul]
  congr 1
  ring

private theorem cuspQ_tendsto :
    Tendsto cuspQ UpperHalfPlane.atImInfty (𝓝[≠] (0 : ℂ)) :=
  (Function.Periodic.qParam_tendsto one_pos).comp UpperHalfPlane.tendsto_coe_atImInfty

private theorem germ_inverse {z : ℂ} (u : X0Model.MeromorphicGerm z)
    (f : ℂ → ℂ) (he : (f : PuncturedGerm z) = X0Model.meromorphicIncl z u)
    (hu : u ≠ 0) :
    ((f⁻¹ : ℂ → ℂ) : PuncturedGerm z) = X0Model.meromorphicIncl z u⁻¹ := by
  obtain ⟨g, hg, hgm⟩ := u.property
  have hfg : f =ᶠ[𝓝[≠] z] g := Germ.coe_eq.mp (he.trans hg.symm)
  have hne : ∀ᶠ w in 𝓝[≠] z, f w ≠ 0 := by
    have h := hgm.eventually_eq_zero_or_eventually_ne_zero.resolve_left fun hz =>
      hu (Subtype.ext (hg.symm.trans (Germ.coe_eq.mpr hz)))
    filter_upwards [hfg, h] with w hw hw' using hw ▸ hw'
  have hm : (f : PuncturedGerm z) * ((f⁻¹ : ℂ → ℂ) : PuncturedGerm z) = 1 :=
    Germ.coe_eq.mpr (hne.mono fun _ h => mul_inv_cancel₀ h)
  calc
    _ = (X0Model.meromorphicIncl z u⁻¹ * (f : PuncturedGerm z)) *
        ((f⁻¹ : ℂ → ℂ) : PuncturedGerm z) := by
      rw [he, ← map_mul, inv_mul_cancel₀ hu, map_one, one_mul]
    _ = _ := by rw [mul_assoc, hm, mul_one]

private abbrev cuspEmbedding (N : ℕ) [NeZero N] : modularFunctionField N →+* LaurentSeries ℂ :=
  (coeffEmb ℂ).comp (modularFunctionField N).subtype

private abbrev cuspSum (A : LaurentSeries ℂ) (τ : UpperHalfPlane) (t : ℂ) : Prop :=
  HasSum (fun n : ℤ => A.coeff n * cuspQ τ ^ n) t

private theorem cuspSum_exp (N : ℕ) [NeZero N] (a : modularFunctionField N)
    (τ : UpperHalfPlane) (t : ℂ) :
    cuspSum (cuspEmbedding N a) τ t ↔
      HasSum (fun n : ℤ => ((a : LaurentSeries ℚ).coeff n : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (τ : ℂ))) t := by
  have hrat : algebraMap ℚ ℂ = Rat.castHom ℂ := Subsingleton.elim _ _
  change HasSum (fun n : ℤ => (coeffEmb ℂ (a : LaurentSeries ℚ)).coeff n * cuspQ τ ^ n) t ↔ _
  simp only [coeffEmb_coeff, hrat, cuspQ, cuspQ_zpow]
  rfl

private theorem cuspSum_ratCast (c : ℚ) (τ : UpperHalfPlane) :
    cuspSum (c : LaurentSeries ℂ) τ (c : ℂ) := by
  have h : (c : LaurentSeries ℂ) = HahnSeries.single 0 (c : ℂ) := by
    rw [← HahnSeries.C_apply, map_ratCast]
  simp only [cuspSum, h]
  simpa only [HahnSeries.coeff_single_same, zpow_zero, mul_one] using
    (hasSum_single (f := fun n : ℤ => (HahnSeries.single 0 (c : ℂ)).coeff n * cuspQ τ ^ n)
      0 (fun n hn => by rw [HahnSeries.coeff_single_of_ne hn, zero_mul]))

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 80000 in
private theorem exists_cuspRepresentative (N : ℕ) [NeZero N] (a : modularFunctionField N) :
    ∃ f : ℂ → ℂ,
      (∀ τ : UpperHalfPlane, (f : PuncturedGerm (τ : ℂ)) =
        X0Model.meromorphicIncl (τ : ℂ) (X0Model.fieldGerm N τ a)) ∧
      ∀ᶠ (τ : UpperHalfPlane) in UpperHalfPlane.atImInfty, AnalyticAt ℂ f (τ : ℂ) ∧
        cuspSum (cuspEmbedding N a) τ (f τ) := by
  let R (a : modularFunctionField N) : Prop :=
    ∃ f : ℂ → ℂ,
      (∀ τ : UpperHalfPlane, (f : PuncturedGerm (τ : ℂ)) =
        X0Model.meromorphicIncl (τ : ℂ) (X0Model.fieldGerm N τ a)) ∧
      ∀ᶠ (τ : UpperHalfPlane) in UpperHalfPlane.atImInfty, AnalyticAt ℂ f (τ : ℂ) ∧
        cuspSum (cuspEmbedding N a) τ (f τ)
  exact IntermediateField.adjoin_induction ℚ (s := {jq, jqN N})
    (motive := fun x hx => R ⟨x, hx⟩)
    (fun x hx => by
      rcases Set.mem_insert_iff.mp hx with rfl | h
      · refine ⟨X0Model.analyticJ ∘ UpperHalfPlane.ofComplex, fun τ => ?_,
          Eventually.of_forall fun τ => ⟨X0Model.analyticOn_j τ τ.im_pos, ?_⟩⟩
        · rw [X0Model.fieldGerm_j]
          exact Germ.coe_eq.mpr (Eventually.of_forall fun _ => by simp)
        · apply (cuspSum_exp N _ τ _).mpr
          simpa only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using X0Model.hasSum_j τ
      · obtain rfl := Set.mem_singleton_iff.mp h
        refine ⟨X0Model.analyticJN N ∘ UpperHalfPlane.ofComplex,
          fun τ => (X0Model.fieldGerm_jN N τ).symm, Eventually.of_forall fun τ =>
            ⟨X0Model.analyticOn_jN N τ τ.im_pos, ?_⟩⟩
        apply (cuspSum_exp N _ τ _).mpr
        simpa only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using X0Model.hasSum_jN N τ)
    (fun c => by
      have hc : (⟨algebraMap ℚ (LaurentSeries ℚ) c, (modularFunctionField N).algebraMap_mem c⟩ :
          modularFunctionField N) = (c : modularFunctionField N) := by
        apply Subtype.ext
        exact DFunLike.congr_fun (Subsingleton.elim (algebraMap ℚ (LaurentSeries ℚ))
          ((modularFunctionField N).subtype.comp (Rat.castHom (modularFunctionField N)))) c
      change R _
      rw [hc]
      refine ⟨fun _ => (c : ℂ), fun τ => ?_, Eventually.of_forall fun τ => ⟨analyticAt_const, ?_⟩⟩
      · change (X0Model.meromorphicIncl (τ : ℂ)).comp (X0Model.constantGerm (τ : ℂ)) (c : ℂ) = _
        simp only [RingHom.comp_apply, map_ratCast]
      · simpa only [map_ratCast] using cuspSum_ratCast c τ)
    (fun x y hx hy hf hg => by
      let b : modularFunctionField N := ⟨x, hx⟩
      let c : modularFunctionField N := ⟨y, hy⟩
      change R (b + c)
      obtain ⟨f, hfe, hf⟩ := hf
      obtain ⟨g, hge, hg⟩ := hg
      refine ⟨f + g, fun τ => ?_, ?_⟩
      · rw [Germ.coe_add, hfe, hge]
        exact (((X0Model.meromorphicIncl (τ : ℂ)).comp (X0Model.fieldGerm N τ)).map_add b c).symm
      · filter_upwards [hf, hg] with τ hf hg
        refine ⟨hf.1.add hg.1, ?_⟩
        simpa only [b, c, cuspSum, map_add, HahnSeries.coeff_add, add_mul, Pi.add_apply] using hf.2.add hg.2)
    (fun x hx hb => by
      let b : modularFunctionField N := ⟨x, hx⟩
      change R b⁻¹
      by_cases hb0 : b = 0
      · rw [hb0, inv_zero]
        exact hb0 ▸ hb
      obtain ⟨f, hfe, hf⟩ := hb
      obtain ⟨τ, hτ⟩ := hf.exists
      have hn : cuspEmbedding N b ≠ 0 := by
        intro h
        apply hb0
        apply Subtype.ext
        change (b : LaurentSeries ℚ) = 0
        exact (map_eq_zero_iff (coeffEmb ℂ) (coeffEmb_injective ℂ)).mp h
      have hi := eventually_hasSum_laurent_inv hn (Function.Periodic.qParam_ne_zero _) hτ.2
      refine ⟨f⁻¹, fun w => ?_, ?_⟩
      · rw [map_inv₀ (X0Model.fieldGerm N w)]
        exact germ_inverse _ f (hfe w) ((map_ne_zero_iff _ (X0Model.fieldGerm N w).injective).mpr hb0)
      · filter_upwards [hf, cuspQ_tendsto.eventually hi] with w hw hi
        obtain ⟨hne, hs⟩ := hi (f w) hw.2
        refine ⟨hw.1.inv hne, ?_⟩
        simpa only [cuspSum, map_inv₀, Pi.inv_apply] using hs)
    (fun x y hx hy hf hg => by
      let b : modularFunctionField N := ⟨x, hx⟩
      let c : modularFunctionField N := ⟨y, hy⟩
      change R (b * c)
      obtain ⟨f, hfe, hf⟩ := hf
      obtain ⟨g, hge, hg⟩ := hg
      obtain ⟨τ, hτ⟩ := hf.exists
      obtain ⟨σ, hσ⟩ := hg.exists
      have hm := eventually_hasSum_laurent_mul (Function.Periodic.qParam_ne_zero _)
        (Function.Periodic.qParam_ne_zero _) hτ.2 hσ.2
      refine ⟨f * g, fun w => ?_, ?_⟩
      · rw [Germ.coe_mul, hfe, hge]
        exact (((X0Model.meromorphicIncl (w : ℂ)).comp (X0Model.fieldGerm N w)).map_mul b c).symm
      · filter_upwards [hf, hg, cuspQ_tendsto.eventually hm] with w hw hw' hm
        refine ⟨hw.1.mul hw'.1, ?_⟩
        simpa only [b, c, cuspSum, map_mul, Pi.mul_apply] using hm (f w) (g w) hw.2 hw'.2)
    a.property

/-- The prescribed bilateral Laurent series sums to the meromorphic continuation
of any element of the modular function field sufficiently high in the upper half-plane. -/
theorem hasSum_meromorphicContinuation (N : ℕ) [NeZero N] (a : modularFunctionField N)
    (g : ℂ → ℂ) (hg : MeromorphicNFOn g {z : ℂ | 0 < z.im})
    (he : ∀ τ : UpperHalfPlane, (g : PuncturedGerm (τ : ℂ)) =
      X0Model.meromorphicIncl (τ : ℂ) (X0Model.fieldGerm N τ a)) :
    ∃ T : ℝ, ∀ τ : UpperHalfPlane, T < τ.im →
      HasSum (fun n : ℤ => ((a : LaurentSeries ℚ).coeff n : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (τ : ℂ))) (g τ) := by
  obtain ⟨f, hf, h⟩ := exists_cuspRepresentative N a
  obtain ⟨T, hT⟩ := (UpperHalfPlane.atImInfty_mem _).mp h
  refine ⟨T, fun τ ht => ?_⟩
  obtain ⟨ha, hs⟩ := hT τ ht.le
  have hfg := ((hg τ.im_pos).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    ha.meromorphicNFAt).mp (Germ.coe_eq.mp ((he τ).trans (hf τ).symm))
  rw [hfg.eq_of_nhds]
  exact (cuspSum_exp N a τ (f τ)).mp hs

/-- Every modular function admits a meromorphic continuation with its
prescribed Laurent sum high in the upper half-plane. -/
theorem exists_hasSum_meromorphicContinuation (N : ℕ) [NeZero N]
    (a : modularFunctionField N) :
    ∃ (g : ℂ → ℂ) (T : ℝ), MeromorphicNFOn g {z : ℂ | 0 < z.im} ∧
      (∀ τ : UpperHalfPlane, (g : PuncturedGerm (τ : ℂ)) =
        X0Model.meromorphicIncl (τ : ℂ) (X0Model.fieldGerm N τ a)) ∧
      ∀ τ : UpperHalfPlane, T < τ.im →
        HasSum (fun n : ℤ => ((a : LaurentSeries ℚ).coeff n : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (τ : ℂ))) (g τ) := by
  obtain ⟨g, hg, he⟩ := X0Model.exists_meromorphicContinuation N a
  obtain ⟨T, hT⟩ := hasSum_meromorphicContinuation N a g hg he
  exact ⟨g, T, hg, he, hT⟩

/-- The section expansion required by the rational model, including its value
at every upper half-plane parameter where the section is regular. -/
theorem sectionExpansion (N : ℕ) [NeZero N] (U : (X0Model.curve N).Opens) [Nonempty U]
    (r : Γ(X0Model.curve N, U)) :
    ∃ (g : ℂ → ℂ) (T : ℝ), MeromorphicOn g {z : ℂ | 0 < z.im} ∧
      (∀ τ : UpperHalfPlane, T < τ.im →
        HasSum (fun n : ℤ =>
          ((X0Model.functionField N ((X0Model.curve N).germToFunctionField U r) :
            LaurentSeries ℚ).coeff n : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (τ : ℂ))) (g τ)) ∧
      ∀ (τ : UpperHalfPlane) (h : X0Model.complexPoint N τ default ∈ U),
        AnalyticAt ℂ g (τ : ℂ) ∧
          X0Model.sectionMap (X0Model.complexPoint N τ) U (by
            intro x _
            rwa [Subsingleton.elim x (default : Spec (.of ℂ))]) r = g τ := by
  obtain ⟨g, hg, he, hreg⟩ := X0Model.sectionMeromorphicContinuation N U r
  obtain ⟨T, hT⟩ := hasSum_meromorphicContinuation N _ g hg he
  exact ⟨g, T, hg.meromorphicOn, hT, hreg⟩


end ZInQ.Manuscript.RC.X0Model2
