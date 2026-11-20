import ZInQKernel.Contrib.OneProof.RC.ModFnClassify.Interior
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-! Level-one classification with complex coefficients and interior poles.
On-the-spot (c) for tex 1785–1787 and 2836–2838. -/

noncomputable section

open Filter Topology UpperHalfPlane Polynomial Matrix Complex
open scoped MatrixGroups ModularForm

namespace ZInQ.Manuscript.RC.ModFnClassify

/-- A function has a meromorphic representative on a tail in the given
cusp parameter. -/
abbrev CuspGerm (h : ℝ) (f : ℍ → ℂ) : Prop :=
  ∃ (G : ℂ → ℂ) (T : ℝ), MeromorphicAt G 0 ∧
    ∀ τ : ℍ, T < τ.im → G (Function.Periodic.qParam h τ) = f τ

/-- A meromorphic cusp representative is analytic at all points of a
sufficiently high tail. -/
theorem cuspGerm_analytic_tail {h : ℝ} (hh : 0 < h) {g : ℂ → ℂ}
    (hg : CuspGerm h (fun τ => g τ)) :
    ∃ T : ℝ, ∀ z ∈ upperDomain, T < z.im → AnalyticAt ℂ g z := by
  obtain ⟨G, T, hm, he⟩ := hg
  have ht : Tendsto (fun τ : ℍ => Function.Periodic.qParam h τ)
      atImInfty (𝓝[≠] (0 : ℂ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨qParam_tendsto_atImInfty hh,
      Eventually.of_forall fun τ => Function.Periodic.qParam_ne_zero τ⟩
  obtain ⟨S, hS⟩ := (atImInfty_mem _).mp (ht.eventually hm.eventually_analyticAt)
  refine ⟨max T S, fun z hz hZ => ?_⟩
  let τ : ℍ := ⟨z, hz⟩
  have ha : AnalyticAt ℂ (fun w => G (Function.Periodic.qParam h w)) z :=
    (hS τ ((le_max_right _ _).trans hZ.le)).comp (by unfold Function.Periodic.qParam; fun_prop)
  apply ha.congr
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hz,
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds
      ((le_max_left _ _).trans_lt hZ)] with w hw ht
  exact he ⟨w, hw⟩ ht

private theorem levelOne_const {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g upperDomain)
    (hi : LevelOneInvariant g) (hb : IsBoundedAtImInfty (fun τ : ℍ => g τ)) :
    ∃ c : ℂ, ∀ τ : ℍ, g τ = c := by
  let f : ℍ → ℂ := fun τ => g τ
  have hs (γ : SL(2, ℤ)) : f ∣[(0 : ℤ)] γ = f := by
    funext τ
    simpa [ModularForm.SL_slash_apply, f] using hi γ τ
  let F : ModularForm 𝒮ℒ 0 :=
    { toFun := f
      slash_action_eq' := by
        intro γ hγ
        obtain ⟨δ, rfl⟩ := hγ
        exact hs δ
      holo' := UpperHalfPlane.mdifferentiable_iff.mpr <| by
        apply (hg.differentiableOn).congr
        intro z hz
        simp [f, ofComplex_apply_of_im_pos hz]
      bdd_at_cusps' := by
        intro c hc
        apply (OnePoint.isBoundedAt_iff_forall_SL2Z hc).mpr
        intro γ _
        rw [hs γ]
        exact hb }
  obtain ⟨c, hc⟩ := ModularFormClass.levelOne_weight_zero_const F
  exact ⟨c, fun τ => congrFun hc τ⟩

/-- The analytic function (qj) has a holomorphic cusp representative with
value one at zero, i.e. (j) has a simple pole there. -/
theorem j_cusp_unit :
    ∃ U : ℂ → ℂ, AnalyticAt ℂ U 0 ∧ U 0 = 1 ∧ ∀ τ : ℍ,
      U (Function.Periodic.qParam 1 τ) = Function.Periodic.qParam 1 τ * jFunction τ := by
  let D (q : ℂ) := ∏' n : ℕ, (1 - q ^ (n + 1)) ^ 24
  have hD : AnalyticAt ℂ D 0 :=
    (ModularForm.differentiableOn_tprod_one_sub_pow_pow 24).analyticAt
      (Metric.ball_mem_nhds 0 one_pos)
  have hD0 : D 0 = 1 := by simp [D, zero_pow (Nat.succ_ne_zero _)]
  let A := cuspFunction 1 ModularForm.E₄
  have hA : AnalyticAt ℂ A 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero ModularForm.E₄ one_pos one_mem_strictPeriods_SL
  have hA0 : A 0 = 1 := by
    rw [show A 0 = (qExpansion 1 ModularForm.E₄).coeff 0 from by simp [A, qExpansion_coeff]]
    exact EisensteinSeries.E_qExpansion_coeff_zero (by norm_num) (by norm_num : Even 4)
  refine ⟨fun q => A q ^ 3 / D q, (hA.pow 3).div hD (by simp [hD0]),
    by simp [hA0, hD0], fun τ => ?_⟩
  have hq := Function.Periodic.qParam_ne_zero (h := 1) (τ : ℂ)
  have hΔ : ModularForm.discriminant τ = Function.Periodic.qParam 1 τ *
      D (Function.Periodic.qParam 1 τ) := ModularForm.discriminant_eq_q_prod τ
  have hδ : D (Function.Periodic.qParam 1 τ) ≠ 0 := by
    intro hd
    exact ModularForm.discriminant_ne_zero τ (by rw [hΔ, hd, mul_zero])
  dsimp only
  rw [show A (Function.Periodic.qParam 1 τ) = ModularForm.E₄ τ from
    SlashInvariantFormClass.eq_cuspFunction _ τ one_mem_strictPeriods_SL one_ne_zero]
  simp only [jFunction, ofComplex_apply, X0Model.analyticJ, hΔ]
  field_simp

/-- Given an analytic representative of (q^d H), cancel its polar
part using powers of (j), and apply weight-zero constancy. -/
theorem levelOne_polynomial_of_cleared_cusp {H A U : ℂ → ℂ}
    (hH : AnalyticOnNhd ℂ H upperDomain) (hi : LevelOneInvariant H)
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 1)
    (hj : ∀ τ : ℍ, U (Function.Periodic.qParam 1 τ) =
      Function.Periodic.qParam 1 τ * jFunction τ)
    (d : ℕ) (hA : AnalyticAt ℂ A 0)
    (hval : ∃ T : ℝ, ∀ τ : ℍ, T < τ.im →
      A (Function.Periodic.qParam 1 τ) = Function.Periodic.qParam 1 τ ^ d * H τ) :
    ∃ P : ℂ[X], ∀ τ : ℍ, H τ = P.eval (jFunction τ) := by
  induction d generalizing H A with
  | zero =>
    obtain ⟨T, hT⟩ := hval
    have hc : Tendsto (fun τ : ℍ => H τ) atImInfty (𝓝 (A 0)) := by
      refine (hA.continuousAt.tendsto.comp (qParam_tendsto_atImInfty one_pos)).congr' ?_
      exact (eventually_gt_atTop T).comap UpperHalfPlane.im |>.mono (fun τ hτ => by
        simpa using hT τ hτ)
    obtain ⟨c, hc⟩ := levelOne_const hH hi (hc.isBigO_one ℝ)
    exact ⟨C c, fun τ => by simpa using hc τ⟩
  | succ d ih =>
    let G : ℂ → ℂ := fun z => H z - A 0 * jFunction z ^ (d + 1)
    let B : ℂ → ℂ := fun q => A q - A 0 * U q ^ (d + 1)
    have hG : AnalyticOnNhd ℂ G upperDomain := fun z hz =>
      (hH z hz).sub (analyticAt_const.mul ((X0Model.analyticOn_j z hz).pow _))
    have hGi : LevelOneInvariant G := by
      intro γ τ
      simp only [G, hi γ τ, jFunction_invariant γ τ]
    have hB : AnalyticAt ℂ B 0 := hA.sub (analyticAt_const.mul (hU.pow _))
    have hB0 : B 0 = 0 := by simp [B, hU0]
    obtain ⟨K, hK, hBK⟩ := hB.exists_eventuallyEq_sum_add_pow_mul 1
    have hBK' : ∀ᶠ q in 𝓝 (0 : ℂ), B q = q * K q := by
      simpa [hB0] using hBK
    obtain ⟨S, hS⟩ := (atImInfty_mem _).mp
      ((qParam_tendsto_atImInfty one_pos).eventually hBK')
    obtain ⟨T, hT⟩ := hval
    have hval' : ∃ R : ℝ, ∀ τ : ℍ, R < τ.im →
        K (Function.Periodic.qParam 1 τ) = Function.Periodic.qParam 1 τ ^ d * G τ := by
      refine ⟨max S T, fun τ hτ => ?_⟩
      have hb := hS τ ((le_max_left _ _).trans hτ.le)
      have ha := hT τ ((le_max_right _ _).trans_lt hτ)
      let q := Function.Periodic.qParam 1 (τ : ℂ)
      apply mul_left_cancel₀ (Function.Periodic.qParam_ne_zero (h := 1) (τ : ℂ))
      change q * K q = q * (q ^ d * G τ)
      calc
        _ = B q := hb.symm
        _ = _ := by dsimp [B, G, q] at *; rw [ha, hj, mul_pow, pow_succ]; ring
    obtain ⟨P, hP⟩ := ih hG hGi hK hval'
    refine ⟨P + C (A 0) * X ^ (d + 1), fun τ => ?_⟩
    simpa [G, eval_add, eval_mul, eval_pow] using (sub_eq_iff_eq_add.mp (hP τ))

/-- An invariant meromorphic level-one function, meromorphic at the cusp,
is a quotient of complex polynomials in `j` as a meromorphic function.
The denominator is monic and the equality holds on every punctured germ. -/
theorem levelOne_rational_in_j {g : ℂ → ℂ} (hg : MeromorphicOn g upperDomain)
    (hi : LevelOneInvariant g) (hc : CuspGerm 1 (fun τ => g τ)) :
    ∃ P D : ℂ[X], D.Monic ∧ ∀ z ∈ upperDomain,
      (fun w => g w * D.eval (jFunction w)) =ᶠ[𝓝[≠] z] (fun w => P.eval (jFunction w)) := by
  obtain ⟨S, hS⟩ := cuspGerm_analytic_tail one_pos hc
  obtain ⟨D, H, hD, hH, hHi, he⟩ := clear_interior_poles hg hi S hS
  obtain ⟨U, hU, hU0, hUval⟩ := j_cusp_unit
  let J : ℂ → ℂ := fun q => U q / q
  have hJ : MeromorphicAt J 0 := hU.meromorphicAt.div (MeromorphicAt.id 0)
  have hJval (τ : ℍ) : J (Function.Periodic.qParam 1 τ) = jFunction τ := by
    dsimp [J]
    rw [hUval, mul_comm, mul_div_cancel_right₀ _ (Function.Periodic.qParam_ne_zero (τ : ℂ))]
  obtain ⟨G, T, hG, hGval⟩ := hc
  have hDJ : MeromorphicAt (fun q => D.eval (J q)) 0 := by
    clear hD he
    induction D using Polynomial.induction_on with
    | C c => simpa only [eval_C] using (MeromorphicAt.const c (0 : ℂ))
    | add P Q hP hQ =>
      exact (hP.add hQ).congr (Eventually.of_forall fun q => by
        change P.eval (J q) + Q.eval (J q) = (P + Q).eval (J q)
        rw [eval_add])
    | monomial n c h =>
      exact (MeromorphicAt.const c (0 : ℂ)).mul (hJ.pow (n + 1)) |>.congr
        (Eventually.of_forall fun q => by simp)
  obtain ⟨d, ha⟩ := hG.mul hDJ
  let A : ℂ → ℂ := fun q => q ^ d * (G q * D.eval (J q))
  have hA : AnalyticAt ℂ A 0 := by simpa only [A, sub_zero, smul_eq_mul, Pi.mul_apply] using ha
  have hac : ∃ R : ℝ, ∀ τ : ℍ, R < τ.im →
      A (Function.Periodic.qParam 1 τ) = Function.Periodic.qParam 1 τ ^ d * H τ := by
    refine ⟨max S T, fun τ hτ => ?_⟩
    have hg' : AnalyticAt ℂ g (τ : ℂ) := hS _ τ.im_pos ((le_max_left _ _).trans_lt hτ)
    have hDJ' : ContinuousAt (fun w => D.eval (jFunction w)) (τ : ℂ) :=
      D.continuous.continuousAt.comp (X0Model.analyticOn_j _ τ.im_pos).continuousAt
    have hvalue : H τ = g τ * D.eval (jFunction τ) :=
      (ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
        (hH _ τ.im_pos).continuousAt (hg'.continuousAt.mul hDJ')).mp
        (he _ τ.im_pos) |>.eq_of_nhds
    simp only [A, hJval, hGval τ ((le_max_right _ _).trans_lt hτ), hvalue]
  obtain ⟨P, hP⟩ := levelOne_polynomial_of_cleared_cusp hH hHi hU hU0 hUval d hA hac
  refine ⟨P, D, hD, fun z hz => (he z hz).symm.trans ?_⟩
  filter_upwards [nhdsWithin_le_nhds (isOpen_upperHalfPlaneSet.mem_nhds hz)] with w hw
  exact hP ⟨w, hw⟩


end ZInQ.Manuscript.RC.ModFnClassify
