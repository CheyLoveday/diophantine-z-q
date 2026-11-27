import ZInQKernel.Contrib.OneProof.RC.ModFnClassify.FormalOrbit
import ZInQKernel.Contrib.OneProof.RC.ModFnClassify.Compositum
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_finrank_adjoin_jqNModC_eq_dedekindPsi_of_socket
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_jqNModC_prime_not_mem_adjoin_of_charZero
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_ModularPolynomialData_eval_E4_cube_div_discriminant_smul_eq_zero
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Mathlib.Analysis.Polynomial.CauchyBound

/-! The analytic generator and the complex classification. On-the-spot (c),
for the map at tex 1785–1787 and 2836–2838. -/

noncomputable section

open Filter Function UpperHalfPlane ModularCurve Polynomial Matrix
open scoped MatrixGroups NNReal
open ZInQ.Manuscript.RC.ModFnField

namespace ZInQ.Manuscript.RC.ModFnClassify

abbrev jNFunction (N : ℕ) [NeZero N] (z : ℂ) : ℂ :=
  X0Model.analyticJN N (ofComplex z)

private theorem dilate_smul_level (N : ℕ) [NeZero N] (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    ∃ δ : SL(2, ℤ), ∀ τ, X0Model.dilate N (γ • τ) = δ • X0Model.dilate N τ := by
  obtain ⟨c, hc⟩ := (CharP.intCast_eq_zero_iff (ZMod N) N (γ 1 0)).mp
    (CongruenceSubgroup.Gamma0_mem.mp hγ)
  have hdet := γ.property
  rw [Matrix.det_fin_two] at hdet
  let A : Matrix (Fin 2) (Fin 2) ℤ := !![γ 0 0, N * γ 0 1; c, γ 1 1]
  have ha : A.det = 1 := by
    rw [Matrix.det_fin_two]
    change γ 0 0 * γ 1 1 - (N : ℤ) * γ 0 1 * c = 1
    rw [hc] at hdet
    linear_combination hdet
  let δ : SL(2, ℤ) := ⟨A, ha⟩
  refine ⟨δ, fun τ => UpperHalfPlane.ext ?_⟩
  change (N : ℂ) * ((γ • τ : ℍ) : ℂ) = ((δ • X0Model.dilate N τ : ℍ) : ℂ)
  rw [UpperHalfPlane.coe_specialLinearGroup_apply, UpperHalfPlane.coe_specialLinearGroup_apply]
  change (N : ℂ) * (((γ 0 0 : ℂ) * (τ : ℂ) + (γ 0 1 : ℂ)) /
    ((γ 1 0 : ℂ) * (τ : ℂ) + (γ 1 1 : ℂ))) =
    (((γ 0 0 : ℂ) * ((N : ℂ) * (τ : ℂ)) + (((N : ℤ) * γ 0 1 : ℤ) : ℂ)) /
    ((c : ℂ) * ((N : ℂ) * (τ : ℂ)) + (γ 1 1 : ℂ)))
  rw [hc]
  push_cast
  have hd : (c : ℂ) * ((N : ℂ) * (τ : ℂ)) + (γ 1 1 : ℂ) =
      (N : ℂ) * (c : ℂ) * (τ : ℂ) + (γ 1 1 : ℂ) := by ring
  rw [hd, ← mul_div_assoc, mul_add]
  congr 1
  ring

theorem jNFunction_invariant (N : ℕ) [NeZero N] : LevelInvariant N (jNFunction N) := by
  intro γ hγ τ
  obtain ⟨δ, hδ⟩ := dilate_smul_level N γ hγ
  simp only [jNFunction, ofComplex_apply, X0Model.analyticJN, hδ]
  exact E4_cube_div_discriminant_smul δ (X0Model.dilate N τ)

theorem jN_translate_analytic (N : ℕ) [NeZero N] (σ : SL(2, ℤ)) :
    AnalyticOnNhd ℂ (fun z => jNFunction N (σ • ofComplex z : ℍ)) upperDomain := by
  intro z hz
  let τ : ℍ := ⟨z, hz⟩
  let A := Matrix.SpecialLinearGroup.mapGL ℝ σ
  have hA : 0 < A.val.det := by
    change 0 < (A.det : ℝ)
    rw [show A.det = 1 from Matrix.SpecialLinearGroup.det_mapGL σ]
    norm_num
  have ha : AnalyticAt ℂ (fun w => ((σ • ofComplex w : ℍ) : ℂ)) z :=
    τ.analyticAt_smul hA
  have hb : ((σ • ofComplex z : ℍ) : ℂ) ∈ upperDomain := (σ • ofComplex z : ℍ).im_pos
  have hh := (X0Model.analyticOn_jN N _ hb).comp (f := fun w => ((σ • ofComplex w : ℍ) : ℂ)) ha
  exact hh

private theorem cuspGrowth_add_one {f g : ℍ → ℂ}
    (hf : CuspGrowth 1 f) (hg : CuspGrowth 1 g) :
    CuspGrowth 1 (fun τ => f τ + g τ) := by
  have hn := cuspGrowth_sub one_pos (cuspGrowth_const (h := 1) 0) hg
  simpa only [zero_sub, sub_neg_eq_add] using cuspGrowth_sub one_pos hf hn

private theorem j_polynomial_growth (p : ℂ[X]) :
    CuspGrowth 1 (fun τ => p.eval (jFunction τ)) := by
  obtain ⟨U, hU, _, hval⟩ := j_cusp_unit
  have hJ : CuspGrowth 1 (fun τ => jFunction τ) := by
    refine ⟨1, ((hU.continuousAt.tendsto.comp
      (qParam_tendsto_atImInfty one_pos)).isBigO_one ℝ).congr' ?_ (by rfl)⟩
    exact Eventually.of_forall fun τ => by simpa only [Function.comp_apply, pow_one] using hval τ
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [eval_add] using cuspGrowth_add_one hp hq
  | monomial n a =>
    have hpow (n : ℕ) : CuspGrowth 1 (fun τ => jFunction τ ^ n) := by
      induction n with
      | zero => simpa only [pow_zero] using cuspGrowth_const (h := 1) 1
      | succ n ih => simpa only [pow_succ] using cuspGrowth_mul ih hJ
    simpa only [eval_monomial] using cuspGrowth_mul (cuspGrowth_const a) (hpow n)

/-- A root of a monic polynomial with coefficients polynomial in the
first j-coordinate has at most exponential growth at infinity. -/
theorem cuspGrowth_root_of_monic {f : ℍ → ℂ} (P : Polynomial (Polynomial ℤ))
    (hP : P.Monic)
    (hf : ∀ τ : ℍ, (P.map (eval₂RingHom (Int.castRingHom ℂ) (jFunction τ))).IsRoot (f τ)) :
    CuspGrowth 1 f := by
  classical
  let coeff (i : Fin P.natDegree) (τ : ℍ) :=
    (P.coeff i).eval₂ (Int.castRingHom ℂ) (jFunction τ)
  have hg (i : Fin P.natDegree) : CuspGrowth 1 (coeff i) := by
    simpa only [coeff, eval_map] using j_polynomial_growth ((P.coeff i).map (Int.castRingHom ℂ))
  choose d hd using hg
  choose M T hT using fun i => isBoundedAtImInfty_iff.mp (hd i)
  let D := ∑ i, d i
  have hdD (i : Fin P.natDegree) : d i ≤ D :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (d j)) (Finset.mem_univ i)
  have hTall : ∀ᶠ τ : ℍ in atImInfty, ∀ i : Fin P.natDegree, T i < τ.im :=
    Filter.eventually_all.mpr (fun i => (eventually_gt_atTop (T i)).comap UpperHalfPlane.im)
  let bound : ℝ≥0 := ∑ i, Real.toNNReal (M i)
  obtain ⟨S, hS⟩ := (atImInfty_mem _).mp hTall
  refine ⟨D, isBoundedAtImInfty_iff.mpr ⟨(bound : ℝ) + 1, S, fun τ hτ => ?_⟩⟩
  let p := P.map (eval₂RingHom (Int.castRingHom ℂ) (jFunction τ))
  have hm : p.Monic := hP.map _
  have hdeg : p.natDegree = P.natDegree := hP.natDegree_map _
  have hq : ‖Periodic.qParam 1 (τ : ℂ)‖ ≤ 1 :=
    (Periodic.norm_qParam_lt_one one_pos τ.im_pos).le
  have hqi (i : Fin P.natDegree) :
      ‖Periodic.qParam 1 (τ : ℂ) ^ D * coeff i τ‖ ≤ (bound : ℝ) := by
    refine le_trans ?_ (le_trans (hT i τ (hS τ hτ i).le) ?_)
    · simp only [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (norm_nonneg _) hq (hdD i))
        (norm_nonneg _)
    · have hm : Real.toNNReal (M i) ≤ bound :=
        Finset.single_le_sum (f := fun j : Fin P.natDegree => Real.toNNReal (M j))
          (fun _ _ => zero_le) (Finset.mem_univ i)
      exact (Real.le_coe_toNNReal _).trans (by exact_mod_cast hm)
  have hb : ‖Periodic.qParam 1 (τ : ℂ)‖₊ ^ D *
      (Finset.range p.natDegree).sup (fun i => ‖p.coeff i‖₊) ≤ bound := by
    rw [NNReal.mul_finset_sup]
    apply Finset.sup_le
    intro i hi
    have hi' : i < P.natDegree := hdeg ▸ Finset.mem_range.mp hi
    exact_mod_cast (show ‖Periodic.qParam 1 (τ : ℂ)‖ ^ D * ‖p.coeff i‖ ≤ (bound : ℝ) from by
      simp only [p, coeff_map]
      exact (show ‖Periodic.qParam 1 (τ : ℂ)‖ ^ D * ‖coeff ⟨i, hi'⟩ τ‖ ≤ (bound : ℝ) by
        simpa only [norm_mul, norm_pow] using hqi ⟨i, hi'⟩))
  have hr := (hf τ).norm_lt_cauchyBound hm.ne_zero
  change ‖f τ‖₊ < p.cauchyBound at hr
  rw [cauchyBound, hm, nnnorm_one, div_one] at hr
  have hfinal : ‖Periodic.qParam 1 (τ : ℂ)‖₊ ^ D * ‖f τ‖₊ ≤ bound + 1 := by
    calc
      _ ≤ ‖Periodic.qParam 1 (τ : ℂ)‖₊ ^ D *
          ((Finset.range p.natDegree).sup (fun i => ‖p.coeff i‖₊) + 1) :=
        mul_le_mul_of_nonneg_left hr.le zero_le
      _ ≤ _ := by
        rw [mul_add, mul_one]
        exact add_le_add hb (pow_le_one₀ zero_le (by exact_mod_cast hq))
  rw [norm_mul, norm_pow]
  exact_mod_cast hfinal

theorem jN_translate_growth (N : ℕ) [NeZero N] (σ : SL(2, ℤ)) :
    CuspGrowth 1 (fun τ => jNFunction N (σ • τ : ℍ)) := by
  obtain ⟨P⟩ := nonempty_modularPolynomialData N
  refine cuspGrowth_root_of_monic (f := fun τ => jNFunction N (σ • τ : ℍ)) P.Φ P.monic ?_
  intro τ
  have hj := jFunction_invariant σ τ
  rw [IsRoot.def, ← hj]
  simpa only [jFunction, jNFunction, ofComplex_apply, X0Model.analyticJ, X0Model.analyticJN] using
    P.eval_E4_cube_div_discriminant_smul_eq_zero N (σ • τ) (X0Model.dilate N (σ • τ)) rfl

private theorem qParam_width_one_zpow (z : ℂ) (n : ℤ) :
    Periodic.qParam 1 z ^ n = Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * z) := by
  rw [Periodic.qParam, Complex.ofReal_one, div_one, ← Complex.exp_int_mul]
  congr 1
  ring

theorem realizes_jN (N : ℕ) [NeZero N] :
    Realizes (jqNModC ℂ N) (fun τ => jNFunction N τ) := by
  have hmap : complexify (jqN N) = jqNModC ℂ N := by
    have hj : complexify jq = jqModC ℂ := map_jqModC (Rat.castHom ℂ)
    ext n
    by_cases hn : (N : ℤ) ∣ n
    · obtain ⟨k, rfl⟩ := hn
      simpa only [complexify_coeff, jqN, jqNModC, qExpand_coeff_mul] using
        congrArg (fun z : LaurentSeries ℂ => z.coeff k) hj
    · simp [jqN, jqNModC, qExpand_coeff_of_not_dvd _ _ hn]
  rw [← hmap]
  filter_upwards with τ
  simpa only [complexify_coeff, qParam_width_one_zpow, jNFunction, ofComplex_apply] using
    X0Model.hasSum_jN N τ

theorem complex_jN_minpoly_degree (N : ℕ) [NeZero N] :
    IsIntegral complexJField (jqNModC ℂ N) ∧
      (minpoly complexJField (jqNModC ℂ N)).natDegree = dedekindPsi N := by
  have hA (σ : SL(2, ℤ)) : ∀ᶠ z : ℂ in comap Complex.im atTop,
      DifferentiableAt ℂ (fun w => jNFunction N (σ • ofComplex w : ℍ)) z := by
    exact ((eventually_gt_atTop (0 : ℝ)).comap Complex.im).mono
      (fun z hz => (jN_translate_analytic N σ z hz).differentiableAt)
  have hI := (formal_degree_bound_of_growth
    (fun z hz => (X0Model.analyticOn_jN N z hz).meromorphicAt)
    (jNFunction_invariant N) hA (jN_translate_growth N) (realizes_jN N)).1
  refine ⟨hI, ?_⟩
  rw [← IntermediateField.adjoin.finrank hI]
  exact finrank_adjoin_jqNModC_eq_dedekindPsi_of_socket N
    (fun p _ _ => jqNModC_prime_not_mem_adjoin_of_charZero p)

theorem complexCuspClassification (N : ℕ) [NeZero N] : ComplexCuspClassification N := by
  intro g s hm hi hc hs
  have hs' : Realizes s (fun τ => g τ) := by
    obtain ⟨T, hT⟩ := hs
    exact ((eventually_gt_atTop T).comap UpperHalfPlane.im).mono hT
  have hwidth (σ : SL(2, ℤ)) : 0 < (translatedLevel N σ).strictWidthInfty := by
    let Γ' := translatedLevel N σ
    have : Γ'.IsArithmetic := by
      simpa [Γ', translatedLevel, ← (Rat.castHom ℝ).algebraMap_toAlgebra, map_inv,
        Matrix.SpecialLinearGroup.map_mapGL]
        using Subgroup.IsArithmetic.conj
          (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))
          (Matrix.SpecialLinearGroup.mapGL ℚ σ)⁻¹
    exact Γ'.strictWidthInfty_pos
  obtain ⟨ha, hb⟩ := cuspGerm_translates_analytic_growth _ hwidth hc
  obtain ⟨hjI, hjD⟩ := complex_jN_minpoly_degree N
  have hsI := (formal_degree_bound_of_growth hm hi ha hb hs').1
  have hS : s ∈ IntermediateField.adjoin complexJField ({jqNModC ℂ N} : Set (LaurentSeries ℂ)) := by
    apply mem_adjoin_of_linear_degree_bound (R := ℂ) hjI hsI
    intro c
    rw [hjD]
    let v : ℂ → ℂ := fun z => jNFunction N z + c * g z
    have hm' : MeromorphicOn v upperDomain := fun z hz =>
      ((X0Model.analyticOn_jN N z hz).meromorphicAt).add ((MeromorphicAt.const c z).mul (hm z hz))
    have hi' : LevelInvariant N v := fun σ hσ τ => by
      simp only [v, jNFunction_invariant N σ hσ τ, hi σ hσ τ]
    have ha' (σ : SL(2, ℤ)) : ∀ᶠ z : ℂ in comap Complex.im atTop,
        DifferentiableAt ℂ (fun w => v (σ • ofComplex w : ℍ)) z := by
      filter_upwards [ha σ, (eventually_gt_atTop (0 : ℝ)).comap Complex.im] with z hz hpos
      exact (jN_translate_analytic N σ z hpos).differentiableAt.add
        ((differentiableAt_const c).mul hz)
    have hb' (σ : SL(2, ℤ)) : CuspGrowth 1 (fun τ => v (σ • τ : ℍ)) :=
      cuspGrowth_add_one (jN_translate_growth N σ) (cuspGrowth_mul (cuspGrowth_const c) (hb σ))
    exact (formal_degree_bound_of_growth hm' hi' ha' hb'
      ((realizes_jN N).add ((Realizes.const c).mul hs'))).2
  rw [modularFunctionFieldC, ← IntermediateField.adjoin_simple_adjoin_simple]
  exact hS


end ZInQ.Manuscript.RC.ModFnClassify
