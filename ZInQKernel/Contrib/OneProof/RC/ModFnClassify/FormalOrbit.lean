import ZInQKernel.Contrib.OneProof.RC.ModFnClassify.Orbit
import ZInQKernel.Contrib.OneProof.RC.ModFnField.FieldMembership
import ZInQKernel.Contrib.OneProof.RC.ModFnField.Degree
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_transcendental_jqModC

/-! The analytic orbit polynomial gives a formal equation over `ℂ(j(q))`.
On-the-spot (c), tex 1785–1787 and 2836–2838. -/

noncomputable section

open Filter Topology Function UpperHalfPlane Polynomial Matrix ModularCurve
open scoped MatrixGroups
open ZInQ.Manuscript.RC.ModFnField

namespace ZInQ.Manuscript.RC.ModFnClassify

abbrev complexJField : IntermediateField ℂ (LaurentSeries ℂ) :=
  IntermediateField.adjoin ℂ ({jqModC ℂ} : Set (LaurentSeries ℂ))

theorem cuspGerm_realizes {f : ℍ → ℂ} (hf : CuspGerm 1 f) :
    ∃ a : LaurentSeries ℂ, Realizes a f := by
  obtain ⟨G, T, hG, hval⟩ := hf
  obtain ⟨a, _, r, hr, _, ha⟩ := meromorphicAt_hasSum_laurent hG
  refine ⟨a, ?_⟩
  filter_upwards [(qParam_tendsto_atImInfty one_pos).eventually (Metric.eball_mem_nhds 0 hr),
    (eventually_gt_atTop T).comap UpperHalfPlane.im] with τ hτ ht
  rw [← hval τ ht]
  exact ha _ (Periodic.qParam_ne_zero (τ : ℂ)) hτ

theorem realizes_j : Realizes (jqModC ℂ) (fun τ => jFunction τ) := by
  filter_upwards with τ
  have hj : complexify jq = jqModC ℂ := map_jqModC (Rat.castHom ℂ)
  simpa only [← hj, complexify_coeff, jFunction, ofComplex_apply, X0Model.analyticJ]
    using hasSum_jq_qParam τ

theorem realizes_finsetSum {ι : Type*} (s : Finset ι) {a : ι → LaurentSeries ℂ} {f : ι → ℍ → ℂ}
    (hf : ∀ i ∈ s, Realizes (a i) (f i)) :
    Realizes (∑ i ∈ s, a i) (fun τ => ∑ i ∈ s, f i τ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Realizes.const 0
  | insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using
      (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem realizes_complexPolynomial {a : LaurentSeries ℂ} {f : ℍ → ℂ} (hf : Realizes a f)
    (P : ℂ[X]) : Realizes (aeval a P) (fun τ => P.eval (f τ)) := by
  simp only [aeval_eq_sum_range, eval_eq_sum_range]
  exact realizes_finsetSum _ fun i _ => (Realizes.const (P.coeff i)).mul (hf.pow i)

/-- The level-one analytic converse in the formal complex Laurent field. -/
theorem realizes_mem_complexJField {a : LaurentSeries ℂ} {g : ℂ → ℂ}
    (hg : MeromorphicOn g upperDomain) (hi : LevelOneInvariant g)
    (hc : CuspGerm 1 (fun τ => g τ)) (ha : Realizes a (fun τ => g τ)) :
    a ∈ complexJField := by
  obtain ⟨P, D, hD, hPD⟩ := levelOne_rational_in_j hg hi hc
  obtain ⟨T, hT⟩ := cuspGerm_analytic_tail one_pos hc
  have hden : aeval (jqModC ℂ) D ≠ 0 := by
    intro he
    exact transcendental_jqModC ℂ ⟨D, hD.ne_zero, he⟩
  have heval (P : ℂ[X]) : aeval (jqModC ℂ) P ∈ complexJField :=
    Algebra.adjoin_le (by intro y hy; exact IntermediateField.subset_adjoin ℂ _ hy)
      (P.aeval_mem_adjoin_singleton ℂ (jqModC ℂ))
  have he : a * aeval (jqModC ℂ) D = aeval (jqModC ℂ) P := by
    apply Realizes.eq_of_eventuallyEq (ha.mul (realizes_complexPolynomial realizes_j D))
      (realizes_complexPolynomial realizes_j P)
    filter_upwards [(eventually_gt_atTop T).comap UpperHalfPlane.im] with τ hτ
    have hJ := (X0Model.analyticOn_j (τ : ℂ) τ.im_pos).continuousAt
    exact ((ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      ((hT _ τ.im_pos hτ).continuousAt.mul (D.continuous.continuousAt.comp hJ))
      (P.continuous.continuousAt.comp hJ)).mp (hPD _ τ.im_pos)).eq_of_nhds
  rw [(eq_div_iff hden).mpr he]
  exact complexJField.div_mem (heval P) (heval D)

/-- A meromorphic level function with all of its cusp germs gives a monic
equation over `ℂ(j(q))` for its Laurent expansion. The degree is bounded by
`ψ(N)`, including when the function has interior poles. -/
theorem formal_degree_bound_of_growth {N : ℕ} [NeZero N] {s : LaurentSeries ℂ} {g : ℂ → ℂ}
    (hg : MeromorphicOn g upperDomain) (hi : LevelInvariant N g)
    (ha' : ∀ σ : SL(2, ℤ), ∀ᶠ z : ℂ in comap Complex.im atTop,
      DifferentiableAt ℂ (fun w => g (σ • ofComplex w : ℍ)) z)
    (hb' : ∀ σ : SL(2, ℤ), CuspGrowth 1 (fun τ => g (σ • τ : ℍ)))
    (hs : Realizes s (fun τ => g τ)) :
    IsIntegral complexJField s ∧ (minpoly complexJField s).natDegree ≤ dedekindPsi N := by
  classical
  let d := Nat.card (LevelCosets N)
  let F (n : ℕ) (z : ℂ) := (orbitPoly hi (ofComplex z)).coeff n
  have hex (n : ℕ) : ∃ a : complexJField, Realizes a (fun τ => F n τ) := by
    obtain ⟨hm, hinv, hcusp⟩ := orbitCoefficient_cusp_of_growth hg hi ha' hb' n
    obtain ⟨a, ha⟩ := cuspGerm_realizes hcusp
    exact ⟨⟨a, realizes_mem_complexJField hm hinv hcusp ha⟩, ha⟩
  choose a ha using hex
  let P : complexJField[X] := ∑ n ∈ Finset.range (d + 1), C (a n) * X ^ n
  have hp_le : P.natDegree ≤ d := by
    refine natDegree_le_iff_coeff_eq_zero.mpr fun n hn => ?_
    simp only [P, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
    exact Finset.sum_eq_zero fun i hi => by
      have hh : n ≠ i := by have := Finset.mem_range.mp hi; omega
      simp [hh]
  have had : a d = 1 := by
    apply Subtype.ext
    apply Realizes.eq_of_eventuallyEq (ha d) (by simpa using Realizes.const 1)
    exact Eventually.of_forall fun τ => by
      have hP := orbitPoly_monic_degree hi τ
      simp only [F, ofComplex_apply]
      change (orbitPoly hi τ).coeff d = 1
      rw [show d = (orbitPoly hi τ).natDegree from hP.2.symm]
      exact hP.1
  have hp_d : P.coeff d = 1 := by
    rw [← had]
    simp only [P, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
    rw [Finset.sum_eq_single d]
    · simp
    · intro i _ hi
      simp [Ne.symm hi]
    · simp
  have hP : P.Monic := monic_of_natDegree_le_of_coeff_eq_one d hp_le hp_d
  have hR : Realizes (aeval s P) (fun τ => (orbitPoly hi τ).eval (g τ)) := by
    simp only [P, map_sum, map_mul, map_pow, aeval_X, aeval_C, IntermediateField.algebraMap_apply]
    refine (realizes_finsetSum (Finset.range (d + 1)) (fun i _ => (ha i).mul (hs.pow i))).mono
      fun τ hτ => ?_
    have hdt : (orbitPoly hi τ).natDegree < d + 1 := by
      rw [(orbitPoly_monic_degree hi τ).2]
      exact Nat.lt_succ_self d
    simpa only [F, ofComplex_apply, eval_eq_sum_range' hdt] using hτ
  have hr : aeval s P = 0 :=
    Realizes.eq_of_eventuallyEq hR (by simpa using Realizes.const 0)
      (Eventually.of_forall (orbitPoly_root hi))
  have hInt : IsIntegral complexJField s := ⟨P, hP, hr⟩
  refine ⟨hInt, ?_⟩
  exact ((minpoly.monic hInt).natDegree_le_of_dvd hP.ne_zero (minpoly.dvd _ _ hr)).trans
    (hp_le.trans (card_levelCosets_le N))

theorem formal_degree_bound {N : ℕ} [NeZero N] {s : LaurentSeries ℂ} {g : ℂ → ℂ}
    (hg : MeromorphicOn g upperDomain) (hi : LevelInvariant N g)
    (h : SL(2, ℤ) → ℝ) (hh : ∀ σ, 0 < h σ)
    (hc : ∀ σ : SL(2, ℤ), CuspGerm (h σ) (fun τ => g (σ • τ : ℍ)))
    (hs : Realizes s (fun τ => g τ)) :
    IsIntegral complexJField s ∧ (minpoly complexJField s).natDegree ≤ dedekindPsi N := by
  obtain ⟨ha, hb⟩ := cuspGerm_translates_analytic_growth h hh hc
  exact formal_degree_bound_of_growth hg hi ha hb hs

/-- The analytic hypotheses of the exact converse already give the uniform
elementwise degree bound. -/
theorem complexCusp_degree_bound {N : ℕ} [NeZero N] {s : LaurentSeries ℂ} {g : ℂ → ℂ}
    (hg : MeromorphicOn g upperDomain) (hi : LevelInvariant N g)
    (hc : ∀ σ : SL(2, ℤ),
      CuspGerm (translatedLevel N σ).strictWidthInfty (fun τ => g (σ • τ : ℍ)))
    (hs : Realizes s (fun τ => g τ)) :
    IsIntegral complexJField s ∧ (minpoly complexJField s).natDegree ≤ dedekindPsi N := by
  apply formal_degree_bound hg hi (fun σ => (translatedLevel N σ).strictWidthInfty) _ hc hs
  intro σ
  let Γ' := translatedLevel N σ
  have : Γ'.IsArithmetic := by
    simpa [Γ', translatedLevel, ← (Rat.castHom ℝ).algebraMap_toAlgebra, map_inv,
      Matrix.SpecialLinearGroup.map_mapGL]
      using Subgroup.IsArithmetic.conj
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))
        (Matrix.SpecialLinearGroup.mapGL ℚ σ)⁻¹
  exact Γ'.strictWidthInfty_pos


end ZInQ.Manuscript.RC.ModFnClassify
