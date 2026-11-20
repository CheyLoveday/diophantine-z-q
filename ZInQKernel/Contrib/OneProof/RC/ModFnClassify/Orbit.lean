import ZInQKernel.Contrib.OneProof.RC.ModFnClassify.Cosets
import ZInQKernel.Contrib.OneProof.RC.ModFnClassify.CuspGrowth

/-! The coset orbit polynomial and the analytic nature of its coefficients.
Provenance (c). -/

noncomputable section

open Filter Topology Function UpperHalfPlane Polynomial Matrix
open scoped MatrixGroups

namespace ZInQ.Manuscript.RC.ModFnClassify

abbrev LevelInvariant (N : ℕ) (g : ℂ → ℂ) : Prop :=
  ∀ σ : SL(2, ℤ), σ ∈ CongruenceSubgroup.Gamma0 N →
    ∀ τ : ℍ, g (σ • τ : ℍ) = g τ

/-- Right multiplication by a modular-group element permutes the cosets. -/
def permuteCosets (N : ℕ) (γ : SL(2, ℤ)) : Equiv.Perm (LevelCosets N) := by
  let r (δ : SL(2, ℤ)) : LevelCosets N → LevelCosets N :=
    Quotient.map (· * δ) fun a b h => QuotientGroup.rightRel_apply.mpr (by
      simpa only [_root_.mul_inv_rev, mul_assoc, mul_inv_cancel_left] using
        QuotientGroup.rightRel_apply.mp h)
  refine ⟨r γ, r γ⁻¹, ?_, ?_⟩
  · intro c
    induction c using Quotient.inductionOn with
    | _ σ =>
      change Quotient.mk _ ((σ * γ) * γ⁻¹) = Quotient.mk _ σ
      rw [mul_inv_cancel_right]
  · intro c
    induction c using Quotient.inductionOn with
    | _ σ =>
      change Quotient.mk _ ((σ * γ⁻¹) * γ) = Quotient.mk _ σ
      rw [inv_mul_cancel_right]

/-- The value on a right coset is independent of the representative. -/
def orbitValue {N : ℕ} {g : ℂ → ℂ} (hg : LevelInvariant N g)
    (c : LevelCosets N) (τ : ℍ) : ℂ :=
  Quotient.liftOn c (fun σ => g (σ • τ : ℍ)) fun a b h => by
    have hb : g ((b * a⁻¹) • (a • τ) : ℍ) = g (a • τ : ℍ) :=
      hg (b * a⁻¹) (QuotientGroup.rightRel_apply.mp h) (a • τ)
    simpa only [← mul_smul, inv_mul_cancel_right] using hb.symm

theorem orbitValue_permute {N : ℕ} {g : ℂ → ℂ} (hg : LevelInvariant N g)
    (c : LevelCosets N) (γ : SL(2, ℤ)) (τ : ℍ) :
    orbitValue hg c (γ • τ) = orbitValue hg (permuteCosets N γ c) τ := by
  induction c using Quotient.inductionOn with
  | _ a =>
    change g (a • γ • τ : ℍ) = g ((a * γ) • τ : ℍ)
    rw [mul_smul]

/-- Product of the linear factors attached to the right cosets. -/
def orbitPoly {N : ℕ} [NeZero N] {g : ℂ → ℂ} (hg : LevelInvariant N g) (τ : ℍ) :
    ℂ[X] := by
  classical
  letI := Fintype.ofFinite (LevelCosets N)
  exact ∏ c : LevelCosets N, (X - C (orbitValue hg c τ))

theorem orbitPoly_invariant {N : ℕ} [NeZero N] {g : ℂ → ℂ} (hg : LevelInvariant N g)
    (γ : SL(2, ℤ)) (τ : ℍ) : orbitPoly hg (γ • τ) = orbitPoly hg τ := by
  classical
  let := Fintype.ofFinite (LevelCosets N)
  unfold orbitPoly
  exact Fintype.prod_equiv (permuteCosets N γ) _ _ fun c => by rw [orbitValue_permute]

theorem orbitPoly_root {N : ℕ} [NeZero N] {g : ℂ → ℂ} (hg : LevelInvariant N g)
    (τ : ℍ) : (orbitPoly hg τ).IsRoot (g τ) := by
  classical
  let := Fintype.ofFinite (LevelCosets N)
  rw [Polynomial.IsRoot, orbitPoly, eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ (Quotient.mk _ 1 : LevelCosets N))
  change (X - C (g ((1 : SL(2, ℤ)) • τ : ℍ))).eval (g τ) = 0
  simp

theorem orbitPoly_monic_degree {N : ℕ} [NeZero N] {g : ℂ → ℂ}
    (hg : LevelInvariant N g) (τ : ℍ) :
    (orbitPoly hg τ).Monic ∧ (orbitPoly hg τ).natDegree = Nat.card (LevelCosets N) := by
  classical
  let := Fintype.ofFinite (LevelCosets N)
  unfold orbitPoly
  refine ⟨monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _), ?_⟩
  rw [natDegree_finsetProd_X_sub_C_eq_card, Finset.card_univ, Nat.card_eq_fintype_card]

private theorem coeff_orbitProduct_closed {α ι : Type*} (s : Finset ι) (g : ι → α → ℂ)
    (P : (α → ℂ) → Prop) (hC : ∀ c : ℂ, P (fun _ => c))
    (hsub : ∀ {f g : α → ℂ}, P f → P g → P (fun z => f z - g z))
    (hmul : ∀ {f g : α → ℂ}, P f → P g → P (fun z => f z * g z))
    (hg : ∀ i ∈ s, P (g i)) (n : ℕ) :
    P (fun z => (∏ i ∈ s, (X - C (g i z))).coeff n) := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty =>
    simpa only [Finset.prod_empty] using hC ((1 : ℂ[X]).coeff n)
  | insert a s ha ih =>
    have hs := fun n => ih (fun i hi => hg i (Finset.mem_insert_of_mem hi)) n
    have ha' := hg a (Finset.mem_insert_self a s)
    have hprod (z : α) :
        (∏ i ∈ insert a s, (X - C (g i z))) =
          (∏ i ∈ s, (X - C (g i z))) * (X - C (g a z)) :=
      (Finset.prod_insert ha).trans (mul_comm _ _)
    cases n with
    | zero =>
      simpa only [hprod, mul_coeff_zero, coeff_sub, coeff_C_zero, coeff_X_zero, zero_sub] using
        hmul (hs 0) (hsub (hC 0) ha')
    | succ n =>
      simpa only [hprod, coeff_mul_X_sub_C] using hsub (hs n) (hmul (hs (n + 1)) ha')

/-- Each coefficient is level-one invariant and meromorphic in the upper
half-plane and in the width-one cusp parameter. No polynomiality in `j`
is asserted for a coefficient that may have interior poles. -/
theorem orbitCoefficient_cusp_of_growth {N : ℕ} [NeZero N] {g : ℂ → ℂ}
    (hg : MeromorphicOn g upperDomain) (hi : LevelInvariant N g)
    (ha' : ∀ σ : SL(2, ℤ), ∀ᶠ z : ℂ in comap Complex.im atTop,
      DifferentiableAt ℂ (fun w => g (σ • ofComplex w : ℍ)) z)
    (hb' : ∀ σ : SL(2, ℤ), CuspGrowth 1 (fun τ => g (σ • τ : ℍ)))
    (n : ℕ) :
    let a : ℂ → ℂ := fun z => (orbitPoly hi (ofComplex z)).coeff n
    MeromorphicOn a upperDomain ∧ LevelOneInvariant a ∧ CuspGerm 1 (fun τ => a τ) := by
  classical
  let := Fintype.ofFinite (LevelCosets N)
  let a : ℂ → ℂ := fun z => (orbitPoly hi (ofComplex z)).coeff n
  have hMer (c : LevelCosets N) : MeromorphicOn (fun z => orbitValue hi c (ofComplex z)) upperDomain := by
    induction c using Quotient.inductionOn with
    | _ σ =>
      intro z hz
      let τ : ℍ := ⟨z, hz⟩
      let A := Matrix.SpecialLinearGroup.mapGL ℝ σ
      have hA : 0 < A.val.det := by
        change 0 < (A.det : ℝ)
        rw [show A.det = 1 from Matrix.SpecialLinearGroup.det_mapGL σ]
        norm_num
      have h₁ : AnalyticAt ℂ (fun w => ((σ • ofComplex w : ℍ) : ℂ)) z := τ.analyticAt_smul hA
      have h₂ := hg (σ • τ : ℍ) (σ • τ : ℍ).im_pos
      change MeromorphicAt (fun w => g (σ • ofComplex w : ℍ)) z
      rw [show τ = ofComplex z from (ofComplex_apply_of_im_pos hz).symm] at h₂
      exact h₂.comp_analyticAt (g := fun w => ((σ • ofComplex w : ℍ) : ℂ)) h₁
  have hAnal (c : LevelCosets N) : ∀ᶠ z : ℂ in comap Complex.im atTop,
      DifferentiableAt ℂ (fun w => orbitValue hi c (ofComplex w)) z := by
    induction c using Quotient.inductionOn with
    | _ σ => exact ha' σ
  have hgrowth (c : LevelCosets N) : CuspGrowth 1 (orbitValue hi c) := by
    induction c using Quotient.inductionOn with
    | _ σ => exact hb' σ
  have hm : MeromorphicOn a upperDomain := by
    apply coeff_orbitProduct_closed Finset.univ (fun c z => orbitValue hi c (ofComplex z))
      (fun f => MeromorphicOn f upperDomain)
    · exact fun c z _ => MeromorphicAt.const c z
    · exact fun hf hg z hz => (hf z hz).sub (hg z hz)
    · exact fun hf hg z hz => (hf z hz).mul (hg z hz)
    · exact fun c _ => hMer c
  have ha : ∀ᶠ z : ℂ in comap Complex.im atTop, DifferentiableAt ℂ a z := by
    apply coeff_orbitProduct_closed Finset.univ (fun c z => orbitValue hi c (ofComplex z))
      (fun f => ∀ᶠ z : ℂ in comap Complex.im atTop, DifferentiableAt ℂ f z)
    · exact fun c => Eventually.of_forall fun _ => differentiableAt_const c
    · exact fun hf hg => (hf.and hg).mono fun _ hh => hh.1.sub hh.2
    · exact fun hf hg => (hf.and hg).mono fun _ hh => hh.1.mul hh.2
    · exact fun c _ => hAnal c
  have hi' : LevelOneInvariant a := by
    intro γ τ
    simpa only [a, ofComplex_apply] using congrArg (fun p : ℂ[X] => p.coeff n)
      (orbitPoly_invariant hi γ τ)
  have hper : Periodic ((fun τ : ℍ => a τ) ∘ ofComplex) (1 : ℝ) := by
    apply UpperHalfPlane.periodic_comp_ofComplex
    intro τ
    simpa only [modular_T_smul] using hi' ModularGroup.T τ
  have hb : CuspGrowth 1 (fun τ : ℍ => a τ) := by
    simp only [a, ofComplex_apply]
    apply coeff_orbitProduct_closed Finset.univ (orbitValue hi) (CuspGrowth 1)
    · exact cuspGrowth_const
    · exact cuspGrowth_sub one_pos
    · exact cuspGrowth_mul
    · exact fun c _ => hgrowth c
  refine ⟨hm, hi', cuspGerm_of_periodic_growth one_pos hper ?_ hb⟩
  filter_upwards [ha, (eventually_gt_atTop (0 : ℝ)).comap Complex.im] with z haz hz
  apply haz.congr_of_eventuallyEq
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hz] with w hw
  simp only [a, Function.comp_apply, ofComplex_apply_of_im_pos hw, coe_mk]

/-- At any positive cusp width, a meromorphic germ provides eventual
differentiability and width-one growth for the translate. -/
theorem cuspGerm_translates_analytic_growth {g : ℂ → ℂ}
    (h : SL(2, ℤ) → ℝ) (hh : ∀ σ, 0 < h σ)
    (hc : ∀ σ : SL(2, ℤ), CuspGerm (h σ) (fun τ => g (σ • τ : ℍ))) :
    (∀ σ : SL(2, ℤ), ∀ᶠ z : ℂ in comap Complex.im atTop,
      DifferentiableAt ℂ (fun w => g (σ • ofComplex w : ℍ)) z) ∧
    (∀ σ : SL(2, ℤ), CuspGrowth 1 (fun τ => g (σ • τ : ℍ))) := by
  constructor
  · intro σ
    have hcs : CuspGerm (h σ) (fun τ => g (σ • ofComplex (τ : ℂ) : ℍ)) := by
      simpa only [ofComplex_apply] using hc σ
    obtain ⟨T, hT⟩ := cuspGerm_analytic_tail (g := fun w => g (σ • ofComplex w : ℍ)) (hh σ) hcs
    filter_upwards [(eventually_gt_atTop (max T 0)).comap Complex.im] with z hz
    exact (hT z ((le_max_right _ _).trans_lt hz) ((le_max_left _ _).trans_lt hz)).differentiableAt
  · exact fun σ => cuspGrowth_changeWidth (hh σ) one_pos (cuspGerm_growth (hh σ) (hc σ))

theorem orbitCoefficient_cusp {N : ℕ} [NeZero N] {g : ℂ → ℂ}
    (hg : MeromorphicOn g upperDomain) (hi : LevelInvariant N g)
    (h : SL(2, ℤ) → ℝ) (hh : ∀ σ, 0 < h σ)
    (hc : ∀ σ : SL(2, ℤ), CuspGerm (h σ) (fun τ => g (σ • τ : ℍ)))
    (n : ℕ) :
    let a : ℂ → ℂ := fun z => (orbitPoly hi (ofComplex z)).coeff n
    MeromorphicOn a upperDomain ∧ LevelOneInvariant a ∧ CuspGerm 1 (fun τ => a τ) := by
  obtain ⟨ha, hb⟩ := cuspGerm_translates_analytic_growth h hh hc
  exact orbitCoefficient_cusp_of_growth hg hi ha hb n

/-- The coefficients of the orbit polynomial are rational functions of
`j`, as meromorphic germs on the upper half-plane. -/
theorem orbitCoefficient_rational_in_j {N : ℕ} [NeZero N] {g : ℂ → ℂ}
    (hg : MeromorphicOn g upperDomain) (hi : LevelInvariant N g)
    (h : SL(2, ℤ) → ℝ) (hh : ∀ σ, 0 < h σ)
    (hc : ∀ σ : SL(2, ℤ), CuspGerm (h σ) (fun τ => g (σ • τ : ℍ)))
    (n : ℕ) :
    ∃ P D : ℂ[X], D.Monic ∧ ∀ z ∈ upperDomain,
      (fun w => (orbitPoly hi (ofComplex w)).coeff n * D.eval (jFunction w)) =ᶠ[𝓝[≠] z]
        (fun w => P.eval (jFunction w)) := by
  obtain ⟨hm, hi', hc'⟩ := orbitCoefficient_cusp hg hi h hh hc n
  exact levelOne_rational_in_j hm hi' hc'

#print axioms orbitValue_permute
#print axioms orbitPoly_invariant
#print axioms orbitPoly_root
#print axioms orbitPoly_monic_degree
#print axioms coeff_orbitProduct_closed
#print axioms orbitCoefficient_cusp_of_growth
#print axioms cuspGerm_translates_analytic_growth
#print axioms orbitCoefficient_cusp
#print axioms orbitCoefficient_rational_in_j

end ZInQ.Manuscript.RC.ModFnClassify
