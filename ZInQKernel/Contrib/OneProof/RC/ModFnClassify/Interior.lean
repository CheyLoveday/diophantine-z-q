import ZInQKernel.Contrib.OneProof.RC.X0Model.Expansion
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_E4_cube_div_discriminant_smul
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.NumberTheory.ModularForms.LevelOne.Basic

/-! Clearing interior poles at level one. On-the-spot (c) for tex 1785–1787
and 2836–2838. -/

noncomputable section

open Filter Topology Set UpperHalfPlane Matrix Polynomial
open scoped MatrixGroups

namespace ZInQ.Manuscript.RC.ModFnClassify

abbrev upperDomain : Set ℂ := {z | 0 < z.im}

abbrev jFunction (z : ℂ) : ℂ := X0Model.analyticJ (ofComplex z)

/-- The closed standard fundamental domain truncated at height `T`, in
complex coordinates. The lower edge is bounded away from the real line. -/
theorem isCompact_truncatedFundamentalDomain (T : ℝ) :
    IsCompact {z : ℂ | ∃ τ : ℍ, τ ∈ ModularGroup.fd ∧ τ.im ≤ T ∧ (τ : ℂ) = z} := by
  let S : Set ℂ := {z | 1 ≤ Complex.normSq z ∧ |z.re| ≤ 1 / 2 ∧ 1 / 2 ≤ z.im ∧ z.im ≤ T}
  have hs : IsClosed S :=
    (isClosed_le continuous_const Complex.continuous_normSq).inter
      ((isClosed_le Complex.continuous_re.abs continuous_const).inter
        ((isClosed_le continuous_const Complex.continuous_im).inter
          (isClosed_le Complex.continuous_im continuous_const)))
  have hc : IsCompact S := by
    refine (isCompact_closedBall (0 : ℂ) (1 + |T|)).of_isClosed_subset hs ?_
    intro z hz
    change 1 ≤ Complex.normSq z ∧ |z.re| ≤ 1 / 2 ∧ 1 / 2 ≤ z.im ∧ z.im ≤ T at hz
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ 1 + |T| := by
        rw [abs_of_nonneg (by linarith [hz.2.2.1] : 0 ≤ z.im)]
        linarith [hz.2.1, le_abs_self T, hz.2.2.2]
  convert hc using 1
  ext z
  constructor
  · rintro ⟨τ, hτ, hT, rfl⟩
    have hi := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hτ
    have hlow : 1 / 2 ≤ τ.im := by nlinarith [τ.im_pos]
    exact ⟨hτ.1, hτ.2, hlow, hT⟩
  · intro hz
    exact ⟨⟨z, lt_of_lt_of_le (by norm_num) hz.2.2.1⟩, ⟨hz.1, hz.2.1⟩, hz.2.2.2, rfl⟩

/-- A meromorphic function analytic above height `T` has only finitely
many nonanalytic points in the standard fundamental domain. -/
theorem finite_bad_in_fd {g : ℂ → ℂ} (hg : MeromorphicOn g upperDomain)
    (T : ℝ) (hT : ∀ z ∈ upperDomain, T < z.im → AnalyticAt ℂ g z) :
    {z : ℂ | (∃ τ : ℍ, τ ∈ ModularGroup.fd ∧ (τ : ℂ) = z) ∧
      ¬AnalyticAt ℂ g z}.Finite := by
  let K := {z : ℂ | ∃ τ : ℍ, τ ∈ ModularGroup.fd ∧ τ.im ≤ T ∧ (τ : ℂ) = z}
  have hK : K ⊆ upperDomain := by
    rintro z ⟨τ, _, _, rfl⟩
    exact τ.im_pos
  have hfin := (isCompact_truncatedFundamentalDomain T).finite_sdiff_of_mem_codiscreteWithin
    ((codiscreteWithin_mono hK) hg.analyticAt_mem_codiscreteWithin)
  apply hfin.subset
  rintro z ⟨⟨τ, hτ, rfl⟩, ha⟩
  exact ⟨⟨τ, hτ, le_of_not_gt (fun h => ha (hT _ τ.im_pos h)), rfl⟩, ha⟩

/-- Weight-zero invariance on the upper half-plane. -/
abbrev LevelOneInvariant (g : ℂ → ℂ) : Prop :=
  ∀ (γ : SL(2, ℤ)) (τ : ℍ), g (γ • τ : ℍ) = g τ

theorem jFunction_invariant : LevelOneInvariant jFunction := by
  intro γ τ
  simpa only [jFunction, ofComplex_apply, X0Model.analyticJ] using
    ModularCurve.E4_cube_div_discriminant_smul γ τ

theorem invariant_order {g : ℂ → ℂ} (hg : LevelOneInvariant g)
    (γ : SL(2, ℤ)) (τ : ℍ) :
    meromorphicOrderAt g (γ • τ : ℍ) = meromorphicOrderAt g (τ : ℂ) := by
  let A := Matrix.SpecialLinearGroup.mapGL ℝ γ
  have hA : 0 < A.val.det := by
    change 0 < (A.det : ℝ)
    rw [show A.det = 1 from Matrix.SpecialLinearGroup.det_mapGL γ]
    norm_num
  let f : ℍ → ℂ := fun w => g w
  have hfg (w : ℍ) : (fun z => f (ofComplex z)) =ᶠ[𝓝[≠] (w : ℂ)] g := by
    filter_upwards [nhdsWithin_le_nhds (isOpen_upperHalfPlaneSet.mem_nhds w.im_pos)]
      with z hz
    simp [f, ofComplex_apply_of_im_pos hz]
  have h := UpperHalfPlane.meromorphicOrderAt_comp_smul (f := f) (τ := τ) hA
  change meromorphicOrderAt (fun z => f (γ • ofComplex z)) (τ : ℂ) =
    meromorphicOrderAt (fun z => f (ofComplex z)) (γ • τ : ℍ) at h
  have he : (fun z => f (γ • ofComplex z)) = (fun z => f (ofComplex z)) :=
    funext fun z => hg γ (ofComplex z)
  simpa only [he, meromorphicOrderAt_congr (hfg τ), meromorphicOrderAt_congr (hfg (γ • τ))]
    using h.symm

private theorem pole_killing_power {g u : ℂ → ℂ} {z : ℂ}
    (hg : MeromorphicAt g z) (hu : AnalyticAt ℂ u z) (huz : u z = 0) :
    ∃ n : ℕ, 0 ≤ meromorphicOrderAt (fun w => g w * u w ^ n) z := by
  have hp : 0 < meromorphicOrderAt u z :=
    (tendsto_zero_iff_meromorphicOrderAt_pos hu.meromorphicAt).mp
      (huz ▸ hu.continuousAt.continuousWithinAt.tendsto)
  cases hgord : meromorphicOrderAt g z with
  | top =>
    refine ⟨0, ?_⟩
    simp [hgord]
  | coe m =>
    let n := (-m).toNat + 1
    refine ⟨n, ?_⟩
    change 0 ≤ meromorphicOrderAt (g * u ^ n) z
    rw [meromorphicOrderAt_mul hg (hu.pow n).meromorphicAt,
      meromorphicOrderAt_pow hu.meromorphicAt, hgord]
    cases huord : meromorphicOrderAt u z with
    | top =>
      have hn : (n : WithTop ℤ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      simp [WithTop.mul_top hn]
    | coe k =>
      rw [huord] at hp
      have hk : (1 : ℤ) ≤ k := by exact Int.add_one_le_iff.mpr (WithTop.coe_pos.mp hp)
      rw [← WithTop.coe_natCast, ← WithTop.coe_mul, ← WithTop.coe_add]
      apply WithTop.coe_nonneg.mpr
      have hm : -m ≤ (n : ℤ) := by dsimp [n]; omega
      have hnk := mul_le_mul_of_nonneg_left hk (Int.natCast_nonneg n)
      omega

/-- Multiplying by a monic polynomial in `j` clears all interior poles.
The product has an invariant analytic representative; isolated assigned
values of the original meromorphic function are immaterial. -/
theorem clear_interior_poles {g : ℂ → ℂ} (hg : MeromorphicOn g upperDomain)
    (hinv : LevelOneInvariant g)
    (T : ℝ) (hT : ∀ z ∈ upperDomain, T < z.im → AnalyticAt ℂ g z) :
    ∃ (D : ℂ[X]) (H : ℂ → ℂ), D.Monic ∧ AnalyticOnNhd ℂ H upperDomain ∧
      LevelOneInvariant H ∧
      ∀ z ∈ upperDomain, H =ᶠ[𝓝[≠] z] (fun w => g w * D.eval (jFunction w)) := by
  classical
  let B := (finite_bad_in_fd hg T hT).toFinset
  have hB (p : ℂ) (hp : p ∈ B) : p ∈ upperDomain := by
    rw [Set.Finite.mem_toFinset] at hp
    obtain ⟨⟨τ, _, rfl⟩, _⟩ := hp
    exact τ.im_pos
  let u := fun (p z : ℂ) => jFunction z - jFunction p
  have hu (p z : ℂ) (hz : z ∈ upperDomain) : AnalyticAt ℂ (u p) z :=
    (X0Model.analyticOn_j z hz).sub analyticAt_const
  have hkill (p : ℂ) (hp : p ∈ B) :
      ∃ n : ℕ, 0 ≤ meromorphicOrderAt (fun z => g z * u p z ^ n) p :=
    pole_killing_power (hg p (hB p hp)) (hu p p (hB p hp)) (sub_self _)
  let n (p : ℂ) : ℕ := if hp : p ∈ B then (hkill p hp).choose else 0
  let D : ℂ[X] := ∏ p ∈ B, (Polynomial.X - Polynomial.C (jFunction p)) ^ n p
  have hD (z : ℂ) : D.eval (jFunction z) = ∏ p ∈ B, u p z ^ n p := by
    simp [D, u, Polynomial.eval_prod, Polynomial.eval_pow]
  let G : ℂ → ℂ := fun z => g z * D.eval (jFunction z)
  have hDanalytic (z : ℂ) (hz : z ∈ upperDomain) :
      AnalyticAt ℂ (fun w => D.eval (jFunction w)) z :=
    (Finset.analyticAt_fun_prod B (fun p _ => (hu p z hz).pow (n p))).congr
      (Eventually.of_forall fun w => (hD w).symm)
  have hm : MeromorphicOn G upperDomain := fun z hz =>
    (hg z hz).mul (hDanalytic z hz).meromorphicAt
  have hGi : LevelOneInvariant G := by
    intro γ τ
    simp only [G, hinv γ τ, jFunction_invariant γ τ]
  have horder (τ : ℍ) (hτ : τ ∈ ModularGroup.fd) :
      0 ≤ meromorphicOrderAt G (τ : ℂ) := by
    by_cases hb : (τ : ℂ) ∈ B
    · let p := (τ : ℂ)
      have hg' : MeromorphicAt (fun w => g w * u p w ^ n p) p :=
        (hg p τ.im_pos).mul ((hu p p τ.im_pos).pow _).meromorphicAt
      have he : G = (fun z => (g z * u p z ^ n p) * ∏ a ∈ B.erase p, u a z ^ n a) := by
        funext z
        simp only [G, hD, mul_assoc]
        congr 1
        exact (Finset.mul_prod_erase B (fun a => u a z ^ n a) hb).symm
      have hrest : AnalyticAt ℂ (fun z => ∏ a ∈ B.erase p, u a z ^ n a) p :=
        Finset.analyticAt_fun_prod _ fun a _ => (hu a p τ.im_pos).pow _
      have hn : 0 ≤ meromorphicOrderAt (fun w => g w * u p w ^ n p) p := by
        have hp : p ∈ B := hb
        simpa only [n, dite_eq_left hp] using (hkill p hp).choose_spec
      rw [he]
      change 0 ≤ meromorphicOrderAt
        ((fun w => g w * u p w ^ n p) * fun z => ∏ a ∈ B.erase p, u a z ^ n a) p
      rw [meromorphicOrderAt_mul hg' hrest.meromorphicAt]
      exact add_nonneg hn hrest.meromorphicOrderAt_nonneg
    · have ha : AnalyticAt ℂ g (τ : ℂ) := by
        by_contra hc
        exact hb ((Set.Finite.mem_toFinset _).mpr ⟨⟨τ, hτ, rfl⟩, hc⟩)
      exact (ha.mul (hDanalytic _ τ.im_pos)).meromorphicOrderAt_nonneg
  have hnonneg (z : ℂ) (hz : z ∈ upperDomain) : 0 ≤ meromorphicOrderAt G z := by
    let τ : ℍ := ⟨z, hz⟩
    obtain ⟨γ, hγ⟩ := ModularGroup.exists_smul_mem_fd τ
    exact (invariant_order hGi γ τ) ▸ horder _ hγ
  let H := toMeromorphicNFOn G upperDomain
  have hHa : AnalyticOnNhd ℂ H upperDomain := by
    intro z hz
    exact (((hm z hz).meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt).mp
      (hnonneg z hz)).congr (toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hm hz).symm
  have hH (z : ℂ) (hz : z ∈ upperDomain) : H =ᶠ[𝓝[≠] z] G :=
    hm.toMeromorphicNFOn_eq_self_on_nhdsNE hz
  refine ⟨D, H, ?_, hHa, ?_, hH⟩
  · exact Polynomial.monic_prod_of_monic _ _ fun p _ =>
      (Polynomial.monic_X_sub_C (jFunction p)).pow _
  · intro γ τ
    let A := Matrix.SpecialLinearGroup.mapGL ℝ γ
    have hA : 0 < A.val.det := by
      change 0 < (A.det : ℝ)
      rw [show A.det = 1 from Matrix.SpecialLinearGroup.det_mapGL γ]
      norm_num
    let F : ℂ → ℂ := fun z => (γ • ofComplex z : ℍ)
    have hF : AnalyticAt ℂ F (τ : ℂ) := τ.analyticAt_smul hA
    have hFd : deriv F (τ : ℂ) ≠ 0 := τ.deriv_smul_ne_zero hA
    have hval : F τ = (γ • τ : ℍ) := by simp [F]
    have ht : Tendsto F (𝓝[≠] (τ : ℂ)) (𝓝[≠] (F τ)) :=
      hF.differentiableAt.hasDerivAt.tendsto_nhdsNE hFd
    have hzF : F τ ∈ upperDomain := by rw [hval]; exact (γ • τ : ℍ).im_pos
    have he := (hH (F τ) hzF).comp_tendsto ht
    have hs : H ∘ F =ᶠ[𝓝[≠] (τ : ℂ)] H := by
      filter_upwards [he, hH (τ : ℂ) τ.im_pos,
        nhdsWithin_le_nhds (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)] with z h1 h2 hz
      have hfz : F z = (γ • (⟨z, hz⟩ : ℍ) : ℍ) := by
        simp only [F, ofComplex_apply_of_im_pos hz]
      exact h1.trans ((congrArg G hfz).trans ((hGi γ ⟨z, hz⟩).trans h2.symm))
    rw [← hval]
    exact tendsto_nhds_unique
      (((hHa (F τ) hzF).continuousAt.comp hF.continuousAt).continuousWithinAt.tendsto)
      ((hHa (τ : ℂ) τ.im_pos).continuousAt.continuousWithinAt.tendsto.congr' hs.symm)

#print axioms isCompact_truncatedFundamentalDomain
#print axioms finite_bad_in_fd
#print axioms jFunction_invariant
#print axioms invariant_order
#print axioms pole_killing_power
#print axioms clear_interior_poles

end ZInQ.Manuscript.RC.ModFnClassify
