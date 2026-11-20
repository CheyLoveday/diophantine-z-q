import ZInQKernel.Contrib.OneProof.RC.ModFnField.Equation

/-! At an interior lattice value the analytic affine x-coordinate has a
genuine pole. Provenance (c), tex 1785–1787. -/

noncomputable section

open Filter Topology Function UpperHalfPlane WeierstrassCurve
open ZInQ.Contrib.CloudB3RC53.CST
open ZInQ.Manuscript.RC.ParamAtScale ZInQ.Manuscript.RC.ModFnField

namespace ZInQ.Manuscript.RC.ModFnClassify

/-- The leading coefficient of x at the cusp implies that the analytic
primitive is not constant on the upper half-plane. -/
theorem scaledPrimitive_not_constant (E : WeierstrassCurve ℚ) {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    {L : PeriodPair} (hL : IsLatticeOf E L) {κ : ℚ} (hκ : κ ≠ 0) (c : ℂ) :
    ¬ ∀ τ : ℍ, scaledPrimitive f κ τ = c := by
  intro hconst
  obtain ⟨x, _, T, _, _, hlead, hs⟩ := coordinates_rationalLaurent E f hf hL hκ
  have hreal : Realizes (complexify x) (fun τ => xCoordinate E f L κ τ) := by
    refine ((eventually_gt_atTop T).comap UpperHalfPlane.im).mono fun τ hτ => ?_
    simpa only [complexify_coeff] using (hs τ hτ).1
  have he := Realizes.eq_of_eventuallyEq hreal
    (Realizes.const (L.weierstrassP c - (E.b₂ : ℂ) / 12))
    (Eventually.of_forall fun τ => by simp only [xCoordinate, hconst τ])
  have hz := congrArg (fun v : LaurentSeries ℂ => v.coeff (-2)) he
  simp only [complexify_coeff, HahnSeries.algebraMap_apply',
    show algebraMap ℂ (PowerSeries ℂ) (L.weierstrassP c - (E.b₂ : ℂ) / 12) =
      PowerSeries.C (L.weierstrassP c - (E.b₂ : ℂ) / 12) by simp,
    HahnSeries.ofPowerSeries_C, hlead] at hz
  change _ = (HahnSeries.single (0 : ℤ) (L.weierstrassP c - (E.b₂ : ℂ) / 12)).coeff (-2) at hz
  rw [HahnSeries.coeff_single_of_ne (by norm_num : (-2 : ℤ) ≠ 0)] at hz
  exact pow_ne_zero 2 (inv_ne_zero (show (κ : ℂ) ≠ 0 by exact_mod_cast hκ)) hz

/-- At a lattice value, x cannot have any analytic representative of its
punctured germ. This includes ramified points where the primitive has zero
derivative. -/
theorem xCoordinate_no_analytic_germ_at_lattice (E : WeierstrassCurve ℚ)
    {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    {L : PeriodPair} (hL : IsLatticeOf E L) {κ : ℚ} (hκ : κ ≠ 0)
    (τ : ℍ) (hτ : scaledPrimitive f κ τ ∈ L.lattice) :
    ¬ ∃ G : ℂ → ℂ, AnalyticAt ℂ G (τ : ℂ) ∧
      G =ᶠ[𝓝[≠] (τ : ℂ)] xCoordinate E f L κ := by
  rintro ⟨G, hG, he⟩
  let l := scaledPrimitive f κ τ
  let u := fun z => scaledPrimitive f κ z - l
  have hu : AnalyticOnNhd ℂ u {z | 0 < z.im} :=
    fun z hz => (scaledPrimitive_analytic f κ hz).sub analyticAt_const
  have hu0 : u τ = 0 := sub_self _
  have hu_ne : ∀ᶠ z in 𝓝[≠] (τ : ℂ), u z ≠ 0 := by
    rcases (hu _ τ.im_pos).meromorphicAt.eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      apply scaledPrimitive_not_constant E f hf hL hκ l
      intro σ
      have hs : meromorphicOrderAt u (σ : ℂ) = ⊤ :=
        hu.meromorphicOn.meromorphicOrderAt_eq_top_of_isPreconnected
          (convex_halfSpace_im_gt 0).isPreconnected τ.im_pos σ.im_pos
          (meromorphicOrderAt_eq_top_iff.mpr h)
      have hEq := (ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
        (hu _ σ.im_pos).continuousAt continuousAt_const).mp
        (meromorphicOrderAt_eq_top_iff.mp hs)
      exact sub_eq_zero.mp hEq.eq_of_nhds
    · exact h
  have ha : AnalyticAt ℂ (fun z => regularPart L (u z) - (E.b₂ : ℂ) / 12) (τ : ℂ) := by
    apply AnalyticAt.sub _ analyticAt_const
    have hh : AnalyticAt ℂ (regularPart L) (u τ) := hu0.symm ▸ L.analyticAt_weierstrassPExcept 0
    exact hh.comp (hu _ τ.im_pos)
  have hEq : (fun z => u z ^ 2 * G z) =ᶠ[𝓝[≠] (τ : ℂ)]
      (fun z => 1 + u z ^ 2 * (regularPart L (u z) - (E.b₂ : ℂ) / 12)) := by
    filter_upwards [he, hu_ne] with z hz hne
    have hj : scaledPrimitive f κ z = u z + l := (sub_add_cancel _ _).symm
    have hp : L.weierstrassP (scaledPrimitive f κ z) = L.weierstrassP (u z) := by
      rw [hj, L.weierstrassP_add_coe _ ⟨l, hτ⟩]
    rw [hz, xCoordinate, hp, weierstrassP_split]
    have hne' : u z ^ 2 ≠ 0 := pow_ne_zero _ hne
    field_simp
    ring
  have h₁ : ContinuousAt (fun z => u z ^ 2 * G z) (τ : ℂ) :=
    ((hu _ τ.im_pos).continuousAt.pow 2).mul hG.continuousAt
  have h₂ : ContinuousAt
      (fun z => 1 + u z ^ 2 * (regularPart L (u z) - (E.b₂ : ℂ) / 12)) (τ : ℂ) :=
    continuousAt_const.add (((hu _ τ.im_pos).continuousAt.pow 2).mul ha.continuousAt)
  have h := ((ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE h₁ h₂).mp hEq).eq_of_nhds
  exact zero_ne_one (by simpa only [hu0, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, add_zero] using h)


end ZInQ.Manuscript.RC.ModFnClassify
