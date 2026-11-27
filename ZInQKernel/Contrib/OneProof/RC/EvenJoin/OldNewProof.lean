import ZInQKernel.Contrib.OneProof.RC.EvenJoin.DistinctCuspColumns
import ZInQKernel.Contrib.TauCeti.Backport.NumberTheory.ModularForms.Newforms.StrongMultiplicityOne.Across

/-! Independence of the old columns in the characteristic-zero inventory
(tex 9649–9654 and 9754–9764). -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenJoin

open CongruenceSubgroup HeckeRing.GL2 Matrix.SpecialLinearGroup ModularForm TauCeti UpperHalfPlane
open scoped MatrixGroups

private abbrev GoodPrime (N : ℕ) := {p : ℕ // p.Prime ∧ p.Coprime N}

private def columnOperator {N : ℕ} [NeZero N] :
    (ZMod N)ˣ ⊕ GoodPrime N → Module.End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) 2)
  | .inl u => diamondOpCusp 2 u
  | .inr p => heckeTCuspNat 2 p.val (_hn := ⟨p.property.1.ne_zero⟩)

private def columnEigenvalues {N : ℕ} (x : CuspDilation N) :
    (ZMod N)ˣ ⊕ GoodPrime N → ℂ
  | .inl u => x.char u
  | .inr p =>
    letI : NeZero x.source.level := ⟨x.source.level_ne⟩
    x.source.newform.eigenvalue ⟨p.val, p.property.1.pos⟩
      (p.property.2.coprime_dvd_right x.source_dvd)

private theorem columnOperator_apply {N : ℕ} [NeZero N] (x : CuspDilation N) (j) :
    columnOperator j x.form = columnEigenvalues x j • x.form := by
  let : NeZero x.source.level := ⟨x.source.level_ne⟩
  let : NeZero x.degree := NeZero.of_dvd (dvd_of_mul_right_dvd x.divides)
  cases j with
  | inl u =>
    exact diamondOpCusp_apply_of_mem_cuspFormCharSpace 2 x.char u
      (CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd x.divides _
        x.source.newform.mem_charSpace)
  | inr p =>
    exact x.source.newform.toEigenformAwayFromLevel.heckeTCuspNat_levelRaise_eq_eigenvalue_smul
      x.divides p.property.1 p.property.2

private theorem source_eq_of_eigenvalues_eq {N : ℕ} [NeZero N] {x y : CuspDilation N}
    (h : columnEigenvalues x = columnEigenvalues y) : x.source = y.source := by
  let : NeZero x.source.level := ⟨x.source.level_ne⟩
  let : NeZero y.source.level := ⟨y.source.level_ne⟩
  have hχ : x.char = y.char :=
    MonoidHom.ext fun u => Units.ext (congrFun h (Sum.inl u))
  have he := Newform.level_eq_and_coe_eq_of_comp_unitsMap_eq
    x.source.newform y.source.newform x.source_dvd y.source_dvd rfl hχ.symm
    (S := ∅) fun p hp hpN _ => congrFun h (Sum.inr ⟨p, hp, hpN⟩)
  rcases x with ⟨⟨L, hL, f⟩, d, hd⟩
  rcases y with ⟨⟨M, hM, g⟩, e, he'⟩
  obtain ⟨hLM, hfg⟩ := he
  change L = M at hLM
  subst M
  have : f = g := Newform.ext (CuspForm.ext (congrFun hfg))
  subst g
  rfl

private theorem column_degree_pos {N : ℕ} [NeZero N] (x : CuspDilation N) :
    0 < x.degree :=
  (NeZero.of_dvd (dvd_of_mul_right_dvd x.divides)).pos _

private theorem column_coeff_degree {N : ℕ} [NeZero N] (x : CuspDilation N) :
    x.coeff x.degree = 1 := by
  let : NeZero x.source.level := ⟨x.source.level_ne⟩
  have h : x.source.coeff 1 = 1 := x.source.newform.isNorm
  simpa only [CuspDilation.coeff, Nat.mul_one] using
    (Odd.divCoeff_mul_left x.source.coeff (column_degree_pos x) 1).trans h

/-- In a nonzero relation within one joint eigenspace, the least degree
with nonzero scalar contributes the only term at that Fourier index. -/
private theorem independent_eigenvalue_fiber {N : ℕ} [NeZero N]
    (a : (ZMod N)ˣ ⊕ GoodPrime N → ℂ) :
    LinearIndependent ℂ (fun x : {x : CuspDilation N // columnEigenvalues x = a} =>
      x.val.form) := by
  classical
  rw [linearIndependent_iff']
  intro s c h x hx
  by_contra hcx
  let t := s.filter fun y => c y ≠ 0
  let degrees := t.image fun y => y.val.degree
  have hne : degrees.Nonempty :=
    ⟨x.val.degree, Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hcx⟩, rfl⟩⟩
  obtain ⟨y, hyt, hymin⟩ := Finset.mem_image.mp (Finset.min'_mem degrees hne)
  have ⟨hys, hcy⟩ := Finset.mem_filter.mp hyt
  let Q : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2 →ₗ[ℂ] ℂ :=
    CuspForm.qExpansionCoeffₗ one_pos (one_mem_strictPeriods_Gamma1_map _) 2 y.val.degree
  have hz := congrArg Q h
  simp only [map_sum, map_smul, map_zero, Q, CuspForm.qExpansionCoeffₗ_apply,
    CuspDilation.coeff_form, smul_eq_mul] at hz
  rw [Finset.sum_eq_single y, column_coeff_degree, mul_one] at hz
  · exact hcy hz
  · intro z hzs hzy
    by_cases hcz : c z = 0
    · simp [hcz]
    have hle : y.val.degree ≤ z.val.degree := by
      rw [hymin]
      exact Finset.min'_le degrees _
        (Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨hzs, hcz⟩, rfl⟩)
    have hlt : y.val.degree < z.val.degree := lt_of_le_of_ne hle fun hd => by
      apply hzy
      apply Subtype.ext
      have hs := source_eq_of_eigenvalues_eq (z.property.trans y.property.symm)
      rcases z with ⟨⟨sz, dz, hz⟩, _⟩
      rcases y with ⟨⟨sy, dy, hy⟩, _⟩
      change sz = sy at hs
      change dy = dz at hd
      cases hs
      cases hd
      rfl
    rw [CuspDilation.coeff, Odd.divCoeff_of_not_dvd _
      (fun hd => (not_le_of_gt hlt) (Nat.le_of_dvd (column_degree_pos y.val) hd)), mul_zero]
  · exact fun hy => (hy hys).elim

set_option maxHeartbeats 800000 in
/-- All distinct dilations of normalized cuspidal newforms are independent
at the ambient level. -/
theorem oldNewIndependenceWeightTwo_proved : OldNewIndependenceWeightTwo := by
  intro N hN
  let E (a : (ZMod N)ˣ ⊕ GoodPrime N → ℂ) :=
    ⨅ j, (columnOperator j).eigenspace (a j)
  have hE : iSupIndep E := iSupIndep_iInf_eigenspace columnOperator
  let columns (a : (ZMod N)ˣ ⊕ GoodPrime N → ℂ)
      (x : {x : CuspDilation N // columnEigenvalues x = a}) := x.val.form
  have hspan (a) : Submodule.span ℂ (Set.range (columns a)) ≤ E a := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    apply (Submodule.mem_iInf _).mpr
    intro j
    exact Module.End.mem_eigenspace_iff.mpr
      ((columnOperator_apply x.val j).trans
        (congrArg (fun c : ℂ => c • x.val.form) (congrFun x.property j)))
  have hdisjoint (a) (t : Set ((ZMod N)ˣ ⊕ GoodPrime N → ℂ)) (hat : a ∉ t) :
      Disjoint (Submodule.span ℂ (Set.range (columns a)))
        (⨆ b ∈ t, Submodule.span ℂ (Set.range (columns b))) := by
    refine (iSupIndep_def.mp hE a).mono (hspan a) (iSup₂_le fun b hb => ?_)
    have hba : b ≠ a := fun he => hat (he ▸ hb)
    exact (hspan b).trans (le_iSup_of_le b (le_iSup_of_le hba le_rfl))
  have h := linearIndependent_iUnion_finite (f := columns)
    independent_eigenvalue_fiber (fun a t _ hat => hdisjoint a t hat)
  exact h.comp (fun x : CuspDilation N => ⟨columnEigenvalues x, x, rfl⟩)
    (fun _ _ he => congrArg (fun x => x.2.val) he)

/-- The dilation label is determined by its actual ambient cusp form. -/
theorem cuspDilation_form_injective {N : ℕ} [NeZero N] :
    Function.Injective (fun x : CuspDilation N => x.form) :=
  (oldNewIndependenceWeightTwo_proved N).injective

theorem cuspDilation_coeff_independent_proved {N : ℕ} [NeZero N] :
    LinearIndependent ℂ (CuspDilation.coeff (N := N)) :=
  cuspDilation_coeff_independent oldNewIndependenceWeightTwo_proved

end ZInQ.Manuscript.RC.EvenJoin
