import ZInQKernel.Contrib.OneProof.RC.ModFnField.Equation

/-! From a complex converse theorem to the exact rational coordinate
statement at tex 1785–1787 and 2836–2838 (on-the-spot, provenance (c)). -/

noncomputable section

open Filter UpperHalfPlane Matrix
open scoped MatrixGroups
open ModularCurve ZInQ.Contrib.CloudB3RC53.CST
open ZInQ.Manuscript.RC.ParamAtScale

namespace ZInQ.Manuscript.RC.ModFnField

/-- The complex converse, stated for a meromorphic level function and its
convergent Laurent series at infinity. There are no rationality or curve
conditions in this statement. -/
def ComplexCuspClassification (N : ℕ) [NeZero N] : Prop :=
  ∀ (g : ℂ → ℂ) (s : LaurentSeries ℂ),
    MeromorphicOn g {z : ℂ | 0 < z.im} →
    (∀ σ : SL(2, ℤ), σ ∈ CongruenceSubgroup.Gamma0 N →
      ∀ τ : ℍ, g (σ • τ : ℍ) = g τ) →
    (∀ σ : SL(2, ℤ), ∃ (G : ℂ → ℂ) (T : ℝ), MeromorphicAt G 0 ∧
      ∀ τ : ℍ, T < τ.im →
        G (Function.Periodic.qParam (translatedLevel N σ).strictWidthInfty τ) = g (σ • τ : ℍ)) →
    (∃ T : ℝ, ∀ τ : ℍ, T < τ.im →
      HasSum (fun m : ℤ => s.coeff m * Function.Periodic.qParam 1 τ ^ m) (g τ)) →
    s ∈ modularFunctionFieldC ℂ N

/-- The width-one exponential monomial in the at-scale interface. -/
private theorem qParam_zpow_widthOne (z : ℂ) (n : ℤ) :
    Function.Periodic.qParam 1 z ^ n =
      Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * z) := by
  rw [Function.Periodic.qParam, Complex.ofReal_one, div_one, ← Complex.exp_int_mul]
  congr 1
  ring

/-- The complex converse gives rational field coordinates with the prescribed
tail, affine equation and leading coefficient. -/
theorem coordinates_in_modularFunctionField_with_equation (E : WeierstrassCurve ℚ)
    {N : ℕ} [NeZero N]
    (hclass : ComplexCuspClassification N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    {L : PeriodPair} (hL : IsLatticeOf E L) {κ : ℚ} (hκ : IsParamScale N f L (κ : ℂ)) :
    ∃ (x y : modularFunctionField N),
      (((x : LaurentSeries ℚ).coeff (-2) : ℚ) : ℂ) = (κ : ℂ)⁻¹ ^ 2 ∧
      Realizes (complexify x) (fun τ => xCoordinate E f L κ τ) ∧
      Realizes (complexify y) (fun τ => yCoordinate E f L κ τ) ∧
      (E.baseChange (LaurentSeries ℚ)).toAffine.Equation x y := by
  have hk : κ ≠ 0 := by
    intro hk
    exact hκ.1 (by simp [hk])
  obtain ⟨x, y, T, _, _, hxlead, htail⟩ := coordinates_rationalLaurent E f hf hL hk
  obtain ⟨hx, hy⟩ := coordinates_meromorphic E f L κ
  have hxm : x ∈ modularFunctionField N := by
    apply modularFunctionField_descent N
    refine hclass _ _ hx (fun σ hσ τ => (coordinates_smul E hκ hσ τ).1) ?_ ?_
    · intro σ
      obtain ⟨_, X, _, hX, _, hval⟩ := coordinates_cusp_meromorphic E f L κ σ
      exact ⟨X, 0, hX, fun τ _ => (hval τ).1⟩
    · exact ⟨T, fun τ hτ => (htail τ hτ).1⟩
  have hym : y ∈ modularFunctionField N := by
    apply modularFunctionField_descent N
    refine hclass _ _ hy (fun σ hσ τ => (coordinates_smul E hκ hσ τ).2) ?_ ?_
    · intro σ
      obtain ⟨_, _, Y, _, hY, hval⟩ := coordinates_cusp_meromorphic E f L κ σ
      exact ⟨Y, 0, hY, fun τ _ => (hval τ).2⟩
    · exact ⟨T, fun τ hτ => (htail τ hτ).2⟩
  have htail' : ∀ᶠ τ : ℍ in atImInfty, T < τ.im :=
    (atImInfty_mem _).mpr ⟨T + 1, fun τ hτ => lt_of_lt_of_le (by linarith) hτ⟩
  have hx' : Realizes (complexify x) (fun τ => xCoordinate E f L κ τ) :=
    htail'.mono fun τ hτ => (htail τ hτ).1
  have hy' : Realizes (complexify y) (fun τ => yCoordinate E f L κ τ) :=
    htail'.mono fun τ hτ => (htail τ hτ).2
  exact ⟨⟨x, hxm⟩, ⟨y, hym⟩, hxlead, hx', hy', coordinates_laurent_equation E f hf hL hk hx' hy'⟩

/-- The complex converse suffices for the exact at-scale coordinate
proposition. Rationality and the analytic cusp hypotheses are supplied by
the preceding theorems. -/
theorem coordinates_in_modularFunctionField (E : WeierstrassCurve ℚ) {N : ℕ} [NeZero N]
    (hclass : ComplexCuspClassification N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    {L : PeriodPair} (hL : IsLatticeOf E L) {κ : ℚ} (hκ : IsParamScale N f L (κ : ℂ)) :
    ∃ (x y : modularFunctionField N) (T : ℝ), ∀ τ : ℍ, T < τ.im →
      HasSum (fun m : ℤ => (((x : LaurentSeries ℚ).coeff m : ℚ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (τ : ℂ))) (xCoordinate E f L κ τ) ∧
      HasSum (fun m : ℤ => (((y : LaurentSeries ℚ).coeff m : ℚ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (τ : ℂ))) (yCoordinate E f L κ τ) := by
  obtain ⟨x, y, _, hx, hy, _⟩ := coordinates_in_modularFunctionField_with_equation E hclass f hf hL hκ
  obtain ⟨T, hT⟩ := (atImInfty_mem _).mp (hx.and hy)
  exact ⟨x, y, T, fun τ hτ => by
    simpa only [Set.mem_ofPred_eq, complexify_coeff, qParam_zpow_widthOne] using hT τ hτ.le⟩

#print axioms qParam_zpow_widthOne
#print axioms coordinates_in_modularFunctionField_with_equation
#print axioms coordinates_in_modularFunctionField

end ZInQ.Manuscript.RC.ModFnField
