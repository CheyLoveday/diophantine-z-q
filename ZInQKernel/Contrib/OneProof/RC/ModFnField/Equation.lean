import ZInQKernel.Contrib.OneProof.RC.ModFnField.RationalExpansion
import ZInQKernel.Contrib.OneProof.RC.ModFnField.Descent
import ZInQKernel.Contrib.OneProof.RC.ModFnField.Tail

/-! Passing the analytic Weierstrass equation to the formal Laurent field.
On-the-spot (c) for tex 1785–1787. -/

noncomputable section

open Filter Topology Function UpperHalfPlane WeierstrassCurve
open ZInQ.Contrib.CloudB3RC53.CST
open ZInQ.Manuscript.RC.ParamAtScale

namespace ZInQ.Manuscript.RC.ModFnField

/-- The complex Laurent series evaluates to the function on a tail at infinity. -/
def Realizes (a : LaurentSeries ℂ) (g : ℍ → ℂ) : Prop :=
  ∀ᶠ τ : ℍ in atImInfty, HasSum (fun m : ℤ => a.coeff m * Periodic.qParam 1 τ ^ m) (g τ)

namespace Realizes

theorem const (c : ℂ) :
    Realizes (algebraMap ℂ (LaurentSeries ℂ) c) (fun _ => c) := by
  filter_upwards with τ
  rw [HahnSeries.algebraMap_apply', show algebraMap ℂ (PowerSeries ℂ) c = PowerSeries.C c by simp,
    HahnSeries.ofPowerSeries_C]
  exact (hasSum_ite_eq 0 c).congr_fun fun m => by by_cases hm : m = 0 <;> simp [hm]

theorem add {a b : LaurentSeries ℂ} {g k : ℍ → ℂ} (ha : Realizes a g) (hb : Realizes b k) :
    Realizes (a + b) (fun τ => g τ + k τ) := by
  filter_upwards [ha, hb] with τ h₁ h₂
  exact (h₁.add h₂).congr_fun fun m => by simp only [HahnSeries.coeff_add, add_mul]

theorem mul {a b : LaurentSeries ℂ} {g k : ℍ → ℂ} (ha : Realizes a g) (hb : Realizes b k) :
    Realizes (a * b) (fun τ => g τ * k τ) := by
  obtain ⟨T, hT⟩ := (atImInfty_mem _).mp (ha.and hb)
  exact (atImInfty_mem _).mpr ⟨max T 0 + 1, fun τ hτ =>
    hasSum_mul_of_tail (fun ζ hz => (hT ζ hz.le).1) (fun ζ hz => (hT ζ hz.le).2) τ
      (lt_of_lt_of_le (by linarith) hτ)⟩

theorem pow {a : LaurentSeries ℂ} {g : ℍ → ℂ} (ha : Realizes a g) (n : ℕ) :
    Realizes (a ^ n) (fun τ => g τ ^ n) := by
  induction n with
  | zero => simpa using const 1
  | succ n ih => simpa only [pow_succ] using ih.mul ha

theorem eq_of_eventuallyEq {a b : LaurentSeries ℂ} {g k : ℍ → ℂ}
    (ha : Realizes a g) (hb : Realizes b k) (hg : g =ᶠ[atImInfty] k) : a = b := by
  obtain ⟨T, hT⟩ := (atImInfty_mem _).mp (ha.and (hb.and hg))
  exact laurent_unique_of_tail (g := g) (T := T) (fun τ hτ => (hT τ hτ.le).1)
    (fun τ hτ => ((hT τ hτ.le).2.2).symm ▸ (hT τ hτ.le).2.1)

end Realizes

private theorem scaledPrimitive_off_lattice_on_tail (E : WeierstrassCurve ℚ)
    {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    (L : PeriodPair) {κ : ℚ} (hκ : κ ≠ 0) :
    ∀ᶠ τ : ℍ in atImInfty, scaledPrimitive f κ τ ∉ L.lattice := by
  obtain ⟨F, hF, hr, hF0, hF1, hval⟩ := primitive_rationalTaylor E f hf κ
  obtain ⟨u, hu, _, hu0, he⟩ := hr.factor_at_zero hF hF0
  have hne : u 0 ≠ 0 := by
    rw [hu0, hF1]
    exact_mod_cast hκ
  have htu := hu.continuousAt (isOpen_ne.mem_nhds hne)
  have ht : Tendsto (fun τ : ℍ => Periodic.qParam 1 τ) atImInfty (𝓝 0) :=
    qParam_tendsto_atImInfty zero_lt_one
  have htF : Tendsto F (𝓝 0) (𝓝 0) := by
    nth_rw 2 [← hF0]
    exact hF.continuousAt.tendsto
  filter_upwards [ht.eventually (he.and htu),
    (htF.comp ht).eventually (L.compl_lattice_sdiff_singleton_mem_nhds (0 : ℂ))] with τ h₁ h₂
  simp only [Function.comp_apply] at h₂
  rw [← hval τ]
  exact fun hmem => h₂ ⟨hmem, by
    rw [Set.mem_singleton_iff, h₁.1]
    exact mul_ne_zero (Periodic.qParam_ne_zero _) h₁.2⟩

/-- Any rational Laurent series realizing these coordinates satisfies the
affine equation over the rational Laurent series field. -/
theorem coordinates_laurent_equation (E : WeierstrassCurve ℚ) {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    {L : PeriodPair} (hL : IsLatticeOf E L) {κ : ℚ} (hκ : κ ≠ 0)
    {x y : LaurentSeries ℚ}
    (hx : Realizes (complexify x) (fun τ => xCoordinate E f L κ τ))
    (hy : Realizes (complexify y) (fun τ => yCoordinate E f L κ τ)) :
    (E.baseChange (LaurentSeries ℚ)).toAffine.Equation x y := by
  let C := algebraMap ℂ (LaurentSeries ℂ)
  have hleft := ((hy.pow 2).add (((Realizes.const (E.a₁ : ℂ)).mul hx).mul hy)).add
    ((Realizes.const (E.a₃ : ℂ)).mul hy)
  have hright := ((((hx.pow 3).add ((Realizes.const (E.a₂ : ℂ)).mul (hx.pow 2))).add
    ((Realizes.const (E.a₄ : ℂ)).mul hx))).add (Realizes.const (E.a₆ : ℂ))
  have heq := hleft.eq_of_eventuallyEq hright (by
    filter_upwards [scaledPrimitive_off_lattice_on_tail E f hf L hκ] with τ hτ
    simpa only [baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, eq_ratCast]
      using (Affine.equation_iff _ _).mp (coordinates_equation E f hL κ hτ))
  apply (Affine.equation_iff _ _).mpr
  apply complexify.injective
  simp only [baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, map_add, map_mul, map_pow]
  have hc (c : ℚ) : complexify (algebraMap ℚ (LaurentSeries ℚ) c) = C (c : ℂ) :=
    DFunLike.congr_fun (Subsingleton.elim (complexify.comp (algebraMap ℚ (LaurentSeries ℚ)))
      (C.comp (Rat.castHom ℂ))) c
  simp only [hc]
  exact heq


end ZInQ.Manuscript.RC.ModFnField
