import ZInQKernel.Contrib.OneProof.RC.PreparedParam.Parametrization
import Mathlib.Analysis.Meromorphic.Order
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Cusps.Basic

/-! The analytic coordinates in the based comparison of tex 1785–1787.
The meromorphic calculation and section comparison are on-the-spot (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassCurve Complex UpperHalfPlane Filter Topology
open ZInQ.Contrib.CloudB3RC53.CST

namespace ZInQ.Manuscript.RC.ParamAtScale

open PreparedParam

/-- The complex primitive at the given scale, read on `ℂ` through the chart. -/
def scaledPrimitive (f : UpperHalfPlane → ℂ) (κ : ℂ) (z : ℂ) : ℂ :=
  κ * eichlerPotential f (ofComplex z)

/-- The meromorphic affine x-coordinate. At lattice values the scheme point
uses the chart at infinity instead. -/
def xCoordinate (E : WeierstrassCurve ℚ) (f : UpperHalfPlane → ℂ) (Lat : PeriodPair)
    (κ : ℂ) (z : ℂ) : ℂ :=
  Lat.weierstrassP (scaledPrimitive f κ z) - (E.b₂ : ℂ) / 12

/-- The meromorphic affine y-coordinate, in the original Weierstrass model. -/
def yCoordinate (E : WeierstrassCurve ℚ) (f : UpperHalfPlane → ℂ) (Lat : PeriodPair)
    (κ : ℂ) (z : ℂ) : ℂ :=
  (Lat.derivWeierstrassP (scaledPrimitive f κ z) -
    (E.a₁ : ℂ) * xCoordinate E f Lat κ z - (E.a₃ : ℂ)) / 2

/-- The scaled Eichler primitive is holomorphic on the upper half plane. -/
theorem scaledPrimitive_analytic {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (κ : ℂ) {z : ℂ} (hz : 0 < z.im) : AnalyticAt ℂ (scaledPrimitive f κ) z := by
  have hΓ := TauCeti.one_mem_strictPeriods_Gamma0_map N
  have hE := TauCeti.mdifferentiable_eichlerIntegral (by norm_num : (0 : ℝ) < 1)
    (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) 1
  have hd := UpperHalfPlane.mdifferentiable_iff.mp hE
  exact analyticAt_const.mul (hd.analyticAt (isOpen_upperHalfPlaneSet.mem_nhds hz))

/-- The scaled primitive has rational Taylor coefficients at the width-one cusp
when the form has the elliptic Dirichlet coefficients and the scale is rational. -/
theorem rational_primitive_hasSum (E : WeierstrassCurve ℚ) {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    (κ : ℚ) (τ : UpperHalfPlane) :
    HasSum (fun n : ℕ =>
      (((κ * (E.LFunction n : ℚ) / (n : ℚ) : ℚ) : ℂ)) *
        Function.Periodic.qParam 1 (τ : ℂ) ^ n)
      (scaledPrimitive f κ (τ : ℂ)) := by
  have hΓ := TauCeti.one_mem_strictPeriods_Gamma0_map N
  have h := (TauCeti.hasSum_eichlerIntegral (by norm_num : (0 : ℝ) < 1)
    (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) 1 τ).mul_left (κ : ℂ)
  change HasSum _ ((κ : ℂ) * eichlerPotential f (ofComplex (τ : ℂ)))
  rw [ofComplex_apply]
  convert h using 1 <;> try rfl
  funext n
  by_cases hn : n = 0
  · subst n
    simp
  · rw [hf n (Nat.pos_of_ne_zero hn)]
    push_cast
    simp only [pow_one]
    ring

/-- The analytic coordinates are meromorphic on the whole upper half plane. -/
theorem coordinates_meromorphic (E : WeierstrassCurve ℚ) {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (Lat : PeriodPair) (κ : ℂ) :
    MeromorphicOn (xCoordinate E f Lat κ) {z : ℂ | 0 < z.im} ∧
      MeromorphicOn (yCoordinate E f Lat κ) {z : ℂ | 0 < z.im} := by
  have hx : MeromorphicOn (xCoordinate E f Lat κ) {z : ℂ | 0 < z.im} := by
    intro z hz
    exact ((Lat.meromorphic_weierstrassP _).comp_analyticAt
      (scaledPrimitive_analytic f κ hz)).sub (MeromorphicAt.const _ _)
  refine ⟨hx, fun z hz => ?_⟩
  have hy := (Lat.meromorphic_derivWeierstrassP (scaledPrimitive f κ z)).comp_analyticAt
    (scaledPrimitive_analytic f κ hz)
  exact ((hy.sub ((MeromorphicAt.const (E.a₁ : ℂ) z).mul (hx z hz))).sub
    (MeromorphicAt.const _ _)).div (MeromorphicAt.const _ _)

/-- The analytic coordinates satisfy the equation of the specified rational
model after extension to `ℂ`, away from the lattice points of the primitive. -/
theorem coordinates_equation (E : WeierstrassCurve ℚ)
    (f : UpperHalfPlane → ℂ) {Lat : PeriodPair} (hLat : IsLatticeOf E Lat)
    (κ : ℂ) {z : ℂ} (hz : scaledPrimitive f κ z ∉ Lat.lattice) :
    (E.baseChange ℂ).toAffine.Equation (xCoordinate E f Lat κ z) (yCoordinate E f Lat κ z) := by
  have h := Lat.derivWeierstrassP_sq (scaledPrimitive f κ z) hz
  rw [hLat.1, hLat.2] at h
  rw [Affine.equation_iff']
  simp only [baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, eq_ratCast, xCoordinate, yCoordinate]
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.c₆, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆] at h ⊢
  push_cast at h ⊢
  linear_combination h / 4

/-- At the fixed scale the two coordinate functions are invariant under the level group. -/
theorem coordinates_smul (E : WeierstrassCurve ℚ) {N : ℕ}
    {f : UpperHalfPlane → ℂ} {Lat : PeriodPair} {κ : ℂ}
    (hκ : IsParamScale N f Lat κ) {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (τ : UpperHalfPlane) :
    xCoordinate E f Lat κ (γ • τ : UpperHalfPlane) = xCoordinate E f Lat κ τ ∧
      yCoordinate E f Lat κ (γ • τ : UpperHalfPlane) = yCoordinate E f Lat κ τ := by
  have hl : scaledPrimitive f κ (γ • τ : UpperHalfPlane) - scaledPrimitive f κ τ ∈ Lat.lattice := by
    simpa only [scaledPrimitive, ofComplex_apply, ← mul_sub] using hκ.2 γ hγ τ
  have hs : scaledPrimitive f κ (γ • τ : UpperHalfPlane) =
      scaledPrimitive f κ τ + (scaledPrimitive f κ (γ • τ : UpperHalfPlane) -
        scaledPrimitive f κ τ) := by ring
  have hx : xCoordinate E f Lat κ (γ • τ : UpperHalfPlane) = xCoordinate E f Lat κ τ := by
    unfold xCoordinate
    rw [hs, Lat.weierstrassP_add_coe _ ⟨_, hl⟩]
  refine ⟨hx, ?_⟩
  unfold yCoordinate
  rw [hx, hs, Lat.derivWeierstrassP_add_coe _ ⟨_, hl⟩]

/-- A regular section and any meromorphic realization of its exact Laurent
coefficients have the same punctured germ at every chart point. -/
theorem section_meromorphic_germ {N : ℕ} [NeZero N] (X : X0Model N)
    (U : X.X.Opens) [Nonempty U] (a : Γ(X.X, U))
    {g : ℂ → ℂ} (hg : MeromorphicOn g {z : ℂ | 0 < z.im}) (T : ℝ)
    (hseries : letI := X.integral; ∀ τ : UpperHalfPlane, T < τ.im →
      HasSum (fun n : ℤ =>
        (((X.functionField (X.X.germToFunctionField U a) : LaurentSeries ℚ).coeff n : ℚ) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (τ : ℂ))) (g τ))
    (τ : UpperHalfPlane) (hτ : (X.complexPoint τ).val default ∈ U) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G (τ : ℂ) ∧
      (X.complexPoint τ).evalSection U hτ a = G τ ∧ G =ᶠ[𝓝[≠] (τ : ℂ)] g := by
  let := X.integral
  obtain ⟨G, S, hm, hS, hval⟩ := X.sectionExpansion U a
  let z₀ : ℂ := ⟨0, max (max S T) 0 + 1⟩
  have hz : max (max S T) 0 < z₀.im := by dsimp [z₀]; linarith
  have hdom : ∀ᶠ z : ℂ in 𝓝[≠] z₀, max (max S T) 0 < z.im :=
    nhdsWithin_le_nhds (isOpen_lt continuous_const Complex.continuous_im |>.mem_nhds hz)
  have hD : MeromorphicOn (fun z => G z - g z) {z : ℂ | 0 < z.im} :=
    fun z hz => (hm z hz).sub (hg z hz)
  have htop : meromorphicOrderAt (fun z => G z - g z) z₀ = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [hdom] with z hz
    have hpos : 0 < z.im := lt_of_le_of_lt (le_max_right _ _) hz
    have hS' : S < z.im := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hz
    have hT' : T < z.im := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hz
    exact sub_eq_zero.mpr ((hS ⟨z, hpos⟩ hS').unique (hseries ⟨z, hpos⟩ hT'))
  have htopτ := hD.meromorphicOrderAt_eq_top_of_isPreconnected
    (convex_halfSpace_im_gt 0).isPreconnected
    (show 0 < z₀.im from lt_of_le_of_lt (le_max_right _ _) hz) τ.im_pos htop
  have heq : G =ᶠ[𝓝[≠] (τ : ℂ)] g := by
    rw [meromorphicOrderAt_eq_top_iff] at htopτ
    filter_upwards [htopτ] with z hz using sub_eq_zero.mp hz
  exact ⟨G, (hval τ hτ).1, (hval τ hτ).2, heq⟩

#print axioms scaledPrimitive_analytic
#print axioms rational_primitive_hasSum
#print axioms coordinates_meromorphic
#print axioms coordinates_equation
#print axioms coordinates_smul
#print axioms section_meromorphic_germ

end ZInQ.Manuscript.RC.ParamAtScale
