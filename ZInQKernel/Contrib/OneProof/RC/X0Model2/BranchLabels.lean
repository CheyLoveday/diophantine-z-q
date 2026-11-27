import ZInQKernel.Contrib.OneProof.RC.X0Model2.JOrbit
import ZInQKernel.Contrib.OneProof.RC.X0Model2.ChartReparam
import Mathlib.Algebra.AlgebraicCard
import Mathlib.Topology.Algebra.Module.Cardinality

/-! Distinguishing the labels of the local modular sheets (tex 2915–2919,
on the spot, provenance (c)). -/

noncomputable section

open Filter ModularCurve
open scoped Topology MatrixGroups Polynomial

namespace ZInQ.Manuscript.RC.X0Model2

private theorem scaled_moebius_lowerLeft (N : ℕ) [NeZero N]
    (γ δ : SL(2, ℤ)) (τ : UpperHalfPlane) (ht : Transcendental ℚ (τ : ℂ))
    (h : X0Model.dilate N (γ • τ) = δ • X0Model.dilate N τ) :
    γ ∈ CongruenceSubgroup.Gamma0 N := by
  let a := γ 0 0
  let b := γ 0 1
  let c := γ 1 0
  let d := γ 1 1
  let A := δ 0 0
  let B := δ 0 1
  let C := δ 1 0
  let D := δ 1 1
  let n : ℤ := N
  let x : ℂ := τ
  have hd : A * D - B * C = 1 := by
    have hm := δ.property
    rwa [Matrix.det_fin_two] at hm
  have he := congrArg UpperHalfPlane.coe h
  change (n : ℂ) * ((γ • τ : UpperHalfPlane) : ℂ) =
    ((δ • X0Model.dilate N τ : UpperHalfPlane) : ℂ) at he
  rw [UpperHalfPlane.coe_specialLinearGroup_apply, UpperHalfPlane.coe_specialLinearGroup_apply] at he
  change (n : ℂ) * (((a : ℂ) * x + b) / ((c : ℂ) * x + d)) =
    ((A : ℂ) * ((n : ℂ) * x) + B) / ((C : ℂ) * ((n : ℂ) * x) + D) at he
  have hden₁ : (c : ℂ) * x + d ≠ 0 :=
    UpperHalfPlane.denom_ne_zero (γ : GL (Fin 2) ℝ) τ
  have hden₂ : (C : ℂ) * ((n : ℂ) * x) + D ≠ 0 :=
    UpperHalfPlane.denom_ne_zero (δ : GL (Fin 2) ℝ) (X0Model.dilate N τ)
  rw [← mul_div_assoc, div_eq_div_iff hden₁ hden₂] at he
  -- These are the entries of δ⁻¹ times the integer matrix with rows (na, nb), (c, d).
  let u := D * n * a - B * c
  let v := D * n * b - B * d
  let s := A * c - C * n * a
  let t := A * d - C * n * b
  let p : ℚ[X] :=
    Polynomial.C (↑(-n * s) : ℚ) * Polynomial.X ^ 2 +
      Polynomial.C (↑(u - n * t) : ℚ) * Polynomial.X + Polynomial.C (v : ℚ)
  have hp : p = 0 := by
    apply (transcendental_iff.mp ht) p
    dsimp only [p]
    simp only [map_add, map_mul, map_pow, Polynomial.aeval_X, map_intCast]
    dsimp only [u, v, s, t]
    push_cast
    linear_combination he
  have hp₂ := congrArg (fun f : ℚ[X] => f.coeff 2) hp
  have hp₁ := congrArg (fun f : ℚ[X] => f.coeff 1) hp
  have hs' : (-n : ℤ) * s = 0 := by
    have hc : ((↑(-n * s) : ℚ)) = 0 := by
      norm_num only [p, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
        Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_zero, ite_true,
        ite_false, add_zero] at hp₂
      exact hp₂
    exact_mod_cast hc
  have hn : n ≠ 0 := by
    change (N : ℤ) ≠ 0
    exact_mod_cast (NeZero.ne N)
  have hs : s = 0 := (mul_eq_zero.mp hs').resolve_left (neg_ne_zero.mpr hn)
  have hu : u - n * t = 0 := by
    have hc : ((↑(u - n * t) : ℚ)) = 0 := by
      norm_num only [p, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
        Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_zero, ite_true,
        ite_false, add_zero, zero_add] at hp₁
      exact hp₁
    exact_mod_cast hc
  have hc : c = C * u + D * s := by
    dsimp only [u, s]
    linear_combination -c * hd
  rw [hs, mul_zero, add_zero, sub_eq_zero.mp hu] at hc
  apply CongruenceSubgroup.Gamma0_mem.mpr
  apply (CharP.intCast_eq_zero_iff (ZMod N) N (γ 1 0)).mpr
  refine ⟨C * t, ?_⟩
  change c = n * (C * t)
  rw [hc]
  ring

/-- A transcendental parameter separates the labels before specializing to a
point of the plane modular equation. -/
theorem gamma0_of_analyticJN_eq_at_transcendental (N : ℕ) [NeZero N]
    (γ : SL(2, ℤ)) (τ : UpperHalfPlane) (ht : Transcendental ℚ (τ : ℂ))
    (h : X0Model.analyticJN N (γ • τ) = X0Model.analyticJN N τ) :
    γ ∈ CongruenceSubgroup.Gamma0 N := by
  obtain ⟨δ, hδ⟩ := (analyticJ_eq_iff _ _).mp h.symm
  exact scaled_moebius_lowerLeft N γ δ τ ht hδ.symm

private theorem frequently_transcendental (z : ℂ) :
    ∃ᶠ w in 𝓝[≠] z, Transcendental ℚ w := by
  have hd := ((Algebraic.countable ℚ ℂ).union (Set.countable_singleton z)).dense_compl ℂ
  rw [frequently_nhdsWithin_iff]
  exact (mem_closure_iff_frequently.mp (hd z)).mono fun w hw => by
    simpa [Transcendental, not_or, and_comm] using hw

/-- Two labels with identical second-coordinate punctured germs differ by
left multiplication in the level subgroup. No assertion about equality of
the values of the germs at the center is needed. -/
theorem gamma0_of_eventuallyEq_analyticJN (N : ℕ) [NeZero N]
    (τ : UpperHalfPlane) (γ₁ γ₂ : SL(2, ℤ))
    (h : (fun w : ℂ => X0Model.analyticJN N (γ₁ • UpperHalfPlane.ofComplex w))
      =ᶠ[𝓝[≠] (τ : ℂ)] (fun w : ℂ => X0Model.analyticJN N (γ₂ • UpperHalfPlane.ofComplex w))) :
    γ₂ * γ₁⁻¹ ∈ CongruenceSubgroup.Gamma0 N := by
  let σ := γ₁ • τ
  have hback : γ₁⁻¹ • σ = τ := inv_smul_smul _ _
  have htend := slMoebius_tendsto γ₁⁻¹ σ
  rw [hback] at htend
  have hd : ∀ᶠ w in 𝓝[≠] (σ : ℂ), 0 < w.im :=
    mem_nhdsWithin_of_mem_nhds (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds σ.im_pos)
  obtain ⟨z, ht, hz, he⟩ :=
    ((frequently_transcendental (σ : ℂ)).and_eventually (hd.and (htend.eventually h))).exists
  let w : UpperHalfPlane := ⟨z, hz⟩
  change X0Model.analyticJN N
    (γ₁ • UpperHalfPlane.ofComplex (slMoebius γ₁⁻¹ (w : ℂ))) =
    X0Model.analyticJN N (γ₂ • UpperHalfPlane.ofComplex (slMoebius γ₁⁻¹ (w : ℂ))) at he
  rw [← coe_sl_smul, UpperHalfPlane.ofComplex_apply, smul_inv_smul] at he
  apply gamma0_of_analyticJN_eq_at_transcendental N (γ₂ * γ₁⁻¹) w ht
  rw [mul_smul]
  exact he.symm

/-- If local monodromy matches the two punctured germs by an element fixing
the center, the labels `Γ₀(N)γ₁` and `Γ₀(N)γ₂` are in the same right orbit. -/
theorem rightOrbit_of_eventuallyEq_analyticJN (N : ℕ) [NeZero N]
    (τ : UpperHalfPlane) (γ₁ γ₂ s : SL(2, ℤ)) (hs : s • τ = τ)
    (h : (fun w : ℂ => X0Model.analyticJN N (γ₁ • UpperHalfPlane.ofComplex w))
      =ᶠ[𝓝[≠] (τ : ℂ)]
        (fun w : ℂ => X0Model.analyticJN N ((γ₂ * s) • UpperHalfPlane.ofComplex w))) :
    ∃ δ k : SL(2, ℤ), δ ∈ CongruenceSubgroup.Gamma0 N ∧
      k • τ = τ ∧ γ₂ = δ * γ₁ * k := by
  refine ⟨(γ₂ * s) * γ₁⁻¹, s⁻¹, gamma0_of_eventuallyEq_analyticJN N τ γ₁ (γ₂ * s) h, ?_, ?_⟩
  · exact inv_smul_eq_iff.mpr hs.symm
  · simp [mul_assoc]


end ZInQ.Manuscript.RC.X0Model2
