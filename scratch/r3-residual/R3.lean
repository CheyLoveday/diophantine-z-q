import ZInQKernel.Contrib.OneProof.JavanpeykarRebase

open CategoryTheory AlgebraicGeometry MeasureTheory Topology Set MonObj Filter
open ZInQ.DefFaltings ZInQ.HeightSplit ZInQ.HeightGlue ZInQ.HeightDict ZInQ.HeightFix
open scoped NumberField

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

namespace ZInQ.R3Residual

/-! ## §1. Generic: charts from a uniformized group and holomorphic maps of `ℂ^g` -/

section Generic

variable {g : ℕ}

/-- The determinant of the derivative of a holomorphic map is nonzero near a point where it is. -/
theorem eventually_det_ne {f : (Fin g → ℂ) → (Fin g → ℂ)} {V : Set (Fin g → ℂ)} (hV : IsOpen V)
    (hf : DifferentiableOn ℂ f V) {z : Fin g → ℂ} (hz : z ∈ V) (hdet : (fderiv ℂ f z).det ≠ 0) :
    ∀ᶠ w in 𝓝 z, w ∈ V ∧ (fderiv ℂ f w).det ≠ 0 := by
  have hc : ContinuousAt (fun w => (fderiv ℂ f w).det) z :=
    ContinuousLinearMap.continuous_det.continuousAt.comp (Holomorphic.continuousAt_fderiv hV hf hz)
  exact Filter.Eventually.and (show ∀ᶠ w in 𝓝 z, w ∈ V from hV.mem_nhds hz)
    (hc.eventually (isOpen_ne.mem_nhds hdet))

/-- A continuous linear equivalence with a given underlying map, from a nonzero determinant. -/
noncomputable def equivOfDet (D : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) (h : D.det ≠ 0) :
    (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ) :=
  (LinearMap.equivOfIsUnitDet (isUnit_iff_ne_zero.mpr h)).toContinuousLinearEquiv

@[simp] theorem equivOfDet_coe (D : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) (h : D.det ≠ 0) :
    ((equivOfDet D h : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ)) : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) = D := by
  ext x; simp [equivOfDet]

variable {X : Type*} [Group X] [TopologicalSpace X] [T2Space X]
variable {Λ : Submodule ℤ (Fin g → ℂ)} [DiscreteTopology Λ] [IsZLattice ℝ Λ]
variable {Φ : (Fin g → ℂ) → X}

/-- **Charts on a uniformized group from a map with invertible holomorphic lift.** Let
`Φ : ℂ^g → X` be a continuous surjective homomorphism with kernel the full lattice `Λ`, and
`h : X → ℂ^g` such that `h ∘ Φ` is holomorphic on an open `V ∋ z₀` with invertible derivative at
`z₀`. Then `h` agrees near `Φ z₀` with a homeomorphism `e` onto an open subset of `ℂ^g`, whose inverse
lifts through `Φ` along a map `σ` that is holomorphic on `e.target`, with derivative the inverse of
the derivative of `h ∘ Φ` (invertible at each point of `σ(e.target)`). -/
theorem exists_chart_of_lift (hΦ : TorusVolume.IsUnif Λ Φ) (h : X → (Fin g → ℂ))
    {V : Set (Fin g → ℂ)} (hV : IsOpen V) (hd : DifferentiableOn ℂ (h ∘ Φ) V) {z₀ : Fin g → ℂ}
    (hz₀ : z₀ ∈ V) (hdet : (fderiv ℂ (h ∘ Φ) z₀).det ≠ 0) :
    ∃ (e : OpenPartialHomeomorph X (Fin g → ℂ)) (σ : (Fin g → ℂ) → (Fin g → ℂ)),
      Φ z₀ ∈ e.source ∧ EqOn h e e.source ∧ σ (e (Φ z₀)) = z₀ ∧ ContinuousOn σ e.target ∧
      ∀ x ∈ e.target, e.symm x = Φ (σ x) ∧ σ x ∈ V ∧ ∃ hx : (fderiv ℂ (h ∘ Φ) (σ x)).det ≠ 0,
        HasFDerivAt σ ((equivOfDet _ hx).symm : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) x := by
  set ψ := h ∘ Φ with hψdef
  have hstrict : HasStrictFDerivAt ψ
      ((equivOfDet _ hdet : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ)) : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) z₀ := by
    rw [equivOfDet_coe]; exact Holomorphic.hasStrictFDerivAt hV hd hz₀
  let P := hstrict.toOpenPartialHomeomorph ψ
  have hPcoe : (P : (Fin g → ℂ) → (Fin g → ℂ)) = ψ := hstrict.toOpenPartialHomeomorph_coe
  -- the open set where `ψ` is holomorphic with invertible derivative, inside an injectivity ball
  obtain ⟨r₀, hr₀, hsep⟩ := TorusVolume.exists_ball_sub_mem Λ
  have hcont : ContinuousOn (fun w => (fderiv ℂ ψ w).det) V := fun w hw =>
    (ContinuousLinearMap.continuous_det.continuousAt.comp
      (Holomorphic.continuousAt_fderiv hV hd hw)).continuousWithinAt
  set N := (V ∩ (fun w => (fderiv ℂ ψ w).det) ⁻¹' {0}ᶜ) ∩ Metric.ball z₀ r₀
  have hNo : IsOpen N := (hcont.isOpen_inter_preimage hV isOpen_compl_singleton).inter Metric.isOpen_ball
  have hz₀N : z₀ ∈ N := ⟨⟨hz₀, hdet⟩, Metric.mem_ball_self hr₀⟩
  let P' := P.restrOpen N hNo
  have hP'coe : (P' : (Fin g → ℂ) → (Fin g → ℂ)) = ψ := hPcoe
  have hP'src : P'.source = P.source ∩ N := P.restrOpen_source N hNo
  -- `Φ` on the ball
  have hinj : InjOn Φ (Metric.ball z₀ r₀) := fun x hx y hy hxy => by
    have h1 : x - z₀ ∈ Metric.ball (0 : Fin g → ℂ) r₀ := by
      rw [mem_ball_zero_iff, ← dist_eq_norm]; exact hx
    have h2 : y - z₀ ∈ Metric.ball (0 : Fin g → ℂ) r₀ := by
      rw [mem_ball_zero_iff, ← dist_eq_norm]; exact hy
    have := hsep _ h1 _ h2 (by rw [sub_sub_sub_cancel_right]; exact (hΦ.eq_iff x y).mp hxy)
    simpa using this
  let Φl := OpenPartialHomeomorph.ofContinuousOpen (hinj.toPartialEquiv Φ (Metric.ball z₀ r₀))
    hΦ.cont.continuousOn hΦ.isOpenMap Metric.isOpen_ball
  have hΦl : ∀ z, Φl z = Φ z := fun z => rfl
  have hΦls : Φl.source = Metric.ball z₀ r₀ := rfl
  let e := Φl.symm.trans P'
  have hesymm : ∀ x, e.symm x = Φ (P'.symm x) := fun x => rfl
  have hz₀s : z₀ ∈ Φl.source := by rw [hΦls]; exact Metric.mem_ball_self hr₀
  have hp : Φ z₀ ∈ e.source := by
    refine ⟨?_, ?_⟩
    · show Φ z₀ ∈ Φl.symm.source
      rw [OpenPartialHomeomorph.symm_source, ← hΦl]; exact Φl.map_source hz₀s
    · show Φl.symm (Φ z₀) ∈ P'.source
      rw [← hΦl, Φl.left_inv hz₀s, hP'src]
      exact ⟨hstrict.mem_toOpenPartialHomeomorph_source, hz₀N⟩
  have heq : EqOn h e e.source := by
    intro x hx
    have hxt : x ∈ Φl.target := hx.1
    show h x = P' (Φl.symm x)
    rw [hP'coe, hψdef, Function.comp_apply, ← hΦl, Φl.right_inv hxt]
  refine ⟨e, P'.symm, hp, heq, ?_, P'.continuousOn_symm.mono ?_, ?_⟩
  · show P'.symm (P' (Φl.symm (Φ z₀))) = z₀
    have h1 : Φl.symm (Φ z₀) = z₀ := by rw [← hΦl, Φl.left_inv hz₀s]
    rw [h1, P'.left_inv (by rw [hP'src]; exact ⟨hstrict.mem_toOpenPartialHomeomorph_source, hz₀N⟩)]
  · intro x hx; exact hx.1
  · intro x hx
    have hxt : x ∈ P'.target := hx.1
    have hσs : P'.symm x ∈ P'.source := P'.map_target hxt
    rw [hP'src] at hσs
    have hσN := hσs.2
    refine ⟨hesymm x, hσN.1.1, hσN.1.2, ?_⟩
    have hfd : HasFDerivAt (P' : (Fin g → ℂ) → (Fin g → ℂ))
        ((equivOfDet _ hσN.1.2 : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ)) : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ))
        (P'.symm x) := by
      rw [hP'coe]
      convert (hd.differentiableAt (hV.mem_nhds hσN.1.1)).hasFDerivAt using 1
      exact equivOfDet_coe _ _
    exact P'.hasFDerivAt_symm hxt hfd

end Generic

end ZInQ.R3Residual
