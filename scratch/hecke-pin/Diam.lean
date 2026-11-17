import ZInQKernel.Contrib.OneProof.HeckePin

noncomputable section
namespace AfTateLam.HeckePin
open PkgI4 (CF coeff)
open Function UpperHalfPlane Real
open scoped MatrixGroups ModularForm
local notation "Iℂ" => Complex.I

variable {N : ℕ}

/-- Derivative of the Möbius map of `g ∈ SL₂(ℤ)` at `τ ∈ ℍ`. -/
theorem hasDerivAt_moebius (g : SL(2, ℤ)) (τ : UpperHalfPlane) :
    HasDerivAt (fun z : ℂ => ((g 0 0 : ℂ) * z + g 0 1) / ((g 1 0 : ℂ) * z + g 1 1))
      (denom g τ ^ (-2 : ℤ)) (τ : ℂ) := by
  have hd : (g 1 0 : ℂ) * τ + g 1 1 ≠ 0 := by
    have := denom_ne_zero g τ
    simpa [ModularGroup.denom_apply] using this
  have h1 : HasDerivAt (fun z : ℂ => (g 0 0 : ℂ) * z + g 0 1) (g 0 0 : ℂ) (τ : ℂ) := by
    simpa using ((hasDerivAt_id (τ : ℂ)).const_mul (g 0 0 : ℂ)).add_const (g 0 1 : ℂ)
  have h2 : HasDerivAt (fun z : ℂ => (g 1 0 : ℂ) * z + g 1 1) (g 1 0 : ℂ) (τ : ℂ) := by
    simpa using ((hasDerivAt_id (τ : ℂ)).const_mul (g 1 0 : ℂ)).add_const (g 1 1 : ℂ)
  convert h1.div h2 hd using 1
  have hdet : (g 0 0 : ℂ) * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.2; rw [Matrix.det_fin_two] at this; exact_mod_cast this
  rw [ModularGroup.denom_apply, zpow_neg, zpow_two]
  field_simp
  linear_combination (-1 : ℂ) * hdet

theorem hasDerivAt_comp_smul {f : CF N 2} {F : UpperHalfPlane → ℂ} (hF : IsPrimitive f F)
    (g : SL(2, ℤ)) (τ : UpperHalfPlane) :
    HasDerivAt (fun z : ℂ => F (g • UpperHalfPlane.ofComplex z)) (f (g • τ) * denom g τ ^ (-2 : ℤ))
      (τ : ℂ) := by
  have hm := hasDerivAt_moebius g τ
  have hmτ : ((g 0 0 : ℂ) * τ + g 0 1) / ((g 1 0 : ℂ) * τ + g 1 1) = ((g • τ : UpperHalfPlane) : ℂ) := by
    rw [coe_specialLinearGroup_apply]; simp
  have hF' := hF (g • τ)
  rw [← hmτ] at hF'
  have hc := hF'.comp (τ : ℂ) hm
  apply hc.congr_of_eventuallyEq
  filter_upwards [(UpperHalfPlane.isOpen_upperHalfPlaneSet).mem_nhds τ.im_pos] with z hz
  simp only [Function.comp]
  congr 1
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  have : ((g 0 0 : ℂ) * z + g 0 1) / ((g 1 0 : ℂ) * z + g 1 1) = ((g • (⟨z, hz⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) := by
    rw [coe_specialLinearGroup_apply]; simp
  rw [this, UpperHalfPlane.ofComplex_apply]

theorem eichler_diamond {χ : DirichletCharacter ℂ N} {f : CF N 2} (hf : PkgI4.HasNebentypus f χ)
    {F : UpperHalfPlane → ℂ} (hF : IsPrimitive f F) (d : (ZMod N)ˣ) (g : SL(2, ℤ))
    (hg1 : (N : ℤ) ∣ g 1 0) (hg2 : ((g 1 1 : ℤ) : ZMod N) = (d : ZMod N)) (τ τ' : UpperHalfPlane) :
    F (g • τ) - F (g • τ') = χ (d : ZMod N) * (F τ - F τ') := by
  have hmem : g ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem]; exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hg1
  have hneb := hf g hmem
  rw [hg2] at hneb
  let Φ : ℂ → ℂ := fun z => F (g • UpperHalfPlane.ofComplex z) - χ (d : ZMod N) * F (UpperHalfPlane.ofComplex z)
  have hΦ : ∀ z ∈ {z : ℂ | 0 < z.im}, HasDerivAt Φ 0 z := by
    intro z hz
    have h1 := hasDerivAt_comp_smul hF g ⟨z, hz⟩
    have h2 := (hF ⟨z, hz⟩).const_mul (χ (d : ZMod N))
    have := h1.sub h2
    have hz0 : f (g • (⟨z, hz⟩ : UpperHalfPlane)) * denom g (⟨z, hz⟩ : UpperHalfPlane) ^ (-2 : ℤ) -
        χ (d : ZMod N) * f ⟨z, hz⟩ = 0 := by
      have := congrFun hneb ⟨z, hz⟩
      rw [ModularForm.SL_slash_apply] at this
      rw [this]; simp
    rw [hz0] at this
    exact this
  have hconst := (UpperHalfPlane.isOpen_upperHalfPlaneSet).is_const_of_deriv_eq_zero
    (convex_halfSpace_im_gt 0).isPreconnected
    (fun z hz => (hΦ z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hΦ z hz).deriv) (x := (τ : ℂ)) (y := (τ' : ℂ)) τ.im_pos τ'.im_pos
  simp only [Φ, UpperHalfPlane.ofComplex_apply] at hconst
  linear_combination hconst

end AfTateLam.HeckePin
