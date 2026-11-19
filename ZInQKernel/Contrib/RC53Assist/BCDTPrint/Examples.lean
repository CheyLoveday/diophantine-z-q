import ZInQKernel.Contrib.RC53Assist.BCDTPrint.Literal

/-!
# A concrete eigenform in the printed sense

Non-vacuity of the printed notions of `Statement.lean` and `Literal.lean`. The discriminant
`Δ = η²⁴` (Mathlib, `CuspForm.discriminant`) is a nonzero cusp form of weight 12 for `SL₂(ℤ)`,
and the weight-12 cusp forms for `SL₂(ℤ)` form a line (Mathlib,
`CuspForm.exists_smul_discriminant_of_weight_eq_twelve`). Since `Γ₁(1) = SL₂(ℤ)`, every Hecke
operator `T_p` maps `Δ` to a multiple of `Δ`: `Δ` is an eigenform of weight 12 and level 1, both
as a library cusp form (`isBCDTEigenform_discriminant`) and as a function in the printed
vocabulary (`isPrintedEigenform_discriminant`). In particular `IsBCDTEigenform`,
`IsPrintedCuspForm` and `IsPrintedEigenform` are satisfiable.
-/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.BCDTPrint

open CongruenceSubgroup UpperHalfPlane Matrix.SpecialLinearGroup HeckeRing.GL2

/-- **PROVED**, by `CongruenceSubgroup.Gamma1_mem` and `ZMod 1` being a singleton: the image of
`Γ₁(1)` in `GL₂(ℝ)` is the image of `SL₂(ℤ)`. -/
theorem gamma1_one_map_eq : (Gamma1 1).map (mapGL ℝ) = (mapGL (R := ℤ) ℝ).range := by
  rw [MonoidHom.range_eq_map]
  congr 1
  rw [eq_top_iff]
  intro A _
  rw [Gamma1_mem]
  exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- **DEFINITION**, the discriminant `Δ` as a cusp form of weight 12 on `Γ₁(1)`: Mathlib's
`CuspForm.discriminant`, transported along `gamma1_one_map_eq` without changing the function. -/
def discriminantGamma1 : CuspForm ((Gamma1 1).map (mapGL ℝ)) 12 :=
  CuspForm.mcast rfl CuspForm.discriminant gamma1_one_map_eq

/-- **PROVED**, by definition: the underlying function is Mathlib's `Δ`. -/
theorem coe_discriminantGamma1 : ⇑discriminantGamma1 = ModularForm.discriminant :=
  rfl

/-- **PROVED**, non-vacuity of `IsBCDTEigenform`: by Mathlib's
`ModularForm.discriminant_ne_zero` and `CuspForm.exists_smul_discriminant_of_weight_eq_twelve`,
the discriminant is an eigenform of weight 12 and level 1 in the printed sense. -/
theorem isBCDTEigenform_discriminant : IsBCDTEigenform discriminantGamma1 := by
  refine ⟨fun h ↦ ?_, fun p hp _ ↦ ?_⟩
  · have hz := congrArg (fun F : CuspForm ((Gamma1 1).map (mapGL ℝ)) 12 ↦ F I) h
    exact ModularForm.discriminant_ne_zero I hz
  · obtain ⟨c, hc⟩ := CuspForm.exists_smul_discriminant_of_weight_eq_twelve
      (CuspForm.mcast rfl (heckeTCuspNat 12 p (_hn := ⟨hp.ne_zero⟩) discriminantGamma1)
        gamma1_one_map_eq.symm)
    refine ⟨c, CuspForm.ext fun z ↦ ?_⟩
    have hz := congrArg (fun F : CuspForm (mapGL (R := ℤ) ℝ).range 12 ↦ F z) hc
    exact hz.symm

/-- **PROVED**, non-vacuity of `IsPrintedEigenform` (and of `IsPrintedCuspForm`), by
`isPrintedEigenform_iff`: Mathlib's `Δ` is an eigenform of weight 12 and level 1 in the printed
vocabulary of Breuil–Conrad–Diamond–Taylor. -/
theorem isPrintedEigenform_discriminant : IsPrintedEigenform 1 12 ModularForm.discriminant :=
  (isPrintedEigenform_iff discriminantGamma1).mpr isBCDTEigenform_discriminant

end ZInQ.Contrib.RC53Assist.BCDTPrint
