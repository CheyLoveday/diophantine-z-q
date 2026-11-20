import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff

/-! Rational descent inside the Laurent series field, on-the-spot (c) for
the rationality in tex 1785–1787 and 2836–2838. -/

noncomputable section

open ModularCurve

namespace ZInQ.Manuscript.RC.ModFnField

local instance : Module ℂ (LaurentSeries ℂ) := Algebra.toModule

/-- Extend the Laurent coefficients from `ℚ` to `ℂ`. -/
def complexify : LaurentSeries ℚ →+* LaurentSeries ℂ where
  toFun x := x.map (Rat.castHom ℂ)
  map_one' := by
    ext n
    by_cases hn : n = 0 <;> simp [HahnSeries.coeff_one, hn]
  map_zero' := by ext n; simp
  map_add' x y := by ext n; simp
  map_mul' _ _ := HahnSeries.map_mul (Rat.castHom ℂ).toNonUnitalRingHom

@[simp] theorem complexify_coeff (a : LaurentSeries ℚ) (n : ℤ) :
    (complexify a).coeff n = (a.coeff n : ℂ) := rfl

/-- Apply a rational linear functional on the coefficients of a Laurent series. -/
private def project (p : ℂ →ₗ[ℚ] ℚ) (x : LaurentSeries ℂ) : LaurentSeries ℚ := x.map p

@[simp] private theorem project_zero (p : ℂ →ₗ[ℚ] ℚ) : project p 0 = 0 := by
  ext n
  simp [project]

@[simp] private theorem project_add (p : ℂ →ₗ[ℚ] ℚ) (a b : LaurentSeries ℂ) :
    project p (a + b) = project p a + project p b := by
  ext n
  simp [project]

/-- The functional sends a complex multiple of a rational series to the
corresponding rational multiple. -/
private theorem project_scalar (p : ℂ →ₗ[ℚ] ℚ) (c : ℂ) (a : LaurentSeries ℚ) :
    project p (algebraMap ℂ (LaurentSeries ℂ) c * complexify a) =
      algebraMap ℚ (LaurentSeries ℚ) (p c) * a := by
  ext n
  have hc : algebraMap ℂ (LaurentSeries ℂ) c = HahnSeries.single 0 c := by
    rw [HahnSeries.algebraMap_apply',
      show algebraMap ℂ (PowerSeries ℂ) c = PowerSeries.C c by simp,
      HahnSeries.ofPowerSeries_C]
    rfl
  simp only [project, HahnSeries.map_coeff, hc, ModularCurve.algebraMap_apply_eq_single,
    HahnSeries.coeff_single_zero_mul, complexify_coeff]
  rw [mul_comm c, ← Rat.smul_def, map_smul, smul_eq_mul, mul_comm]

/-- Multiplication by a rational series commutes with projection on the
complex span of rational series. -/
private theorem project_mul (p : ℂ →ₗ[ℚ] ℚ)
    (D : IntermediateField ℚ (LaurentSeries ℚ)) (s : LaurentSeries ℚ)
    {x : LaurentSeries ℂ} (hx : x ∈ Submodule.span ℂ (complexify '' (D : Set _))) :
    project p (complexify s * x) = s * project p x := by
  let C := algebraMap ℂ (LaurentSeries ℂ)
  have h (c : ℂ) (a : LaurentSeries ℂ)
      (ha : a ∈ Submodule.span ℂ (complexify '' (D : Set _))) :
      project p (complexify s * (C c * a)) = s * project p (C c * a) := by
    induction ha using Submodule.span_induction generalizing c with
    | mem x hx =>
      obtain ⟨a, _, rfl⟩ := hx
      rw [mul_left_comm, ← map_mul, project_scalar, project_scalar, mul_left_comm]
    | zero => simp
    | add x y _ _ hx hy => simp only [mul_add, project_add, hx, hy]
    | smul a x _ ih =>
      rw [Algebra.smul_def, ← mul_assoc (C c), ← map_mul]
      exact ih (c * a)
  simpa only [map_one, one_mul] using h 1 x hx

/-- The image under projection of the complex span of a rational field is
contained in the rational field. -/
private theorem project_mem (p : ℂ →ₗ[ℚ] ℚ)
    (D : IntermediateField ℚ (LaurentSeries ℚ)) {x : LaurentSeries ℂ}
    (hx : x ∈ Submodule.span ℂ (complexify '' (D : Set _))) : project p x ∈ D := by
  let C := algebraMap ℂ (LaurentSeries ℂ)
  have h (c : ℂ) (a : LaurentSeries ℂ)
      (ha : a ∈ Submodule.span ℂ (complexify '' (D : Set _))) : project p (C c * a) ∈ D := by
    induction ha using Submodule.span_induction generalizing c with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      rw [project_scalar]
      exact D.mul_mem (D.algebraMap_mem _) hy
    | zero => simp
    | add x y _ _ hx hy => simpa only [mul_add, project_add] using D.add_mem (hx c) (hy c)
    | smul a x _ ih =>
      rw [Algebra.smul_def, ← mul_assoc (C c), ← map_mul]
      exact ih (c * a)
  simpa only [map_one, one_mul] using h 1 x hx

/-- If the coefficients of a complex rational expression in rational Laurent
series are rational, the expression descends to the field over `ℚ`.
Apply a rational linear functional to its numerator and denominator after
clearing denominators, choosing it to detect a nonzero denominator coefficient. -/
theorem mem_rat_adjoin_of_complexify_mem {S : Set (LaurentSeries ℚ)} {s : LaurentSeries ℚ}
    (hs : complexify s ∈ IntermediateField.adjoin ℂ (complexify '' S)) :
    s ∈ IntermediateField.adjoin ℚ S := by
  let D := IntermediateField.adjoin ℚ S
  let M := (D.toSubfield.toSubmonoid).map complexify.toMonoidHom
  have hspan {a : LaurentSeries ℂ} (ha : a ∈ Algebra.adjoin ℂ (complexify '' S)) :
      a ∈ Submodule.span ℂ (complexify '' (D : Set _)) := by
    change a ∈ (Algebra.adjoin ℂ (complexify '' S)).toSubmodule at ha
    rw [Algebra.adjoin_eq_span] at ha
    refine Submodule.span_mono ?_ ha
    change Submonoid.closure (complexify '' S) ≤ M
    exact Submonoid.closure_le.mpr (Set.image_mono (IntermediateField.subset_adjoin ℚ S))
  by_cases hz : s = 0
  · simpa only [hz] using D.zero_mem
  obtain ⟨a, ha, b, hb, hab⟩ := IntermediateField.mem_adjoin_iff_div.mp hs
  have hb0 : b ≠ 0 := by
    intro he
    rw [he, div_zero] at hab
    exact hz (complexify.injective (hab.trans (map_zero _).symm))
  have hlead : b.coeff b.order ≠ 0 := by
    simpa only [HahnSeries.leadingCoeff_eq] using (HahnSeries.leadingCoeff_ne_zero.mpr hb0)
  obtain ⟨p, hp⟩ := Module.Projective.exists_dual_eq_one ℚ hlead
  have hpb : project p b ≠ 0 := by
    intro he
    have he' : p (b.coeff b.order) = 0 := congrArg (fun z : LaurentSeries ℚ => z.coeff b.order) he
    exact one_ne_zero (hp.symm.trans he')
  have hmul := congrArg (project p) ((eq_div_iff hb0).mp hab)
  rw [project_mul p D s (hspan hb)] at hmul
  rw [(eq_div_iff hpb).mpr hmul]
  exact D.div_mem (project_mem p D (hspan ha)) (project_mem p D (hspan hb))

/-- Rational descent for the specified two-generator modular function field. -/
theorem modularFunctionField_descent (N : ℕ) [NeZero N] (s : LaurentSeries ℚ)
    (hs : complexify s ∈ modularFunctionFieldC ℂ N) : s ∈ modularFunctionField N := by
  have hj : complexify jq = jqModC ℂ := map_jqModC (Rat.castHom ℂ)
  have hjN : complexify (qExpand ℚ N jq) = jqNModC ℂ N := by
    ext n
    by_cases hn : (N : ℤ) ∣ n
    · obtain ⟨k, rfl⟩ := hn
      simpa only [complexify_coeff, jqNModC, qExpand_coeff_mul] using
        congrArg (fun z : LaurentSeries ℂ => z.coeff k) hj
    · simp [jqNModC, qExpand_coeff_of_not_dvd _ _ hn]
  apply mem_rat_adjoin_of_complexify_mem
  simpa only [Set.image_insert_eq, Set.image_singleton, hj, hjN, modularFunctionFieldC] using hs


end ZInQ.Manuscript.RC.ModFnField
