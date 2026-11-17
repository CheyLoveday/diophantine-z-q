import ZInQKernel.Contrib.OneProof.GrossZagierAlgebraic

noncomputable section

open UpperHalfPlane Filter Topology

namespace ZInQ.GZDict2

open ZInQ.GZAlg

/-! ## §1. Algebra of `q`-expansions -/

theorem hasQExp_add {X Y : ℍ → ℂ} {x y : LaurentSeries ℚ} (hX : HasQExp X x) (hY : HasQExp Y y) :
    HasQExp (fun τ => X τ + Y τ) (x + y) := by
  obtain ⟨T1, h1⟩ := hX
  obtain ⟨T2, h2⟩ := hY
  refine ⟨max T1 T2, fun τ hτ => ?_⟩
  have := (h1 τ (lt_of_le_of_lt (le_max_left _ _) hτ)).add
    (h2 τ (lt_of_le_of_lt (le_max_right _ _) hτ))
  convert this using 1
  funext m
  simp [HahnSeries.coeff_add, add_mul]

theorem algebraMap_laurent (c : ℚ) :
    algebraMap ℚ (LaurentSeries ℚ) c = HahnSeries.single 0 c :=
  (RingHom.congr_fun (Subsingleton.elim (algebraMap ℚ (LaurentSeries ℚ)) HahnSeries.C) c).trans rfl

theorem hasQExp_const (c : ℚ) :
    HasQExp (fun _ => (c : ℂ)) (algebraMap ℚ (LaurentSeries ℚ) c) := by
  refine ⟨0, fun τ _ => ?_⟩
  rw [algebraMap_laurent]
  have h := hasSum_single (f := fun m : ℤ => (((HahnSeries.single (0 : ℤ) c).coeff m : ℚ) : ℂ) *
    qPar τ ^ m) 0 (fun b hb => by simp [HahnSeries.coeff_single_of_ne hb])
  simpa using h

/-- The coefficient of a product of Laurent series, as a (finite) convergent sum in `ℂ`. -/
theorem hasSum_coeff_mul (x y : LaurentSeries ℚ) (m : ℤ) :
    HasSum (fun a : ℤ => ((x.coeff a : ℚ) : ℂ) * ((y.coeff (m - a) : ℚ) : ℂ))
      (((x * y).coeff m : ℚ) : ℂ) := by
  classical
  set A := Finset.antidiagonal x.isPWO_support y.isPWO_support m
  have hmem : ∀ ij : ℤ × ℤ, ij ∈ A ↔ x.coeff ij.1 ≠ 0 ∧ y.coeff ij.2 ≠ 0 ∧ ij.1 + ij.2 = m := by
    intro ij
    simp [A, HahnSeries.mem_support]
  have hsum : HasSum (fun a : ℤ => ((x.coeff a : ℚ) : ℂ) * ((y.coeff (m - a) : ℚ) : ℂ))
      (∑ a ∈ A.image Prod.fst, ((x.coeff a : ℚ) : ℂ) * ((y.coeff (m - a) : ℚ) : ℂ)) :=
    hasSum_sum_of_ne_finset_zero (fun a ha => by
      by_contra h0
      apply ha
      have h0' : x.coeff a * y.coeff (m - a) ≠ 0 := by exact_mod_cast h0
      refine Finset.mem_image.2 ⟨(a, m - a), (hmem _).2 ⟨left_ne_zero_of_mul h0',
        right_ne_zero_of_mul h0', by ring⟩, rfl⟩)
  convert hsum using 1
  rw [HahnSeries.coeff_mul, Finset.sum_image]
  · push_cast
    refine Finset.sum_congr rfl fun ij hij => ?_
    obtain ⟨-, -, h⟩ := (hmem ij).1 hij
    rw [show m - ij.1 = ij.2 by omega]
  · intro ij hij ij' hij' he
    obtain ⟨-, -, h⟩ := (hmem ij).1 hij
    obtain ⟨-, -, h'⟩ := (hmem ij').1 hij'
    exact Prod.ext he (by omega)

theorem hasQExp_mul {X Y : ℍ → ℂ} {x y : LaurentSeries ℚ} (hX : HasQExp X x) (hY : HasQExp Y y) :
    HasQExp (fun τ => X τ * Y τ) (x * y) := by
  obtain ⟨T1, h1⟩ := hX
  obtain ⟨T2, h2⟩ := hY
  refine ⟨max T1 T2, fun τ hτ => ?_⟩
  have hs1 := h1 τ (lt_of_le_of_lt (le_max_left _ _) hτ)
  have hs2 := h2 τ (lt_of_le_of_lt (le_max_right _ _) hτ)
  have hq := qPar_ne_zero τ
  set f : ℤ → ℂ := fun m => (x.coeff m : ℂ) * qPar τ ^ m
  set g : ℤ → ℂ := fun m => (y.coeff m : ℂ) * qPar τ ^ m
  have hf : Summable fun m => ‖f m‖ := summable_norm_iff.2 hs1.summable
  have hg : Summable fun m => ‖g m‖ := summable_norm_iff.2 hs2.summable
  have hprod := hs1.mul hs2 (summable_mul_of_summable_norm hf hg)
  -- reindex `(a, b) ↦ (a + b, a)`
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun p => (p.2, p.1 - p.2)
      invFun := fun p => (p.1 + p.2, p.1)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  have he := (e.hasSum_iff (f := fun p : ℤ × ℤ => f p.1 * g p.2)).2 hprod
  refine he.prod_fiberwise fun m => ?_
  have hc := (hasSum_coeff_mul x y m).mul_right (qPar τ ^ m)
  convert hc using 1
  funext a
  simp only [Function.comp_apply, e, Equiv.coe_fn_mk, f, g]
  rw [show m = a + (m - a) by ring, zpow_add₀ hq]
  simp only [add_sub_cancel_left]
  ring

theorem hasQExp_congr {X X' : ℍ → ℂ} {x : LaurentSeries ℚ} (h : HasQExp X x) (hXX : ∀ τ, X τ = X' τ) :
    HasQExp X' x := by
  have : X = X' := funext hXX
  exact this ▸ h

/-- A function with `q`-expansion `0` vanishes high up. -/
theorem HasQExp.eq_zero {X : ℍ → ℂ} (h : HasQExp X 0) : ∃ T : ℝ, ∀ τ : ℍ, T < τ.im → X τ = 0 := by
  obtain ⟨T, hT⟩ := h
  exact ⟨T, fun τ hτ => ((hT τ hτ).unique (by simp only [HahnSeries.coeff_zero, Rat.cast_zero, zero_mul]; exact hasSum_zero))⟩

end ZInQ.GZDict2
