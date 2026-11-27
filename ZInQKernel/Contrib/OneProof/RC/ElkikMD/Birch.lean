import ZInQKernel.Contrib.OneProof.RC.ElkikMD.Periods
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.ModularSymbols.Period.Integral
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.LFunction.Basic
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Twist.Basic

/-!
# The finite Fourier expansion at the central point

The analytic part of Birch's calculation: translate the cusp form, use the finite Fourier
expansion of the twist, and take the Mellin integral at `1`. The explicit quadratic Fourier
evaluation and the coefficient comparison with the curve twist are separate arithmetic inputs.
This calculation is on-the-spot (c); no Birch statement is added as a print.
-/

noncomputable section

open Complex Matrix Matrix.GeneralLinearGroup Matrix.SpecialLinearGroup
  CongruenceSubgroup MeasureTheory Set OnePoint
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm ZMod
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.GenusOdd

namespace ZInQ.Manuscript.RC.ElkikMD

private theorem translation_det (r : ℚ) :
    0 < (↑(upperRightHom r : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det := by
  simp [upperRightHom_apply, Matrix.det_fin_two]

private theorem translation_slash (f : ℍ → ℂ) (r : ℚ) :
    (f ∣[(2 : ℤ)] (upperRightHom r : GL (Fin 2) ℚ)) = fun z => f ((r : ℝ) +ᵥ z) := by
  have hmap : Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (upperRightHom r) =
      upperRightHom (r : ℝ) := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upperRightHom_apply]
  rw [ModularForm.rat_slash, hmap]
  exact funext (TauCeti.ModularForm.slash_upperRightHom_apply 2 _ f)

private theorem cuspSymbol_eq_integral (f : ℍ → ℂ) (r : ℚ) :
    cuspSymbol f r = (2 * (Real.pi : ℂ)) *
      ∫ t in Set.Ioi (0 : ℝ), f ((r : ℝ) +ᵥ ofComplex (I * t)) := by
  have h0 : (upperRightHom r : GL (Fin 2) ℚ) • ((0 : ℚ) : OnePoint ℚ) = r := by
    simp [upperRightHom_apply, smul_some_eq_ite]
  have hinf : (upperRightHom r : GL (Fin 2) ℚ) • (∞ : OnePoint ℚ) = ∞ := by
    simp [upperRightHom_apply, smul_infty_eq_ite]
  rw [cuspSymbol, ← h0, ← hinf, TauCeti.cuspIntegral_smul_zero_smul_infty _ (translation_det r),
    geodesicIntegral_def, translation_slash]
  have hI : (-(2 * (Real.pi : ℂ) * I)) * I = 2 * (Real.pi : ℂ) := by
    rw [neg_mul, mul_assoc, I_mul_I]
    ring
  rw [← mul_assoc, hI]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [UpperHalfPlane.resToImagAxis_of_pos _ ht,
    ofComplex_apply_of_im_pos (by simpa using ht : 0 < (I * t : ℂ).im)]

private theorem integrable_translate {N : ℕ} [NeZero N] (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2)
    (r : ℚ) : IntegrableOn (fun t : ℝ => f ((r : ℝ) +ᵥ ofComplex (I * t))) (Ioi 0) := by
  let p : MvPolynomial.homogeneousSubmodule (Fin 2) ℂ 0 :=
    ⟨1, MvPolynomial.isHomogeneous_one _ _⟩
  have hp : TauCeti.ModularSymbols.periodIntegrand f p = ⇑f := by
    funext z
    simp [p, TauCeti.ModularSymbols.periodIntegrand]
  have hi := TauCeti.ModularSymbols.integrableOn_resToImagAxis_periodIntegrand_slash
    f (w := 0) (by norm_num) p (translation_det r)
  rw [hp, translation_slash] at hi
  refine hi.congr_fun (fun t ht => ?_) measurableSet_Ioi
  rw [UpperHalfPlane.resToImagAxis_of_pos _ ht,
    ofComplex_apply_of_im_pos (by simpa using ht : 0 < (I * t : ℂ).im)]

private theorem l_one_eq_symbol {L : ℕ} [NeZero L] (g : CuspForm ((Gamma1 L).map (mapGL ℝ)) 2) :
    ModularForm.L (by decide : (0 : ℤ) < 2) g 1 = cuspSymbol g 0 := by
  rw [ModularForm.L, CuspForm.Λ_eq_mellin, Complex.Gammaℂ_one, mellin, sub_self, cuspSymbol_eq_integral]
  simp [mul_comm]

/-- The analytic Birch identity, given the arithmetic evaluation of the Fourier coefficients
and the equality of the twisted Dirichlet coefficients. Here `M = |d|`, `τ` is the Gauss sum,
and `Φ` is the quadratic character (written as a function on `ℤ/Mℤ`). Neither equality mentions a
lattice or asserts rationality of a central value. -/
theorem quadraticCuspSum_eq_twisted_value {E : WeierstrassCurve ℚ} {d : ℤ}
    [NeZero d.natAbs] {N L : ℕ} [NeZero N] [NeZero L]
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2) (Φ : ZMod d.natAbs → ℂ)
    (hNL : N * d.natAbs ∣ L) (hML : d.natAbs * d.natAbs ∣ L)
    {τ : ℂ} (hτ : τ ≠ 0)
    (hDFT : ∀ a : ZMod d.natAbs, (d.natAbs : ℂ)⁻¹ * ZMod.dft Φ a =
      (chiD d a.val : ℂ) / τ)
    (hcoeff : ∀ n : ℕ, 0 < n → Φ n * (qExpansion 1 f).coeff n =
      ((qtwist E d).LFunction n : ℂ))
    (hcont : ∃ F, IsLContinuation (qtwist E d) F) :
    quadraticCuspSum f d = τ * Lval (qtwist E d) := by
  let g := CuspForm.twist Φ hNL hML f
  obtain ⟨F, hF⟩ := hcont
  have hFg : F = ModularForm.L (by decide : (0 : ℤ) < 2) g := by
    have h := CuspForm.eq_strictWidthInfty_cpow_mul_L g (by decide) hF.1 (fun {s} hs => by
      have hs' : (3 : ℝ) / 2 < s.re := by norm_num at hs ⊢; linarith
      rw [hF.2 s hs', WeierstrassCurve.LSeries]
      apply LSeries_congr
      intro n hn
      rw [strictWidthInfty_Gamma1]
      exact (CuspForm.qExpansion_twist_coeff Φ hNL hML f n).trans (hcoeff n (Nat.pos_of_ne_zero hn)) |>.symm)
    simpa [strictWidthInfty_Gamma1] using h
  have hshift : ∀ z : ℍ, τ * g z =
      ∑ a : ZMod d.natAbs, (chiD d a.val : ℂ) * f (((a.val : ℝ) / d.natAbs) +ᵥ z) := by
    intro z
    rw [show g z = CuspForm.twist Φ hNL hML f z from rfl, CuspForm.twist_apply,
      mul_left_comm, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    have hc : τ * ((d.natAbs : ℂ)⁻¹ * ZMod.dft Φ a) = (chiD d a.val : ℂ) := by
      rw [hDFT a]
      field_simp
    calc
      _ = (τ * ((d.natAbs : ℂ)⁻¹ * ZMod.dft Φ a)) * f (((a.val : ℝ) / d.natAbs) +ᵥ z) := by ring
      _ = _ := by rw [hc]
  have hsum : τ * cuspSymbol g 0 =
      ∑ a : ZMod d.natAbs, (chiD d a.val : ℂ) * cuspSymbol f ((a.val : ℚ) / d.natAbs) := by
    let c : ℂ := 2 * (Real.pi : ℂ)
    let T (a : ZMod d.natAbs) (t : ℝ) :=
      (chiD d a.val : ℂ) * f ((((a.val : ℚ) / d.natAbs : ℚ) : ℝ) +ᵥ ofComplex (I * t))
    have hT : ∀ a : ZMod d.natAbs, IntegrableOn (T a) (Ioi 0) :=
      fun a => (integrable_translate f ((a.val : ℚ) / d.natAbs)).const_mul _
    calc
      _ = c * ∫ t in Ioi (0 : ℝ), τ * g (ofComplex (I * t)) := by
        simp only [cuspSymbol_eq_integral, Rat.cast_zero, zero_vadd, integral_const_mul]
        dsimp [c]
        ring
      _ = c * ∫ t in Ioi (0 : ℝ), ∑ a, T a t := by
        apply congrArg (c * ·)
        refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
        simpa only [T, Rat.cast_div, Rat.cast_natCast] using hshift (ofComplex (I * t))
      _ = _ := by
        rw [integral_finsetSum _ (fun a _ => hT a), Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        simp only [cuspSymbol_eq_integral, T, integral_const_mul]
        dsimp [c]
        ring
  have hreindex : (∑ a : ZMod d.natAbs,
      (chiD d a.val : ℂ) * cuspSymbol f ((a.val : ℚ) / d.natAbs)) = quadraticCuspSum f d := by
    unfold quadraticCuspSum
    apply Finset.sum_bij (fun a _ => (a : ZMod d.natAbs).val)
    · exact fun a _ => Finset.mem_range.mpr (ZMod.val_lt a)
    · exact fun a _ b _ hab => ZMod.val_injective _ hab
    · intro b hb
      exact ⟨(b : ZMod d.natAbs), Finset.mem_univ _, ZMod.val_natCast_of_lt (Finset.mem_range.mp hb)⟩
    · intros; rfl
  rw [← hreindex, ← hsum, ← l_one_eq_symbol, ← hFg, ← Lval_eq hF]


end ZInQ.Manuscript.RC.ElkikMD
