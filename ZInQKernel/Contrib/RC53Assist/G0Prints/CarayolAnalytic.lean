import ZInQKernel.Contrib.RC53Assist.G0Prints.Faltings
import ZInQKernel.Contrib.CloudB3RC53.Hasse.Convergence
import ZInQKernel.Contrib.CloudB3RC53.WeilIsogeny.HasseProof
import Mathlib.NumberTheory.LSeries.Injectivity
import Mathlib.NumberTheory.ModularForms.Bounds

/-!
# Reading Carayol's equality of complete L-functions

An equality of the analytic L-functions on their common convergence half-plane
is not replaced by an assumed coefficient equality. Absolute convergence is
proved from the existing Hasse theorem and the cusp-form coefficient bound.
Uniqueness of convergent Dirichlet series then gives the coefficients.
The two proved prime-power recurrences recover the entire local polynomial,
including its quadratic coefficient and the primes dividing the level.

Locators: Carayol 1986, §0.8, Corollaire, p. 411; Li 1975, Theorem 3(i),
p. 295; Silverman V.1.1; bibliography key `carayol`, TeX lines 11205–11208.
-/

noncomputable section

set_option maxHeartbeats 800000
set_option autoImplicit false

namespace ZInQ.Contrib.RC53Assist.G0Prints

open NumberField IsDedekindDomain Filter Asymptotics UpperHalfPlane
open CongruenceSubgroup HeckeRing.GL2 Polynomial
open ZInQ.Contrib.RC53Assist.NewformGlueG0
open ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion
open ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary

/-- **DEFINITION**, the complete Dirichlet L-series of the genuine normalized
newform, including every bad Euler factor. The coefficients are its actual
period-one Fourier coefficients. Locator: Carayol 1986, §0.8, p. 411. -/
def newformL {M : ℕ} [NeZero M] (F : Newform M 2) (s : ℂ) : ℂ :=
  LSeries (fun n : ℕ => (qExpansion 1 F.toCuspForm).coeff n) s

/-- **PROVED**, the period-one Fourier coefficients of a weight-two cusp form
are `O(n)`. This uses the mean-square bound at the specified period, so it
makes no unproved change of the width at infinity.
Locator: Hecke's cusp-form bound, in the proved mean-square coefficient theorem. -/
theorem cusp_qExpansion_one_isBigO {Γ : Subgroup (GL (Fin 2) ℝ)}
    [Γ.IsArithmetic] (f : CuspForm Γ 2) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) :
    (fun n : ℕ => (qExpansion 1 f).coeff n) =O[atTop] fun n : ℕ => (n : ℝ) := by
  obtain ⟨C, hC⟩ := CuspFormClass.exists_sum_range_norm_sq_qExpansion_coeff_le_of_mem_strictPeriods
    (k := 2) f one_pos hΓ
  have hC0 : 0 ≤ C := by
    have h := hC 1
    have hsum : 0 ≤ ‖(qExpansion 1 f).coeff 0‖ ^ 2 := sq_nonneg _
    norm_num at h
    exact hsum.trans (by simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using h)
  have hb : ∀ n : ℕ, ‖(qExpansion 1 f).coeff n‖ ≤ Real.sqrt C * (n + 1 : ℝ) := by
    intro n
    have hle : ‖(qExpansion 1 f).coeff n‖ ^ 2 ≤
        ∑ m ∈ Finset.range (n + 1), ‖(qExpansion 1 f).coeff m‖ ^ 2 :=
      Finset.single_le_sum (f := fun m : ℕ => ‖(qExpansion 1 f).coeff m‖ ^ 2)
        (a := n) (fun _ _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_self n))
    have hn := hle.trans (hC (n + 1))
    have hs : Real.sqrt C ^ 2 = C := Real.sq_sqrt hC0
    have hnon : 0 ≤ Real.sqrt C * (n + 1 : ℝ) := by positivity
    push_cast at hn
    nlinarith [norm_nonneg ((qExpansion 1 f).coeff n)]
  apply Asymptotics.IsBigO.of_bound (2 * Real.sqrt C)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h := hb n
  rw [Real.norm_of_nonneg (Nat.cast_nonneg n)]
  nlinarith [Real.sqrt_nonneg C]

/-- **PROVED**, the newform Dirichlet series has finite abscissa of absolute
convergence. It is bounded by `2`; no summability hypothesis is smuggled into
the analytic equality of L-functions.
Locator: the cusp-form coefficient bound and the Dirichlet convergence theorem. -/
theorem newform_abscissa_lt_top {M : ℕ} [NeZero M] (F : Newform M 2) :
    LSeries.abscissaOfAbsConv (fun n : ℕ => (qExpansion 1 F.toCuspForm).coeff n) < ⊤ := by
  have h := cusp_qExpansion_one_isBigO F.toCuspForm
    (TauCeti.one_mem_strictPeriods_Gamma1_map M)
  have hpow : (fun n : ℕ => (qExpansion 1 F.toCuspForm).coeff n) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by simpa only [Real.rpow_one] using h
  have ha := LSeries.abscissaOfAbsConv_le_of_isBigO_rpow hpow
  exact ha.trans_lt (by
    convert EReal.coe_lt_top (2 : ℝ) using 1 <;> norm_num <;> rfl)

/-- **PROVED**, the elliptic-curve Dirichlet series has finite abscissa of
absolute convergence. The Hasse bound is already proved in the curve library.
Locator: Silverman V.1.1 and the proved Hasse convergence assembly. -/
theorem elliptic_abscissa_lt_top (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    LSeries.abscissaOfAbsConv (fun n : ℕ => (E.LFunction n : ℂ)) < ⊤ := by
  have hH : ZInQ.Contrib.CloudB3RC53.Hasse.HasseBound :=
    fun F _ _ W _ => ZInQ.Contrib.CloudB3RC53.WeilIsogeny.hasseBoundProved_proof F W
  have hs : LSeriesSummable (fun n : ℕ => (E.LFunction n : ℂ)) (3 : ℂ) :=
    ZInQ.Contrib.CloudB3RC53.Hasse.hasseConvergence_of_hasseBound hH E
      inferInstance (3 : ℂ) (by norm_num)
  exact hs.abscissaOfAbsConv_le.trans_lt (by norm_num : ((3 : ℂ).re : EReal) < ⊤)

/-- **PROVED CONVERGENCE**, the newform's actual Dirichlet series is
absolutely summable for `Re(s) > 2`. No summability hypothesis is supplied.
Locator: Hecke's cusp-form bound and Dirichlet-series convergence. -/
theorem newform_summable_of_two_lt_re {M : ℕ} [NeZero M] (F : Newform M 2)
    (s : ℂ) (hs : 2 < s.re) :
    LSeriesSummable (fun n : ℕ => (qExpansion 1 F.toCuspForm).coeff n) s := by
  apply LSeriesSummable_of_isBigO_rpow hs
  simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one] using
    cusp_qExpansion_one_isBigO F.toCuspForm (TauCeti.one_mem_strictPeriods_Gamma1_map M)

/-- **PROVED CONVERGENCE**, the elliptic curve's actual Dirichlet series is
absolutely summable for `Re(s) > 2`. The Hasse theorem is already proved.
Locator: Silverman V.1.1 and the proved Hasse convergence theorem. -/
theorem elliptic_summable_of_two_lt_re (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (s : ℂ) (hs : 2 < s.re) :
    LSeriesSummable (fun n : ℕ => (E.LFunction n : ℂ)) s := by
  have hH : ZInQ.Contrib.CloudB3RC53.Hasse.HasseBound :=
    fun F _ _ W _ => ZInQ.Contrib.CloudB3RC53.WeilIsogeny.hasseBoundProved_proof F W
  exact ZInQ.Contrib.CloudB3RC53.Hasse.hasseConvergence_of_hasseBound hH E
    inferInstance s (by linarith)

/-- **PROVED ANALYTIC READING**, Carayol's equality of the complete analytic
L-functions determines every positive Dirichlet coefficient. No equality of
coefficients or local polynomials is an input.
Locator: Carayol 1986, §0.8, p. 411; uniqueness of convergent Dirichlet series. -/
theorem coefficients_eq_of_complete_L (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {M : ℕ} [NeZero M] (F : Newform M 2)
    (hL : ∀ s : ℂ, 2 < s.re → E.LSeries s = newformL F s)
    (n : ℕ) (hn : n ≠ 0) :
    (E.LFunction n : ℂ) = (qExpansion 1 F.toCuspForm).coeff n := by
  apply LSeries.eq_of_LSeries_eventually_eq (elliptic_abscissa_lt_top E)
    (newform_abscissa_lt_top F) (n := n) _ hn
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with x hx
  exact hL (x : ℂ) (by simpa only [Complex.ofReal_re] using hx)

/-- **PROVED LOCAL READING**, the equality of complete L-functions gives the
exact existing local polynomial equality at every prime. The prime and prime
square determine the two coefficients by the proved recurrence; the constant
coefficient and degree bound come from the genuine local-polynomial definition.
This includes additive and both multiplicative reduction cases without using
the false invariant-space reading.
Locators: Carayol 1986, §0.8, p. 411; Li 1975, Theorem 3(i), p. 295. -/
theorem localPolynomial_eq_newform_of_complete_L
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {M : ℕ} [NeZero M] (F : Newform M 2) (hχ : F.χ = 1)
    (hL : ∀ s : ℂ, 2 < s.re → E.LSeries s = newformL F s)
    (p : ℕ) (hp : p.Prime) :
    (localPolynomialQ E (primeIdealQ p hp)).map (Int.castRingHom ℂ) =
      newformEulerPolynomial F hχ p := by
  have hpcoef := coefficients_eq_of_complete_L E F hL p hp.ne_zero
  have hpsq := coefficients_eq_of_complete_L E F hL (p ^ 2) (pow_ne_zero 2 hp.ne_zero)
  have hEr := lFunction_prime_pow_recurrence E p hp 0
  have hFr := newform_prime_pow_recurrence F hχ p hp 0
  simp only [zero_add, pow_one, pow_zero, lFunction_one] at hEr hFr
  rw [F.isNorm, mul_one] at hFr
  have hErC := congrArg (fun z : ℤ => (z : ℂ)) hEr
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, mul_one] at hErC
  have hquad : ((localPolynomialQ E (primeIdealQ p hp)).coeff 2 : ℂ) =
      if Nat.Coprime p M then (p : ℂ) else 0 := by
    rw [hpcoef, hpsq] at hErC
    linear_combination hErC - hFr
  rw [localPolynomialQ_shape E p hp]
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_pow, Polynomial.map_one,
    Int.coe_castRingHom]
  rw [hpcoef, hquad]
  rfl

end ZInQ.Contrib.RC53Assist.G0Prints
