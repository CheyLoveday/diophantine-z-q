import ZInQKernel.Contrib.RC53Assist.G0Prints.Assembly

/-!
# Non-vacuity and normalization of the source factors

The concrete rational curve y² = x³ − x is nonsingular and its actual
rational Tate module has rank two. Arithmetic Frobenius exists at p = 3.
For a genuine newform, normalization forces the printed image vector to
be nonzero. The analytic series converge on a common half-plane.

No existence of a rational weight-two newform is postulated in these
examples. Its genuine type is an explicit premise where it is used.

Locators: Silverman III.1 and III.7; Shimura 1973, p. 526;
Carayol 1986, p. 411; Faltings 1983, p. 361.
-/

noncomputable section

set_option maxHeartbeats 800000
set_option autoImplicit false

namespace ZInQ.Contrib.RC53Assist.G0Prints

open NumberField Polynomial Module
open UpperHalfPlane CongruenceSubgroup HeckeRing.GL2
open ZInQ.Contrib.RC53Assist.NewformGlueG0
open ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion
open ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent
open ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary
open ZInQ.Contrib.RC53Assist.GlobalTrace

/-- **PROVED NON-VACUITY**, an actual elliptic rational curve and an actual
rank-two Tate basis exist. This is stronger than inhabitation by the zero
vector. Locator: Silverman III.1, III.7; the genuine rational Tate basis. -/
theorem concrete_rational_tate_rank_two :
    let : Fact (Nat.Prime 2) := ⟨by decide⟩
    Module.finrank ℚ_[2] (rationalTate testCurve 2) = 2 := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  change Module.finrank ℚ_[2] (rationalTate testCurve 2) = 2
  rw [Module.finrank_eq_card_basis (rationalTateBasis testCurve 2)]
  exact Fintype.card_fin 2

/-- **PROVED NON-VACUITY**, the concrete Frobenius and source local Tate
polynomial use different residual and auxiliary primes.
Locator: Faltings p. 361; the actual Frobenius construction. -/
theorem concrete_faltings_source_factor :
    let : Fact (Nat.Prime 2) := ⟨by decide⟩
    ∃ D : LocalArithmeticFrobenius 3,
      faltingsLv testCurve 2 D = faltingsLv testCurve 2 D := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨D⟩ := localArithmeticFrobenius_nonempty 3 (by decide)
  exact ⟨D, rfl⟩

/-- **PROVED NORMALIZATION**, every integer source factor has constant
coefficient one, so its formal reciprocal is an actual reciprocal and
not a totalized default. The corrected bad reading supplies rational
integer descent; good reduction is already proved.
Locators: Silverman Appendix C, §16; Faltings p. 361. -/
theorem sourceEulerPolynomial_constant_one (hB : BadReductionTatePolynomialReadingCoinv)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (v : RationalPlace) :
    (sourceEulerPolynomial E v).coeff 0 = 1 := by
  rw [sourceEulerPolynomial_eq_localPolynomial hB E v]
  unfold localPolynomialQ
  exact localPolynomial_coeff_zero _ _

/-- **PROVED NON-VACUITY**, the source Tate Euler-product L-series has a
finite abscissa of absolute convergence. Its equality on a half-plane
cannot be caused by totalizing a divergent sum to zero.
Locators: the proved Hasse bound and coefficientwise source dictionary. -/
theorem source_abscissa_lt_top (hB : BadReductionTatePolynomialReadingCoinv)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    LSeries.abscissaOfAbsConv (fun n : ℕ => (sourceLFunction E n : ℂ)) < ⊤ := by
  rw [sourceLFunction_eq_LFunction hB E]
  exact elliptic_abscissa_lt_top E

/-- **PROVED COMMON CONVERGENCE DOMAIN**, both series in Carayol's equality
are absolutely summable on `Re(s) > 2`, including the genuine Tate-factor
series after the corrected source dictionary. No totalized divergent sum
is used. Locators: Hecke's bound, Silverman V.1.1, Carayol p. 411. -/
theorem source_and_newform_summable (hB : BadReductionTatePolynomialReadingCoinv)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {M : ℕ} [NeZero M] (F : Newform M 2)
    (s : ℂ) (hs : 2 < s.re) :
    LSeriesSummable (fun n : ℕ => (sourceLFunction E n : ℂ)) s ∧
      LSeriesSummable (fun n : ℕ => (qExpansion 1 F.toCuspForm).coeff n) s := by
  rw [sourceLFunction_eq_LFunction hB E]
  exact ⟨elliptic_summable_of_two_lt_re E s hs, newform_summable_of_two_lt_re F s hs⟩

/-- **PROVED NON-VACUITY**, the line in Shimura's algebraic reading has a
nonzero canonical q-expansion and rational dimension one in its quotient.
Locators: Shimura 1973, Theorem 1(iii),(iv), p. 526. -/
theorem shimura_nonzero_line {M : ℕ} [NeZero M] (F : Newform M 2) (hχ : F.χ = 1)
    (S : ShimuraJacobianSetting M) (A : PkgI3.AbVar ℚ) (ν : PkgI3.AbVar.Hom S.J A)
    (θ : coefficientField F →+* A.End0) (h : IsShimuraRationalTriple F hχ S A ν θ)
    (hdim : A.dim = 1) :
    S.mu (gamma0Newform F hχ) ≠ 0 ∧
      Module.finrank ℚ (rationalAbelianDifferentials A) = 1 :=
  ⟨shimura_mu_newform_ne_zero F hχ S,
    shimura_rational_differentials_finrank F hχ S A ν θ h hdim⟩

end ZInQ.Contrib.RC53Assist.G0Prints
