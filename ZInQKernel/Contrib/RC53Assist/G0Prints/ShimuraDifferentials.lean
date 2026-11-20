import ZInQKernel.Contrib.RC53Assist.G0Prints.QuotientDifferentials

/-!
# The geometric reading of Shimura's actual quotient

The dimension of the quotient's global differential space is proved from
Theorem 1(iv): its actual pullback is injective and has the printed
one-dimensional image. No tangent–differential comparison, GAGA assertion,
invariant-sheaf trivialization, or assumed Weierstrass model is a hypothesis.

The proved regular Kähler–Weil comparison gives genus one. Riemann–Roch at
the actual rational identity then constructs a pointed nonsingular
Weierstrass presentation over the rationals.

Locators: Shimura 1973, Theorem 1(i),(iii),(iv), p. 526;
Silverman II.4–5 and III.3.1; Stacks Tags 01UM and 00S2.
Bibliography key `shimura-factors`, TeX lines 11053–11057.
-/

noncomputable section

set_option maxHeartbeats 800000
set_option autoImplicit false

namespace ZInQ.Contrib.RC53Assist.G0Prints

open AlgebraicGeometry CategoryTheory Module
open UpperHalfPlane CongruenceSubgroup HeckeRing.GL2
open ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent
open ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary
open ZInQ.Contrib.RC53Assist.AbelianCurve
open ZInQ.Contrib.RC53Assist.AbelianCurveInputs
open ZInQ.Contrib.RC53Assist.InvariantDifferential
open ZInQ.Contrib.RC53Assist.IsogenyScheme

/-- **PROVED NON-VACUITY**, the genuine converted newform is nonzero because
its first Fourier coefficient is one. Locator: Shimura p. 526, normalization. -/
theorem gamma0Newform_ne_zero {M : ℕ} [NeZero M]
    (F : Newform M 2) (hχ : F.χ = 1) : gamma0Newform F hχ ≠ 0 := by
  have hc : (qExpansion 1 (gamma0Newform F hχ)).coeff 1 = 1 :=
    (gamma0Newform_coeff F hχ 1).trans F.isNorm
  intro hz
  simp only [hz, FunLike.coe_zero, UpperHalfPlane.qExpansion_zero,
    map_zero, zero_ne_one] at hc

/-- **PROVED NON-VACUITY**, the printed image vector is nonzero in the actual
differential space, not a formal label. Locator: Shimura Theorem 1(iv), p. 526. -/
theorem shimura_mu_newform_ne_zero {M : ℕ} [NeZero M]
    (F : Newform M 2) (hχ : F.χ = 1) (S : ShimuraJacobianSetting M) :
    S.mu (gamma0Newform F hχ) ≠ 0 := by
  intro hz
  exact gamma0Newform_ne_zero F hχ (S.mu.injective (hz.trans (S.mu.map_zero).symm))

/-- **PROVED FROM THE ACTUAL TRIPLE**, the global regular differential space
of the one-dimensional quotient has rational dimension one. Injectivity of
actual sheaf pullback is proved from dominance and characteristic zero;
the image is the nonzero line printed in clause (iv).
Locator: Shimura 1973, Theorem 1(i),(iii),(iv), p. 526. -/
theorem shimura_rational_differentials_finrank {M : ℕ} [NeZero M]
    (F : Newform M 2) (hχ : F.χ = 1) (S : ShimuraJacobianSetting M)
    (A : PkgI3.AbVar ℚ) (ν : PkgI3.AbVar.Hom S.J A)
    (θ : coefficientField F →+* A.End0) (h : IsShimuraRationalTriple F hχ S A ν θ)
    (hdim : A.dim = 1) : Module.finrank ℚ (rationalAbelianDifferentials A) = 1 := by
  have hinj := shimuraDelta_injective ν h.quotient.1 hdim
  let e : shimuraDB A ≃ₗ[ℂ] (shimuraDelta ν).range :=
    LinearEquiv.ofBijective (shimuraDelta ν).rangeRestrict
      ⟨fun x y hxy => hinj (congrArg Subtype.val hxy),
        LinearMap.surjective_rangeRestrict (shimuraDelta ν)⟩
  have hr : Module.finrank ℂ (shimuraDelta ν).range = 1 := by
    rw [h.differential_image]
    exact finrank_span_singleton (shimura_mu_newform_ne_zero F hχ S)
  have hd := e.finrank_eq.trans hr
  rw [Module.finrank_baseChange] at hd
  exact hd

/-- **PROVED GEOMETRIC READING**, the actual quotient's function field has
genus one. The regular Kähler–Weil comparison is already proved; it is not
supplied as a dimension map or source reading.
Locators: Shimura Theorem 1(iv), p. 526; Silverman II.4–5. -/
theorem shimura_quotient_genus_one {M : ℕ} [NeZero M]
    (F : Newform M 2) (hχ : F.χ = 1) (S : ShimuraJacobianSetting M)
    (A : PkgI3.AbVar ℚ) (ν : PkgI3.AbVar.Hom S.J A)
    (θ : coefficientField F →+* A.End0) (h : IsShimuraRationalTriple F hχ S A ν θ)
    (hdim : A.dim = 1) :
    letI := abelian_scheme_integral A.X
    letI := functionFieldAlgebra A.X.hom
    TauCeti.genus ℚ A.X.left.functionField = 1 := by
  let := abelian_scheme_integral A.X
  letI := functionFieldAlgebra A.X.hom
  letI := globalSectionsModule A.X.hom (differentialSheaf A.X.hom)
  obtain ⟨e⟩ := LocalFacts.regularDifferentialComparison A.X.left A.X.hom hdim
  rw [← TauCeti.finrank_weilDifferentialFiltration_zero
    (isFunctionField_of_dimension_one A.X.hom hdim)
    (functionField_exact_constants A.X.hom), ← e.finrank_eq]
  exact shimura_rational_differentials_finrank F hχ S A ν θ h hdim

/-- **PROVED GEOMETRIC READING**, Riemann–Roch at the actual degree-one
identity place constructs a nonsingular Weierstrass presentation of the
printed quotient. The scheme isomorphism is over the rationals and sends
the genuine identity to the point at infinity.
Locators: Shimura Theorem 1, p. 526; Silverman II.5 and III.3.1. -/
theorem weierstrassPresentation_of_shimura_triple {M : ℕ} [NeZero M]
    (F : Newform M 2) (hχ : F.χ = 1) (S : ShimuraJacobianSetting M)
    (A : PkgI3.AbVar ℚ) (ν : PkgI3.AbVar.Hom S.J A)
    (θ : coefficientField F →+* A.End0) (h : IsShimuraRationalTriple F hχ S A ν θ)
    (hdim : A.dim = 1) :
    ∃ E : WeierstrassCurve ℚ, E.IsElliptic ∧ IsWeierstrassPresentation A E := by
  let := abelian_scheme_integral A.X
  letI := functionFieldAlgebra A.X.hom
  obtain ⟨W, hW, e, hx, _, _, _⟩ := exists_weierstrassModel_of_genus_eq_one
    (isFunctionField_of_dimension_one A.X.hom hdim)
    (functionField_exact_constants A.X.hom)
    (shimura_quotient_genus_one F hχ S A ν θ h hdim) (smoothIdentityPlace_degree A.X hdim)
  let E := W.toAffine
  let : E.IsElliptic := hW
  let := projectiveStructure_proper E
  let er := (projFunctionFieldEquiv E).trans e.toRingEquiv
  obtain ⟨i, hi, hη⟩ := isomorphism_of_functionField_equiv A.X.hom (projectiveStructure E)
    (smooth_curve_valuation_stalk A.X.hom hdim) (projective_valuation_stalk E) er
  have hfield : i.hom.functionFieldMap.hom =
      e.toRingHom.comp (projFunctionFieldEquiv E).toRingHom :=
    congrArg CommRingCat.Hom.hom (isomorphism_functionFieldMap er i hη)
  exact ⟨E, hW, i, hi, comparison_sends_identity A.X hdim E e.toRingEquiv i hfield hx⟩

end ZInQ.Contrib.RC53Assist.G0Prints
