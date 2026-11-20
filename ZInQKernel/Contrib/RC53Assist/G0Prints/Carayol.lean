import ZInQKernel.Contrib.RC53Assist.G0Prints.ShimuraDifferentials
import ZInQKernel.Contrib.RC53Assist.G0Prints.CarayolAnalytic
import ZInQKernel.Contrib.RC53Assist.G0Prints.SourceL

/-!
# Carayol's printed rational-newform corollary

The associated elliptic curve is the actual pointed Weierstrass presentation
of Shimura's one-dimensional quotient. Carayol's conclusion is equality of
the complete analytic L-functions and equality of the geometric conductors.
The geometric conductor is read from the cohomological Tate representation;
its identification with the minimal-model conductor is not asserted.

The local-polynomial consequence is proved by analytic Dirichlet-series
uniqueness and the two existing prime-power recurrences. Thus it does not
assume the local-polynomial equality it is meant to prove.

Locators: Carayol, Ann. Sci. ÉNS 19 (1986), §0.8, Corollaire, p. 411;
Shimura, J. Math. Soc. Japan 25 (1973), Theorem 1, p. 526;
bibliography keys `carayol` (TeX 11205–11208), `shimura-factors` (11053–11057).
-/

noncomputable section

set_option maxHeartbeats 800000
set_option autoImplicit false

namespace ZInQ.Contrib.RC53Assist.G0Prints

open UpperHalfPlane CongruenceSubgroup HeckeRing.GL2
open ZInQ.Contrib.RC53Assist.NewformGlueG0
open ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion
open ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent
open ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary
open ZInQ.Contrib.RC53Assist.GlobalTrace
open ZInQ.Contrib.RC53Assist.AbelianCurve
open scoped TensorProduct

/-- **DEFINITION**, the cohomological representation `H¹(E_{
  ℚ̄},ℚ_ℓ)` in its genuine Tate-module dual realization.
Geometric Frobenius on its inertia invariants gives the corrected
coinvariant polynomial with arithmetic Frobenius on `V_ℓ(E)`.
Locators: Carayol 1986, §0.8, p. 411, the proof paragraph;
`localTatePolynomialCoinv_eq_dual`. -/
def associatedCohomologicalRep (E : WeierstrassCurve ℚ) (ℓ : ℕ) [Fact ℓ.Prime] :
    Representation ℚ_[ℓ] GlueC10.GQ (Module.Dual ℚ_[ℓ] (rationalTate E ℓ)) :=
  (rationalTateRep E ℓ).dual

/-- **DEFINITION**, the genuine two-dimensional matrix representation of the
cohomological Tate module, by the dual of the actual rational Tate basis.
Locator: Carayol's natural Galois representation on `H¹`, p. 411. -/
def associatedCohomologicalMatrix (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime] : GlueC10.GQ →* GL (Fin 2) ℚ_[ℓ] := by
  let ρ := associatedCohomologicalRep E ℓ
  let b := (rationalTateBasis E ℓ).dualBasis
  exact
    { toFun := fun g =>
        ⟨LinearMap.toMatrix b b (ρ g), LinearMap.toMatrix b b (ρ g⁻¹), by
          rw [← LinearMap.toMatrix_mul, ← map_mul, mul_inv_cancel, map_one,
            LinearMap.toMatrix_one], by
          rw [← LinearMap.toMatrix_mul, ← map_mul, inv_mul_cancel, map_one,
            LinearMap.toMatrix_one]⟩
      map_one' := by
        apply Units.ext
        simp only [map_one, LinearMap.toMatrix_one, Units.val_one]
      map_mul' := fun g h => by
        apply Units.ext
        simp only [map_mul, LinearMap.toMatrix_mul, Units.val_mul] }

/-- **DEFINITION**, the geometric conductor of the associated elliptic curve
at `p ≠ ℓ`, in the existing Artin–Swan representation language. Coefficients
are extended to the actual algebraic closure of `ℚ_ℓ`.
Locator: Carayol 1986, §0.8, p. 411; the existing conductor definition. -/
def associatedGeometricConductorExponent (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime] (p : ℕ) [Fact p.Prime] : ℚ :=
  LadicCond.condExp
    (((Matrix.GeneralLinearGroup.map (algebraMap ℚ_[ℓ] (PadicAlgCl ℓ))).comp
      (associatedCohomologicalMatrix E ℓ)).comp (PkgI4.decomp p))

/-- **PROVED**, the cohomological invariant polynomial uses geometric, not
arithmetic, Frobenius. It equals the corrected local Tate coinvariant
polynomial, including ramified places.
Locators: Carayol §§0.4–0.8, pp. 409–411; the proved dual-coinvariant identity. -/
theorem associatedCohomological_local_factor (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime] {p : ℕ} (D : LocalArithmeticFrobenius p) :
    inertiaEulerPolynomial (associatedCohomologicalRep E ℓ) (inertiaAt D) D.element⁻¹
        (fun i hi => by simpa only [inv_inv] using inertiaAt_conj D i hi) =
      localTatePolynomialCoinv E ℓ D :=
  (localTatePolynomialCoinv_eq_dual E ℓ D).symm

/-- **PRINT**, Carayol 1986, §0.8, Corollaire, p. 411, with the associated
elliptic curve supplied by the genuine Shimura quotient and an actual pointed
Weierstrass presentation. The conclusion keeps both the analytic L-function
and geometric conductor equalities. No equality of minimal-reduction
polynomials is present. The conductor is read through the natural
cohomological Galois representation, not an arbitrary function of the curve.
Bibliography key `carayol`, TeX lines 11205–11208.

Verbatim printed text, p. 411:

0.8. APPLICATION. — Le théorème précédent, appliqué dans le cas particulier où F = Q
et k = 2, fournit facilement une réponse affirmative à une conjecture concernant les
courbes elliptiques de Weil :

COROLLAIRE. — Soit f ∈ S₂(Γ₀(N)) une nouvelle forme rationnelle, valeur propre normali-
sée des opérateurs de Hecke, et soit E_f la courbe elliptique sur Q associée à f. Alors la
fonction L de E_f est égale à L(f,s), et le conducteur géométrique de E_f est égal à N.

En effet, notons π la représentation automorphe attachée à f, et soit σ^λ la représentation
l-adique que le théorème associe à π. De la définition de E_f et du théorème de Čebotarev,
il résulte que σ^λ est isomorphe à la représentation naturelle de Galois sur l'espace
H¹(E_f ⊗ Q̄, Q_l). L'égalité des séries L découle de ce fait et du théorème. De même pour
l'égalité des conducteurs, compte tenu du travail de Ogg[Og].

Mathematics is transcribed with Unicode. Equality on `Re(s) > 2` is the
restriction of the printed equality to a proved common convergence domain;
Dirichlet-series uniqueness is proved in the separate reading theorem. -/
def Carayol1986CorollaireRational : Prop :=
  ∀ (M : ℕ) [NeZero M] (F : Newform M 2) (hχ : F.χ = 1),
    (∀ n : ℕ, ∃ b : ℚ, (qExpansion 1 F.toCuspForm).coeff n = (b : ℂ)) →
      ∀ (S : ShimuraJacobianSetting M) (A : PkgI3.AbVar ℚ)
        (ν : PkgI3.AbVar.Hom S.J A) (θ : coefficientField F →+* A.End0),
        IsShimuraRationalTriple F hχ S A ν θ →
        ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], IsWeierstrassPresentation A E →
          (∀ s : ℂ, 2 < s.re → sourceLSeries E s = newformL F s) ∧
          ∀ (ℓ : ℕ) [Fact ℓ.Prime] (p : ℕ) [Fact p.Prime], p ≠ ℓ →
            associatedGeometricConductorExponent E ℓ p = (M.factorization p : ℚ)

/-- **PROVED FROM THE PRINT, GEOMETRIC READING AND CORRECTED BAD READING**,
the exact existing G0 rational-newform field. The named geometric interface
supplies the algebraic reading of Shimura's clause (iv); its canonical
comparison with the printed holomorphic spaces is still open.
Injectivity of actual sheaf pullback gives dimension one, and Riemann–Roch
constructs the pointed Weierstrass presentation through proved dictionaries.
Carayol supplies complete source L-function equality; the Tate-to-minimal
and analytic-to-local readings are proved. No independent tangent-duality
or invariant-sheaf trivialization hypothesis is used by this reduction.
Locators: Shimura Theorem 1, p. 526; Carayol §0.8, p. 411;
Silverman III.3.1; Li 1975, Theorem 3(i), p. 295. -/
theorem Carayol1986RationalNewformEulerFactors_of_print_of_geometricReading_of_badReading
    (hB : BadReductionTatePolynomialReadingCoinv) :
    Shimura1973RationalGeometricReading → Carayol1986CorollaireRational →
      Carayol1986RationalNewformEulerFactors := by
  intro hS hC M _ F hχ hrat
  obtain ⟨S, A, ν, θ, htriple, hdim⟩ := hS.dimension_one M F hχ hrat
  obtain ⟨E, hE, hmodel⟩ :=
    weierstrassPresentation_of_shimura_triple F hχ S A ν θ htriple hdim
  let : E.IsElliptic := hE
  have hsource := (hC M F hχ hrat S A ν θ htriple E hmodel).1
  have hL : ∀ s : ℂ, 2 < s.re → E.LSeries s = newformL F s := by
    intro s hs
    rw [← sourceLSeries_eq_LSeries hB E s]
    exact hsource s hs
  exact ⟨E, hE, fun p hp => localPolynomial_eq_newform_of_complete_L E F hχ hL p hp⟩

/-- **PROVED FROM THE PRINT, GEOMETRIC READING AND THREE BAD-PRIME INPUTS**,
the exact existing rational-newform field. The geometric interface is
explicitly GLUE; it is not a replacement name for a literal Shimura print.
The complete source L-function uses genuine cohomological Tate factors.
Its minimal-model reading uses the good-prime proofs and only the three
existing bad-prime hypotheses. The analytic-to-local step is proved.
Locators: Shimura pp. 524–526; Carayol p. 411; Silverman Appendix C §§14 and 16. -/
theorem Carayol1986RationalNewformEulerFactors_of_print_of_geometricReading
    (hT : TateCurveTateModulePrint) (hLG : DecompositionGroupLocalGlobalGlue)
    (hA : AdditiveReductionCoinvariantsVanish) :
    Shimura1973RationalGeometricReading → Carayol1986CorollaireRational →
      Carayol1986RationalNewformEulerFactors :=
  Carayol1986RationalNewformEulerFactors_of_print_of_geometricReading_of_badReading
    (badReductionTatePolynomialReadingCoinv_of_inputs hT hLG hA)

/-- **PROVED CONDITIONAL PRINT READING**, the unchanged destination field
from Carayol's Corollaire. The remaining Shimura realization is explicitly
named as a geometric source reading; it is not relabeled PRINT. The three
bad-prime inputs are the existing ones, consumed without restatement.
Locators: Carayol §0.8, p. 411; Shimura Theorem 1, p. 526. -/
theorem Carayol1986RationalNewformEulerFactors_of_print
    (hT : TateCurveTateModulePrint) (hLG : DecompositionGroupLocalGlobalGlue)
    (hA : AdditiveReductionCoinvariantsVanish)
    (hS : Shimura1973RationalGeometricReading) :
    Carayol1986CorollaireRational → Carayol1986RationalNewformEulerFactors :=
  Carayol1986RationalNewformEulerFactors_of_print_of_geometricReading hT hLG hA hS

/-- **PROVED NON-VACUITY**, the analytic equality is genuinely a relation
between summable Dirichlet series, not equality of totalized divergent sums.
Both abscissae are finite for every elliptic curve and genuine newform.
Locators: Hecke's bound, Silverman V.1.1, Carayol 1986, p. 411. -/
theorem carayol_analytic_nonvacuity (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {M : ℕ} [NeZero M] (F : Newform M 2) :
    LSeries.abscissaOfAbsConv (fun n : ℕ => (E.LFunction n : ℂ)) < ⊤ ∧
      LSeries.abscissaOfAbsConv (fun n : ℕ => (qExpansion 1 F.toCuspForm).coeff n) < ⊤ :=
  ⟨elliptic_abscissa_lt_top E, newform_abscissa_lt_top F⟩

end ZInQ.Contrib.RC53Assist.G0Prints
