import ZInQKernel.Contrib.RC53Assist.G0Prints.CuspReading
import ZInQKernel.HDecomp.ModCurves.Defs

/-!
# Shimura's actual quotient, endomorphisms, and differentials

The quotient is an abelian variety as a proper smooth geometrically integral
group scheme. Its map from the Jacobian is a genuine homomorphism of group
schemes, and the coefficient field acts on its actual rational endomorphism
algebra. The Hecke relations are equalities of rationalized scheme morphisms,
not an assumed equality of Fourier coefficients with an elliptic curve.

The differential space is the complex scalar extension of the genuine
rational global relative differential sections. For proper smooth varieties
this is the algebraic realization of Shimura's holomorphic differential
space. The pullback is the actual universal-derivation sheaf pullback.

Only the rational-coefficient algebraic reading of the geometric clauses
(i)–(iv) of Theorem 1 is used. The zeta clause and uniqueness assertion are
quoted, but are not formal fields. The canonical comparison of these
complexified algebraic sections with Shimura's holomorphic forms is not
proved, so the interface remains GLUE. No Weierstrass curve or equality
of local factors occurs in that interface.

Locators: Shimura, J. Math. Soc. Japan 25 (1973), pp. 525–527, Theorem 1;
bibliography key `shimura-factors`, TeX lines 11053–11057.
-/

noncomputable section

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ZInQ.Contrib.RC53Assist.G0Prints

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory
open CartesianMonoidalCategory MonObj UpperHalfPlane CongruenceSubgroup HeckeRing.GL2
open scoped TensorProduct WithZero
open ZInQ.Contrib.RC53Assist.NewformGlueG0
open ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent
open ZInQ.Contrib.RC53Assist.NewformPeriods
open ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary
open ZInQ.Contrib.RC53Assist.AbelianCurve
open ZInQ.Contrib.RC53Assist.AbelianCurveInputs

/-- **DEFINITION**, rational global regular differentials on the actual abelian
variety. Locator: Shimura 1973, pp. 524–525, `D_B`, algebraic realization. -/
abbrev rationalAbelianDifferentials (A : PkgI3.AbVar ℚ) : Type :=
  Γ(differentialSheaf A.X.hom, ⊤)

/-- **DEFINITION**, the rational scalar structure supplied by the actual
structure map. Locator: rational global relative differential sections. -/
instance rationalAbelianDifferentials_module (A : PkgI3.AbVar ℚ) :
    Module ℚ (rationalAbelianDifferentials A) :=
  globalSectionsModule A.X.hom (differentialSheaf A.X.hom)

/-- **DEFINITION**, the complex differential space of the proper rational
abelian variety, in its algebraic realization by scalar extension.
Locator: Shimura 1973, pp. 524–525, `D_B`. -/
abbrev shimuraDB (A : PkgI3.AbVar ℚ) : Type :=
  ℂ ⊗[ℚ] rationalAbelianDifferentials A

/-- **DEFINITION**, `δν`, the scalar extension of the actual sheaf pullback of
global differential sections, using the relative universal derivation.
Locator: Shimura 1973, p. 525, (1.1), (1.3); relative differential pullback. -/
def shimuraDelta {J A : PkgI3.AbVar ℚ} (ν : PkgI3.AbVar.Hom J A) :
    shimuraDB A →ₗ[ℂ] shimuraDB J := by
  letI : IsIntegral J.X.left := abelian_scheme_integral J.X
  letI : IsIntegral A.X.left := abelian_scheme_integral A.X
  exact (globalDifferentialPullback J.X.hom A.X.hom ν.hom.left ν.hom.w).baseChange ℂ

/-- **DEFINITION**, postcomposition with the actual quotient morphism, as an
integer-linear map on genuine homomorphisms of abelian varieties.
Locator: Shimura 1973, Theorem 1(ii), p. 526, `θ(a_n) ∘ ν`. -/
def postcomposeQuotient {J A : PkgI3.AbVar ℚ} (ν : PkgI3.AbVar.Hom J A) :
    PkgI3.AbVar.End A →ₗ[ℤ] PkgI3.AbVar.Hom J A :=
  (AddMonoidHom.mk' (fun f : PkgI3.AbVar.End A =>
    PkgI3.AbVar.Hom.mk' (ν.hom ≫ f.hom)) (by
      intro f g
      apply PkgI3.AbVar.Hom.ext'
      simp only [PkgI3.AbVar.Hom.hom_mk', PkgI3.AbVar.Hom.hom_add, MonObj.comp_mul]
    )).toIntLinearMap

/-- **DEFINITION**, rationalized composition `End(A) ⊗ ℚ → Hom(J,A) ⊗ ℚ`.
Locator: Shimura 1973, Theorem 1(ii), p. 526. -/
def postcomposeQuotientQ {J A : PkgI3.AbVar ℚ} (ν : PkgI3.AbVar.Hom J A) :
    A.End0 →ₗ[ℚ] (ℚ ⊗[ℤ] PkgI3.AbVar.Hom J A) :=
  (postcomposeQuotient ν).baseChange ℚ

/-- **DEFINITION**, a quotient by an actual abelian subvariety. The kernel
square is a scheme-theoretic pullback, with a closed subgroup immersion;
`ν` is surjective. No abstract label stands for the quotient.
Locator: Shimura 1973, p. 525, the definition of `(A,ν) = J/C`. -/
def IsAbelianQuotient (J A : PkgI3.AbVar ℚ) (ν : PkgI3.AbVar.Hom J A) : Prop :=
  Surjective ν.hom.left ∧
    ∃ (C : PkgI3.AbVar ℚ) (j : PkgI3.AbVar.Hom C J),
      IsClosedImmersion j.hom.left ∧
        IsPullback j.hom (toUnit C.X) ν.hom η[A.X]

/-- **DEFINITION**, the actual `Γ₀(M)` form underlying a trivial-character
newform, by the proved subgroup equivalence. Locator: `S₂(Γ₀(M))` in Shimura. -/
def gamma0Newform {M : ℕ} [NeZero M] (F : Newform M 2) (hχ : F.χ = 1) :
    CuspForm (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) 2 :=
  TauCeti.cuspFormCharSpaceOneEquiv M 2 ⟨F.toCuspForm, hχ ▸ F.mem_charSpace⟩

/-- **PROVED**, the subgroup conversion does not change any Fourier
coefficient. Locator: the function-preserving trivial-character equivalence. -/
theorem gamma0Newform_coeff {M : ℕ} [NeZero M] (F : Newform M 2)
    (hχ : F.χ = 1) (n : ℕ) :
    (qExpansion 1 (gamma0Newform F hχ)).coeff n =
      (qExpansion 1 F.toCuspForm).coeff n := by
  have h := TauCeti.coe_cuspFormCharSpaceOneEquiv_apply
    (⟨F.toCuspForm, hχ ▸ F.mem_charSpace⟩ : cuspFormCharSpace 2
      (1 : (ZMod M)ˣ →* ℂˣ))
  change (qExpansion 1 (TauCeti.cuspFormCharSpaceOneEquiv M 2 _)).coeff n = _
  rw [h]

/-- **PROVED**, the converted form is normalized and is a common eigenfunction
of every printed Hecke operator, not merely the good-prime operators.
Locator: Shimura 1973, p. 526, the hypothesis of Theorem 1. -/
theorem gamma0Newform_isCommonEigenform {M : ℕ} [NeZero M] (F : Newform M 2)
    (hχ : F.χ = 1) : IsShimuraCommonEigenform M (gamma0Newform F hχ) := by
  apply normalizedFullEigenform_isShimuraEigenform
  refine ⟨?_, F.toEigenform, ?_, ?_⟩
  · rw [gamma0Newform_coeff]
    exact F.isNorm
  · simpa only [Newform.toEigenform_χ] using hχ
  · intro τ
    rw [Newform.toEigenform_toCuspForm]
    exact (congrFun (TauCeti.coe_cuspFormCharSpaceOneEquiv_apply
      (⟨F.toCuspForm, hχ ▸ F.mem_charSpace⟩ : cuspFormCharSpace 2
        (1 : (ZMod M)ˣ →* ℂˣ))) τ).symm

/-- **DEFINITION**, the specified q-expansion embedding of the actual
modular function field, followed by inclusion in rational Laurent series.
Its rational scalar compatibility follows from the function-field
isomorphism; no extra scalar-tower instance is selected by typeclass search.
Locator: Shimura 1973, p. 525, the q-coordinate at the rational cusp. -/
def modularQExpansionEmbedding (M : ℕ) [NeZero M]
    (X : Over (Spec (.of ℚ))) [IsIntegral X.left]
    (e : X.left.functionField ≃+* modularFunctionFieldQ M) :
    letI := functionFieldAlgebra X.hom;
    X.left.functionField →ₐ[ℚ] LaurentSeries ℚ := by
  letI := functionFieldAlgebra X.hom
  let φ : X.left.functionField →+* LaurentSeries ℚ :=
    (modularFunctionFieldQ M).toSubfield.subtype.comp e.toRingHom
  exact { φ with commutes' := fun r => RingHom.map_rat_algebraMap φ r }

/-- **DEFINITION OF THE ALGEBRAIC SETTING**, a smooth proper rational model with
function field `ℚ(j,j_M)`, its rational base point and actual Jacobian, and the
actual endomorphisms `ξ_n` read through the differential isomorphism `μ`.
The Hecke action is the proved action on the genuine cusp-form space.
Locators: Shimura 1973, p. 525, (1.3), and the final paragraph defining `ξ_n`;
p. 526, the rational standard model. -/
structure ShimuraJacobianSetting (M : ℕ) [NeZero M] where
  /-- **DATA**, the smooth proper modular curve. Locator: Shimura p. 525. -/
  X : Over (Spec (.of ℚ))
  /-- **PROPERTY**, the actual smooth proper curve conditions. Locator: Shimura p. 525. -/
  curve : LeafModCurves.IsCurve X
  /-- **PROPERTY**, the actual integral model. Locator: Shimura p. 526. -/
  integral : IsIntegral X.left
  /-- **DATA**, its rational base point. Locator: the canonical Jacobian map, p. 525. -/
  basePoint : LeafModCurves.RatPt X
  /-- **DATA**, the specified rational q-expansion of the standard model.
  Locator: Shimura p. 525, the parameter `z` at the rational cusp. -/
  functionField :
    letI := integral
    letI := functionFieldAlgebra X.hom
    X.left.functionField ≃+* modularFunctionFieldQ M
  /-- **PROPERTY**, the base point is the actual rational cusp of this
  q-expansion: its local ring and maximal ideal give the q-adic unit ball
  and open unit ball, respectively. Locator: the canonical map at the cusp,
  Shimura p. 525. -/
  cusp :
    letI := integral
    letI := functionFieldAlgebra X.hom
    let x := basePoint.left (IsLocalRing.closedPoint ℚ)
    let κ := modularQExpansionEmbedding M X functionField
    ∀ a : X.left.functionField,
      ((Valued.v : Valuation (LaurentSeries ℚ) ℤᵐ⁰) (κ a) ≤ 1 ↔
        ∃ b : X.left.presheaf.stalk x, algebraMap _ X.left.functionField b = a) ∧
      ((Valued.v : Valuation (LaurentSeries ℚ) ℤᵐ⁰) (κ a) < 1 ↔
        ∃ b : X.left.presheaf.stalk x, b ∈ IsLocalRing.maximalIdeal _ ∧
          algebraMap _ X.left.functionField b = a)
  /-- **DATA**, the genuine rational Jacobian. Locator: Shimura p. 525, `J`. -/
  J : PkgI3.AbVar ℚ
  /-- **DATA**, the Abel–Jacobi morphism. Locator: Shimura p. 525, `ψ`. -/
  aj : X ⟶ J.X
  /-- **PROPERTY**, the actual Jacobian universal property. Locator: Shimura p. 525. -/
  jacobian : LeafModCurves.IsJacobian X basePoint J aj
  /-- **DATA**, the genuine Hecke endomorphisms. Locator: Shimura p. 525, `ξ_n`. -/
  xi : ℕ → PkgI3.AbVar.End J
  /-- **DATA**, the differential isomorphism. Locator: Shimura p. 525, `μ`. -/
  mu : CuspForm (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) 2 ≃ₗ[ℂ] shimuraDB J
  /-- **PROPERTY**, the literal normalization `δψ(μ(f)) = f(z) dz`,
  through the actual Abel–Jacobi pullback and the specified q-expansion.
  Since `dq/q = 2πi dz`, the value is `f(q)/(2πi)`.
  Locator: Shimura p. 525, the definition of `μ`. -/
  mu_normalization :
    letI := integral
    letI := functionFieldAlgebra X.hom
    let κ := modularQExpansionEmbedding M X functionField
    ∀ f : CuspForm (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) 2,
      jacobianEulerReadingC X J aj κ (mu f) =
        (2 * Real.pi * Complex.I)⁻¹ • HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 f)
  /-- **PROPERTY**, the actual Hecke differential relation. Locator: Shimura p. 525, (1.3). -/
  hecke : ∀ n : ℕ+, (shimuraDelta (xi n)) ∘ₗ mu.toLinearMap =
    mu.toLinearMap ∘ₗ heckeGamma0 M n

/-- **DEFINITION OF THE ALGEBRAIC TRIPLE**, the rational reading of
(i)–(iv): actual quotient, actual coefficient-field endomorphisms, the exact
Hecke relation, dimension equal to the coefficient-field degree, and the
actual differential pullback image. No Tate or Weierstrass conclusion occurs.
Locator: Shimura 1973, Theorem 1, p. 526. -/
structure IsShimuraRationalTriple {M : ℕ} [NeZero M] (F : Newform M 2)
    (hχ : F.χ = 1) (S : ShimuraJacobianSetting M) (A : PkgI3.AbVar ℚ)
    (ν : PkgI3.AbVar.Hom S.J A) (θ : coefficientField F →+* A.End0) : Prop where
  /-- **PRINTED (i)**, the quotient by an abelian subvariety over `ℚ`. -/
  quotient : IsAbelianQuotient S.J A ν
  /-- **PRINTED (ii)**, the coefficient field embeds in the actual endomorphism algebra. -/
  theta_injective : Function.Injective θ
  /-- **PRINTED (ii)**, equality of actual rationalized scheme homomorphisms. -/
  theta_hecke : ∀ n : ℕ+,
    (1 : ℚ) ⊗ₜ[ℤ] PkgI3.AbVar.Hom.mk' ((S.xi n).hom ≫ ν.hom) =
      postcomposeQuotientQ ν (θ ⟨(qExpansion 1 F.toCuspForm).coeff n, coeff_mem F n⟩)
  /-- **PRINTED (iii)**, dimension of the actual abelian variety. -/
  dimension : A.dim = (Module.finrank ℚ (coefficientField F) : WithBot ℕ∞)
  /-- **PRINTED (iv)**, the singleton embedding case of the differential image formula. -/
  differential_image : (shimuraDelta ν).range =
    Submodule.span ℂ {S.mu (gamma0Newform F hχ)}

/-- **PROVED**, a rational-coefficient newform has exactly the rational
coefficient subfield. No almost-all agreement or descent print is needed.
Locator: Shimura's field `K`, p. 526; the definition by coefficient generators. -/
theorem coefficientField_eq_bot_of_rational {M : ℕ} [NeZero M]
    (F : Newform M 2)
    (hrat : ∀ n : ℕ, ∃ b : ℚ, (qExpansion 1 F.toCuspForm).coeff n = (b : ℂ)) :
    coefficientField F = ⊥ := by
  apply bot_unique
  rw [coefficientField, IntermediateField.adjoin_le_iff]
  rintro _ ⟨n, rfl⟩
  obtain ⟨b, hb⟩ := hrat n
  exact IntermediateField.mem_bot.mpr ⟨b, hb.symm⟩

/-- **PROVED**, its coefficient-field degree is one, justifying the exact
rational specialization of (iii) and the singleton case in (iv).
Locator: Shimura 1973, Theorem 1, p. 526, `[K:ℚ]`. -/
theorem coefficientField_finrank_of_rational {M : ℕ} [NeZero M]
    (F : Newform M 2)
    (hrat : ∀ n : ℕ, ∃ b : ℚ, (qExpansion 1 F.toCuspForm).coeff n = (b : ℂ)) :
    Module.finrank ℚ (coefficientField F) = 1 := by
  rw [coefficientField_eq_bot_of_rational F hrat]
  exact (IntermediateField.botEquiv ℚ ℂ).toLinearEquiv.finrank_eq.trans
    (Module.finrank_self ℚ)

/-- **GLUE, ALGEBRAIC SOURCE READING**, Shimura 1973, Theorem 1, p. 526,
(i)–(iv), with the Jacobian and differential setting on p. 525. The actual
quotient and Hecke homomorphisms are retained. The differential spaces here
are scalar extensions of rational global algebraic differential sections.
The canonical comparison with the printed holomorphic spaces has not been
proved. This interface is therefore not classified as a literal PRINT.
Uniqueness and the final zeta clause are quoted but are not formal fields.
The Lean statement contains no Weierstrass presentation or local-factor
conclusion. Bibliography key `shimura-factors`, TeX lines 11053–11057.

Verbatim printed text, p. 525 (setting):

By a quotient of B by an abelian subvariety, say C, of B, we understand
a couple (A, ν) formed by an abelian variety A which canonically represents
B/C and a natural map ν: B → A with C = Ker(ν) (cf. Chow [3]).

Let Γ be a group of level N, and J the jacobian variety of ℌ*/Γ. Let
ψ: ℌ* → J be the map obtained by composing the natural map ℌ* → ℌ*/Γ with
a canonical map of ℌ*/Γ into J. Then there is an isomorphism μ: S₂(Γ) → D_J
defined by δψ(μ(f)) = f(z)dz for f ∈ S₂(Γ), where δψ is the “pull back” asso-
ciated with ψ, and z is a standard variable on ℌ.

For a positive integer n, let q be the largest divisor of n prime to N, and
put n = mq. Then we define T_n and ξ_n by T_n = T_m T_q, ξ_n = ξ_m ξ_q,
T_m = [ΓαΓ]₂, ξ_m = {ΓαΓ} with α = [1 0; 0 m], and T_q = ∑_β [ΓβΓ]₂,
ξ_q = ∑_β {ΓβΓ}, where ∑_β is extended over all distinct ΓβΓ with det(β) = q,
β ≡ [1 0; 0 q] (mod N). Then μ ∘ T_n = δξ_n ∘ μ.

Verbatim printed text, p. 526 (theorem):

As shown in [11, §7.3], there is a “standard model” of ℌ*/Γ defined
over Q (see also §4 below), so that J can naturally be defined over Q. Let
f(z) = ∑_{n=1}^∞ a_n e^{2πinz}, with a₁ = 1, be an element of S₂(Γ), that is a common eigen-
function of T_n for all n (i. e., f | T_n = a_n f). Fix f, and let K be the subfield
of C generated over Q by the complex numbers a_n for all n. (Of course K
depends on f.) Then we have

THEOREM 1. There exists a triple (A, ν, θ) formed by the objects satisfying
the following conditions:
(i) (A, ν) is a quotient of J by an abelian subvariety rational over Q.
(ii) θ is an isomorphism of K into End(A) ⊗ Q such that ν ∘ ξ_n = θ(a_n) ∘ ν
for all n. (This implies especially θ(1) = id_A.)
(iii) dim(A) = [K: Q].
Moreover, let I denote the set of all isomorphisms of K into C. Then, for every
σ ∈ I, there exists an element f_σ of S₂(Γ) such that f_σ | T_n = a_n^σ f for all n, and
f_σ(z) = ∑_{n=1}^∞ a_n^σ e^{2πinz}. With these f_σ, one has
(iv) δν(D_A) = μ(∑_{σ∈I} Cf_σ).
Under the conditions (i, ii), the triple (A, ν, θ) is unique up to isomorphisms
over Q. Furthermore, the one-dimensional part of the zeta function of A over
Q coincides, up to finitely many Euler factors for bad primes, with
∏_{σ∈I}(∑_{n=1}^∞ a_n^σ n^{−s}), provided that Γ = Γ₀(N), or
∑_{σ∈I} Cf_σ is stable under the map h(z) ↦ h(−1/Nz)/z².

The printed final `f` in the conjugate eigenrelation is retained above. The
proof on p. 527 reads it as `f_σ`; in the rational specialization `σ = id`,
so the distinction disappears. Mathematics is transcribed with Unicode. -/
def Shimura1973RationalGeometricReading : Prop :=
  ∀ (M : ℕ) [NeZero M] (F : Newform M 2) (hχ : F.χ = 1),
    (∀ n : ℕ, ∃ b : ℚ, (qExpansion 1 F.toCuspForm).coeff n = (b : ℂ)) →
      ∃ (S : ShimuraJacobianSetting M) (A : PkgI3.AbVar ℚ)
        (ν : PkgI3.AbVar.Hom S.J A) (θ : coefficientField F →+* A.End0),
        IsShimuraRationalTriple F hχ S A ν θ

/-- **PROVED**, the source reading produces an actual one-dimensional abelian variety,
with all its quotient data retained. It is not a Weierstrass existence input.
Locator: Shimura 1973, Theorem 1(iii), p. 526. -/
theorem Shimura1973RationalGeometricReading.dimension_one
    (hS : Shimura1973RationalGeometricReading) (M : ℕ) [NeZero M]
    (F : Newform M 2) (hχ : F.χ = 1)
    (hrat : ∀ n : ℕ, ∃ b : ℚ, (qExpansion 1 F.toCuspForm).coeff n = (b : ℂ)) :
    ∃ (S : ShimuraJacobianSetting M) (A : PkgI3.AbVar ℚ)
      (ν : PkgI3.AbVar.Hom S.J A) (θ : coefficientField F →+* A.End0),
      IsShimuraRationalTriple F hχ S A ν θ ∧ A.dim = 1 := by
  obtain ⟨S, A, ν, θ, h⟩ := hS M F hχ hrat
  refine ⟨S, A, ν, θ, h, ?_⟩
  rw [h.dimension, coefficientField_finrank_of_rational F hrat]
  rfl

/-- **DEFINITION**, a pointed projective Weierstrass presentation of the
actual one-dimensional abelian variety. It includes an actual isomorphism of
schemes over `ℚ`, carrying the group identity to the point at infinity.
Locator: Silverman III.3.1; Shimura's `A`, Theorem 1, p. 526. -/
def IsWeierstrassPresentation (A : PkgI3.AbVar ℚ) (E : WeierstrassCurve ℚ) : Prop :=
  ∃ i : A.X.left ≅ Proj E.toProjective.grading,
    i.hom ≫ projectiveStructure E = A.X.hom ∧
      i.hom (identityPoint A.X) = ZInQ.Contrib.RC53Assist.IsogenyScheme.pointO E

/-- **PROVED NON-VACUITY**, the source reading's output cannot be the zero abelian
variety: it has dimension one. This witnesses a genuine positive-dimensional
scheme whenever the printed rational-newform premise is supplied.
Locator: Shimura 1973, Theorem 1(iii), p. 526. -/
theorem shimura_reading_nonzero_output (hS : Shimura1973RationalGeometricReading)
    (M : ℕ) [NeZero M] (F : Newform M 2) (hχ : F.χ = 1)
    (hrat : ∀ n : ℕ, ∃ b : ℚ, (qExpansion 1 F.toCuspForm).coeff n = (b : ℂ)) :
    ∃ A : PkgI3.AbVar ℚ, A.dim = 1 ∧ A.dim ≠ 0 := by
  obtain ⟨_, A, _, _, _, hdim⟩ := hS.dimension_one M F hχ hrat
  exact ⟨A, hdim, by rw [hdim]; norm_num⟩

end ZInQ.Contrib.RC53Assist.G0Prints
