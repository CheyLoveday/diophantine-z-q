# G0 local factors: exact reductions and the remaining source boundary

## Result

**B1 is reduced to the printed Faltings implication and the three previously named bad-prime inputs.**
Its destination is exactly `NewformGlueG0.Descent.Faltings1983EulerFactorRigidityQ`.

**B2 has a proved exact-destination reduction, but not a literal-PRINT-only closure.**
Its additional `Shimura1973RationalGeometricReading` is explicitly classified **GLUE**, not PRINT.
The canonical realization of Shimura's holomorphic differential spaces in the algebraic objects
used by that interface remains unproved. The final source does not call this gap a PRINT.

All ten new Lean modules build. The build includes the explicit common-domain summability
proofs. The audited declarations use only `propext`, `Classical.choice`,
and `Quot.sound`; literature propositions and bad-prime inputs remain explicit hypotheses,
not new axioms or unconditional proofs of the destination propositions.


All Lean source files are new files under `ZInQKernel/Contrib/RC53Assist/G0Prints/`.
No existing source or destination definition was edited.

## 1. B1: Faltings's printed iii ⇒ iv

### Genuine objects

`RationalPlace` is the height-one spectrum of the actual ring of integers of ℚ.
`LocalArithmeticFrobenius p` contains an actual valuation subring of ℚ̄, a genuine Galois
arithmetic Frobenius, its residue action, and its integral-closure Frobenius property.

The printed polynomial and reciprocal factor are:

```lean
def faltingsPv (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime] {p : ℕ} (D : LocalArithmeticFrobenius p) :
    Polynomial ℚ_[ℓ] :=
  localTatePolynomialCoinv E ℓ D

def faltingsLv (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime] {p : ℕ} (D : LocalArithmeticFrobenius p) :
    RatFunc ℚ_[ℓ] :=
  (algebraMap (Polynomial ℚ_[ℓ]) (RatFunc ℚ_[ℓ]) (faltingsPv E ℓ D))⁻¹
```

Thus the factor uses arithmetic Frobenius on **homological inertia coinvariants**.
The existing proved duality identifies this with geometric Frobenius on the inertia
invariants of the cohomological dual. It is not arithmetic Frobenius on homological
inertia invariants.

### Exact new PRINT

```lean
def Faltings1983Korollar2iiiivPrint : Prop :=
  ∀ (E A : WeierstrassCurve ℚ) [E.IsElliptic] [A.IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime],
    (∀ᶠ v : RationalPlace in cofinite, v.asIdeal.absNorm ≠ ℓ →
      ∀ D : LocalArithmeticFrobenius v.asIdeal.absNorm,
        faltingsLv E ℓ D = faltingsLv A ℓ D) →
    ∀ (v : RationalPlace), v.asIdeal.absNorm ≠ ℓ →
      ∀ D : LocalArithmeticFrobenius v.asIdeal.absNorm,
        faltingsLv E ℓ D = faltingsLv A ℓ D
```

This is the elliptic-ℚ specialization of iii ⇒ iv, restricted to residual
characteristic different from the auxiliary prime. The reduction chooses a different
auxiliary prime for each requested place, so the destination still covers **every** finite place.

### Page-image-checked printed text

Faltings, *Endlichkeitssätze für abelsche Varietäten über Zahlkörpern*, Invent. Math.
73 (1983), §5, printed pp. 360–361. Bibliography key `faltings1983`, TeX lines 11084–11086.
The PDF has a cover: printed p. 360 is PDF page 13 and printed p. 361 is PDF page 14.
Mathematical typography is transcribed with Unicode; the German words are retained.

> §5. Endomorphismen
> Sei K Zahlkörper, A/K eine abelsche Varietät der Dimension g, l eine Prim-
> zahl, T_l = T_l(A) der Tate-Modul, auf dem π = Gal(K̄/K) operiert.
>
> Korollar 1. Seien A₁ und A₂ abelsche Varietäten über K. Dann ist
> Hom_K(A₁, A₂) ⊗_ℤ ℤ_l → Hom_π(T_l(A₁), T_l(A₂))
> ein Isomorphismus.
>
> Die L-Reihe eines A's ist bekanntlich definiert als
> L(A,s) = ∏_v 1 / det(1 − (N_v)^{−s} · F_v | T_l(A)) = ∏_v L_v(A,s),
> wobei das Produkt über fast alle Stellen von K zu erstrecken ist. Die lokalen
> L-Faktoren L_v(A,s) sind unabhängig von l.
>
> Korollar 2. Seien A₁, A₂ wie im Korollar 1. Es sind äquivalent
> i) A₁ und A₂ sind isogen.
> ii) T_l(A₁) ⊗_{ℤ_l} ℚ_l ≅ T_l(A₂) ⊗_{ℤ_l} ℚ_l als π-Modul.
> iii) L_v(s,A₁) = L_v(s,A₂) für fast alle Stellen v von K.
> iv) L_v(s,A₁) = L_v(s,A₂) für alle v.

### Exact proved destination theorem

```lean
theorem Faltings1983EulerFactorRigidityQ_of_print
    (hT : TateCurveTateModulePrint) (hLG : DecompositionGroupLocalGlobalGlue)
    (hA : AdditiveReductionCoinvariantsVanish) :
    Faltings1983Korollar2iiiivPrint → Descent.Faltings1983EulerFactorRigidityQ
```

There is also the more direct version:

```lean
theorem Faltings1983EulerFactorRigidityQ_of_print_of_badReading
    (hB : BadReductionTatePolynomialReadingCoinv) :
    Faltings1983Korollar2iiiivPrint → Descent.Faltings1983EulerFactorRigidityQ
```

The three inputs are consumed only through the existing theorem
`badReductionTatePolynomialReadingCoinv_of_inputs`. They are not restated.

Proof steps:

1. A reciprocal in the rational-function field determines its polynomial.
2. The rational prime-ideal norm dictionary identifies each finite place with `(p)`.
3. At good reduction, `globalGoodReductionTraceReading_proved` and
   `localTatePolynomialCoinv_of_good` give the polynomial reading. That existing chain
   uses `goodReductionFrobeniusTraceDictionaryQ_proved` and the proved determinant-degree input.
4. At bad reduction, the corrected named coinvariant reading gives the polynomial reading.
5. The printed iii ⇒ iv gives equality at the selected place.
6. Injectivity of integer coefficient extension gives the exact integer local polynomials.

### Unchanged destination statement

```lean
def Faltings1983EulerFactorRigidityQ : Prop :=
  ∀ E A : WeierstrassCurve ℚ, E.IsElliptic → A.IsElliptic →
    LocalPolynomialsAgreeAlmostEverywhere E A →
      ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
        localPolynomialQ E v = localPolynomialQ A v
```

## 2. B2: Carayol's Corollaire and Shimura's remaining realization

### Carayol source specialization

The associated-curve predicate retains the actual Shimura quotient data and a pointed
scheme isomorphism to the nonsingular projective Weierstrass model.
The cohomological representation is the dual of the genuine rational Tate representation;
its local invariant polynomial uses **inverse** arithmetic Frobenius, i.e. geometric Frobenius.
The conductor exponent uses the existing Artin–Swan definition on that actual representation.
No minimal-model conductor equality is asserted by a separate definition.

`sourceLSeries` is defined from the genuine Tate polynomials, not from minimal-reduction
polynomials by fiat. At each place, it chooses an auxiliary prime different from the place norm
and descends the actual Tate polynomial to its unique integer preimage. Its unused fallback is `1`.
The existence of that preimage and equality with the minimal-reduction polynomial are proved from
the good and corrected bad readings. `sourceLFunction_eq_LFunction` then proves equality of the
Euler products term by term.

The source corollary specialization, on its stated associated-curve predicate, is:

```lean
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
```

The equality of analytic L-functions is restricted to `Re(s) > 2`, a common convergence
half-plane. The conductor conclusion is retained but is not needed to extract the destination
Euler factors. The remaining source-to-associated-curve realization is discussed below;
this is not claimed as a completed literal-only formalization of both sources.

### Page-image-checked Carayol text

Carayol, *Sur les représentations l-adiques associées aux formes modulaires de Hilbert*,
Ann. Sci. ÉNS 19 (1986), §0.8, printed p. 411 = PDF page 4.
Bibliography key `carayol`, TeX lines 11205–11208.
Printed pp. 409–410 were also read for the normalization preceding the theorem.

> 0.8. APPLICATION. — Le théorème précédent, appliqué dans le cas particulier où F = Q
> et k = 2, fournit facilement une réponse affirmative à une conjecture concernant les
> courbes elliptiques de Weil :
>
> COROLLAIRE. — Soit f ∈ S₂(Γ₀(N)) une nouvelle forme rationnelle, valeur propre normali-
> sée des opérateurs de Hecke, et soit E_f la courbe elliptique sur Q associée à f. Alors la
> fonction L de E_f est égale à L(f,s), et le conducteur géométrique de E_f est égal à N.
>
> En effet, notons π la représentation automorphe attachée à f, et soit σ^λ la représentation
> l-adique que le théorème associe à π. De la définition de E_f et du théorème de Čebotarev,
> il résulte que σ^λ est isomorphe à la représentation naturelle de Galois sur l'espace
> H¹(E_f ⊗ Q̄, Q_l). L'égalité des séries L découle de ce fait et du théorème. De même pour
> l'égalité des conducteurs, compte tenu du travail de Ogg[Og].

The new source does not restate, modify, import, or claim `CarayolRefold.*`.
It does not prove Carayol's Théorème (A), construct a separate automorphic σ^λ,
or prove its local Langlands compatibility. The natural cohomological Tate representation
in the quoted proof paragraph is the representation used here.

### Exact proved destination theorems — with the remaining GLUE visible

```lean
theorem Carayol1986RationalNewformEulerFactors_of_print
    (hT : TateCurveTateModulePrint) (hLG : DecompositionGroupLocalGlobalGlue)
    (hA : AdditiveReductionCoinvariantsVanish)
    (hS : Shimura1973RationalGeometricReading) :
    Carayol1986CorollaireRational → Carayol1986RationalNewformEulerFactors
```

Equivalently, with the source reading placed in the arrow chain:

```lean
theorem Carayol1986RationalNewformEulerFactors_of_print_of_geometricReading
    (hT : TateCurveTateModulePrint) (hLG : DecompositionGroupLocalGlobalGlue)
    (hA : AdditiveReductionCoinvariantsVanish) :
    Shimura1973RationalGeometricReading → Carayol1986CorollaireRational →
      Carayol1986RationalNewformEulerFactors
```

The bad-reading version takes only `BadReductionTatePolynomialReadingCoinv` in place of
those three named hypotheses. All destination occurrences refer to the existing definition,
not a copy with altered quantifiers or premises.

The fully proved post-realization chain is:

1. Rational coefficients give `coefficientField F = ⊥` and degree one.
2. The genuine triple gives an actual quotient abelian variety of dimension one.
3. Its actual sheaf differential pullback is injective: dominance, characteristic-zero
   formal smoothness, Jacobi–Zariski, generic stalk naturality, and flat scalar extension.
4. Clause (iv), in the explicit algebraic source reading, gives its nonzero one-dimensional image.
5. The proved regular Kähler–Weil comparison gives genus one.
6. Riemann–Roch at the actual identity's degree-one place constructs the pointed
   nonsingular Weierstrass presentation over ℚ.
7. Carayol supplies equality of the complete source L-series.
8. The good and corrected bad dictionaries identify the source and minimal Euler products.
9. Hasse's proved bound and the proved cusp coefficient bound establish finite abscissae.
10. Dirichlet-series uniqueness gives coefficients at `p` and `p²`.
11. The two existing prime-power recurrences recover both coefficients of the local polynomial,
    including at additive, split multiplicative, and nonsplit multiplicative primes.

No tangent-duality PRINT, invariant-differential trivialization, assumed Weierstrass model,
or assumed equality of local polynomials is used in this reduction.

### Unchanged destination statement

```lean
def Carayol1986RationalNewformEulerFactors : Prop :=
  ∀ (M : ℕ) [NeZero M] (F : Newform M 2) (hχ : F.χ = 1),
    (∀ n : ℕ, ∃ b : ℚ, (qExpansion 1 F.toCuspForm).coeff n = (b : ℂ)) →
      ∃ A : WeierstrassCurve ℚ, A.IsElliptic ∧
        ∀ (p : ℕ) (hp : p.Prime),
          (localPolynomialQ A (primeIdealQ p hp)).map (Int.castRingHom ℂ) =
            newformEulerPolynomial F hχ p
```

## 3. The remaining Shimura boundary — not PRINT

The exact named interface is:

```lean
def Shimura1973RationalGeometricReading : Prop :=
  ∀ (M : ℕ) [NeZero M] (F : Newform M 2) (hχ : F.χ = 1),
    (∀ n : ℕ, ∃ b : ℚ, (qExpansion 1 F.toCuspForm).coeff n = (b : ℂ)) →
      ∃ (S : ShimuraJacobianSetting M) (A : PkgI3.AbVar ℚ)
        (ν : PkgI3.AbVar.Hom S.J A) (θ : coefficientField F →+* A.End0),
        IsShimuraRationalTriple F hχ S A ν θ
```

Its objects are genuine: smooth proper rational modular-curve setting with actual
function field `ℚ(j,j_M)`, the q-adic cusp local ring, the actual Jacobian universal property,
actual scheme homomorphisms `ξ_n`, actual rationalized endomorphisms `θ`, a surjective quotient
with a scheme-theoretic abelian kernel, and actual global differential sheaf pullbacks.
The q-normalization of `μ` is specified by the actual Abel–Jacobi pullback, generic restriction,
and the universal Kähler Euler derivative; it is not an arbitrary eigenform-permuting isomorphism.

However, `shimuraDB A = ℂ ⊗[ℚ] Γ(Ω¹_{A/ℚ}, ⊤)` is **not by definition** the space of all
analytic holomorphic 1-forms on `A(ℂ)` in Shimura's text. A canonical base-change/analytification
comparison, compatible with pullback and the q-normalization, remains to be proved.
The setting's existence and the all-clauses literal source statement also need separation from
this realization. Uniqueness and the final zeta clause are quoted but not formal fields.
Consequently this proposition is named `Reading` and its docstring says **GLUE**.
There is no final declaration named `Shimura1973RationalGeometricPrint`.

### Page-image-checked Shimura text

Shimura, *On the factors of the jacobian variety of a modular function field*, J. Math.
Soc. Japan 25 (1973), §1, printed pp. 524–527 = PDF pages 2–5.
Bibliography key `shimura-factors`, TeX lines 11053–11057.

Printed p. 525, setting:

> By a quotient of B by an abelian subvariety, say C, of B, we understand
> a couple (A, ν) formed by an abelian variety A which canonically represents
> B/C and a natural map ν: B → A with C = Ker(ν) (cf. Chow [3]). We see
> easily that
>
> (1.2) Y_C = {v ∈ Y_B | (u, v)_B = 0 for all u ∈ δν(D_A)}.
>
> Let Γ be a group of level N, and J the jacobian variety of ℌ*/Γ. Let
> ψ: ℌ* → J be the map obtained by composing the natural map ℌ* → ℌ*/Γ with
> a canonical map of ℌ*/Γ into J. Then there is an isomorphism μ: S₂(Γ) → D_J
> defined by δψ(μ(f)) = f(z)dz for f ∈ S₂(Γ), where δψ is the “pull back” asso-
> ciated with ψ, and z is a standard variable on ℌ.
>
> For a positive integer n, let q be the largest divisor of n prime to N, and
> put n = mq. Then we define T_n and ξ_n by T_n = T_m T_q, ξ_n = ξ_m ξ_q,
> T_m = [ΓαΓ]₂, ξ_m = {ΓαΓ} with α = [1 0; 0 m], and T_q = ∑_β [ΓβΓ]₂,
> ξ_q = ∑_β {ΓβΓ}, where ∑_β is extended over all distinct ΓβΓ with det(β) = q,
> β ≡ [1 0; 0 q] (mod N). Then μ ∘ T_n = δξ_n ∘ μ.

Printed p. 526, theorem:

> As shown in [11, §7.3], there is a “standard model” of ℌ*/Γ defined
> over Q (see also §4 below), so that J can naturally be defined over Q. Let
> f(z) = ∑_{n=1}^∞ a_n e^{2πinz}, with a₁ = 1, be an element of S₂(Γ), that is a common eigen-
> function of T_n for all n (i. e., f | T_n = a_n f). Fix f, and let K be the subfield
> of C generated over Q by the complex numbers a_n for all n. (Of course K
> depends on f.) Then we have
>
> THEOREM 1. There exists a triple (A, ν, θ) formed by the objects satisfying
> the following conditions:
> (i) (A, ν) is a quotient of J by an abelian subvariety rational over Q.
> (ii) θ is an isomorphism of K into End(A) ⊗ Q such that ν ∘ ξ_n = θ(a_n) ∘ ν
> for all n. (This implies especially θ(1) = id_A.)
> (iii) dim(A) = [K: Q].
> Moreover, let I denote the set of all isomorphisms of K into C. Then, for every
> σ ∈ I, there exists an element f_σ of S₂(Γ) such that f_σ | T_n = a_n^σ f for all n, and
> f_σ(z) = ∑_{n=1}^∞ a_n^σ e^{2πinz}. With these f_σ, one has
> (iv) δν(D_A) = μ(∑_{σ∈I} Cf_σ).
> Under the conditions (i, ii), the triple (A, ν, θ) is unique up to isomorphisms
> over Q. Furthermore, the one-dimensional part of the zeta function of A over
> Q coincides, up to finitely many Euler factors for bad primes, with
> ∏_{σ∈I}(∑_{n=1}^∞ a_n^σ n^{−s}), provided that Γ = Γ₀(N), or
> ∑_{σ∈I} Cf_σ is stable under the map h(z) ↦ h(−1/Nz)/z².

The last `f` in the printed conjugate eigenrelation is retained, not silently corrected.
The proof on p. 527 uses `f_σ`. In the rational specialization there is only the identity
embedding, so this distinction does not affect the constructed algebraic reading.

The preceding definition on p. 524 says:

> For an abelian variety B defined over C, we denote by D_B, or D(B), the vector space
> over C of all holomorphic 1-forms on B, and by Y_B, or Y(B), the tangent
> space of B at the origin. Then D_B is dual to Y_B.

No separate algebraic rephrasing of this sentence is left in the source as a PRINT.
The model proof instead uses the proved injectivity of actual sheaf differential pullback.

## 4. Non-vacuity and verification

`Nonvacuity.lean` proves:

- `testCurve = ⟨0,0,0,-1,0⟩` is elliptic, with discriminant 64.
- Its genuine rational Tate module at ℓ = 2 has dimension **2**, not merely a zero element.
- A genuine arithmetic Frobenius at p = 3 exists.
- The printed Faltings almost-all premise is inhabited by the diagonal concrete pair.
- The source integer local polynomial has constant coefficient 1 when the corrected bad
  dictionary is supplied; the fallback in integer descent is then never used.
- Both genuine analytic coefficient series have finite abscissae.
- For any genuine newform and actual Shimura setting/triple, the normalized image vector
  is nonzero and the quotient's differential space has dimension one.

The B2 examples are conditional on a genuine `Newform M 2`; **no unconditional concrete
rational weight-two newform is constructed**. They are nonzero-output/normalization checks,
not a proof that the quantified newform type is inhabited.

The author build command names only the new module target:

```sh
PATH=$HOME/.elan/bin:$PATH LEAN_NUM_THREADS=8 \
  taskset -c 24-47 nice -n 10 \
  lake build +ZInQKernel.Contrib.RC53Assist.G0Prints.Nonvacuity
```

`Nonvacuity` imports the assembly and all ten new Lean modules. Its final author build
succeeds after restoration of the shared dependency checkout. It includes explicit absolute
summability of both actual series for every `s` with `Re(s) > 2`, not just finite abscissae.
Some imports emit module-system compatibility warnings and some proofs emit style-only
warnings. Those warnings are not proof holes.

The final kernel axiom audit used `lake env lean --stdin` after the hold was lifted.
A successful direct `lean --stdin` audit was also completed during the temporary hold.
No audit commands remain in final `.lean` files. `KernelAudit.txt` records the actual
transitive axiom output. `FileCustody.txt` lists byte counts and SHA256 values of the ten
new Lean sources, the page images, and verification receipts; it excludes itself.

The source checks find no forbidden declarations/tactics, no lines over 100 characters,
and no private names or workspace paths in the new public Lean text.
Each file sets `maxHeartbeats` to 800000.

The three protected files retain their initial SHA256 and byte counts:

- `NewformGlueG0/GaloisCompletion.lean`: 60085 bytes;
  `eb2592b3be3ef04f543d09755ba750c420937c4a8bcbfc48cd49b187e23a1d1f`.
- `GlobalTrace/GoodReductionReading.lean`: 54984 bytes;
  `225cc04861eb3ac8d621472b2f57eded456634183cd631e350615ac36a3723bc`.
- `GlobalTrace/CoinvariantReadings.lean`: 67296 bytes;
  `c142c83a7fc5040a7ff69b661c8f76b3bd7558d34391087385e0e8a97ea9fd51`.

No subagents, history commands, source checkouts, dependency updates, outreach, or memory
writes were used. The supplied integration head was kept. This is an author build in the
specified worktree, not a separate independent review.

The final audit lists **32** declarations, all with the standard axiom set. It includes the
explicit `newform_summable_of_two_lt_re`, `elliptic_summable_of_two_lt_re`, and
`source_and_newform_summable` theorems.

An auxiliary page-image check of Milne, *Abelian Varieties*, version 2.00 (2008), IV,
printed p. 152 = PDF page 158, confirms the existing invariant-differential locator:

> PROPOSITION 6.4. Let V be a smooth algebraic variety of dimension g over a field k.
> (a) The sheaf of differentials Ω¹_{V/k} on V is a locally free sheaf of O_V-modules of rank g.
> (b) If V is a group variety, then Ω¹ is free.

The PDF and checked page image are deposited as auxiliary literature evidence only.
No Milne proposition is added as an input to the B1 or B2 reductions.

## 5. What remains

1. **Expected inputs, both reductions:**
   `TateCurveTateModulePrint`, `DecompositionGroupLocalGlobalGlue`, and
   `AdditiveReductionCoinvariantsVanish` remain named hypotheses. Their proofs belong to
   their respective work. The exact Faltings iii ⇒ iv proposition remains the literature PRINT.
2. **B2 literal-source closure:** formalize the complete literal Shimura statement with its
   holomorphic objects, and prove its canonical realization as
   `Shimura1973RationalGeometricReading`, including existence of the modular Jacobian setting,
   pullback compatibility, and the specified q-normalization. Do not replace this by a
   differently named copy of the destination Euler-factor statement.
3. **Carayol source validation:** reconcile the associated-curve predicate and the natural
   Tate-dual realization with the printed σ^λ/H¹ identification. A separate automorphic
   representation construction/local Langlands statement is not supplied here.
4. **Non-vacuity strengthening:** an unconditional explicit rational weight-two newform
   example has not been constructed.
5. **Integration/review:** only new files were created. Existing assemblies were not edited
   to consume them; no public source publication or history command was issued.
6. **Independent verification:** an independent review has not yet been performed.

The substantial new proved contribution for B2 is the full post-realization join:
actual quotient → differential dimension → pointed Weierstrass model → actual Tate Euler
product → analytic equality → every exact local polynomial. The remaining geometric source
boundary is visible and is not claimed to have disappeared.
