# G0: newform comparison components

## Status

The proposition `LiCarayolNewformOfModular` in
`ZInQKernel/Contrib/CloudB3RC53/ModularWeil/NewformGlue.lean` remains open.
No declaration below assumes that proposition, or an equivalent existence
statement, as an input.

The contribution proves the arithmetic Hecke bridge, divisor-level newform
extraction with agreement at almost all primes, the full-eigenform and
trivial-character conversions, the characteristic-zero Brauer–Nesbitt theorem,
the Frobenius-character comparison, and the transport of local Euler
polynomials under an actual representation isomorphism. The missing part is
identifying the particular newform and Tate-module representations with the
particular local polynomials in the statement.

Only `HeckeBridge.lean`, `BrauerNesbitt.lean`, `FrobeniusLocal.lean`,
`PrintedInputs.lean`, and this note are proposed source contributions.
`Scratch/` and `Sources/` hold verification and reference materials, not
proposed publications.

## Proved components

### Arithmetic and Hecke operators

`HeckeBridge.lean` uses the existing `WeierstrassCurve.LFunction`, its local
minimal-reduction polynomials, and its actual Euler product.

* `lFunction_isMultiplicative`, `lFunction_one`, `lFunction_prime_pow`: global
  multiplicativity, normalization, and equality of each prime-power
  coefficient with its actual local reciprocal coefficient.
* `lFunction_prime_pow_recurrence`: the uniform good- and bad-prime recurrence
  with quadratic scalar equal to the actual quadratic local-polynomial
  coefficient. `lFunction_good_prime_mul` gives the full good-prime recurrence
  at every index, including the zero index.
* `modular_restrict_hecke_good`, `modular_heckeGamma0_good`: the supplied
  weight-two cusp form is a genuine Hecke eigenvector at a prime which is good
  for the curve and does not divide its level. No assertion that all bad
  primes divide the supplied level is assumed.
* `modular_hecke_almost_all`: the first Fourier coefficient is one and the
  good-prime eigenrelations hold outside a finite set.
* `exists_newform_of_cofinite_prime_eigen`: the existing old/new spanning
  theorem is refined to an eigensystem outside an arbitrary finite set, with
  inducing nebentypus preserved.
* `exists_newform_almost_all_prime_coeff`: from exactly the curve, positive
  level, cusp form, and positive-coefficient data of G0, obtain a newform
  `F : Newform M 2`, `M ∣ N`, `F.χ = 1`, with the elliptic coefficients at
  almost all primes.
* `exists_gamma0_full_eigenform_almost_all`: obtain the corresponding
  normalized full eigenform on the genuine space `S₂(Γ₀(M))`. Eigen-ness at
  all indices, including the bad indices, is already proved; agreement with
  the elliptic coefficients is still only at almost all primes.

The post-comparison arithmetic is also proved:

* `newformCoefficients_isMultiplicative` and `newform_prime_pow_recurrence`
  give the genuine newform coefficient identities at all primes.
* `newform_prime_pow_coeff_of_local_polynomial` extends an equality of local
  polynomials at one specified prime to equality at every power of that
  prime. It assumes neither equality at all primes nor a newform-existence
  statement.
* `arithmeticFunction_eq_of_prime_recurrences` is the general coprime-product
  assembly theorem: equal prime data and equal recurrence scalars determine
  the whole multiplicative arithmetic function.

### Brauer–Nesbitt and Frobenius comparison

`BrauerNesbitt.lean` proves `brauerNesbittChar0` at exactly the existing
proposition `GlueC10.BrauerNesbittChar0`. It has no literature input.

The proof is over an arbitrary characteristic-zero field and an arbitrary
acting group, not merely finite groups or algebraically closed fields. More
generally, `semisimple_actionTrace_comparison` proves the algebra-module
version. It uses simple constituents, isotypic submodules, Schur's lemma,
Jacobson density for finite semisimple modules, and induction on dimension.

`galois_comparison_from_frobenius` discharges both Čebotarev and
Brauer–Nesbitt: actual continuous semisimple representations of the genuine
absolute Galois group of the rationals are isomorphic when their traces agree
at arithmetic Frobenius elements outside a finite set. The remaining
semisimplicity and continuity hypotheses concern the actual representations;
no proof that the newform or Tate-module objects satisfy those hypotheses is
claimed here.

`FrobeniusLocal.lean` also proves `frobeniusElements_dense` as a topological
density assertion and `trace_eq_of_frobenius` without a semisimplicity
hypothesis. The Frobenius predicate is the existing congruence in the integral
closure of the integers, not a freely specified collection of group elements.

### Local-factor transport

`fixedInertia`, `inertiaFrobenius`, and `inertiaEulerPolynomial` use actual
representations, invariant subspaces, restricted endomorphisms, and reversed
characteristic polynomials. The inertia subgroup and its Frobenius normalizer
condition are explicit.

`fixedInertiaEquiv`, `inertiaFrobenius_conj`, and
`inertiaEulerPolynomial_eq_of_equiv` prove that an actual representation
isomorphism transports every such local polynomial, including ramified
places and zero-dimensional fixed spaces.

`localFactors_eq_of_BN_frobenius` displays Brauer–Nesbitt as a parameter for
an independent interface. That parameter is discharged by
`BrauerNesbitt.lean`. The comparison must concern the actual representations:
replacing an arbitrary representation by its semisimplification is not, by
itself, a valid replacement in an inertia-invariant local factor.

## Precisely identified printed facts

### Li 1975 — bibitem `li-newforms`

W.-C. W. Li, *Newforms and Functional Equations*, Math. Ann. **212**
(1975), 285–315.

1. **Section 2, p. 294:** the new subspace is the Petersson-orthogonal
   complement of the old subspace; a newform is a nonzero common good Hecke
   eigenform in that new subspace, and normalization is `a₁ = 1`. Cusp forms
   are spanned by level-raised newforms of divisor levels. The existing
   newform API supplies proved versions of this content.
2. **Theorem 3(i), p. 295**, at weight two and trivial character:
   at `p ∤ M`,
   `a_{pn} + p a_{n/p} = a_p a_n`, with the second term zero if `p ∤ n`;
   at `p ∣ M`, `a_{pn} = a_p a_n`. The Euler polynomials are therefore
   `1 - a_p T + p T²` and `1 - a_p T`, respectively. The imported full
   eigenform API and the proved arithmetic lemmas give these identities.
3. **Theorem 3(iii), p. 295:** for a weight-two trivial-character newform,
   `a_p = 0` when `p² ∣ M`, and `a_p² = 1` when `p ∣ M` but `p² ∤ M`.
   The character factors through `M/p`, as required by the print.
   `Li1975BadPrimeWeightTwo` is exactly this special-case proposition.
4. **Theorem 5, p. 298:** normalized newforms at two levels with equal prime
   coefficients at almost all primes have the same level and the same
   underlying form. `Li1975StrongMultiplicityOneWeightTwo` states its
   weight-two trivial-character special case. It is used only in the
   explicitly conditional uniqueness theorem, not in divisor-level extraction.

These printed propositions are not proved here and are not new axioms.
`newform_bad_prime_sign`, `newform_bad_prime_values`, and
`newform_bad_operator_values` prove their algebraic consequences from the
first proposition. `elliptic_bad_prime_values` proves the same three value
possibilities for the actual curve coefficient at bad reduction directly
from its local-polynomial definition. Possibilities agreeing is not a proof
that the signs agree at the same prime.

Page images checked: pp. 294–298, PDF pages 11–15. Printed p. 285 is PDF
page 2. The manuscript's locator p. 296 is the Fricke-conjugation discussion,
not the newform-existence conclusion for an arbitrary elliptic curve.

### Carayol 1986 — bibitem `carayol`

H. Carayol, *Sur les représentations ℓ-adiques associées aux formes
modulaires de Hilbert*, Ann. Sci. ÉNS **19** (1986), 409–468.

**Théorème (A), §0.7, pp. 410–411:** let the totally real field have degree
`d`, and let `k₁,…,k_d ≥ 2` and `w` be integers of the same parity. For a
cuspidal automorphic representation `π` of `GL₂` with archimedean components
`π_{τ_i} ≅ D_{k_i,w}` as in §0.3, and, in even degree, at least one finite
component essentially square-integrable, there is a finite extension of the
rationality field `Q(π)` and a strictly compatible system of continuous
two-dimensional λ-adic Galois representations. For every finite place `v`
and every λ whose
residue characteristic differs from that of `v`, restriction to the local
Weil group is equivalent to the λ-adic realization of the Hecke
correspondence attached to the local automorphic representation. The
additional essentially square-integrable finite-place hypothesis in §0.3 is
only required in even degree, so does not arise for the rational field.

**Normalization, §§0.4–0.5, pp. 409–410:** the print sends geometric
Frobenius to a uniformizer. Its Hecke correspondence includes a twist and
contragredient, and its determinant is the inverse central character times
the inverse cyclotomic character. The arithmetic-Frobenius Tate-module
reading must use the corresponding dual and classical weight-two
normalization. At good primes it must give trace `a_p` and determinant `p`.
These normalizations are not silently identified in the contribution.

**Unnumbered Corollaire, §0.8, p. 411:** for a rational normalized weight-two
newform on `Γ₀(N)` and its associated elliptic curve `E_f`,
`L(E_f,s) = L(f,s)` and the geometric conductor of `E_f` is `N`.
This is about the associated curve `E_f`, not directly the arbitrary curve
in the modularity hypothesis of G0. The printed proof itself uses a Galois
representation comparison and, for conductors, Ogg's work.

Page images checked: printed pp. 409–411, PDF pages 2–4.

### Casselman 1973 — bibitem `casselman`

W. Casselman, *On Some Results of Atkin and Lehner*, Math. Ann. **201**
(1973), 301–314. This bibitem is present in the manuscript.

**Theorem 1, p. 302; proof pp. 302–306:** for an irreducible admissible
infinite-dimensional representation `ρ` of `GL₂(k)`, with central
quasicharacter `ε`, let `c(ρ)` be the largest ideal such that the
`Γ₀(c(ρ))` space with action `ρ(g)v = ε(g₁₁)v` is nonzero. That space is
one-dimensional. Here nonzero, rather than nonemptiness of a vector-space
type, is essential. The proof on p. 306 gives conductor one for an
unramified special twist and the square of the character conductor for a
ramified special twist.

**Corollary to the proof, p. 306:** replacing `c(ρ)` by the smaller ideal
`c(ρ) 𝔭^i` gives dimension `i + 1`. The **Remark continuing to p. 307**
identifies the same conductor ideal with the exponent in the local
ε-factor's dependence on `s`, with the additive-character normalization
stated there.

**Theorem 4, p. 313:** for the automorphic representation `π`, the relevant
modular-form space at `N` is zero if `c(π) ∤ N`; if
`N = c(π) ∏ p_i^{n_i}`, its dimension is `∏ (n_i + 1)`. At `N = c(π)`
the dimension is one and the corresponding form is a newform; all newforms
arise this way. This supplies the newform-level/automorphic-conductor reading,
not by itself the comparison with the arbitrary curve of G0.

Page images checked: pp. 302, 304–307, 313, PDF pages 3, 5–8, 14.

## Exact remaining obligations for full G0

1. **Attach the actual representations.** For the extracted newform construct
   the Carayol compatible system, a genuine coefficient field with its
   complex and λ-adic embeddings, and the normalized arithmetic-Frobenius
   representation. For the curve use its actual rational Tate module,
   extended to the same λ-adic field. Prove or provide the actual continuity
   and semisimplicity hypotheses of the comparison theorem.
2. **The good-prime dictionaries.** Identify traces of every allowed
   arithmetic Frobenius with the newform coefficient and with
   `E.LFunction p`, in the common coefficient field. The existing
   `ModularWeil/FrobeniusTrace.lean` displays further Tate-specialization and
   determinant-degree inputs for the curve side; those inputs are not
   discharged by the present proof of Brauer–Nesbitt.
3. **The bad-prime local dictionaries.** Identify the actual decomposition
   and inertia subgroups and Frobenius elements, and identify the two
   inertia-fixed Euler polynomials with the actual curve polynomial and
   the classical newform polynomial. Apply Carayol (A), with its normalization,
   and the Li/Casselman newvector reading, rather than inserting equality of
   all Fourier coefficients as a premise.
4. **Avoid the auxiliary-prime exception.** Carayol (A) requires `p ≠ ℓ`.
   For equality at every rational prime, use a compatible family or two
   distinct auxiliary primes. A comparison at one fixed ℓ does not by itself
   recover the Euler factor at that same prime.
5. **Return the coefficients.** Transport the polynomials through the
   coefficient-field embeddings. Equality at one prime then gives equality
   at all its powers by the proved theorem, and coprime multiplicativity
   gives every positive coefficient by the proved assembly theorem.

The conductor of an elliptic curve is not introduced here. The original G0
statement only asks for `M ∣ N`; that divisibility is already proved. A separate
claim `M = conductor(E)` still needs the conductor dictionary and the
Carayol/Casselman reading.

## Reference copies

The following are the exact reference copies used for the page-image checks.

* Li: <https://gdz.sub.uni-goettingen.de/download/pdf/PPN235181684_0212/LOG_0047.pdf>
  — 2,210,387 bytes;
  SHA-256 `3bf1fca9ecd1ab88890999f021062cdae7ccb21cc7af1d23459ce9872e73945a`.
* Carayol: <https://www.numdam.org/item/ASENS_1986_4_19_3_409_0.pdf>
  — 5,887,969 bytes;
  SHA-256 `d4a5fb6b1cd76f944f8948e06df1c7ad5656ae5ee14b9189178ee1e8f2b0dab8`.
* Casselman: <https://gdz.sub.uni-goettingen.de/download/pdf/PPN235181684_0201/LOG_0060.pdf>
  — 1,348,606 bytes;
  SHA-256 `a4980e5b4a00967bcfc6d8ae820e4465bae01ed0da5e8cf9f0927edfda6895b1`.

## Verification records

All four source files pass individual checks. The combined check in
`Scratch/StatementsAxioms.lean` also passes and includes a local-factor
comparison with the Brauer–Nesbitt parameter discharged by its proved theorem.

`Scratch/TheoremStatements.md` contains the exact printed statement and
axiom report for every one of the 52 source theorems, plus the integrated
comparison. `Scratch/StatementsAxioms.txt` is the raw output, and
`Scratch/AuditSummary.json` records all 64 audited declarations and the source
checksums. The unfolded Brauer–Nesbitt and Li propositions are included.
Every audited axiom set is a subset of
`[propext, Classical.choice, Quot.sound]`; no additional axiom is used.
