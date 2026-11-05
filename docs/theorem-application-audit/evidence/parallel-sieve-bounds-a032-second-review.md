# A032 independent acceptance review

Reviewed 2026-11-05. Input is the A032 proposal in `parallel-009/theta-local/REPORT.md` and `REPLACEMENTS.md`, for manuscript SHA256 `a17e021ea3a6b90f861d87aff048f905b1dc31226e3445caf273739f7659e51e`, principally lines 9460–9486 and the summary at 2428–2431. I did not edit the manuscript or the first review.

The substantive normalization repair is correct. In the stated unitary convention the Fourier operator has eigenvalue `sqrt(p) mu_1(p)`, and this is the arithmetic-Frobenius eigenvalue on the unramified Galois line. Neither an extra factor p nor its inverse is needed. The two dual operations in the proposed Carayol application are necessary and compatible.

There is one wording correction to make before adopting the review: its explanatory report says that conjugation by the Weyl matrix converts Casselman's character convention. The ordinary Weyl matrix does not normalize K0(p). Use the level-p Atkin–Lehner matrix specified below. The proposed manuscript text only says “conjugation and interchange”; replace that vague phrase by the explicit matrix. This correction does not change the scalar calculation.

## Primary sources inspected

I independently inspected the primary page images, including the displayed formulas, rather than relying on the first review's transcriptions.

- Carayol, *Sur les représentations l-adiques associées aux formes modulaires de Hilbert*, Ann. Sci. ENS 19 (1986), 409–468. Source `work/astra-t3-opus-reconciliation-001/primary/carayol-1986.pdf`, SHA256 `d4a5fb6b1cd76f944f8948e06df1c7ad5656ae5ee14b9189178ee1e8f2b0dab8`. Inspected printed pp.409–411, §§0.2–0.7, Theorem A and the elliptic-curve interpretation in §0.8. [Publication record](https://www.numdam.org/item/ASENS_1986_4_19_3_409_0/).
- Casselman, *On some results of Atkin and Lehner*, Math. Ann. 201 (1973), 301–314. Source `work/astra-t3-opus-reconciliation-001/primary/casselman-1973.pdf`, SHA256 `7f91ebae1a8f5e695800f4afb9fc06d0e2ea0b3a476751a31a7c8c3f38ad537d`. Inspected printed pp.302–307 and 313, including Theorem 1, the intervening proofs, its corollary, and Theorem 4. [Author's publication list](https://personal.math.ubc.ca/~cass/research/publications.html) identifies this article and its Göttingen archive copy. The author's warning about his separate representation-theory notes is not an erratum to this article.

No new source PDF is needed for this second review. The exact existing bytes above bind the locators; the public records were checked separately.

## Carayol and the two dual operations

Carayol §0.4 sends geometric Frobenius to a uniformizer. On p.410, omega is the character `|.|_p`, so omega(Frob_geo)=p^-1 and omega(Frob_arith)=p. Section 0.5 expressly includes a contragredient in the correspondence. Its formula for normalized induction is

`sigma(Ind(xi_1,xi_2)) = xi_1^-1 omega^-1/2 + xi_2^-1 omega^-1/2`.

Thus, for the unitary automorphic representation with `Pi_p=Ind(mu_1,mu_2)`, applying the theorem to `Pi^vee` gives `sigma(Pi^vee)` with characters `mu_i omega^-1/2`, interpreted using geometric reciprocity. After the Galois dual,

`rho = sigma(Pi^vee)^vee = (mu_1^-1 omega^1/2) + (mu_2^-1 omega^1/2)`.

At arithmetic Frobenius an unramified mu_i has value mu_i(p)^-1 in this reciprocity convention. Therefore rho has eigenvalue `mu_i(p) sqrt(p)`. Equivalently, taking the dual and replacing geometric Frobenius by its inverse cancel on the eigenvalues. At a good q, their sum is a_q and product q chi(q), exactly the desired polynomial. Applying Carayol to Pi without the automorphic contragredient and then merely dualizing would give `sqrt(q) mu_i(q)^-1`, which is generally different.

On inertia rho has the inverse of the corresponding inducing character. For the present ramified quadratic character the inverse equals the character itself. The proposed inertia claim is therefore correct in this quadratic setting; it must not be generalized to arbitrary nebentype without retaining the inverse.

The global hypotheses are satisfied for the bounded application: F=Q has odd degree, k=2, and the unitary representation and its contragredient have the permitted real discrete-series type D_{2,0}. Carayol's parity requirement k congruent to w modulo 2 holds for w=0. Its extra finite discrete-series condition applies only to even degree and is absent here. The coefficient place is above 2 and p is odd. The theorem gives the local Weil representation, including the monodromy interpretation, not only good-prime characteristic polynomials. Here the principal-series parameter has N=0 and the two distinct inertia types separate its character lines. No inference from good primes alone is needed to assert the splitting at p.

## Conductor and the unramified inducing character

The application still assumes the manuscript's preceding block statement: local level exponent at most one and primitive quadratic character at p. Under that input, the local conductor is one. The central character cannot be ramified in an unramified representation, giving the lower bound, and a vector at that level gives the upper bound.

Casselman p.303 explicitly has n_nu<=-2 for the supercuspidal Kirillov calculation; p.304 obtains conductor exponent -n_1. Thus a supercuspidal conductor is at least two. This is not merely an unstated classification fact attributed to Theorem 1. On p.306 the special-representation calculation gives twice the twisting-character conductor when ramified, and exponent one for an unramified twist. The latter has unramified central character. Both alternatives are excluded here.

The principal-series calculation on p.306 gives the product of the two conductor ideals, hence the sum of their exponents. At exponent one exactly one character is unramified. The representation is irreducible: a quotient mu_1/mu_2 with nontrivial inertia cannot be `|.|` or its inverse, the reducibility alternatives on p.305. That page also states the isomorphism under interchange of the inducing characters in the irreducible case. It is therefore legitimate to label the unramified one mu_1. This labelling is essential: the Fourier eigenvalue in this induced model is its value, not the value of the ramified mu_2.

The newvector line and oldspace dimension are exactly Casselman Theorem 1 and its p.306 corollary. At conductor exponent one and level exponent one the local dimension is one. Theorem 4 on p.313 factors global multiplicities into local dimensions. Old multiplicities elsewhere do not replace the local scalar by a matrix at p.

## Exact character-convention correction

Casselman's Theorem 1 uses the character epsilon(a) of `k=[[a,b],[c,d]]` in K0(p). Set

`h_p = [[0,1],[-p,0]]`.

Then

`h_p^-1 k h_p = [[d,-c/p],[-pb,a]]`.

This is again in K0(p), and its upper-left entry is d. Thus if v transforms by epsilon(a), then `Pi(h_p)v` transforms by epsilon(d). This is also the matrix used in Casselman's p.303 lemma. The ordinary Weyl matrix with lower-left entry -1 conjugates K0(p) to the opposite subgroup and cannot supply this same-subgroup assertion by itself.

Use this replacement for the sentence in the proposed manuscript:

```tex
This is the lower-right-character convention. Casselman's
upper-left-character convention is carried to it by
$h_p=\left(\begin{smallmatrix}0&1\\-p&0\end{smallmatrix}\right)$,
which normalizes $K_0(p)$ and interchanges its diagonal entries
under conjugation. We label the inducing characters so that
$\mu_1$ is unramified, using the interchange isomorphism for
irreducible principal series.
```

## The local Hecke sum

Casselman p.304 gives precisely the normalized induced transformation law in the proposal. For k in B intersect K0(p), its diagonal entries are units, so mu_1(a)=1, the modulus factor is one, and its left inducing character equals mu_2(d). Therefore the function supported on B K0(p), right transforming by k↦mu_2(k_22), with v(1)=1, is well-defined. The newvector dimension makes this the required line.

For t=diag(p,1), the p right cosets in K0(p)tK0(p) are

`[[p,b],[0,1]] K0(p)`, for b modulo p.

The intersection character is compatible under conjugation by t, since the lower-right entry does not change. With vol(K0(p))=1 and the character-weighted Hecke function equal to one at t, the operator on this line is the displayed sum. Equivalently, this sum directly preserves the specified character line, which avoids any ambiguity about whether a Hecke algebra author uses inverse characters in the function convention.

Each summand evaluated at 1 is `mu_1(p)|p|^(1/2)=mu_1(p)/sqrt(p)`. There are p summands. Hence the eigenvalue is `sqrt(p)mu_1(p)`. This calculation also shows why replacing the unramified inducing character by mu_2 would be wrong in this model.

## Fourier and Whittaker normalization

The proposed `a_n/n` is correct for the finite Whittaker factor of weight two. It is not the normalized Hecke coefficient `a_n/sqrt(n)`. These are different quantities.

One can derive the bridge directly, so an additional external theorem is not needed for this scalar. Normalize the archimedean weight-two Whittaker function on positive diagonal y by `W_infty(a(y))=y exp(-2 pi y)`, and the adelized classical function by `phi_f(a(y)_infty)=y f(iy)`. In its global Whittaker expansion, the positive n term is

`W_fin(a(n)) n y exp(-2 pi n y)`.

Comparing with `y sum a_n exp(-2 pi n y)` gives `W_fin(a(n))=a_n/n`. This remains the correct coefficient comparison for vectors in the same automorphic representation; it does not assume a separate good-prime eigenform calculation at p.

For integral n, the matrix identity

`a(n)[[p,b],[0,1]] = n(nb) a(np)`

is exact. Choose the standard local additive character trivial on Z_p. Its factor at nb is one. Thus the p-term sum gives `p W(a(np))`. The finite Whittaker coefficient of the output is consequently `p a_(pn)/(pn)=a_(pn)/n`, which is precisely the classical Fourier rule `sum a_n q^n -> sum a_(pn) q^n`. The sum is H_p=U_p^(2), without any further scaling. Checking n=p^m already suffices on the local new line and avoids any issue about a single local factor versus the product of finite Whittaker factors. For general n the product form gives the same comparison.

If desired, insert the preceding two-sentence derivation of `a_n/n` into the proposed manuscript; it makes the potentially confusing factor explicit. The first review's shorter assertion is mathematically correct.

## Eisenstein and limits of acceptance

For a primitive weight-two Eisenstein pair (chi_1,chi_2), with exactly one character ramified at p, the divisor-sum coefficient is `a_n=sum_{d|n} chi_1(n/d) chi_2(d)d`. If chi_1 is unramified, terms force the full p-power into n/d, yielding `a_(pn)=chi_1(p)a_n`. If chi_2 is unramified, terms force the full p-power into d, yielding `a_(pn)=p chi_2(p)a_n`. These are the unramified Frobenius eigenvalues of the two character summands `chi_1 + chi_2 cyclotomic`. This explicitly checks both possible placements of the ramified character. In the present quadratic local setting the inverse-character convention does not alter them on inertia. Carayol is not invoked for these constituents.

Acceptance is limited to the characteristic-zero normalization and local conductor-one statement. It uses the preceding level and character properties of the actual blocks and does not independently prove the block construction or the subsequent integral trace-module arguments. Subject to those stated inputs, adopt the A032 replacement with the explicit h_p correction above. No unresolved p-factor, square-root, dual, Frobenius, or Satake-choice error remains in this bounded repair.
