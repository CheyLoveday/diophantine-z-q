# Semantic source-coverage review

The review found two substantive source-accounting omissions within existing families. Both have sufficient primary statements and checked substitutions below. Add a Mertens subobligation to A021 and quaternion classification/embedding subobligations to A052, cross-referenced by A028. No new top-level family is needed. These are omissions from the current inventory, not counterexamples to the manuscript.

The baseline is `diophantine_zq.tex`, SHA256 `a17e021ea3a6b90f861d87aff048f905b1dc31226e3445caf273739f7659e51e`. All line anchors below refer to that file. No shared files have been changed. `COVERAGE-REPLACEMENTS.json` contains five exact old/new replacements, each verified to match the baseline exactly once. `COVERAGE-BIBLIOGRAPHY.tex` contains the two corresponding entries. `COVERAGE-SOURCES.json` pins downloaded bytes, URLs, versions and locators.

## A021: prime products and sums

Consumers are L1278–1286, L1380–1395, L1405–1414 and L1415–1421. The first uses a product lower bound uniform in L; the second uses a logarithmically weighted prime sum; the last two need prime harmonic sums with bounded errors. The current A021 source mapping names the Green–Tao trilogy. A057 records Dirichlet progression existence/density. Neither mapping expressly accounts for these quantitative Mertens inputs. Density alone does not imply the bounded remainder asserted at L1410.

The added source is Kenneth S. Williams, *Mertens' theorem for arithmetic progressions*, JNT 6 (1974), 353–359, Theorem 1, printed p356, PDF p4. I inspected the page image because the extracted formula is damaged. For fixed k>1 and a coprime residue l, its product is C(k,l)(log x)^(-1/phi(k)) times 1+O_k(1/log x), with nonzero positive leading constant. Use only k=2,l=1 and k=4,l=1. The source and these substitutions are fixed; no modulus tends to infinity. The downloaded published scan is [here](https://people.math.carleton.ca/~williams/papers/pdf/057.pdf).

Here are the complete elementary deductions needed by the consumers. Taking logarithms and expanding log(1-1/p) gives

    S_k,l(x) := sum_{p<=x, p=l mod k} 1/p
              = log log x / phi(k) + C'_k,l + O_k(1/log x).

The higher-order terms converge absolutely; their tails are O(1/x), bounded by the corresponding integer tail of sum n^-2. The product leading constant is positive, so its logarithm exists. Adding p=2 to the k=2 result gives

    S(x) = sum_{p<=x} 1/p = log log x + C + O(1/log x).

Partial summation now gives

    sum_{p<=x} (log p)/p = S(x) log x - integral_2^x S(t)/t dt
                         = log x + O(log log x).

The C terms cancel up to a constant. The error at the upper endpoint is O(1), and integrating O(1/log t)/t gives O(log log x). This is enough for the upper bound 2 log x used at L1392 for all sufficiently large x. The baseline's stronger equality with O(1) at L1395 is a true classical Mertens statement, but it does not follow from the pinned product estimate by this argument. The supplied replacement explicitly uses the weaker sufficient estimate and gives the partial-summation argument. Thus the repair introduces no unpinned weighted-sum theorem.

For L1281, W_0 contains every prime <=324 by L1242. Every factor under consideration therefore has q>324>44, and

    log product_{q<=L, q not dividing W_0} (1-44/q)
      = -44 log log L + O_A(1).

The Taylor remainders are absolutely summable and the excluded prime set is fixed. Exponentiating proves the stated positive lower bound, with constants independent of L and X. A finite initial interval of allowed L can be absorbed into the constant.

For the first denominator, 1+h(q)=1/(1-g(q)). With g(q)=2/q-1/q^2 and q>Q_*>=324, log(1+h(q))=2/q+O(q^-2), uniformly. The k=4,l=1 sum therefore gives log H(z)=log log z+O_{Q_*}(1). Omitting one prime multiplies H by 1-g(ell), which is >=1/2 for ell>Q_*. This supplies uniformity in the omitted prime without any progression theorem involving that prime.

For the second denominator, the displayed bounds on g(q) imply g(q)=21/q+O(210/q^2), uniformly in Omega_q. Since g(q)<=21/325<1, the expansion of -log(1-g(q)) has an absolute uniform remainder O(q^-2). Therefore log H(z)=21 log log z+O_{Q_*}(1), independently of the root sets. The Markov step still has expectation <=42 log z, hence <=0.42 log Z, and no other coefficient changes.

Acceptance: add these locators, the two fixed-modulus substitutions, and these uniformity deductions to A021. Apply the supplied weaker weighted-sum wording. This closes the discovered accounting gap without claiming that the prime asymptotic itself supplies Mertens estimates.

## A052, with A028 cross-reference: quaternion existence and embedding

L8153 chooses B ramified at ell_0 and infinity. L8839–8843 asserts a rational embedding of the imaginary quadratic F into B because F stays a field at the two ramified places. The latter is a global local-to-global theorem, not the local lattice calculation preceding it and not merely Skolem–Noether. The existing A052 theta-source entry and A028 oriented-reduction entry do not expressly record this use.

I downloaded John Voight, *Quaternion algebras*, corrected online edition v1.0.7u, August 5, 2026. Its front matter explicitly distinguishes this corrected edition from the printed Springer edition. Do not replace its page locators with the printed edition's pages. The exact source is [the author's PDF](https://jvoight.github.io/quat-book.pdf).

Main Theorem 14.6.1, printed p223, PDF p243, classifies quaternion algebras over a global field by finite even-cardinality sets of noncomplex places. With base field Q and set {ell_0,infinity}, both places are noncomplex, distinct and the set has cardinality two. Thus B exists, is unique up to Q-isomorphism, and is ramified exactly at those places. The citation addition does not assert that this theorem constructs the Eichler order or proves the supersingular moduli description. Those remain in the original A052 source scope.

Proposition 14.6.7, printed p224, PDF p244, applies to a finite separable extension K/F of global fields. For degree two it equates an F-algebra embedding K into B with the requirement that every ramified place of B be nonsplit in K. Be careful with the letters: the source's base F is Q here; its K is the manuscript's F=Q(sqrt(Dh_*)).

The manuscript assumes D>0, Dh_* an odd fundamental discriminant, and h_*<0. The last sign is also explicitly recalled at L8889. Thus this is a separable quadratic field over Q, and its real completion is C, a field. At L8795–8797 the filter condition (D/ell_0)=1 makes ell_0 inert in this F, as already stated in the proposition. Its ell_0 completion is therefore a quadratic field. Those are all the ramified places of B. Condition (v) of Voight's proposition holds, so condition (iii) gives the rational embedding required at L8840. There are no missing requirements of unramifiedness at other primes or integrality of this rational embedding.

The next choice of z_0 is a separate local conjugacy/integrality step. The rational embedding theorem alone does not choose an optimal embedding into a fixed global order, or solve a selectivity problem for such an order. Here z_0 is allowed to vary adelically and the preceding local embedding construction supplies its components. This distinction is essential to the valid application. The supplied citation ends before that choice and makes no stronger assertion.

Acceptance: add the classification consumer L8153 and rational embedding consumers L8839–8843 to A052, with A028 recording the dependency of its comparison on this A052 subobligation. The two exact citations close the discovered gap.

## Pending patch source coverage

I inspected the pending geometry, forward-modularity, Galois-height, theta-local and root replacement material in addition to the baseline passages. The newly introduced large inputs I checked have named sources: the analytic torus algebraization in the geometry patch, the modular quotient and analytic-rank-zero theorems in the forward patch, and the explicit Casselman conventions in the theta-local patch. I found no additional independent theorem family required by those inspected repairs.

There is one small locator improvement to the root's A056 replacement. Its inline citation currently says Sutherland section 5.5, Lemma 5.20 and Theorem 5.21, then also invokes denominator nonvanishing for a nontorsion point. Add Lemma 5.24, or broaden the inline citation to sections 5.5–5.6, Lemmas 5.20 and 5.24 and Theorem 5.21. The closure report already names Lemma 5.24; this is synchronization of the proposed text with that evidence, not another missing source. See `A056-SECOND-REVIEW.md` for the limits of the lecture notes' proof completeness.

The earlier A032 review's Atkin–Lehner correction and A068 convention checks remain in their separate reports. This coverage pass does not replace those acceptance conditions.

## Scope and limits

This was a semantic pass using the actual manuscript, followed by comparison with the 82-family inventory and pending repair text. In particular I read the initial geometric/descent and modularity discussion, the prime sieve argument, the quaternionic theta setup and point comparison, and the already reviewed reciprocity and division-polynomial applications. I also considered the quadratic-twist L-function factorization used in the forward argument. In that setting it uses Euler-factor identities and the already sourced modularity/analytic inputs; I found no separate unrecorded general automorphic base-change theorem being invoked there.

This is not a second proof audit of all 82 families and does not prove that no omission exists in any sentence of the manuscript. The findings above are positive, checked omissions with complete source repairs. Searches for names and citations helped locate passages but were not used as a substitute for reading their mathematical content.
