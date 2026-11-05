# Independent staging integration review

Reviewed the canonical baseline against `../staging/diophantine_zq.tex` and `../staging/EDIT_LEDGER.json`. Baseline SHA256: `a17e021ea3a6b90f861d87aff048f905b1dc31226e3445caf273739f7659e51e`. Staging SHA256: `bbf216b0590c5260539ea0f6c54a1c96e71104cdaf3a8147fadb4f47713e7fad`. Line references below refer to this staging snapshot.

## Result

No blocking mathematical integration error found in the geometry, A017, A071, or A072 changes. These edits supply conventions and arguments for the existing construction; they do not add a new arithmetic hypothesis or change its variable, degree, coefficient, or cutoff bounds. One harmless but worth-correcting identity-point notation issue is identified below. This is a focused integration review, not approval of every independent source audit.

The later A011 Fricke/realization patch is absent from this snapshot as expected. This omission is not a finding against the intended final manuscript. The independent A011 review remains in `A011-FRICKE-REVIEW.md`.

## Mechanical integration

All 44 ledger replacements have exactly one old-text match at the point they are applied. Replaying the complete ledger reproduces the staging text exactly. Evidence is in `STAGING-STRUCTURAL-CHECKS.json`; the complete comparison is in `STAGING.diff`.

No duplicate labels or bibliography keys, unbalanced net braces, or newly duplicated long paragraphs were found. The only newly introduced command names are the standard commands `\\not` and `\\twoheadrightarrow`. No accidental duplicated or contradictory text was identified in the reviewed changes. These checks do not replace a final TeX build.

## Geometry

The explicit quaternionic lattice basis and inverse-mu Rosati convention agree with the source checks in `REPORT.md`. Their insertion does not alter the algebra, polarization degree, level structure, or quotient being used. The Milne analytic-Hom paragraph supplies the missing analytic-to-algebraic bridge and descent explanation; it does not assume a new field of definition. The existing cohomology citation serves its separate purpose and is retained. The changes introduce no new counting variables or polynomial relations.

## A017: theta normalization, lines approximately 900–923

The displayed invariant normalization is internally consistent: from J2=12(j+1), J4=6(j²+j+1), J10=j³, one obtains psi4=J2²−24J4=144j and chi10=−j³/4. Hence j=16·144^5·chi10²/psi4^5. Substituting psi4=2^−2 sum(z_m^8) and chi10=−2^−14 product(z_m²) gives coefficient 144^5/2^14=3779136 exactly.

Both resulting homogeneous polynomials have degree 40. Their coefficient 1-norms are 3779136 and 10^5, respectively, so the stated additive height allowance 22 remains sufficient. The denominator is nonzero on the already specified finite, nonzero j locus. The quotient of modular forms has weight zero; a common weighted rescaling of the invariant representative cancels. No choice of separate, incompatible scalings was inserted.

## A071: formal group and cutoff

Lines approximately 1122–1203 correctly distinguish z=−x/y and w=1/x from Silverman's auxiliary coordinate. For y²=x³−d²x, direct substitution gives dx/(2y)=dz/sqrt(1+4d²z^4). Integrating its binomial expansion produces the seven displayed coefficients of L/16575. The first omitted degree is 29. At the primes p>324 under consideration, e=v(p)=1 and v(z)≥1, so its relative error has valuation at least 28. The isometry condition v(z)>e/(p−1) is satisfied, rather than inferred from a false unrestricted formal-log claim.

The ratio argument first proves integrality before replacing a relative error by an absolute congruence. Subtracting the two displayed congruences modulo p^25 gives c*(n_i−A_i)=0. The already excluded support of c* permits this division. In particular, the argument does not divide by possibly nonunit h. It preserves the original precision 25 and the original polynomial L.

The six-test argument near lines 6096–6106 treats identity coordinates separately and uses nonzero guarded denominators. The congruence-to-log-ratio step again has the needed integrality. No new nonvanishing premise is imposed on a coordinate allowed to be zero.

For the cutoff near lines 6221–6258, actual reduction orders are used as annihilators. Good reduction orders are at most (p+1)²<p³, and the bad smooth group at the specified place over 7 has order 7. The reductions (2,6) and the good conjugate place are consistent with the displayed curve and point. At most two places occur above an odd rational prime, so m0≤Ns^6 is unchanged. Odd formal valuations and the dyadic normalization v_s(2)=2 give the stated increases. Extracting rational coefficients by division by 2 and 2s loses at most three dyadic valuation units, within the displayed margin. The resulting cutoff remains M0≤Ns^10.

There is one optional notation repair in this passage. Lines 6242 and 6249 write `1/x([N_s^4m_0]P_0)` even though lines 6223–6227 deliberately permit identity points and explain that the constructor accepts them. The proof is valid by stopping immediately if the tested point is the identity, but that case split is implicit in the later reciprocal displays. To make the claimed independence from nontorsion completely literal, insert before “At each odd place”:

> If this multiple is the identity, the search has already succeeded. Otherwise its reciprocal coordinate is defined, and the following estimates apply.

Alternatively use the previously defined regular coordinate w, with w(O)=0, and state v(0)=+infinity. This does not change a bound or require a new hypothesis. The point is also proved nontorsion elsewhere, so this is not a counterexample to any stated conclusion.

## A072: CM trace and group cardinalities, lines approximately 1540–1583

The proof uses the existing congruence classes p≡1 mod 8 and p≡3 mod 7. These imply splitting in Q(sqrt(2)) and (7/p)=−1. Since the two reductions of d have product 7, the two curves are opposite quadratic twists of y²=x³−x. Their discriminants are units at these primes.

The order-four automorphism is defined over Fp and commutes with Frobenius. At the auxiliary prime 3, its polynomial T²+1 is irreducible over Q3, so its centralizer on the two-dimensional Tate module has dimension two. Injectivity of the rational endomorphism representation bounds the rational centralizer by that dimension, while Q(i) is already contained in it. Integrality of Frobenius therefore places it in Z[i], giving a²+b²=p and traces ±2a. This does not assume rational coefficients of an unrelated modular form or add a new condition on p.

Both full group cardinalities are divisible by four because the full 2-torsion is rational. Their sum is 2(p+1), whose 2-adic valuation is exactly two for p≡1 mod 8, so the common 2-primary factor is exactly four. Hasse's bounds put each cardinality between zero and 2p for p>324; divisibility by four excludes equality to p. The text correctly uses these cardinalities as annihilators, without calling them the exact orders of the reduced points. All original degree and coefficient budgets are unaffected.

## Remaining final-integration checks

Apply the later A011 patch, perform citation/application rebinding against the final text, and run the normal TeX build. The optional identity-case sentence above may be incorporated during that integration. No shared file was changed by this review.
