# A056 independent second review

Reviewed 2026-11-05. I checked `closure/BATCH-010.md`, the actual division-polynomial implementation, and the new Sutherland source against manuscript SHA256 `a17e021ea3a6b90f861d87aff048f905b1dc31226e3445caf273739f7659e51e`. No shared files were changed.

The proposed source replacement and the mathematical application pass. Closure is conditional on actually adding the Sutherland reference to the manuscript and canonical source register, as batch 10 itself requires. It resolves the need for a source stating the corrected formula; it does not retroactively establish that the official Silverman errata were retrieved. No implementation change is needed.

## Sources and exact evidence

The replacement is Andrew V. Sutherland, MIT 18.783, Fall 2025, Lecture 5, *Isogeny kernels and division polynomials*, dated September 18, 2025. I read the definitions on printed p.10, Lemma 5.20 and Theorem 5.21 on p.11, the verification on p.12, and Lemma 5.24 on p.14. The pinned PDF has 15 pages, the last an OCW notice. Its hash is `4d638ce3bbe1127ae7947a8b4deda6c6e51247912194bbacaf3920d4c9bb19d7`, verified from `closure/primary/sutherland-2025-lecture05.pdf`. The [MIT source URL](https://ocw.mit.edu/courses/18-783-elliptic-curves-fall-2025/mit18_783_f25_lec05.pdf) identifies the same lecture and date.

The reviewed implementation is `construction/elliptic-division-polynomials.js`, SHA256 `ce4d92950444eff9e590dfb3ecb9fa78e84fdbb7348891166f8f90b2300364d7`. I also read the field operations and point-code branches it calls in `construction/rational-elliptic-core.js`. The relevant manuscript definitions are lines 210–222 and the fixed-point formulas at 6398–6408.

This is acceptance of three standard external source statements: polynomial parity/integrality in Lemma 5.20, multiplication in Theorem 5.21, and coprimality in Lemma 5.24. It is not a proof audit establishing every line of the lecture from scratch.

## Source proof completeness

Batch 10 correctly describes the notes' status and limits. Theorem 5.21 explicitly gives the required multiplication map. Its proof cites Washington Theorem 9.33, verifies the psi recurrence, and leaves the analogous phi and omega checks to the reader. Lemma 5.20 similarly sends its induction to Washington. The short proof of Lemma 5.24 invokes the interpretation of division-polynomial zeros as torsion; it should not be presented as an independent, self-contained derivation of the zero-locus property from the recurrence alone.

Accordingly, the supported claim is that Sutherland states the corrected standard theorem and that the manuscript's substitution satisfies its hypotheses. Neither these notes nor the finite regression examples constitute a machine-checked proof of the general multiplication theorem. If an independent proof of that theorem, rather than an application audit, is later required, the omitted numerator inductions and the zero-locus/coprimality argument remain to be supplied or checked in a complete source. This qualification does not prevent using the expressly stated theorem and lemma in the present audit.

The minus sign in omega is displayed directly on p.10. Footnote 5 on p.11 separately warns of typographical errors in Silverman III Exercise 3.7. Thus the repaired application need not depend on an unseen errata PDF or on an assertion that the 2009 printed formula is correct. A source substitution is legitimate when explicitly recorded; it is not legitimate to mark the old official-errata retrieval as successful. Batch 10 makes this distinction.

## Hypotheses and normalization

The field is Q(sqrt(2)), of characteristic zero. The actual coefficient is `A=-11243+7950 sqrt(2)=-(75-53 sqrt(2))^2`, and B=0. The factor `75-53 sqrt(2)` is nonzero, since its norm is 7. Thus A is nonzero and the discriminant `-64 A^3` is nonzero. The curve is a nonsingular short-Weierstrass elliptic curve covered by the source. No characteristic-two or characteristic-three modification is needed.

The source uses Jacobian coordinates. Its triple `(phi_n:omega_n:psi_n)` has affine coordinates `(phi_n/psi_n^2,omega_n/psi_n^3)`. Treating it as an ordinary projective triple would give the wrong denominators. Batch 10 retains the correct convention.

With `psi_n=f_n` for odd n and `psi_n=2y f_n` for even n, the source initial values at B=0 give exactly the four memoized nonzero indices:

```
f_1=f_2=1,
f_3=3x^4+6Ax^2-A^2,
f_4=2(x^6+5Ax^4-5A^2x^2-A^3).
```

The choice f_0=0 gives psi_0=0. This is a polynomial normalization, not evaluation of a quotient by y at a point with y=0.

## Every recursive branch

The source odd recurrence is `psi_(2m+1)=psi_(m+2)psi_m^3-psi_(m-1)psi_(m+1)^3`.

- If m is even, the first product has four factors 2y and the second has none. The result is `D*left-right` with `D=16(x^3+Ax)^2`, exactly the code.
- If m is odd, the second product has those four factors, giving `left-D*right`, exactly the other code branch.

For the even recurrence, write the source bracket as `psi_(m+2)psi_(m-1)^2-psi_(m-2)psi_(m+1)^2`. If m is even it contains one factor 2y, while the prefactor psi_m/(2y) is f_m. If m is odd it contains `(2y)^2`, while the prefactor is f_m/(2y). Dividing the result by the single factor 2y that defines f_(2m) gives in both cases

`f_(2m)=f_m (f_(m+2) f_(m-1)^2-f_(m-2) f_(m+1)^2)`.

There is no remaining factor of 2, y, or the curve polynomial. The code implements precisely this expression. The identities are first taken in the generic coordinate ring, where the source's polynomial divisibility justifies the cancellation, and then specialized. They do not divide by a point coordinate during execution.

For even input n>4, n>=6 and the largest recursive index n/2+2 is smaller than n. For odd input n>4, n>=5 and the largest recursive index floor(n/2)+2 is smaller than n. The remaining indices are nonnegative. Bases 0 through 4 therefore terminate every branch. The public psi function handles negative indices by `-psi(-n)`, matching the source convention. Structural induction consequently identifies all generated polynomials with the normalized source polynomials for every fixed integer n; a finite sample test is not being substituted for this induction.

## Ordinate identity and both graph directions

The corrected formula is

`omega_n=(psi_(n+2)psi_(n-1)^2-psi_(n-2)psi_(n+1)^2)/(4y)`.

Comparison with the even recurrence gives `psi_(2n)=2 psi_n omega_n`. At n=1 the base values give omega_1=y and psi_2=2y; at n=2 they give omega_2=psi_4/(4y) and psi_2=2y. Thus the small cases also agree. On the open set psi_n!=0, Theorem 5.21 yields

```
x([n]P) psi_n(P)^2
  = x(P) psi_n(P)^2-psi_(n+1)(P)psi_(n-1)(P),
2 y([n]P) psi_n(P)^4 = psi_(2n)(P).
```

These are exactly the two equations in `fixedScalarRelation`. The JavaScript expression `2n*n` is a BigInt literal 2 multiplied by the variable n. It denotes 2n mathematically, not 2n squared. The code's `fsquare(g2)` is psi_n^4, since g2=psi_n^2.

For the forward implication, P is assumed to belong to the torsion-free carrier D. If n!=0 and P!=O, then [n]P!=O. Lemma 5.24 together with the multiplication map identifies psi_n=0 with the nonidentity n-torsion: the coprime x-coordinate denominator has no removable zero. Hence the actual [n]P satisfies the finite equations and the nonzero guard.

Conversely, the guard makes psi_n invertible. Dividing the first equation by psi_n^2 and the second by 2 psi_n^4 recovers both affine coordinates of [n]P. Thus any accepted finite R equals [n]P. No separate R-on-curve condition is needed: the two forced coordinates already are those of [n]P. This converse would fail without the guard because cleared equations alone can acquire extraneous solutions at torsion.

The guard is on the full psi_n, including its 2y factor for even n, not merely on f_n. Consequently it does not accidentally accept points with y=0 for even scalar multiplication. In the implementation it introduces the rational inverse of the field norm `g_0^2-2g_1^2`. In Q(sqrt(2)) this norm is nonzero exactly when g is nonzero, since sqrt(2) is irrational. Its rational reciprocal exists in precisely that case. This verifies the elementary field interface locally while leaving the repository's general witness compiler as a separate implementation premise.

For n=0, the predicate is exactly R=O under its stated input-carrier precondition. For n!=0, P=O is handled only by the branch requiring R=O. On the finite branch both flags are zero. For negative n, the code replaces P by -P and n by -n; on the short model this negates both ordinate components and preserves the canonical O code. Since D is a subgroup, this retains the carrier precondition and implements `[n]P=[-n](-P)`.

The function does not itself assert P∈D. Its correctness is conditional on the documented precondition and the callers that establish it. The theorem replacement does not remove that requirement or independently prove D is torsion-free. The same nonvanishing reasoning applies to the fixed point P_0 in manuscript lines 6404–6408 using its separately established nontorsion property.

## Disposition

Accept batch 10's recurrence, normalization, source identity, guard, and graph-equivalence conclusions with its stated carrier and compiler premises. The explicit source replacement is adequate for an external-theorem application audit, even though the lecture proof is not fully self-contained. The general argument is structural induction plus the cited multiplication and coprimality statements; the 44 valid and 74 invalid numerical examples remain regression checks only.

Before recording canonical closure, add Sutherland's exact edition and locators to the source register and cite it at the division-polynomial application. Keep the unsuccessful official Silverman-errata retrieval as a historical fact. Do not rephrase this result as verification of the unseen errata, a full independent proof of Theorem 5.21, or unconditional correctness on arbitrary five-tuples outside the input carrier.
