# Tenth closure pass: division polynomials and the fixed-scalar relation

Date: 2026-11-05. Reviewer: root assistant. Scope: A056, against manuscript SHA256 `a17e021ea3a6b90f861d87aff048f905b1dc31226e3445caf273739f7659e51e` and the repository's `construction/elliptic-division-polynomials.js`. This record replaces the unresolved errata retrieval requirement in batch 2 with an explicitly identified source for the corrected formulas. It does not claim that the official Silverman errata PDF was downloaded.

## Exact source and its limits

Andrew V. Sutherland, MIT 18.783, Fall 2025, Lecture 5, *Isogeny kernels and division polynomials*, dated September 18, 2025. The MIT OpenCourseWare PDF has 15 PDF pages and printed lecture pages 1–14. The full file is pinned as `closure/primary/sutherland-2025-lecture05.pdf`, SHA256 `4d638ce3bbe1127ae7947a8b4deda6c6e51247912194bbacaf3920d4c9bb19d7`.

Retrieval URL: https://ocw.mit.edu/courses/18-783-elliptic-curves-fall-2025/mit18_783_f25_lec05.pdf

The relevant statements are the explicit definitions on printed p.10, Lemma 5.20 and Theorem 5.21 on p.11, the recurrence verification on p.12, and Lemma 5.24 on p.14. These are openly published lecture notes, not a peer-reviewed research article. Theorem 5.21 is explicitly stated for the multiplication map; its proof gives the division-polynomial recurrence calculation and refers to Washington for the complete proof, leaving analogous numerator calculations to the reader. This audit uses that theorem as a standard source theorem. It does not misrepresent the notes as a newly machine-checked or entirely self-contained proof.

In particular the source explicitly writes the minus sign in the numerator of omega. The note on p.11 identifies typos in Silverman III Exercise 3.7. The new source therefore supplies the corrected statement directly. It is unnecessary to infer a formula from search-index excerpts or to pretend that the unavailable official errata file has been inspected.

## Objects, hypotheses, and conventions

The actual curve has characteristic zero and equation `y^2=x^3+A*x`, with `A=-d^2` and nonzero d. Its discriminant is nonzero. Sutherland uses the short equation `y^2=x^3+A*x+B`; specialize `B=0`. This avoids the characteristic-two/three caveat and the extra terms in the general-Weierstrass ordinate convention.

The source's Jacobian coordinates `(phi_n:omega_n:psi_n)` mean affine coordinates `(phi_n/psi_n^2,omega_n/psi_n^3)`, not ordinary projective coordinates. The distinction is necessary for the exponent four in the implemented ordinate equation.

Put `psi_n=f_n` for odd n and `psi_n=2*y*f_n` for even n. The source's four initial values give exactly

```
f_0=0, f_1=f_2=1,
f_3=3*x^4+6*A*x^2-A^2,
f_4=2*(x^6+5*A*x^4-5*A^2*x^2-A^3).
```

The convention `f_0=0` is compatible with `psi_0=0`. It is not obtained by dividing a value at a point with y=0. All normalizations are first polynomial identities in the coordinate ring of the generic short equation.

## Recurrences and signs

The source recurrence for an odd index is

```
psi_(2m+1)=psi_(m+2)*psi_m^3-psi_(m-1)*psi_(m+1)^3.
```

If m is even, the first term contains four factors of `2*y`; the second contains none. If m is odd, the second term contains those four factors. Since `(2*y)^4=16*(x^3+A*x)^2`, these are precisely the two branches in `normal(n)`. There is no extra sign or division.

The even recurrence is

```
psi_(2m)=psi_m/(2*y) *
 (psi_(m+2)*psi_(m-1)^2-psi_(m-2)*psi_(m+1)^2).
```

If m is even, the outside `2*y` cancels and the bracket has one factor `2*y`. If m is odd, the bracket has two factors `2*y` and the denominator cancels one. In both cases normalization of `psi_(2m)` leaves exactly

```
f_(2m)=f_m*(f_(m+2)*f_(m-1)^2-f_(m-2)*f_(m+1)^2).
```

The explicit base cases cover m=1,2. For every recursive call above those bases the requested subindices are smaller than the input. Thus the recursion terminates and uniquely specifies polynomials with integer coefficients. This matches the manuscript and code, including the negative-index convention `psi_(-n)=-psi_n`.

The corrected source numerator is

```
omega_n=(psi_(n+2)*psi_(n-1)^2-psi_(n-2)*psi_(n+1)^2)/(4*y).
```

Comparison with the even recurrence yields `psi_(2n)=2*psi_n*omega_n`. At n=1,2 the same identity follows from the displayed initial values. Theorem 5.21 therefore gives, whenever `psi_n(P)` is nonzero,

```
x([n]P)*psi_n(P)^2
  =x(P)*psi_n(P)^2-psi_(n+1)(P)*psi_(n-1)(P),
2*y([n]P)*psi_n(P)^4=psi_(2n)(P).
```

These are exactly the two field equalities in `fixedScalarRelation`, whose `psi(2n*n)` expression is JavaScript BigInt syntax for `psi(2*n)`, not `psi(2*n^2)`.

## Domain guards and both directions

The advertised precondition is that P belongs to the torsion-free carrier D. For n nonzero and P not the identity, `[n]P` is not the identity. The multiplication theorem and coprime numerator/denominator statement identify the zeros of `psi_n` with the nonidentity n-torsion. Consequently the inverse-norm guard on `psi_n(P)` is satisfiable for every such P.

Conversely, on the guarded finite branch `psi_n(P)` is nonzero. The two cleared equalities then determine the actual affine coordinates of `[n]P`, so any admitted finite R equals `[n]P`. This direction does not need torsion-freeness beyond the predicate's ambient carrier assumptions. The zero-index branch explicitly requires R to be the identity; the nonzero identity branch explicitly requires both P and R to be the identity. For negative n the implementation replaces P by `-P` and n by `-n`, which agrees with the short-model inverse `(x,-y)` and `[n]P=[-n](-P)`.

The inverse-norm implementation over Q(sqrt(2)) is a separate field-encoding interface. This check consumes its established equivalence with nonzero field elements; it does not count a syntactic inverse variable as evidence of that equivalence.

## Disposition

A056's recurrence, normalization, ordinate, domain, and source-identity obligations can be closed using this replacement source and the existing field-encoding and carrier premises. The 44 valid and 74 invalid numerical cases recorded in batch 2 are regression examples only. The justification for arbitrary fixed n is the source multiplication theorem and the generic polynomial calculations above.

The source list and manuscript must explicitly add Sutherland's notes before this disposition is applied to the canonical inventory. The failed official-errata download remains honestly recorded as historical retrieval failure, rather than a current essential dependency.
