# A011: the Fricke-stability condition in Shimura's realization

Date: 2026-11-05. This note discharges the specific Fricke condition found by the galois-height reviewer in Shimura 1973, Theorem 1, printed p.526. It does not replace that reviewer's other A011 checks.

Conclusion: the condition holds for the full coefficient-conjugate span of the weight-two primitive newform used by the manuscript, including arbitrary nebentypus and arbitrary coefficient field. The exact primary source is Wen-Ch'ing Winnie Li, *Newforms and Functional Equations*, Mathematische Annalen 212 (1975), 285–315, printed p.296, the paragraph immediately before Lemma 6. This statement is unnumbered; it should not be cited as part of Lemma 6 or as Theorem 7, which has different hypotheses.

## Sources actually checked

The galois-height reviewer supplied the GDZ METS and OCR for the published article. I located the relevant text in the OCR, then downloaded and visually checked four original page scans:

| Printed page | GDZ order/image filename | Checked content |
|---|---|---|
| 285 | 293 / `00000293.jpg` | Title, publication, weight, slash action, arbitrary-character space |
| 294 | 302 / `00000302.jpg` | Primitive/newform definition, normalization, old/new decomposition and uniqueness |
| 296 | 304 / `00000304.jpg` | Fricke operator, coefficient conjugation, their effect on the new space, exact scalar relation |
| 298 | 306 / `00000306.jpg` | Theorem 5, strong multiplicity one at arbitrary character |

`A011-FRICKE-PINS.json` gives the exact scan URLs, hashes, and local paths. The published article has DOI [10.1007/BF01344466](https://doi.org/10.1007/BF01344466). No separate erratum to this statement was found in the targeted title/erratum search. This is the 1975 published version, not a later set of notes.

The galois-height OCR filenames are offset: `li-295.xml` contains printed page 296. Use the printed page and METS order, not the local OCR basename, for citation. The scans resolve the bars over characters and coefficients that the OCR loses.

## Exact conventions and hypotheses

Li's introduction on p.285 fixes a positive integer weight k and defines the slash action by

`(F|A)(tau) = det(A)^(k/2) * (c*tau+d)^(-k) * F((a*tau+b)/(c*tau+d))`.

Her space `C_epsilon(M,1)` is the cusp-form space of weight k and character epsilon for Gamma_0(M), viewed inside the Gamma_1(M) space. The character can be any Dirichlet character modulo M with `epsilon(-1)=(-1)^k`; it need not be primitive. Thus the manuscript's k=2 case has epsilon(-1)=1, with no assumption epsilon=1.

On p.294 she defines a newform as a nonzero common good-prime Hecke eigenform in the orthogonal complement of the old space, and normalization as a(1)=1. The discussion establishes uniqueness and decomposition into forms coming from primitive forms at divisor levels. This agrees with the primitive newform selected after twisting in A011.

On p.296 define

`H_M = [[0,-1],[M,0]]`, and `(F|K)(tau)=overline(F(-overline(tau)))`.

Here K is an antilinear operation on forms, not the coefficient field. It conjugates every Fourier coefficient. Both H_M and K send the epsilon space to the conjugate-epsilon space and preserve newness. The paragraph before Lemma 6 asserts for every normalized newform F that

`F|H_M = gamma * (F|K)`

for a scalar gamma. The scalar is nonzero since H_M is invertible and F is nonzero. The proof immediately above uses the preservation of old/new spaces, the Hecke relations, and uniqueness. No rational-coefficient, real-coefficient, trivial-character, or prime-level hypothesis appears. No algebraicity or coefficient-field membership of gamma is needed below.

## Why all coefficient conjugates are still primitive

Let f be the manuscript's normalized primitive weight-two form of level N, and E its full Fourier-coefficient field. Shimura's Theorem 1 supplies f^sigma at the same level for every embedding sigma:E->C, with the conjugate Fourier coefficients and eigenvalues. The nebentypus is conjugated as well; its values are recovered from the good-prime Hecke relation and hence belong to E.

One can justify primitivity without adding an assumption about E or citing an unidentified Galois-invariance theorem. Suppose f^sigma came from a primitive form g of level M properly dividing N. Extend sigma to an automorphism of the algebraic numbers. Apply the coefficient-conjugate existence part of Shimura's Theorem 1 at level M to g with the inverse automorphism. This produces a weight-two eigenform at level M whose good-prime eigenvalues equal those of f. Li's old/new decomposition on p.294 then supplies a primitive form h of some level L dividing M with those eigenvalues. The character of h induces the original character of f, since conjugating back restores the nebentypus. Li's Theorem 5, p.298, says that two normalized primitive forms with the same good-prime eigenvalues have the same level and are equal. This forces L=N, contradicting L|M<N.

This argument uses Shimura's coefficient-conjugate existence, which is unconditional in the earlier part of Theorem 1, not its later zeta-function assertion. It therefore does not use the desired Fricke-stability conclusion circularly. The same old/new decomposition and uniqueness show that an eigenform whose primitive level is N is itself the normalized primitive form there.

## The required invariant span

Set `V = span_C { f^sigma : sigma:E -> C }`, exactly the full span in Shimura's theorem. Write c for ordinary complex conjugation on algebraic numbers. Coefficientwise conjugation sends f^sigma to f^(c composed with sigma). This is another element of the same list of embeddings, whether or not E is Galois or its chosen image is invariant under c.

Apply Li's result to each primitive f^sigma:

`f^sigma | H_N = gamma_sigma * f^(c composed with sigma) in V`.

At weight two the slash normalization above gives

`f^sigma(-1/(N*z))/z^2 = N * (f^sigma | H_N)(z)`.

Thus V is stable under precisely the map stated in Shimura's Theorem 1, not just under an operator with an unchecked normalization. Multiplication by N and the nonzero scalar gamma_sigma does not affect a complex vector-space span. The map is invertible, so this is equality of the image with V. No single form is asserted to be a Fricke eigenform when the character is nontrivial.

Consequently the additional Fricke premise of Shimura's zeta-function conclusion is discharged for the primitive weight-two form in A011. Shimura's conclusion is still the product over all embeddings, up to the indicated finite set of Euler factors. Extracting the chosen 5-adic constituent and keeping track of duality remains the separate comparison addressed in the galois-height review.

## Suggested manuscript addition

At the first use of the modular abelian variety, the following text makes this condition explicit:

```tex
For completeness, the Fricke condition in Shimura's realization theorem
holds for the full coefficient-conjugate span of the primitive form $f$.
Li's newform relation gives
$f^\sigma|_2H_N=\gamma_\sigma f^{c\sigma}$ for every coefficient
embedding $\sigma$, where $H_N=\left(\begin{smallmatrix}0&-1\\N&0\end{smallmatrix}\right)$
and $c$ is complex conjugation
\cite[p.~296, paragraph before Lemma 6]{li1975}.
The map $h(z)\mapsto h(-1/(Nz))/z^2$ is $N$ times this slash operator,
so it preserves that span. This permits nontrivial nebentypus.
```

Add Li's p.285 conventions and p.294/p.298 primitivity argument to the audit record. A short manuscript need not repeat the full Galois-primitivity proof, but the explicit audit dependency should remain.
