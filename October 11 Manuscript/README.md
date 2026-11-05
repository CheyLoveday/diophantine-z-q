# Comparison of the 10/11 and 11/4 manuscripts

This folder preserves the [10/11 manuscript PDF](ZIsDiophantineInQBySohailsGPT-6.pdf), *A conditional Diophantine definition of Z in Q from four arithmetic inputs*, dated October 11, 2026. The [11/4 manuscript PDF](../diophantine_zq.pdf) and [TeX source](../diophantine_zq.tex) are in the repository root.

These notes compare the statements, proof architecture, and quantitative claims of the two manuscripts. They are not a new independent proof audit. Page references below refer to the 25-page 10/11 PDF. The comparison was checked on November 5, 2026, against the 141-page revision of the 11/4 manuscript.

## Provenance

The October 11 Manuscript was produced by Sohail Farhangi with ChatGPT 6. The November 4 Manuscript was produced by Elliot Glazer with Astra 6, Sol 6.1, and Opus 5.5, with auditing from Fable 5.1.

## Shared mathematical strategy

Both manuscripts build on arithmetic inputs from OpenAI's October 6 preprint, *Hilbert's tenth problem over the rational numbers*. Both use the elliptic curve over $F=\mathbb Q(\sqrt 2)$ given by

$$
E:\quad y^2=x^3-d^2x,\qquad d=75-53\sqrt 2.
$$

An infinite cyclic subgroup supplies integer labels $nP$. Finite certificates based on pole parity and formal-group estimates allow arithmetic on those labels, including multiplication.

Both manuscripts then address a separate problem: identifying the ordinary rational scalar $n$ with the elliptic-curve label $nP$. A Diophantine model of integer arithmetic alone does not identify the literal subset $\mathbb Z\subseteq\mathbb Q$.

The scalar identification has the same broad structure in both manuscripts. Certificates control the primes with odd contact order for a candidate rational number. A height estimate bounds its logarithmic height in terms of that prime support. Sufficiently strong approximation to the labelled integer then forces equality. Both constructions encode variable precision inside a fixed finite existential formula.

## Differences in scope and construction

| Aspect | 10/11 manuscript | 11/4 manuscript |
| --- | --- | --- |
| Arithmetic scope | Explicitly assumes four OpenAI arithmetic inputs: pole parity, rank one, a five-point height estimate, and compatible prime patterns. It does not independently verify their proofs or companion-paper dependencies. | Presents an unconditional argument, with extended justifications for its arithmetic inputs, including the restricted converse, pole completeness, and an explicit height estimate. The current revision replaces the von Känel–Kret dependency. |
| Integer arithmetic | Constructs finite formulas for general polynomial relations on the integer labels, then specializes to multiplication. | Uses a specific multiplication construction and a concrete computation and polynomial compiler. |
| Contact and support certificates | Uses five projective contact points, including infinity, leaving four finite linear forms. Separate support certificates relate rational scalars to integer labels. | Uses six finite contacts, a combined product/trace pole test, and a shared auxiliary shift $\kappa$. |
| Completeness interface | Assumes a pole predicate complete on all integers and builds a support relation complete on every nonzero integer. | Uses a pole-completeness result for specially prepared inputs, together with the shift and witness constructions needed by the final formula. |
| Final equality test | Uses variable-precision congruence at the fixed prime $3$. | Uses real approximation with an explicit precision bound depending on the integer label and $\kappa$. |
| Quantitative specification | Uses MRDP for fixed computably enumerable relations and leaves several fixed arithmetic constants and the final formula size unspecified. | Specifies the polynomial through finite expressions and substitutions and gives simultaneous bounds on variables, degree, and coefficients. |

The 10/11 manuscript states its conditional scope on pages 1–4. Its shorter length partly reflects that scope. The 11/4 manuscript's unconditional presentation should be distinguished from independent human peer review or a completed Lean verification; see the repository's [verification status](../README.md#verification-status).

## The final scalar identification

The most substantial difference is the choice of approximation.

In the 10/11 manuscript, Sections 12–14 construct a congruence relation expressing

$$
\operatorname{Cong}_3(x,nP,kP)\quad\Longleftrightarrow\quad v_3(x-n)\ge k.
$$

The construction uses a Diophantine definition of $\mathbb Z_{(3)}$, formal-group approximants, and the relation $b=16\cdot3^k$ encoded on integer labels. The four finite contact forms give a height bound, and the chosen precision $K(n)$ makes a nonzero difference impossible: the congruence would force

$$
K(n)\log 3\le h(x-n)<K(n).
$$

In the 11/4 manuscript, the final construction uses a real height-and-distance argument. Its certificates give a bound $h(x)\le B(n,\kappa)$ and require

$$
|x-n|<e^{-B(n,\kappa)}.
$$

If $x=a/b$ is in lowest terms and $x\ne n$, then $|x-n|\ge1/|b|\ge e^{-h(x)}$, contradicting the required distance. The shared shift $\kappa$ connects the support certificate to the precision computation.

The fixed-prime construction in the 10/11 manuscript is therefore a possible alternative to the real-approximation step in the 11/4 manuscript. Establishing that it gives a smaller or simpler fully specified polynomial would require instantiating its constants and counting the resulting formulas.

## Variable, degree, and coefficient bounds

The bounds must be compared for the same polynomial, with all auxiliary variables counted.

| Quantity | 10/11 manuscript | 11/4 specified polynomial |
| --- | --- | --- |
| Total ambient variables | $N+1$, with $N\ge1$ unspecified. No numerical upper bound is supplied. | $292{,}890{,}231{,}905$, including the rational input. |
| Degree | No bound is stated for the raw final polynomial in Corollary 14.3. An equivalent polynomial of degree at most $4$ is available after introducing additional variables, as explained below. | Less than $2\uparrow\uparrow7$. |
| Maximum absolute coefficient | No numerical upper bound is supplied. | Less than $2\uparrow\uparrow8$. |

Here $2\uparrow\uparrow r$ denotes a right-associated tower of $r$ twos. The three 11/4 bounds apply simultaneously to its specified polynomial. The variable count is an ambient bound, not a claim that every variable occurs essentially.

Section 8 of the 10/11 manuscript, on page 12, explicitly converts an intermediate reduction polynomial $Q_f$ to degree at most four. Introduce variables for arithmetic-circuit gates, write each addition or multiplication gate as an equation of degree at most two, and take the sum of the squares of those equations together with the required output equation. Over $\mathbb Q$, that sum vanishes exactly when every equation vanishes.

The same conversion applies to the final defining polynomial $D$ in Corollary 14.3, preserving its free rational input. This extension is a deduction from the stated conversion, rather than a separately quantified bound in that corollary. It introduces further witness variables whose number is not given.

The same quartic conversion also applies to the 11/4 polynomial, with additional variables. Consequently, the quartic bound alone does not establish a quantitative advantage for either construction. The 10/11 manuscript explicitly leaves some fixed constants unspecified on pages 4, 22, and 24; without them and a counted compilation, no numerical comparison of the final variable counts or coefficient sizes is available.

## Source identity

The 10/11 PDF is included without modification. The current 11/4 files include the November 5 AI attribution update naming Fable 5.1; their mathematical text is unchanged from the revision used for this comparison. The current files have the following SHA-256 hashes:

```text
e5752baaf5ed8bc44707a9e96be545276ea6587349ece8f8030c78006f7983d6  ZIsDiophantineInQBySohailsGPT-6.pdf
c59598ba474a1512dd03787c2bc9ff093a3c3a8a0604f96d5f8bcfa140c61693  ../diophantine_zq.tex
3ae95226ebcd477aa3b29ecf8600cb0a47b830f761d9bf6e3388e5b76ed9f84b  ../diophantine_zq.pdf
```
