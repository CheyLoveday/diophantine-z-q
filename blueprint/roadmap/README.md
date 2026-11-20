---
article_id: af_c6be9f76e8285425161078ad
open_statements: allowed
---

# Z is Diophantine in Q

This blueprint formalizes Theorem 1.1 of the 11/5 manuscript *ℤ is Diophantine in ℚ*:
an integer polynomial in 292,890,231,905 variables, of degree below $2\uparrow\uparrow 7$
and with coefficients below $2\uparrow\uparrow 8$, whose rational zero projection to the
first variable is exactly $\mathbb Z$.

The proof has one target, a shared construction and two inputs: the six-contact height estimate and
pole completeness. There are two routes to the pole input, and each gives a headline theorem. Both are
headlines; they are means to the same end.

| | Elliot's route | The congruent-number route |
| --- | --- | --- |
| Headline | [The main theorem by Elliot's route](main/main-theorem.md) | [The main theorem by the congruent-number route](main/main-theorem-reading-a-gross-zagier.md) |
| Pole polynomial | the manuscript's, with curves $y^2=x(x-\ell)(x+3\ell)$ | a variant, with the congruent number curves $y^2=x(x-\ell)(x+\ell)$ |
| Pole input | pole completeness (Theorem 5.2), derived from the restricted converse (Theorem 5.3) | the certified rank hypothesis, from Tian–Yuan–Zhang's Theorem 3.5(2) in reading A and Gross–Zagier |
| Height input | the minimal height hypothesis | the minimal height hypothesis |
| Lean | this fork's main, `ZInQ.OneProof.frozenTarget` | the tag `route-k-final` (`ZInQ.Contrib.GaussFE.frozenTarget_of_sixContactMin_tyzThm35ReadingA_grossZagier`); pinned upstream in elliotglazer/diophantine-z-q, whose main has the form that also assumes Hecke's continuation and the functional equation; nasqret/z-in-q-lean builds on it |

**The height input.** Both headlines assume the minimal form of the six-contact height estimate, the one
instance of the manuscript's Theorem 4.1 that the proof uses. It is not a published theorem: its proof
combines refereed theorems and exact computations with new arguments, the manuscript's and this
project's, reviewed only by AI models. [The height-decomposition chapter](height-decomposition/README.md)
derives it from statements of the literature. It may also be assumed in its $j$-form, a bound on the height
of the Hauptmodul value (not a published theorem) from which the minimal form is proved. A separate
project reaches an ineffective height estimate by another route
([a note on it](height-von-kanel-note.md)).

**Elliot's route.** Pole completeness is the manuscript's Theorem 5.2: an explicit polynomial, whose
rational zeros put two points on curves $y^2=x(x-\ell)(x+3\ell)$, has a zero for every suitably prepared
input. The manuscript derives it from its restricted converse theorem (Theorem 5.3) by a simultaneous
2-descent (Section 5.1). That derivation is formalized:
`ZInQ.Manuscript.PoleS12.poleCompleteness_of_restrictedConverseGenuine_casselsTatePairing` proves
Theorem 5.2 from Theorem 5.3, the Cassels–Tate pairing on the curves $E_\ell$, the modularity theorem of
Breuil, Conrad, Diamond and Taylor, and a consequence of Kolyvagin's Theorem 1. The single proof
`ZInQ.OneProof.frozenTarget` takes these four as hypotheses (`hRC`, `hCT`, `hB` and `hK`), beside the open
statements of the height estimate. The proof of Theorem 5.3 (Sections 7–9 and Appendices E–G) is reduced
in Lean to the results it cites (some in consequence form) and one structure of remaining hypotheses,
which are not proved, so `frozenTarget` still takes Theorem 5.3 as one hypothesis.

**The congruent-number route.** Until fork issue #77 this fork used it in place of pole completeness: a
variant of the pole polynomial for the congruent number curves, whose pole completeness follows from the
certified rank hypothesis, derived from Tian–Yuan–Zhang's Theorem 3.5(2) in reading A and from
Gross–Zagier. Its Lean is kept at the tag `route-k-final` and pinned upstream in
elliotglazer/diophantine-z-q, and nasqret/z-in-q-lean builds on it. Its chapters are listed under the pole
input below.

**The shared construction.** The manuscript's other inputs are proved, multiplication from the height and
pole inputs. The Mordell–Weil theorem for the generator curve, which the generator input uses and which
was first stated as a hypothesis, is proved too. Two of these proofs depart from the manuscript:
- The bound for the prime catalogue follows from an effective Dirichlet theorem, with a larger cutoff
  than the manuscript's.
- The manuscript's twenty-two-prime pattern is not needed. A change in the completeness proof, route
  AP, uses long arithmetic progressions of good primes instead. These come from Szemerédi's theorem in
  the primes, from a Lean proof of the Green–Tao theorem, and from a density theorem for those primes.

Everything else is proved, with every finite computation checked by the Lean kernel.

## Chapters

### Target and headlines

- [The main theorem and its hypotheses](main/README.md)

### Shared construction

- [The finite specification of the polynomial](syntax/README.md)
- [The elliptic model of integer indices](model/README.md)
- [Multiplication and the finite false-triple guard](multiplication/README.md)
- [Exact precision computation and polynomial compilation](compiler/README.md)
- [Assembly and the ordinary-value relation](assembly/README.md)
- [The cutoff and polynomial size](size/README.md)
- [Primes in arithmetic progressions](progressions/README.md)
- [Long progressions of good primes replace the prime pattern (route AP)](route-ap/README.md)
- [Szemerédi's theorem in the primes (Green–Tao)](green-tao/README.md)
- [The density of good slope primes (Proposition D)](density/README.md)

### Height estimate

- [The minimal height hypothesis from the literature](height-decomposition/README.md)
- [An ineffective height estimate through von Känel's bound (nasqret/z-in-q-lean)](height-von-kanel-note.md)

### Pole input

#### Elliot's route

- [Pole completeness from the restricted converse (Theorem 5.2 from Theorem 5.3)](pole-completeness-from-5-3/README.md)
- [The restricted converse (Theorem 5.3)](restricted-converse/README.md)

#### The congruent-number route

- [Pole completeness from certified rank](route-k/README.md)
- [The explicit system is the 2-Selmer group (Proposition 0)](selmer/README.md)
- [The row-5b determinant](rank-5b/README.md)
- [Rédei's formula for the 4-rank of class groups](redei/README.md)
- [The rank hypothesis as positive rank](rank/README.md)
