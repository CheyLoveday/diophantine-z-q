# Shared research framing and evidence boundaries

This note records the working judgment supplied with the review and the
framing used for our own follow-up decisions. It is a research thesis, not a
new theorem or a substitute for source verification. “Current size” below uses
the later Glazer comparison snapshot supplied with the review; it is not a
description of this repository's unchanged Version 10 manuscript.

## 1. Sun's advance is existential compression with shared structure

Sun reduces the existential definition of $\mathbb Z$ over $\mathbb Q$ to 28
unknowns:

$$
x\in\mathbb Z\quad\Longleftrightarrow\quad
\exists y_1,\ldots,y_{28}\in\mathbb Q:\ F(x,\mathbf y)=0.
$$

This is a substantial compression. Its importance is not merely mechanical
variable elimination: Sun makes arithmetic constraints share elliptic points,
height detectors, local predicates and a final algebraic compiler.

The final polynomial is obtained constructively, not supplied as a fully
expanded coefficient table. The argument also relies heavily on prior
arithmetic results of Glazer and collaborators and on Sun's earlier work. Our
three principal audit targets are therefore:

1. preservation of rational witnesses by the compiler at every specialization;
2. simultaneous-prime completeness, including genuine order data and tails;
3. inherited determinant, duality and integral-descent assumptions.

**No counterexample or decisive proof defect was found. The complete argument
has not been independently verified by our review.**

## 2. Glazer supplies foundations; Sun supplies compression

The comparison used to organize the next steps is:

| Issue | Glazer et al. | Sun |
|---|---|---|
| Distinctive contribution | Broad arithmetic construction and explicit polynomial representations | Radical existential-variable compression |
| Comparison snapshot | 222 total variables, degree 4 | 29 total variables; no comparably bounded degree claim here |
| Arithmetic basis | Elliptic curves, Selmer groups, local/global arithmetic and heights | Imports substantial parts of that basis |
| Sensitive verification gate | Actual arithmetic duality, normalization and universal integral descent | Correct imported applications, prime completeness and rational-witness compilation |

**Sun builds on Glazer's mathematical foundations rather than superseding
them.**

Our determinant work is directly relevant to the shared sensitive interface.
The source-relative derivation gives

$$
 c_F=-\kappa u,\qquad c_S=\kappa u,
$$

which identifies an integral-unit relationship under the retained arithmetic
hypotheses. This is a genuine clarification of the normalization interface. It
is not, by itself, a construction of global duality or a proof of universal
integral descent. In particular, the earlier description “the scalar sign is
untouched” is now obsolete; the source-relative sign relation exists and must
be quoted with its retained conditions.

## 3. The E364 bridge: marked elliptic sources, not loose curve analogies

### 3.1 A literal denominator link

For an even midpoint of a candidate powerful triple, the E364 construction gives

$$
N(N^2-1)=Ds^2
$$

and a marked point

$$
P_N=(DN,D^2s)\qquad\text{on}\qquad
E_D:\ y^2=x^3-D^2x.
$$

Powerfulness has an exact denominator translation:

$$
\boxed{\ \text{Powerful triple}\ \Longleftrightarrow\ D\mid s
\ \Longleftrightarrow\ 2D\mid B_2.\ }
$$

Here $B_2$ is the square/cube denominator base of the doubled point, which the
formal packet proves is $2s$ under the retained even-midpoint hypotheses. Odd
primes in an exponent-one defect give zero formal depth; powerfulness forces
positive depth at the odd support primes. The dyadic condition is kept
separate.

This is a real connection to formal groups and local valuations. It is not an
assertion that the E364 problem has thereby been solved. The formal packet has
since closed the powerfulness/unit-defect formulation, but it has not proved
the explicit prime-product defect formula or the ordered Kummer profile. The
original marked source and its double must remain together: doubling alone
forgets the mod-2 Kummer marking.

### 3.2 Preserve joint structure before selecting witnesses

Sun's local machinery forces the tests to hold at **one common prime above**
$p$, not at independently selected places for individual conditions. That is a
central idea for SPROUT.

An admissible representation must retain the same original midpoint, the same
ordered squarefree kernels, Kummer class and marked elliptic point, plus all
permitted local branches. If we first take marginals of these constraints and
then combine them, individually compatible fragments may describe no genuine
powerful triple. Those artificial survivors make an exclusion machinery weak
or misleading. Conversely, a convenient but unproved compatibility condition
can incorrectly discard actual sources.

The required transformation is therefore:

> translate each source with its ordered marking, aggregate only justified
> local restrictions, and preserve enough information to recover one common
> original witness.

This is also why our local review rechecked Sun's product-before-trace
valuation bound instead of accepting independent-prime reasoning.

### 3.3 The desired global contradiction shape

The transferable architecture is:

> local arithmetic restrictions $\Rightarrow$ large forced divisibility
> $\Rightarrow$ a global height bound $\Rightarrow$ incompatible growth
> $\Rightarrow$ excluded arithmetic possibilities.

This matches the contradiction mechanism we want for E364. But Sun uses a
fixed elliptic curve and fixed-carrier estimates, whereas our E364 curve
$E_D$, ranks, constants and source coordinates vary with $D$. Pell coordinates
can grow exponentially in their indices. His height constants, polynomial
index growth and prime-production estimates cannot simply be substituted.

The unresolved alternative is either:

- a source-uniform global height/growth comparison for all marked E364 sources;
  or
- another complete, source-qualified obstruction that excludes every
  candidate without relying on such a growth comparison.

A bounded calculation or an unmarked curve invariant supplies neither.

## 4. Our integrated assessment and research direction

- **Sun:** a major compression theorem with a coherent proof architecture;
  imported arithmetic, prime completeness and witness-preserving compilation
  remain substantial audit targets.
- **Glazer:** much of the shared arithmetic foundation. The source-relative
  determinant/duality derivation sharpens one sensitive interface; actual
  global duality and universal descent still require careful construction and
  checking.
- **E364:** a precise possible route: turn powerful-triple candidates into
  marked elliptic sources, preserve all justified joint local relationships,
  and seek a uniform obstruction or contradiction for the resulting source
  family.

**Central opportunity:** integrate Sun's joint local certificates and global
height strategy with the existing E364 congruent-curve, Kummer and SPROUT
machinery. That is a concrete research programme, **not yet a new E364
theorem** and not evidence that the prime-pattern, global-height or universal
descent obligations have been discharged.

## 5. How this framing changes the next work

The ownership map in `README.md` follows these priorities:

1. preserve exact source identities and markings before introducing abstract
   representations;
2. separate exact algebra from imported analytic and cohomological inputs;
3. distinguish counterexamples to weaker inferences from defects in the actual
   constructions;
4. do not claim the restricted converse, Diophantine theorem or E364 from
   scalar signs, local examples, characterwise unit values, denominator
   identities or replayed finite checks.

The deliverable is deliberately incremental: close one source-facing Lean
interface at a time, audit its quantifiers and axioms, and keep all remaining
arithmetic application assumptions visible.
