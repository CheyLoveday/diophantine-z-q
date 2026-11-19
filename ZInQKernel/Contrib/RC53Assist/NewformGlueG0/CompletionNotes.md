# G0 completion: exact consequences and source boundaries

## New source

`GaloisCompletion.lean` is the sole new proposed Lean module. It contains the
new declarations below without importing unbuilt new helper modules. The
previously committed component modules are unchanged. The working source
fragments and audit material are kept in `Scratch/`.

The unchanged target is
`ZInQ.Contrib.CloudB3RC53.ModularWeil.LiCarayolNewformOfModular`.

There are two precise assemblies of that target:

1. `Descent.liCarayolNewformOfModular_of_printed_corollaries`, from four
   independent manuscript-cited literature interfaces, with the object
   readings listed below. This proof does not assume either Tate local
   reading used by the second assembly.
2. `Completion.liCarayolNewformOfModular_of_representations`, from the
   rational Carayol realization, Faltings semisimplicity, the same proved
   coefficient-field descent, and two explicitly named remaining Tate
   readings. This proves all representation and coefficient assembly steps,
   but does not declare those two readings proved.

Neither statement is an unconditional proof of the literature inputs. The
inputs remain propositions used as theorem parameters, not new axioms.
No input is the newform-existence conclusion for the original elliptic curve.

## The coefficient-field descent

The additional printed source is Shimura 1973, Theorem 1, p. 526, manuscript
bibitem `shimura-factors`. For the genuine weight-two trivial-character
newform `F`, define its actual coefficient field

`C_F = ℚ(a_n(F) : n ≥ 0) ⊆ ℂ`.

`Shimura1973ConjugateEigenforms` retains the finite coefficient-field reading
and the theorem's conjugate eigenforms: for every complex embedding of `C_F`,
there is a normalized full eigenform on the same `Γ₀(M)` whose coefficients
are the embedded coefficients. The existing newform API proves that `F` is
a normalized full eigenform, so the printed common-eigenfunction premise is
not inserted as an unproved bridge.

The new Lean proof is as follows.

* A conjugate form has the original curve's prime coefficients outside the
  same finite set, since those coefficients are integers and every rational
  algebra embedding fixes them.
* The proved old/new decomposition extracts a newform of divisor level from
  the conjugate full eigenform, with the inducing trivial character.
* Li 1975, Theorem 5, p. 298, forces this extracted newform to have the original
  level and to be the original newform.
* The proved whole-character-space multiplicity-one theorem then identifies
  the conjugate form itself with `F`, at every coefficient, not just almost
  all prime coefficients.
* Consequently all complex embeddings of the actual coefficient field are
  equal. `AlgHom.card` gives degree one over the rationals. A rank-one
  vector-space argument proves every coefficient rational.

`embedding_fixes_coefficients`,
`coefficients_rational_of_almost_all_primes`, and
`coefficientField_eq_bot_of_almost_all_primes` prove these steps. The last
statement identifies the actual coefficient field with the rational subfield;
the common completion `ℚ_ℓ` is therefore justified, not chosen by fiat.

## The independent printed-corollary route to exact G0

`Carayol1986RationalNewformEulerFactors` starts with a genuine rational
newform, not the input elliptic curve. Shimura's rational quotient construction
provides the associated curve `A`, and Carayol's Corollaire of §0.8, p. 411,
identifies its local Euler factors with those of the newform. The interface
retains the corresponding actual local polynomial identities.

The proof never asserts that this associated curve is the original curve `E`.
Their coefficients agree at almost all primes by the already proved extraction
and the curve's local polynomial dictionary. The already proved arithmetic
dictionary converts that into equality of their local polynomials almost
everywhere. Faltings 1983, §5, Korollar 2, iii ⇒ iv, p. 361, supplies equality
at every finite place.

The proved prime-power recurrence and coprime multiplicativity then return
all positive coefficients. The output is exactly a newform `F : Newform M 2`
with `M ∣ N`, trivial character, and

`(qExpansion 1 F.toCuspForm).coeff n = (E.LFunction n : ℂ)`

for every `n > 0`. The original level and quantifier order are unchanged.
`newformOfModularCurveGlue_of_printed_corollaries` also returns the original
newform-periods G0 interface through the previously proved full-eigenform and
subgroup conversion.

This route uses the rational Corollaire only after rationality has been proved.
Its curve-existence input is the reverse construction from a rational newform
to its associated curve; it is not an input asserting a newform for `E`.

## Actual representations, not placeholders

`integralTateRep E ℓ` is precisely the existing coordinatewise Galois action on

`T_ℓ(E(AlgebraicClosure ℚ))`.

`rationalTateRep E ℓ` is its scalar extension to `ℚ_ℓ`.
`extendedTateRep E ℓ K` is the further scalar extension into a common field.
The integral, rational, and extended two-element bases, their dimensions,
and matrix-continuity assertions are proved. Continuity of basis coordinates
uses the continuous scalar action and the compact-to-Hausdorff inverse theorem;
no replacement topology is assigned to the Tate module.

`Carayol1986ThmAWeightTwoQ` states the number-field-completion form of the
printed source: the realization field is an actual finite number subfield of
the complex numbers containing the actual newform coefficients, and the
representations live over its actual completions at places above `ℓ`.

`Carayol1986ThmARationalWeightTwo` is the rational realization used after
coefficient descent. `CarayolRationalRealization` supplies an actual
representation of the genuine absolute Galois group on `ℚ_ℓ²`, with continuity,
plain irreducibility, the normalized good-prime traces and the local-factor
reading at every `p ≠ ℓ`. Its `cohomologicalRep` is explicitly its dual.

The irreducibility assertion comes from Carayol's printed Remarque after (A),
p. 411; that paragraph credits an unpublished argument of Ribet. It is not
silently made a clause of the literal theorem (A), and no unsupported absolute
irreducibility or oddness assertion is inserted. Faltings 1983, Satz 3, p. 360,
provides semisimplicity of the actual rational Tate representation. No extension
of that printed semisimplicity statement into arbitrary coefficient fields is
silently assumed.

`LocalArithmeticFrobenius` holds a genuine valuation place, a genuine Galois
element, the arithmetic residue-field action, and the integral-closure Frobenius
reading. Existence at every specified rational prime is proved by lying-over
and the existing finite-layer Frobenius existence theorem. `inertiaAt` is the
actual inertia kernel mapped from the actual decomposition group, and its
normalization by Frobenius is proved.

`tate_equiv_Carayol_of_almost_all_primes` applies the already proved
characteristic-zero Brauer–Nesbitt and Čebotarev comparison to precisely these
representations. `localTatePolynomial_eq_newform_of_comparison` transports the
actual inertia-fixed Frobenius polynomials, including bad primes.

The final representation assembly chooses an auxiliary prime different from
each prime being compared. Thus the factor at `p = ℓ` is never obtained by
illicitly applying Carayol at that same auxiliary characteristic.

## The newly proved local good-reduction dictionary

`Completion.goodReductionFrobeniusTraceDictionaryQ_proved` has exactly the
existing type
`NewformPeriodsDictionary.GoodReductionFrobeniusTraceDictionaryQ`.

It reproduces the proof in `FrobeniusTraceDictionary/Proved.lean` through its
compiled dependencies: the proved Tate-reduction comparison and
`DetDegree.frobeniusTateDetFormOne_proved`. It is not a new literature input,
and the local trace-and-determinant formula is not re-assumed.

## Exactly what remains on the raw representation route

1. `GlobalGoodReductionTraceReading` is the globalization of the now proved
   local good-reduction dictionary. It identifies the actual global Tate
   action on the algebraic closure of the rationals with the relevant local
   completion action, at the actual integral-closure Frobenius. The reading
   includes global inertia triviality and trace and determinant normalization.
   It is explicitly GLUE, not a statement about arbitrary curves attributed
   to Carayol. Sources for the intended reading: Silverman VII.3.1, VII.7.1;
   the completion restriction of the actual Tate action.
2. `BadReductionTatePolynomialReading` identifies the Frobenius polynomial
   on the actual global Tate inertia invariants with the actual bad minimal
   Weierstrass polynomial. It is explicitly GLUE, not a Carayol theorem about
   every arbitrary elliptic curve. Intended sources: the local determinant
   definition before Faltings Korollar 2, p. 361; Silverman VII.6–7 and
   Appendix C.16, p. 449. The Silverman body at this locator was not page-checked.

All implications after these two readings are proved, including passage through
the injective rational embeddings, equality of each prime-power coefficient,
and the complete positive-index coefficient assembly. The independent
printed-corollary route does not depend on these two propositions.

## Literature interfaces and locators

All the following bibliography items occur in the manuscript.

* `shimura-factors`: Shimura 1973, Theorem 1, setting pp. 525–526 and theorem
  p. 526: finite coefficient field and conjugate common eigenforms; rational
  one-dimensional quotient. The exact theorem is quoted in the existing
  `NewformPeriods/Leaves.lean`. A fresh publisher PDF retrieval for this
  continuation did not succeed; no new page-image check is claimed.
* `li-newforms`: Li 1975, §2 p. 294, Theorem 3(i), (iii) p. 295, and Theorem 5
  p. 298. The old/new and full-eigenform parts are proved by the imported APIs;
  the strong multiplicity-one specialization remains a literature parameter.
  The manuscript's locator p. 296 is the different Fricke-conjugation step.
* `carayol`: Carayol 1986, §§0.4–0.6 pp. 409–410, (A) in §0.7 pp. 410–411,
  irreducibility Remarque p. 411, rational Corollaire §0.8 p. 411.
* `casselman`: Casselman 1973, Theorem 1 and proof pp. 302–306, Corollary p. 306,
  ε-factor Remark p. 307, Theorem 4 p. 313. These supply the newvector and
  newform-level local reading of Carayol's automorphic compatibility.
* `faltings1983`: Faltings 1983, §5, Satz 3 p. 360; Korollar 2, especially
  iii ⇒ iv, p. 361. These pages were checked against the legitimate Göttingen
  article images in this continuation.
* `silverman`: Silverman 2009, III.7, VII.3, VII.6–7, Appendix C.16 p. 449.
  The publisher's full book was unavailable. The public back matter confirmed
  the index locator p. 449, but not the body of Appendix C.16.

The source interfaces are faithful specializations or explicitly labeled
corollary consequences. In particular, the newform/automorphic representation,
dual normalization, associated-curve/Weierstrass, and normalized polynomial
readings are named as readings, not claimed to be a literal replacement of
Carayol's statement about automorphic representations. No scheme construction
of the associated quotient is newly implemented here.

The level divisibility `M ∣ N` is proved. No new assertion `M = conductor(E)`
is made, and no elliptic-curve conductor is defined as a substitute.

## Verification records

The standalone `GaloisCompletion.lean` and the complete scratch audit both
compile with the prescribed single-file command. The audit covers 70 new
declarations, including all 36 theorem/lemma declarations. Every individual
axiom report is exactly `[propext, Classical.choice, Quot.sound]`.

`Scratch/CompletionTheoremStatements.md` contains every theorem's exact
printed type and individual `#print axioms` report, together with the unfolded
target and literature interfaces. `Scratch/CompletionAxioms.txt` is the raw
output, and `Scratch/CompletionAxioms.lean` is the complete audit input.
`Scratch/CompletionAuditSummary.json` records the complete declaration data.

The primary source fingerprint is preserved after verification. The four
previously committed component fingerprints are unchanged. Source policy
checks found no prohibited declarations, execution commands, or identifiers.
