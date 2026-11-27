# Local-global decomposition-group glue

## Statement and status

The existing interface `ZInQ.Contrib.RC53Assist.GlobalTrace.DecompositionGroupLocalGlobalGlue` asks, for a rational prime p and a given global arithmetic-Frobenius datum D, for:

- a valuation on an algebraic closure of the p-adic completion, extending the existing local valuation up to equivalence;
- an embedding of the algebraic closure of Q into that local algebraic closure and a restriction homomorphism of the corresponding Galois groups;
- equivariance through that same embedding;
- equality of the image of local inertia with inertia at D.place;
- a local arithmetic Frobenius whose image is D.element.

The implementation at reviewed commit `5404d2b6a80a35863194abc8fc736a923a901e52` inhabits this unchanged interface. It adds `PlaceConjugacy.lean`, `SpectralPlace.lean`, `GaloisLift.lean`, `LocalGlobal.lean`, and `Glue.lean` under `ZInQKernel/Contrib/RC53Assist/DecompositionGlue/`. The independent review approved the contribution with notes, with no correction requested to those five files and no additional assumed copy of the glue proposition.

A dated integration receipt on 19 November 2026 records all five files on main `320e81c0c878dadd6e81bac494c19f5cd0fe1c5e`, with file blobs identical to the reviewed `5404d2b6a80a35863194abc8fc736a923a901e52` source. The original review commit is not an ancestor of main: [PR 141](https://github.com/Deicyde/diophantine-z-q/pull/141) carried the same files in its own commits, including `7b950b3253b5ccb232cab9e98cfbbd7aeb3afb5a`, and landed through merge `740aa8edca40a1e583381a51e0a142bb29512d95`. This records file-level integration without changing or erasing the original proof history.

The separate isolated build, axiom check and Jacobian import-closure check remain blocked in that receipt; they have not run. File presence on main and the earlier review do not substitute for those checks. Public credit/roadmap integration is also a separate delivery step. No whole restricted-converse or original Diophantine proof is asserted.

## Classical ingredients

The standard number-theoretic ingredients have precise source locations in Milne's *Algebraic Number Theory*, version 3.08, 19 July 2020:

1. Theorem 7.38, p. 123: a complete discretely valued field has a unique extended absolute value on a finite separable extension, which is complete, with the norm formula. Corollary 7.40, p. 124, extends uniqueness to separable algebraic extensions.
2. Corollary 7.42, p. 124: the finite extension degree is e f, with f the residue degree.
3. Corollary 7.52, pp. 128–129: for the stated perfect complete-field setting, the residue field of the algebraic closure is the algebraic closure of the residue field. This applies to Q_p and F_p.
4. Proposition 8.2, p. 136: completion at a place of a finite number-field extension gives a finite extension of the completed base, with the product decomposition.
5. Proposition 8.10 and its footnote, p. 139: at finite Galois level, the decomposition group is isomorphic to the Galois group of the completion; restriction is the inverse map.

Milne's text is the author's course notes. These finite-level statements are not a literal quotation of the complete infinite-level interface. Choosing the compatible embedding and passing to the required local/global witnesses is an argument assembled from the classical theory.

A classical alternative uses Krasner's lemma and its finite-extension generation corollary: Lang, *Algebraic Number Theory*, second edition, Springer 1986, corrected third printing 1994, Chapter II section 2, Proposition 3, p. 43, and Proposition 4 with its corollary, p. 44. This gives the compositum equality between the image of the global algebraic closure and Q_p inside the local algebraic closure. It is a route to the stronger group identification, not an extra hypothesis of the existing interface.

The reviewed implementation instead uses density and approximation. It proves preservation of local minimal polynomials, constructs compatible finite lifts, and uses compactness to obtain a local automorphism. Density also gives local residue representatives and restriction injectivity. It does not need an explicit Krasner/compositum-generation step. This is not a claim that every transitive library dependency is independent of Krasner's lemma.

## Place, residue and Frobenius compatibility

The embedding is chosen after the given global place. An embedding unrelated to that place would give the decomposition group of a different, conjugate place, which would not satisfy the intended same-place statement.

All residue actions are transferred through the residue map induced by the same embedding. Local elements are algebraic over Q_p, not necessarily over Q. Local residue algebraicity therefore uses finite extensions of Q_p and their finite residue degree. Global residue algebraicity uses algebraicity over Q. The residue of a general algebraically closed valued field need not be algebraic over F_p; a Gauss valuation on an algebraic closure of Q_p(T) is a counterexample to that broader claim.

Arithmetic Frobenius means the p-power residue action. Milne p. 141 states the convention for a finite unramified prime and elements of its ring of integers. The predicate on an infinite valuation ring is not that literal finite uniqueness theorem; its transfer is proved separately. Geometric Frobenius, the inverse convention, is not substituted.

The reviewed construction uses the nonnegative reals as an ordered commutative valuation codomain with zero. The extension clause forces p to have value strictly between zero and one. The review also tested the p=2 case against trivial valuation and identity-Frobenius interpretations.

## Verification boundary and roadmap classification

The independent review reports exact-statement checks, re-elaboration of byte-identical source copies, non-vacuity probes, stronger place/restriction checks, and a proof/type dependency audit. The axiom output is the three standard logical axioms. No nonstandard axiom, admission, unsafe or partial dependency, or project-authored opaque constant was reported in the reached closure.

A literal assertion that the entire dependency graph has zero opaque constants would be false: safe standard-library and Mathlib implementation wrappers remain. Imported Lean/Mathlib artifacts retain their ordinary trust boundary; the review did not independently rebuild every upstream artifact. The additional isolated current-tree verification remains an open, separately recorded gate; it is not retroactively completed by the merge.

The appropriate roadmap classification is a completed classical argument and reviewed implementation present on main, with isolated current-tree verification still pending. It is not completion of Theorem 5.3, pole completeness, the original Z-in-Q definition, or the H10 consequence. Existing claim, credit and review ledgers remain canonical; this research note is not a second claim hub.

## References

- Milne, *Algebraic Number Theory*, v3.08 (19 July 2020), author's course notes: https://www.jmilne.org/math/CourseNotes/ANT.pdf . Exact locators are listed above.
- Lang, *Algebraic Number Theory*, second edition (1986), corrected third printing (1994), GTM 110, Chapter II section 2, pp. 43–44. The consulted public text is https://archive.org/stream/algebraic-number-theory/Algebraic%20Number%20Theory_djvu.txt .
