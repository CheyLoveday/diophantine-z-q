# Non-author mathematical and statement-fidelity review

Reviewer: Codex, GPT-6-based model, task `/root/review_core_contribution`. Role: read-only non-author review. No source edits, builds, tests, commits or remote operations were performed by this reviewer.

## 1. Verification target and binding

**Verdict: accepted within the bounded local-transport scope below.** No unresolved mathematical or statement-fidelity defect was found in the final snapshot.

Base commit: `3a7dce59e3d0601a3758cf924810563a6e5f0a98`.

| Reviewed artifact | SHA-256 |
| --- | --- |
| `MANIFEST.sha256` | `0ea39b7725cce044dc41ba586b552a6dabe2d5e4647c9c239d27709c0272a711` |
| `lean/Research/DerivativeSwitch/ConjugateLocalTransport.lean` | `8688eef27fcc89c02eb3ab270e5359534dc23ef16e11678bdb1dd3587e3f8b86` |
| `lean/Research/DerivativeSwitch/ConjugateLocalH1.lean` | `078ac50ae0c90c8e609a57c51c5884a25646ad7305531f1cf531617485b9078f` |
| `SPEC.md` | `c98bcf33bda7d31fb5f7e1fb013b99a6a7e01585f75b657e7f8e3ab15d365c62` |
| `APPLICATION.md` | `20b4a52e556a8a238b45a191f0f595b2f366042f0594c638c40919a6a3801b77` |
| Final `DERIVATION.md` | `ad679e62e29d97e2752a683e5c9de1ea9cf244002f76c57a716d9237654e10e0` |
| `evidence/native/RESULT.json` | `b047f06bdd83c1d02455eaaa1ee775031e67e91f51d0b03707786b7a46c94d9e` |
| `evidence/EDITORIAL_BINDING.json` | `5d7a25cb5e4161214f059637cd3acf312b73263d539eda7398e67135c6a796ce` |

Unqualified packet paths in this report are relative to `research/conjugate-local-transport/`. All 25 manifest entries were independently hash-checked and matched.

The unchanged V13 source has SHA-256 `9db71bbfcefb37db56eabcf40a5f9dd85de9ed58294635da3dbf6d4f5caa8fcd`. Both source/consumer whole-file hashes and all 11 excerpt hashes in `evidence/source-bindings.json` were independently checked.

## 2. Independent derivation and statement comparison

The core contribution is substantive: the scalar transporter action is derived from the actual twisted representation, rather than supplied as a normalization hypothesis.

From $\varphi=d\tau$ and $T(\varphi)=T(\tau)$, cancellation gives $T(d)=1$. Consequently the twist satisfies $\sigma(d)=\alpha(d)\operatorname{id}$, with the explicit unit $u=\alpha(d)^{-1}$. The complete crossed-cocycle conjugation formula retains its coboundary term; trivial action at $F$ and $I$ removes that term. Using $F=\varphi^2$ and $\varphi I\varphi^{-1}=I^\ell$ then gives

$$
c_\tau(p)(F)=u\,p(F),\qquad
c_\tau(p)(I)=u\,\ell\,p(I).
$$

The same unit therefore works for every cocycle on the fixed data. The proof does not require a field, division by two, primitive vectors, nonzero classes or a globally quadratic character. The additional hypothesis $(\ell:R)=-1$ yields the stated finite-precision sign.

This matches `ConjugateLocalTransport.lean`: the source hypotheses are explicit in `LocalData` at lines 70–85; the unit and scalar action are derived at lines 92–124; the coordinate identities are proved at lines 159–190.

The coefficient-system distinction is correct. Raw pullback lands in $\sigma\circ\operatorname{Ad}_\tau$, not generally in $\sigma$. No second $J$ is inserted. Coboundaries vanish at the relevant original and conjugated local elements.

`ConjugateLocalH1.lean` constructs evaluation and pullback through Mathlib's actual `groupCohomology.H1` and `H1π`, using the actual kernel theorem. I checked the owning Mathlib definitions and projection results in `LowDegree.lean`, particularly lines 963–999. The theorem at lines 127–142 is therefore a statement about the cohomology of the inhomogeneous cochain complex, not an invented class carrier.

## 3. Arithmetic application and retained limit

The source crosswalk is faithful to the passages reviewed: V13 2898–2967, H12 at 3225–3233, the common coefficient construction at 3339–3417, the tame model at 3434–3453, H22 at 3509–3542, and the retained-limit passages at 4454–4464 and 4577–4636.

The common finite quotient argument is sound under its stated arithmetic premises. Finite continuous affine actions provide open normal kernels. Intersecting the required kernels and their conjugates preserves both cocycles and coefficient systems. Local triviality makes the cocycles homomorphisms on wild inertia; a pro-$\ell$ group has no nontrivial continuous image in the finite 2-primary additive module when $\ell\ne2$. The tame relation consequently becomes legitimate in the common quotient.

The Frobenius orientation is consistent with the cited Nekovář convention: forward arithmetic-Frobenius conjugation supplies $\ell$. Its inverse convention supplies $\ell^{-1}$; both specialize to $-1$ at retained precision.

The final retained-unit argument also passes review, **relative to the manuscript's finite-model/retained-inner-limit construction**. One fixed ultrafilter selects compatible residues for $u_i$ and its inverse. Their product identities survive, giving an integral unit without requiring compatible moving characters. Adjoining these entries does not change existing limits.

The universal-class argument in `DERIVATION.md` 169–196 addresses the nonflat-base-change concern. A reduced limiting cycle is used directly in a matching reduced stage model. Retained contractions identify it with an actual reduced cocycle, to which the finite theorem applies. No lift to a cycle at the larger coefficient precision, or surjectivity of cohomology base change, is assumed. Separatedness then gives the limiting identity.

This establishes the local shared-unit equation in the specified retained diagram. It does not itself identify every later consumer model.

## 4. Evidence and resolved discrepancies

I inspected the native commands, audit source, elaborated statement evidence, runner and result. The supplied record reports fresh Lean 4.35 compilation of the two new modules with kernel checking enabled. Its 27 statement/axiom entries independently parse to the result's exact target map. The only reported transitive axioms are `propext`, `Quot.sound` and `Classical.choice`.

This is inspection of supplied execution evidence, not a separate proof replay by this reviewer. Imported Mathlib artifacts remain a declared cache trust boundary.

Four prose delimiter errors were found and corrected at `DERIVATION.md` lines 46, 49, 55 and 162. I inspected the exact before/after diff: only the intended function-argument parentheses were restored. The native run's original prose bytes remain retained at SHA-256 `11742329eea50c06759ec7361b369c540cb9a8912032fa4e7efea04381281259`. I acknowledge the editorial binding above; the compiled Lean sources are unchanged, and no new proof run is represented as having occurred.

The preservation receipt concerns byte preservation of the frozen packets. It is not new verification of their proofs, and their earlier external-checker results do not cover these modules.

## 5. Certification and limits

I accept the finite ring theorem, its descent to actual Mathlib H¹, and the stated human arithmetic/inner-limit application under the named source premises.

This is a non-author model review, not independent human specialist acceptance. Continuous Galois/Selmer constructions and the retained-limit lemma are not newly formalized here. Global boundary–cup adjunction, orthogonal comparison inverses, common-strict realization, actual functional rows, determinant comparisons and localization occurrence remain separate obligations.

The result removes one local normalization input. It does not prove the complete arithmetic determinant-compatibility theorem or establish a finite/singular triangle isomorphism.
