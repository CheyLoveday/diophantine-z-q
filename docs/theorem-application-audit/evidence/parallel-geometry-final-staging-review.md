# Final staging review

Reviewed on 2026-11-05. This is a read-only integration and rendered-output review of the staged manuscript, not a new whole-proof audit.

## Bound artifacts and result

- TeX SHA256: `f880d559e9a76281573e4d5110852f347bc422af3f2daf0b483fbb7f01c62fb3`.
- PDF SHA256: `571f3b0cf5861e788c098f7d55f4d75536eb857fe46b4ac55bd8335ab6d5f39a`.
- Baseline SHA256: `a17e021ea3a6b90f861d87aff048f905b1dc31226e3445caf273739f7659e51e`.
- PDF length: 148 pages.

The staged TeX and PDF match the requested hashes and `BUILD.json`. All 53 ledger replacements have exactly one matching old passage when applied in order, and the replay reproduces the final TeX exactly. No new mathematical discrepancy or blocking layout defect was found in the reviewed changes. Final inventory acceptance fields still need to be merged as described below; the TeX/PDF themselves are acceptable within this review's scope.

## Mathematical and source integration

The quaternionic basis, inverse-mu Rosati convention and analytic-to-algebraic Hom argument match `REPORT.md`. The additions preserve the degree, field and height bounds. The A017 weighted invariant normalization retains the degree-40 numerator and denominator and coefficient 3779136. The explicit identity case requested in `STAGING-REVIEW.md` is now inserted before the reciprocal-coordinate estimates; no extra nontorsion premise is needed there.

The A011 paragraph now includes the Li Fricke formula and Shimura quotient/Euler-factor application. It matches the source interface checked in `A011-FRICKE-REVIEW.md`: coefficient conjugates span a Fricke-stable space, with no restriction to rational coefficients or trivial nebentypus. The paragraph retains the Tate/cohomological duality distinction and conductor invariance. Its new citations resolve to Li p.296 and Shimura Theorem 1 in the bibliography. This replaces the expected omission in the earlier staging snapshot.

The AFP insertion names the correct definitions and lemmas and explicitly distinguishes the integer-valued recurrence from natural-valued uses. Its bibliography records the exact authenticated revision `b4f3b892d0ae25cea27412ba4007cdb63e44b0eb`, not an inferred Isabelle release. The formula blocks are unchanged by this source addition.

The new Voight citations occur at the correct two claims: existence of the algebra ramified at {ell_0,infinity}, and existence of a rational quadratic-field embedding. The second citation ends before choosing the adelic integral realization, so it does not imply optimal embedding into an arbitrarily fixed global order. The bibliography correctly names corrected edition v1.0.7u, August 5, 2026, pp.223–224. This satisfies the source-addition condition in my A052 acceptance, and A028 can reference the resulting subobligation.

I read ledger entries 16–19 and 40 and the rendered local-cochain discussion, including its continuation. The new passage states the retained precision, trivial local character, generator choices, possible transfer shear, and retained D^0 term before using the local matrices. It does not silently replace arithmetic Frobenius by geometric Frobenius or discard the finite/singular transport. In the contraction formulas, the declared convention is 1−ip=dh+hd. Direct expansion then gives the displayed composition identity with right side Ld−dL, so the sign is consistent. A degree-minus-one map on these derivative conditions lands in retained D^0; the displayed degree-minus-two map vanishes on them. The distinction between this derivative model and old Kummer conditions is explicit. The cochain construction and its full source acceptance remain the theta-local/forward reviewers' scope; this pass found no transcription or integration change invalidating those stated conventions.

The finite-coefficient stalk/Leray passage names its affine, quasi-compact, quasi-separated generic-point map. The inverse-limit passage explicitly uses finiteness of degree-zero groups and Mittag–Leffler before removing the lim-one term. These are visible and legible rather than omitted from the compiled text. None of these source/convention additions changes the displayed construction's variable, degree or coefficient budget.

## Rendered checks

I rendered the staged PDF with pypdfium2 and visually inspected pages 8, 10, 12, 14, 45–46, 77–78, 84, 94–95, 103, 135, 137 and 144–148. The page images are under `geometry/final-staging/`. Pages are identified by both PDF position and printed number, which agree in this file.

These cover the quaternionic and Milne additions; A011; theta normalization; both pages of the new local-cochain argument; AFP definitions; the identity/cutoff repair; stalk and inverse-limit passages; a representative amended Selmer-complex passage; the wide pre-existing equation; and every bibliography page.

The inspected formulas, superscripts, subscripts, accents and quotation-free theorem references render correctly. There are no clipped lines, missing glyphs, overlapping text or unresolved citation boxes in these pages. The local-cochain paragraph crosses pages 45–46 at an ordinary sentence continuation; its composition identity and the next numbered subsection remain readable. The AFP sentence crosses pages 77–78, but its definition names and continuation are intact. Bibliography URLs wrap within the page; the long AFP revision is complete and legible. No duplicate bibliography entry or repeated inserted paragraph was found.

The build log has no TeX errors or unresolved references. It does contain the following nonblocking width warnings:

- A 0.66798-point overfull line in the new AFP paragraph, TeX L5856–5863/PDF p.77. The line extends imperceptibly into the right margin; no content is cut. An optional line-break adjustment could remove the warning but is not required for readable output.
- A 1.08102-point paragraph warning at L1087–1090 and a 14.9669-point display warning at L10341. The latter is the unchanged combined definition of B, b1, bp and H on PDF p.135. It visibly extends into the margin but remains entirely on the page. It is present in the baseline formula and was not introduced by these edits.

The remaining log warnings are underfull lines, principally bibliography/URL wrapping, and the harmless inputenc warning under the Unicode engine. I did not find a corresponding loss of content in the inspected pages. This is a targeted visual inspection, not a claim to have viewed every one of the 148 pages.

## Anchors and acceptance overlay

The final TeX has no duplicate label or bibliography keys, and every literal citation key has a bibliography entry. `rebind-reviewed-result.json` is bound to the correct final TeX hash and reports success: zero errors, zero unclassified new citations, 150 citation mappings, 286 line mappings and 147 active citation roles. This includes explicit mappings for removed citations rather than treating their absence as an accidental shift.

I also inspected the relevant application records in that result. A028 and A052 include the `voight-quaternion` key and the newly mapped sites. A077 and A079 carry the intended completed source-check status and locators. However, this rebind result is still a pre-acceptance-overlay artifact for A028, A052 and A054: their statuses remain `specified_not_freshly_verified`, A052's locator omits Voight, and A054 still has the old unused all-cusp-vanishing description. This is not a TeX defect. Before canonical inventory regeneration, merge `geometry/ACCEPTANCE-UPDATES.json` (aligned to the actual source key `voight-quaternion`) and the other reviewers' final acceptance updates. In particular A054 must describe automorphy and holomorphy in M_(3/2), not certify a stronger cuspidality argument absent from its consumer.

No additional manuscript repair is requested by this review. Preserve the final source hash and rebind results when applying the acceptance overlay. No shared file was modified.
