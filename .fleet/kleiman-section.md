# kleiman-section (fleet note)

**Result.** `kleimanPicZeroProper` is restated over Kleiman's own functor `T ↦ Pic(X_T)/Pic(T)`, and the comparison
with the tree's `picardFunctor` is a Lean theorem that needs **no section**:
`KleimanSection.picardFunctorIsoKleiman : picardFunctor f ≅ kleimanPicardSheaf f`, for any `f`. Pic(T) classes are
Zariski-locally trivial, so the quotient map is locally bijective. The identity components agree
(`identityComponent_repKleiman`). File: `ZInQKernel/Contrib/OneProof/KleimanPicZeroProperQuot.lean`. It builds, has no
sorry and uses only the standard axioms.

**Leaves.**
- `KleimanPicZeroProperPrinted` (recommended). Kleiman 9.5.4 in its weakest reading: X proper, geometrically
  integral, geometrically normal, projective and with a K-point. It is a consequence of the print whether the print
  assumes proper or projective. With the étale reading it follows by Kleiman 9.2.5. Rated: printed form.
- `KleimanPicZeroProperQ`. Same hypotheses as the old leaf. Printed form only under the proper/fppf reading.

**Folds.**
- Hand fold (recommended): `scratch/kleiman-section/TailZ56.lean` gives `OpenAddedLeaves26` and
  `sixContactMin_of_open49`. Its conversion goes to `OpenAddedLeaves22PZ` through `picZeroAbVar0_of_printed`.
  `FrozenCheck.lean` compiles frozenTarget with this fold.
- Autofold (fallback): `scratch/kleiman-section/autofold.json`. `#discharges` shows `kleimanPicZeroProper` discharged
  by `kleimanPicZeroProper_of_Q`. The dry run reports counts 11/18 -> 11/18 and compiles.
- Either way the field the review rated GLUE becomes a LEAF: −1 GLUE against the review, no new GLUE.

**Remains.** Kleiman's numbering and hypotheses are UNVERIFIED (no copy on the host). A locators.md row is needed.
Report: docs/research/kleiman-section.md.
