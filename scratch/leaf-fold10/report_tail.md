## 6. `frozenTarget`: removed and added hypotheses

**Bundles.**
- Removed: `t : OpenTextbookLeaves9`, `l : OpenAddedLeaves8`.
- Added: `t : OpenTextbookLeaves10`, `l : OpenAddedLeaves9`.
- `r : OpenResearchLeaves9` and `g : OpenGlue7` are unchanged.

**TYZ / GZ.** `h11`, `h29`, `hS`, `h33`, `hL2`, `hL3` are unchanged.

**Fields removed (2):**
- textbook `dimJacobianEqGenus` (`ZInQ.Contrib.CurvesG.DimJacobianEqGenus`): proved outright, with no hypotheses
  (dimjac-glue, `ModularSplit.DimJac.dimJacobianEqGenus`);
- added `y3Connected` (`TSHecke.Y3Connected`): proved from the new field `deligneComponentsY3Printed`
  (shimura-glue's `deligneComponentsY3_of_printed`, shimura-split's `y3Connected_of_deligne`).

**Fields added (1), added-leaf bundle:**
- `deligneComponentsY3Printed : ShimuraGlue.DeligneComponentsY3Printed`.

One removed field is proved outright: `dimJacobianEqGenus`.
