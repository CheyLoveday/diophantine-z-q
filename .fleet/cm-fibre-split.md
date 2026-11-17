# cm-fibre-split (2026-11-17)

**Manuscript check: no error found in diophantine_zq.tex L581-586** (thm:height proof, "CM fibers"). "All its
elements are defined over L" is correct: L = EK is A8's Hom field (L544-561). G_L fixes the (e0,e0)-block End(A_Qbar)
of End(Res_{K/Q} A ⊗ Qbar), and invariant morphisms descend. Formalized: `endBC_surjective_of_homField`.

**Result.** `CMBranch.CMFibreSplit` is reduced, in Lean, to the chain's open4 leaves plus one strictly smaller
on-the-spot glue `CMCurveOrder`: End(E_Lbar) is an order of an imaginary quadratic field. Theorem:
`HDec.CMBranch.FibreSplit.cmFibreSplit_of_curveOrder` (ZInQKernel/Contrib/OneProof/CMFibreSplit.lean). It compiles
with standard axioms and no sorry.

**Proved on the way:**
* A8's Hom field at every fibre, with no NoCM and no conjugacy maps: `cmHomFieldModel_of`, built from the kernel
  field, Hom-field descent and rigidity;
* the CM case of Yu's dichotomy: `end0Matrix_of_noncentral`;
* multiples of matrix units;
* E = image of n e11, E² = E × E, and an L-isogeny E² → A via an explicit quasi-inverse, with dim E = 1:
  `matrixUnit_isogeny`.

**Fold:** dry run `HDec.HSyn.sixContactMin_of_open73_cmfs (r : OpenResearchLeaves54CMFS) t l`
(Contrib/OneProof/CMFibreSplit/Fold.lean, generated). It is cm-branch2's fold with cmFibreSplit → cmCurveOrder.
Spec: scratch/cm-fibre-split/autofold.json. GLUE column: 0 net, one GLUE replaced by a strictly smaller one; no new
leaves. #discharges is recorded; no top field is discharged, as expected: Main's top is now OpenResearchLeaves57,
and rebasing is cm-fold-rebase's job.

**Remains:** `CMCurveOrder` (report §4 sketches it). It needs End transport between algebraic closures, the
corner of a rank-one idempotent in M₂(k), the AdjoinRoot number-field instances, and integrality plus finite
conductor. Report: docs/research/cm-fibre-split.md.
