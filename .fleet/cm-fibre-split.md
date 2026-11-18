# cm-fibre-split (2026-11-17)

**Manuscript check: no error found in diophantine_zq.tex L581-586** (thm:height proof, "CM fibers"). "All its
elements are defined over L" is correct: L = EK is A8's Hom field (L544-561). G_L fixes the (e0,e0)-block End(A_Qbar)
of End(Res_{K/Q} A ⊗ Qbar), and invariant morphisms descend.

**Result: `CMBranch.CMFibreSplit` is proved**, statement verbatim, from leaves the chain already carries at the
open4 generation:
* Yu's dichotomy (`hYu`);
* T6 (`t.t6`);
* NOS (`r.r7a`);
* Raynaud (`r.r6`);
* torsion structure (`t.t5`);
* the chain's own G2 (`fibreCoverExists_of_propTSAll'`).

It needs no new leaf and no new glue. Theorem: `HDec.CMBranch.FibreSplit.cmFibreSplit_of_leaves`
(ZInQKernel/Contrib/OneProof/CMFibreSplit.lean, with Reduction/Curve/CurveOrder.lean). It compiles with standard
axioms and no sorry; scratch/cm-fibre-split/Statement.lean checks the verbatim copy with Iff.rfl.

**Steps, all in Lean:**
* A8's Hom field at every fibre, with no NoCM and no conjugacy maps: kernel field, Hom-field descent, rigidity;
* the CM case of Yu's dichotomy;
* multiples of matrix units;
* E = image of n e11, E² = E × E, and an L-isogeny E² → A via an explicit quasi-inverse, with dim E = 1;
* End(E_Lbar) is an order of Q(√d). This uses the corner of a rank-one idempotent, End transport between algebraic
  closures, integrality from T6, and finite conductor via cm-branch2's discr_order.

**Fold: the CM fold is one GLUE lower.** Dry run `HDec.HSyn.sixContactMin_of_open73_cmfs (r : OpenResearchLeaves54CMFS) t l`
(Contrib/OneProof/CMFibreSplit/Fold.lean, generated) is cm-branch2's fold with the field cmFibreSplit removed.
Spec: scratch/cm-fibre-split/autofold.json. Against cm-branch2's spec: GLUE −1, no new leaves. #discharges is
recorded; no top field is discharged, as expected: Main's top is now OpenResearchLeaves57. cm-fold-rebase should call
`cmFibreSplit_of_leaves` at its open4 generation.

**Remains:** nothing for CMFibreSplit. Known issue: the CM case enters through Yu (T27, pre-existing) rather than the
manuscript's own L563-577 dichotomy. Report: docs/research/cm-fibre-split.md.
