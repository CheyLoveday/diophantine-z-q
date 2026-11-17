# hgz-steps manual fold spec (hGZ is a frozenTarget binder: autofold.py does not apply)

Edits to `ZInQKernel/OneProof/Main.lean` (not made here; the integrator applies them):

1. Add `import ZInQKernel.Contrib.OneProof.GrossZagierScheme` (after `import ZInQKernel.Contrib.OneProof.GrossZagierAlgebraic`).
2. In `ZInQ.OneProof.frozenTarget`, retype the binder
   `(hGZ : ZInQ.GZAlg.GrossZagierAlgOptCd)` -> `(hGZ : ZInQ.GZSch.GrossZagierCurveCd)`.
3. In the body, replace `ZInQ.GZAlg.grossZagierFormulaCd_of_alg hGZ` by
   `ZInQ.GZAlg.grossZagierFormulaCd_of_alg (ZInQ.GZSch.grossZagierAlgOptCd_of_curve hGZ)`.
4. Module docstring, GZ bullet: "Gross–Zagier over the algebraic curve X₀(N) (`hGZ`)" -> "Gross–Zagier for a
   modular parametrization π : X₀(N) → E, a morphism of ℚ-schemes (`hGZ`, hgz-steps' `GZSch.GrossZagierCurveCd`,
   bridged by `grossZagierAlgOptCd_of_curve`)".
5. kinds.tsv: replace the row `frozenTarget hGZ` by the row in `kinds-row.tsv`. locators.md: add the row in
   `locators-row.md`. Regenerate OPEN.md (OpenStatements.lean, render_open.py, --check).

The new modules (`GrossZagierScheme.lean` and `GrossZagierScheme/{Core,EpsD,Model,PointTau}.lean`) import gz-dict2's
`GrossZagierPlane.lean` and `GrossZagierPlane/Extension.lean` (branch `wip/gz-dict2`, merged into this branch).

Check: `scratch/hgz-steps/FoldCheck.lean` is the result of 2-3 as a separate theorem `ZInQ.HGZSteps.frozenTarget_hgz`;
`#print axioms` gives `[propext, Classical.choice, Quot.sound]` (FoldCheck-output.txt). No existing constant changes
except `frozenTarget`.
