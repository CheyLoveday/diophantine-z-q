# gz-dict2 manual fold spec (hGZ is a frozenTarget binder: autofold.py does not apply)

Edits to `ZInQKernel/OneProof/Main.lean` (not made here; the integrator applies them):

1. Add `import ZInQKernel.Contrib.OneProof.GrossZagierPlane` (after `import ZInQKernel.Contrib.OneProof.GrossZagierAlgebraic`).
2. In `ZInQ.OneProof.frozenTarget`, retype the binder
   `(hGZ : ZInQ.GZAlg.GrossZagierAlgOptCd)` -> `(hGZ : ZInQ.GZDict2.GrossZagierPlaneOptCd)`.
3. In the body, replace `ZInQ.GZAlg.grossZagierFormulaCd_of_alg hGZ` by
   `ZInQ.GZAlg.grossZagierFormulaCd_of_alg (ZInQ.GZDict2.grossZagierAlgOptCd_of_plane hGZ)`.
4. Module docstring: in the GZ bullet, "Gross–Zagier over the algebraic curve X₀(N) (`hGZ`)" ->
   "Gross–Zagier over X₀(N) with φ read on the plane model (`hGZ`, gz-dict2's `GZDict2.GrossZagierPlaneOptCd`,
   bridged by `grossZagierAlgOptCd_of_plane`)".
5. kinds.tsv: replace the row `frozenTarget hGZ` by the row in `kinds-row.tsv` (first line; the second line is the
   alternative under the strictest reading). Regenerate OPEN.md (OpenStatements.lean, render_open.py, --check).

Check: `scratch/gz-dict2/FoldCheck.lean` is the result of 2-3 as a separate theorem `frozenTarget_gzdict2`;
`#print axioms` gives `[propext, Classical.choice, Quot.sound]` (FoldCheck-output.txt). No existing constant
changes except `frozenTarget`.
