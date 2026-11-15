# x6-glue (2026-11-14)

**Result.** Both X₆ fields are theorems from seven leaves (VERIFIED, compiled, standard axioms):
`HDec.QMSplit.Moduli.r1r2_of_published` (→ `LeafAdopt.R1R2fpRep`) and `x6ConicModel_of_published`
(→ `X6Kummer.X6ConicModel`); bundled as `X6Leaves` / `x6Rows_of_leaves`. Six leaves are in published form:
* `DeligneComponentsX6Printed` (Deligne's π₀ display at level 𝒪̂^×);
* `GeomConnOfAlgClosure` (textbook, weakened);
* T5 (textbook);
* `BabaGranathRational` (printed; one table reading UNVERIFIED);
* `GonzalezRotgerX6` (printed);
* the new `ElkiesEquationsX6` (see below).

One leaf is still a consequence: `RayClassCM` (Shimura reciprocity in ray-class form).

**New this task.**
* `ElkiesEquationsX6` replaces shimura-glue's points-form `ElkiesConicT`. It states Elkies' equations as
  scheme charts over the t-line (`X6Glue.ElkiesCharts`): `Γ({t≠∞}) ≅ ℚ[t,s,r]/(s²+t, r²−3(t−1))`, the same at
  `t≠0` with `a=1/s`, `b=r/s`, both opens affine, glued.
* `X6Glue.conicModelT_of_charts` derives the old points form. It rests on new Mathlib-level lemmas: K-points
  in an affine open correspond to ring homs `Γ(U)→K` (`ev_injective`, `ev_surjective`, `ev_comp`).
* The X₆ double coset `ℚ^×_{>0}\𝔸_f^×/nrd(𝒪̂^×) = 1` and `deligneComponentsX6_of_printed` were already done by
  shimura-glue. They were re-verified unchanged in this tree.

**What compiles.**
* `scratch/x6-glue/X6Glue.lean` (shimura-glue `RowsGlue.lean` verbatim + 4 parts): 0 errors, 2 min, 82 axiom
  lines all standard.
* `ConicDev.lean` (light check over `HDecomp.QM.Leaves`): 0 errors.
* `DeligneX6.lean`: 0 errors.

**Review.** An independent model review found the new leaf true for the genuine conic, not stronger than
Elkies' function-field statement, not vacuous, and the proof sound.

**What remains.**
* `RayClassCM`. The printed law needs the adelic uniformization of Y₃ with its moduli dictionary, which is
  not in the kernel.
* The fibre clause of the Elkies leaf combines Elkies' "t is a coordinate on X₆/W" with the moduli meaning of
  W (twists).
* Elkies' display, section number and 0/∞ orientation are UNVERIFIED (from memory). The leaf's truth does
  not depend on the orientation.

Report: docs/research/x6-glue.md.
