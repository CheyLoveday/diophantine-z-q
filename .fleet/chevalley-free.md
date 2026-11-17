# chevalley-free

**Verdict: field `chevalleyPerfect` removable with no new leaf.** `ZInQ.HeightFix.SemiAbelianDescendsPerfect` is
proved outright (`ZInQ.ChevFree.semiAbelianDescendsPerfect_proof`, no hypotheses, axioms propext / Classical.choice
/ Quot.sound), so Chevalley's theorem over a perfect field is no longer needed. Strict count 16/15 on 31 → 15/15 on 30
(autofold count dry run); no GLUE added.

**What compiles** (VERIFIED, `lake env lean`):
- `scratch/chevalley-free/ChevFree.lean` (2060 lines, ~25 s): spreading out to a finite subextension (vendored
  `exists_finiteSubext_isPullback` + Mathlib `exists_π_app_comp_eq_of_locallyOfFinitePresentation`); rigidity of
  tori in abelian varieties over any field (vendored ℙ¹, valuative extension, `RationalCurves.eq_zero_comp`); the
  transport condition from rigidity with field tests on a smooth universal source; descent of the quotient along a
  finite flat cover (descent datum by effective-epi descent, vendored `isEffective_of_isFinite`); group laws through
  fpqc quotients; property descent; the fields `bostLowerBound`, `gaudronRemondThm14`, `javanpeykarBound`,
  `pazukiCor13Upper` from height-fix's printed leaves with no Chevalley. 22 axiom checks, all standard.
- `scratch/chevalley-free/fold/`: bypass module `TailZ65.lean.txt` (generator `gen_bypass.py`;
  `OpenResearchLeaves40` = 39 minus the field, mapped straight to 36EB where its three readers are fields),
  `Main.lean.patched.txt`, `MainCheck.lean` (frozenTarget on the new bundle: standard axioms; closure free of
  `ChevalleyPerfect` and `sorryAx`).

**What remains**: landing it (copy ChevFree.lean to `ZInQKernel/Contrib/OneProof/ChevalleyFree.lean`, add TailZ65,
switch Main, drop the `chevalleyPerfect` rows of kinds.tsv/claims.tsv, run OpenStatements/render_open/#discharges/
hash guard) — not done, `ZInQKernel/` is outside this task. Report: `docs/research/chevalley-free.md`.
