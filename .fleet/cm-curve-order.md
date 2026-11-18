# cm-curve-order — complete

**VERIFIED:** the original `CMCurveOrder` statement at `324f0655a` is proved.
The body does not assume `A.dim = 2`; this is checked against a verbatim copy.
The merged fibre-split tip proves the surface specialization. This task proves the
original by excluding the identity corner using T6: the reverse split would
inject the rank-eight endomorphism lattice of A into that of E, of rank at most four.
The manuscript's `thm:height` proof, L582–587, correctly uses the uncited standard
corner and full-order facts at the CM fibre.

The provider `cmFibreSplit_of_curveOrder324` uses only inputs available at open4.
The open78 CM fold removes `cmFibreSplit` and preserves the GR §9 branch.
**H strict LEAF/GLUE: 5/28 on 33 → 5/27 on 32.** No new leaf or glue.

Both new modules and the scratch statement, fold dry run, closure audit, and
discharge checks compiled. The order proof, split provider, open78 and frozen
target use only `propext`, `Classical.choice`, and `Quot.sound`. The targeted
discharge output and all other transcripts are in `scratch/cm-curve-order/`.

See `docs/research/cm-curve-order.md` (report commit `9cd46cfdf`) and the hand
spec `scratch/cm-curve-order/autofold.json`. Integration remains: switch Main
to `OpenResearchLeaves59CMFS` and `sixContactMin_of_open78_cm` and regenerate the
open rows. Main and the inherited ratings were left as supplied.
