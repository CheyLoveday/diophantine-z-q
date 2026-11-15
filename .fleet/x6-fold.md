# x6-fold (fleet summary)

**Verdict: folded.** `ZInQ.OneProof.frozenTarget` now goes through `HDec.HSyn.sixContactMin_of_open16`
(`ZInQKernel/OneProof/H/TailZ22.lean`). It has 65 fields, and the strict LEAF/GLUE count is **55/10** (it was
61 fields, 50/11).

* **Removed:** `r1r2Ab` (GLUE comp) and `x6ConicModel` (GLUE c), both now proved by x6-glue's
  `r1r2_of_published` / `x6ConicModel_of_published`.
* **Added (LEAF):** `babaGranathRationalAb`, `gonzalezRotgerX6Ab`, `elkiesEquationsX6Ab`,
  `deligneComponentsX6PrintedAb`, `geomConnOfAlgClosure`.
* **Added (GLUE c):** `rayClassCMAb`.
* **Not new fields:** T5 comes from the existing textbook field `mumfordTorsionAlgClosed`. `DeligneComponentsX6Printed`
  is reused from `TailZ12`.
* **Abelian-scheme forms.** The five moduli leaves enter in abelian-scheme form (`R1fpPropsAb`, as route-a-fold did).
  Each is converted back by `rw [r1fpProps_eq_ab' hR]` under `mumfordRigidityCore`.

**What compiles (VERIFIED):**
* New modules `TailZ20` (104.5 KB), `TailZ21` (71.5 KB) and `TailZ22` (21 KB). They hold x6-glue's `X6Glue.lean`
  minus the 258 declarations the chain already has (same name and type) and minus dead code, with 12 verbatim
  curve-split copies replaced by an `open`. TailZ22 has the bundles and conversions.
* `lake build +ZInQKernel.OneProof.Main` passes.
* `frozenTarget`'s axioms are `[propext, Classical.choice, Quot.sound]`.
* DumpCompact: 0 existing constants deleted or changed; 459 new (TailZ20-22 and frozenTarget).
* PruneScan: 0 unused fields.

**Reading risks (from x6-glue):**
* Elkies' display, section number and `0`/`∞` orientation are UNVERIFIED.
* One Baba–Granath reading (the §3.1 table, CM assignment) is UNVERIFIED.
* Elkies' fibre clause is a composite under the strict reading. The count is then 54/11, still no rise.
* `RayClassCM` is a consequence; turning it into the printed form needs the adelic uniformization of `Y₃`.

**What remains:**
* 10 strict GLUE fields (docs/research/x6-fold.md §5).
* Optional dedupe of content-level overlaps: shimura-split Part 1 against `ZInQ.LeafFold9`, and `CoarseFactorAG`
  against `CurveSplit`.

Report: docs/research/x6-fold.md; log: scratch/x6-fold/log.md.
