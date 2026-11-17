# charpoly-port (fleet note)

**Result: deg-det's `DegDet.DegHomogPoly` is proved in every characteristic with no hypothesis, so the open field
`charPolyIndepOfEllAlgClosed` (Mumford §19 Thm 4) closes with no new leaf** (together with charpoly-p's
`charPolyIndepOfEllAlgClosed_of_degHomogPoly'`). Standard axioms throughout.

- `ZInQ.Contrib.OneProof.DegPolyFLT.degHomogPoly : DegDet.DegHomogPoly` (`ZInQKernel/Contrib/OneProof/DegHomogPolyFLT.lean`).
- Anthropic FLT's `exists_isHomogeneous_eval_eq_endDegree_of_abelianSchemePropertyBundle`:
  - 59 new modules, unwrapped from the Lean 4.35 Worker-13 port on `origin/cloud-b3/w13-recovery` into main's
    CloudB3W16Torsion conventions;
  - location `ZInQKernel/Contrib/OneProof/CharPolyPort/Vendor/AnthropicFLT/` (Apache-2.0 notices kept and
    modification lines added);
  - 5 small manual repairs; it builds.
- The comparison `degEnd = endDegree` is proved:
  - finite endomorphisms are flat (FLT's miracle-flatness argument, generalized from `[n]`), hence surjective;
  - a finite kernel makes the endomorphism finite (FLT);
  - the rank at the generic point equals the function-field degree. This is new: `CharPolyPort.finrank_genericPoint`
    in `CharPolyPort/FinrankGeneric.lean`, from Mathlib only.
- `HomFreeFiniteAlgClosedNoEmb` is not needed (charpoly-p's assembly uses `DegHomogPoly` alone).
- Fold: `scratch/charpoly-port/autofold.json` discharges `charPolyIndepOfEllAlgClosed` outright (no leaves).
  Dry run: strict 15/16 on 31 → 14/16 on 30. It imports charpoly-p's `CharPolyCharP`.
- Report: `docs/research/charpoly-port.md`. Log: `scratch/charpoly-port/log.md`.
- Dry-run fold module compiles (`sixContactMin_of_open59`, standard axioms); `#discharges`: the field is discharged with `still assumes: []`.
